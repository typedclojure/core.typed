;; should be a JVM pass since it calls `run-passes`
(ns clojure.core.typed.analyzer2.passes.beta-reduce
  (:require [clojure.core.typed.analyzer2.passes.add-binding-atom :as add-binding-atom]
            [clojure.core.typed.analyzer2.passes.jvm.classify-invoke :as classify-invoke]
            [clojure.tools.analyzer.passes.jvm.annotate-tag :as annotate-tag]
            [clojure.tools.analyzer.passes.jvm.analyze-host-expr :as analyze-host-expr]
            [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]
            [clojure.tools.analyzer.passes.source-info :as source-info]
            [clojure.tools.analyzer.ast :as ast]
            [clojure.core.typed.analyzer2.pre-analyze :as pre]
            [clojure.core.typed.analyzer2.jvm :as jana2]
            [clojure.pprint :as pprint]
            [clojure.core.typed.analyzer2 :as ana]
            [clojure.tools.analyzer.utils :as u]
            [clojure.core.typed.analyzer2.passes.uniquify :as uniquify]))

(def beta-limit 500)

(defn find-matching-method [ast nargs]
  {:pre [(= :fn (:op ast))
         (nat-int? nargs)]
   :post [((some-fn nil? (comp #{:fn-method} :op)) %)]}
  (let [{fixed-arities false variadic-arities true} (group-by (comp boolean :variadic?) (:methods ast))
        matching-method (->> fixed-arities
                             (filter (fn [a]
                                       (= (:fixed-arity a) nargs)))
                             first)
        matching-method (or matching-method
                            (when-let [[variadic-arity] variadic-arities]
                              (when (<= (:fixed-arity variadic-arity) nargs)
                                variadic-arity)))]
    matching-method))

; Ast [TailAst -> Ast] -> Ast
(defn visit-tail-pos [ast f]
  (let [rec #(visit-tail-pos % f)]
    (case (:op ast)
      :do (update ast :ret rec)
      :if (-> ast
              (update :then rec)
              (update :else rec))
      (:let :letfn) (update ast :body rec)
      (f ast))))

(defn unwrap-with-meta [ast]
  (if (= :with-meta (:op ast))
    (recur (:expr ast))
    ast))

;; assumption: none of (keys subst) occur in (vals subst)
(defn subst-locals [ast subst]
  (ast/postwalk ast
                (fn [ast]
                  (case (:op ast)
                    :local (if-let [sast (subst (:name ast))]
                             sast
                             ast)
                    ast))))

(defn var->vsym [^clojure.lang.Var v]
  (symbol (some-> (.ns v) ns-name str) (str (.sym v))))

(defn splice-seqable-expr
  "If ast is a seqable with a known size and sequential, returns a vector
  of the members. Otherwise nil.

  eg. (vector 1 2 3)
  [{:op :rest :expr (vector 1 2 3) :count 3}]

  eg. (cons 4 (vector 1 2 3))
  [{:op :fixed :expr 4}
   {:op :rest :expr (vector 1 2 3) :count 3}]
  
  eg. (concat (vector 1 2 3) (range 0))
  [{:op :rest :expr (vector 1 2 3) :count 3}
   {:op :rest :expr (range 0) :count ##Inf}]

  eg. (concat (vector 1 2 3) (range 0) (vector 1 2 3))
  [{:op :rest :expr (vector 1 2 3) :count 3}
   {:op :rest :expr (range 0) :count ##Inf}
   {:op :rest :expr (vector 1 2 3) :count 3}]

  eg. (range 0)
  [{:op :rest :expr (range 0) :count ##Inf}]

  eg. (range 0 39)
  [{:op :rest :expr (range 0 39) :count 39}]

  eg. nil
  [{:op :rest :expr nil :count 0}]

  eg. (take-while symbol? (read-string))
  [{:op :unknown-rest :expr (take-while symbol? (read))}]
  "
  [{:keys [op env] :as ast}]
  {:post [((some-fn nil? map?) %)]}
  (prn "splice-seqable-expr" op (emit-form ast))
  (case op
    :local (do
             (prn "has init" (map? (:init ast)))
             (prn "env has init" (-> env :locals (get (:form ast)) map?)
                  (-> env :locals (get (:form ast)) ((juxt :op :children))))
             (some-> (:init ast) splice-seqable-expr))
    :vector (mapv (fn [i]
                    {:op :fixed
                     :expr i})
                  (:items ast))
    :const (cond
             (sequential? (:val ast))
             (mapv (fn [i]
                     {:op :fixed
                      :expr #(pre/pre-analyze-const % env)})
                   (:val ast))

             (seqable? (:val ast))
             [{:op :rest
               :expr (pre/pre-analyze-const (:val ast) env)
               :count (count (:val ast))}])
    :do (splice-seqable-expr (:ret ast))
    (:let :let-fn) (splice-seqable-expr (:body ast))
    ;TODO lift `if` statements around invoke nodes so they are
    ; automatically handled (if performant)
    :invoke (let [{:keys [args]} ast
                  cargs (count args)
                  ufn (unwrap-with-meta (:fn ast))]
              (case (:op ufn)
                :var (let [vsym (var->vsym (:var ufn))]
                       (case vsym
                         clojure.core/concat
                         (loop [c []
                                args args]
                           (if (empty? args)
                             c
                             (let [[arg] args]
                               (if-let [spliced (splice-seqable-expr arg)]
                                 (recur (update c :fixed into spliced) (next args))
                                 (assoc c :rest-form `(concat ~@(map emit-form args)))))))
                         clojure.core/seq
                         (when (= 1 cargs)
                           (splice-seqable-expr (first args)))
                         ;FIXME something fishy about all these. I don't think they
                         ; should return vectors, don't we need to resplice the results?
                         ;clojure.core/first
                         ;(when (= 1 cargs)
                         ;  (when-let [spliced (splice-seqable-expr (first args))]
                         ;    [(nth spliced 0 (pre/pre-analyze-const nil env))]))
                         ;clojure.core/second
                         ;(when (= 1 cargs)
                         ;  (when-let [spliced (splice-seqable-expr (first args))]
                         ;    [(nth spliced 1 (pre/pre-analyze-const nil env))]))
                         ;clojure.core/nth
                         ;(when (#{2 3} cargs)
                         ;  (let [[coll-expr idx-expr default-expr] args]
                         ;    (when (and (= :const (:op idx-expr))
                         ;               (nat-int? (:val idx-expr)))
                         ;      (when-let [spliced (splice-seqable-expr coll-expr)]
                         ;        (let [idx (:val idx-expr)]
                         ;          [(nth spliced idx (or default-expr
                         ;                                (pre/pre-analyze-const nil env)))])))))
                         nil))
                nil))
    nil))

(defn make-invoke-expr [the-fn args env]
  {:op :invoke
   :fn the-fn
   :env env
   :args args
   :form (list* (:form the-fn)
                (map :form args))
   :children [:fn :args]})

(defn make-var-expr [var env]
  {:op :var
   :var var
   :env env
   :form (var->vsym var)})

(defn fake-seq-invoke [seq-args env]
  (let [the-fn (make-var-expr #'seq env)
        args [{:op :vector
               :env env
               :items (vec seq-args)
               :form (mapv :form seq-args)
               :children [:items]}]
        invoke-expr (make-invoke-expr the-fn args env)]
    invoke-expr))

; ((fn* ([params*] body)) args*)
; ;=> body[args*/params*]
(defn maybe-beta-reduce-fn [ufn args & [{:keys [before-reduce] :as opts}]]
  {:pre [(= :fn (:op ufn))
         (vector? args)]}
  (when-not (:local ufn) ;;TODO
    (when-let [{:keys [params body variadic? fixed-arity env]} (find-matching-method ufn (count args))]
      ;; update before any recursive calls (ie. run-passes)
      (when before-reduce (before-reduce))
      (let [[fixed-params variadic-param] (if variadic?
                                            [(pop params) (peek params)]
                                            [params nil])
            [fixed-args variadic-args] (split-at fixed-arity args)
            subst (merge (zipmap (map :name fixed-params) fixed-args)
                         (when variadic-param
                           {(:name variadic-param) (fake-seq-invoke variadic-args env)}))]
        (-> body
            (subst-locals subst)
            ana/run-passes)))))

(defn record-beta-reduction [state]
  (swap! state update ::expansions inc))

(defn reached-beta-limit? [state]
  (or (::reached-beta-limit @state)
      (< beta-limit (::expansions @state))))

(defn ensure-within-beta-limit [state & [err-f]]
  (when (reached-beta-limit? state)
    (do (swap! state assoc ::reached-beta-limit true)
        (when err-f
          (err-f (::expansions @state))))))

; (apply f args* collarg)
; ;=> (f args* ~@collarg)
(defn maybe-beta-reduce-apply [{:keys [env] :as ufn} args & [{:keys [before-reduce] :as opts}]]
  {:pre [(= 'clojure.core/apply (var->vsym (:var ufn)))
         (vector? args)]}
  (when (<= 1 (count args))
    (let [[single-args collarg] ((juxt pop peek) args)]
      (let [{:keys [fixed rest-form] :as spliced} (splice-seqable-expr collarg)]
        (when (and spliced (seq fixed))
          (let [;; move as many fixed arguments out of the collection argument as possible
                form (if (contains? spliced :rest-form)
                       (cons (emit-form ufn)
                             (concat (map emit-form (concat single-args fixed)) [rest-form]))
                       (map emit-form (concat single-args fixed)))]
            (when before-reduce (before-reduce))
            (ana/run-passes (pre/pre-analyze-form form env))))))))

(defn push-invoke
  "Push arguments into the function position of an :invoke
  so the function and arguments are both in the
  same :invoke node, then reanalyze the resulting :invoke node.
  
  eg. ((let [a 1] identity) 2)
      ;=> (let [a 1] (identity 2))
  eg. ((if c identity first) [1])
      ;=> (if c (identity [1]) (first [1]))
  "
  {:pass-info {:walk :post
               :before #{#'annotate-tag/annotate-tag
                         #'analyze-host-expr/analyze-host-expr
                         #'classify-invoke/classify-invoke}
               :state (fn [] (atom {::expansions 0}))}}
  [state {:keys [op] :as ast}]
  {:post [(:op %)]}
  ;(prn "expansions" (::expansions @state))
  (if (reached-beta-limit? state)
    (do
      (when-not (::reached-beta-limit @state)
        (prn "beta limit reached")
        (swap! state assoc ::reached-beta-limit true))
      ast)
    (case op
      :invoke (let [{the-fn :fn :keys [args]} ast]
                (visit-tail-pos
                  the-fn 
                  (fn [tail-ast]
                    (let [fn-form (emit-form tail-ast)
                          form (with-meta
                                 (list* fn-form (map emit-form args))
                                 (meta fn-form))
                          _ (prn "form" form)
                          env (:env tail-ast)
                          mform (ana/macroexpand-1 form env)]
                      (prn "mform" mform)
                      (if (= mform form)
                        (let [ufn (unwrap-with-meta tail-ast)
                              special-case
                              (case (:op ufn)
                                ;manually called by core.typed
                                ;:fn (maybe-beta-reduce-fn ufn args {:before-reduce #(swap! state update ::expansions inc)})
                                :var (case (var->vsym (:var ufn))
                                       clojure.core/apply (maybe-beta-reduce-apply ufn args)
                                       nil)
                                ;;TODO
                                :const (case (:type ast)
                                         #_:keyword #_(when (= 1 (count args))
                                                        (let [[map-arg] args]
                                                          ))
                                         #_:symbol
                                         #_:map
                                         #_:vector
                                         #_:set
                                         nil)
                                nil)]
                          (or special-case
                              (cond
                                ;; return original :invoke where possible
                                (= the-fn tail-ast) ast
                                :else {:op :invoke
                                       :form form
                                       :fn tail-ast
                                       :args args
                                       :env env
                                       :children [:fn :args]})))
                        (do (swap! state update ::expansions inc)
                            (prn "reparsing invoke" (first mform))
                            ;; TODO like pre-analyze-seq, perhaps we can reuse the implemenation
                            (ana/run-passes
                              (-> (pre/pre-analyze-form mform env)
                                  (update-in [:raw-forms] (fnil conj ())
                                             (vary-meta form assoc ::pre/resolved-op (u/resolve-sym (first form) env)))))))))))
      ast)))

