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
            [clojure.core.typed.analyzer2.jvm.pre-analyze :as jpre]
            [clojure.core.typed.analyzer2.jvm :as jana2]
            [clojure.pprint :as pprint]
            [clojure.core.typed.analyzer2 :as ana]
            [clojure.core.typed.analyzer2.passes.uniquify :as uniquify]))

(def beta-limit 100)

(defn find-matching-method [ast nargs]
  {:pre [(= :fn (:op ast))
         (nat-int? nargs)]
   :post [((some-fn nil? (comp #{:fn-method} :op)) %)]}
  (let [matching-method (->> ast
                             :methods
                             (filter (fn [a]
                                       ; inline fixed arities only for now
                                       (and (not (:variadic? a))
                                            (= (:fixed-arity a) nargs))))
                             first)]
    matching-method))

(comment
                                   ;; try and macroexpand
                                   :var (let [;; TODO cache analysis results for args
                                              form (list* (emit-form ast) (map emit-form args))
                                              ;; because we have already fully analyzed the args,
                                              ;; I think using the :var's :env is correct.
                                              env (:env ast)
                                              _ (prn "calling macroexpand-1" (:var ast))
                                              mform (ana/macroexpand-1 form env)]
                                          (if (= form mform)
                                            ;; FIXME do we need this reduced?
                                            (reduced
                                              {:op :invoke
                                               :form form
                                               :fn ast
                                               :args args
                                               :env env
                                               :children [:fn :args]})
                                            (do
                                              (swap! state update ::beta-count inc)
                                              (prn "rerun passes" (::beta-count @state))
                                              ;; FIXME do we need this reduced?
                                              (reduced (jana2/pre-parse+run-passes mform env)))))
                                   :fn (if-let [{:keys [params body]} (find-matching-method ast (count args))]
                                         ;; substitute locals
                                         (let [subst (zipmap (map :name params) args)
                                               subst-fn (fn [ast]
                                                          {:post [((some-fn map? reduced?) %)]}
                                                          (assert (:op ast) (pr-str (class ast)))
                                                          (cond
                                                            (< beta-limit (::beta-count @state)) (do
                                                                                                   (prn "reached beta reduction limit")
                                                                                                   (reduced ast))
                                                            (= (:op ast) :local) (if-let [sast (subst (:name ast))]
                                                                                   (do
                                                                                     (swap! state update ::beta-count inc)
                                                                                     (reduced sast))
                                                                                   ast)
                                                            :else ast))]
                                           (prn "found :fn")
                                           (swap! state update ::beta-count inc)
                                           ;; FIXME do we need this reduced?
                                           (reduced (ast/prewalk body subst-fn)))
                                         ast)
  )

; Ast [TailAst -> Ast] -> Ast
(defn push-tail-pos [ast f]
  (ast/prewalk (assoc-in ast [::pre/config ::tail] true)
               (fn [ast]
                 (if-not (get-in ast [::pre/config ::tail])
                   (reduced ast)
                   (case (:op ast)
                     :do (assoc-in ast [:ret ::pre/config ::tail] true)
                     :if (-> ast
                             (assoc-in [:then ::pre/config ::tail] true)
                             (assoc-in [:else ::pre/config ::tail] true))
                     (:let :letfn) (assoc-in ast [:body ::pre/config ::tail] true)
                     (reduced (f ast)))))))

(defn push-invoke
  "Push arguments into the function position of an :invoke
  so the function and arguments are both in the
  same :invoke node.
  
  eg. ((let [a 1] identity) 2)
      ;=> (let [a 1] (identity 2))
  eg. ((if c identity first) [1])
      ;=> (if c (identity [1]) (first [1]))
  "
  ;; tempting to make :pre, but I think we want the arguments to
  ;; be fully analyzed before we substitute them
  {:pass-info {:walk :post
               :before #{#'annotate-tag/annotate-tag
                         #'analyze-host-expr/analyze-host-expr
                         #'classify-invoke/classify-invoke}}}
  [{:keys [op] :as ast}]
  {:post [(:op %)]}
  (case op
    :invoke (let [{the-fn :fn :keys [args]} ast]
              (push-tail-pos the-fn 
                             (fn [tail-ast]
                               (let [form (list* (:form tail-ast) (map :form args))]
                                 {:op :invoke
                                  :form form
                                  :fn tail-ast
                                  :args args
                                  :env (:env tail-ast)
                                  :children [:fn :args]}))))
    ast))

(defn unwrap-with-meta [ast]
  (if (= :with-meta (:op ast))
    (unwrap-with-meta (:expr ast))
    ast))

(defn subst-locals [ast subst]
  (ast/prewalk ast
               (fn [ast]
                 (case (:op ast)
                   :local (if-let [sast (subst (:name ast))]
                            (reduced sast)
                            ast)
                   ast))))

(defn beta-reduce
  {:pass-info {:walk :post
               :depends #{#'push-invoke}
               :state (fn [] (atom {::beta-count 0}))}}
  [state {:keys [op] :as ast}]
  (prn "beta-reduce" (emit-form ast))
  (case op
    :invoke (let [{:keys [args]} ast
                  the-fn (unwrap-with-meta (:fn ast))]
              (prn "(:op the-fn)" (:op the-fn))
              (case (:op the-fn)
                :fn (if-let [{:keys [params body]} (find-matching-method the-fn (count args))]
                      (subst-locals body (zipmap (map :name params) args))
                      ast)
                ast))
    ast))
