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
(defn push-tail-pos [ast f]
  (let [id (gensym 'tail)]
    (ast/prewalk (assoc-in ast [::pre/config ::tail] id)
                 (fn [ast]
                   (if-not (= id (get-in ast [::pre/config ::tail]))
                     (reduced ast)
                     (case (:op ast)
                       :do (assoc-in ast [:ret ::pre/config ::tail] id)
                       :if (-> ast
                               (assoc-in [:then ::pre/config ::tail] id)
                               (assoc-in [:else ::pre/config ::tail] id))
                       (:let :letfn) (assoc-in ast [:body ::pre/config ::tail] id)
                       (reduced (f ast))))))))

(defn unwrap-with-meta [ast]
  (if (= :with-meta (:op ast))
    (recur (:expr ast))
    ast))

(defn subst-locals [ast subst]
  (ast/postwalk ast
                (fn [ast]
                  (case (:op ast)
                    :local (if-let [sast (subst (:name ast))]
                             sast
                             ast)
                    ast))))

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
                         #'classify-invoke/classify-invoke}}}
  [{:keys [op] :as ast}]
  {:post [(:op %)]}
  (case op
    :invoke (let [{the-fn :fn :keys [args]} ast]
              (push-tail-pos
                the-fn 
                (fn [tail-ast]
                  (let [fn-form (emit-form tail-ast)
                        form (with-meta
                               (list* fn-form (map emit-form args))
                               (meta fn-form))
                        env (:env tail-ast)
                        mform (ana/macroexpand-1 form env)]
                    (if (= mform form)
                      (let [unwrapped-fn (unwrap-with-meta tail-ast)
                            special-case
                            (case (:op unwrapped-fn)
                              :fn (when-let [{:keys [params body variadic? fixed-arity env]}
                                             (find-matching-method unwrapped-fn (count args))]
                                    (let [[fixed-params variadic-param] (if variadic?
                                                                          [(pop params) (peek params)]
                                                                          [params nil])
                                          [fixed-args variadic-args] (split-at fixed-arity args)
                                          subst (merge (zipmap (map :name fixed-params) fixed-args)
                                                       (when variadic-param
                                                         (let [the-fn {:op :var
                                                                       :var #'seq
                                                                       :env env
                                                                       :form `seq}
                                                               args [{:op :vector
                                                                      :env env
                                                                      :items (vec variadic-args)
                                                                      :form (mapv :form variadic-args)
                                                                      :children [:items]}]
                                                               invoke-expr {:op :invoke
                                                                            :fn the-fn
                                                                            :env env
                                                                            :args args
                                                                            :form (list* (:form the-fn)
                                                                                         (map :form args))
                                                                            :children [:fn :args]}]
                                                         {(:name variadic-param) invoke-expr})))]
                                      (prn "subst" (zipmap (keys subst) (map emit-form (vals subst))))
                                      (-> body
                                          (subst-locals subst)
                                          jana2/run-passes)))
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
                      (jana2/pre-parse+run-passes mform env))))))
    ast))

