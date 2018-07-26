(ns clojure.core.typed.analyzer2.passes.beta-reduce
  (:require [clojure.core.typed.analyzer2.passes.add-binding-atom :as add-binding-atom]
            [clojure.core.typed.analyzer2.passes.jvm.classify-invoke :as classify-invoke]
            [clojure.tools.analyzer.passes.jvm.annotate-tag :as annotate-tag]
            [clojure.tools.analyzer.passes.jvm.analyze-host-expr :as analyze-host-expr]
            [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]
            [clojure.tools.analyzer.passes.source-info :as source-info]
            [clojure.core.typed.analyzer2.pre-analyze :as pre]
            [clojure.core.typed.analyzer2.jvm.pre-analyze :as jpre]))

(defn beta-reduce-pre
  ""
  ;; want this to go just after pre-analyze so we can call pre-analyze again
  {:pass-info {:walk :pre :before #{#'source-info/source-info}}}
  [{{:keys [::beta-reduce-opts]} ::pre/config, :keys [op] :as ast}]
  {:pre [op]
   :post [(:op %)]}
  (case op
    :invoke (let [beta-reduced-flag (atom nil)]
              (-> ast
                  (assoc [::beta-reduced-flag] beta-reduced-flag)
                  (assoc-in [:fn ::pre/config ::beta-reduce-opts]
                            {::beta-reduced-flag beta-reduced-flag
                             ::args (:args ast)})))
    :fn (if-let [{:keys [::args ::beta-reduced-flag]} beta-reduce-opts]
          (let [nargs (count args)
                matching-method-idx (->> ast
                                         :methods
                                         (map-indexed vector)
                                         (filter (fn [[i a]]
                                                   ; inline fixed arities only for now
                                                   (and (not (:variadic? a))
                                                        (= (:fixed-arity a) nargs))))
                                         ffirst)]
            (if-not matching-method-idx
              ast
              (let [{:keys [params body]} (nth (:methods ast) matching-method-idx)
                    _ (reset! beta-reduced-flag matching-method-idx)]
                (-> ast
                    (update-in [:methods matching-method-idx :params]
                               (fn [params]
                                 (mapv (fn [param arg]
                                         ;; will be copied to all locals because of pre-analyze.
                                         ;; if this proves problematic, we can add a :depends on 
                                         ;; clojure.core.typed.analyzer2.passes.add-binding-atom
                                         ;; and swap! it into the relevant atom in the :binding case.
                                         (assoc param ::subst-to arg))
                                       params
                                       args)))))))
          ast)
    ;; pass opts to tail position
    :do (if beta-reduce-opts
          (assoc-in ast [:ret ::pre/config ::beta-reduce-opts] beta-reduce-opts)
          ast)
    (:let :letfn) (if beta-reduce-opts
                    (assoc-in ast [:body ::pre/config ::beta-reduce-opts] beta-reduce-opts)
                    ast)
    ;do we want to do this in pre or post?
    ;; subst locals
    :local (if-let [sbt (::subst-to ast)]
             (-> sbt
                 (assoc-in sbt [::pre/config ::beta-reduce-opts] beta-reduce-opts)
                 jpre/pre-analyze
                 ;; hmmm do we need/want to recur here?
                 beta-reduce-pre)
             ast)
    ast))

(defn beta-reduce-post
  ""
  {:pass-info {:walk :post :before #{#'annotate-tag/annotate-tag
                                     #'analyze-host-expr/analyze-host-expr
                                     #'classify-invoke/classify-invoke}}}
  [{:keys [op] :as ast}]
  {:post [(:op %)]}
  (case op
    :invoke (if-let [matching-method-idx (some-> (::beta-reduced-flag ast) deref)]
              (get-in ast [:fn :methods matching-method-idx :body])
              ast)
    ast))
