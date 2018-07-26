(ns clojure.core.typed.analyzer2.passes.beta-reduce
  (:require [clojure.core.typed.analyzer2.passes.add-binding-atom :as add-binding-atom]
            [clojure.core.typed.analyzer2.passes.jvm.classify-invoke :as classify-invoke]
            [clojure.tools.analyzer.passes.jvm.annotate-tag :as annotate-tag]
            [clojure.tools.analyzer.passes.jvm.analyze-host-expr :as analyze-host-expr]
            [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]
            [clojure.tools.analyzer.passes.source-info :as source-info]
            [clojure.core.typed.analyzer2.pre-analyze :as pre]
            [clojure.core.typed.analyzer2.jvm.pre-analyze :as jpre]
            [clojure.pprint :as pprint]))

(defn beta-reduce-pre
  ""
  ;; want this to go just after pre-analyze so we can call pre-analyze again
  {:pass-info {:walk :pre :before #{#'source-info/source-info}}}
  [{{:keys [::beta-reduce-opts]} ::pre/config, :keys [op] :as ast}]
  {:pre [op]
   :post [(:op %)]}
  (case op
    :invoke (let [beta-reduced-flag (atom nil)]
              (assert (= :unanalyzed (:op (:fn ast)))
                      (:op (:fn ast)))
              (-> ast
                  (assoc ::beta-reduced-flag beta-reduced-flag)
                  (assoc-in [:fn ::pre/config ::beta-reduce-opts]
                            {::beta-reduced-flag beta-reduced-flag
                             ::args (:args ast)})))
    :fn (if-let [{:keys [::args ::beta-reduced-flag]} beta-reduce-opts]
          (let [nargs (count args)
                matching-method (->> ast
                                     :methods
                                     (filter (fn [a]
                                               ; inline fixed arities only for now
                                               (and (not (:variadic? a))
                                                    (= (:fixed-arity a) nargs))))
                                     first)]
            (if-let [{:keys [params body]} matching-method]
              (let [_ (reset! beta-reduced-flag true)
                    ;; never clashes with uniquify, since that changes :name
                    param-names (mapv :form params)
                    _ (run! (fn [[param arg]]
                              (swap! (::pre/atom param) assoc ::subst-to arg))
                            (map vector params args))]
                ;; FIXME
                ;; should return `body` if we want ((fn [a] a) 1) => 1
                ;; however, for the moment we have ((fn [a] a) 1) => ((fn [a] 1) 1)
                ;; because :with-meta nodes still hang around the fn.
                ;; eg. (^:line (fn [a] a) 1) ;=> ^:line 1
                ;; we can probably fix it.
                #_body
                ast)
              ast))
          ast)
    ;; pass opts to tail position
    :do (cond-> ast
          beta-reduce-opts
          (assoc-in [:ret ::pre/config ::beta-reduce-opts] beta-reduce-opts))
    (:let :letfn) (cond-> ast
                    beta-reduce-opts
                    (assoc-in [:body ::pre/config ::beta-reduce-opts] beta-reduce-opts))
    :with-meta (cond-> ast
                 beta-reduce-opts
                 (assoc-in [:expr ::pre/config ::beta-reduce-opts] beta-reduce-opts))
    ;do we want to do this in pre or post?
    ; probably in pre so we can reuse all the other :pre passes.
    ; need to make sure the tag inference etc. doesn't get confused
    ;; subst locals
    :local (if-let [sbt (::subst-to @(::pre/atom ast))]
             (-> sbt
                 (assoc-in [::pre/config ::beta-reduce-opts] beta-reduce-opts)
                 jpre/pre-analyze
                 ;; hmmm do we need/want to recur here?
                 #_beta-reduce-pre)
             ast)
    ast))

(defn beta-reduce-post
  ""
  {:pass-info {:walk :post :before #{#'annotate-tag/annotate-tag
                                     #'analyze-host-expr/analyze-host-expr
                                     #'classify-invoke/classify-invoke}}}
  [{:keys [op] :as ast}]
  {:post [(:op %)]}
  (prn "post op" (pprint/pprint (emit-form ast)))
  (case op
    :invoke (if (some-> (::beta-reduced-flag ast) deref)
              (do
                (prn "yes")
                (:fn ast))
              (do
                (prn "no")
                ast))
    ast))
