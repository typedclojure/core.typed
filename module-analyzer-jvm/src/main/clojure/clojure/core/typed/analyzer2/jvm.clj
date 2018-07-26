;; adapted from tools.analyzer.jvm
(ns clojure.core.typed.analyzer2.jvm
  (:refer-clojure :exclude [macroexpand-1])
  (:require [clojure.tools.analyzer.utils :as u]
            [clojure.tools.analyzer.jvm.utils :as ju]
            [clojure.tools.analyzer.env :as env]
            [clojure.tools.analyzer :as ta]
            [clojure.tools.analyzer.ast :as ast]
            [clojure.tools.analyzer.jvm :as taj]
            [clojure.tools.analyzer.passes.jvm.emit-form :as emit-form]
            [clojure.tools.analyzer.passes :as passes]
            [clojure.tools.analyzer.passes.trim :as trim]
            #_[clojure.tools.analyzer.passes.jvm.box :as box]
            #_[clojure.tools.analyzer.passes.jvm.warn-on-reflection :as warn-on-reflection]
            #_[clojure.tools.analyzer.passes.warn-earmuff :as warn-earmuff]
            [clojure.core.typed.analyzer2.passes.jvm.infer-tag :as infer-tag]
            [clojure.tools.analyzer.passes.jvm.analyze-host-expr :as analyze-host-expr]
            #_[clojure.tools.analyzer.passes.jvm.validate-loop-locals :as validate-loop-locals]
            [clojure.tools.analyzer.passes.elide-meta :as elide-meta]
            [clojure.tools.analyzer.passes.source-info :as source-info]
            [clojure.tools.analyzer.passes.jvm.constant-lifter :as constant-lift]
            [clojure.core.typed.analyzer2.passes.jvm.classify-invoke :as classify-invoke]
            [clojure.core.typed.analyzer2.passes.uniquify :as uniquify2]
            [clojure.core.typed.analyzer2.passes.jvm.validate :as validate]
            [clojure.core.typed.analyzer2 :as ana]
            [clojure.core.typed.analyzer2.pre-analyze :as pre]
            [clojure.core.typed.analyzer2.jvm.pre-analyze :as jpre])
  (:import (clojure.lang IObj RT Var)))

(def specials
  "Set of the special forms for clojure in the JVM"
  (into ana/specials
        '#{monitor-enter monitor-exit clojure.core/import* reify* deftype* case*}))

(defn macroexpand-1
  "If form represents a macro form or an inlineable function, returns its expansion,
   else returns form."
  ([form] (macroexpand-1 form (taj/empty-env)))
  ([form env]
       (cond

        (seq? form)
        (let [[op & args] form]
          (if (specials op)
            form
            (let [v (u/resolve-sym op env)
                  m (meta v)
                  local? (-> env :locals (get op))
                  macro? (and (not local?) (:macro m)) ;; locals shadow macros
                  inline-arities-f (:inline-arities m)
                  inline? (and (not local?)
                               (or (not inline-arities-f)
                                   (inline-arities-f (count args)))
                               (:inline m))
                  t (:tag m)]
              (cond

               macro?
               (let [res (apply v form (:locals env) (rest form))] ; (m &form &env & args)
                 (if (u/obj? res)
                   (vary-meta res merge (meta form))
                   res))

               inline?
               (let [res (apply inline? args)]
                 (if (u/obj? res)
                   (vary-meta res merge
                              (and t {:tag t})
                              (meta form))
                   res))

               :else
               (taj/desugar-host-expr form env)))))

        (symbol? form)
        (taj/desugar-symbol form env)

        :else
        form)))

;;redefine passes mainly to move dependency on `uniquify-locals`
;; to `uniquify2/uniquify-locals`

(defn compile-passes [pre-passes post-passes info]
  (let [with-state (filter (comp :state info) (concat pre-passes post-passes))
        state      (zipmap with-state (mapv #(:state (info %)) with-state))

        pfns-fn    (fn [passes direction]
                     (reduce (fn [f p]
                               (let [i (info p)
                                     p (cond
                                         (:state i)
                                         (fn [_ s ast] 
                                           ;(prn (str "before state " direction " pass" p))
                                           ;(clojure.pprint/pprint ast)
                                           (let [ast (p (s p) ast)]
                                             ;(prn (str "after state " direction " pass" p))
                                             ;(clojure.pprint/pprint ast)
                                             ast))
                                         (:affects i)
                                         (fn [a _ ast]
                                           (assert nil "affects not allowed, single pass only")
                                           ;(prn (str "before affects " direction " pass" p))
                                           ;(clojure.pprint/pprint ast)
                                           (let [ast ((p a) ast)]
                                             ;(prn (str "after affects " direction " pass" p))
                                             ;(clojure.pprint/pprint ast)
                                             ast))
                                         :else
                                         (fn [_ _ ast] 
                                           ;(prn (str "before normal " direction " pass" p))
                                           ;(prn (:op ast) (emit-form/emit-form ast))
                                           (let [ast (p ast)]
                                             ;(prn (str "after normal " direction " pass" p))
                                             ;(prn (:op ast) (emit-form/emit-form ast))
                                             ast)))]
                                 (fn [a s ast]
                                   (p a s (f a s ast)))))
                             (fn [_ _ ast] ast)
                             passes))
        pre-pfns  (pfns-fn pre-passes :pre)
        post-pfns  (pfns-fn post-passes :post)]
    (fn analyze [ast]
      (ast/walk ast
                (partial pre-pfns analyze (u/update-vals state #(%)))
                (partial post-pfns analyze (u/update-vals state #(%)))))))

(defn schedule
  "Takes a set of Vars that represent tools.analyzer passes and returns a function
   that takes an AST and applies all the passes and their dependencies to the AST,
   trying to compose together as many passes as possible to reduce the number of
   full tree traversals.

   Each pass must have a :pass-info element in its Var's metadata and it must point
   to a map with the following parameters (:before, :after, :affects and :state are
   optional):
   * :after    a set of Vars, the passes that must be run before this pass
   * :before   a set of Vars, the passes that must be run after this pass
   * :depends  a set of Vars, the passes this pass depends on, implies :after
   * :walk     a keyword, one of:
                 - :none if the pass does its own tree walking and cannot be composed
                         with other passes
                 - :post if the pass requires a postwalk and can be composed with other
                         passes
                 - :pre  if the pass requires a prewalk and can be composed with other
                         passes
                 - :any  if the pass can be composed with other passes in both a prewalk
                         or a postwalk
   * :affects  a set of Vars, this pass must be the last in the same tree traversal that all
               the specified passes must participate in
               This pass must take a function as argument and return the actual pass, the
               argument represents the reified tree traversal which the pass can use to
               control a recursive traversal, implies :depends
   * :state    a no-arg function that should return an atom holding an init value that will be
               passed as the first argument to the pass (the pass will thus take the ast
               as the second parameter), the atom will be the same for the whole tree traversal
               and thus can be used to preserve state across the traversal
   An opts map might be provided, valid parameters:
   * :debug?   if true, returns a vector of the scheduled passes rather than the concrete
               function"
  [passes & [opts]]
  {:pre [(set? passes)
         (every? var? passes)]}
  (let [info        (@#'passes/indicize (mapv (fn [p] (merge {:name p} (:pass-info (meta p)))) passes))
        passes+deps (into passes (mapcat :depends (vals info)))]
    (if (not= passes passes+deps)
      (recur passes+deps [opts])
      (let [[{pre-passes  :passes :as pre}
             {post-passes :passes :as post}
             :as ps]
            (-> (passes/schedule-passes info)
                (update-in [0 :passes] #(vec (cons #'jpre/pre-analyze %))))

            _ (assert (= 2 (count ps)))
            _ (assert (= :pre (:walk pre)))
            _ (assert (= :post (:walk post)))
            ]
        (if (:debug? opts)
          (mapv #(select-keys % [:passes :walk]) ps)
          (compile-passes pre-passes post-passes info))))))

(def default-passes
  "Set of passes that will be run by default on the AST by #'run-passes"
  ;taj/default-passes
  #{;#'warn-on-reflection
    ;#'warn-earmuff

    #'uniquify2/uniquify-locals

;KEEP
    #'source-info/source-info
    #'elide-meta/elide-meta
    #'constant-lift/constant-lift
;KEEP

    ; not compatible with core.typed
    ;#'trim/trim

    ; FIXME is this needed? introduces another pass
    ; TODO does this still introduce another pass with `uniquify2/uniquify-locals`?
    ;#'box
    ;#'box/box

;KEEP
    #'analyze-host-expr/analyze-host-expr
    ;#'validate-loop-locals
    #'validate/validate
    #'infer-tag/infer-tag
;KEEP

;KEEP
    #'classify-invoke/classify-invoke
;KEEP
    })

(def scheduled-default-passes
  (delay
    (schedule default-passes)))

(comment
  (clojure.pprint/pprint
    (schedule default-passes
                     {:debug? true}))
  )

(defn ^:dynamic run-passes
  "Function that will be invoked on the AST tree immediately after it has been constructed,
   by default runs the passes declared in #'default-passes, should be rebound if a different
   set of passes is required.

   Use #'clojure.tools.analyzer.passes/schedule to get a function from a set of passes that
   run-passes can be bound to."
  [ast]
  (@scheduled-default-passes ast))

(def default-passes-opts
  "Default :passes-opts for `analyze`"
  {:collect/what                    #{:constants :callsites}
   :collect/where                   #{:deftype :reify :fn}
   :collect/top-level?              false
   :collect-closed-overs/where      #{:deftype :reify :fn :loop :try}
   :collect-closed-overs/top-level? false})

(defn analyze
  "Analyzes a clojure form using tools.analyzer augmented with the JVM specific special ops
   and returns its AST, after running #'run-passes on it.

   If no configuration option is provides, analyze will setup tools.analyzer using the extension
   points declared in this namespace.

   If provided, opts should be a map of options to analyze, currently the only valid
   options are :bindings and :passes-opts (if not provided, :passes-opts defaults to the
   value of `default-passes-opts`).
   If provided, :bindings should be a map of Var->value pairs that will be merged into the
   default bindings for tools.analyzer, useful to provide custom extension points.
   If provided, :passes-opts should be a map of pass-name-kw->pass-config-map pairs that
   can be used to configure the behaviour of each pass.

   E.g.
   (analyze form env {:bindings  {#'ana/macroexpand-1 my-mexpand-1}})"
  ([form] (analyze form (taj/empty-env) {}))
  ([form env] (analyze form env {}))
  ([form env opts]
     (with-bindings (merge {Compiler/LOADER     (RT/makeClassLoader)
                            #'ana/macroexpand-1 macroexpand-1
                            #'ana/create-var    taj/create-var
                            #'pre/pre-parse  jpre/pre-parse
                            #'ana/var?          var?
                            #'*ns*              (the-ns (:ns env))}
                           (:bindings opts))
       (env/ensure (taj/global-env)
         (doto (env/with-env (u/mmerge (env/deref-env) {:passes-opts (get opts :passes-opts default-passes-opts)})
                 (run-passes (pre/pre-analyze-child form env)))
           (do (taj/update-ns-map!)))))))

(deftype ExceptionThrown [e ast])

(defn ^:private throw! [e]
  (throw (.e ^ExceptionThrown e)))

(defmethod emit-form/-emit-form :unanalyzed
  [{:keys [analyzed-atom form] :as ast} opts]
  (if-some [ast @analyzed-atom]
    (emit-form/emit-form ast)
    (do (assert (not (#{:hygienic :qualified-symbols} opts))
                "Cannot support emit-form options on unanalyzed form")
        #_(throw (Exception. "Cannot emit :unanalyzed form"))
        #_(prn (str "WARNING: emit-form: did not analyze: " form))
        form)))

(defn eval-ast [a {:keys [handle-evaluation-exception]
                   :or {handle-evaluation-exception throw!}
                   :as opts}]
  (let [frm (emit-form/emit-form a)
        ;_ (prn "frm" frm)
        result (try (eval frm) ;; eval the emitted form rather than directly the form to avoid double macroexpansion
                    (catch Exception e
                      (handle-evaluation-exception (ExceptionThrown. e a))))]
    (merge a {:result result})))

(defn analyze+eval
  "Like analyze but evals the form after the analysis and attaches the
   returned value in the :result field of the AST node.

   If evaluating the form will cause an exception to be thrown, the exception
   will be caught and wrapped in an ExceptionThrown object, containing the
   exception in the `e` field and the AST in the `ast` field.

   The ExceptionThrown object is then passed to `handle-evaluation-exception`,
   which by defaults throws the original exception, but can be used to provide
   a replacement return value for the evaluation of the AST.

   Unrolls `do` forms to handle the Gilardi scenario.

   Useful when analyzing whole files/namespaces."
  ([form] (analyze+eval form (taj/empty-env) {}))
  ([form env] (analyze+eval form env {}))
  ([form env {:keys [additional-gilardi-condition
                     eval-fn
                     annotate-do
                     statement-opts-fn
                     stop-gildardi-check
                     analyze-fn]
              :or {additional-gilardi-condition (fn [form env] true)
                   eval-fn eval-ast
                   annotate-do (fn [a _ _] a)
                   statement-opts-fn identity
                   stop-gildardi-check (fn [form env] false)
                   analyze-fn analyze}
              :as opts}]
     (env/ensure (taj/global-env)
       (taj/update-ns-map!)
       (let [env (merge env (u/-source-info form env))
             [mform raw-forms] (with-bindings {Compiler/LOADER     (RT/makeClassLoader)
                                               #'*ns*              (the-ns (:ns env))
                                               #'ana/macroexpand-1 (get-in opts [:bindings #'ana/macroexpand-1] 
                                                                           macroexpand-1)}
                                 (loop [form form raw-forms []]
                                   (let [mform (if (stop-gildardi-check form env)
                                                 form
                                                 (ana/macroexpand-1 form env))]
                                     (if (= mform form)
                                       [mform (seq raw-forms)]
                                       (recur mform (conj raw-forms
                                                          (if-let [[op & r] (and (seq? form) form)]
                                                            (if (or (ju/macro? op  env)
                                                                    (ju/inline? op r env))
                                                              (vary-meta form assoc ::ana/resolved-op (u/resolve-sym op env))
                                                              form)
                                                            form)))))))]
         (if (and (seq? mform) (= 'do (first mform)) (next mform)
                  (additional-gilardi-condition mform env))
           ;; handle the Gilardi scenario
           (let [[statements ret] (u/butlast+last (rest mform))
                 statements-expr (mapv (fn [s] (analyze+eval s (-> env
                                                                (u/ctx :ctx/statement)
                                                                (assoc :ns (ns-name *ns*)))
                                                            (statement-opts-fn opts)))
                                       statements)
                 ret-expr (analyze+eval ret (assoc env :ns (ns-name *ns*)) opts)]
             (annotate-do
               {:op         :do
                :top-level  true
                :form       mform
                :statements statements-expr
                :ret        ret-expr
                :children   [:statements :ret]
                :env        env
                :result     (:result ret-expr)
                :raw-forms  raw-forms}
               statements-expr
               ret-expr))
           (let [a (analyze-fn mform env opts)
                 e (eval-fn a (assoc opts :original-form mform))]
             (merge e {:raw-forms raw-forms})))))))
