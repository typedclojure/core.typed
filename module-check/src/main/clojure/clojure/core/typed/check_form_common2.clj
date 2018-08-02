(ns ^:skip-wiki clojure.core.typed.check-form-common2
  (:require [clojure.core.typed.profiling :as p]
            [clojure.core.typed.check :as chk]
            [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.utils :as u]
            [clojure.core.typed.reset-caches :as reset-caches]
            [clojure.core.cache :as cache]
            [clojure.core.typed.file-mapping :as file-map]
            [clojure.core.typed.type-rep :as r]
            [clojure.core.typed.util-vars :as vs]
            [clojure.core.typed.current-impl :as impl]
            [clojure.core.typed.lex-env :as lex-env]
            [clojure.core.typed.errors :as err]
            [clojure.repl :as repl]
            [clojure.core.typed.analyzer2 :as ana]
            [clojure.core.typed.analyzer2.passes.beta-reduce :as beta-reduce]
            [clojure.core.typed.parse-unparse :as prs])
  (:import (clojure.lang ExceptionInfo)))

;; (check-form-info config-map form & kw-args)
;; 
;; Takes a configuration map which different implementations can customize
;; (via eg. clojure.core.typed.check-form-{clj,cljs}), a form to type check
;; and keyword arguments propagated from core.typed users
;; (via eg. {clojure,cljs}.core.typed/check-form-info).
;;
;; Also see docstrings for clojure.core.typed/check-form-info
;; and cljs.core.typed/check-form-info.
;;
;; 
;; Takes config-map as first argument:
;;  Mandatory
;; - :check-top-level    function taking form and expected type and returns a checked AST.
;;
;;  Optional
;; - :eval-out-ast  function taking checked AST which evaluates it and returns the AST
;;                  with a :result entry attached, the result of evaluating it,
;;                  if no type errors occur.
;; - :unparse-ns    namespace in which to pretty-print type.  (FIXME Currently unused)
;; - :emit-form     function from AST to equivalent form, returned in :out-form entry.
;; - :runtime-check-expr    function taking AST and expected type and returns an AST with inserted
;;                          runtime checks.
;; - :runtime-infer-expr    function taking AST and expected type and returns an AST with inserted
;;                          runtime instrumentation.
;; - :should-runtime-infer?  If true, instrument this expression for runtime inference.
;; - :custom-expansions?     If true, we are using custom expansions to type check forms.
;;
;;  (From here, copied from clojure.core.typed/check-form-info)
;; Keyword arguments
;;  Options
;;  - :expected        Type syntax representing the expected type for this form
;;                     type-provided? option must be true to utilise the type.
;;  - :type-provided?  If true, use the expected type to check the form.
;;  - :profile         Use Timbre to profile the type checker. Timbre must be
;;                     added as a dependency.
;;  - :file-mapping    If true, return map provides entry :file-mapping, a hash-map
;;                     of (Map '{:line Int :column Int :file Str} Str).
;;  - :checked-ast     Returns the entire AST for the given form as the :checked-ast entry,
;;                     annotated with the static types inferred after checking.
;;                     If a fatal type error occurs, :checked-ast is nil.
;;  - :bindings-atom   an atom which contains a value suitable for with-bindings.
;;                     Will be updated during macroexpansion and evaluation.
;;  - :beta-limit      A natural integer which denotes the maximum number of beta reductions
;;                     the type system can perform.
;;  
;;  Default return map
;;  - :ret             TCResult inferred for the current form
;;  - :out-form        The macroexpanded result of type-checking, if successful. 
;;  - :result          The evaluated result of :out-form, unless :no-eval is provided.
;;  - :ex              If an exception was thrown during evaluation, this key will be present
;;                     with the exception as the value.
;;  DEPRECATED
;;  - :delayed-errors  A sequence of delayed errors (ex-info instances)
(defn check-form-info
  [{:keys [check-top-level 
           custom-expansions?
           emit-form 
           env
           eval-out-ast 
           runtime-check-expr
           runtime-infer-expr 
           should-runtime-infer?
           instrument-infer-config
           unparse-ns
           analyze-bindings-fn]}
   form & {:keys [expected-ret expected type-provided? profile
                  checked-ast no-eval bindings-atom beta-limit]}]
  {:pre [((some-fn nil? con/atom?) bindings-atom)
         ((some-fn nil? symbol?) unparse-ns)]}
  (assert (not (and expected-ret type-provided?)))
  (p/profile-if profile
    (reset-caches/reset-caches)
    (binding [vs/*already-collected* (atom #{})
              vs/*already-checked* (atom #{})
              vs/*delayed-errors* (err/-init-delayed-errors)
              vs/*analyze-ns-cache* (cache/soft-cache-factory {})
              vs/*in-check-form* true
              vs/*lexical-env* (lex-env/init-lexical-env)
              ;; custom expansions might not even evaluate
              vs/*can-rewrite* (not custom-expansions?)
              vs/*custom-expansions* custom-expansions?
              vs/*beta-count* (when custom-expansions?
                                (atom {:count 0
                                       :limit (or beta-limit 500)}))]
      (let [expected (or
                       expected-ret
                       (when type-provided?
                         (r/ret (binding [prs/*parse-type-in-ns* unparse-ns]
                                  (prs/parse-type expected)))))
            delayed-errors-fn (fn [] (seq @vs/*delayed-errors*))
            file-mapping-atom (atom [])
            should-runtime-check? (and runtime-check-expr
                                       (u/should-runtime-check-ns? *ns*))
            _ (assert (not (and should-runtime-infer? (not runtime-infer-expr)))
                      "Missing runtime inference function when inference is forced.")
            should-runtime-infer? (and runtime-infer-expr
                                       (or (u/should-runtime-infer-ns? *ns*)
                                           should-runtime-infer?))
            ;_ (prn "should-runtime-check?" should-runtime-check?)
            ;_ (prn "should-runtime-infer?" should-runtime-infer?)
            ;_ (prn "ns" *ns*)
            _ (assert (and (not should-runtime-infer?)
                           (not should-runtime-check?))
                      "FIXME")
            #_#_
            check-expr (or (when should-runtime-infer?
                             #(binding [vs/*instrument-infer-config* instrument-infer-config]
                                (runtime-infer-expr %1 %2)))
                           (when should-runtime-check?
                             runtime-check-expr)
                           check-expr)
            terminal-error (atom nil)
            c-ast (try
                    (check-top-level form expected)
                    (catch Throwable e
                      (let [e (if (some-> e ex-data err/tc-error?)
                                (try
                                  (err/print-errors! (vec (concat (delayed-errors-fn) [e])))
                                  (catch Throwable e
                                    e))
                                (do
                                  #_(binding [*out* *err*]
                                    (prn e))
                                  e))]
                        (reset! terminal-error e)
                        nil)))
            res (some-> c-ast u/expr-type)
            delayed-errors (delayed-errors-fn)
            ex @terminal-error]
        (merge
          {:delayed-errors (vec delayed-errors)
           :ret (or res (r/ret r/-error))}
          (when ex
            {:ex ex})
          (when checked-ast
            ;; fatal type error = nil
            {:checked-ast c-ast})
          (when (and (impl/checking-clojure?)
                     (not no-eval)
                     (empty? delayed-errors)
                     (not ex))
            {:result (:result c-ast)})
          (when (and c-ast emit-form (not ex))
            {:out-form (emit-form c-ast)}))))))

(defn check-form*
  [{:keys [impl unparse-ns] :as config} form expected type-provided?]
  (let [{:keys [ex delayed-errors ret]} (check-form-info config form
                                                      :expected expected 
                                                      :type-provided? type-provided?)]
    (if-let [errors (seq delayed-errors)]
      (err/print-errors! errors)
      (if ex
        (throw ex)
        (prs/unparse-TCResult-in-ns ret unparse-ns)))))
