(ns clojure.core.typed.compiler
  (:refer-clojure :exclude [*warn-on-reflection*])
  (:import (clojure.asm Type)
           (clojure.asm.commons Method GeneratorAdapter)
           (clojure.lang 
             Namespace 
             IPersistentMap)
           (clojure.core.typed.lang
             Compiler$BooleanExpr
             Compiler$LocalBinding
             Compiler$LocalBindingExpr
             Compiler$ObjMethod
             Compiler$NilExpr)
  ))

(ns-unmap *ns* 'Compiler)
(import '(clojure.core.typed.lang Compiler))

;; don't use the actual WARN_ON_REFLECTION because core.typed might be able
;; to resolve the reflection.
(def ^:dynamic *warn-on-reflection* false)
;; symbol->localbinding
(def ^:dynamic *local-env* nil)
;; vector<localbinding>
(def ^:dynamic *loop-locals*)
;; Label
(def ^:dynamic *loop-label*)
;; vector<object>
(def ^:dynamic *constants*)
;; IdentityHashMap
(def ^:dynamic *constant-ids*)
;; vector<keyword>
(def ^:dynamic *keyword-callsites*)
;; vector<var>
(def ^:dynamic *protocol-callsites*)
;; set<var>
(def ^:dynamic *var-callsites*)
;; keyword->constid
(def ^:dynamic *keywords*)
;; var->constid
(def ^:dynamic *vars*)
;; FnFrame
(def ^:dynamic *method* nil)
;; null or not
(def ^:dynamic *in-catch-finally* nil)
(def ^:dynamic *no-recur* nil)
;; DynamicClassLoader
(def ^:dynamic *loader*)

;; Integer
(def ^:dynamic ^Integer *line* 0)
(def ^:dynamic ^Integer *column* 0)
(def ^:dynamic ^Integer *line-before* 0)
(def ^:dynamic ^Integer *column-before* 0)
(def ^:dynamic ^Integer *line-after* 0)
(def ^:dynamic ^Integer *column-after* 0)

;; Integer
(def ^:dynamic *next-local-num* 0)
;; Integer
(def ^:dynamic *ret-local-num*)

(def ^:dynamic *compile-stub-sym* nil)
(def ^:dynamic *compile-stub-class* nil)

;; PathNode chain
(def ^:dynamic *clear-path* nil)
;; tail of PathNode chain
(def ^:dynamic *clear-root* nil)
;; LocalBinding -> Set<LocalBindingExpr>
(def ^:dynamic *clear-sites* nil)

(def CONST-PREFIX "const__")
(def TRUE-EXPR (Compiler$BooleanExpr. true true))
(def FALSE-EXPR (Compiler$BooleanExpr. false false))

(deftype ObjExpr
  [^:unsynchronized-mutable ^String name
   ^:unsynchronized-mutable ^String internal-name
   ^:unsynchronized-mutable ^Type this-name
   ^:unsynchronized-mutable ^Type obj-type
   tag
   form
   ^:unsynchronized-mutable closes
   ])

(defn line-deref []
  (.intValue *line*))

(defn column-deref []
  (.intValue *column*))

(defn tag-of [o]
  {:post [((some-fn symbol? nil?) %)]}
  (let [tag (get (meta o) :tag)]
    (cond
      (symbol? tag) tag
      (string? tag) (symbol nil tag))))

;; TODO bad set!
#_
(defn close-over [^Compiler$LocalBinding b 
                  ^Compiler$ObjMethod method]
  {:post [(nil? %)]}
  (cast Compiler$LocalBinding b)
  (cast Compiler$ObjMethod method)
  (cond
    (and b method)
    (let [lb (cast Compiler$LocalBinding (get (.locals method) b))]
      (if (nil? lb)
        (do (let [o (.objx method)]
              (set! (.closes o)
                    (cast IPersistentMap 
                          (assoc (-> method .objx .closes) b b))))
            (close-over b (.parent method)))
        (do (when (zero? (.idx lb))
              (set! (.usesThis method) true))
            (when *in-catch-finally*
              (set! (.localsUsedInCatchFinally method)
                    (cast PersistentHashSet
                          (-> method 
                              .localsUsedInCatchFinally
                              (.cons (.idx b)))))))))))

(declare close-over)

(defn reference-local [sym]
  (when (bound? #'*local-env*)
    (let [^Compiler$LocalBinding
          b (cast Compiler$LocalBinding 
                  (get @*local-env* sym))]
      (when-not b
        (let [^Compiler$ObjMethod
              method (cast Compiler$ObjMethod *method*)]
          (when (zero? (.idx b))
            (set! (.usesThis method) true))
          (close-over b method)))
      b)))

(defn namespace-for 
  ([sym] (namespace-for *ns* sym))
  ([^Namespace inns sym]
   {:pre [(instance? Namespace inns)
          (symbol? sym)
          (namespace sym)]
    :post [(or (nil? %)
               (instance? Namespace %))]}
   ;; note, presumes non-nil sym.ns
   ;;  first check against currentNS' aliases...
   (let [nssym (symbol (namespace sym))
         ns (.lookupAlias inns nssym)]
     (if (nil? ns)
       ;; ...otherwise check the Namespaces map.
       (Namespace/find nssym)
       ns))))

(defn analyze-symbol [sym]
  {:pre [(symbol? sym)]}
  (let [tag (tag-of sym)
        b (when (nil? (namespace sym)) ; ns-qualified syms are always Vars
            (reference-local sym))]
    (cond
      b (Compiler$LocalBindingExpr. b tag sym)
      :else (assert "TODO")
      )))

(defn analyze
  ([context form] (analyze context form nil))
  ([context form nme]
   (try
     (let [form
           (if (instance? clojure.lang.LazySeq form)
             (let [mform form
                   form (seq form)
                   form (if (nil? form)
                          clojure.lang.PersistentList/EMPTY
                          form)
                   form (with-meta form (meta mform))]
               form)
             form)]
       (cond
         (nil? form) (Compiler$NilExpr. form)
         (true? form) TRUE-EXPR
         (false? form) FALSE-EXPR
         (symbol? form) (analyze-symbol form)
         :else (throw (Exception. "placeholder"))
         ))
     (catch Throwable e
       (throw e)
       #_(if (not (instance? Compiler$CompilerException e))
           ;; TODO how to import CompilerException?
           (throw (Compiler$CompilerException. *file* (line-deref) (column-deref) e))
           (throw e))))))
