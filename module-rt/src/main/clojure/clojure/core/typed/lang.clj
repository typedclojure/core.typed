(ns clojure.core.typed.lang
  "Extensible languages in Clojure, a la Racket's #lang.
  
  This is a simple library that monkey patches clojure.core/load
  to be extensible to different backends.

  `monkey-patch-extensible-load` does the actual monkey-patching and
  must be called explicitly.
  
  `lang-dispatch` is an atom containing a map from keywords to alternative 
  `load` functions (of type [String -> nil]). 
  The corresponding function will be used to load a file according its 
  :lang metadata entry in the `ns` form.

  To add a new implementation, choose a namespace name you want to be a
  :lang, and define any of the following vars inside that namespace:

    - lang-load: a 2 argument that sustitutes for clojure.core/load
    - lang-eval: a 1 argument that sustitutes for clojure.core/eval

  eg. A file with a `ns` form
        (ns fancy-ns-form
          {:lang :my-new-lang})
      will use `my-new-lang/lang-load` to load the file.
  "
  (:require [clojure.tools.namespace.file :as ns-file]
            [clojure.core.typed.errors :as err]
            [clojure.core.typed.internal :as internal]
            [clojure.java.io :as io]))

;; copied from clojure.core.typed.ns-deps-utils
(defn ns-form-for-file
  "Returns the namespace declaration for the file, or
  nil if not found"
  [file]
  (some-> (io/resource file)
          ns-file/read-file-ns-decl))

;; copied from clojure.core.typed.ns-deps-utils
(defn ns-form-name
  "Returns the symbol naming this namespace, with any
  metadata attached."
  [ns-form]
  {:post [(symbol? %)]}
  (let [ns-form (next ns-form)
        [nsym ns-form] (internal/take-when symbol? ns-form)
        _ (when-not (symbol? nsym)
            (err/int-error "Malformed ns form"))
        [docstr ns-form]  (internal/take-when string? ns-form)
        [metamap ns-form] (internal/take-when map? ns-form)]
    (if (map? metamap)
      (vary-meta nsym merge metamap)
      nsym)))

;; copied from clojure.core.typed.ns-deps-utils
(defn ns-meta
  "Returns the metadata map for this namespace"
  [ns-form]
  (meta (ns-form-name ns-form)))

; [String -> nil]
(defn default-load1 
  "Roughly equivalent to clojure.core/load."
  [^String base-resource-path]
  (clojure.lang.RT/load base-resource-path))

; [Any -> Any]
(defn default-eval 
  "Roughly equivalent to clojure.core/eval."
  [form]
  (. clojure.lang.Compiler (eval form)))

;; assumes lang has already been resolved and loaded
(defn lang-load-for-lang [lang]
  (when (keyword? lang)
    (some-> (find-ns (symbol (name lang)))
            (ns-resolve 'lang-load))))

;; assumes lang has already been resolved and loaded
(defn lang-eval-for-lang [lang]
  (when (keyword? lang)
    (some-> (find-ns (symbol (name lang)))
            (ns-resolve 'lang-eval))))

(def short-hand-langs {:core.typed :clojure.core.typed})

(defn resolve-short-lang [l]
  (get short-hand-langs l l))

(defn lang-from-ns-meta [m]
  {:pre [(or (nil? m)
             (map? m))]}
  (-> m
      :lang
      resolve-short-lang))

; [Str -> Any]
(defn file-lang
  "Returns the :lang entry in ns form in the given namespace."
  [res]
  (some-> res 
          ns-form-for-file 
          ns-meta 
          lang-from-ns-meta))

; [Namespace -> Any]
(defn ns-lang
  "Returns the :lang value in the give Namespace's metadata."
  [ns]
  (-> (meta ns) lang-from-ns-meta))

(defn retrieve-and-load-lang [mlang]
  (let [lang (resolve-short-lang mlang)]
    (when (keyword? lang)
      (require (symbol (name lang)))
      lang)))

; [Str * -> nil]
(defn extensible-load
  "Loads Clojure code from resources in classpath. A path is interpreted as
   classpath-relative if it begins with a slash or relative to the root
   directory for the current namespace otherwise."
  {:added "1.0"}
  [& paths]
  (doseq [^String path paths]
    (let [^String path (if (.startsWith path "/")
                          path
                          (str (#'clojure.core/root-directory (ns-name *ns*)) \/ path))]
      (when @#'clojure.core/*loading-verbosely*
        (printf "(clojure.core/load \"%s\")\n" path)
        (flush))
      (#'clojure.core/check-cyclic-dependency path)
      (when-not (= path (first @#'clojure.core/*pending-paths*))
        (with-bindings {#'clojure.core/*pending-paths* (conj @#'clojure.core/*pending-paths* path)}
          (let [base-resource-path (.substring path 1)
                lang (-> (or (file-lang (str base-resource-path ".clj"))
                             (file-lang (str base-resource-path ".cljc")))
                         retrieve-and-load-lang)
                disp (or (lang-load-for-lang lang)
                         default-load1)]
            (disp base-resource-path)))))))

(defn extensible-eval
  "Evaluates the form data structure (not text!) and returns the result."
  [form]
  (let [lang (-> (ns-lang *ns*)
                 retrieve-and-load-lang)
        disp (or (lang-eval-for-lang lang)
                 default-eval)]
    (disp form)))

; [-> nil]
(def monkey-patch-extensible-load
  "A no-argument function that installs the extensible `load` function
  over clojure.core/load."
  (let [l (delay (alter-var-root #'load (constantly #'extensible-load)))]
    (fn []
      @l
      nil)))

; [-> nil]
(def monkey-patch-extensible-eval
  "A no-argument function that installs the extensible `eval` function
  over clojure.core/eval."
  (let [l (delay (alter-var-root #'eval (constantly #'extensible-eval)))]
    (fn []
      @l
      nil)))

(defn install 
  "A no-argument function that installs extensible `eval` and `load`
  alternatives that respect :lang ns metadata"
  ([] (install :all))
  ([features]
   (when (or (= features :all)
             (:load features))
     (monkey-patch-extensible-load))
   ;; Only patch load at the moment.
   ;(when (or (= features :all)
   ;          (:eval features))
   ;  (monkey-patch-extensible-eval))
   nil))
