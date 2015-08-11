(ns clojure.core.typed.env)

(def ^:dynamic *checker* nil)

(defn checker []
  (let [c *checker*]
    (assert (instance? clojure.lang.IAtom c) "No checker state")
    c))

(defn empty-checker []
  {})

(defn init-checker []
  (atom (empty-checker)
        :validator map?))

(defn deref-checker []
  {:post [(map? %)]}
  @(checker))

(defn swap-checker! [& args]
  (apply swap! (checker) args))

(defmacro with-checker [c & body]
  `(binding [*checker* ~c]
     ~@body))
