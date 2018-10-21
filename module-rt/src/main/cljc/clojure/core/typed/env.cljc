(ns clojure.core.typed.env
  #?(:clj (:import (clojure.lang IAtom))))

(def ^:dynamic *checker* nil)

(defn checker-or-nil []
  {:post [(or (instance? IAtom %)
              (nil? %))]}
  *checker*)

(defn checker []
  (let [c *checker*]
    (assert (instance? IAtom c) (str "No checker state: " (pr-str c)))
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

#?(:clj
(defmacro with-checker [c & body]
  `(binding [*checker* ~c]
     ~@body)))
