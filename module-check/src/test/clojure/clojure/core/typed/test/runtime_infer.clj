(ns clojure.core.typed.test.runtime-infer
  {:lang :core.typed
   :core.typed {:features #{:runtime-infer}}}
  (:require [clojure.core.typed :as t]))

(defn foo [x]
  (inc x))

(foo 1)
(foo 2)
(foo 3)

(defn blah [t m]
  (into {} t m))

(blah (map identity)
      {:a 1})

(defn assoc-a [m v]
  (assoc m :a v))

(assoc-a {:b 1} 2)
