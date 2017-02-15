(ns clojure.core.typed.test.rt-infer.loop
  {:lang :core.typed
   :core.typed {:features #{:runtime-infer}}}
  (:require [clojure.core.typed :as t]))

(defn b [coll]
  (loop [c coll
         out []]
    (if (seq c)
      (recur (next c) (conj out (inc (first c))))
      out)))

(b [1 2 3 4 5])
