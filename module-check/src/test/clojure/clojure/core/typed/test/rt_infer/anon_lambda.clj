(ns clojure.core.typed.test.rt-infer.anon-lambda
  {:lang :core.typed
   :core.typed {:features #{:runtime-infer}}}
  (:require [clojure.core.typed :as t]))

(defn b [coll]
  (->> coll
       (map (fn [n]
              (inc n)))
       (filter
         (fn [n]
           (odd? n)))))

(b [1 2 3 4 5])
