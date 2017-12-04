(ns clojure.core.typed.test.ctyp-273
  (:require [clojure.test :refer :all]
            [clojure.core.typed.test.test-utils :refer :all]))

(deftest recur-intersection-test
  (is-tc-e (fn [x]
             (recur :kw))
           (IFn [Kw -> Boolean]
                [Int -> Boolean])))
