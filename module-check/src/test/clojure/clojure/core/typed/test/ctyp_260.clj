(ns clojure.core.typed.test.ctyp-260
  (:require [clojure.test :refer :all]
            [clojure.core.typed.test.test-utils :refer :all]))

(deftest motivating-use-case
  "This prompted CTYP-260 in the first place."
  (is-tc-e (t/fn [q :- (java.util.Queue String)] (first q))
           [(java.util.Queue String) -> (t/Option String)])
  (is-tc-e (t/fn [q :- (java.util.concurrent.BlockingQueue String)] (first q))
           [(java.util.concurrent.BlockingQueue String) -> (t/Option String)]))

(deftest type-params
  "Queue and BlockingQueue should have type params."
  (is-tc-e (t/ann-form (java.util.LinkedList. [1 2 3]) (java.util.Queue t/Any)))
  (is-tc-e (t/ann-form (java.util.concurrent.LinkedBlockingQueue. [1 2 3]) (java.util.concurrent.BlockingQueue t/Any))))

(deftest seqable
  "Queue and BlockingQueue are both (Seqable a)"
  (is-tc-e (t/ann-form (java.util.LinkedList. [1 2 3]) (t/Seqable t/Any)))
  (is-tc-e (t/ann-form (java.util.concurrent.LinkedBlockingQueue. [1 2 3]) (t/Seqable t/Any))))

