(ns clojure.core.typed.test.frozen-macros
  (:require [clojure.core.typed.test.test-utils :refer :all]
            [clojure.core.typed :as t]
            [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]
            [clojure.test :refer [deftest is]]
            [clojure.pprint :refer [pprint]]))

#_
(deftest unevaluated-macro
  (is (tc-e (do
              (defmacro dont-expand-me [arg]
                `(inc ~arg))
              (dont-expand-me (inc 4)))))
  (is (tc-e (clojure.core/defmacro test-macro [arg]
              (inc arg)
              `(inc ~arg))))
  (is (tc-e (clojure.core/doseq []) nil))
  ;; bug in clojure, this returns 1!
  (is (tc-e (clojure.core/doseq [] 1) nil))
  (is (tc-err (clojure.core/for [])))
  (is (tc-err (clojure.core/for [a [1]])))
  (is (tc-e (clojure.core/doseq [a [1 2 3]] (inc a))))
  (is (tc-e (clojure.core/doseq [a [1 2 3] b [3 4 5] :let [c 2]] (+ a b c))))
  (is (tc-e (clojure.core/doseq [a [1 2 3] b [3 4 5] :let [c 2]] (+ a b c))
            nil))
  (is (tc-err (clojure.core/doseq [a [1 2 3] b [3 4 5] :let [c 2]] (+ a b c))
              (Seqable Any)))
  (is (tc-e (clojure.core/doseq [a [1 2 3] b [3 4 5] :let [c 2]] (+ a b c))
            (U nil (Seqable Any))))
  (is (tc-e (clojure.core/doseq [a [1 2 3] b [3 4 5] :let [c 2]] (+ a b c))
            Any))
  (is (tc-err (clojure.core/doseq [a [1 2 3] b [3 4 5] :let [c 2]] (+ a b c))
              Number))
  (is (tc-err (clojure.core/for [a [1 2 3] b [3 4 5] :let [c 2]] (+ a b c))
              Number))
  (is (tc-err (clojure.core/for [a [1 2 3] b [3 4 5] :let [c 2]] (+ a b c))
              nil))
  (is (tc-e (clojure.core/for [a [1 2 3] b [3 4 5] :let [c 2]] (+ a b c))))
  (is (tc-e (clojure.core/mapcat (clojure.core/fn [a] (clojure.core/map (clojure.core/fn [b] (clojure.core/let [c 2] (do (+ a b c)))) [3 4 5])) [1 2 3])))
	(is (tc-e (clojure.core/mapcat (clojure.core/fn [a] 
                                   (clojure.core/map
                                     (clojure.core/fn [b] 
                                       (clojure.core/let [c 2] 
                                         (do (+ a b c))))
                                     [3 4 5]))
                                 [1 2 3])))
  ;; FIXME bad destructuring error
  (is (tc-err (clojure.core/doseq [[a] #{1}] (inc a))))
  (is (tc-e (clojure.core/dotimes [b 20] (inc b))))
  (is (tc-e (clojure.core/dotimes [b 20] (ann-form b Long))))
  (is (tc-err (clojure.core/dotimes [b 20] (ann-form b nil))))
  (is (tc-err (clojure.core/dotimes [b 20] (b))))
  (is (tc-e (clojure.core/swap! (atom :- Num, 1) (fn [a b] (+ a b)) 2)))
  (is (tc-err (clojure.core/swap! (atom :- Num, 1) (fn [a b] (+ a b)) nil)))
  (is (tc-e (clojure.core/swap! (atom :- Num, 1) (fn [a] (inc a)))))
  (is (tc-e (clojure.core/swap! (atom :- Num, 1) inc)))
  (is (tc-e (clojure.core/swap! (atom :- Num, 1) + 2)))
  (is (tc-err (clojure.core/swap! (atom :- Num, 1) + nil)))
  (is (tc-e (clojure.core/swap! (atom :- Num, 1) (fnil + 0 0) nil)))
  ;; FIXME better error?
  (is (tc-err (clojure.core/swap! (atom :- Num, 1) (fnil + 0) nil)))
  (is (tc-e (clojure.core/swap! (atom :- '{:a Number}, {:a 1}) update :a inc)))
  (is (tc-e (clojure.core/swap! (atom :- '{:a (U nil Number)}, {:a nil}) update :a (fnil inc 0))))
  (is (tc-e ((fnil inc 0) nil)))
  ;; FIXME better error
  (is (tc-err (fnil inc nil)))
  (is (tc-err (clojure.core/swap! (atom :- Num, 1) (fn [a] nil))))
  ;; FIXME
  (is (tc-err (clojure.core/swap! (atom :- Num, 1) (fn [a] nil) 1)))
  (is (tc-err (clojure.core/swap! (atom :- Num, 1))))
  (is (tc-err (clojure.core/swap!)))
  ;(is (tc-e ((clojure.core/juxt inc dec) 1)))
  (is (tc-e (every? (fn [a] (number? (inc a))) [1 2 3])))
  (is (tc-e (let [a (ann-form [] (Coll (U nil Number)))]
              (when (every? (fn [a] (number? a)) a)
                (apply + a)))))
  ;;FIXME
  (is (tc-e (let [a (ann-form [] (Coll (U nil Number)))]
              (when (every? number? a)
                (apply + a)))))
  (is (tc-e (let [a (ann-form 1 (U nil Number))]
              (when ((complement nil?) a)
                (inc a)))))
  ;; FIXME
  (is (tc-err (:a {} nil nil)))
  (is (tc-e ((fn [a] (inc a)) 1)))
  )
