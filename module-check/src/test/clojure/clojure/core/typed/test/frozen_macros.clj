(ns clojure.core.typed.test.frozen-macros
  (:require 
    ; this loads the type system, must go first
    [clojure.core.typed.test.test-utils :refer :all]
    [clojure.test :refer :all]
    [clojure.core.typed.analyzer2.pre-analyze :as pre]
    [clojure.core.typed.analyzer2.jvm :as ana]
    [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]
    [clojure.tools.analyzer.jvm :as taj]
    [clojure.tools.analyzer.jvm.utils :as ju]))

(deftest ns-test
  (is-tc-e (ns foo) nil)
  (is-tc-err (ns foo) Symbol))

(deftest ann-form-test
  (is-tc-e (ann-form 1 Integer))
  (is-tc-err (ann-form 1 Integer) nil)
  (is-tc-err (ann-form 1 nil)))

(deftest tc-ignore-test
  (is-tc-e (tc-ignore #(/ nil nil)))
  (is-tc-err (tc-ignore #(/ nil nil)) nil))

(deftest when-test
  (is-tc-e (fn [a :- (U nil Number)]
             (when a (inc a))))
  (is-tc-e (fn [a :- (U nil Number)]
             (when a (inc a))))
  (is-tc-e (fn [a :- Number] :- Number
             (when a (inc a))))
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when a (inc a))))
  ;; error msg
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when a))))

(deftest let-test
  (is-tc-e (let [a 1]
             (inc a)))
  (is-tc-e #(let [a (throw (Exception.))]
              (/ nil nil)))
  (is-tc-e #(let [a 1
                  b 2]
              (/ a b)))
  (is-tc-e #(let [a (throw (Exception.))
                  b (/ nil nil)]))
  (is-tc-err #(let [a (/ nil nil)
                    b (throw (Exception.))]
                (/ a b)))
  (is-tc-err #(let [a (/ nil nil)]
                (inc a)))
  (is-tc-err #(let [a 1]
                (/ nil nil)))
  ;destructuring
  (is-tc-e (let [{:keys [a]} {:a 1}]
             (inc a)))

  ;; locals shadow vars
  (is-tc-e (let [identity identity]
             (identity 1))))
