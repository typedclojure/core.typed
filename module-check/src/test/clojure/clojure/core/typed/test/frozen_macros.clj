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

(deftest when-not-test
  (is-tc-e (fn [a :- (U nil Number)]
             (when-not (not a) (inc a))))
  (is-tc-e (fn [a :- (U nil Number)]
             (when-not (not a) (inc a))))
  (is-tc-e (fn [a :- Number] :- Number
             (when-not (not a) (inc a))))
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when-not (not a) (inc a))))
  ;; error msg
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when-not (not a)))))

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

(deftest when-let-test
  (is-tc-e (when-let [_ 1]
             (inc 1)))
  (is-tc-e (when-let [a 1]
             (inc a)))
  (is-tc-e (when-let [a (ann-form 1 (U nil Number))]
             (inc a)))
  (is-tc-err (when-let [a (ann-form 1 (U nil Number String))]
               (inc a)))
  (is-tc-err (when-let [a "a"]
               (inc a)))
  )

(deftest if-let-test
  (is-tc-e (if-let [_ 1]
             (inc 1)))
  (is-tc-e (if-let [a 1]
             (inc a)))
  (is-tc-e (if-let [a (ann-form 1 (U nil Number))]
             (inc a)))
  (is-tc-e (if-let [{:keys [a]} {:a 1}]
             (inc a)
             1))
  (is-tc-err (if-let [a (ann-form 1 (U nil Number String))]
               (inc a)))
  (is-tc-err (if-let [a "a"]
               (inc a)))
  )

(deftest assert-test
  (binding [*assert* true]
    (is-tc-e #(assert 1)))
  (binding [*assert* true]
    (is-tc-e #(assert 1 "foo")))
  (binding [*assert* false]
    (is-tc-e #(assert (/ nil nil) "foo")))
  (binding [*assert* false]
    (is-tc-e #(assert (/ nil nil "foo"))))
  (is-tc-err #(assert (/ nil) "foo"))
  ;; unreachable message
  (is-tc-e #(assert "foo" (/ nil)))
  (is-tc-err #(assert nil (/ nil))))

(deftest with-open-test
	(is-tc-e #(with-open [r (java.io.FileInputStream. "some/dir")] 
              (.available r))))

(deftest fn-test
  (is-tc-e (clojure.core/fn [a] a)))
