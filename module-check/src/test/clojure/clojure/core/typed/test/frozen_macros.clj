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
  (is-tc-e (ann-form 1 Integer) nil)
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
  (is-tc-e (fn [a :- (U nil Number)] :- Number,
             (when a (inc a))))
  ;; 'else' expected error
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when a 1)))
  ;; 'then+else' expected error
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
  ;; 'then' expected error
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when-not (not a) 1)))
  ;; 'then+else' expected error
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when-not (not a)))))

(deftest let-test
  (is-tc-e (let [a 1]) Number)
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
  (is-tc-e (let [{:keys [a]} []]
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
  (is-tc-err (when-let [a (ann-form nil (U nil Number))]
               (inc a))
             Number)
  )

(deftest if-let-test
  (is-tc-e (if-let [_ 1]
             (inc 1)))
  (is-tc-e (if-let [_ (ann-form 1 (U nil Number))]
             (inc 1))
           Number)
  (is-tc-e (if-let [a 1]
             (inc a)))
  (is-tc-e (if-let [a (ann-form 1 (U nil Number))]
             (inc a)))
  ; improved error
  (is-tc-err (if-let [a (ann-form 1 (U nil Number))]
               (inc a))
             Number)
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
              (.available r)))
  ;; better error
  (is-tc-err #(with-open [r (java.io.FileInputStream. "some/dir")])
             [-> Number]))

(deftest fn-test
  (is-tc-e (clojure.core/fn [a]))
  (is-tc-e (clojure.core/fn [a] a))
  (is-tc-e (clojure.core/fn [a]
             {:pre [(-> a identity)]}
             a))
  (is-tc-e (clojure.core/fn [a]
             {:post [(symbol? %)]}
             a))
  (is-tc-err (clojure.core/fn [a])
             [Number -> Number])
  )

(deftest for-test
  (is-tc-e (clojure.core/for [a [1 2]] a))
  (is-tc-e (clojure.core/for [a [1 2]] a) (Seqable Number))
  ;; FIXME improve error
  (is-tc-err (clojure.core/for [a [1 2]] a) Number)
  ;; FIXME improve error
  (is-tc-e (clojure.core/for [a [1 2]] a) nil)
  (is-tc-e (clojure.core/for [a [1 2] b [2 3]] [a b]))
  (is-tc-e (clojure.core/for [a [1 2] b [2 3]] [a b]) (Seq '[Num Num]))
  ;FIXME use t/fn instead of fn*
  ;; propagates expected type to body
  (is-tc-e (clojure.core/for [a [1 2] b [2 3]] (fn* [c] (+ c a b)))
           (Seq [Num -> Num]))
  ;; example of bad type propagating to body
  (is-tc-err (clojure.core/for [a [1 2] b [2 3]] (fn* [c] (+ c a b))) (Seq [nil -> Num]))
)
