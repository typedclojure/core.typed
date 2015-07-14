(ns clojure.core.typed.test.transients
  (:require [clojure.core.typed :refer :all]
            [clojure.core.typed.test.test-utils :refer :all]
            [clojure.test :refer :all])
  (:import (clojure.lang ITransientMap ITransientVector ITransientSet
                         ITransientAssociative ATransientSet)))

;(deftest basic-tests
  ;(is-tc-err (let [x (transient [])]
              ;(conj! x 1)
              ;(conj! x 2)
              ;(conj! x "a")))
  ;(is-tc-err (let [x (transient {})]
               ;(do
                 ;(println x)
                 ;(println x))))
  ;(is-tc-err (let [x (transient {})]
               ;(do 
                 ;x
                 ;x)))
  ;(is-tc-err (let [x (transient {:a 1})]
               ;(assoc! x :b 2)
               ;(assoc! x :c 3)))
  ;(is-tc-err (let [x (transient [1 2 3])]
               ;[x x]))
  ;(is-tc-err (let [x (transient [1 2 3])]
               ;(let [y x]
                 ;[y y])))
  ;(is-tc-e (let [x (transient [])]
             ;x))
  ;(is-tc-err (let [xyz (transient [1 2 3])]
             ;(let [yyz xyz]
               ;xyz)))
  ;(is-tc-err (let [x (transient [1 2 3])]
               ;(let [y 0]
                 ;(conj! x 1))
               ;(conj! x 2))))

;(deftest if-tests
  ;(is-tc-err (let [x (transient {})]
              ;(do
                ;x
                 ;(if (< 1 2)
                   ;x
                   ;x))))
  ;(is-tc-err (let [x (transient {})]
               ;(if (< 1 2)
                 ;(do
                   ;x
                   ;(if (< 1 2)
                     ;x
                     ;x)
                   ;x))))
  ;(is-tc-err (let [x (transient {})]
              ;(if (< 1 2)
                ;x
                ;x)
               ;x))
  ;(is-tc-e (let [x (transient {})]
             ;(if (< 1 2)
               ;(if (< 1 2) x x)
               ;x)))
  ;(is-tc-err (let [x (transient {})]
             ;(when true
               ;x
               ;x)
             ;x))
  ;(is-tc-err (let [x (transient {})]
              ;(if (< 1 2)
                ;[x x]
                ;x)))
  ;(is-tc-e (let [x (transient {})]
             ;(if false
               ;[x x]
               ;x)))
  ;(is-tc-err (let [x (transient {})]
              ;(if (< 1 2)
                ;[x x]
                ;[x x])))
  ;(is-tc-err (let [x (transient {})]
              ;(if true
                ;x
                ;[x x])
              ;x))
  ;(is-tc-err (let [x (transient {})]
               ;(if x 
                 ;x
                 ;x)))
  ;(is-tc-err (let [x (transient {})]
              ;(do
                ;x
                ;(if true
                  ;x
                  ;x)
                ;x))))

(deftest loop-tests
  (is-tc-err (let [t (transient [])]
               (dotimes [i 10]
                 (conj! t i))
               (persistent! t)))
  (is-tc-err (let [t (transient {})]
               (dotimes [i 1]
                 (assoc! t i i))))
  (is-tc-e (persistent! 
             (reduce (fn [t i] (assoc! t i i))
                   (transient {})
                   (range 10)))))


;(let [t (transient {})]
  ;(dotimes [i 10]
    ;(assoc! t i i)))

;(let [x (transient {})]
  ;x)

;(let [t (transient [])]
  ;(loop [] t))

;(let [x (transient [])]
  ;x)


;(let [m-atom (atom (transient {}))]
  ;(assoc! @m-atom :a 1)
  ;(assoc! @m-atom :b 2))

;(let [x [1 "a" (transient {})]]
  ;x
  ;x)


; Some more interesting cases 


; (let [x (transient {})] (if c x x))
; (let [x (transient {})] (if c x x) x)
; (let [x (transient {}) f (fn [] x)] (f) (f))
; (let [x (transient {}) f (fn [] x) g f] (g) (f))
; (let [x (transient {}) f [(fn [] x) g f]] (first g) g)
; (let [x (transient {}) f [1 (fn [] x)]] (first f) (first f))

;(defn vrange2 [n :- Number]
  ;(loop [i :- Number, 0 
         ;v (transient [])]
    ;(if (< i n)
      ;(recur (inc i) (conj! v i))
      ;(persistent! v))))

;(let [t :- (Unique (ITransientMap Any Any)), (transient {})]
  ;(dotimes [i 10]
    ;(assoc! t :a 1)))


;(let [t (transient {})]
  ;(dotimes [i 10]
    ;(assoc! t i i))
  ;(persistent! t))



;(let [x  [1 (transient {}) 3], y 5]
  ;x
  ;x
  ;y)
