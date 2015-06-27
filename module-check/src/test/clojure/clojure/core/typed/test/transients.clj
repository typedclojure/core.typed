(ns clojure.core.typed.test.transients
  (:require [clojure.core.typed :refer :all]
            [clojure.test :refer :all])
  (:import (clojure.lang ITransientMap ITransientVector ITransientSet
                         ITransientAssociative ATransientSet)))

;(let [x :- (ITransientVector Number), (transient [1])]
  ;(conj! x 1)
  ;(conj! x 2)
  ;(conj! x "a"))

;(let [x :- (ITransientVector Number), (transient [1 2 3])]
  ;[x x])

;(let [x (transient {:a 1})]
  ;(assoc! x :b 2)
  ;(assoc! x :c 3))

;(let [x :- (ITransientVector Number), (transient [1 2 3])]
  ;(let [y x]
    ;[y y]))

;(is (clojure.core.typed.type-rep/Unique? 1))

;(let [z :- (Unique Int), 1]
  ;z
  ;z)

;(let [xyz [1 2 3]]
  ;(let [yyz xyz]
    ;xyz))

;(defn trial [aki :- Number]
  ;(+ aki aki))

;(let [x 1]
  ;x
  ;x)

;(let [x :- (ITransientVector Number), (transient [1 2 3])]
  ;(let [y 0]
    ;(conj! x 1))
  ;(conj! x 2)

;(let [m-atom :- (Atom1 (ITransientMap Keyword Number)), (atom (transient {}))]
  ;(assoc! @m-atom :a 1)
  ;(assoc! @m-atom :b 2))


;(let [abc 1]
  ;abc)

  ; Some more interesting cases 

; (let [x (transient {})] (if c x x))
; (let [x (transient {})] (if c x x) x)
; (let [x (transient {}) f (fn [] x)] (f) (f))
; (let [x (transient {}) f (fn [] x) g f] (g) (f))
; (let [x (transient {}) f [(fn [] x) g f]] (first g) g)
; (let [x (transient {}) f [1 (fn [] x)]] (first f) (first f))

