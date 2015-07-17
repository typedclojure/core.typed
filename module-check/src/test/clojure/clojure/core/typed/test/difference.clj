(ns clojure.core.typed.test.difference
  (:require [clojure.core.typed :as tc :refer []]
            [clojure.core.typed.test.test-utils :refer :all]
            [clojure.core.typed.type-rep :refer :all]
            [clojure.core.typed.type-ctors :refer :all]
            [clojure.core.typed.cs-gen :refer :all]
            [clojure.core.typed.cs-rep :refer :all]
            [clojure.core.typed.parse-unparse :refer :all]
            [clojure.core.typed.subst :refer [subst-all]]
            [clojure.test :refer :all]))

;; When Difference is ready, uncomment tests at the bottom

(deftest not-type-subtype
  (is-clj (not (subtype? (make-Not -nil) -nil)))
  (is-clj (subtype? (make-Not -nil) (make-Not -nil)))
  (is-clj (not (subtype? (make-Not -nil) (make-Not -false))))
  (is-clj (subtype? (make-Not (Un -false -nil)) (make-Not -false))))

(deftest Not-combine-test
  (is-clj (= (In -nil (make-Not -nil))
             (Un)))
  (is-clj (clj
            (= (In (RClass-of Integer) (make-Not (RClass-of Number)))
               (Un))))

  (is-clj (not (overlap (RClass-of Integer) (make-Not (RClass-of Number)))))
  (is-clj (overlap (RClass-of Number) (make-Not -nil)))

  (is-clj (overlap (make-Not (RClass-of Number))
                   (make-Not (RClass-of Integer))))

  (is-clj (not (overlap (make-Not (RClass-of Number)) 
                        (RClass-of Integer))))

  (is-clj (= (In (RClass-of Number) (make-Not -nil))
             (RClass-of Number)))

  (is-clj (= (In (Un (RClass-of Number) -nil) -nil)
             -nil))
  (is-clj (= (In (Un (RClass-of Number) -nil) (make-Not -nil))
             (RClass-of Number)))
  (is-clj (= (In (RClass-of Number) (make-Not -nil))
             (RClass-of Number)))

  (is-clj (clj (= (In (Un -nil (RClass-of Number)) (make-Not (Un -false -nil)))
                  (RClass-of Number))))

  (is-clj (overlap (Un -nil (RClass-of Number)) (make-Not (Un -false -nil))))

  (is-clj (= (In (Un -nil (RClass-of Number)) (make-Not -nil))
             (RClass-of Number)))
  (is-clj (= (Un (In -nil (make-Not -nil))
                 (In (RClass-of Number) (make-Not -nil)))
             (RClass-of Number)))

  (is-clj (= (In (make-Not (RClass-of Number))
                 (make-Not (RClass-of Integer)))
             (make-Not (RClass-of Number))))

  (is-clj (subtype? (RClass-of Number) (make-Not -nil)))
  (is-clj (subtype? (RClass-of Number) (make-Not (RClass-of Integer))))
  (is-clj (not (subtype? (RClass-of Integer) (make-Not (RClass-of Number)))))
  (is-clj (not (subtype? (make-Not -nil) (RClass-of Number))))

  (is-clj (overlap (make-F 'x) (make-Not (make-F 'y))))
  (is-clj (overlap (make-F 'x) (make-F 'y)))
  (is-clj (overlap (make-Not (make-F 'x)) (make-F 'y)))
  (is-clj (overlap (make-Not (make-F 'x)) (make-Not (make-F 'y))))

  (is-clj (= (In (Un (RClass-of Number) -nil) -nil)
             -nil))
  (is-clj (= (In (Un (RClass-of Number) -nil) (make-F 'y))
             (Un (In (RClass-of Number) (make-F 'y))
                 (In -nil (make-F 'y)))))

  (is-clj (not= (In -nil (make-F 'y))
                (Un)))
  (is-clj (overlap -nil (make-F 'y)))

  (is-clj (= (let [i (subst-all {'x (->t-subst (Un (RClass-of Number) -nil) no-bounds) 
                                 'y (->t-subst -nil no-bounds)} 
                                (In (make-F 'x) (make-Not (make-F 'y))))
                   _ (assert (Intersection? i) (pr-str i))]
               (apply In (:types i)))
             (RClass-of Number)))

  (is-clj (overlap (make-F 'x)
                   (make-Not (make-F 'y))))
  (is-clj (overlap (B-maker 0)
                   (make-Not (B-maker 1))))
  (is-clj (not (subtype? (B-maker 0)
                         (make-Not (B-maker 1)))))
  (is-clj (not= (In (make-F 'x)
                    (make-Not (make-F 'y)))
                (Un))))

;(deftest difference-type-subtype
;  (is-clj (not (sub? (Difference Any nil) nil)))
;  (is-clj (sub? (Difference Any nil) (Difference Any nil)))
;  (is-clj (overlap -any (make-Not -nil)))
;  (is-clj (not (sub? (Difference Any nil) (Difference Any false))))
;  (is-clj (sub? (Difference Any (U false nil)) (Difference Any false)))
;  (is-clj (sub? (Difference Any false nil) (Difference Any false)))
;  (is-clj (sub? (Difference (U Long Float) Float) Long)))
;
;(deftest Difference-combine-test
;  (is-clj (= (-difference -nil (make-Not -nil))
;             (Un)))
;  (is-clj (clj
;            (= (-difference (RClass-of Integer) (RClass-of Number))
;               (Un))))
;
;  (is-clj (not (overlap (RClass-of Integer) (-difference -any (RClass-of Number)))))
;  (is-clj (clj (overlap (RClass-of Number) (-difference -any -nil))))
;
;  (is-clj (overlap (-difference -any (RClass-of Number))
;                   (-difference -any (RClass-of Integer))))
;
;  (is-clj (not (overlap (-difference -any (RClass-of Number))
;                        (RClass-of Integer))))
;
;  (is-clj (= (-difference (RClass-of Number) -nil)
;             (RClass-of Number)))
;
;  (is-clj (= (-difference (Un (RClass-of Number) -nil) -nil)
;             (RClass-of Number)))
;  (is-clj (= (-difference (RClass-of Number) -nil)
;             (RClass-of Number)))
;
;  (is-clj (clj (= (-difference (Un -nil (RClass-of Number)) (Un -false -nil))
;                  (RClass-of Number))))
;
;  (is-clj (overlap (Un -nil (RClass-of Number)) 
;                   (-difference -any (Un -false -nil))))
;
;  (is-clj (= (-difference (Un -nil (RClass-of Number)) -nil)
;             (RClass-of Number)))
;  (is-clj (= (Un (-difference -nil -nil)
;                 (-difference (RClass-of Number) -nil))
;             (RClass-of Number)))
;
;  (is-clj (= (In (-difference -any (RClass-of Number))
;                 (-difference -any (RClass-of Integer)))
;             (-difference -any (RClass-of Number))))
;
;  (is-clj (subtype? (RClass-of Number) (-difference -any -nil)))
;  (is-clj (subtype? (RClass-of Number) (-difference -any (RClass-of Integer))))
;  (is-clj (not (subtype? (RClass-of Integer) (-difference -any (RClass-of Number)))))
;  (is-clj (not (subtype? (-difference -any -nil) (RClass-of Number))))
;
;  (is-clj (= (let [i (subst-all {'x (->t-subst (Un (RClass-of Number) -nil) no-bounds) 
;                                 'y (->t-subst -nil no-bounds)} 
;                                (-difference (make-F 'x) (make-F 'y)))
;                   _ (assert (Intersection? i))]
;               (apply In (:types i)))
;             (RClass-of Number)))
;
;  (is-clj (overlap (make-F 'x)
;                   (-difference -any (make-F 'y))))
;  (is-clj (overlap (B-maker 0)
;                   (-difference -any (B-maker 1))))
;  (is-clj (not (subtype? (B-maker 0)
;                         (-difference -any (B-maker 1)))))
;  (is-clj (not= (-difference (make-F 'x)
;                             (make-F 'y))
;                (Un))))
;
;(deftest negative-filter-test
;  (is-tc-e ;need to instantiate negative types for now
;         (fn [a] 
;           ((inst a (U nil Number) nil)
;            (inst identity (U nil Number)) 
;            [1 nil]))
;         :expected
;         [(All [x y]
;               [[x -> Any :filters {:then (! y 0)}]
;                (Seqable x) -> (Seq (Difference x y))])
;          -> (Seqable Number)]))
  #_(is-tc-e (let [filter (ann-form filter
                                  (All [x y]
                                       [[x -> Any :filters {:then (! y 0)}] 
                                        (U nil (Seqable x)) -> (Seq (Difference x y))]))]
             (filter (inst identity (U nil Number)) [1 nil]))
           :expected (Seqable Number))
