(ns clojure.core.typed.test.overlap
  (:require [clojure.test :refer :all]
            [clojure.core.typed.test.test-utils :refer :all]
            [clojure.core.typed :refer [Kw HVec Num Str Int
                                        HMap] :as t]
            [clojure.core.typed.type-ctors :refer :all]
            [clojure.core.typed.type-rep :refer :all]
            [clojure.core.typed.parse-unparse :refer [parse-type]]))

(defmacro overlap-prs [s1 s2]
  `(clj
     (overlap (parse-type ~s1) (parse-type ~s2))))

(deftest overlap-test
  (is-clj (not (overlap -false -true)))
  (is-clj (not (overlap (-val :a) (-val :b))))
  (is-clj (overlap (RClass-of Number) (RClass-of Integer)))
  (is-clj (not (overlap (RClass-of Number) (RClass-of clojure.lang.Symbol))))
  (is-clj (not (overlap (RClass-of Number) (RClass-of String))))
  (is-clj (overlap (RClass-of clojure.lang.Seqable [-any]) (RClass-of clojure.lang.IMeta)))
  (is-clj (overlap (RClass-of clojure.lang.Seqable [-any]) (RClass-of clojure.lang.PersistentVector [-any]))))

(deftest hmap-overlap-test
  (is-clj
    (not (overlap-prs `Int `Kw)))
  (is-clj
    (not
      (overlap-prs
        `(HMap :mandatory {:a Int})
        `(HMap :mandatory {:a Kw}))))
  (is-clj
    (overlap-prs
      `(HMap :optional {:a Int})
      `(HMap :optional {:a Kw})))
  (is-clj
    (overlap-prs
      `(HMap :complete? true :optional {:a Int})
      `(HMap :complete? true :optional {:a Kw}))))

(deftest hvec-overlap-test
  (testing "without rest types"
    (testing "when the fixed types match"
      (is-clj
       (overlap-prs
        `(HVec [Num])
        `(HVec [Num]))))

    (testing "when the fixed types differ"
      (is-clj
       (not
        (overlap-prs
         `(HVec [Num])
         `(HVec [Str])))))

    (testing "with a differing number of fixed types"
      (is-clj
       (not
        (overlap-prs
         `(HVec [Num])
         `(HVec [Num Str]))))))

  (testing "with one rest type"
    (testing "when fixed types match"
      (is-clj
       (overlap-prs
        `(HVec [Num])
        `(HVec [Num Str ~'*]))))

    (testing "when fixed types differ"
      (is-clj
       (not
        (overlap-prs
         `(HVec [Num])
         `(HVec [Str Str ~'*])))))

    (testing "when the extra fixed types match the rest type"
      (is-clj
       (overlap-prs
        `(HVec [Num ~'*])
        `(HVec [Num]))))

    (testing "when the extra fixed types differ from the rest type"
      (is-clj
       (not
        (overlap-prs
         `(HVec [Num ~'*])
         `(HVec [Str])))))

    (testing "when the extra fixed types come from type with the rest type"
      (is-clj
       (not
        (overlap-prs
         `(HVec [Str Str Str ~'*])
         `(HVec [Str]))))))

  (testing "with two rest types"
    (testing "when the rest types match"
      (is-clj
       (overlap-prs
        `(HVec [Num ~'*])
        `(HVec [Num ~'*]))))

    (testing "when the rest types differ"
      (is-clj
       (not
        (overlap-prs
         `(HVec [Num ~'*])
         `(HVec [Str ~'*])))))

    (testing "when the extra fixed types match the rest type of shorter"
      (is-clj
       (overlap-prs
        `(HVec [Num ~'*])
        `(HVec [Num Num ~'*]))))

    (testing "when the extra fixed types differ from the rest type of shorter"
      (is-clj
       (not
        (overlap-prs
         `(HVec [Num ~'*])
         `(HVec [Str Num ~'*])))))

    (testing "when the fixed types match"
      (is-clj
       (overlap-prs
        `(HVec [Num Str ~'*])
        `(HVec [Num Str ~'*]))))

    (testing "when the fixed types differ"
      (is-clj
       (not
        (overlap-prs
         `(HVec [Num Str ~'*])
         `(HVec [Str Str ~'*])))))))

(deftest hvec-complex-overlap
  (is-clj (overlap-prs `(HVec [Int Num])
                       `(HVec [Num Int]))))
