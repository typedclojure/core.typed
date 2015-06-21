(ns clojure.core.typed.test.testnew
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]))

(deftest function?-test
  (is-tc-e   (function? function?) Boolean
             :requires [[clojure.test :refer [function?]]])
  (is-tc-err   (function? function?) String
             :requires [[clojure.test :refer [function?]]]))
  
(deftest assert-any-test
  (is-tc-e   (assert-any "Hi" (= 4(+ 2 2) )) Any
             :requires [[clojure.test :refer [assert-any]]]))
         
(deftest is-test
  (is-tc-e ( is (= 4 (+ 2 2))) Boolean))



