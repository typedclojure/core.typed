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
           
(deftest do-report-test
  (is-tc-e  (do-report 1)  t/Any
             :requires [[clojure.test :refer [do-report]]]))
           
(deftest runTest-test
  (is-tc-e  #(run-tests 'clojure.core.typed.test.abc) (Map Any Any)
             :requires [[clojure.test :refer [run-tests]]]))     

(deftest successful?-test
  (is-tc-e  (successful? 1) Boolean
             :requires [[clojure.test :refer [successful?]]]))



