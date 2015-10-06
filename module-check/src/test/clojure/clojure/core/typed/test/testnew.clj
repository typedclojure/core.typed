(ns clojure.core.typed.test.testnew
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]
             [clojure.core.typed.test.destructure]))

(deftest function?-test
  (is-tc-e (function? function?) Boolean
             :requires [[clojure.test :refer [function?]]])
  (is-tc-err (function? function?) String
             :requires [[clojure.test :refer [function?]]]))
  
(deftest assert-any-test
  (is-tc-e (assert-any "Hi" (= 4(+ 2 2) )) Any
             :requires [[clojure.test :refer [assert-any]]]))
           
(deftest do-report-test
  (is-tc-e (do-report 1)  Any
             :requires [[clojure.test :refer [do-report]]]))
            
(deftest run-tests-test
  	(is-tc-e #(run-tests)  [-> (t/Map t/Any t/Any)]
             :requires [[clojure.test :refer [run-tests]]])
        (is-tc-err (run-tests) String
             :requires [[clojure.test :refer [run-tests]]]))
            
(deftest run-all-tests-test
  	(is-tc-e #(run-all-tests)  [-> (t/Map t/Any t/Any)]
             :requires [[clojure.test :refer [run-all-tests]]])
        (is-tc-err (run-all-tests) String
             :requires [[clojure.test :refer [run-all-tests]]]))
            
(deftest successful?-test
  (is-tc-e (successful? 1) Boolean
             :requires [[clojure.test :refer [successful?]]]))
            
(deftest compose-fixtures-test
  	(is-tc-e (compose-fixtures (fn a [](+ 2 1)) (fn c [](+ 1 2) ) ) Any
             :requires [[clojure.test :refer [compose-fixtures]]]))
           
(deftest testing-vars-str-test
  	(is-tc-e (testing-vars-str 1 )  String
             :requires [[clojure.test :refer [testing-vars-str]]])
	  (is-tc-err (testing-vars-str 1 ) (Map Any Any)
             :requires [[clojure.test :refer [testing-vars-str]]]))
           
(deftest testing-contexts-str-test
  	(is-tc-e (testing-contexts-str)  String
             :requires [[clojure.test :refer [testing-contexts-str]]])
	  (is-tc-err (testing-contexts-str) (Map Any Any)
             :requires [[clojure.test :refer [testing-contexts-str]]])
	  (is-tc-err (testing-contexts-str 1)  String
             :requires [[clojure.test :refer [testing-contexts-str]]]))

(deftest test-ns-test
  	(is-tc-e #(test-ns 'clojure.core.typed.test.destructure) [-> (t/Map t/Any t/Any)]
             :requires [[clojure.test :refer [test-ns]]]))
            
