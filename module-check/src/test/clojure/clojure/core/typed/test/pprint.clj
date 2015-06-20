(ns clojure.core.typed.test.pprint
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]))

(deftest cl-format-test
  (is-tc-e   #(cl-format true "abc" ) [-> Any]
             :requires [[clojure.pprint :refer [cl-format]]])
  (is-tc-err   (cl-format "abc" "abc" ) Any
             :requires [[clojure.pprint :refer [cl-format]]])
  (is-tc-err   (cl-format true true ) Any
             :requires [[clojure.pprint :refer [cl-format]]]))

(deftest fresh-line-test
  (is-tc-e   (fresh-line) Any
             :requires [[clojure.pprint :refer [fresh-line]]]))
 
(deftest get-pretty-writer-test
  (is-tc-e   (get-pretty-writer 1 ) Any
             :requires [[clojure.pprint :refer [get-pretty-writer]]])) 

(deftest pprint-test
   (is-tc-e   (pprint 1 ) Any
             :requires [[clojure.pprint :refer [pprint]]]))

 
