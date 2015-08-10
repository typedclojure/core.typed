(ns clojure.core.typed.test.zip
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]))

(deftest zipper-test
   (is-tc-e (zipper vector? seq (fn [_ c] c) "abc") (Vec Any)
	     :requires[[clojure.zip :refer [zipper]]])
   (is-tc-err (zipper vector? seq (fn [_ c] c) "abc") String
	     :requires[[clojure.zip :refer [zipper]]]))
	    
(deftest seq-zip-test
   (is-tc-e (seq-zip "abc") (Vec Any)
	     :requires[[clojure.zip :refer [seq-zip]]])
   (is-tc-err (seq-zip "abc") String
	     :requires[[clojure.zip :refer [seq-zip]]]))

(deftest vector-zip-test
   (is-tc-e (vector-zip "abc") (Vec Any)
	     :requires[[clojure.zip :refer [vector-zip]]])
   (is-tc-err (vector-zip "abc") String
	     :requires[[clojure.zip :refer [vector-zip]]]))

(deftest xml-zip-test
   (is-tc-e   (xml-zip 1) (Vec Any)
	     :requires[[clojure.zip :refer [xml-zip]]])
   (is-tc-err (xml-zip 1) String
	     :requires[[clojure.zip :refer [xml-zip]]]))

(deftest node-test
   (is-tc-e   (node [1 2 3]) Any
	     :requires[[clojure.zip :refer [node]]])
   (is-tc-err (node 1) Any
	     :requires[[clojure.zip :refer [node]]]))

(deftest branch?-test
   (is-tc-e (branch? (vector-zip [1 2])) Boolean
	     :requires[[clojure.zip :refer [branch?]]
		       [clojure.zip :refer [vector-zip]]])
   (is-tc-err (branch? (vector-zip [1 2])) String
	     :requires[[clojure.zip :refer [branch?]]
		       [clojure.zip :refer [vector-zip]]]))

(deftest children-test
   (is-tc-e (children (vector-zip [1 2])) Any
	     :requires[[clojure.zip :refer [children]]
		       [clojure.zip :refer [vector-zip]]]))






