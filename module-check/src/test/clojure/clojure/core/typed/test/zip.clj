(ns clojure.core.typed.test.zip
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]))


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







