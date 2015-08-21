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

(deftest root-test
  (is-tc-e (root [1 2]) Any
	     :requires[[clojure.zip :refer [root]]])
   (is-tc-err (root 1) Any
	     :requires[[clojure.zip :refer [root]]]))

(deftest rightmost-test
  (is-tc-e (rightmost [1 2 3]) (Vec Any)
            :requires[[clojure.zip :refer [rightmost]]])
  (is-tc-err (rightmost [1 2 3]) String
            :requires[[clojure.zip :refer [rightmost]]])
  (is-tc-err (rightmost 1) (Vec Any)
            :requires[[clojure.zip :refer [rightmost]]]))

(deftest right-test
  (is-tc-e (right [1 2 3]) (U nil Any)
            :requires[[clojure.zip :refer [right]]])
  (is-tc-err (right [1 2 3]) String
            :requires[[clojure.zip :refer [right]]])
  (is-tc-err (right 1) (U nil Any)
            :requires[[clojure.zip :refer [right]]]))
         
(deftest up-test
   (is-tc-e (up (vector-zip [1 2])) (U nil (Vec Any))
	     :requires[[clojure.zip :refer [up]]
		       [clojure.zip :refer [vector-zip]]])
   (is-tc-err (up (vector-zip [1 2])) String
	     :requires[[clojure.zip :refer [up]]
		       [clojure.zip :refer [vector-zip]]]))

(deftest rights-test
  (is-tc-e (rights [1 2 3]) (U nil Any)
            :requires[[clojure.zip :refer [rights]]])
  (is-tc-err (rights [1 2 3]) String
            :requires[[clojure.zip :refer [rights]]])
  (is-tc-err (rights 1) (U nil Any)
            :requires[[clojure.zip :refer [rights]]]))
           
(deftest replace-test
   (is-tc-e (replace (vector-zip [1 2 [3 4] 5]) 3)  (Vec Any)
	     :requires[[clojure.zip :refer [replace]]
		       [clojure.zip :refer [vector-zip]]])
   (is-tc-err (replace (vector-zip [1 2 [3 4] 5]) 3)  String
	     :requires[[clojure.zip :refer [replace]]
		       [clojure.zip :refer [vector-zip]]])
   (is-tc-err (replace 1 3)  (Vec Any)
	     :requires[[clojure.zip :refer [replace]]
		       [clojure.zip :refer [vector-zip]]]))

(deftest up-test
   (is-tc-e (up [1 2 [3 4] 5] )  (U nil (Vec Any))
	     :requires[[clojure.zip :refer [up]]])
   (is-tc-err (up [1 2 [3 4] 5] )  String
	     :requires[[clojure.zip :refer [up]]])
   (is-tc-err (up 1 )  (U nil (Vec Any))
	     :requires[[clojure.zip :refer [up]]]))

(deftest down-test
   (is-tc-e (down (zipper vector? seq 1 [1 3 4 ])) (U nil(Vec Any))
	     :requires[[clojure.zip :refer [zipper]]
                       [clojure.zip :refer [down]]])
   (is-tc-err (down (zipper vector? seq 1 [1 3 4 ]))  String
	     :requires[[clojure.zip :refer [zipper]]
                       [clojure.zip :refer [down]]])
   (is-tc-err (down 1) (U nil(Vec Any))
	     :requires[[clojure.zip :refer [down]]]))

(deftest left-test
   (is-tc-e (left [1 2 [3 4] 5] )  (U nil (Vec Any))
	     :requires[[clojure.zip :refer [left]]])
   (is-tc-err (left [1 2 [3 4] 5] )  String
	     :requires[[clojure.zip :refer [left]]])
   (is-tc-err (left 1 )  (U nil (Vec Any))
	     :requires[[clojure.zip :refer [left]]]))

(deftest leftmost-test
   (is-tc-e (leftmost [1 2 [3 4] 5] )  (U nil (Vec Any))
	     :requires[[clojure.zip :refer [leftmost]]])
   (is-tc-err (leftmost [1 2 [3 4] 5] )  String
	     :requires[[clojure.zip :refer [leftmost]]])
   (is-tc-err (leftmost 1 )  (U nil (Vec Any))
	     :requires[[clojure.zip :refer [leftmost]]]))

(deftest lefts-test
   (is-tc-e (lefts [1 2 [3 4] 5] )  (U nil (Vec Any))
	     :requires[[clojure.zip :refer [lefts]]])
   (is-tc-err (lefts [1 2 [3 4] 5] )  String
	     :requires[[clojure.zip :refer [lefts]]])
   (is-tc-err (lefts 1 )  (U nil (Vec Any))
	     :requires[[clojure.zip :refer [lefts]]]))
	    
(deftest append-child-test
(is-tc-e (append-child (vector-zip [1 2]) 9) (Vec Any)	     
                 :requires[[clojure.zip :refer [append-child]]
		           [clojure.zip :refer [vector-zip]]])
(is-tc-err (append-child (vector-zip [1 2]) 9) String	     
                 :requires[[clojure.zip :refer [append-child]]
		           [clojure.zip :refer [vector-zip]]]))
(is-tc-err (append-child (vector-zip [1 2]) 9 ) (Vec Any)	     
                 :requires[[clojure.zip :refer [append-child]]
		           [clojure.zip :refer [vector-zip]]]))

