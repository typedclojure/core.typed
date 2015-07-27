(ns clojure.core.typed.test.walk
	(:require  	[clojure.core.typed :as t] 
             
			[clojure.test :refer :all]                
             
			[clojure.core.typed.test.test-utils :refer :all]))


(deftest keywordize-keys-test
(is-tc-e (keywordize-keys {"a" 1 "b" 2}) Any             
	:requires [[clojure.walk :refer [keywordize-keys]]]))



(deftest macroexpand-all-test
(is-tc-e (macroexpand-all '(-> c (+ 3) (* 2))) Any           
	:requires [[clojure.walk :refer [macroexpand-all]]]))



(deftest postwalk-test
(is-tc-e (postwalk #(if(keyword? %)(keyword (name %)) %) {:page/tags [{:tag/category "lslsls"}]}) Any           
	:requires [[clojure.walk :refer [postwalk]]]))



(deftest postwalk-demo-test
(is-tc-e #(postwalk-demo [[1 2] [3 4 [5 6]] [7 8]]) [-> Any]           
	:requires [[clojure.walk :refer [postwalk-demo]]]))


(deftest postwalk-replace-test
(is-tc-e (postwalk-replace {:a 1 :b 2} [:a :b]) Any           
	:requires [[clojure.walk :refer [postwalk-replace]]])
(is-tc-err (postwalk-replace 1 [:a :b]) Any           
	:requires [[clojure.walk :refer [postwalk-replace]]]))


(deftest prewalk-test
(is-tc-e (prewalk #(if(keyword? %)(keyword (name %)) %) {:page/tags [{:tag/category "lslsls"}]}) Any           
	:requires [[clojure.walk :refer [prewalk]]]))



(deftest prewalk-demo-test
  
(is-tc-e #(prewalk-demo [[1 2] [3 4 [5 6]] [7 8]]) [-> Any]           
	:requires [[clojure.walk :refer [prewalk-demo]]])
)

(deftest prewalk-replace-test
(is-tc-e (prewalk-replace {:a 1 :b 2} [:a :b]) Any           
	:requires [[clojure.walk :refer [prewalk-replace]]])
(is-tc-err (prewalk-replace 1 [:a :b]) Any           
	:requires [[clojure.walk :refer [prewalk-replace]]]))

(deftest stringify-keys-test
(is-tc-e (stringify-keys {:a 1 :b 2}) Any            
	:requires [[clojure.walk :refer [stringify-keys]]]))

(deftest walk-test
(is-tc-e (walk first reverse [[1 2] [3 4] [5 6]] ) (List Any)           
	:requires [[clojure.walk :refer [walk]]])
(is-tc-err (walk first reverse [[1 2] [3 4] [5 6]] ) String          
	:requires [[clojure.walk :refer [walk]]])
(is-tc-err (walk first reverse 1 ) (List Any)           
	:requires [[clojure.walk :refer [walk]]]))
