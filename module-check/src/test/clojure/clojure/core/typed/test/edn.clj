(ns clojure.core.typed.test.edn
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]
             [clojure.core.typed.test.destructure]))

(deftest read-string-test
  (is-tc-e   (read-string "abc" ) (U nil Symbol Long)
             :requires [[clojure.edn :refer [read-string]]])
  (is-tc-err   (read-string "abc" ) String
             :requires [[clojure.edn :refer [read-string]]])
  (is-tc-err   (read-string 1 ) (U nil Symbol Long)
             :requires [[clojure.edn :refer [read-string]]]))
  
