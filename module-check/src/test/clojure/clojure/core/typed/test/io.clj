(ns clojure.core.typed.test.io
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]
             [clojure.core.typed.test.destructure]))

(deftest delete-file-test
  (is-tc-e   #(delete-file "abc" ) [-> Boolean]
             :requires [[clojure.java.io :refer [delete-file]]])
  (is-tc-err   (delete-file "abc" ) String
             :requires [[clojure.java.io :refer [delete-file]]])
  (is-tc-err   (delete-file 1 ) Boolean
             :requires [[clojure.java.io :refer [delete-file]]]))

  
