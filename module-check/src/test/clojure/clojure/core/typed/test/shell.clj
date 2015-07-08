(ns clojure.core.typed.test.shell
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]
             [clojure.core.typed.test.destructure]))

(deftest sh-test
  (is-tc-e   (sh "ls" ) (Map Any Any)
             :requires [[clojure.java.shell :refer [sh]]])
  (is-tc-err   (sh "ls" )  String
             :requires [[clojure.java.shell :refer [sh]]])
  (is-tc-err  (sh 1 ) (Map Any Any)
             :requires [[clojure.java.shell :refer [sh]]]))
