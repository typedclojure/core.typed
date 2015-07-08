(ns clojure.core.typed.test.stacktrace
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]
             [clojure.core.typed.test.destructure]))

(deftest e-test
  (is-tc-e   ( e ) (U nil Any)
             :requires [[clojure.stacktrace :refer [e]]]))
