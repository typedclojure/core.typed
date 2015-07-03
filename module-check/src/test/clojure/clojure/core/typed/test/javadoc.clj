(ns clojure.core.typed.test.javadoc
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]
             [clojure.core.typed.test.destructure]))

(deftest add-local-javadoc-test
  (is-tc-e (add-local-javadoc 1) List
             :requires [[clojure.java.javadoc :refer [add-local-javadoc]]])
  (is-tc-err (add-local-javadoc 1) String
             :requires [[clojure.java.javadoc :refer [add-local-javadoc]]]))

(deftest add-remote-javadoc-test
  (is-tc-e (add-remote-javadoc "org.apache.commons.csv." "http://commons.apache.org/proper/commons-csv/apidocs/index.html") clojure.lang.PersistentTreeMap
             :requires [[clojure.java.javadoc :refer [add-remote-javadoc]]])
  (is-tc-err (add-remote-javadoc "org.apache.commons.csv." "http://commons.apache.org/proper/commons-csv/apidocs/index.html") String
             :requires [[clojure.java.javadoc :refer [add-remote-javadoc]]]) 
  (is-tc-err (add-remote-javadoc 1 "http://commons.apache.org/proper/commons-csv/apidocs/index.html") clojure.lang.PersistentTreeMap
             :requires [[clojure.java.javadoc :refer [add-remote-javadoc]]]))

(deftest javadoc-test
  (is-tc-e (defn a [](javadoc 1)) Boolean
             :requires [[clojure.java.javadoc :refer [javadoc]]])
  (is-tc-err (javadoc 1) String
             :requires [[clojure.java.javadoc :refer [javadoc]]]))


  
