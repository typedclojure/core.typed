(ns clojure.core.typed.test.mainnew
  (:require  [clojure.core.typed :as t] 
             [clojure.test :refer :all]                
             [clojure.core.typed.test.test-utils :refer :all]))

(deftest demunge-test
  (is-tc-e (demunge "abc" ) String 
             :requires [[clojure.main :refer [demunge]]])
  (is-tc-err (demunge "abc" ) Boolean
             :requires [[clojure.main :refer [demunge]]])
  (is-tc-err (demunge 1 ) String 
             :requires [[clojure.main :refer [demunge]]]))

(deftest repl-prompt-test
  (is-tc-e #(repl-prompt) [-> Any] 
             :requires [[clojure.main :refer [repl-prompt]]]))

(deftest repl-test
  (is-tc-e #(repl) [-> Any] 
             :requires [[clojure.main :refer [repl]]]))

(deftest main-test
  (is-tc-e #(main) [-> nil] 
             :requires [[clojure.main :refer [main]]]))


