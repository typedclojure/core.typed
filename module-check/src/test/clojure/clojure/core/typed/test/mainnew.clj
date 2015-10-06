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
           
(deftest load-script-test
  (is-tc-e #(load-script "sample.clj" ) [-> Any] 
             :requires [[clojure.main :refer [load-script]]])
  (is-tc-err (load-script 1 ) Any
             :requires [[clojure.main :refer [load-script]]]))

(deftest repl-caught-test
  (is-tc-e (repl-caught (Exception. "a")) Any 
             :requires [[clojure.main :refer [repl-caught]]])
  (is-tc-err (repl-caught "A") Any
             :requires [[clojure.main :refer [repl-caught]]]))

(deftest repl-exception-test
  (is-tc-e (repl-exception (Exception. "a")) Any 
             :requires [[clojure.main :refer [repl-exception]]])
  (is-tc-err (repl-exception "A") Any
             :requires [[clojure.main :refer [repl-exception]]]))

(deftest root-cause-test
  (is-tc-e (root-cause (Exception. "a")) Exception 
             :requires [[clojure.main :refer [root-cause]]])
  (is-tc-err (root-cause "A") Exception
             :requires [[clojure.main :refer [root-cause]]])
  (is-tc-err (root-cause (Exception. "a")) String
             :requires [[clojure.main :refer [root-cause]]]))




