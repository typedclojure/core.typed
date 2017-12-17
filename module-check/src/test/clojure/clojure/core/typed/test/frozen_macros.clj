(ns clojure.core.typed.test.frozen-macros
  (:require 
    ; this loads the type system, must go first
    [clojure.core.typed.test.test-utils :refer :all]
    [clojure.test :refer :all]
    [clojure.core.typed.analyzer2.pre-analyze :as pre]
    [clojure.core.typed.analyzer2.jvm :as ana]
    [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]
    [clojure.tools.analyzer.jvm :as taj]
    [clojure.tools.analyzer.jvm.utils :as ju]))

(deftest ns-test
  (is-tc-e (ns foo)))

(deftest ann-form-test
  (is-tc-e (ann-form 1 Integer))
  (is-tc-err (ann-form 1 nil)))
