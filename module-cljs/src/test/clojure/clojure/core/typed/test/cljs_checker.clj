(ns clojure.core.typed.test.cljs-checker
  (:require [clojure.core.typed.test.cljs-utils :refer :all]
            [clojure.test :refer :all]
            [cljs.core.typed :as t]
            [clojure.core.typed.type-rep :as r]
            [clojure.core.typed.subtype :as sub]
            [clojure.core.typed.analyze-cljs :as ana]
            [clojure.core.typed.check-cljs :as chk]
            [clojure.core.typed.test.cljs-utils :refer :all]
            [clojure.core.typed.utils :as u :refer [expr-type]]))

;;Testing the exhaustivity of the checker in terms of AST nodes
;;Specs of AST is at typedclojure/clojurescript/spec/quickref.html

(defn form->ast [form]
  (ana/ast-for-form form {:expected nil :eval-fn false}))

;;Alphabetical order

(defn node-t [node]
  (:t (expr-type node)))

(defn form-checked-type [form]
  (node-t (chk/check (form->ast form))))

(def f-c-t form-checked-type)

(defn is-t [x]
  (is x true))

(deftest binding-test
  (is-t (r/Value? (f-c-t 1)))
  )



;;;;;;;;;;;;;

(deftest ast-nodes-test
  (t/check-ns* 'cljs.core.typed.test.ympbyc.ast-nodes))
