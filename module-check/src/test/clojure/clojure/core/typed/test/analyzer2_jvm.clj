(ns clojure.core.typed.test.analyzer2-jvm
  (:require [clojure.test :refer :all]
            [clojure.core.typed.analyzer2.pre-analyze :as pre]
            [clojure.core.typed.analyzer2.jvm :as ana]
            [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]
            [clojure.tools.analyzer.jvm :as taj]
            [clojure.tools.analyzer.jvm.utils :as ju]))

(defmacro ast' [form]
  `(ana/analyze '~form))

(defmacro ast [form]
  `(ana/analyze+eval '~form))

(deftest analyzer-test
  (is (= 1
         (:result (ast 1))))
  (is (= 2 
         (:result (ast (-> 1 inc)))))
  (is (= 1
         (:result (ast (let [a 1] a)))))
  (is (= 1
         (:result (ast (loop [a 1] a)))))
  (is (= 1
         (:result (ast (do (def a 1)
                           a)))))
  (is (= 1
         (:result (ast (do (deftype Abc [a])
                           (.a (->Abc 1)))))))
  (is (= true
         (:result (ast (do (ns foo) (= 1 1))))))
  (is (= "a"
         (:result (ast (.toString (reify Object (toString [this] "a")))))))
  (is (= 2 (:result (ast (#(inc %) 1)))))
  (is (->
        (ast (do (ns bar
                   (:require [clojure.core.typed :as t]))
                 (t/ann-form 'foo 'a)))
        :ret))
  (is (not= :maybe-class (:op (ast Number))))
  )

(deftest async-test
  (is (-> (ast (do (ns asdfasdf
                     (:require [clojure.core.async :as a]
                               [clojure.core.typed.async :refer [go chan]]))
                   #(go)))
          :result)))

;; FIXME uncomment when frozen macros are back up and running
#_
(deftest frozen-macros-test
  (is (binding [ana/frozen-macros #{'clojure.core/doseq}]
        (= :frozen-macro (:op (ast' (doseq [a []]))))))
  (is (binding [ana/frozen-macros #{#_'clojure.core/doseq}]
        (not= :frozen-macro (:op (ast' (doseq [a []]))))))
  (is (binding [ana/frozen-macros #{'clojure.core/doseq}]
        (not= :frozen-macro
              (:op 
                (ana/thaw-frozen-macro
                  (ast' (doseq [a []])))))))
  (let [frozen (binding [ana/frozen-macros #{'clojure.core/doseq}]
                 (ast' (doseq [a [(-> 1 identity)]]
                         (-> a identity))))
        env (:env frozen)
        [_ bindings body-form :as frozen-form] (:form frozen)
        ;; TODO how to uniquify?
        dummy-bindings (into {}
                             (map (fn [[b _]]
                                    (when (symbol? b)
                                      [b {:op    :binding
                                          :env   env
                                          :form  b
                                          :local :fn
                                          :name  b}])))
                             (partition 2 bindings))
        body-env (update env :locals merge dummy-bindings)
        thawed-body (ana/thaw-form body-form body-env)
        ;_ (prn thawed-body)
        thawed-body-form (emit-form thawed-body)
        ]
    (is (= thawed-body-form '(identity a)))))

(deftest deftype-test
  (is (some?
        (binding [*ns* *ns*]
          (eval `(ns ~(gensym)))
          (ast
            (deftype A []
              Object
              (toString [_] (A.) "a")))))))

(deftest uniquify-test
  (let [ret (ast' (let [a 1]
                    (let [a 2]
                      a)))]
    (is (= (let [sym (-> ret :body :ret :bindings first :name)]
             (is (symbol? sym))
             sym)
           (-> ret :body :ret :body :ret :name)))
    (is (not= 'a (-> ret :body :ret :body :ret :name)))))
