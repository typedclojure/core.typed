(ns clojure.core.typed.test.analyzer2-jvm
  (:require [clojure.test :refer :all]
            [clojure.core.typed.analyzer2.pre-analyze :as pre]
            [clojure.core.typed.analyzer2.jvm.pre-analyze :as jpre]
            [clojure.core.typed.analyzer2.jvm :as ana]
            [clojure.core.typed.analyze-clj :as anaclj]
            [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]
            [clojure.tools.analyzer.jvm :as taj]
            [clojure.tools.analyzer.env :as env]
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

;; how to interleave checking and analysis?
(defn check* [ast expected {:keys [pre post] :as opts}]
  (case (:op ast)
    :unanalyzed (check* (pre ast) expected opts)
    :do (let [ast (-> ast
                      (update :statements (fn [statements]
                                            (mapv #(check* % nil opts) statements)))
                      (update :ret #(check* % expected opts))
                      post)]
          (assoc ast :expr-type (-> ast :ret :expr-type)))
    :const (post (assoc ast :expr-type `(Value ~(:val ast))))
    :new (let [ast (-> ast
                       (update :class #(check* % nil opts))
                       (update :args #(mapv (fn [a] (check* a nil opts)) %))
                       post)]
           ast)
    :maybe-class (let [ast (post ast)]
                   ast)
    :host-call (let [ast (-> ast
                             (update :target #(check* % nil opts))
                             (update :args #(mapv (fn [a] (check* a nil opts)) %))
                             post)]
                 ast)
    :host-interop (let [_ (assert (empty? (:args ast)))
                        ast (-> ast
                                (update :target #(check* % nil opts))
                                post)]
                    ast)
    :let (let [ast (update ast :bindings (fn [statements]
                                           (mapv #(check* % nil opts) statements)))
               ast (update :body #(check* % expected opts))
               ast (post ast)]
          (assoc ast :expr-type (-> ast :body :expr-type)))
    ))

(defn check [form expected]
  (with-bindings (anaclj/thread-bindings)
    (env/ensure (taj/global-env)
      (check* (pre/pre-analyze-child form (taj/empty-env)) expected
              ana/scheduled-default-passes))))

(comment
        (check 1 nil)
        (keys (check '(.toString 1) nil))
        (keys (check '(.compareTo (java.io.File. "a") (java.io.File. "a")) nil))
        )
