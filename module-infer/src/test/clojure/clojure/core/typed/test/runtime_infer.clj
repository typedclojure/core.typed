(ns clojure.core.typed.test.runtime-infer
  (:require [clojure.test :refer :all]
            [com.gfredericks.test.chuck :as chuck]
            [com.gfredericks.test.chuck.clojure-test :refer [checking]]
            [com.gfredericks.test.chuck.generators :as gen']
            [clojure.test.check.generators :as gen]
            [clojure.core.typed :as t]
            [clojure.core.typed.runtime-infer :refer :all]))

(defn add-tmp-aliases [env as]
  (update-alias-env env merge (zipmap as (repeat nil))))

(defmacro with-tmp-aliases [env as & body]
  `(binding [*envs* (atom (add-tmp-aliases ~env ~as))] 
     ~@body))

#_(defmacro with-type-and-alias-env 
  [t a & body]
  `(binding [*envs* 
             (atom {(current-ns)
                    {:type-env ~t
                     :alias-env ~a}})]
     ~@body))

(deftest union-test
  (is (= (make-Union [(prs Long)
                      (prs Double)])
         (prs Number)
         (make-Union [(prs Long)
                      (prs Double)
                      (prs Number)])
         )))

(deftest join-test
  (is (= (join* (prs String))
         (make-Union [(prs String)])
         (prs String)))
  (is (= (join* (prs Sym))
         (make-Union [(prs Sym)])
         (prs Sym)))
  (is (not= (prs Any)
            (prs (U Sym String))))
  ;;FIXME
  #_
  (is (=
       (prs (U '{:f [? :-> java.lang.Long], :a ?} 
               '{:f [? :-> java.lang.Long]}))
       (prs (HMap :mandatory {:f [? :-> java.lang.Long]} 
                  :optional {:a ?}))))
  ;;FIXME
  #_
  (is (=
       (join-HMaps
         (prs '{:f ':op1, :a Any})
         (prs '{:f ':op2, :a Any}))
       (join
         (prs '{:f ':op1, :a Any})
         (prs '{:f ':op2, :a Any}))
       (prs (U 
              '{:f ':op1, :a Any}
              '{:f ':op2, :a Any}))))
  (checking
    "join maps"
    5
    [ts (gen/shuffle
          [(prs
             '{:E ':false})
           (prs
             '{:args (Vec '{:name clojure.lang.Symbol, :E ':var}),
               :fun
               (U
                '{:E ':lambda,
                  :arg clojure.lang.Symbol,
                  :body '{:name clojure.lang.Symbol, :E ':var},
                  :arg-type
                  '{:T ':intersection, :types clojure.lang.PersistentHashSet}}
                '{:name clojure.lang.Symbol, :E ':var}),
               :E ':app})])]

    (is (= (apply join ts)
           (prs
             (U
              '{:E ':false}
              '{:args (Vec '{:name clojure.lang.Symbol, :E ':var}),
                :fun
                (U
                 '{:E ':lambda,
                   :arg clojure.lang.Symbol,
                   :body '{:name clojure.lang.Symbol, :E ':var},
                   :arg-type
                   '{:T ':intersection, :types clojure.lang.PersistentHashSet}}
                 '{:name clojure.lang.Symbol, :E ':var}),
                :E ':app})))))
  (checking
    "inner vec"
    5
    [ts (gen/shuffle
          [(prs (Vec '{:a ?}))
           (prs (Vec '{:b ?}))])]
    (is 
      (= (apply join* ts)
         (prs (Vec (U '{:a ?} '{:b ?}))))))
  (checking 
    "functions"
    30
    [ts (gen/shuffle
          [(prs '{:a ?})
           (prs '{:a [? :-> ?]})
           (prs '{:a [? :-> Long]})
           (prs '{:a [Long :-> Long]})])]
    (= (apply join* ts)
       (prs '{:a [Long :-> Long]})))
  (checking
    "HOF"
    5
    [ts (gen/shuffle
          [(prs '{:f ?, :a java.lang.Long}) 
           (prs '{:f [[? :-> java.lang.Long] :-> ?], :a ?})])]
    (is
      (= (apply join* ts)
         (prs '{:f [[? :-> java.lang.Long] :-> ?], :a java.lang.Long}))))
  (checking
    "map return"
    5
    [ts (gen/shuffle
          [(prs ['{:f ?, :a java.lang.Long} :-> '{:b ?, :f clojure.lang.IFn, :a ?}])
           (prs ['{:f [[? :-> java.lang.Long] :-> ?], :a ?} :-> ?])])]
    (is (= (apply join ts)
           (prs
             ['{:f [[? :-> java.lang.Long] :-> ?], :a java.lang.Long}
              :->
              '{:b ?, :f clojure.lang.IFn, :a ?}]))))
  (checking
    "join union"
    5
    [ts (gen/shuffle
          [(prs
             (U '{:f [? :-> java.lang.Long], :a ?} 
                '{:f clojure.lang.IFn}))
           (prs 
             '{:f [? :-> java.lang.Long]})])]
     (is (= (apply join ts)
            (prs
              (U '{:f [? :-> java.lang.Long], :a ?} 
                 '{:f [? :-> java.lang.Long]})))))
  (checking
    "join fn in map"
    5
    [ts (gen/shuffle
          [(prs '{:f [[java.lang.Long :-> java.lang.Long] :-> ?]})
           (prs '{:f [[java.lang.Long :-> java.lang.Long] :-> java.lang.Long]})])]
    (is (= (apply join ts)
           (prs '{:f [[java.lang.Long :-> java.lang.Long] :-> java.lang.Long]})))))

(deftest squash-test
  #_
  (let [config (init-config)
        env (init-env)
        env (update-alias-env env merge
                              (with-tmp-aliases env '[a1 a2]
                                {'a1 (prs '{:a a2})
                                 'a2 (prs '{:a nil})}))]
    (binding [*envs* (atom env)]
      (is (= (alias-env (squash env config (prs a1)))
             {'a1 (prs '{:a (U nil a1)})
              'a2 (prs a1)}))))
#_
  (let [aenv (with-tmp-aliases '[a1 a2 a3 a4]
               {'a1 (prs a2)
                'a2 (prs '{:a a3})
                'a3 (prs a4)
                'a4 (prs
                      '{:a nil})})]
    (with-type-and-alias-env 
      (type-env @*envs*)
      aenv
      (is (= (squash-all (prs a1))
             (prs a1)))
      (is (= (alias-env)
             (with-tmp-aliases '[a1 a2]
               {'a1 (prs '{:a (U nil a1)})
                'a2 (prs a1)
                'a3 (prs a2) ;;TODO <^v
                'a4 (prs a3)
                }))))))

;; testing only
(defn update-path' [env infer-results]
  (let [config (init-config)
        env (generate-tenv
              env
              config
              {:infer-results infer-results})]
    (type-env env)))

(deftest update-path-test
  (checking
    "update map"
    10
    [infers (gen/shuffle
              [(infer-result [(var-path 'use-map)
                              (key-path #{:a} :a)]
                             -unknown)
               (infer-result [(var-path 'use-map)
                              (key-path #{:a} :a)]
                             (-class Long []))])]
    (is (= (update-path' (init-env) infers)
           {'use-map (prs '{:a Long})})))
  (checking
    "update nested map"
    20
    [infers (gen/shuffle
              [(infer-result [(var-path 'use-map)]
                             (-class clojure.lang.IFn []))
               (infer-result [(var-path 'use-map)
                              (fn-rng-path 1)
                              (key-path #{:b :f :a} :f)]
                             (-class clojure.lang.IFn []))
               (infer-result [(var-path 'use-map)
                              (fn-dom-path 1 0)
                              (key-path #{:f :a} :a)]
                             (-class Long []))
               (infer-result [(var-path 'use-map)
                              (fn-dom-path 1 0)
                              (key-path #{:f :a} :f)
                              (fn-dom-path 1 0)
                              (fn-rng-path 1)]
                             (-class Long []))])]
    (is (= (update-path' (init-env) infers))
        {'use-map
         (prs ['{:f [[? :-> Long] :-> ?], :a java.lang.Long} :-> '{:b ?, :f clojure.lang.IFn, :a ?}])}))
  (checking
    "function dom rng"
    10
    [infers (gen/shuffle
              [(infer-result [(var-path 'foo) (fn-rng-path 1)]
                             (parse-type 'Long))
               (infer-result [(var-path 'foo) (fn-dom-path 1 0)]
                             (parse-type 'Long))])]
    (is (= (update (update-path' (init-env) infers) 'foo dissoc :top-level-def)
           {'foo (prs [Long :-> Long])})))
  (checking
    "unknown with function"
    10
    [infers (gen/shuffle
              [(infer-result [(var-path 'foo)] (prs ?))
               (infer-result [(var-path 'foo)] (prs [Long :-> ?]))])]
    (is (= (update (update-path' (init-env) infers) 'foo dissoc :top-level-def)
           {'foo (prs [java.lang.Long :-> ?])})))

  (checking
    "combine functions"
    10
    [ts (gen/shuffle
          [(prs [(U '{:f [? :-> java.lang.Long], :a ?} 
                    '{:f [? :-> java.lang.Long]}) :-> 
                 '{:b ?, :f ?, :a java.lang.Long}])
           (prs ['{:f clojure.lang.IFn, :a ?} :-> ?])])]

    (is
      (= (apply join ts)
         (prs
           [(U '{:f [? :-> java.lang.Long], :a ?} '{:f [? :-> java.lang.Long]})
            :->
            '{:b ?, :f ?, :a java.lang.Long}]))))

  (checking
    "IFn with fns"
    10
    [ts (gen/shuffle 
          [(prs (U '{:f [? :-> java.lang.Long], :a ?} 
                   '{:f [? :-> java.lang.Long]}))
           (prs '{:f clojure.lang.IFn, :a ?})])]
    (is
      (= (apply join ts)
         (prs (U '{:f [? :-> java.lang.Long], :a ?} 
                 '{:f [? :-> java.lang.Long]})))))
  
  ;;hardcoded, but now fails
  #_
  (checking
    "big"
    75
    [infers (gen/shuffle
              (mapv parse-infer-result
                    '[[[#'clojure.core.typed.runtime-infer/use-map (dom 1 0) (key #{:f} :f)]
                       :-
                       clojure.lang.IFn]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (dom 1 0)
                        (key #{:f :a} :f)
                        (rng 1)]
                       :-
                       java.lang.Long]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (rng 1)
                        (key #{:b :f :a} :a)]
                       :-
                       java.lang.Long]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (dom 1 0)
                        (key #{:f} :f)
                        (rng 1)]
                       :-
                       java.lang.Long]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (dom 1 0)
                        (key #{:f :a} :f)]
                       :-
                       clojure.lang.IFn]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (dom 1 0)
                        (key #{:f :a} :f)
                        (dom 1 0)]
                       :-
                       clojure.lang.IFn]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (dom 1 0)
                        (key #{:f} :f)
                        (dom 1 0)
                        (rng 1)]
                       :-
                       java.lang.Long]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (dom 1 0)
                        (key #{:f :a} :a)]
                       :-
                       java.lang.Long]
                      [[#'clojure.core.typed.runtime-infer/use-map] :- clojure.lang.IFn]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (dom 1 0)
                        (key #{:f} :f)
                        (dom 1 0)
                        (dom 1 0)]
                       :-
                       java.lang.Long]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (rng 1)
                        (key #{:b :f} :f)]
                       :-
                       clojure.lang.IFn]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (dom 1 0)
                        (key #{:f :a} :f)
                        (dom 1 0)
                        (dom 1 0)]
                       :-
                       java.lang.Long]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (dom 1 0)
                        (key #{:f :a} :f)
                        (dom 1 0)
                        (rng 1)]
                       :-
                       java.lang.Long]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (rng 1)
                        (key #{:b :f} :b)]
                       :-
                       java.lang.Long]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (rng 1)
                        (key #{:b :f :a} :f)]
                       :-
                       clojure.lang.IFn]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (dom 1 0)
                        (key #{:f} :f)
                        (dom 1 0)]
                       :-
                       clojure.lang.IFn]
                      [[#'clojure.core.typed.runtime-infer/use-map
                        (rng 1)
                        (key #{:b :f :a} :b)]
                       :-
                       java.lang.Long]]))]
    (is
      (= (update-path' (init-env) infers)
         {'clojure.core.typed.runtime-infer/use-map
          (prs
            [(U
              '{:f [[java.lang.Long :-> java.lang.Long] :-> java.lang.Long]}
              '{:f [[java.lang.Long :-> java.lang.Long] :-> java.lang.Long],
                :a java.lang.Long})
             :->
             (U
              '{:b java.lang.Long, :f clojure.lang.IFn, :a java.lang.Long}
              '{:b java.lang.Long, :f clojure.lang.IFn})])})))

#_
(is
(ppenv
  (update-path' {}
                (mapv parse-infer-result
'[[[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:name :E} :name)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :args)
   (index 2 0)
   (key #{:name :E} :E)]
  :-
  ':var]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:E :arg :body :arg-type} :body)
   (key #{:name :E} :name)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:E :arg :body :arg-type} :arg-type)
   (key #{:T :types} :types)]
  :-
  clojure.lang.PersistentHashSet]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:E :arg :body :arg-type} :body)
   (key #{:name :E} :E)]
  :-
  ':var]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:E :arg :body :arg-type} :arg)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :args)
   (index 1 0)
   (key #{:name :E} :name)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :E)]
  :-
  ':app]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :args)
   (index 1 0)
   (key #{:name :E} :E)]
  :-
  ':var]
 [[#'clojure.core.typed.test.mini-occ/parse-exp (dom 1 0)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp (dom 1 0)]
  :-
  clojure.lang.PersistentList]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:else :E :then :test} :then)
   (key #{:name :E} :E)]
  :-
  ':var]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :fun)
   (key #{:E :arg :body :arg-type} :body)
   (key #{:name :E} :name)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :args)
   (index 2 0)
   (key #{:name :E} :name)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:else :E :then :test} :else)
   (key #{:name :E} :E)]
  :-
  ':var]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:else :E :then :test} :test)
   (key #{:name :E} :name)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp] :- clojure.lang.IFn]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :fun)
   (key #{:name :E} :name)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :args)
   (index 2 1)
   (key #{:name :E} :E)]
  :-
  ':var]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:else :E :then :test} :test)
   (key #{:name :E} :E)]
  :-
  ':var]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :fun)
   (key #{:name :E} :E)]
  :-
  ':var]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :args)
   (index 2 1)
   (key #{:name :E} :name)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp (rng 1) (key #{:E} :E)]
  :-
  ':false]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:E :arg :body :arg-type} :arg-type)
   (key #{:T :types} :T)]
  :-
  ':intersection]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :fun)
   (key #{:E :arg :body :arg-type} :arg-type)
   (key #{:T :types} :T)]
  :-
  ':intersection]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:else :E :then :test} :E)]
  :-
  ':if]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:else :E :then :test} :else)
   (key #{:name :E} :name)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp (dom 1 0)] :- false]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :fun)
   (key #{:E :arg :body :arg-type} :E)]
  :-
  ':lambda]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :fun)
   (key #{:E :arg :body :arg-type} :body)
   (key #{:name :E} :E)]
  :-
  ':var]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:else :E :then :test} :then)
   (key #{:name :E} :name)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:name :E} :E)]
  :-
  ':var]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :fun)
   (key #{:E :arg :body :arg-type} :arg)]
  :-
  clojure.lang.Symbol]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:E :arg :body :arg-type} :E)]
  :-
  ':lambda]
 [[#'clojure.core.typed.test.mini-occ/parse-exp
   (rng 1)
   (key #{:args :fun :E} :fun)
   (key #{:E :arg :body :arg-type} :arg-type)
   (key #{:T :types} :types)]
  :-
  clojure.lang.PersistentHashSet]
]


  )))))

(deftest delete-generated-annotations-in-str-test
  (is (= (delete-generated-annotations-in-str
           (str "\n"
                generate-ann-start 
                "\n"
                "foo\n"
                generate-ann-end "\n"
                "bar\n\n"))
         "\nbar\n")))

#_(deftest group-arities-test
  (is (group-arities
        {:op :IFn, 
         :arities [{:op :IFn1, :dom [], :rng {:op :class, :class java.lang.Long, :args []}}]}
        {:op :IFn, :arities [{:op :IFn1, :dom [{:op :unknown}], :rng {:op :class, :class java.lang.Long, :args []}}]})))

(deftest squash-horizonally-test
  (is (let [config (init-config)
            env (as-> (init-env) env
                  (update-alias-env env
                                    assoc 
                                    'foo (prs '{:baz Long})
                                    'bar (prs '{:baz Boolean}))
                  (binding [*envs* (atom env)]
                    (update-type-env env
                                     assoc 
                                     `var1 (prs foo)
                                     `var2 (prs bar))))
            env (squash-horizonally env config)
            env (follow-all env (assoc config :simplify? false))]
        (pprint env)
        (= (get (type-env env) `var1)
           (get (type-env env) `var2)))))

(defmacro try-prim [invoke-args & body]
  (let [name (gensym)]
    `(do (defn ~name ~@body)
         (alter-var-root 
           (var ~name)
           (constantly
             (track-var ~name)))
         (~name ~@invoke-args))))

(deftest track-prim-fn
  (is (=
       :ok
       (try-prim
         [1]
         [^long a]
         :ok)))
  (is (=
       10
       (try-prim
         [1 'a]
         ^long [^long a ^Object b]
         10)))
  (is (=
       10
       (try-prim
         []
         ^long []
         10)))
  (is (=
       10.5
       (try-prim
         []
         ^double []
         10.5)))
  (is (=
       :ok
       (try-prim
         [1]
         (^double [] 10.5)
         (^Object [^long a] :ok))))
  (is (=
       10.5
       (try-prim
         []
         (^double [] 10.5)
         (^Object [^long a] :ok))))
  )

(deftest mini-occ-test
  (is 
    (do
      (require 'clojure.core.typed.test.mini-occ :reload)
      :ok)))

(deftest optional-keys-test
  (is 
    (= 
      (join-HMaps
        (prs
          (HMap :optional {:a Any}))
        (prs
          (HMap :optional {:a Any})))
      (prs
        (HMap :optional {:a Any}))))
  (is 
    (= 
      (join-HMaps
        (prs
          (HMap :optional {:a String}))
        (prs
          (HMap :mandatory {:a Long})))
      (prs
        (HMap :optional {:a (U String Long)}))))
  (is 
    (= 
      (join-HMaps
        (prs
          (HMap :mandatory {:op ':Foo}))
        (prs
          (HMap :mandatory {:op ':Foo}
                :optional {:bar String})))
      (prs
        (HMap :mandatory {:op ':Foo}
              :optional {:bar String}))))

  (is (=
       (HMap-req-keyset
         (prs
           (HMap :mandatory {:a Long})))
       #{:a}))
  (is (=
       (HMap-req-keyset
         (prs
           (HMap :optional {:a Long})))
       #{}))
  (is (=
       (HMap-req-keyset
         (prs
           (HMap :optional {:a Long}
                 :mandatory {:b Long})))
       #{:b}))
  (is (=
       (HMap-req-opt-keysets
         (prs
           (HMap :optional {:a Long}
                 :mandatory {:b Long})))
       #{{:req-keyset #{:b}, :opt-keyset #{:a}}}))
  (is (=
       (make-Union
         [(prs
            (HMap :mandatory {:op ':Foo}))
          (prs
            (HMap :mandatory {:op ':Foo}
                  :optional  {:opt String}))])
       (prs (HMap :mandatory {:op ':Foo}
                  :optional {:opt String}))))
  (is (=
       (make-Union
         [(prs
            (HMap :mandatory {:op ':Foo}
                  :optional {:opt Long}))
          (prs
            (HMap :optional {:op ':Foo
                             :opt String}))])
       (prs (HMap :optional {:op ':Foo
                             :opt (U Long String)}))))
  (is 
    (= 
      (join-HMaps
        (prs
          '{:op ':the-foo
            :the-bar Sym
            :opt Sym})
        (prs
          '{:op ':the-foo
            :the-bar Sym}))
      (prs
        (HMap :mandatory {:op ':the-foo
                          :the-bar Sym}
              :optional {:opt Sym}))))
)

(def ^:dynamic *print-anns* true)

(defn *-from-tenv [f tenv config]
  (let [ns (create-ns (gensym))]
    (binding [*ann-for-ns* (constantly ns)
              *ns* ns
              *debug* (if-let [[_ debug] (find config :debug)]
                        debug
                        *debug*)]
      ;; set up ns refers
      (refer-clojure)
      (require '[clojure.core.typed 
                 :as t 
                 :refer [defalias ann Str Any U Vec Map
                         Sym HMap Nothing]])
      (when spec-ns
        (require [spec-ns :as 's]))

      (let [_ (prn "Current ns:" (current-ns))
            env (as-> (init-env) env
                  (update-type-env env merge tenv))
            env (populate-envs env config)
            anns (f env config)]
        (when *print-anns*
          (pprint anns))))))

(defn anns-from-tenv [tenv & [config]]
  (*-from-tenv envs-to-annotations
               tenv
               (or config {})))

(defn specs-from-tenv [tenv & [config]]
  (*-from-tenv envs-to-specs
               tenv
               (merge config
                      {:spec? true})))

(let [st-type (prs
                '{:quads
                  (Vec
                    '{:klingons java.lang.Long,
                      :quadrant (Vec java.lang.Long),
                      :stars java.lang.Long,
                      :bases java.lang.Long}),
                  :stardate
                  '{:start java.lang.Long,
                    :current java.lang.Long,
                    :end java.lang.Long},
                  :current-klingons (Vec Nothing),
                  :starting-klingons java.lang.Long,
                  :lrs-history (Vec java.lang.String),
                  :current-sector (Vec java.lang.Long),
                  :enterprise
                  '{:photon_torpedoes java.lang.Long,
                    :sector (Vec java.lang.Long),
                    :quadrant (Vec (U java.lang.Integer java.lang.Long)),
                    :energy java.lang.Long,
                    :damage
                    '{:phasers java.lang.Long,
                      :warp_engines java.lang.Long,
                      :damage_control java.lang.Long,
                      :long_range_sensors java.lang.Long,
                      :short_range_sensors java.lang.Long,
                      :computer_display java.lang.Long,
                      :photon_torpedo_tubes java.lang.Long,
                      :shields java.lang.Long},
                    :is_docked false,
                    :shields java.lang.Long}})]
  (anns-from-tenv {'t1 st-type
                   't2 st-type}))

(let [t (prs
  [(U
    '{:exp '{:name Sym, :E ':var},
      :P ':is,
      :type '{:T ':intersection, :types (Set Nothing)}}
    '{:P ':not,
      :p
      '{:P ':=,
        :exps
        (Set
         (U
          '{:name Sym, :E ':var}
          '{:args (Vec '{:name Sym, :E ':var}),
            :fun '{:name Sym, :E ':var},
            :E ':app}))}}
    '{:P ':=,
      :exps
      (Set
       (U
        '{:name Sym, :E ':var}
        '{:args (Vec '{:name Sym, :E ':var}),
          :fun '{:name Sym, :E ':var},
          :E ':app}))}
    '{:P (U ':or ':and),
      :ps
      (Set
       (U
        '{:exp '{:name Sym, :E ':var},
          :P ':is,
          :type '{:T ':intersection, :types (Set Nothing)}
          :foo Sym}
        '{:P ':=,
          :exps
          (Set
           (U
            '{:name Sym, :E ':var}
            '{:args (Vec '{:name Sym, :E ':var}),
              :fun '{:name Sym, :E ':var},
              :E ':app}))}))})
   :->
   Any])]
(anns-from-tenv {;'unparse-prop1 t
                 'unparse-prop2 t}
                {:debug :iterations}))

(let [t (prs
  ['{:P ':or
     :ps
     (Set
       '{:P ':and
         :ps
         (Set
           '{:P ':Top})})}
   :->
   Any])]
(anns-from-tenv {;'unparse-prop1 t
                 'unparse-prop2 t}
                {:debug #{:iterations :squash}}))

(let [t (prs
  ['{:P ':or
     :ps
     (Set
       (U '{:P ':Top}
       '{:P ':and
         :ps
         (Set
           '{:P ':Top})}))}
   :->
   Any])]
(anns-from-tenv {;'unparse-prop1 t
                 'unparse-prop2 t}
                {:debug #{:iterations :squash}}))

(let [t (prs
  '{:P ':or
     :ps
     (Set
       '{:P ':and
         :ps
         (Set
           (U '{:P ':Top}
              '{:P ':Bottom}))})}
   )]
(anns-from-tenv {;'unparse-prop1 t
                 'unparse-prop2 t}
                {:debug #{:squash :iterations
                          :squash-horizontally}}))

;; collapse maps with completely disjoint keys
(let [t (prs
          [(U '{:entry1 String}
              '{:entry2 Boolean}
              '{:entry3 Boolean})
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

;; don't collapse common keys with keyword entry
(let [t (prs
          [(U '{:op :foo
                :entry1 String}
              '{:op :bar
                :entry2 Boolean}
              '{:op :baz
                :entry3 Boolean})
           :->
           Any])]
  (anns-from-tenv {'config-in t}
                  {:debug true}))

;; upcast Kw + HMap to Any
(let [t (prs
          [(U ':foo
              '{:op :bar
                :entry2 Boolean})
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

;; simplify keywords + seqables to Any
(let [t (prs
          [(U ':foo
              (clojure.lang.Seqable String))
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

;; simplify Sym/Kw + seqable to Any
(let [t (prs
          [(U Sym
              (clojure.lang.Seqable String))
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

;; don't simplify Seqable + nil
(let [t (prs
          [(U nil
              (clojure.lang.Seqable String))
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

;; use optional keys
(let [t (prs
          [(U '{:foo String}
              '{:foo String
                :bar Boolean})
           :->
           Any])]
  (anns-from-tenv {'config-in t}
                  {:debug true}))

;upcast union to Any
(let [t (prs
          [(U Any
              '{:foo String
                :bar Boolean})
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

; Kw simplification
(let [t (prs
          [(U ':foo ':bar)
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

; join on class arguments
(let [t (prs
          [(U (Vec Integer)
              (Vec Long))
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

; don't alias args implicitly
(let [t (prs
          [[Any :->  Any]
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

; upcast HMaps to Map if they appear in a union
(let [t (prs
          [(U '{:foo Any}
              (clojure.lang.IPersistentMap Any Any))
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

; upcast HMaps to Map if they appear in a union
(let [t (prs
          [(U '{:foo Any}
              (clojure.lang.IPersistentMap Any Any))
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

; optional HMaps test
(let [t (prs
          [(HMap :optional {:foo String})
           :->
           Any])]
  (anns-from-tenv {'config-in t}))

(let [t (prs
          [(U '{:op ':the-foo
                :the-bar Sym
                :opt Sym}
              '{:op ':the-foo
                :the-bar Sym})
           :->
           Any])]
  (anns-from-tenv {'config-in t}
                  {:debug true}))

; namespaced entry + spec
(let [t (prs
          ['{::op ':the-foo}
           :->
           Any])]
  (specs-from-tenv {'config-in t}))

;; TODO recursive example of this test
(let [t (prs
          [(U '{:op ':the-bar
                :the-foo String
                :the-baz String}
              '{:op ':the-foo
                :the-foo Sym
                :the-baz Sym})
           :->
           Any])]
  (anns-from-tenv {'config-in t}
                  {:debug true}))

; HMap alias naming test
(let [t (prs
          [
           '{:op ':foo
             :the-bar '{:op ':term
                        :val Sym}}
           :->
           Any])]
  ((juxt specs-from-tenv
         anns-from-tenv)
    {'config-in t}))

; recursive HMaps test
(let [t (prs
          [(U
           '{:op ':foo
             :the-bar '{:op ':bar
                        :the-foo '{:op ':foo
                                   :the-bar '{:op ':term
                                              :val Sym}}}}
           '{:op ':foo
             :opt Sym
             :the-bar '{:op ':bar
                        :the-foo '{:op ':foo
                                   :the-bar '{:op ':term
                                              :val Sym}}}}
           #_
             '{:op ':bar
               :the-foo '{:op ':foo
                          :the-bar '{:op ':bar
                                     :the-foo '{:op ':term
                                                :val Sym}}}}
)
           :->
           Any])]
         
  ((juxt #_specs-from-tenv ;; FIXME
         anns-from-tenv)
    {'config-in t}
    {:debug true}))

;; FIXME prefer :op over :type?
(let [t (prs
          [
           (U
           '{:op ':foo
             :type (U ':int ':nil ':faz)
             :the-bar '{:op ':bar
                        :type (U ':int ':nil ':faz)
                        :the-foo '{:op ':foo
                                   :type (U ':int ':nil ':faz)
                                   :the-bar '{:op ':term
                                              :val Sym}}}}
           '{:op ':foo
             :type (U ':int ':nil ':faz)
             :opt Sym
             :the-bar '{:op ':bar
                        :type (U ':int ':nil ':faz)
                        :the-foo '{:op ':foo
                                   :type (U ':int ':nil ':faz)
                                   :the-bar '{:op ':term
                                              :val Sym}}}}
             '{:op ':bar
               :type (U ':int ':nil ':faz)
               :the-foo '{:op ':foo
                          :type (U ':int ':nil ':faz)
                          :the-bar '{:op ':bar
                                     :type (U ':int ':nil ':faz)
                                     :the-foo '{:op ':term
                                                :val Sym}}}})
           :->
           Any])]
  (;specs-from-tenv 
   anns-from-tenv 
   {'config-in t}
   {:fuel 0})
  )

(let [t (prs
          [':a
           Integer
           ':b
           Boolean
           :->
           Any])]
         
  ((juxt #_specs-from-tenv ;; FIXME
         anns-from-tenv)
    {'config-in t}
    {:debug true}))

;; combine maps that look similar
(let [t (prs
          ['{:a Long
             :b Long
             :c Long
             :d Long}
           '{:a Long
             :b Long
             :c Long}
           :->
           Any])]
         
  ((juxt #_specs-from-tenv ;; FIXME
         anns-from-tenv)
    {'config-in t}
    ))

;; performance tests
(defn gen-height [n]
  {:pre [(not (neg? n))]}
  (if (zero? n)
    `'{:tag ':null}
    `'{:tag ':cons :cdr ~(gen-height (dec n))}))

(defn gen-tagged-union [n]
  {:pre [(not (neg? n))]}
  (if (zero? n)
    `'{:tag ':null}
    `'{:tag '~(keyword (str "cons" n)) :cdr ~(gen-tagged-union (dec n))}))

(defmacro bench
  "Evaluates expr and returns the time it took."
  [expr]
  `(let [start# (. System (nanoTime))
         ret# ~expr
         msduration# (/ (double (- (. System (nanoTime)) start#)) 1000000.0)]
     [ret# msduration#]))

(defn bench-iteratively 
  ([f n] (bench-iteratively f 0 n))
  ([f start n]
   (loop [times []
          i start]
     (if (< n i)
       times
       (let [[_ t] (f i)]
         (recur (conj times t)
                (inc i)))))))

(defn write-csv [n v]
  {:pre [(vector? v)]}
  (spit n (apply str (interpose "," v))))

(comment
(def bench-height
  (write-csv "height-bench.csv"
             (bench-iteratively
               #(let [t (parse-type (gen-height %))]
                  (binding [*print-anns* false]
                    (bench
                      (anns-from-tenv {'prop t}
                                      {}))))
               120)))

(let [t (parse-type (gen-height 5))]
  (anns-from-tenv {'prop t}
                  {}))
(pprint (gen-tagged-union 5))

(let [t (parse-type (gen-tagged-union 10))]
  (anns-from-tenv {'prop t}
                  {}))

(def bench-tagged
  (write-csv
    "tagged-bench-past110.csv"
    (bench-iteratively
      #(let [t (parse-type (gen-tagged-union %))]
         (binding [*print-anns* false]
           (bench
             (anns-from-tenv {'prop t}
                             {}
                             #_{:debug #{:squash :iterations
                                         :squash-horizontally}}))))
      111 
      120)))
)

; TODO
; other types don't collapse tagged maps
; should combining tagged and untagged maps upcast to (Map Any Any)?
(let [t (prs
          (U nil
             '{:a ':b}
             '{:op ':foo
               :b Long
               :c Long
               :d Long}
             '{:op ':bar
               :e Long
               :w Long
               :q Long}))]
         
  ((juxt #_specs-from-tenv ;; FIXME
         anns-from-tenv)
    {'config-in t}
    ))

; merging sufficiently similar maps
(let [t (prs
          (U nil
             (HMap
               :mandatory {:name Sym}
               :optional {:blah Sym})
             (HMap
               :mandatory {:name Sym
                           :ns Sym}
               :optional {:tag Sym
                          :tag1 Sym
                          :tag2 Sym
                          :tag3 Sym
                          :tag4 Sym
                          :tag5 Sym
                          :tag6 Sym
                          :tag7 Sym
                          :tag8 Sym
                          :tag9 Sym
                          :tag10 Sym
                          :tag11 Sym
                          })))]
         
  ((juxt #_specs-from-tenv ;; FIXME
         anns-from-tenv)
    {'config-in t}
    ))
