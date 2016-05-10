(ns clojure.core.typed.runtime-infer
  (:require [clojure.pprint :refer [pprint]]
            [clojure.set :as set]
            [clojure.test :refer :all]
            [clojure.core.typed.ast-utils :as ast]
            [clojure.core.typed.current-impl :as impl]
            [clojure.core.typed.ast-utils :as ast]))

#_
(defalias Type
  (U '{:op :val :val Any}
     '{:op :HMap :map (Map Kw Type)}
     '{:op :HVec :vec (Vec Type)}
     '{:op :union :types (Set Type)}
     '{:op :class 
       :class Class
       :args (Vec Type)}
     '{:op :IFn 
       :arities (Vec '{:op :IFn1
                       :dom (Vec Type)
                       :rng Type})}
     '{:op :Unknown}
     '{:op :Top}))

#_
(defalias PathElem
  (U '{:op :var
       :name Sym}
     '{:op :fn-domain
       :arity Int
       :position Int}
     '{:op :fn-range
       :arity Int}
     '{:op :key
       :keys (Set Kw)
       :key Kw}
     '{:op :index
       :count Int
       :nth Int}))

#_
(defalias Path
  (Vec Path)) ; path extends to the right, ie. [x :dom :rng] is x's domain's range.

#_
(defalias InferResult
  {:path Path
   :type Type})

#_
(defalias TypeEnv
  (Map Sym Type))

#_
(defalias AliasEnv
  (Map Sym Type))

#_
(defalias AliasTypeEnv
  '{:alias-env AliasEnv
    :type-env TypeEnv})

#_
(defalias InferResultEnv
  (Set InferResult))

; results-atom : (Atom InferResultEnv)
(def results-atom (atom #{}))

(defn infer-result [path type]
  {:type type
   :path path})

(defn var-path [name]
  {:op :var
   :name name})

(defn -unknown []
  {:op :unknown})

(defn fn-dom-path [arity pos]
  {:op :fn-domain
   :arity arity :position pos})

(defn fn-rng-path [arity]
  {:op :fn-range
   :arity arity})

(defn key-path [keys key]
  {:op :key
   :keys keys
   :key key})

(defn index-path [count nth]
  {:op :index
   :count count
   :nth nth})

(defn -class [cls args]
  {:pre [(class? cls)]}
  {:op :class
   :class cls
   :args args})

(defn -val [v]
  {:op :val
   :val v})

(declare parse-path-elem)

(defn parse-infer-result [[p _ t]]
  {:path (mapv parse-path-elem p)
   :type (parse-type t)})

(declare unparse-type)

(defn unparse-infer-result [p]
  [(mapv unparse-path-elem (:path p))
   :-
   (unparse-type (:type p))])

(defn parse-path-elem [p]
  (case (first p)
    val (-val (second p))
    class (-class (resolve (second p)) (mapv parse-type (nth p 2)))
    key (key-path (second p) (nth p 2))
    rng (fn-rng-path (second p))
    dom (fn-dom-path (second p) (nth p 2))
    var (var-path (second p))))

(defn unparse-path-elem [p]
  (case (:op p)
    :val (list 'val (:val p))
    :class (list 'class (symbol (.getName ^Class (:class p)))
                 (mapv unparse-type (:args p)))
    :key (list 'key (:keys p) (:key p))
    :fn-range (list 'rng (:arity p))
    :fn-domain (list 'dom (:arity p) (:position p))
    :var (list 'var (:name p))))

(defn type? [t]
  (and (map? t)
       (keyword? (:op t))))

(defn HMap? [t]
  (and (type? t)
       (= :HMap (:op t))))

(declare parse-type)

(defn parse-arity [a]
  (let [[doms [_->_ rng :as rng-arrow]] (split-with (complement #{:->}) a)
        _ (assert (= 2 (count rng-arrow)))]
    {:op :IFn1
     :dom (mapv parse-type doms)
     :rng (parse-type rng)}))

(defn parse-HVec [v]
  {:op :HVec 
   :vec (mapv parse-type v)})

(defn parse-HMap [m]
  {:op :HMap
   :map (into {}
              (map (fn [[k v]]
                     [k (parse-type v)]))
              m)})

(defn parse-type [m]
  (cond
    (= 'Any m) {:op :Top}
    (= '? m) {:op :unknown}

    (or (= nil m)
        (= false m)
        (keyword? m)) {:op :val :val m}

    (vector? m) {:op :IFn
                 :arities [(parse-arity m)]}

    (symbol? m) (do (assert (class? (resolve m)))
                    {:op :class
                     :class (resolve m)
                     :args []})
    (list? m) (case (first m)
                quote (let [in (second m)]
                        (cond
                          (vector? in) (parse-HVec in)
                          (map? in) (parse-HMap in)
                          :else (assert nil (str "Bad quote: " m))))

                IFn {:op :IFn
                     :arities (mapv parse-arity (rest m))}
                U (make-Union
                    (into #{}
                          (map parse-type)
                          (rest m))))
    :else (assert nil (str "bad type " m))))


; [Node :-> Any]
(defn unparse-type' [{:as m}]
  (assert (type? m)
          m)
  (case (:op m)
    :var (:name m)
    :val (let [t (:val m)]
           (cond
             ((some-fn nil? false?) t) t
             (keyword? t) `'~t
             :else 'Any))
    :union (list* 'U (set (map unparse-type (:types m))))
    :HVec `'~(mapv unparse-type (:vec m))
    :HMap `'~(into {}
                   (map (fn [[k v]]
                          [k (unparse-type v)]))
                   (:map m))
    :IFn (let [as (map
                    (fn [{:keys [dom rng]}]
                      {:pre [dom rng]}
                      (conj (mapv unparse-type dom)
                            :->
                            (unparse-type rng)))
                    (:arities m))]
           (if (== 1 (count as))
             (first as)
             (list* 'IFn as)))
    :class (let [cls (condp = (:class m)
                       clojure.lang.IPersistentVector 'Vec
                       (:class m))]
             (if (seq (:args m))
               (list* cls (map unparse-type (:args m)))
               cls))
    :Top 'Any
    :unknown '?
    (assert nil (str "No unparse-type case: " m))))

(defn unp [t]
  (pprint (unparse-type t)))

(def ^:dynamic unparse-type unparse-type')

(defn flatten-union [t]
  {:pre [(type? t)]
   :post [(set? %)]}
  (if (#{:union} (:op t))
    (into #{}
          (mapcat flatten-union)
          (:types t))
    #{t}))

(defn flatten-unions [ts]
  {:post [(set? %)]}
  (into #{} 
        (mapcat flatten-union)
        ts))

(defn make-Union [args]
  (let [ts (flatten-unions args)
        {hmaps true non-hmaps false} (group-by (comp boolean #{:HMap} :op) ts)
        hmap-by-keys (group-by (comp set keys :map) hmaps)
        hmaps-merged (into #{}
                           (map (fn [ms]
                                  {:post [(HMap? %)]}
                                  (reduce join-HMaps (first ms) (rest ms))))
                           (vals hmap-by-keys))
        ;_ (prn "hmaps-merged" (map unparse-type hmaps-merged))
        ts (into hmaps-merged non-hmaps)]
    (assert (every? (complement #{:union}) (map :op ts)))
    (cond
      (= 1 (count ts)) (first ts)
      :else 
      {:op :union
       :types ts})))

(declare join)

;; (U nil (Atom AliasEnv))
(def ^:dynamic *alias-env* nil)
;; (U nil (Atom AliasEnv))
(def ^:dynamic *type-env* nil)

(defn group-arities [t1 t2]
  {:pre [(#{:IFn} (:op t1))
         (#{:IFn} (:op t2))]}
  (vals
    (group-by (comp count :dom)
              (concat (:arities t1)
                      (:arities t2)))))

#_(deftest group-arities-test
  (is (group-arities
        {:op :IFn, 
         :arities [{:op :IFn1, :dom [], :rng {:op :class, :class java.lang.Long, :args []}}]}
        {:op :IFn, :arities [{:op :IFn1, :dom [{:op :unknown}], :rng {:op :class, :class java.lang.Long, :args []}}]})))

(defn join-HMaps [t1 t2]
  {:pre [(#{:HMap} (:op t1))
         (#{:HMap} (:op t2))
         (= (-> t1 :map keys set)
            (-> t2 :map keys set))]
   :post (#{:HMap} (:op %))}
  (let [t2-map (:map t2)]
    ;(prn "join HMaps")
    {:op :HMap
     :map (into {}
                (map (fn [[k1 t1]]
                       (let [left t1
                             right (get t2-map k1)]
                         ;(prn "key" k1)
                         ;(prn "left" (unparse-type left))
                         ;(prn "right" (unparse-type right))
                         [k1 (join left right)])))
                (:map t1))}))

; join : Type Type -> Type
(defn join [t1 t2]
  (let [id (gensym (apply str (map :op [t1 t2])))
        ;_ (prn "join" id (unparse-type t1) (unparse-type t2))
        res (cond
              (= t1 t2) t1

              ;; annihilate unknown
              (#{:unknown} (:op t1)) t2
              (#{:unknown} (:op t2)) t1

              ((some-fn #{:union})
               (:op t1)
               (:op t2))
              (apply join* (flatten-unions [t1 t2]))

              (and (#{:class} (:op t1))
                   (= clojure.lang.IFn
                      (:class t1))
                   (#{:IFn} (:op t2)))
              t2

              (and (#{:class} (:op t2))
                   (= clojure.lang.IFn
                      (:class t2))
                   (#{:IFn} (:op t1)))
              t1

              (and (#{:HMap} (:op t1))
                   (#{:HMap} (:op t2))
                   (= (-> t1 :map keys set)
                      (-> t2 :map keys set)))
              (join-HMaps t1 t2)

              (and (#{:IFn} (:op t1))
                   (#{:IFn} (:op t2)))
              (let [;_ (apply prn "join IFn" (map unparse-type [t1 t2]))
                    grouped (group-arities t1 t2)
                    ;_ (prn "grouped" grouped)
                    arities
                    (mapv
                      ;; each `as` is a list of :IFn1 nodes
                      ;; with the same arity
                      (fn [as]
                        {:pre [(every? #{[:IFn1 (-> as first :dom count)]}
                                       (map (juxt :op (comp count :dom))
                                            as))]
                         :post [(#{:IFn1} (:op %))]}
                        {:op :IFn1
                         :dom (apply mapv
                                     (fn [& [dom & doms]]
                                       {:pre [dom]}
                                       ;(prn "join IFn IFn dom" (map :op (cons dom doms)))
                                       (apply join* dom doms))
                                     (map :dom as))
                         :rng (let [[rng & rngs] (map :rng as)]
                                (assert rng)
                                (apply join* rng rngs))})
                      grouped)]
                {:op :IFn
                 :arities arities})

              :else 
              (let []
                ;(prn "join union fall through")
                (make-Union [t1 t2])))]
    ;(prn "join result" id (unparse-type res))
    res))

(defn join* [& args]
  (letfn [(merge-type [t as]
            {:pre [(type? t)
                   (not= :union (:op t))
                   (set? as)]
             :post [(set? %)]}
            ;(prn "merge-type" (unparse-type t) (mapv unparse-type as))
            (let [ms (into #{}
                           (comp
                             (map #(join t %))
                             ;(mapcat flatten-union)
                             )
                           (flatten-unions as))
                  res (cond
                        (empty? ms) #{t}
                        :else ms)]
              ;(prn "merge-type result" (map unparse-type res))
              res))]
    (make-Union
      (reduce (fn [as t]
                (merge-type t as))
              #{}
              (flatten-unions args)))))

(deftest join-test
  (is 
    (= 
      (join*
        (parse-type ''{:a ?})
        (parse-type ''{:a [? :-> ?]})
        (parse-type ''{:a [? :-> Long]})
        (parse-type ''{:a [Long :-> Long]}))
      (parse-type ''{:a [Long :-> Long]})))
  (is
    (= 
      (join*
        (parse-type ''{:f ?, :a java.lang.Long}) 
        (parse-type ''{:f [[? :-> java.lang.Long] :-> ?], :a ?}))
      (parse-type ''{:f [[? :-> java.lang.Long] :-> ?], :a java.lang.Long})))
  (is (=
       (join (parse-type '['{:f ?, :a java.lang.Long} :-> '{:b ?, :f clojure.lang.IFn, :a ?}])
             (parse-type '['{:f [[? :-> java.lang.Long] :-> ?], :a ?} :-> ?]))
       (parse-type
         '['{:f [[? :-> java.lang.Long] :-> ?], :a java.lang.Long}
           :->
           '{:b ?, :f clojure.lang.IFn, :a ?}])))
  (is (= (join (parse-type '['{:f ?, :a java.lang.Long} :-> '{:b ?, :f clojure.lang.IFn, :a ?}])
               (parse-type '['{:f [[? :-> java.lang.Long] :-> ?], :a ?} :-> ?]))
         (parse-type
           '['{:f [[? :-> java.lang.Long] :-> ?], :a java.lang.Long}
             :->
             '{:b ?, :f clojure.lang.IFn, :a ?}])))

  (is (= (join (parse-type
                 '(U '{:f [? :-> java.lang.Long], :a ?} 
                     '{:f clojure.lang.IFn}))
               (parse-type 
                 ''{:f [? :-> java.lang.Long]}))
         (parse-type
           '(U '{:f [? :-> java.lang.Long], :a ?} 
               '{:f [? :-> java.lang.Long]}))))
  (is (= 
        (join
          (parse-type ''{:f [[java.lang.Long :-> java.lang.Long] :-> ?]})
          (parse-type ''{:f [[java.lang.Long :-> java.lang.Long] :-> java.lang.Long]}))
        (parse-type ''{:f [[java.lang.Long :-> java.lang.Long] :-> java.lang.Long]})))
  )

; update-path : Path Type -> AliasTypeEnv
(defn update-path [path type]
  {:pre [(vector? path)]}
  (cond 
    (empty? path) (throw (Exception. "Cannot update empty path"))
    (= 1 (count path)) (let [x (nth path 0)
                             n (:name x)
                             t (if-let [t (get @*type-env* n)]
                                 (do
                                   #_(prn "update-path join"
                                        (map :op [t type]))
                                   (join t type))
                                 type)]
                         (assert (#{:var} (:op x))
                                 (str "First element of path must be a variable " x))
                         (swap! *type-env* assoc n t))
    :else 
    (let [last-pos (dec (count path))
          cur-pth (nth path last-pos)
          nxt-pth (subvec path 0 last-pos)]
      (assert (:op cur-pth) (str "What is this? " cur-pth
                                 " full path: " path))
      (case (:op cur-pth)
        :var (throw (Exception. "Var path element must only be first path element"))
        :key (let [{:keys [keys key]} cur-pth]
               (update-path nxt-pth
                            {:op :HMap
                             :map (assoc (zipmap keys (repeat {:op :unknown}))
                                         key type)}))
        :fn-domain (let [{:keys [arity position]} cur-pth]
                     (update-path nxt-pth
                                  {:op :IFn
                                   :arities [{:op :IFn1
                                              :dom (assoc (into [] 
                                                                (repeat (:arity cur-pth) {:op :unknown}))
                                                          position type)
                                              :rng {:op :unknown}}]}))
        :fn-range (let [{:keys [arity]} cur-pth]
                     (update-path nxt-pth
                                  {:op :IFn
                                   :arities [{:op :IFn1
                                              :dom (into [] (repeat (:arity cur-pth) {:op :unknown}))
                                              :rng type}]}))))))

(defn update-path' [env infer-results]
  (binding [*type-env* (atom env)]
    (doseq [{:keys [path type]} infer-results]
      (update-path path type))
    @*type-env*))

(defn ppenv [env]
  (pprint (into {}
                (map (fn [[k v]]
                       [k (unparse-type v)]))
                env)))

(deftest update-path-test
  (is (= (update-path' {}
                       [(infer-result [(var-path 'use-map)
                                       (key-path #{:a} :a)]
                                      (-unknown))
                        (infer-result [(var-path 'use-map)
                                       (key-path #{:a} :a)]
                                      (-class Long []))])
         {'use-map (parse-type ''{:a Long})}))
  (is (= (update-path' {}
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
                                      (-class Long []))
                        ]))
         {'use-map
          (parse-type '['{:f [[? :-> Long] :-> ?], :a java.lang.Long} :-> '{:b ?, :f clojure.lang.IFn, :a ?}])})
  (is (= (->
           (update-path' {}
                       [(infer-result [(var-path 'foo) (fn-rng-path 1)]
                                      (parse-type 'Long))
                        (infer-result [(var-path 'foo) (fn-dom-path 1 0)]
                                      (parse-type 'Long))])
           ;ppenv
           )
         {'foo (parse-type '[Long :-> Long])}))
  (is (=
        (update-path' {}
                      [(infer-result [(var-path 'foo)]
                                     (parse-type
                                       '?))
                       (infer-result [(var-path 'foo)]
                                     (parse-type
                                       '[Long :-> ?]))])
        {'foo (parse-type '[java.lang.Long :-> ?])}))

(is
  (=
    (join
      (parse-type '[(U '{:f [? :-> java.lang.Long], :a ?} '{:f [? :-> java.lang.Long]}) :-> '{:b ?, :f ?, :a java.lang.Long}])
      (parse-type '['{:f clojure.lang.IFn, :a ?} :-> ?]))
    (parse-type
      '[(U '{:f [? :-> java.lang.Long], :a ?} '{:f [? :-> java.lang.Long]})
        :->
        '{:b ?, :f ?, :a java.lang.Long}])))

(is
  (=
   (join
     (parse-type '(U '{:f [? :-> java.lang.Long], :a ?} '{:f [? :-> java.lang.Long]}))
     (parse-type ''{:f clojure.lang.IFn, :a ?}))
   (parse-type '(U '{:f [? :-> java.lang.Long], :a ?} '{:f [? :-> java.lang.Long]}))))
  
(is
(=
  (update-path' {}
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
                        java.lang.Long]
                      ]
                      ))
{'clojure.core.typed.runtime-infer/use-map
 (parse-type
 '[(U
   '{:f [[java.lang.Long :-> java.lang.Long] :-> java.lang.Long]}
   '{:f [[java.lang.Long :-> java.lang.Long] :-> java.lang.Long],
     :a java.lang.Long})
  :->
  (U
   '{:b java.lang.Long, :f clojure.lang.IFn, :a java.lang.Long}
   '{:b java.lang.Long, :f clojure.lang.IFn})])}))
  )

; track : (Atom InferResultEnv) Value Path -> Value
(defn track [results-atom v path]
  {:pre [(vector? path)]}
  (cond
    ;; only accurate up to 20 arguments.
    ;; all arities 21 and over will collapse into one.
    (fn? v) (do
              ;; if this is never called, remember it is actually a function
              (swap! results-atom conj (infer-result path (-class clojure.lang.IFn [])))
              (with-meta
                (fn [& args]
                  (let [blen (impl/bounded-length args 20) ;; apply only realises 20 places
                        args (map-indexed
                               (fn [n v]
                                 (track results-atom v (conj path (fn-dom-path blen n))))
                               args)]
                    (track results-atom (apply v args) (conj path (fn-rng-path blen)))))
                (meta v)))

    ; TODO implement :index in update-path
    ;(and (vector? v) 
    ;     (satisfies? clojure.core.protocols/IKVReduce v)) ; MapEntry's are not IKVReduce
    ;(let [len (count v)]
    ;  ;; TODO handle zero-length vectors, also might 
    ;  ;; want to remember IPV like IFn above.
    ;  (reduce-kv
    ;    (fn [e k v]
    ;      (let [v' (track results-atom v (conj path (index-path len k)))]
    ;        (if (identical? v v')
    ;          e
    ;          (assoc e k v'))))
    ;    v
    ;    v))

    ;; maps with keyword keys
    (and (or (instance? clojure.lang.PersistentHashMap v)
             (instance? clojure.lang.PersistentArrayMap v))
         (every? keyword? (keys v)))
    (let [ks (set (keys v))]
      (reduce
        (fn [m k]
          (let [orig-v (get m k)
                v (track results-atom orig-v
                         (conj path (key-path ks k)))]
            ;; only assoc if needed
            (if (identical? v orig-v)
              m
              (assoc m k v))))
        v
        ks))

    ;(instance? clojure.lang.IAtom v)
    ;(reify

    ((some-fn keyword? nil? false?) v)
    (do
      (swap! results-atom conj (infer-result path (-val v)))
      v)

    :else (do
            (swap! results-atom conj (infer-result path (-class (class v) [])))
            v)))

(defn track-var'
  ([vr] (track-var' results-atom vr *ns*))
  ([results-atom vr ns]
   {:pre [(var? vr)
          (instance? clojure.lang.IAtom results-atom)]}
   (track results-atom @vr [#_(ns-name ns) ; don't track current namespace yet
                            {:op :var
                             :name (impl/var->symbol vr)}])))

(defmacro track-var [v]
  `(track-var' (var ~v)))

(defn track-def-init [vsym val]
  (track results-atom val [{:op :var :name vsym}]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Analysis compiler pass
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def ns-exclusions
  '#{clojure.core
     clojure.core.typed
     clojure.test
     clojure.string})

(defn wrap-var-deref [expr vsym *ns*]
  (do
    #_
    (println (str "Instrumenting " vsym " in " (ns-name *ns*) 
                  #_":" 
                  #_(-> expr :env :line)
                  #_(when-let [col (-> expr :env :column)]
                      ":" col)))
    {:op :invoke 
     :children [:fn :args]
     :form `(track-var' (var ~vsym))
     :env (:env expr)
     :fn {:op :var
          :var #'track-var'
          :form `track-var'
          :env (:env expr)}
     :args [{:op :var
             :form `results-atom
             :env (:env expr)
             :var #'results-atom}
            {:op :the-var
             :form `(var ~vsym)
             :env (:env expr)
             :var (:var expr)}
            {:op :const
             :type :unknown
             :form *ns*
             :val *ns*
             :env (:env expr)}]}))

(defn wrap-def-init [expr vsym *ns*]
  (do
    #_
    (println (str "Instrumenting def init " vsym " in " (ns-name *ns*) 
                  #_":" 
                  #_(-> expr :env :line)
                  #_(when-let [col (-> expr :env :column)]
                      ":" col)))
    {:op :invoke
     :children [:fn :args]
     :form `(track-def-init '~vsym ~(:form expr))
     :env (:env expr)
     :fn {:op :var
          :var #'track-def-init
          :form `track-def-init
          :env (:env expr)}
     :args [{:op :const
             :type :symbol
             :form `'~vsym
             :env (:env expr)
             :val vsym}
            expr]}))

(defn check
  "Assumes collect-expr is already called on this AST."
  ([expr] (check expr nil))
  ([expr expected]
   (letfn []
     (case (:op expr)
       ;; Wrap def's so we can instrument their usages outside this
       ;; namespace.
       :def (if (:init expr)
              (update expr :init wrap-def-init (ast/def-var-name expr) *ns*)
              expr)
       ;; Only wrap library imports so we can infer how they are used.
       :var (let [vsym (impl/var->symbol (:var expr))
                  vns (symbol (namespace vsym))]
              ;(prn "var" vsym)
              (if-not (contains? (conj ns-exclusions (ns-name *ns*)) vns)
                (wrap-var-deref expr vsym *ns*)
                expr))
       (ast/walk-children check expr)))))

(def runtime-infer-expr check)

(defmacro for-fold [[acc acc-init] [arg arg-coll] & body]
  `(reduce
     (fn [~acc ~arg]
       ~@body)
     ~acc-init
     ~arg-coll))

; generate : (Set InferResultEnv) -> TypeEnv
(defn generate [is]
  (binding [*alias-env* (atom {})
            *type-env*  (atom {})]
    (let [_ (doseq [{:keys [path type]} is]
              (update-path path type))]
      (pprint
        (into {}
              (map (fn [[name t]]
                     ;(prn "generate" t)
                     [name (unparse-type t)]))
              @*type-env*)))))

(defn gen-current []
  (generate @results-atom))

(defn ppresults []
  (pprint
    (into #{}
          (map (fn [a]
                 (update a :type unparse-type)))
          @results-atom)))

;; TESTS

(defn foo [a]
  (+ a 2))

(defn bar [f]
  (f 1))

(bar (track-var foo))

(defn use-map [m]
  (merge m {:b ((:f m) foo)}))

(use-map {:a 1, :f bar})

((track-var use-map) {:a 1, :f bar})

((track-var use-map) {:f bar})

((track-var use-map) {:f (track-var bar)})

(defn multi-arg 
  ([a] (inc a))
  ([s1 s2] (str s1 s2)))

((track-var multi-arg) 1)
((track-var multi-arg) "a" "a")

(defn take-map [m]
  m)

(comment

((track-var take-map) nil)
((track-var take-map) {:a nil})
((track-var take-map) {:a {:a nil}})
((track-var take-map) {:a {:a {:a {:a nil}}}})

(ppres)

(defn postfix [& words]
  (reduce (fn [stack t]
            (if (fn? t)
              (let [[l r & m] stack]
                (cons (t r l) m))
              (cons t stack)))
          [] 
          words))

(postfix 1 2 )
)
