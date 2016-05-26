(ns clojure.core.typed.runtime-infer
  (:require [clojure.pprint :refer [pprint]]
            [clojure.set :as set]
            [clojure.test :refer :all]
            [clojure.string :as str]
            [clojure.core.typed.ast-utils :as ast]
            [rhizome.viz :as viz]
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
     '{:op :unknown}
     '{:op :poly
       :known-params (Vec Sym)
       :params (Map (Set Path) 
                    {:weight Int
                     :name Sym
                     :types (Set Kw)})
       :type Type}
     '{:op :alias
       :name Sym}
     '{:op :free
       :name Sym}
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
     '{:op :set-entry}
     '{:op :seq-entry}
     '{:op :transient-vector-entry}
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
  '{:op ':path-type
    :path Path
    :type Type})

#_
(defalias Equiv
  '{:op ':equiv
    := (Vec Path)
    :type (U ':nil
             ':keyword
             ':fn
             ':number
             ':symbol
             ':string
             ':bool
             ':coll
             ':other)})

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
  '{:infer-results (Set InferResult)
    :equivs (Vec Equiv)
    :path-occ (Map Path Int)
    :value-envs (MutableIdentityMap Any ValueEnv)})

#_
(defalias ValueResultEnv
  '{:path Path
    :aliases (Set Path)
    :infer-results (Set InferResult)
    :parent (U nil [Any])})

(defn initial-results 
  ([] (initial-results nil []))
  ([parent base]
   {:infer-results #{}
    :equivs []
    :path-occ {}
    ; current path
    :base base
    :parent parent}))

; results-atom : (Atom InferResultEnv)
(def results-atom (atom (initial-results)
                        :validator
                        (fn [m]
                          (and (map? m)
                               (-> m :infer-results set?)
                               (-> m :path-occ map?)
                               (-> m :equivs vector?)))))

(defn find-top-parent [results-atom]
  {:pre [(instance? clojure.lang.IAtom results-atom)]
   :post [(instance? clojure.lang.IAtom %)]}
  (loop [results-atom results-atom]
    (if (:parent @results-atom)
      (recur (:parent @results-atom))
      results-atom)))

(defn has-parent? [results-atom]
  {:pre [(instance? clojure.lang.IAtom results-atom)]}
  (boolean (:parent @results-atom)))

(defn rename-infer-result-prefix [ir old new]
  {:pre [(= old (take (count old) (:path ir)))]}
  (update ir :path
          (fn [p]
            (into old
                  (drop (count old) p)))))

(defn add-infer-result! [results-atom r]
  (swap! results-atom update :infer-results conj r))

(defn add-equiv! [results-atom e]
  (swap! results-atom update :equivs conj e))

(defn get-infer-results [results-atom]
  (get @results-atom :infer-results))

(defn infer-result [path type]
  {:op :path-type
   :type type
   :path path})

(defn equiv-result [ps cls]
  {:pre [(set? ps)
         (= 2 (count ps))
         (keyword? cls)]}
  {:op :equiv
   := ps
   :type cls})

(defn var-path [name]
  {:op :var
   :name name})

(defn -alias [name]
  {:pre [(symbol? name)]}
  {:op :alias
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

(defn seq-entry []
  {:op :set-entry})

(defn set-entry []
  {:op :set-entry})

(defn transient-vector-entry []
  {:op :transient-vector-entry})

(defn -class [cls args]
  {:pre [(class? cls)]}
  {:op :class
   :class cls
   :args args})

(defn -val [v]
  {:op :val
   :val v})

(defn make-free [name]
  {:pre [(symbol? name)]}
  {:op :free
   :name name})

(declare parse-path-elem parse-type)

(defn parse-infer-result [[p _ t]]
  {:path (mapv parse-path-elem p)
   :type (parse-type t)})

(declare unparse-path-elem unparse-type)

(defn unparse-path [ps]
  (mapv unparse-path-elem ps))

(defn unparse-infer-result [p]
  [(unparse-path (:path p) :- (unparse-type (:type p)))])

(defn parse-path-elem [p]
  (case (first p)
    val (-val (second p))
    class (-class (resolve (second p)) (mapv parse-type (nth p 2)))
    key (key-path (second p) (nth p 2))
    rng (fn-rng-path (second p))
    dom (fn-dom-path (second p) (nth p 2))
    var (var-path (second p))
    index (index-path (second p) (nth p 2))))

(defn unparse-path-elem [p]
  (case (:op p)
    :val (list 'val (:val p))
    :class (list 'class (symbol (.getName ^Class (:class p)))
                 (mapv unparse-type (:args p)))
    :key (list 'key (:keys p) (:key p))
    :fn-range (list 'rng (:arity p))
    :fn-domain (list 'dom (:arity p) (:position p))
    :var (list 'var (:name p))
    :index (list 'index (:count p) (:nth p))
    :set-entry (list 'set-entry)
    :seq-entry (list 'seq-entry)
    :transient-vector-entry (list 'transient-vector-entry)))

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

(declare make-Union)

(def ^:dynamic *type-var-scope* #{})

(defn parse-type [m]
  (cond
    (= 'Any m) {:op :Top}
    (= '? m) {:op :unknown}

    (or (= nil m)
        (= false m)
        (keyword? m)) {:op :val :val m}

    (vector? m) {:op :IFn
                 :arities [(parse-arity m)]}

    (symbol? m) (case m
                  Nothing {:op :union :types #{}}
                  (if (contains? *type-var-scope* m)
                    {:op :var
                     :name m}
                    (do
                      (assert (class? (resolve m)))
                      {:op :class
                       :class (resolve m)
                       :args []})))
    (list? m) (case (first m)
                All (let [[vs t :as rst] (second m)
                          _ (assert (= 2 (count rst)))]
                      {:op :poly
                       :known-params (into []
                                           (map (fn [m]
                                                  {:pre [(symbol? m)]}
                                                  m))
                                           vs)
                       :params {}
                       :type (binding [*type-var-scope* (into *type-var-scope* vs)]
                               (parse-type t))})
                quote (let [in (second m)]
                        (cond
                          (vector? in) (parse-HVec in)
                          (map? in) (parse-HMap in)
                          (keyword? in) {:op :val :val in}
                          :else (assert nil (str "Bad quote: " m))))

                IFn {:op :IFn
                     :arities (mapv parse-arity (rest m))}
                U (make-Union
                    (into #{}
                          (map parse-type)
                          (rest m)))
                Vec (-class clojure.lang.IPersistentVector
                            [(parse-type (second m))])
                Set (-class clojure.lang.IPersistentSet
                            [(parse-type (second m))])
                Sym (-class clojure.lang.Symbol [])
                (let [res (resolve (first m))]
                  (assert (class? res) (prn-str "Must be class: " (first m)))
                  (-class res (mapv parse-type (drop 1 m)))))
    :else (assert nil (str "bad type " m))))

(defmacro prs [t]
  `(parse-type '~t))

(def ^:dynamic *unparse-abbrev-alias* false)
(def ^:dynamic *unparse-abbrev-class* false)

; [Node :-> Any]
(defn unparse-type' [{:as m}]
  (assert (type? m)
          m)
  (case (:op m)
    :alias (if *unparse-abbrev-alias*
             (-> (:name m) name symbol)
             (:name m))
    :val (let [t (:val m)]
           (cond
             ((some-fn nil? false?) t) t
             (keyword? t) `'~t
             :else 'Any))
    :union (if (empty? (:types m))
             'Nothing
             (list* 'U (set (map unparse-type (:types m)))))
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
                       clojure.lang.IPersistentSet 'Set
                       clojure.lang.Symbol 'Sym
                       (if *unparse-abbrev-class*
                         (symbol 
                           (apply str (last (partition-by #{\.} (str (:class m))))))
                         (:class m)))]
             (if (seq (:args m))
               (list* cls (map unparse-type (:args m)))
               cls))
    :Top 'Any
    :unknown '?
    :free (:name m)
    :poly (list 'All (into (mapv (fn [[ps {:keys [weight name types]}]]
                                   {:pre [(= 2 (count ps))]}
                                   [name 
                                    types
                                    weight :of 
                                    [(get-in @results-atom [:path-occ (first ps)] 0)
                                     (get-in @results-atom [:path-occ (second ps)] 0)]
                                    '<- (mapv unparse-path ps)])
                                 (:params m))
                           (:known-params m))
                (unparse-type (:type m)))
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

(declare join-HMaps join*)

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

(defn should-join-HMaps? [t1 t2]
  ;; join if the keys are the same, 
  ;; (TODO)
  ;; and common
  ;; keys are not always different keywords
  (let [t1-map (:map t1)
        t2-map (:map t2)]
    (and (= (set (keys t1-map))
            (set (keys t2-map)))
         ;; TODO
         #_
         (every?
           ;; should return true if we should merge
           ;; this entry
           (fn [[k left]]
             (let [right (t2-map k)]
               (or (= left right)
                   (not ((every-pred (comp #{:val} :op)
                                     (comp keyword? :val))
                         left
                         right)))))
           t1-map))))


(defn join-HMaps [t1 t2]
  {:pre [(#{:HMap} (:op t1))
         (#{:HMap} (:op t2))
         (should-join-HMaps? t1 t2)]
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

              (and (#{:poly} (:op t1))
                   (#{:poly} (:op t2)))
              {:op :poly
               :known-params (into (:known-params t1)
                                   (:known-params t2))
               :params (merge-with (fn [{w1 :weight
                                         v1 :name
                                         t1 :types}
                                        {w2 :weight
                                         v2 :name
                                         t2 :types}]
                                     ;; throw away v2
                                     (prn "Merging:" w1 w2)
                                     {:weight (+ w1 w2)
                                      :name v1
                                      :types (into t1 t2)})
                                   (:params t1) (:params t2))
               :types (join (:type t1) (:type t2))}

              (#{:poly} (:op t1))
              (update t1 :type join t2)
              (#{:poly} (:op t2))
              (update t2 :type join t1)

              (and (#{:class} (:op t1))
                   (#{:class} (:op t2))
                   (= (:class t1)
                      (:class t2))
                   (= (count (:args t1))
                      (count (:args t2))))
              (-class (:class t1) (mapv join (:args t1) (:args t2)))

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
                   (should-join-HMaps? t1 t2))
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
  (is (=
       (join
         (prs
           '{:E (quote :false)})
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
             :E ':app}))
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
            :E ':app}))))
  (is 
    (=
      (join*
        (prs (Vec '{:a ?}))
        (prs (Vec '{:b ?})))
      (prs (Vec (U '{:a ?} '{:b ?})))))
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

(declare update-path)

(defn update-var-down-paths [ps new-var]
  #_
  (doseq [p ps]
    (update-path p new-var)))

(defn update-equiv [ps tpe]
  {:pre [(set? ps)
         (= 2 (count ps))
         (every? vector? ps)
         (every? (comp #{:var} :op first) ps)
         ; vars must be the same
         (apply = (map (comp :name :op first) ps))
         (keyword? tpe)]}
  ;(prn "update-equiv")
  ;(pprint (mapv unparse-path ps))
  (let [nme (-> ps first first :name)
        _ (assert (symbol? nme))
        t (get @*type-env* nme)
        _ (assert (type? t) (pr-str nme))]
    (case (:op t)
      :poly (let [; find existing path that overlaps with any
                  ; of the current paths
                  vs (remove (fn [[s _]]
                               (assert (set? s) s)
                               (empty? 
                                 (set/intersection s ps)))
                             (:params t))]
              (case (count vs)
                ;; no matches
                0 (let [new-sym (gensym "var")
                        new-var (make-free new-sym)]
                    ;(prn "Found no matching poly, extending with " new-sym)
                    ;; first add the variable to the parameter list
                    (swap! *type-env* assoc-in [nme :params ps] 
                           ; weight of 1
                           {:weight 1 
                            :name new-sym
                            :types #{tpe}})
                    ;; then update the variable down each path
                    (update-var-down-paths ps new-var))
                ;; process results
                (doseq [[vps {vsym :name}] vs]
                  (let [var (make-free vsym)]
                    ;(prn "Found many matching poly, " vsym)
                    (swap! *type-env* 
                           (fn [m]
                             (-> m
                                 (update-in [nme :params vps :weight] 
                                            (fn [i]
                                              ;(prn "adding i" i)
                                              (inc i)))
                                 (update-in [nme :params vps :types] conj tpe))))
                    ;; update var down each path
                    (update-var-down-paths ps var)))))
      (let [new-sym (gensym "var")
            new-var (make-free new-sym)]
        ;(prn "No polymorphic type found, creating new poly with " new-sym)
        ;; first construct a poly type that wraps the original type
        (swap! *type-env* assoc nme
               {:op :poly
                :params {ps {:weight 1 
                             :name new-sym
                             :types #{tpe}}} ; weight of 1
                :type t})
        ;; then update the var down each path
        (update-var-down-paths ps new-var)))))

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
        :set-entry (update-path nxt-pth
                                (-class clojure.lang.IPersistentSet [type]))
        :seq-entry (update-path nxt-pth
                                (-class clojure.lang.ISeq [type]))
        :transient-vector-entry (update-path nxt-pth
                                             (-class clojure.lang.ITransientVector [type]))
        :index (update-path nxt-pth
                            (-class clojure.lang.IPersistentVector [type]))
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

(defn walk-type-children [v f]
  {:pre [(type? v)]
   :post [(type? %)]}
  (case (:op v)
    :val v
    :alias v
    :unknown v
    :HMap (update v :map (fn [m]
                           (reduce-kv
                             (fn [m k v]
                               (assoc m k (f v)))
                             {}
                             m)))
    :class (update v :args (fn [m]
                             (reduce-kv
                               (fn [m k v]
                                 (assoc m k (f v)))
                               []
                               m)))
    :HVec (update v :vec (fn [m]
                           (reduce-kv
                             (fn [m k v]
                               (assoc m k (f v)))
                             []
                             m)))
    :union (apply join* (into #{}
                              (map f)
                              (:types v)))
    ;:var (update v :name (fn [n]
    ;                       (get s n n)))
    :IFn (update v :arities
                 (fn [as]
                   (mapv f as)))
    :IFn1 (-> v
              (update :dom
                      (fn [ds]
                        (mapv f ds)))
              (update :rng f))))

; tools.analyzer
(defn walk
  "Walk the ast applying `pre` when entering the nodes, and `post` when exiting.
   Both functions must return a valid node since the returned value will replace
   the node in the AST which was given as input to the function.
   Short-circuits on reduced."
  ([ast pre post]
     (unreduced
      ((fn walk [ast pre post]
         (let [walk #(walk % pre post)]
           (if (reduced? ast)
             ast
             (let [ret (walk-type-children (pre ast) walk)]
               (if (reduced? ret)
                 ret
                 (post ret))))))
       ast pre post))))

; tools.analyzer
(defn prewalk
  "Shorthand for (walk ast f identity)"
  [ast f]
  (walk ast f identity))

; tools.analyzer
(defn postwalk
  "Shorthand for (walk ast identity f reversed?)"
  ([ast f] (walk ast identity f)))

(defn register-alias [name t]
  {:pre [(symbol? name)
         (namespace name)]}
  (swap! *alias-env* assoc name t)
  nil)

(defn register-merge-alias [sym t]
  ;(prn "gen" sym)
  (let [t' (get @*alias-env* sym)]
    (if t'
      (do
        (swap! *alias-env* update sym join t')
        sym)
      (do
        (swap! *alias-env* assoc sym t)
        sym))))

(defn register-unique-alias [sym t]
  (let [sym (if (contains? @*alias-env* sym)
              (gensym (str sym "__"))
              sym)]
    (register-alias sym t)
    sym))

(defn resolve-alias [{:keys [name] :as a}]
  {:pre [(symbol? name)
         (type? a)]
   :post [(type? %)]}
  ;(prn "resolve" name)
  (@*alias-env* name))

(def kw-val? (every-pred (comp #{:val} :op)
                         (comp keyword? :val)))

#_ 
(ann likely-HMap-dispatch [HMap -> (U nil '[Kw (Set Kw)])])
(defn likely-HMap-dispatch
  "Given a HMap type, returns a vector tuple
  of the best guess for the dispatch entry for this HMap.
  The first entry contains the keyword key, and the second
  contains a set of keys that dispatch to this type.
  
  eg. (likely-HMap-dispatch (prs '{:op ':val})) 
      ;=> [:op #{:val}]

  eg. (likely-HMap-dispatch (prs '{:T (U ':intersection :union)}))
      ;=> [:T #{:intersection :union}]
  "
  [t]
  {:pre [(HMap? t)]
   :post [((some-fn nil? vector?) %)]}
  (let [singles (filter (comp (some-fn
                                ; either a literal keyword
                                kw-val?
                                ; or a union of literal keywords
                                (every-pred (comp #{:union} :op)
                                            #(every? kw-val? (:types %))))
                              val)
                        (:map t))]
    (when-let [[k t] (and (= (count singles) 1)
                          (first singles))]
      [k (case (:op t)
           :val #{(:val t)}
           :union (into #{}
                        (map :val)
                        (:types t)))])))

(defn alias-hmap-type [t]
  (letfn [(do-alias [t]
            (let [[nme merge?] (case (:op t)
                                 :HMap (if-let [[k v] (likely-HMap-dispatch t)]
                                         [(apply str (name k) "-" 
                                                (into []
                                                      (comp
                                                        (map name)
                                                        (interpose "-"))
                                                      v))
                                          true]
                                         [(apply str (interpose "-" (map name (keys (:map t)))))
                                          false])
                                 :union (if (every? (comp #{:alias} :op) (:types t))
                                          (let [ls (into []
                                                         (map (comp likely-HMap-dispatch resolve-alias))
                                                         (:types t))]
                                            (let [ss (into #{}
                                                           (comp (filter some?)
                                                                 (map first))
                                                           ls)]
                                              (if (and (every? some? ls)
                                                       (= (count ss) 1))
                                                [(name (first ss)) true]
                                                ["union" false])))
                                          ["union" false])
                                 ["unknown" false])
                  _ (assert (instance? Boolean merge?))
                  n (symbol (-> *ns* ns-name str) nme)
                  a (;(if merge? register-merge-alias register-unique-alias)  ;; buggy
                     register-unique-alias
                     n t)]
              (-alias a)))]
    (postwalk t
              (fn [t]
                (case (:op t)
                  :HMap (do-alias t)
                  :union (if (and (seq (:types t))
                                  (not-every?
                                    (fn [t]
                                      (case (:op t)
                                        :val true
                                        :class (empty? (:args t))
                                        false))
                                    (:types t)))
                           (do-alias t)
                           t)
                  ;:IFn1 (-> t
                  ;          (update :dom #(mapv do-alias %))
                  ;          (update :rng do-alias))
                  t)))))

(declare generate-tenv ppenv)

(defn alias-hmap-envs* [aenv tenv]
  (binding [*type-env* (atom tenv)
            *alias-env* (atom aenv)]
    (doseq [[v t] @*type-env*]
      (swap! *type-env* update v alias-hmap-type))
    [@*type-env* @*alias-env*]))

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

#_
(= [map {:dom 0} {:dom 0}]
   [map {:dom 1} {:index 0}])

(defn identity-hash []
  (new java.util.IdentityHashMap))

(def identity-hash-lock (Object.))

(defn update-identity-hash! 
  [^java.util.IdentityHashMap h k f & args]
  (locking h
    (doto h
      (.put k (apply f (.get h k) args)))))

(defn summarize-object [v] 
  #_(System/identityHashCode v)
  v)

(defn type-of [v]
  (cond
    (nil? v) :nil
    (keyword? v) :keyword
    (symbol? v) :symbol
    (string? v) :string
    (instance? Boolean v) :bool
    (coll? v) :coll
    (number? v) :number
    (fn? v) :fn
    (instance? clojure.lang.ITransientCollection v) :transient
    :else :other))

(defmacro cond-wrap [f & clauses]
  (letfn [(wrap [f clauses]
            (when clauses
              (list 'if (first clauses)
                    (if (next clauses)
                      (list f (second clauses))
                      (throw (IllegalArgumentException.
                               "cond-wrap requires an even number of forms")))
                    (wrap f (next (next clauses))))))]
    (let [b (gensym "f")]
      `(let [~b ~f]
         ~(wrap b clauses)))))


; value-cache :
;WeakIdentityRefMap
#_
(Ref (Map Int (Vec '[(U nil WeakReference)
                     (Ref '{:infer-results (Set InferResult)
                            :path Path
                            :aliases (Set Path)})])))
(def value-cache (ref {}))

; track : (Atom InferResultEnv) Value Path -> Value
(defn track 
  ([results-atom v path]
   {:pre [(vector? path)]}
   (let []
     (cond
       ;; only accurate up to 20 arguments.
       ;; all arities 21 and over will collapse into one.
       (fn? v) (let [;; if this is never called, remember it is actually a function
                     ir (infer-result path (-class clojure.lang.IFn []))
                     _ (add-infer-result! results-atom ir)]
                 (with-meta
                   (fn [& args]
                     (let [blen (impl/bounded-length args 20) ;; apply only realises 20 places
                           args (map-indexed
                                  (fn [n v]
                                    (track results-atom v (conj path (fn-dom-path blen n))))
                                  args)]
                       (track results-atom (apply v args) (conj path (fn-rng-path blen)))))
                   (meta v)))

       (list? v)
       (with-meta
         (list* (map (fn [e]
                       (track results-atom e (conj path (seq-entry))))
                     v))
         (meta v))

       (and (seq? v)
            (not (list? v)))
       (letfn [(wrap-lseq [v]
                 (with-meta
                   (lazy-seq
                     (if (empty? v)
                       v
                       (cons (track results-atom
                                    (first v)
                                    (conj path (seq-entry)))
                             (wrap-lseq (rest v)))))
                   (meta v)))]
         (wrap-lseq v))

       (instance? clojure.lang.ITransientVector v)
       (let [cnt (count v)]
         (reduce
           (fn [v i]
             (let [e (nth v i)
                   e' (track results-atom e
                             (conj path (transient-vector-entry)))]
               (if (identical? e e')
                 v
                 (assoc! v i e'))))
           v
           (range cnt)))

       (and (vector? v) 
            (satisfies? clojure.core.protocols/IKVReduce v)) ; MapEntry's are not IKVReduce
       (let [len (count v)]
         (when (= 0 len)
           (add-infer-result! results-atom (infer-result path (-class clojure.lang.IPersistentVector [{:op :union :types #{}}]))))
         (reduce-kv
           (fn [e k v]
             (let [v' (track results-atom v (conj path (index-path len k)))]
               (if (identical? v v')
                 e
                 (assoc e k v'))))
           v
           v))

       (set? v)
       (do
         (when (empty? v)
           (add-infer-result!
             results-atom
             (infer-result path
                           (-class clojure.lang.IPersistentSet
                                   [{:op :union :types #{}}]))))
         (into #{}
               (map (fn [e]
                      (track results-atom e (conj path (set-entry)))))
               v))

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
         (add-infer-result! results-atom (infer-result path (-val v)))
         v)

       :else (do
               (add-infer-result! results-atom (infer-result path (-class (class v) [])))
               v)))))

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
  {:pre [(symbol? vsym)
         (namespace vsym)]}
  (track results-atom val [{:op :var :name vsym}]))

(defmacro defntrack [n & args]
  `(def ~n (track-def-init
             '~(symbol (str (ns-name *ns*)) (str n))
             (fn ~@args))))

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

; generate : InferResultEnv -> TypeEnv
(defn generate [is]
  (binding [*alias-env* (atom {})
            *type-env*  (atom {})]
    (let [_ (reset! *type-env* (generate-tenv is))]
      (pprint
        (into {}
              (map (fn [[name t]]
                     ;(prn "generate" t)
                     [name (unparse-type t)]))
              @*type-env*)))))

; generate-tenv : InferResultEnv -> TypeEnv
(defn generate-tenv [{:keys [infer-results equivs] :as is}]
  (binding [*type-env* (atom {})]
    (doseq [i infer-results]
      (let [{:keys [path type]} i] 
        (update-path path type)))
    (doseq [i equivs]
      (update-equiv (:= i)
                    (:type i)))
    @*type-env*))

(defn gen-current1
  "Print the currently inferred type environment"
  []
  (generate @results-atom))

(defn gen-current2 
  "Turn the currently inferred type environment
  into type aliases. Also print the alias environment."
  []
  (binding [*type-env* (atom {})
            *alias-env* (atom {})]
    (reset! *type-env*
            (into {}
                  (map (fn [[v t]]
                         [v (alias-hmap-type t)]))
                  (generate-tenv @results-atom)))
    (ppenv @*type-env*)
    (ppenv @*alias-env*)))

(declare visualize unmunge)

(def premade-configs
  {:vfn {:spit (fn [& args]
                 (spit "visualize.svg" (apply viz/graph->svg args)))
         :viz viz/view-graph}
   :options {:small {:dpi 50
                     ;:fixedsize false
                     :fontname "Courier"
                     :vertical? true}}
   :node->cluster {:unmunge (fn [n]
                              (when-not (namespace n)
                                (unmunge n))
                              #_
                              (let [t (-> n meta :type)]
                                (case (:op t)
                                  :HMap
                                  (let [singles (filter (comp #{:val} :op val) (:map t))]
                                    (when-let [[k v] (and (= (count singles) 1)
                                                          (first singles))]
                                      (str k "-" (pr-str (:val v)))))
                                  nil)))
                   :HMaps
                   (fn [n]
                     (let [t (-> n meta :type)]
                       (case (:op t)
                         :HMap (apply str (interpose "-" (sort (map name (keys (:map t))))))
                         nil)))}
   :cluster->descriptor 
   {:random-color (fn [c]
                    {:color (rand-nth [:red :blue :green :yellow :black])})
    :known-colors (fn [c]
                    {:color 
                     #_(case (first c)
                         \P "#EDA985"
                         \E "#D0E84A"
                         \T :lightblue
                         :black)
                     (rand-nth [;:lightgrey 
                                "#44C7F2"
                                ;:red 
                                "#129AC7"
                                "#126E8C"
                                "#7AD7F5"
                                "#5CA1B8"
                                "#9DBBC4"
                                ;:turquoise 
                                #_:blue 
                                #_:green 
                                ;:yellow
                                ])
                     :style :filled
                     :label c
                     })
    }
   :edge->descriptor {:bold (fn [n1 n2]
                              {:style :bold})}
   :node->descriptor 
   {:just-label 
    (fn [n]
      (let [t (-> n meta :type)]
        {:label (str n ":\n" 
                     (with-out-str 
                       (binding [*unparse-abbrev-alias* true
                                 *unparse-abbrev-class* true]
                         (pprint (unparse-type t)))))}))
    :default
    (fn [n] 
      (let [t (-> n meta :type)]
        {;:color (case (:op t)
         ;         :union :blue
         ;         :HMap :red
         ;         :IFn :yellow
         ;         :black)
         :color (if (namespace n)
                  :green
                  #_(case (:op t)
                      :union :blue
                      :HMap :red
                      :IFn :yellow
                      :black))
         :style (when (namespace n)
                  :filled)

         ;:shape :box
         :label (cond true #_(namespace n) (str n ":\n" 
                                                (with-out-str 
                                                  (binding [*unparse-abbrev-alias* true
                                                            *unparse-abbrev-class* true]
                                                    (pprint (unparse-type t)))))
                      :else (unmunge n))}))}})

(defn gen-current3 
  "Turn the currently inferred type environment
  into type aliases. Also print the alias environment."
  []
  (binding [*type-env* (atom {})
            *alias-env* (atom {})]
    (reset! *type-env*
            (into {}
                  (map (fn [[v t]]
                         [v (alias-hmap-type t)]))
                  (generate-tenv @results-atom)))
    (visualize
      {:top-levels #{`take-map}
       :viz-args {:options (-> premade-configs :options :small)
                  :node->descriptor (-> premade-configs
                                        :node->descriptor
                                        :just-label)}}
      @*alias-env* @*type-env*)))

(defn fv
  "Returns the aliases referred in this type, in order of
  discovery. If recur? is true, also find aliases
  referred by other aliases found."
  ([v] (fv v false))
  ([v recur?]
   (let [fv (fn [v] (fv v recur?))]
     (case (:op v)
       (:Top :unknown :val) []
       :HMap (into []
                   (mapcat fv)
                   (-> v :map vals))
       :HVec (into []
                   (mapcat fv)
                   (-> v :vec))
       :union (into []
                    (mapcat fv)
                    (-> v :types))
       :class (into []
                    (mapcat fv)
                    (-> v :args))
       :alias (conj
                (if recur?
                  (fv (resolve-alias v))
                  [])
                (:name v))
       :IFn (into []
                  (mapcat (fn [f']
                            (into (into [] 
                                        (mapcat fv) 
                                        (:dom f'))
                                  (fv (:rng f')))))
                  (:arities v))))))

(defn unmunge [n]
  (when-let [s (first (partition-by #{\_} (str n)))]
    (apply str s)))

;https://github.com/ToBeReplaced/mapply/blob/master/src/org/tobereplaced/mapply.cl
(defn mapply
  "Applies a function f to the argument list formed by concatenating
  everything but the last element of args with the last element of
  args.  This is useful for applying a function that accepts keyword
  arguments to a map."
  [f & args]
  (apply f (apply concat (butlast args) (last args))))

(defn visualize [{:keys [top-levels] :as config} alias-env type-env]
  (let [relevant (atom #{})
        type-env-edge-map 
        (reduce
          (fn [g [v t]]
            (if (or (contains? top-levels v)
                    (contains? top-levels :all))
              (let [fvs (fv t)]
                (swap! relevant into fvs)
                (assoc g v fvs))
              g))
          {}
          type-env)

        _ (prn "relevant" @relevant)

        alias-env-edge-map
        (loop [g {}
               wl (select-keys alias-env @relevant)]
          (if (empty? wl)
            g
            (let [[v t] (first wl)
                  fvs (fv t)]
              (recur (assoc g v fvs)
                     (merge
                       (dissoc wl v)
                       (select-keys alias-env
                                    (set/difference
                                      (set fvs)
                                      (set (keys g))
                                      (set (keys wl))
                                      #{v})))))))

        edge-map (merge type-env-edge-map
                        alias-env-edge-map)

        nodes (into #{}
                    (map (fn [[v t]]
                           (with-meta v {:type t})))
                    (select-keys (merge alias-env type-env)
                                 (keys edge-map)))]
    (mapply viz/view-graph 
            nodes
            edge-map
            (:viz-args config))))


(defn ppresults []
  (pprint
    (into #{}
          (map (fn [a]
                 (update a :type unparse-type)))
          (get-infer-results results-atom))))


(defn var-constraints 
  "Return the bag of constraints in the current results-atom
  for the given fully qualified var.
  
  eg. (var-constraints 'clojure.core.typed.test.mini-occ/parse-exp)
  "

  [vsym]
  (pprint (mapv unparse-infer-result 
                (-> (->> (get-infer-results results-atom) (group-by (comp :name first :path))) 
                    (get vsym)))))

;; TESTS

(defntrack foo 
  [a]
  (+ a 2))

(defntrack bar
  [f]
  (f 1))

(bar foo)
(bar foo)

(defntrack use-map [m]
  (merge m {:b ((:f m) foo)}))

(use-map {:a 1, :f bar})

(use-map {:a 1, :f bar})

(use-map {:f bar})

(use-map {:f bar})

(defntrack multi-arg 
  ([a] (inc a))
  ([s1 s2] (str s1 s2)))

(multi-arg 1)
(multi-arg "a" "a")
(multi-arg "b" "c")
(multi-arg "d" "e")

(defntrack take-map [m]
  {:a m})


(take-map nil)
(take-map {:a nil})
(take-map {:a {:a nil}})
(take-map {:a {:a {:a {:a nil}}}})

(defntrack postfix [& words]
  (reduce (fn [stack t]
            (if (fn? t)
              (let [[l r & m] stack]
                (cons (t r l) m))
              (cons t stack)))
          [] 
          words))

(postfix 1 2)

(defntrack mymapv [f c]
  (mapv f c))

(mymapv inc [1 2 3 4])
(mymapv str '[a b c d])
(mymapv (juxt first second) {'a 'b 'c 'd 'e 'f})

(defntrack iden [x] x)
;(defntrack f [x] (add1 x))

(defntrack invthunk [f]
  (f)
  f)

(defntrack invnested [f g]
  (f g)
  [f g])

(invnested (fn [g] (g))
           (fn [] (+ 1 2)))

#_
((track
   results-atom
   (fn [g] (g))
   [#'invnested (dom 2 0)])
 (track
   results-atom
   (fn [] (+ 1 2))
   [#'invnested (dom 2 0)]))

#_
((let [atm (atom #{})]
   (fn [g]
     (track
       results-atom
       ((fn [g] (g))
        (track results-atom g [#'invnested (dom 2 0) (dom 1 0)]))
       [#'invnested (dom 2 0) (rng 1)])))
 (let [atm (atom #{})]
   (fn []
     (track
       results-atom
       ((fn [] (+ 1 2)))
       [#'invnested (dom 2 1) (rng 0)]))))


; (Rec [f] [f -> f])
; (All [a] [a -> a])
(iden iden)
;(iden 1)
;(iden 'a)
;(iden [1])
;(iden [2 3])
;(iden [5 8])

(invthunk #(+ 2 3))

#_
(fn [f] ; f = #(+ 2 3)
  (let [f (let [app-info (atom {:infer-results #{}
                                :base-path '[#'invthunk]
                                :alias-paths #{}
                                :parent results-atom})]
            (with-meta
              (fn []
                (track
                  app-info
                  (f)
                  '[#'invthunk (dom 1 0) (rng 0)]))
              {:inferred (atom )}))]
    (f) ; [#'invthunk (dom 1 0) (rng 0)] : Long

    (swap! app-info update :equiv-paths conj '[#'invthunk (rng 1)])
    (track
      f   
    ; [#'invthunk (dom 1 0) (rng 0)] = [#'invthunk (rng 1)]
    )))

(defntrack maptrans [f]
  (map f))

(into []
      (maptrans identity)
      [1 2 3])

(into []
      (maptrans identity)
      ['a 'b 'c])

(into []
      (maptrans str)
      ['a 'b 'c])

(comment

(ppres)

)
