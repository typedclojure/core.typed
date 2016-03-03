(ns clojure.core.typed.runtime-infer
  (:require [clojure.pprint :refer [pprint]]
            [clojure.set :as set]
            [clojure.test :refer :all]
            [rhizome.viz :as viz]))

#_
(defalias Node
  (U '{:op :val :val Any}
     '{:op :HMap :map (Map Kw Node)}
     '{:op :HVec :vec (Vec Node)}
     '{:op :union :types (Set Node)}
     '{:op :class :class Class}
     '{:op :IFn :arities (Vec '{:op :IFn1
                                :dom (Vec Node)
                                :rng Node})}
     '{:op :var :name Sym}
     '{:op :Top}))

;(defalias RTInfo
;  "Used to summarise the types of values. The Vector's generally
;   denote a place where many alternatives are possible.
;
;  eg. if `1`, `'a` and `nil` pass through the same path, we generate:
;
;      {:class [Number Symbol]
;       :val [nil]}"
;  (HMap :optional 
;        {:class (Vec Class)
;         :fn (Map Int {:dom (Map Int RTInfo)
;                       :rng RTInfo})
;         ;; indexed by gensym
;         :map (Map Sym 
;                   ;; indexed by actual key of map, always a keyword
;                   (Map Kw RTInfo))
;         :val (Vec (U Kw nil false))}))

; (Atom (Map Sym RTInfo))
(def remember-var (atom {}))

; RTInfo -> Node
(defn rtinfo->type [m]
  (let [cls (when-let [cls (:class m)]
              (map (fn [c]
                     {:op :class :class c})
                   cls))
        tfn (when-let [tfn (:fn m)]
              (let [as (mapv
                         (fn [[arity f]]
                           {:op :IFn1
                            :dom (mapv (fn [n]
                                         (rtinfo->type (get (:dom f) n)))
                                       (range (count (:dom f))))
                            :rng (rtinfo->type (:rng f))})
                         tfn)]
                (when (seq as)
                  #{{:op :IFn :arities as}})))
        tmap (when-let [tmap (:map m)]
               (let [vs (vals tmap)
                     ms (set
                          (map
                            (fn [m]
                              {:op :HMap
                               :map (into {}
                                          (map (fn [[k v]]
                                                 [k (rtinfo->type v)]))
                                          m)})
                            vs))]
                 (not-empty ms)))
        tvec nil #_(when-let [tvec (:vec m)]
               (let [vs (vals (:map m))]
                 (cond
                   (empty? vs)   nil

                   (== (count vs) 1)
                   #{(let [vv (first vs)]
                       `'~(mapv (fn [n]
                                  (rtinfo->type (get vv n)))
                                (range (count vv))))}

                   :else #{clojure.lang.IPersistentVector})))
        _ (assert ((some-fn nil? set?) tvec))
        tvals (when-let [tvals (:val m)]
                (set
                  (map (fn [t]
                         {:op :val :val t})
                       tvals)))
        ts (into (set (or cls tvals)) 
                 (concat tvec tmap tfn))
        ;; remove IFn if we already know it's a function
        ts (if tfn
             (disj ts {:op :class :class clojure.lang.IFn})
             ts)]
    (cond
      (seq ts)
      (if (== (count ts) 1)
        (first ts)
        {:op :union :types ts})

      :else {:op :Top})))

; [Node :-> Any]
(defn unparse-node [{:as m}]
  (case (:op m)
    :val (let [t (:val m)]
           (cond
             ((some-fn nil? false?) t) t
             (keyword? t) `'~t
             :else 'Any))
    :union (list* 'U (map unparse-node (:types m)))
    :HMap `'~(into {}
                   (map (fn [[k v]]
                          [k (unparse-node v)]))
                   (:map m))
    :IFn (let [as (map
                    (fn [{:keys [dom rng]}]
                      (conj (mapv unparse-node dom)
                            :->
                            (unparse-node rng)))
                    (:arities m))]
           (if (== 1 (count as))
             (first as)
             (list* 'IFn as)))
    :class (:class m)
    :Top 'Any
    (assert nil (str "No unparse-node case: " m))))

;; Graph data structure
;;
;;  nil + {:a nil} =>
;;
;;  {'a nil
;;   'b {:a (U 'b 'a}}

(def val? (some-fn nil? keyword? symbol? number?))

; Graph Any -> (U nil Sym)
(defn lookup-val [g v]
  {:pre [(map? g)
         (val? v)]
   :post [((some-fn symbol? nil?) %)]}
  (reduce-kv
    (fn [m k v']
      (when (= v' v)
        (reduced k)))
    nil
    g))

; Node Node -> Node
(defn union [s t]
  (cond
    (and (#{:union} (:op s))
         (#{:union} (:op t)))
    {:op :union
     :types (set/union (:types s)
                       (:types t))}

    (#{:union} (:op s))
    (update s :types conj t)

    (#{:union} (:op t))
    (update t :types conj s)

    :else
    (let [ts (into #{} [s t])]
      (if (== 1 (count ts))
        (first ts)
        {:op :union
         :types ts}))))

; Graph Node -> '[Graph Node]
(defn join [seen t]
  {:pre [(map? seen)
         (map? t)
         (keyword? (:op t))]
   :post [(vector? %)
          (map? (first %))
          (map? (second %))]}
  (prn "join" t)
  (letfn []
    (case (:op t)
      (:union)
      (reduce 
        (fn [[seen _] t]
          (join seen t))
        [seen t]
        (:types t))

      (:val :var)
      [seen t]

      ;; generate a new name for each entry's value, which is a unique node
      ;; in our final graph
      :HMap
      (let [ks (-> t :map keys set)

            [seen m]
            (reduce-kv
              (fn [[seen m] k v]
                (let [[seen v'] (join seen v)]
                  [seen (update-in m 
                                   [:map k]
                                   (fn [n]
                                     (cond
                                       (nil? n) v'
                                       :else (union n v'))))]))
              [seen {:op :HMap :map {}}] ;; initial compacted type
              (:map t))

            ;; find an entry in the graph that has the same keys, if possible.
            ;; we do this here to let the `seen` map be as big as possible.
            e (some (fn [v]
                      (when (-> v val :op #{:HMap})
                        (when (= ks (-> v val :map keys set))
                          v)))
                    seen)
            [seen m] (if e
                       ;; merge with existing `seen` map
                       (reduce-kv
                         (fn [[seen m] k v]
                           (let [[seen v'] (join seen v)]
                             [seen (update-in m [:map k] union v')]))
                         [seen m]
                         (:map (val e)))
                       [seen m])
            nme (or (some-> e key)
                    (gensym (apply str "map-" 
                                   (concat (apply interpose "-" (map name ks))
                                           ["__"]))))
            seen (assoc seen nme m)]
        [seen {:op :var :name nme}])

      (assert nil (str "Cannot join op: " (pr-str (:op t)))))))

(deftest simplify-test
  (is (= (join {} {:op :val :val nil})
         [{} {:op :val :val nil}]))
  (is (= (join {'b {:op :HMap
                    :map {:a {:op :val :val nil}}}}
               {:op :HMap :map {:a {:op :val :val nil}}})
         [{'b {:op :HMap
               :map {:a {:op :val :val nil}}}}
          {:op :var :name 'b}]))
  (is (= (join {'b {:op :HMap,
                    :map {:a {:op :val,
                              :val nil}}}}
               {:op :HMap
                :map {:a 
                      {:op :HMap
                       :map {:a 
                             {:op :HMap
                              :map {:a 
                                    {:op :val :val nil}}}}}}}
               )
         {'a {:op :val, :val nil}
          'b {:op :HMap,
              :map {:a {:op :union
                        :types [{:op :var,
                                 :name 'a}
                                {:op :var,
                                 :name 'b}]}}}}))
  (is (let [[seen v] (join {} {:a nil})]
        (and (#{:var} (:op v))
             (contains? seen (:name v)))))
  (is (let [[seen v] (join {} {:op :HMap
                               :map {:a 
                                     {:op :HMap
                                      :map {:a 
                                            {:op :HMap
                                             :map {:a 
                                                   {:op :val :val nil}}}}}}})]
        (and (#{:var} (:op v))
             (contains? seen (:name v)))))
  (is (visualize
        (first
          (join {}
                {:op :if
                 :test {:op :val
                        :val nil}
                 :then {:op :if
                        :test {:op :val
                               :val 'a}
                        :then {:op :val
                               :val :a}
                        :else {:op :val
                               :val nil}}
                 :else {:op :val
                        :val 1}})))))

; Node -> (Set Sym)
(defn fv [v]
  (case (:op v)
    :val #{}
    :HMap (apply set/union (-> v :map vals fv))
    :union (apply set/union (-> v :types fv))
    :var #{(:name v)}
    #{}))

; Graph -> Any
(defn visualize [gr]
  (viz/view-graph (map (fn [[v1 v2]]
                         (with-meta v1
                                    {:val v2}))
                       gr)
                  (reduce
                    (fn [g [s v]]
                      (assoc g s (fv v)))
                    {}
                    gr)
                  :node->descriptor (fn [n] {:label (str #_#_n ": " (-> n meta :val pr-str))})))

; [:-> nil]
(defn ppres []
  (pprint (into {}
                (map (fn [[k v]]
                       [k (-> v rtinfo->type unparse-node)]))
                @remember-var)))

; [Var :-> (U nil Any)]
(defn type-of-var [v]
  (get @remember-var v))

; [Var :-> Sym]
(defn var->symbol [^clojure.lang.Var v]
  {:pre [(var? v)]
   :post [(symbol? %)]}
  (symbol (str (ns-name (.ns v))) (str (.sym v))))

; [Seqable Int :-> Int]
(defn bounded-length [s len]
  (clojure.lang.RT/boundedLength s len))

;(defalias Path (Vec (U Int Kw Sym)))

;(defalias Value Any)

; [Value Path :-> Value]
(defn infer-val [v path]
  {:pre [(vector? path)]}
  (cond
    ;; only accurate up to 20 arguments.
    ;; all arities 21 and over will collapse into one.
    (fn? v) (do
              ;; if this is never called, remember it is actually a function
              (swap! remember-var
                     update-in
                     (conj path :class)
                     (fnil conj [])
                     clojure.lang.IFn)
              (fn [& args]
                (let [blen (bounded-length args 20) ;; apply only realises 20 places
                      args (map-indexed
                             (fn [n v]
                               (infer-val v (conj path :fn blen :dom n)))
                             args)]
                  (infer-val
                    (apply v args)
                    (conj path :fn blen :rng)))))

    (vector? v) (let [len (count v)]
                  (reduce-kv
                    (fn [e k v]
                      (let [v' (infer-val v (conj path :vec len k))]
                        (if (identical? v v')
                          e
                          (assoc e k v'))))
                    v
                    v))

    ;; maps with keyword keys
    (and (or (instance? clojure.lang.PersistentHashMap v)
             (instance? clojure.lang.PersistentArrayMap v))
         (every? keyword? (keys v)))
    (let [g (gensym)]
      (reduce
        (fn [m k]
          (let [orig-v (get m k)
                v (infer-val orig-v (conj path :map g k))]
            ;; only assoc if needed
            (if (identical? v orig-v)
              m
              (assoc m k v))))
        v
        (keys v)))

    ;(instance? clojure.lang.IAtom v)
    ;(reify

    ((some-fn keyword? nil? false?) v)
    (do
      (swap! remember-var
             update-in
             (conj path :val)
             (fnil conj [])
             v)
      v)


    :else (do
            (swap! remember-var
                   update-in
                   (conj path :class)
                   (fnil conj [])
                   (class v))
            v)))

(defn infer-var' [vr]
  {:pre [(var? vr)]}
  (infer-val @vr [(var->symbol vr)]))

(defmacro infer-var [v]
  `(infer-var' (var ~v)))


(defn foo [a]
  (+ a 2))

(defn bar [f]
  (f 1))

(bar (infer-var foo))

(defn use-map [m]
  (merge m {:b ((:f m) foo)}))

(use-map {:a 1, :f bar})

((infer-var use-map) {:a 1, :f bar})

((infer-var use-map) {:f bar})

((infer-var use-map) {:f (infer-var bar)})

(defn multi-arg 
  ([a] (inc a))
  ([s1 s2] (str s1 s2)))

((infer-var multi-arg) 1)
((infer-var multi-arg) "a" "a")

(defn take-map [m]
  m)

; (Rec [x]
;   (U nil '{:a x}))

; (U nil
;    '{:a nil}
;    '{:a '{:a nil}}
;    '{:a '{:a '{:a '{:a nil}}}})

; Step 1:
; - break down types into their subcomponents
; - base types are the base cases
; - recursively defined types refer to base types instead of original types
; - reuse existing names where possible

; Step 2:
; - figure out if this should be a recursive type
; - the non-base types should be reused at least once
;   - if none are reused, abort
;     eg.
;     (U nil
;        '{:a Num}
;        '{:b Num})
;     
;     (Let [x nil
;           n Num
;           y '{:a n}  ;not referenced
;           z '{:b n}] ;not referenced
;       (U x
;          y
;          z))

; Step 3:
; - build and simplify recursive type
; - build recursive type by unrolling the subcomponents
;   eg. 
;     (Let [x1 nil
;           x2 '{:a x1}
;           x3 '{:a x2}
;           x  '{:a x3}
;           y x3
;           z x2]
;       (U x
;          y
;          z))
;     
;     (Rec [x]
;       (U nil
;          '{:a x}
;          '{:a '{:a x}}
;          '{:a '{:a '{:a x}}}))
; - simplify by testing if we can make a new supertype by deleting a clause
;     (Rec [x]
;       (U nil
;          '{:a x}
;          '{:a '{:a x}}
;          '{:a '{:a '{:a x}}}))
;     <:
;     (Rec [x]
;       (U nil
;          '{:a x}
;              ;;; DELETED '{:a '{:a x}}
;          '{:a '{:a '{:a x}}}))
;     <:
;     (Rec [x]
;       (U nil
;          '{:a x}
;              ;;; DELETED '{:a '{:a x}}
;              ;;; DELETED '{:a '{:a '{:a x}}}
;          ))

;(Let [x nil
;      y '{:a x}
;      z '{:a y}
;      a '{:a z}
;      b '{:a a}]
;  (U x
;     y
;     z
;     b))
;
;(U nil
;   '{:a Num}
;   '{:b Num})
;
;(Let [x nil
;      n Num
;      y '{:a n}
;      z '{:b n}]
;  (U x
;     y
;     z))


;(Rec [x]
;  (U nil
;    '{:a x}
;    '{:a '{:a nil}}
;    '{:a '{:a '{:a '{:a nil}}}})


;(Let [n nil]
;      y '{:a n}]
;  (U n
;     '{:a y}))

((infer-var take-map) nil)
((infer-var take-map) {:a nil})
((infer-var take-map) {:a {:a nil}})
((infer-var take-map) {:a {:a {:a {:a nil}}}})

(ppres)
