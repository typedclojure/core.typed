(ns ^:skip-wiki clojure.core.typed.cs-gen-new
  (:require [clojure.core.typed.utils :as u]
            [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.errors :as err]
            [clojure.core.typed.coerce-utils :as coerce]
            [clojure.core.typed.type-rep :as r :refer []]
            [clojure.core.typed.type-ctors :as c]
            [clojure.core.typed.filter-rep :as fr]
            [clojure.core.typed.filter-ops :as fo]
            [clojure.core.typed.object-rep :as or]
            ; use subtype? utility defined in this namespace
            [clojure.core.typed.subtype :as sub]
            [clojure.core.typed.parse-unparse :as prs]
            [clojure.core.typed.cs-rep :as cr]
            [clojure.core.typed.current-impl :as impl]
            [clojure.core.typed.util-vars :as vs]
            [clojure.core.typed.dvar-env :as denv]
            [clojure.core.typed.frees :as frees]
            [clojure.core.typed.free-ops :as free-ops]
            [clojure.core.typed.promote-demote :as prmt]
            [clojure.core.typed.subst :as subst]
            [clojure.core.typed.indirect-ops :as ind]
            [clojure.core.typed.indirect-utils :as ind-u]
            [clojure.math.combinatorics :as comb]
            [clojure.core.typed :as t :refer [letfn>]]
            [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [clojure.pprint :refer [pprint]]
            [clojure.core.typed.test.test-utils :refer [is-clj]]))

(defn maybe-Mu* [name body]
  (let [original-name (-> name r/make-F r/F-original-name)
        in? (contains? (frees/fv body) name)]
    (cond
      in? (let [v (r/Mu-maker (c/abstract name body))]
            (@#'c/with-original-names v original-name))
      :else body)))

(defn constraint? [c]
  (and (map? c)
       (symbol? (:constraint/var c))
       (r/Type? (:constraint/S c))
       (r/Type? (:constraint/T c))))

(defn constraint-set? [cs]
  (and (set? cs)
       (every? constraint? cs)))

(defn constraint-set-set? [css]
  (and (vector? css)
       (every? constraint-set? css)))

(defn constraint [S var T]
  {:pre [(r/Type? S)
         (symbol? var)
         (r/Type? T)]
   :post [(constraint? %)]}
  {:constraint/S S
   :constraint/var var
   :constraint/T T})

(defn constraint-set [& c]
  {:pre [(every? constraint? c)]
   :post [(constraint-set? %)]}
  (set c))

(defn constraint-set-set [& cs]
  {:pre [(every? constraint-set? cs)]
   :post [(constraint-set-set? %)]}
  (into []
        (distinct)
        cs))

(defn intersect-css2 [cs1 cs2]
  {:pre [(constraint-set-set? cs1)
         (constraint-set-set? cs2)]
   :post [(constraint-set-set? %)]}
  (apply
    constraint-set-set
    (for [c1 cs1
          c2 cs2]
      (set/union c1 c2))))

(defn intersect-css [& cs]
  {:pre [(every? constraint-set-set? cs)]
   :post [(constraint-set-set? %)]}
  (cond
    (empty? cs)
    (constraint-set-set?)

    (= 1 (count cs))
    (first cs)

    :else
    (reduce intersect-css2 (first cs) (next cs))))

(defn union-css [& cs]
  {:pre [(every? constraint-set-set? cs)]
   :post [(constraint-set-set? %)]}
  (into []
       (mapcat identity)
       cs))

(defn maybe-NotType-pred [p]
  (fn [t]
    (boolean
      (if (r/NotType? t)
        (p (:type t))
        (p t)))))

(def F-or-NotF (maybe-NotType-pred r/F?))

;; assume t is fully resolved at the top-level
(defn single [a_k t]
  {:pre [(symbol? a_k)
         (r/Type? t)
         (not (r/Union? t))]
   :post [(constraint? %)]}
  (let [ts (if (r/Intersection? t)
             (:types t)
             [t])
        ;; just looking for one type that is either a free variable
        ;; named a_k or a negation of that.
        already-found (atom nil)
        {tvar true other false}
        (group-by (maybe-NotType-pred
                    (fn [t]
                      {:pre [(r/Type? t)]}
                      (when-not @already-found
                        (when (r/F? t)
                          (let [found? (= (:name t) a_k)]
                            (when found?
                              (reset! already-found true))
                            found?)))))
                  ts)
        _ (assert (= 1 (count tvar))
                  (pr-str tvar))
        the-tvar (first tvar)
        _ (assert (r/Type? the-tvar))
        ]
    (cond
      (r/F? the-tvar)
      (constraint
        r/-nothing
        (:name the-tvar)
        (apply c/Un 
               ;; flip negations
               (map (fn [t]
                      (if (r/NotType? t)
                        (:type t)
                        (r/NotType-maker t)))
                    other)))

      (r/NotType? the-tvar)
      (constraint
        (apply c/In other)
        (:name (:type the-tvar))
        r/-any)
      
      :else (assert nil (str "What is this? " the-tvar)))))

(defmacro post-msg [assert msg]
  `(let [a# ~assert]
     (when-not a#
       (assert nil (str "Assertion failed: " '~assert "\n"
                        ~msg)))
     a#))

(defn norm [no-mention t M]
  {:pre [(set? no-mention)
         (r/Type? t)
         (set? M)]
   :post [(post-msg (constraint-set-set? %)
                    (pr-str %))]}
  (let [t (c/fully-resolve-type t)
        t (cond
            (r/Union? t) (apply c/Un (map 
                                       (fn [t]
                                         (let [t (c/fully-resolve-type t)]
                                           (if (r/Intersection? t)
                                             (apply c/In (map c/fully-resolve-type (:types t)))
                                             t)))
                                       (:types t)))
            (r/Intersection? t) (apply c/In (map c/fully-resolve-type (:types t)))
            :else t)]
    (cond
      ;; already seen this type, trivial solution
      (contains? M t) (constraint-set-set
                        (constraint-set))

      ;; we have an intersection, or a singleton intersection
      (or (r/Bottom? t)
          (not (r/Union? t)))
      (let [ts (if (r/Intersection? t)
                 (:types t)
                 [t])
            fs (filter F-or-NotF ts)]
        (cond
          (seq fs) 
          (let [fnames (map (fn [f] 
                              {:post [(symbol? %)]}
                              (:name 
                                (if (r/NotType? f)
                                  (:type f)
                                  f)))
                            fs)
                can-mention (sort (filter #(not (contains? no-mention %)) fnames))]
            (assert (every? symbol? can-mention))
            (cond
              ;; we have some variable that we can constrain
              (seq can-mention)
              (constraint-set-set
                (constraint-set
                  (single (first can-mention) t)))

              ;; all are in no-mention
              :else (norm no-mention (apply c/In (remove F-or-NotF ts)) 
                          (conj M t))))

          ;; no type variables
          :else
          (let [{fns true other false} (group-by (maybe-NotType-pred r/FnIntersection?) ts)]
            (cond

              ;; just have functions
              (and (empty? other)
                   (seq fns))
              (let [{P true N false} (group-by r/FnIntersection? fns)
                    N (set (mapcat (comp :types :type) N))
                    P (set (mapcat :types P))
                    _ (assert (every? r/Function? N))
                    _ (assert (every? r/Function? P))]
                (apply
                  union-css
                  (map (fn [n]
                         {:pre [(r/Function? n)]}
                         (let [_ (assert (= 1 (count (:dom n))))
                               s_n (first (:dom n))
                               t_n (:t (:rng n))
                               _ (assert (r/Type? s_n))
                               _ (assert (r/Type? t_n))
                               c1 (norm no-mention 
                                        (apply c/In s_n
                                               (map (fn [p]
                                                      (assert (= 1 (count (:dom p))))
                                                      (r/NotType-maker (first (:dom p))))
                                                    P))
                                        M)
                               c2 (apply intersect-css
                                         (map
                                           (fn [P']
                                             (assert (every? #(= 1 (count (:dom %))) P'))
                                             (let [c3 (norm no-mention 
                                                            (apply c/In s_n
                                                                   (map (comp r/NotType-maker first :dom) P'))
                                                            (conj M t))
                                                   P-without-P' (set/difference P P')
                                                   c4 (norm no-mention 
                                                            (apply c/In
                                                              (r/NotType-maker t_n)
                                                              (map
                                                                (fn [p]
                                                                  {:pre [(r/Function? p)]}
                                                                  (:t (:rng p)))
                                                                P-without-P'))
                                                            (conj M t))]
                                               (union-css c3 c4)))
                                           ;; want all proper subsets of P
                                           (map set (butlast (comb/subsets (seq P))))))]
                           (intersect-css c1 c2)))
                       N)))

              ;; other stuff (just RClasses for now)
              :else 
              (let [_ (assert (empty? fns))
                    _ (assert (every? (maybe-NotType-pred r/RClass?) other))
                    {P true N false} (group-by r/RClass? fns)
                    N (set (map :type N))
                    P (set P)
                    _ (assert (every? r/RClass? N))
                    _ (assert (every? r/RClass? P))]
                (cond
                  (sub/subtype? (apply r/Intersection? N)
                                (apply r/Union? P))
                  (constraint-set-set
                    (constraint-set))

                  :else (constraint-set-set)))))))

      (r/Union? t)
      (apply intersect-css 
             (map (fn [t_i]
                    (norm no-mention t_i M))
                  (:types t)))

      ;; no solution
      :else (constraint-set-set))))

(defn csmerge [no-mention cs M]
  {:pre [(constraint-set? cs)
         (set? M)]
   :post [(constraint-set-set? %)]}
  (let [ts (group-by :constraint/var cs)
        ord-tvars (sort (keys ts))
        ;; turn all constraints of form:
        ;;    S1 <: a <: T1
        ;;    S2 <: a <: T2
        ;;    ...
        ;;    Sn <: a <: Tn
        ;;
        ;; into 
        ;;
        ;;    S1 v S2 v ... v Sn <: a <: T1 ^ T2 ^ ... ^ Tn
        cs (apply
             constraint-set
             (reduce 
               (fn [cs var-constraints]
                 {:pre [(every? constraint? cs)
                        (seq var-constraints)
                        (every? constraint? var-constraints)]
                  :post [(every? constraint? %)]}
                 (conj cs
                       (constraint
                         (apply c/Un (map :constraint/S var-constraints))
                         (:constraint/var (first var-constraints))
                         (apply c/In (map :constraint/T var-constraints)))))
               []
               (map #(get ts %) ord-tvars)))
        _ (assert (constraint-set? cs))
        
        ;; check, for each constraint S <: a <: T,
        ;;  that S <: T
        not-in-M (first
                   (filter
                     (fn [{:keys [:constraint/S :constraint/T] :as c}]
                       {:pre [(constraint? c)]}
                       (contains? M (c/In S (r/NotType-maker T))))
                     cs))
        ;; if there exists a contract such that S <: T, but S ^ ~T is not in M,
        ;; then recur.
        css
        (if-let [{:keys [:constraint/S :constraint/T]} not-in-M]
          (let [_ (assert (constraint? not-in-M))
                t (c/In S (r/NotType-maker T))
                l (intersect-css
                    (constraint-set-set cs)
                    (norm no-mention t #{}))]
            (apply union-css
                   (map (fn [C']
                          {:pre [(constraint-set? C')]
                           :post [(constraint-set-set? %)]}
                          (csmerge C' (conj M t)))
                        l)))
          (constraint-set-set cs))]
    css))

(defn cssmerge [no-mention css]
  {:pre [(set? no-mention)
         (constraint-set-set? css)]
   :post [(constraint-set-set? %)]}
  (apply union-css
         (reduce (fn [css cs]
                   {:pre [(every? constraint-set-set? css)
                          (constraint-set? cs)]
                    :post [(every? constraint-set-set? %)]}
                   (conj css (csmerge no-mention cs #{})))
                 []
                 css)))

(defn cnorm 
  "Normalize types Ss <: Ts, pairwise."
  [no-mention Ss Ts]
  {:pre [(set? no-mention)
         (every? symbol? no-mention)
         (every? r/Type? Ss)
         (every? r/Type? Ts)
         (= (count Ss) (count Ts))]
   :post [(constraint-set-set? %)]}
  (apply intersect-css
         (map (fn [s t]
                (norm no-mention (c/In s (r/NotType-maker t)) #{}))
              Ss Ts)))

(defn substitution? [m]
  (and (map? m)
       (every? symbol? (keys m))
       (every? r/Type? (vals m))))

(def placeholder-prefix "placeholder_4422__")

(defn placeholder-tvar-name []
  (gensym placeholder-prefix))

(defn placeholder? [n]
  {:pre [(symbol? n)]
   :post [(boolean? %)]}
  (.startsWith (name n) placeholder-prefix))

(defn solve [cs]
  {:pre [(constraint-set? cs)]
   :post [(substitution? %)]}
  (into {}
        (map (fn [{:keys [:constraint/S :constraint/var :constraint/T]}]
               [var (c/In (c/Un S (r/make-F (placeholder-tvar-name)))
                          T)]))
        cs))

(declare unify)

(defn csssolve [css]
  {:pre [(constraint-set-set? css)]
   :post [(every? substitution? %)]}
  (mapv solve css))

(defn unify [E]
  {:pre [(substitution? E)]
   :post [(substitution? %)]}
  (if (empty? E)
    {}
    (let [;; select smallest variable
          a (first (sort (keys E)))
          t_a (get E a)
          rec_a (maybe-Mu* a t_a)
          E' (into {}
                   (map (fn [[k v]]
                          [k (subst/subst-all (c/make-simple-substitution [a] [rec_a])
                                              v)]))
                   (dissoc E a))
          sigma (unify E')]
      (merge {a (subst/subst-all (c/make-simple-substitution
                                   (keys E')
                                   (vals E'))
                                 rec_a)} 
             sigma))))

(defn clean-placeholders [s]
  {:pre [(substitution? s)]
   :post [(substitution? %)]}
  (into {}
        (map (fn [[k v]]
               [k (let [fvs (filter (comp placeholder? key) (frees/fv-variances v))]
                    (reduce (fn [t [pl variance]]
                              (subst/subst-all
                                (c/make-simple-substitution
                                  [pl]
                                  [(case variance
                                     :covariant r/-nothing
                                     :contravariant r/-any)])
                                t))
                            v
                            fvs))]))
        s))

(defn unify-all [substs]
  {:pre [(every? substitution? substs)]
   :post [(every? substitution? %)]}
  (mapv (comp clean-placeholders unify) substs))

(defn ppcss [css]
  (pprint
    (read-string
      (pr-str
        (mapv (fn [cs]
                (map 
                  (fn [{:keys [:constraint/S :constraint/var :constraint/T]}]
                    [S :< var :< T])
                  (sort-by :constraint/var cs)))
              css)))))

(defn ppsubst [subst]
  (pprint
    (read-string
      (pr-str
        subst))))

(deftest norm-test
  (is-clj
    (let [left (r/make-FnIntersection
                 (r/make-Function
                   [(r/make-F 'a)]
                   (c/RClass-of Boolean)))
          right (r/make-FnIntersection
                  (r/make-Function
                    [(r/make-F 'b)]
                    (r/make-F 'b)))
          t (c/In left (r/NotType-maker right))]
      (norm #{}
            t
            #{})))
  (is-clj
    (let [left (r/make-FnIntersection
                 (r/make-Function
                   [(r/make-F 'a)]
                   (c/RClass-of Boolean)))
          right (r/make-FnIntersection
                  (r/make-Function
                    [(r/make-F 'b)]
                    (r/make-F 'b)))
          t (c/In left (r/NotType-maker right))
          no-mentions #{}
          cs (norm no-mentions t #{})
          cs (cssmerge no-mentions cs)]
      cs)
      )
  (is-clj
    (let [left1 (r/make-FnIntersection
                 (r/make-Function
                   [(r/make-F 'a)]
                   (c/RClass-of Boolean)))
          right1 (r/make-FnIntersection
                  (r/make-Function
                    [(r/make-F 'b)]
                    (r/make-F 'b)))
          left2 (r/make-FnIntersection
                 (r/make-Function
                   [(c/Un (c/RClass-of Integer)
                          (c/RClass-of Boolean))]
                   (c/RClass-of Integer)))
          right2 (r/make-FnIntersection
                  (r/make-Function
                    [(r/make-F 'a)]
                    (r/make-F 'b)))
          no-mentions #{}
          css (cnorm no-mentions [left1 left2] [right1 right2])
          _ (assert (seq css))
          css (cssmerge no-mentions css)
          ;_ (ppcss css)
          _ (assert (seq css))
          substs (csssolve css)
          ;_ (ppsubst subst)
          substs (unify-all substs)
          _ (run! ppsubst substs)
          ]
      true)))
