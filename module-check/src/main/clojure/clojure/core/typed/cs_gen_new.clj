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
            [clojure.core.typed.debug :refer [dbg]]
            [clojure.tools.trace :refer [trace-vars]]
            [clojure.core.typed.test.test-utils :refer [is-clj clj]])
  (:import (clojure.lang Seqable)))

(declare ppcss
         ppcss-str
         cs-gen-normalized-no-tvar
         ppsubst
         )

(t/ann gen-repeat [Number (t/Seqable Any) -> (t/Seqable Any)])
(defn ^:private gen-repeat [times repeated]
  (reduce (fn [acc cur]
            (concat acc cur))
          []
          (repeat times repeated)))

(defn fully-resolve-under-Not [t]
  (let [t (c/fully-resolve-type t)
        t' (cond
             (r/NotType? t) (c/-not (fully-resolve-under-Not (:type t)))
             ((some-fn r/Intersection?
                       r/FnIntersection?) t) 
             (apply c/In (mapv fully-resolve-under-Not (:types t)))
             (r/Extends? t) (apply c/In (concat
                                          (mapv fully-resolve-under-Not (:extends t))
                                          ;; is this the correct way to convert :without?
                                          (mapv (comp c/-not fully-resolve-under-Not) (:without t))))
             (r/Union? t) (apply c/Un (mapv fully-resolve-under-Not (:types t)))
             :else (c/fully-resolve-type t))]
    ;(prn "fully-resolve-under-Not" t t')
    t'))

(defn group-by-boolean [p s]
  (group-by (comp boolean p) s))

(defn maybe-Mu* [name body]
  (let [original-name (-> name r/make-F r/F-original-name)
        in? (contains? (frees/fv body) name)]
    (cond
      in? (let [v (r/Mu-maker (c/abstract name body))]
            (@#'c/with-original-names v original-name))
      :else body)))

(defn constraint? [c]
  (cr/c? c))

(defn constraint-set? [cs]
  (cr/cset-entry? cs))

(defn constraint-set-set? [css]
  (cr/cset? css))

(defn constraint [S var T]
  {:pre [(r/Type? S)
         (symbol? var)
         (r/Type? T)]
   :post [(constraint? %)]}
  (cr/c-maker S var T nil))

(defn constraint-set [& cs]
  {:pre [(every? constraint? cs)]
   :post [(constraint-set? %)]}
  (let [ts (group-by :X cs)
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
        cs (reduce
             (fn [cs var-constraints]
               {:pre [(every? constraint? cs)
                      (seq var-constraints)
                      (every? constraint? var-constraints)]
                :post [(every? constraint? %)]}
               (conj cs
                     (constraint
                       (apply c/Un (map :S var-constraints))
                       (:X (first var-constraints))
                       (apply c/In (map :T var-constraints)))))
             []
             (map #(get ts %) ord-tvars))]
    (assert (distinct? (map :X cs)))
    (cr/make-cset-entry
      (zipmap (map :X cs) cs))))

(defn constraint-set-set [& cs]
  {:pre  [(every? constraint-set? cs)]
   :post [(constraint-set-set? %)]}
  (cr/cset-maker (set cs)))

(def fail-css (constraint-set-set))
(def success-css 
  (constraint-set-set
    (constraint-set)))

(defn c-meet 
  ([c1 c2] (c-meet c1 c2 nil))
  ([{S  :S X  :X T  :T :as c1}
    {S* :S X* :X T* :T :as c2}
    var]
   (when-not (or var (= X X*))
     (err/int-error (str "Non-matching vars in c-meet:" X X*)))
   (let [S (c/Un S S*)
         T (c/In T T*)]
     (cr/c-maker S (or var X) T nil))))

(defn dcon-meet [dc1 dc2]
  {:pre [(cr/dcon-c? dc1)
         (cr/dcon-c? dc2)]
   :post [((some-fn nil? cr/dcon-c?) %)]}
  (cond
    (and (cr/dcon-exact? dc1)
         (or (cr/dcon? dc2) 
             (cr/dcon-exact? dc2)))
    (let [{fixed1 :fixed rest1 :rest} dc1
          {fixed2 :fixed rest2 :rest} dc2]
      (when (and rest2 (= (count fixed1) (count fixed2)))
        (cr/dcon-exact-maker
          (mapv
            (fn [c1 c2]
              (c-meet c1 c2 (:X c1)))
            fixed1 fixed2)
          (c-meet rest1 rest2 (:X rest1)))))
    ;; redo in the other order to call the first case
    (and (cr/dcon? dc1)
         (cr/dcon-exact? dc2))
    (dcon-meet dc2 dc1)

    (and (cr/dcon? dc1)
         (not (:rest dc1))
         (cr/dcon? dc2)
         (not (:rest dc2)))
    (let [{fixed1 :fixed} dc1
          {fixed2 :fixed} dc2]
      (when (= (count fixed1) (count fixed2))
        (cr/dcon-maker
          (doall
            (for [[c1 c2] (map vector fixed1 fixed2)]
              (c-meet c1 c2 (:X c1))))
          nil)))

    (and (cr/dcon? dc1)
         (not (:rest dc1))
         (cr/dcon? dc2))
    (let [{fixed1 :fixed} dc1
          {fixed2 :fixed rest :rest} dc2]
      (assert rest)
      (when (>= (count fixed1) (count fixed2))
        (cr/dcon-maker
          (let [vector' (t/inst vector c c t/Any t/Any t/Any t/Any)]
            (doall
              (t/for
                [[c1 c2] :- '[c c], (map vector' fixed1 (concat fixed2 (repeat rest)))]
                :- c
                (c-meet c1 c2 (:X c1)))))
          nil)))

    (and (cr/dcon? dc1)
         (cr/dcon? dc2)
         (not (:rest dc2)))
    (dcon-meet dc2 dc1)

    (and (cr/dcon? dc1)
         (cr/dcon? dc2))
    (let [{fixed1 :fixed rest1 :rest} dc1
          {fixed2 :fixed rest2 :rest} dc2
          [shorter longer srest lrest]
          (if (< (count fixed1) (count fixed2))
            [fixed1 fixed2 rest1 rest2]
            [fixed2 fixed1 rest2 rest1])]
      (cr/dcon-maker
        (mapv (fn [c1 c2] (c-meet c1 c2 (:X c1)))
              longer (concat shorter (repeat srest)))
        (c-meet lrest srest (:X lrest))))

    (and (cr/dcon-dotted? dc1)
         (cr/dcon-dotted? dc2))
    (let [{fixed1 :fixed c1 :dc {bound1 :name} :dbound} dc1
          {fixed2 :fixed c2 :dc {bound2 :name} :dbound} dc2]
      (when (and (= (count fixed1) (count fixed2))
                     (= bound1 bound2))
        (cr/dcon-dotted-maker 
          (mapv (fn [c1 c2] (c-meet c1 c2 (:X c1))) fixed1 fixed2)
          (c-meet c1 c2 bound1) bound1)))

    (and (cr/dcon? dc1)
         (cr/dcon-dotted? dc2))
    nil

    (and (cr/dcon-dotted? dc1)
         (cr/dcon? dc2))
    nil

    (and (cr/dcon-repeat? dc1)
         (cr/dcon? dc2)
         (not (:rest dc2)))
    (let [{fixed1 :fixed repeated :repeat} dc1
          {fixed2 :fixed} dc2
          fixed1-count (count fixed1)
          fixed2-count (count fixed2)
          repeat-count (count repeated)
          diff (- fixed2-count fixed1-count)]
      (assert repeated)
      (when (and (>= fixed2-count fixed1-count)
                 (zero? (rem diff repeat-count)))
        (cr/dcon-repeat-maker
          (let [vector' (t/inst vector c c Any Any Any Any)]
            (doall
              (t/for 
                [[c1 c2] :- '[c c], (map vector'
                                         fixed2
                                         (concat fixed1
                                                 (gen-repeat (quot diff repeat-count) repeated)))]
                :- c
                (c-meet c1 c2 (:X c1)))))
          repeated)))
    (and (cr/dcon-repeat? dc2)
         (cr/dcon? dc1)
         (not (:rest dc1)))
    (dcon-meet dc2 dc1)

    (every? cr/dcon-repeat? [dc1 dc2])
    (let [[{short-fixed :fixed short-repeat :repeat}
           {long-fixed :fixed long-repeat :repeat}]
          (sort-by (fn [x] (-> x :fixed count)) [dc1 dc2])
          s-fixed-count (count short-fixed)
          l-fixed-count (count long-fixed)
          s-repeat-count (count short-repeat)
          l-repeat-count (count long-repeat)
          diff (- l-fixed-count s-fixed-count)
          _ (assert (= s-repeat-count l-repeat-count))
          vector' (t/inst vector c c Any Any Any Any)
          merged-repeat (mapv (fn [c1 c2] (c-meet c1 c2 (:X c1)))
                              short-repeat long-repeat)]
      (assert (zero? (rem diff s-repeat-count)))
      (cr/dcon-repeat-maker
        (mapv (fn [c1 c2] (c-meet c1 c2 (:X c1)))
              long-fixed
              (concat short-fixed
                      (gen-repeat (quot diff s-repeat-count) short-repeat)))
        merged-repeat))

    :else (err/nyi-error (str "NYI dcon-meet " dc1 dc2))))

(defn merge-with-or-nil [f m1 m2]
  {:pre [(map? m1)
         (map? m2)]
   :post [((some-fn nil? map?) %)]}
  (reduce (fn [m [k v]]
            (if-let [[_ v-m] (find m k)]
              (if-some [r (f v-m v)]
                (assoc m k r)
                (reduced nil))
              (assoc m k v)))
          m1 m2))

(defn dmap-meet [dm1 dm2]
  {:pre [(cr/dmap? dm1)
         (cr/dmap? dm2)]
   :post [((some-fn cr/dmap? nil?) %)]}
  (some-> (merge-with-or-nil dcon-meet (:map dm1) (:map dm2))
          cr/dmap-maker))

(defn cset-meet [{maps1 :maps :as x} {maps2 :maps :as y}]
  {:pre [(cr/cset? x)
         (cr/cset? y)]
   :post [(cr/cset? %)]}
  (let [maps (into #{}
                   (remove nil?)
                   (for [{map1 :fixed dmap1 :dmap} maps1
                         {map2 :fixed dmap2 :dmap} maps2]
                     (when-let [cm (merge-with-or-nil c-meet map1 map2)]
                       (when-let [dm (dmap-meet dmap1 dmap2)]
                         (cr/cset-entry-maker cm dm)))))]
    (cr/cset-maker maps)))

(defn intersect-css2 [cs1 cs2]
  {:pre [(constraint-set-set? cs1)
         (constraint-set-set? cs2)]
   :post [(constraint-set-set? %)]}
  (cset-meet cs1 cs2))

(defn cset-meet* [args]
  {:pre [(every? cr/cset? args)]
   :post [(cr/cset? %)]}
  (reduce cset-meet
          (cr/cset-maker #{(cr/cset-entry-maker {} (cr/dmap-maker {}))})
          args))

(defn intersect-css [& cs]
  {:pre [(every? constraint-set-set? cs)]
   :post [(constraint-set-set? %)]}
  (let [res (cset-meet* (set cs))]
    (prn "intersect-css in")
    (run! ppcss cs)
    (prn "intersect-css out")
    (ppcss res)
    res))

(defn union-css [& cs]
  {:pre [(every? constraint-set-set? cs)]
   :post [(constraint-set-set? %)]}
  (cr/cset-maker
    (into #{}
          (mapcat :maps)
          cs)))

(defn maybe-NotType-pred [p]
  (fn [t]
    (boolean
      (if (r/NotType? t)
        (p (:type t))
        (p t)))))

(def F-or-NotF (maybe-NotType-pred r/F?))

;; assume t is fully resolved at the top-level
;; if variable a_k is contained in t as a negation,
;; returns constraint t\~a_k <: a_k
;; otherwise, returns a_k <: t\a_k 

(defn single [a_k t]
  {:pre [(symbol? a_k)
         (r/Type? t)
         (not (r/Union? t))]
   :post [(constraint-set? %)]}
  ;(prn "single" a_k t)
  (let [ts (if (r/Intersection? t)
             (:types t)
             [t])
        ;; just looking for one type that is either a free variable
        ;; named a_k or a negation of that.
        already-found (atom nil)
        {tvar true other false}
        (group-by-boolean 
          (maybe-NotType-pred
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
        c (cond
            (r/F? the-tvar)
            (constraint
              r/-nothing
              (:name the-tvar)
              (apply c/Un 
                     ;; flip negations
                     (map (fn [t]
                            (if (r/NotType? t)
                              (:type t)
                              (c/-not t)))
                          other)))

            (r/NotType? the-tvar)
            (constraint
              (apply c/In other)
              (:name (:type the-tvar))
              r/-any)

            :else (assert nil (str "What is this? " the-tvar)))
        ]
    (constraint-set c)))

(defmacro post-msg [assert msg]
  `(let [a# ~assert]
     (when-not a#
       (assert nil (str "Assertion failed: " '~assert "\n"
                        ~msg)))
     a#))

(declare norm)

(defn norm2 [no-mention S T M]
  {:pre [(r/Type? S)
         (r/Type? T)]}
  (prn "norm2" S T)
  (prn "calling with (unsimplified)"
       "(I" S "(Not" T "))")
  (norm no-mention (c/In S (c/-not T)) M))

(defn norm [no-mention t M]
  {:pre [(set? no-mention)
         (r/Type? t)
         (set? M)]
   :post [(post-msg (constraint-set-set? %)
                    (pr-str %))]}
  (prn "norm:" t)
  (let [t (fully-resolve-under-Not t)
        res (cond
              ;; already seen this type, trivial solution
              (contains? M t) success-css

              (and (not (r/Bottom? t))
                   (r/Union? t))
              (do
                ;(prn "union" t)
                (apply intersect-css 
                       (map (fn [t_i]
                              (norm no-mention t_i M))
                            (:types t))))

              :else
              (let [ts (if (r/Intersection? t)
                         (:types t)
                         [t])
                    fs (filter F-or-NotF ts)]
                ;(prn "non union" ts)
                (cond
                  (seq fs)
                  (let [;_ (prn "norm: frees case" fs)
                        fnames (map (fn [f] 
                                      {:post [(symbol? %)]}
                                      (:name 
                                        (if (r/NotType? f)
                                          (:type f)
                                          f)))
                                    fs)
                        can-mention (sort (remove no-mention fnames))]
                    (assert (every? symbol? can-mention))
                    (cond
                      ;; we have some variable that we can constrain
                      (seq can-mention)
                      (constraint-set-set
                        (single (first can-mention) t))

                      ;; all are in no-mention
                      :else (norm no-mention (apply c/In (remove F-or-NotF ts))
                                  (conj M t))))

                  ;; no type variables
                  :else
                  (cs-gen-normalized-no-tvar no-mention ts M))))]
    (prn "norm result:")
    (ppcss res)
    res
    ))

(defn norm-with-variance
  [no-mention variance S T M]
  {:pre [(r/variance? variance)
         (r/AnyType? S)
         (r/AnyType? T)]
   :post [(constraint-set-set? %)]}
  ;(prn "norm-with-variance" S T variance)
  (let [norm2 #(norm2 no-mention %1 %2 M)
        ret (case variance
              (:covariant :constant) (norm2 S T)
              :contravariant (norm2 T S)
              :invariant (intersect-css (norm2 S T)
                                        (norm2 T S)))]
    ;(println "norm-with-variance return" "\n" (ppcss-str ret))
    ret))

(defn upcast-RClass
  [S T]
  {:pre [(r/RClass? S)
         (r/RClass? T)]
   :post [((some-fn nil? r/Type?) %)]}
  (prn "upcast-RClass" (class S) S (class T) T)
  (let [rsupers (c/RClass-supers* S)
        relevant-S (some #(when (r/RClass? %)
                            (and (= (:the-class %) (:the-class T))
                                 %))
                         (map c/fully-resolve-type (conj rsupers S)))]
    relevant-S))

(defn norm-RClass
  [no-mention S T M]
  {:pre [(r/RClass? S)
         (r/RClass? T)]
   :post [(constraint-set-set? %)]}
  ;(prn "norm-RClass" S T)
  (let [rsupers (c/RClass-supers* S)
        relevant-S (some #(when (r/RClass? %)
                            (and (= (:the-class %) (:the-class T))
                                 %))
                         (map c/fully-resolve-type (conj rsupers S)))]
    ;(prn "relevant-S" relevant-S)
    (cond
      relevant-S
      (let [css (mapv (fn [vari si ti]
                        (norm-with-variance no-mention vari si ti M))
                      (:variances T)
                      (:poly? relevant-S)
                      (:poly? T))]
        ;(apply println "norm-RClass after" relevant-S T (map ppcss css))
        (apply intersect-css css))
      :else (constraint-set-set))))

(declare cs-gen)

(defn cs-gen2 [no-mention S T M]
  (cs-gen no-mention S T M))

(defn cs-gen-filter [no-mention s t M]
  {:pre [(fr/Filter? s)
         (fr/Filter? t)]
   :post [(constraint-set-set? %)]}
  (let [norm #(norm no-mention %1 %2 M)]
    (cond
      (= s t) success-css
      (fr/TopFilter? t) success-css

      (and (fr/TypeFilter? s)
           (fr/TypeFilter? t)
           (and (= (:path s) (:path t))
                (= (:id s) (:id t))))
      (intersect-css (norm (:type s) (:type t))
                     (norm (:type t) (:type s)))

      (and (fr/NotTypeFilter? s)
           (fr/NotTypeFilter? t)
           (and (= (:path s) (:path t))
                (= (:id s) (:id t))))
      (intersect-css (norm (:type s) (:type t))
                     (norm (:type t) (:type s)))

      ; simple case for unifying x and y in (& (is x sym) ...) (is y sym)
  ;    (and (fr/AndFilter? s)
  ;         (fr/TypeFilter? t)
  ;         (every? fo/atomic-filter? (:fs s))
  ;         (= 1 (count (filter fr/TypeFilter? (:fs s)))))
  ;    (let [tf (first (filter fr/TypeFilter? (:fs s)))]
  ;      (cs-gen-filter V X Y tf t))
      :else fail-css)))

(defn cs-gen-filter-set [no-mentions s t M]
  {:pre [(fr/FilterSet? s)
         (fr/FilterSet? t)]
   :post [(constraint-set-set? %)]}
  (cond
    (= s t) success-css
    :else
    (let [{s+ :then s- :else} s
          {t+ :then t- :else} t]
      (intersect-css (cs-gen-filter no-mentions s+ t+ M)
                     (cs-gen-filter no-mentions s- t- M)))))

(defn cs-gen-datatypes-or-records 
  [no-mention S T M]
  {:pre [(every? r/DataType? [S T])]}
  (cond
    ;fail
    (not (= (:the-class S) (:the-class T)))
    (constraint-set-set)

    :else (apply intersect-css
                 (map (fn [variance s t]
                        (norm-with-variance no-mention variance s t M))
                      (:variances T) (:poly? S) (:poly? T)))))

(defn cs-gen-object [no-mention s t M]
  {:pre [(or/RObject? s)
         (or/RObject? t)]
   :post [(constraint-set-set? %)]}
  (cond
    (= s t) success-css
    (or/EmptyObject? t) success-css
    ;;FIXME do something here
    :else fail-css))

(declare cnorm)

(defn cs-gen-HSequential
  [no-mention S T M]
  {:pre [(r/HSequential? S)
         (r/HSequential? T)]
   :post [(cr/cset? %)]}
  (let [norm* (fn [Ss Ts]
                (cnorm no-mention Ss Ts M))]
    (apply intersect-css
      (concat
        (cond
          ;simple case
          (not-any? (some-fn :rest :drest :repeat) [S T])
          [(norm* (:types S) (:types T))]

          ;rest on right, optionally on left
          (and (:rest T)
               (not-any? (some-fn :drest :repeat) [S]))
          (concat [(norm* (:types S) (concat (:types T)
                                             (repeat (- (count (:types S))
                                                        (count (:types T)))
                                                     (:rest T))))]
                  (when (:rest S)
                    [(norm* (:rest S) (:rest T))]))

          ; repeat on right, nothing on left
          (and (:repeat T)
               (not-any? (some-fn :rest :drest :repeat) [S]))
          (let [s-types (:types S)
                t-types (:types T)
                s-types-count (count s-types)
                t-types-count (count t-types)]
            (if (and (>= s-types-count t-types-count)
                     (zero? (rem s-types-count t-types-count)))
              [(norm* s-types (gen-repeat (/ s-types-count
                                             t-types-count)
                                          t-types))]
              [(constraint-set-set)]))

          ; repeat on left, rest on right
          (and (:repeat S)
               (:rest T))
          (let [s-types (:types S)
                t-types (:types T)
                s-types-count (count s-types)
                t-types-count (count t-types)]
            (if (>= s-types-count t-types-count)
              [(norm* s-types (concat t-types
                                      (repeat (- s-types-count
                                                 t-types-count)
                                              (:rest T))))]
              (err/nyi-error (pr-str "NYI HSequential inference " S T))))

          ; repeat on left, drest on right
          (and (:repeat S)
               (:drest T))
          (let [_ (assert nil "FIXME repeat on left, drest on right")
                ;{t-dty :pre-type dbound :name} (:drest T)
                ;_ (when-not (Y dbound)
                ;    (fail! S T))
                ;merged-X (merge X {dbound (Y dbound)})
                ;get-list-of-c (fn get-list-of-c [S-list]
                ;                (mapv #(get-c-from-cmap % dbound)
                ;                      (t/for [s :- r/Type, S-list]
                ;                        :- cset
                ;                        (cs-gen V merged-X Y s t-dty))))
                ;repeat-c (get-list-of-c (:types S))
                ]
            ;[(assoc-in (cr/empty-cset X Y) [:maps 0 :dmap :map dbound] (cr/dcon-repeat-maker [] repeat-c))]
            )

          ;; dotted on the left, nothing on the right
          (and (:drest S)
               (not-any? (some-fn :rest :drest :repeat) [T]))
          (assert nil "FIXME repeat on left, drest on right")
          #_(let [{dty :pre-type dbound :name} (:drest S)]
            (when-not (Y dbound)
              (fail! S T))
            (when-not (<= (count (:types S)) (count (:types T)))
              (fail! S T))
            (let [vars (var-store-take dbound dty (- (count (:types T))
                                                     (count (:types S))))
                  new-tys (doall (t/for
                                   [var :- t/Sym, vars] :- r/AnyType
                                   (subst/substitute (r/make-F var) dbound dty)))
                  new-s-hsequential (r/-hsequential (concat (:types S) new-tys))
                  new-cset (cs-gen-HSequential V 
                                               ;move dotted lower/upper bounds to vars
                                               (merge X (zipmap vars (repeat (Y dbound)))) Y new-s-hsequential T)]
              [(move-vars-to-dmap new-cset dbound vars)]))

          ;; dotted on the right, nothing on the left
          (and (not-any? (some-fn :rest :drest :repeat) [S])
               (:drest T))
          (assert nil "FIXME repeat on left, drest on right")
          #_(let [{dty :pre-type dbound :name} (:drest T)]
            (when-not (Y dbound)
              (fail! S T))
            (when-not (<= (count (:types T)) (count (:types S)))
              (fail! S T))
            (let [vars (var-store-take dbound dty (- (count (:types S)) (count (:types T))))
                  new-tys (doall
                            (t/for
                              [var :- t/Sym, vars] :- r/AnyType
                              (subst/substitute (r/make-F var) dbound dty)))
                  new-t-hsequential (r/-hsequential (concat (:types T) new-tys))
                  new-cset (cs-gen-HSequential V 
                                               ;move dotted lower/upper bounds to vars
                                               (merge X (zipmap vars (repeat (Y dbound)))) Y S new-t-hsequential)]
              [(move-vars-to-dmap new-cset dbound vars)]))

          ;TODO cases
          :else (err/nyi-error (pr-str "NYI HSequential inference " S T)))
        (map (fn [fs1 fs2]
               (cs-gen-filter-set no-mention fs1 fs2 M))
             (:fs S) (:fs T))
        (map (fn [o1 o2]
               (cs-gen-object no-mention o1 o2 M))
             (:objects S) (:objects T))))))

(defn cs-gen-TApp
  [no-mention S T M]
  {:pre [(r/TApp? S)
         (r/TApp? T)]
   :post [(constraint-set-set? %)]}
  (let [Srator (c/fully-resolve-type (:rator S))
        Trator (c/fully-resolve-type (:rator T))]
    (cond
      (not= Srator Trator) fail-css
      :else
      (let [;; these should be TypeFn's (I think?)
            _ (assert ((every-pred r/TypeFn?) Srator Trator))
            variances (:variances Srator)]
        (assert (= (count variances)
                   (count (:rands S))
                   (count (:rands T))))
        (apply intersect-css
          (mapv (fn [var s1 t1]
                  (norm-with-variance no-mention var s1 t1 M))
                variances (:rands S) (:rands T)))))))

(declare cs-gen-Function)

(defn cs-gen-FnIntersection
  [no-mention S T M]
  {:pre [(r/FnIntersection? S)
         (r/FnIntersection? T)]
   :post [(constraint-set-set? %)]}
  (apply intersect-css
         (map
           (fn [t-arr]
             {:pre [(r/Function? t-arr)]}
             ;; for each t-arr, we need to some combination of s-arr's that fit under.
             ;; This is where we implement (I [a -> c] [b -> c]) <: [(U a b) -> c]
             ;; TODO we can probably memoize some of these results, and combine
             ;; them as needed.
             ;; FIXME Aha! This is where dovetailing is needed.
             ;;  Computing all the subsets of S for every T is exponential,
             ;;  and, for nothing if one of the simpler ones just worked.
             (let [results (mapv
                             (fn [s-arrs]
                               {:pre [(every? r/Function? s-arrs)]}
                               (prn "function combinations"
                                    (count s-arrs))
                               (let [css (cond 
                                           ;; I think ?
                                           (empty? s-arrs)
                                           fail-css

                                           (= 1 (count s-arrs))
                                           (cs-gen-Function no-mention (first s-arrs t-arr M))

                                           :else
                                           (let [carrs (mapv
                                                         (fn [s-arr]
                                                           {:pre [(r/Function? s-arr)]}
                                                           ;; memoize this?
                                                           (cs-gen-Function no-mention s-arr t-arr M))
                                                         s-arrs)]
                                             (prn "carrs")
                                             (apply intersect-css carrs)))]
                                 css))
                             (comb/subsets (vec (:types S))))
                   comb (apply union-css results)]
               comb))
           (:types T))))

(defn cs-gen-flow-set [no-mention s t M]
  {:pre [(r/FlowSet? s)
         (r/FlowSet? t)]
   :post [(constraint-set-set? %)]}
  (cond
    (= s t) success-css
    :else
    (let [{n1 :normal} s
          {n2 :normal} t]
      (cs-gen-filter no-mention n1 n2 M))))

(defn cs-gen-Result
  [no-mention S T M]
  {:pre [(r/Result? S)
         (r/Result? T)]}
  (intersect-css (norm2 no-mention (r/Result-type* S) (r/Result-type* T) M)
                 (cs-gen-filter-set no-mention (r/Result-filter* S) (r/Result-filter* T) M)
                 (cs-gen-object no-mention (r/Result-object* S) (r/Result-object* T) M)
                 (cs-gen-flow-set no-mention (r/Result-flow* S) (r/Result-flow* T) M)))

(defn cs-gen-Function-just-rests [no-mention S T M]
  ;just a rest arg, no drest, no keywords, no prest
  {:pre [(and (some-fn :rest [S T])
              (not-any? (some-fn :drest :kws :prest) [S T]))]
   :post [(constraint-set-set? %)]}
  (let [norm* (fn [Ss Ts] (cnorm no-mention Ss Ts M))
        arg-mapping (cond
                      ;both rest args are present, so make them the same length
                      (and (:rest S) (:rest T))
                      (norm* (cons (:rest T) (u/pad-right (count (:dom S)) (:dom T) (:rest T)))
                             (cons (:rest S) (u/pad-right (count (:dom T)) (:dom S) (:rest S))))
                      ;no rest arg on the right, so just pad left and forget the rest arg
                      (and (:rest S) (not (:rest T)))
                      (let [new-S (u/pad-right (count (:dom T)) (:dom S) (:rest S))]
                        ;                            (prn "infer rest arg on left")
                        ;                            (prn "left dom" (map prs/unparse-type (:dom S)))
                        ;                            (prn "right dom" (map prs/unparse-type (:dom T)))
                        ;                            (prn "new left dom" (map prs/unparse-type new-S))
                        (norm* (:dom T) new-S))
                      ;no rest arg on left, or wrong number = fail
                      :else fail-css)
        ret-mapping (cs-gen-Result no-mention (:rng S) (:rng T) M)]
    (intersect-css arg-mapping ret-mapping)))

(defn cs-gen-Function-prest-on-left [no-mention S T M]
  ; prest on left, nothing on right
  {:pre [(and (:prest S)
              (not-any? (some-fn :rest :drest :kws :prest) [T]))]}
  (let [s-dom (:dom S)
        t-dom (:dom T)
        s-dom-count (count s-dom)
        t-dom-count (count t-dom)]
    (if (and (<= t-dom-count s-dom-count)
             (not (zero? (rem (- t-dom-count s-dom-count)
                              (count (-> S :prest :types))))))
      fail-css
      (let [norm* #(cnorm no-mention %1 %2 M)
            norm2 #(norm2 no-mention %1 %2 M)
            [short-T rest-T] (split-at s-dom-count t-dom)
            short-cs (norm* short-T s-dom)
            s-prest-types (-> S :prest :types)
            rest-S (gen-repeat (/ (count rest-T) (count s-prest-types)) s-prest-types)
            rest-cs (norm* rest-T rest-S)
            ret-mapping (norm2 (:rng S) (:rng T))]
        (intersect-css short-cs rest-cs ret-mapping)))))

(defn cs-gen-Function-prest-drest [no-mention S T M]
  (assert nil "TODO cs-gen-Function-prest-drest")
  #_(let [{t-dty :pre-type dbound :name} (:drest T)
        _ (when-not (Y dbound)
            (fail! S T))
        S-dom (:dom S)
        S-dom-count (count S-dom)
        T-dom (:dom T)
        T-dom-count (count T-dom)
        S-prest-types (-> S :prest :types)
        S-prest-types-count (count S-prest-types)
        merged-X (merge X {dbound (Y dbound)})
        get-list-of-c (fn get-list-of-c [S-list]
                        (mapv #(get-c-from-cmap % dbound)
                              (map
                                (fn [s] (cs-gen V merged-X Y t-dty s))
                                S-list)))
        repeat-c (get-list-of-c S-prest-types)
        ret-mapping (cg (:rng S) (:rng T))]
    (if (<= S-dom-count T-dom-count)
      ; hard mode
      (let [T-rest-count (- T-dom-count S-dom-count)
            [arg-S-prest remain-S-prest] (split-at (rem T-rest-count
                                                        S-prest-types-count) S-prest-types)
            new-S (concat S-dom
                          (gen-repeat (quot T-rest-count S-prest-types-count) S-prest-types)
                          arg-S-prest)
            arg-mapping (cs-gen-list V X Y T-dom new-S)
            fixed-c (if (= (count arg-S-prest) 0)
                      []
                      (get-list-of-c remain-S-prest))
            darg-mapping (assoc-in (cr/empty-cset X Y)
                                   [:maps 0 :dmap :map dbound]
                                   (cr/dcon-repeat-maker fixed-c repeat-c))]
        (cset-meet* [arg-mapping darg-mapping ret-mapping]))
      ; easy mode
      (let [[arg-S rest-S] (split-at T-dom-count S-dom)
            arg-mapping (cs-gen-list V X Y T-dom arg-S)
            fixed-c (get-list-of-c rest-S)
            darg-mapping (assoc-in (cr/empty-cset X Y)
                                   [:maps 0 :dmap :map dbound]
                                   (cr/dcon-repeat-maker fixed-c repeat-c))]
        (cset-meet* [arg-mapping darg-mapping ret-mapping])))))

(defn cs-gen-Function
  [no-mention S T M]
  {:pre [(r/Function? S)
         (r/Function? T)]
   :post [(constraint-set-set? %)]}
  (let [norm2 (fn [S T] (norm2 no-mention S T M))
        norm* (fn [Ss Ts] (cnorm no-mention Ss Ts M))]
    (cond
      ;easy case - no rests, drests, kws, prest
      (not-any? (some-fn :rest :drest :kws :prest) [S T])
      (intersect-css
             ; contravariant
             (norm* (:dom T) (:dom S))
             ; covariant
             (cs-gen-Result no-mention (:rng S) (:rng T) M))

      ;just a rest arg, no drest, no keywords, no prest
      (and (some-fn :rest [S T])
           (not-any? (some-fn :drest :kws :prest) [S T]))
      (cs-gen-Function-just-rests no-mention S T M)

      ; :rest is less restricted than :prest
      (and (:prest S)
           (:rest T)
           (> (-> S :prest :types count) 1))
      fail-css

      (and (:rest S)
           (:prest T))
      (cs-gen-Function-just-rests no-mention S T M)

      ; prest on left, nothing on right
      (and (:prest S)
           (not-any? (some-fn :rest :drest :kws :prest) [T]))
      (cs-gen-Function-prest-on-left no-mention S T M)

      ; prest on left, drest on right
      (and (:prest S)
           (:drest T))
      (cs-gen-Function-prest-drest no-mention S T M)

      ;; dotted on the left, nothing on the right
      (and (:drest S)
           (not-any? (some-fn :rest :drest :kws :prest) [T]))
      (assert nil "TODO cs-gen-Function-dotted-left-nothing-right")
      #_(cs-gen-Function-dotted-left-nothing-right V X Y S T)

      ;; dotted on the right, nothing on the left
      (and (not-any? (some-fn :rest :drest :kws :prest) [S])
           (:drest T))
      (assert nil "TODO cs-gen-Function-dotted-right-nothing-left")
      #_(cs-gen-Function-dotted-right-nothing-left V X Y S T)

      ;; * <: ...
      (and (:rest S)
           (:drest T))
      (assert nil "TODO cs-gen-Function-star-<-dots")
      #_
      (cs-gen-Function-star-<-dots cg V X Y S T)

      ;; ... <: *
      ; Typed Racket notes that this might not be a correct subtyping case?
      (and (:drest S)
           (:rest T))
      (assert nil "TODO cs-gen-Function-dots-<-star")
      #_
      (cs-gen-Function-dots-<-star cg V X Y S T)

      :else 
      (err/nyi-error (pr-str "NYI Function inference " (prs/unparse-type S) (prs/unparse-type T))))))

(defn cs-gen-Protocol
  [no-mention S T M]
  {:pre [(r/Protocol? S)
         (r/Protocol? T)]
   :post [(constraint-set-set? %)]}
  (let [norm2 #(norm2 no-mention %1 %2 M)]
    (if (= (:the-var S)
           (:the-var T))
      (apply intersect-css
             (for
               [[vari si ti]
                (map vector
                     (:variances T)
                     (:poly? S)
                     (:poly? T))]
               (case vari
                 (:covariant :constant) (norm2 si ti)
                 :contravariant (norm2 ti si)
                 :invariant (intersect-css (norm2 si ti)
                                           (norm2 ti si)))))
      fail-css)))

(defn upcast-to-RClass [S T]
  (cond
    (r/RClass? S) (upcast-RClass S T)
    ;; FIXME
    :else nil))

(defn upcast-to-Function [S]
  {:pre [(and (r/Type? S)
              (not (r/Union? S))
              (not (r/Top? S))
              (not (r/F? S))
              (not (r/Intersection? S))
              (not (r/FnIntersection? S)))]
   :post [((some-fn nil? r/Type?) %)]}
  (cond
    (r/Function? S) S
    (c/keyword-value? S) (c/keyword->Fn (:val S))
    :else nil))

(defn upcast-S [S T]
  {:pre [(r/Type? S)
         (r/Type? T)]
   :post [((some-fn nil? r/Type?) %)]}
  (prn "upcast-S" S T)
    (let []
      (cond
        (r/Top? T)
        r/-any

        (r/Bottom? T)
        r/-nothing

        ((some-fn r/Union? r/Intersection?) S T)
        (err/int-error "Shouldn't pass Union/Intersection to cs-gen")

        (and (r/Value? S)
             (r/Value? T))
        S
        
        ;values are subtypes of their classes
        (r/Value? S)
        (impl/impl-case
          :clojure (if (nil? (:val S))
                     nil
                     (apply c/In (c/RClass-of (class (:val S)))
                            (cond 
                              ;keyword values are functions
                              (keyword? (:val S)) [(c/keyword->Fn (:val S))]
                              ;strings have a known length as a seqable
                              (string? (:val S)) [(r/make-ExactCountRange (count (:val S)))])))
          :cljs (cond
                  (integer? (:val S)) (r/IntegerCLJS-maker)
                  (number? (:val S)) (r/NumberCLJS-maker)
                  (string? (:val S)) (r/StringCLJS-maker)
                  (con/boolean? (:val S)) (r/BooleanCLJS-maker)
                  (symbol? (:val S)) (c/DataType-of 'cljs.core/Symbol)
                  (keyword? (:val S)) (c/DataType-of 'cljs.core/Keyword)
                  :else nil))

        ;; constrain body to be below T
        (or (r/Poly? S)
            (r/Poly? T))
        (err/int-error (str "bad Poly"))
;        (r/Poly? S)
;        (let [nms (c/Poly-fresh-symbols* S)
;              body (c/Poly-body* nms S)
;              bbnds (c/Poly-bbnds* nms S)]
;          (prn "Poly?" body T)
;          (free-ops/with-bounded-frees (zipmap (map r/F-maker nms) bbnds)
;            (norm2 body T)))

        (or (r/Name? S)
            (r/Name? T))
        (err/int-error (str "bad name"))

;        (r/Name? S)
;        (norm2 (c/resolve-Name S) T)
;
;        (r/Name? T)
;        (norm2 S (c/resolve-Name T))

        ; copied from TR's infer-unit
        ;; if we have two mu's, we rename them to have the same variable
        ;; and then compare the bodies
        ;; This relies on (B 0) only unifying with itself, and thus only hitting the first case of this `match'
;        (and (r/Mu? S)
;             (r/Mu? T))
;        (norm2 (r/Mu-body-unsafe S) (r/Mu-body-unsafe T))

        (or (r/Mu? S)
            (r/Mu? T))
        (err/int-error (str "bad Mu"))

        ;; other mu's just get unfolded
;        (r/Mu? S) (norm2 (c/unfold S) T)
;        (r/Mu? T) (norm2 S (c/unfold T))

;        (and (r/TApp? S)
;             (not (r/F? (:rator S))))
;        (norm2 (c/resolve-TApp S) T)
;
;        (and (r/TApp? T)
;             (not (r/F? (:rator T))))
;        (norm2 S (c/resolve-TApp T))
;
;        (and (r/Extends? S)
;             (r/Extends? T))
;        (norm2 (apply c/In (:extends S) (mapv r/NotType? (:without S)))
;               (apply c/In (:extends T) (mapv r/NotType? (:without T))))
;
;        (r/Extends? S)
;        (norm2 (apply c/In (:extends S) (mapv r/NotType? (:without S)))
;               T)
;
;        (r/Extends? T)
;        (norm2 S
;               (apply c/In (:extends T) (mapv r/NotType? (:without T))))
;
;
;        (r/App? S)
;        (norm2 (c/resolve-App S) T)
;
;        (r/App? T)
;        (norm2 S (c/resolve-App T))
;
;;        (and (r/DataType? S)
;;             (r/DataType? T)) (cs-gen-datatypes-or-records no-mention S T M)
;
;        ; handle Record as HMap
;        (r/Record? S) (norm2 (c/Record->HMap S) T)
;
;;        (and (r/HeterogeneousVector? S)
;;             (r/HeterogeneousVector? T))
;;        (cs-gen-HSequential no-mention (c/HVec->HSequential S) (c/HVec->HSequential T) M)
;
;;        (and (r/HeterogeneousSeq? S)
;;             (r/HeterogeneousSeq? T))
;;        (cs-gen-HSequential no-mention (c/HSeq->HSequential S) (c/HSeq->HSequential T) M)
;
;;        (and (r/HeterogeneousList? S)
;;             (r/HeterogeneousList? T))
;;        (cs-gen-HSequential no-mention (c/HList->HSequential S) (c/HList->HSequential T) M)
;
;        ; HList/HSeq/HVector are HSequential
;;        (and ((some-fn r/HeterogeneousList?
;;                       r/HeterogeneousSeq?
;;                       r/HeterogeneousVector?)
;;              S)
;;             (r/HSequential? T))
;;        (norm (cond
;;                (r/HeterogeneousList? S) (c/HList->HSequential S) 
;;                (r/HeterogeneousVector? S) (c/HVec->HSequential S) 
;;                :else (c/HSeq->HSequential S))
;;              T)
;
;        ; HList is a HSeq
;        (and (r/HeterogeneousList? S)
;             (r/HeterogeneousSeq? T))
;        (cs-gen-HSequential no-mention (c/HList->HSequential S) (c/HSeq->HSequential T) M)
;
;        (and (r/HSequential? S)
;             (r/HSequential? T))
;        (cs-gen-HSequential no-mention S T M)
;
;        (and (r/HeterogeneousMap? S)
;             (r/HeterogeneousMap? T))
;        ; assumes optional/mandatory/absent keys are disjoint
;        (let [Skeys (set (keys (:types S)))
;              Tkeys (set (keys (:types T)))
;              Soptk (set (keys (:optional S)))
;              Toptk (set (keys (:optional T)))
;              Sabsk (:absent-keys S)
;              Tabsk (:absent-keys T)]
;          (cond
;            ; All keys must be values
;            (not (every? r/Value? 
;                         (concat
;                           Skeys Tkeys
;                           Soptk Toptk
;                           Sabsk Tabsk)))
;            fail-css
;
;            ; If the right is complete, the left must also be complete
;            (and (c/complete-hmap? T)
;                 (not (c/complete-hmap? S)))
;            fail-css
;
;            ; check mandatory keys
;            (if (c/complete-hmap? T)
;              ; If right is complete, mandatory keys must be identical
;              (= Tkeys Skeys)
;              ; If right is partial, all mandatory keys on the right must also appear mandatory on the left
;              (seq (set/difference Tkeys Skeys)))
;            fail-css
;
;            ; All optional keys on the right must appear either absent, mandatory or optional
;            ; on the left
;            (seq (set/difference Toptk 
;                                 (set/union Skeys 
;                                            Soptk 
;                                            Sabsk)))
;            fail-css
;
;            ; All absent keys on the right must appear absent on the left
;            (seq (set/difference Tabsk Sabsk))
;            fail-css
;
;            :else
;            ; now check the values with cs-gen
;            (let [;only check mandatory entries that appear on the right
;                  check-mandatory-keys Tkeys
;                  Svals (map (:types S) check-mandatory-keys)
;                  Tvals (map (:types T) check-mandatory-keys)
;                  _ (assert (every? r/Type? Svals))
;                  _ (assert (every? r/Type? Tvals))
;                  ;only check optional entries that appear on the right
;                  ; and also appear as mandatory or optional on the left
;                  check-optional-keys (set/intersection
;                                        Toptk (set/union Skeys Soptk))
;                  Sopts (map (some-fn (:types S) (:optional S)) check-optional-keys)
;                  Topts (map (:optional T) check-optional-keys)
;                  _ (assert (every? r/Type? Sopts))
;                  _ (assert (every? r/Type? Topts))]
;              (intersect-css (norm* Svals Tvals)
;                             (norm* Sopts Topts)))))
;
;        (and (r/GetType? S)
;             (not (r/F? (:target S))))
;        (norm2 (c/-resolve S) T)
;
;        (and (r/GetType? T)
;             (not (r/F? (:target T))))
;        (norm2 S (c/-resolve T))
;
;        (and (r/AssocType? S)
;             (r/AssocType? T))
;        (let [{S-target :target S-entries :entries S-dentries :dentries} S
;              {T-target :target T-entries :entries T-dentries :dentries} T
;              target-cset (cg S-target T-target)
;              S-entries (reduce concat S-entries)
;              T-entries (reduce concat T-entries)
;              entries-cset (norm* S-entries T-entries)
;              _ (when (and S-dentries T-dentries)
;                  (err/nyi-error "NYI dentries of Assoc in cs-gen"))
;              ]
;          (intersect-css target-cset entries-cset))
;
;        (and (r/AssocType? S)
;             (r/RClass? T)
;             ; (Map xx yy)
;             (= 'clojure.lang.IPersistentMap (:the-class T)))
;        (assert nil "TODO AssocType RClass")
;#_
;        (let [{:keys [target entries dentries]} S
;              {:keys [poly? the-class]} T
;              dentries-cset (when-let [{dty :pre-type dbound :name} dentries]
;                              (when (and dbound (not (Y dbound)))
;                                (fail! S T))
;                              ;(println "passed when")
;                              (let [merged-X (merge X {dbound (Y dbound)})
;                                    get-list-of-c (fn get-list-of-c [t-list]
;                                                    (mapv #(get-c-from-cmap % dbound)
;                                                          (t/for [t :- r/Type, t-list]
;                                                                :- cset
;                                                                (cs-gen V merged-X Y dty t))))
;                                    repeat-c (get-list-of-c poly?)]
;                                (assoc-in (cr/empty-cset X Y)
;                                          [:maps 0 :dmap :map dbound]
;                                          ; don't constrain on fixed, otherwise will fail
;                                          ; on (assoc m x y)
;                                          (cr/dcon-repeat-maker [] repeat-c))))
;              ;_ (println "dentries-cset" dentries-cset)
;
;              ; if it's nil, we also accept it
;              map-cset (when-not (r/Nil? target)
;                         (cs-gen V X Y target T))
;              entries-keys (map first entries)
;              entries-vals (map second entries)
;              cg #(cs-gen V X Y %1 %2)
;              key-cset (map cg entries-keys (repeat (first poly?)))
;              val-cset (map cg entries-vals (repeat (second poly?)))]
;          (cset-meet* (concat (when map-cset [map-cset]) key-cset val-cset)))
;
;        ; transform Record to HMap, this is not so useful until we can do
;        ; cs-gen Assoc with dentries with HMap
;        (and (r/AssocType? S)
;             (r/Record? T))
;        (let [{:keys [target]} S
;              target-cset (norm2 target T)
;              cset (norm2 S (c/Record->HMap T))]
;          (intersect-css target cset))
;
;; Completeness matters:
;;
;; (Assoc x ':a Number ':b Long) <: (HMap {:a Number :b Long} :complete? true)
;; (Assoc x ':a Number ':b Long ':c Foo) <!: (HMap {:a Number :b Long} :complete? true)
;        (and (r/AssocType? S)
;             (r/HeterogeneousMap? T))
;        (assert nil "TODO AssocType HeterogeneousMap")
;#_
;        (let [;_ (prn "cs-gen Assoc HMap")
;              {:keys [target entries dentries]} S
;              {:keys [types absent-keys]} T
;              _ (when-not (nil? dentries) (err/nyi-error (pr-str "NYI cs-gen of dentries AssocType with HMap " S T)))
;              Assoc-keys (map first entries)
;              Tkeys (keys types)
;              ; All keys must be keyword values
;              _ (when-not (every? c/keyword-value? (concat Tkeys Assoc-keys absent-keys))
;                  (fail! S T))
;              ; All keys explicitly not in T should not appear in the Assoc operation
;              absents-satisfied?
;              (if (c/complete-hmap? T)
;                ; if T is partial, we just need to ensure the absent keys in T
;                ; don't appear in the entries of the Assoc.
;                (empty?
;                  (set/intersection
;                    (set absent-keys)
;                    (set (map first entries))))
;                ; if T is complete, all entries of the Assoc should *only* have
;                ; keys that are mandatory keys of T.
;                (empty?
;                  (set/difference
;                    (set (map first entries))
;                    (set Tkeys))))
;              _ (when-not absents-satisfied?
;                  (fail! S T))
;              ;; Isolate the entries of Assoc in a new HMap, with a corresponding expected HMap.
;              ; keys on the right overwrite those on the left.
;              assoc-args-hmap (c/make-HMap :mandatory (into {} entries))
;              expected-assoc-args-hmap (c/make-HMap :mandatory (select-keys (:types assoc-args-hmap) (set Assoc-keys)))
;              
;              ;; The target of the Assoc needs all the keys not explicitly Assoc'ed.
;              expected-target-hmap 
;              (let [types (select-keys (into {} entries)
;                                       (set/difference (set Assoc-keys) (set Tkeys)))]
;                (if (c/complete-hmap? T) 
;                  (c/-complete-hmap types)
;                  (c/-partial-hmap types absent-keys)))
;              
;              ;_ (prn assoc-args-hmap :< expected-assoc-args-hmap)
;              ;_ (prn (:target S) :< expected-target-hmap)
;              ]
;          (cs-gen-list V X Y
;                       [assoc-args-hmap 
;                        (:target S)]
;                       [expected-assoc-args-hmap
;                        expected-target-hmap]))
;
;        (and (r/AssocType? S)
;             (r/HeterogeneousVector? T))
;        (assert nil "TODO AssocType HVec")
;#_
;        (let [elem-type (apply c/Un
;                               (concat
;                                 (:types T)
;                                 (when-let [rest (:rest T)]
;                                   [rest])
;                                 (when (:drest T)
;                                   [r/-any])))
;              vec-any (r/-hvec [] :rest r/-any)
;              num-type (c/RClass-of 'java.lang.Number)
;              target-cset (cs-gen V X Y (:target S) vec-any)
;              entries-key (map first (:entries S))
;              entries-val (map second (:entries S))
;              key-cset (cs-gen-list V X Y entries-key (repeat (count entries-key)
;                                                              num-type))
;              ;_ (println "key-cset" key-cset)
;              val-cset (cs-gen-list V X Y entries-val (repeat (count entries-val)
;                                                              elem-type))
;              ;_ (println "val-cset" val-cset)
;              dentries-cset (when-let [{dty :pre-type dbound :name} (:dentries S)]
;                              (when (and dbound (not (Y dbound)))
;                                (fail! S T))
;                              ;(println "passed when")
;                              (let [merged-X (merge X {dbound (Y dbound)})
;                                    get-list-of-c (fn get-list-of-c [t-list]
;                                                    (mapv #(get-c-from-cmap % dbound)
;                                                          (t/for [t :- r/Type, t-list]
;                                                            :- cset
;                                                            (cs-gen V merged-X Y dty t))))
;                                    repeat-c (get-list-of-c [num-type elem-type])]
;                                (assoc-in (cr/empty-cset X Y)
;                                          [:maps 0 :dmap :map dbound]
;                                          ; don't constrain on fixed, otherwise will fail
;                                          ; on (assoc m x y)
;                                          (cr/dcon-repeat-maker [] repeat-c))))
;              ]
;          (cset-meet* (concat [target-cset key-cset val-cset]
;                              (when dentries-cset [dentries-cset]))))
;
;        (and (r/PrimitiveArray? S)
;             (r/PrimitiveArray? T)
;             (impl/checking-clojure?))
;        (norm* 
;          ;input contravariant
;          ;output covariant
;          [(:input-type T) (:output-type S)]
;          [(:input-type S) (:output-type T)])
;
;        ; some RClass's have heterogeneous vector ancestors (in "unchecked ancestors")
;        ; It's useful to also trigger this case with HSequential, as that's more likely
;        ; to be on the right.
;        (and (r/RClass? S)
;             ((some-fn r/HeterogeneousVector? r/HSequential?) T))
;        (if-let [[Sv] (seq
;                        (filter (some-fn r/HeterogeneousVector? r/HSequential?)
;                                (map c/fully-resolve-type (c/RClass-supers* S))))]
;          (norm2 Sv T)
;          fail-css)
;        
;        (and (r/TApp? S)
;             (r/TApp? T))
;        (cs-gen-TApp no-mention S T M)
;
;        (and (r/FnIntersection? S)
;             (r/FnIntersection? T))
;        (cs-gen-FnIntersection no-mention S T M)
;
;        (and (r/Function? S)
;             (r/Function? T))
;        (cs-gen-Function no-mention S T M)
;
;        (and (r/Result? S)
;             (r/Result? T))
;        (cs-gen-Result no-mention S T M)
;
;        (and (r/Value? S)
;             (r/AnyValue? T))
;        fail-css
;
;; must remember to update these if HeterogeneousList gets rest/drest
;        (and (r/HeterogeneousSeq? S)
;             (r/RClass? T))
;        (norm2 (let [ss (apply c/Un
;                               (concat
;                                 (:types S)
;                                 (when-let [rest (:rest S)]
;                                   [rest])
;                                 (when (:drest S)
;                                   [r/-any])))]
;                 (c/In (impl/impl-case
;                         :clojure (c/RClass-of clojure.lang.ISeq [ss])
;                         :cljs (c/Protocol-of 'cljs.core/ISeq [ss]))
;                       ((if (or (:rest S) (:drest S)) r/make-CountRange r/make-ExactCountRange)
;                        (count (:types S)))))
;               T)
;
;; must remember to update these if HeterogeneousList gets rest/drest
;        (and (r/HeterogeneousList? S)
;             (r/RClass? T))
;        (norm2 (c/In (impl/impl-case
;                       :clojure (c/RClass-of clojure.lang.IPersistentList [(apply c/Un (:types S))])
;                       :cljs (c/Protocol-of 'cljs.core/IList [(apply c/Un (:types S))]))
;                     (r/make-ExactCountRange (count (:types S))))
;               T)
;
;        ; TODO add :repeat support
;        (and (r/HSequential? S)
;             (r/RClass? T))
;        (norm2 (let [ss (apply c/Un
;                               (concat
;                                 (:types S)
;                                 (when-let [rest (:rest S)]
;                                   [rest])
;                                 (when (:drest S)
;                                   [r/-any])))]
;                 (c/In (impl/impl-case
;                         :clojure (c/In (c/RClass-of clojure.lang.IPersistentCollection [ss])
;                                        (c/RClass-of clojure.lang.Sequential))
;                         :cljs (throw (Exception. "TODO CLJS HSequential cs-gen")))
;                       ((if (or (:rest S) (:drest S)) r/make-CountRange r/make-ExactCountRange)
;                        (count (:types S)))))
;               T)
;
;        ; TODO add :repeat support
;        (and (r/HeterogeneousVector? S)
;             (r/RClass? T))
;        (norm2 (let [ss (apply c/Un 
;                               (concat
;                                 (:types S)
;                                 (when-let [rest (:rest S)]
;                                   [rest])
;                                 (when (:drest S)
;                                   [r/-any])))]
;                 (c/In (impl/impl-case
;                         :clojure (c/RClass-of clojure.lang.APersistentVector [ss])
;                         :cljs (c/Protocol-of 'cljs.core/IVector [ss]))
;                       ((if (or (:rest S) (:drest S)) r/make-CountRange r/make-ExactCountRange)
;                        (count (:types S)))))
;               T)
;
        (and (r/RClass? S)
             (r/RClass? T))
        (upcast-RClass S T)

;        (and (r/Protocol? S)
;             (r/Protocol? T))
;        (cs-gen-Protocol no-mention S T M)
;
;        (r/HeterogeneousMap? S)
;        (let [new-S (c/upcast-hmap S)]
;          (norm2 new-S T))
;
;        (r/HSet? S)
;        (let [new-S (c/upcast-hset S)]
;          (norm2 new-S T))
;
;        (r/HeterogeneousVector? S)
;        (norm2 (c/upcast-hvec S) T)
;
;        (and (r/AssocType? S)
;             (r/Protocol? T))
;        (norm2 (:target S) T)
;
;        :else fail-css
)))

(defn cs-gen [no-mention S T M]
  {:pre [(r/Type? S)
         (r/Type? T)
         (not (r/F? S))
         (not (r/F? T))]
   :post [(constraint-set-set? %)]}
  (prn "cs-gen" S T)
  (if (or (contains? M (c/In S (c/-not T)))
          (sub/subtype? S T))
    ;already been around this loop, is a subtype
    success-css
    (let [M (conj M (c/In S (c/-not T)))
          norm2 #(norm2 no-mention %1 %2 M)
          norm* (fn [Ss Ts]
                  (cnorm no-mention Ss Ts M))
          cg #(cs-gen no-mention %1 %2 M)]
      (cond
        (r/Top? T)
        success-css

        (r/Bottom? T)
        fail-css

        ((some-fn r/Union? r/Intersection?) S T)
        (err/int-error "Shouldn't pass Union/Intersection to cs-gen")
        
        ;values are subtypes of their classes
        (r/Value? S)
        (impl/impl-case
          :clojure (if (nil? (:val S))
                     fail-css
                     (norm2 (apply c/In (c/RClass-of (class (:val S)))
                                   (cond 
                                     ;keyword values are functions
                                     (keyword? (:val S)) [(c/keyword->Fn (:val S))]
                                     ;strings have a known length as a seqable
                                     (string? (:val S)) [(r/make-ExactCountRange (count (:val S)))]))
                            T))
          :cljs (cond
                  (integer? (:val S)) (norm2 (r/IntegerCLJS-maker) T)
                  (number? (:val S)) (norm2 (r/NumberCLJS-maker) T)
                  (string? (:val S)) (norm2 (r/StringCLJS-maker) T)
                  (con/boolean? (:val S)) (norm2 (r/BooleanCLJS-maker) T)
                  (symbol? (:val S)) (norm2 (c/DataType-of 'cljs.core/Symbol) T)
                  (keyword? (:val S)) (norm2 (c/DataType-of 'cljs.core/Keyword) T)
                  :else (constraint-set-set)))

        ;; constrain body to be below T
        (r/Poly? S)
        (let [nms (c/Poly-fresh-symbols* S)
              body (c/Poly-body* nms S)
              bbnds (c/Poly-bbnds* nms S)]
          (prn "Poly?" body T)
          (free-ops/with-bounded-frees (zipmap (map r/F-maker nms) bbnds)
            (norm2 body T)))

        (r/Name? S)
        (norm2 (c/resolve-Name S) T)

        (r/Name? T)
        (norm2 S (c/resolve-Name T))

        ; copied from TR's infer-unit
        ;; if we have two mu's, we rename them to have the same variable
        ;; and then compare the bodies
        ;; This relies on (B 0) only unifying with itself, and thus only hitting the first case of this `match'
        (and (r/Mu? S)
             (r/Mu? T))
        (norm2 (r/Mu-body-unsafe S) (r/Mu-body-unsafe T))

        ;; other mu's just get unfolded
        (r/Mu? S) (norm2 (c/unfold S) T)
        (r/Mu? T) (norm2 S (c/unfold T))

        (and (r/TApp? S)
             (not (r/F? (:rator S))))
        (norm2 (c/resolve-TApp S) T)

        (and (r/TApp? T)
             (not (r/F? (:rator T))))
        (norm2 S (c/resolve-TApp T))

        (and (r/Extends? S)
             (r/Extends? T))
        (norm2 (apply c/In (:extends S) (mapv r/NotType? (:without S)))
               (apply c/In (:extends T) (mapv r/NotType? (:without T))))

        (r/Extends? S)
        (norm2 (apply c/In (:extends S) (mapv r/NotType? (:without S)))
               T)

        (r/Extends? T)
        (norm2 S
               (apply c/In (:extends T) (mapv r/NotType? (:without T))))


        (r/App? S)
        (norm2 (c/resolve-App S) T)

        (r/App? T)
        (norm2 S (c/resolve-App T))

        (and (r/DataType? S)
             (r/DataType? T)) (cs-gen-datatypes-or-records no-mention S T M)

        ; handle Record as HMap
        (r/Record? S) (norm2 (c/Record->HMap S) T)

        (and (r/HeterogeneousVector? S)
             (r/HeterogeneousVector? T))
        (cs-gen-HSequential no-mention (c/HVec->HSequential S) (c/HVec->HSequential T) M)

        (and (r/HeterogeneousSeq? S)
             (r/HeterogeneousSeq? T))
        (cs-gen-HSequential no-mention (c/HSeq->HSequential S) (c/HSeq->HSequential T) M)

        (and (r/HeterogeneousList? S)
             (r/HeterogeneousList? T))
        (cs-gen-HSequential no-mention (c/HList->HSequential S) (c/HList->HSequential T) M)

        ; HList/HSeq/HVector are HSequential
        (and ((some-fn r/HeterogeneousList?
                       r/HeterogeneousSeq?
                       r/HeterogeneousVector?)
              S)
             (r/HSequential? T))
        (norm (cond
                (r/HeterogeneousList? S) (c/HList->HSequential S) 
                (r/HeterogeneousVector? S) (c/HVec->HSequential S) 
                :else (c/HSeq->HSequential S))
              T)

        ; HList is a HSeq
        (and (r/HeterogeneousList? S)
             (r/HeterogeneousSeq? T))
        (cs-gen-HSequential no-mention (c/HList->HSequential S) (c/HSeq->HSequential T) M)

        (and (r/HSequential? S)
             (r/HSequential? T))
        (cs-gen-HSequential no-mention S T M)

        (and (r/HeterogeneousMap? S)
             (r/HeterogeneousMap? T))
        ; assumes optional/mandatory/absent keys are disjoint
        (let [Skeys (set (keys (:types S)))
              Tkeys (set (keys (:types T)))
              Soptk (set (keys (:optional S)))
              Toptk (set (keys (:optional T)))
              Sabsk (:absent-keys S)
              Tabsk (:absent-keys T)]
          (cond
            ; All keys must be values
            (not (every? r/Value? 
                         (concat
                           Skeys Tkeys
                           Soptk Toptk
                           Sabsk Tabsk)))
            fail-css

            ; If the right is complete, the left must also be complete
            (and (c/complete-hmap? T)
                 (not (c/complete-hmap? S)))
            fail-css

            ; check mandatory keys
            (if (c/complete-hmap? T)
              ; If right is complete, mandatory keys must be identical
              (= Tkeys Skeys)
              ; If right is partial, all mandatory keys on the right must also appear mandatory on the left
              (seq (set/difference Tkeys Skeys)))
            fail-css

            ; All optional keys on the right must appear either absent, mandatory or optional
            ; on the left
            (seq (set/difference Toptk 
                                 (set/union Skeys 
                                            Soptk 
                                            Sabsk)))
            fail-css

            ; All absent keys on the right must appear absent on the left
            (seq (set/difference Tabsk Sabsk))
            fail-css

            :else
            ; now check the values with cs-gen
            (let [;only check mandatory entries that appear on the right
                  check-mandatory-keys Tkeys
                  Svals (map (:types S) check-mandatory-keys)
                  Tvals (map (:types T) check-mandatory-keys)
                  _ (assert (every? r/Type? Svals))
                  _ (assert (every? r/Type? Tvals))
                  ;only check optional entries that appear on the right
                  ; and also appear as mandatory or optional on the left
                  check-optional-keys (set/intersection
                                        Toptk (set/union Skeys Soptk))
                  Sopts (map (some-fn (:types S) (:optional S)) check-optional-keys)
                  Topts (map (:optional T) check-optional-keys)
                  _ (assert (every? r/Type? Sopts))
                  _ (assert (every? r/Type? Topts))]
              (intersect-css (norm* Svals Tvals)
                             (norm* Sopts Topts)))))

        (and (r/GetType? S)
             (not (r/F? (:target S))))
        (norm2 (c/-resolve S) T)

        (and (r/GetType? T)
             (not (r/F? (:target T))))
        (norm2 S (c/-resolve T))

        (and (r/AssocType? S)
             (r/AssocType? T))
        (let [{S-target :target S-entries :entries S-dentries :dentries} S
              {T-target :target T-entries :entries T-dentries :dentries} T
              target-cset (cg S-target T-target)
              S-entries (reduce concat S-entries)
              T-entries (reduce concat T-entries)
              entries-cset (norm* S-entries T-entries)
              _ (when (and S-dentries T-dentries)
                  (err/nyi-error "NYI dentries of Assoc in cs-gen"))
              ]
          (intersect-css target-cset entries-cset))

        (and (r/AssocType? S)
             (r/RClass? T)
             ; (Map xx yy)
             (= 'clojure.lang.IPersistentMap (:the-class T)))
        (assert nil "TODO AssocType RClass")
#_
        (let [{:keys [target entries dentries]} S
              {:keys [poly? the-class]} T
              dentries-cset (when-let [{dty :pre-type dbound :name} dentries]
                              (when (and dbound (not (Y dbound)))
                                (fail! S T))
                              ;(println "passed when")
                              (let [merged-X (merge X {dbound (Y dbound)})
                                    get-list-of-c (fn get-list-of-c [t-list]
                                                    (mapv #(get-c-from-cmap % dbound)
                                                          (t/for [t :- r/Type, t-list]
                                                                :- cset
                                                                (cs-gen V merged-X Y dty t))))
                                    repeat-c (get-list-of-c poly?)]
                                (assoc-in (cr/empty-cset X Y)
                                          [:maps 0 :dmap :map dbound]
                                          ; don't constrain on fixed, otherwise will fail
                                          ; on (assoc m x y)
                                          (cr/dcon-repeat-maker [] repeat-c))))
              ;_ (println "dentries-cset" dentries-cset)

              ; if it's nil, we also accept it
              map-cset (when-not (r/Nil? target)
                         (cs-gen V X Y target T))
              entries-keys (map first entries)
              entries-vals (map second entries)
              cg #(cs-gen V X Y %1 %2)
              key-cset (map cg entries-keys (repeat (first poly?)))
              val-cset (map cg entries-vals (repeat (second poly?)))]
          (cset-meet* (concat (when map-cset [map-cset]) key-cset val-cset)))

        ; transform Record to HMap, this is not so useful until we can do
        ; cs-gen Assoc with dentries with HMap
        (and (r/AssocType? S)
             (r/Record? T))
        (let [{:keys [target]} S
              target-cset (norm2 target T)
              cset (norm2 S (c/Record->HMap T))]
          (intersect-css target cset))

; Completeness matters:
;
; (Assoc x ':a Number ':b Long) <: (HMap {:a Number :b Long} :complete? true)
; (Assoc x ':a Number ':b Long ':c Foo) <!: (HMap {:a Number :b Long} :complete? true)
        (and (r/AssocType? S)
             (r/HeterogeneousMap? T))
        (assert nil "TODO AssocType HeterogeneousMap")
#_
        (let [;_ (prn "cs-gen Assoc HMap")
              {:keys [target entries dentries]} S
              {:keys [types absent-keys]} T
              _ (when-not (nil? dentries) (err/nyi-error (pr-str "NYI cs-gen of dentries AssocType with HMap " S T)))
              Assoc-keys (map first entries)
              Tkeys (keys types)
              ; All keys must be keyword values
              _ (when-not (every? c/keyword-value? (concat Tkeys Assoc-keys absent-keys))
                  (fail! S T))
              ; All keys explicitly not in T should not appear in the Assoc operation
              absents-satisfied?
              (if (c/complete-hmap? T)
                ; if T is partial, we just need to ensure the absent keys in T
                ; don't appear in the entries of the Assoc.
                (empty?
                  (set/intersection
                    (set absent-keys)
                    (set (map first entries))))
                ; if T is complete, all entries of the Assoc should *only* have
                ; keys that are mandatory keys of T.
                (empty?
                  (set/difference
                    (set (map first entries))
                    (set Tkeys))))
              _ (when-not absents-satisfied?
                  (fail! S T))
              ;; Isolate the entries of Assoc in a new HMap, with a corresponding expected HMap.
              ; keys on the right overwrite those on the left.
              assoc-args-hmap (c/make-HMap :mandatory (into {} entries))
              expected-assoc-args-hmap (c/make-HMap :mandatory (select-keys (:types assoc-args-hmap) (set Assoc-keys)))
              
              ;; The target of the Assoc needs all the keys not explicitly Assoc'ed.
              expected-target-hmap 
              (let [types (select-keys (into {} entries)
                                       (set/difference (set Assoc-keys) (set Tkeys)))]
                (if (c/complete-hmap? T) 
                  (c/-complete-hmap types)
                  (c/-partial-hmap types absent-keys)))
              
              ;_ (prn assoc-args-hmap :< expected-assoc-args-hmap)
              ;_ (prn (:target S) :< expected-target-hmap)
              ]
          (cs-gen-list V X Y
                       [assoc-args-hmap 
                        (:target S)]
                       [expected-assoc-args-hmap
                        expected-target-hmap]))

        (and (r/AssocType? S)
             (r/HeterogeneousVector? T))
        (assert nil "TODO AssocType HVec")
#_
        (let [elem-type (apply c/Un
                               (concat
                                 (:types T)
                                 (when-let [rest (:rest T)]
                                   [rest])
                                 (when (:drest T)
                                   [r/-any])))
              vec-any (r/-hvec [] :rest r/-any)
              num-type (c/RClass-of 'java.lang.Number)
              target-cset (cs-gen V X Y (:target S) vec-any)
              entries-key (map first (:entries S))
              entries-val (map second (:entries S))
              key-cset (cs-gen-list V X Y entries-key (repeat (count entries-key)
                                                              num-type))
              ;_ (println "key-cset" key-cset)
              val-cset (cs-gen-list V X Y entries-val (repeat (count entries-val)
                                                              elem-type))
              ;_ (println "val-cset" val-cset)
              dentries-cset (when-let [{dty :pre-type dbound :name} (:dentries S)]
                              (when (and dbound (not (Y dbound)))
                                (fail! S T))
                              ;(println "passed when")
                              (let [merged-X (merge X {dbound (Y dbound)})
                                    get-list-of-c (fn get-list-of-c [t-list]
                                                    (mapv #(get-c-from-cmap % dbound)
                                                          (t/for [t :- r/Type, t-list]
                                                            :- cset
                                                            (cs-gen V merged-X Y dty t))))
                                    repeat-c (get-list-of-c [num-type elem-type])]
                                (assoc-in (cr/empty-cset X Y)
                                          [:maps 0 :dmap :map dbound]
                                          ; don't constrain on fixed, otherwise will fail
                                          ; on (assoc m x y)
                                          (cr/dcon-repeat-maker [] repeat-c))))
              ]
          (cset-meet* (concat [target-cset key-cset val-cset]
                              (when dentries-cset [dentries-cset]))))

        (and (r/PrimitiveArray? S)
             (r/PrimitiveArray? T)
             (impl/checking-clojure?))
        (norm* 
          ;input contravariant
          ;output covariant
          [(:input-type T) (:output-type S)]
          [(:input-type S) (:output-type T)])

        ; some RClass's have heterogeneous vector ancestors (in "unchecked ancestors")
        ; It's useful to also trigger this case with HSequential, as that's more likely
        ; to be on the right.
        (and (r/RClass? S)
             ((some-fn r/HeterogeneousVector? r/HSequential?) T))
        (if-let [[Sv] (seq
                        (filter (some-fn r/HeterogeneousVector? r/HSequential?)
                                (map c/fully-resolve-type (c/RClass-supers* S))))]
          (norm2 Sv T)
          fail-css)
        
        (and (r/TApp? S)
             (r/TApp? T))
        (cs-gen-TApp no-mention S T M)

        (and (r/FnIntersection? S)
             (r/FnIntersection? T))
        (cs-gen-FnIntersection no-mention S T M)

        (and (r/Function? S)
             (r/Function? T))
        (cs-gen-Function no-mention S T M)

        (and (r/Result? S)
             (r/Result? T))
        (cs-gen-Result no-mention S T M)

        (and (r/Value? S)
             (r/AnyValue? T))
        fail-css

; must remember to update these if HeterogeneousList gets rest/drest
        (and (r/HeterogeneousSeq? S)
             (r/RClass? T))
        (norm2 (let [ss (apply c/Un
                               (concat
                                 (:types S)
                                 (when-let [rest (:rest S)]
                                   [rest])
                                 (when (:drest S)
                                   [r/-any])))]
                 (c/In (impl/impl-case
                         :clojure (c/RClass-of clojure.lang.ISeq [ss])
                         :cljs (c/Protocol-of 'cljs.core/ISeq [ss]))
                       ((if (or (:rest S) (:drest S)) r/make-CountRange r/make-ExactCountRange)
                        (count (:types S)))))
               T)

; must remember to update these if HeterogeneousList gets rest/drest
        (and (r/HeterogeneousList? S)
             (r/RClass? T))
        (norm2 (c/In (impl/impl-case
                       :clojure (c/RClass-of clojure.lang.IPersistentList [(apply c/Un (:types S))])
                       :cljs (c/Protocol-of 'cljs.core/IList [(apply c/Un (:types S))]))
                     (r/make-ExactCountRange (count (:types S))))
               T)

        ; TODO add :repeat support
        (and (r/HSequential? S)
             (r/RClass? T))
        (norm2 (let [ss (apply c/Un
                               (concat
                                 (:types S)
                                 (when-let [rest (:rest S)]
                                   [rest])
                                 (when (:drest S)
                                   [r/-any])))]
                 (c/In (impl/impl-case
                         :clojure (c/In (c/RClass-of clojure.lang.IPersistentCollection [ss])
                                        (c/RClass-of clojure.lang.Sequential))
                         :cljs (throw (Exception. "TODO CLJS HSequential cs-gen")))
                       ((if (or (:rest S) (:drest S)) r/make-CountRange r/make-ExactCountRange)
                        (count (:types S)))))
               T)

        ; TODO add :repeat support
        (and (r/HeterogeneousVector? S)
             (r/RClass? T))
        (norm2 (let [ss (apply c/Un 
                               (concat
                                 (:types S)
                                 (when-let [rest (:rest S)]
                                   [rest])
                                 (when (:drest S)
                                   [r/-any])))]
                 (c/In (impl/impl-case
                         :clojure (c/RClass-of clojure.lang.APersistentVector [ss])
                         :cljs (c/Protocol-of 'cljs.core/IVector [ss]))
                       ((if (or (:rest S) (:drest S)) r/make-CountRange r/make-ExactCountRange)
                        (count (:types S)))))
               T)

        (and (r/RClass? S)
             (r/RClass? T))
        (norm-RClass no-mention S T M)

        (and (r/Protocol? S)
             (r/Protocol? T))
        (cs-gen-Protocol no-mention S T M)

        (r/HeterogeneousMap? S)
        (let [new-S (c/upcast-hmap S)]
          (norm2 new-S T))

        (r/HSet? S)
        (let [new-S (c/upcast-hset S)]
          (norm2 new-S T))

        (r/HeterogeneousVector? S)
        (norm2 (c/upcast-hvec S) T)

        (and (r/AssocType? S)
             (r/Protocol? T))
        (norm2 (:target S) T)

        :else fail-css))))

;; returns a set of all the ways the set s
;; can be divided into n parts.
(defn all-splits [s n]
  (let []
    (assert nil "TODO")))

(defn cs-gen-many-RClasses [no-mention P N M]
  {:pre [(set? no-mention)
         (every? r/Type? P)
         (every? r/RClass? N)
         (set? M)]
   :post [(constraint-set-set? %)]}
  (let [;;FIXME must add the type representing P ^ ~N to M
        norm #(norm no-mention % M)
        Ngroups (group-by :the-class N)
        Ncss (mapv (fn [relevant-Ns]
                     {:pre [(every? r/RClass? relevant-Ns)
                            (vector? relevant-Ns)
                            (seq relevant-Ns)]}
                     ;; follow rule for pairs. Find a 
                     (let [N-combs (map set (comb/subsets relevant-Ns))
                           N (set relevant-Ns)
                           N-css 
                           (mapv
                             (fn [N']
                               {:pre [(every? r/RClass? N')]}
                               (let [relevant-Ps (keep #(upcast-to-RClass % (first relevant-Ns)) P)
                                     _ (assert (every? r/RClass? relevant-Ps) relevant-Ps)
                                     variances (:variances (first relevant-Ns))
                                     css (mapv (fn [i]
                                                 (let [ith-poly (comp #(nth % i) :poly?)
                                                       norms2 #(norm (apply c/In (concat %1 (map c/-not %2))))
                                                       pp (map ith-poly relevant-Ps)
                                                       nn (map ith-poly relevant-Ns)
                                                       c (case (nth variances i)
                                                           (:covariant :constant)
                                                           (norms2 pp nn)
                                                           :contravariant
                                                           (norms2 nn pp)
                                                           :invariant
                                                           (intersect-css
                                                             (norms2 pp nn)
                                                             (norms2 nn pp)))]
                                                   c))
                                               (range (:variances (first relevant-Ns))))]
                                 (apply intersect-css css)))
                             N-combs)
                           ]
                       ))
                     (vals Ngroups))]
    (assert nil "TODO use all-splits instead of comb")))

;; upcast the P's to be functions, then generate constraints
;; that make (^ P) <: (v N)
(defn cs-gen-many-functions [no-mention P N M]
  {:pre [(set? no-mention)
         (every? r/Type? P)
         (every? r/Function? N)
         (set? M)]
   :post [(constraint-set-set? %)]}
  (let [up-P (vec (keep upcast-to-Function P))
        _ (assert (every? r/Function? up-P) up-P)
        P's (map set (comb/subsets (vec P)))
        P (set P)
        Ncss (mapv (fn [n]
                     {:pre [(r/Function? n)]}
                     (apply intersect-css
                       (mapv (fn [P']
                               {:pre [(every? r/Function? P')]}
                               (cond
                                 (not-any? (some-fn :rest :drest :kws :prest :pdot) (concat P' [n]))
                                 (let [relevant-P' (filter (fn [a]
                                                             (= (count (:dom a))
                                                                (count (:dom n))))
                                                           P')
                                       ;; constraints for arguments
                                       Sargs_P' (apply intersect-css
                                                       (map (fn [p]
                                                              {:pre [(integer? p)]}
                                                              (let [pth-dom #(nth (:dom %) p)
                                                                    t1j (pth-dom n)
                                                                    t1is (map (comp c/-not pth-dom) relevant-P')]
                                                                (norm no-mention (apply c/In t1j t1is) M)))
                                                            (range (count (:dom n)))))
                                       P-without-P' (set/difference P P')
                                       ;; constraints for range
                                       Srng_P' (if (= P P-without-P')
                                                 fail-css
                                                 ;; TODO filters objects!
                                                 (let [rng-t (comp :t :rng)]
                                                   (norm no-mention
                                                         (apply c/In (c/-not (rng-t n))
                                                                (map rng-t P-without-P'))
                                                         M)))]
                                   (union-css Sargs_P' Srng_P'))))
                             P's)))
                   N)]
    (apply union-css Ncss)))

;; returns a constraint set that satisfies (I ts ...) <: (U)
(defn cs-gen-normalized-no-tvar [no-mention ts M]
  {:pre [(set? no-mention)
         (every? symbol? no-mention)
         (every? r/Type? ts)
         (set? M)
         (every? r/Type? M)]
   :post [(constraint-set-set? %)]}
  ;(prn "cs-gen-normalized-no-tvar" ts)
  (let [pred (fn [t]
               (let [t (if (r/NotType? t)
                         (:type t)
                         t)]
                 (and (r/Type? t)
                      (not (r/NotType? t))
                      (or (r/Bottom? t)
                          (not (r/Union? t)))
                      (not (r/F? t))
                      (not (r/Intersection? t)))))]
    (assert (every? pred ts) (vec (remove pred ts))))
  (let [ts (mapv fully-resolve-under-Not ts)
        {N true P false} (group-by-boolean r/NotType? ts)
        _ (assert (every? (every-pred r/Type? (complement r/NotType?)) P))
        N (or (seq (map :type N))
              ;; since (Not Nothing) in N would be converted to Any,
              ;; which is then lost in the intersection being passed
              ;; to this function, we assume N = {Nothing} if no negations
              ;; are present.
              #_[r/-nothing])
        _ (assert (every? r/Type? N))
        {:keys [::N-functions ::N-others ::N-RClasses]}
        (group-by (fn [t]
                    {:post [(keyword? %)]}
                    (cond
                      (r/Function? t) ::N-functions
                      (r/RClass? t) ::N-RClasses
                      :else ::N-others))
                  N)
        _ (assert (empty? N-others) (mapv class N-others))
        css-functions (if (seq N-functions)
                        (cs-gen-many-functions no-mention P N-functions M)
                        fail-css)
        css-RClasses (if (seq N-RClasses)
                        (cs-gen-many-RClasses no-mention P N-functions M)
                        fail-css)
        css (union-css css-functions
                       css-RClasses)
        ]
    css
    ))

(defn csmerge [no-mention cs M]
  {:pre [(constraint-set? cs)
         (set? M)]
   :post [(constraint-set-set? %)]}
  (let [;; check, for each constraint S <: a <: T,
        ;;  that S <: T
        not-in-M (first
                   (remove
                     (fn [{:keys [S T] :as c}]
                       {:pre [(constraint? c)]}
                       (prn "merge check M" M (c/In S (c/-not T)))
                       (contains? M (c/In S (c/-not T))))
                     (concat (sort-by :X (vals (:fixed cs)))
                             (reduce (fn [r dcon]
                                       (cond
                                         (cr/dcon? dcon) 
                                         (into r
                                               (concat (:fixed dcon)
                                                       (when (:rest dcon)
                                                         [(:rest dcon)])))
                                         :else (throw (Exception.
                                                        (str "What is this? " (pr-str (class dcon)))))))
                                     [] (-> cs :dmap :map vals)))))
        ;; if there exists a contract such that S <: T, but S ^ ~T is not in M,
        ;; then recur.
        css
        (if-let [{:keys [S X T]} not-in-M]
          (let [_ (prn "merge" X)
                _ (assert (constraint? not-in-M))
                t (c/In S (c/-not T))
                l (intersect-css
                    (constraint-set-set cs)
                    (norm no-mention t #{}))]
            (apply union-css
                   (map (fn [C']
                          {:pre [(constraint-set? C')]
                           :post [(constraint-set-set? %)]}
                          (csmerge no-mention C' (conj M t)))
                        (:maps l))))
          (constraint-set-set cs))]
    css))

(defn cssmerge [no-mention css]
  {:pre [(set? no-mention)
         (constraint-set-set? css)]
   :post [(constraint-set-set? %)]}
  (prn "cssmerge")
  (ppcss css)
  (apply union-css
         (reduce (fn [css cs]
                   {:pre [(every? constraint-set-set? css)
                          (constraint-set? cs)]
                    :post [(every? constraint-set-set? %)]}
                   (conj css (csmerge no-mention cs #{})))
                 []
                 (:maps css))))

(defn cnorm 
  "Normalize types Ss <: Ts, pairwise."
  [no-mention Ss Ts M]
  {:pre [(set? no-mention)
         (every? symbol? no-mention)
         (every? r/Type? Ss)
         (every? r/Type? Ts)
         (= (count Ss) (count Ts))]
   :post [(constraint-set-set? %)]}
  (apply intersect-css
         (map (fn [s t]
                (norm2 no-mention s t M))
              Ss Ts)))

(defn substitution? [m]
  (cr/substitution-c? m))

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
        (map (fn [{:keys [S X T]}]
               [X (cr/t-subst-maker
                    (c/In (c/Un S (r/make-F (placeholder-tvar-name)))
                          T)
                    nil)]))
        (vals (:fixed cs))))

(declare unify)

(defn csssolve [css]
  {:pre [(constraint-set-set? css)]
   :post [(every? substitution? %)]}
  (mapv solve (:maps css)))

(defn subst-in-subst [subst target]
  {:pre [(substitution? subst)
         (cr/subst-rhs? target)]
   :post [(cr/subst-rhs? %)]}
  (let [f #(subst/subst-all subst %)]
    (cond
      (cr/t-subst? target) (do
                             (prn "subst-in-subst" (read-string (with-out-str (ppsubst subst))) (:type target))
                             (cr/t-subst-maker
                               (f (:type target))
                               nil))
      (cr/i-subst? target) (cr/i-subst-maker
                             (mapv f (:types target)))
      (cr/i-subst-starred? target) (cr/i-subst-starred-maker
                                     (mapv f (:types target))
                                     (f (:starred target)))
      (cr/i-subst-dotted? target) (cr/i-subst-dotted-maker
                                    (mapv f (:types target))
                                    (f (:dty target))
                                    (f (:dbound target)))
      :else (throw (Exception. (str "What is this? " (class target)))))))

(defn unify [E]
  {:pre [(substitution? E)]
   :post [(substitution? %)]}
  (prn "unify top")
  (prn (ppsubst E))
  (if (empty? E)
    {}
    (let [;; select smallest variable
          a (first (sort (keys E)))
          _ (prn "unify var" a)
          t_a (get E a)
          rec_a (cond
                  (cr/t-subst? t_a) (cr/t-subst-maker (maybe-Mu* a (:type t_a))
                                                      nil)
                  :else (throw (Exception. (str "What is this? " (pr-str (class t_a))))))
          _ (assert (cr/subst-rhs? rec_a))
          E' (into {}
                   (map (fn [[k v]]
                          {:pre [(cr/subst-rhs? v)]}
                          [k (subst-in-subst {a rec_a} v)]))
                   ; adding this sort-by seems to make inference more deterministic?
                   (sort-by first (dissoc E a)))
          _ (assert (substitution? E'))
          sigma (unify E')]
      (merge {a (subst-in-subst E' rec_a)}
             sigma))))

(declare unify-all ppsubst)

(defn css-potential-solution? [css]
  {:pre [(constraint-set-set? css)]}
  (boolean (seq (:maps css))))

(defn infer-substs [no-mentions Ss Tt]
  (prn "infer-substs" no-mentions Ss Tt)
  (let [css (cnorm no-mentions Ss Tt #{})
        _ (prn "after norm" (count (:maps css)))
        _ (ppcss css)]
    (if-not (css-potential-solution? css)
      (do (prn "Fail after norm")
          nil)
      (let [css (cssmerge no-mentions css)
            _ (prn "after merge" (count (:maps css)))
            _ (ppcss css)]
        (if-not (css-potential-solution? css)
          (do (prn "Fail after merge")
              nil)
          (let [substs (csssolve css)
                _ (run! ppsubst substs)
                substs (unify-all substs)]
            (prn "final subst: " (count substs)) 
            ;(run! ppsubst substs)
            substs))))))

(defn ppinfer-substs [no-mention Ss Tt]
  (let [substs (infer-substs no-mention Ss Tt)]
    (run! ppsubst substs)
    substs))

(defn clean-placeholders [s]
  {:pre [(substitution? s)]
   :post [(substitution? %)]}
  (into {}
        (map (fn [[k v]]
               {:pre [(cr/subst-rhs? v)]}
               [k (cond
                    (cr/t-subst? v)
                    (let [t (:type v)
                          fvs (filter key (frees/fv-variances t))]
                      (cr/t-subst-maker
                        (reduce (fn [t [pl variance]]
                                  {:pre [(r/variance? variance)]}
                                  (case variance
                                    :invariant t
                                    (subst/subst-all
                                      (c/make-simple-substitution
                                        [pl]
                                        [(case variance
                                           :covariant r/-nothing
                                           :contravariant r/-any)])
                                      t)))
                                t fvs)
                        nil))
                    :else (throw (Exception. (str "What is this? " (class v)))))]))
        s))

(defn unify-all [substs]
  {:pre [(every? substitution? substs)]
   :post [(every? substitution? %)]}
  (mapv (comp clean-placeholders unify) substs))

(defn ppcss [css]
  {:pre [(constraint-set-set? css)]}
  (pprint
    (read-string
      (pr-str
        (mapv (fn [cs]
                {:pre [(constraint-set? cs)]}
                (map 
                  (fn [{:keys [S X T] :as c}]
                    {:pre [(constraint? c)]}
                    [S :< X :< T])
                  (sort-by :X (-> cs :fixed vals))))
              (:maps css))))))

(defn ppcss-str [css]
  (with-out-str (ppcss css)))

(defn ppsubst [subst]
  (pprint
    (read-string
      (pr-str
        (into {}
              (map (fn [[k v]]
                     [k (cond
                          (cr/t-subst? v) (:type v)
                          :else (throw (Exception. "What is this? " (class v))))]))
             subst)))))

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
          t (c/In left (c/-not right))]
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
          t (c/In left (c/-not right))
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
          css (ppinfer-substs no-mentions [left1 left2] [right1 right2])
          ]
      true))
  (is-clj
    (let [left1 (r/make-FnIntersection
                 (r/make-Function
                   [(r/make-F 'a)]
                   (c/RClass-of Seqable [(c/RClass-of Boolean)])))
          right1 (r/make-FnIntersection
                  (r/make-Function
                    [(r/make-F 'b)]
                    (r/make-F 'b)))
          left2 (r/make-FnIntersection
                 (r/make-Function
                   [(c/Un (c/RClass-of Seqable [(c/RClass-of Integer)])
                          (c/RClass-of Seqable [(c/RClass-of Boolean)]))]
                   (c/RClass-of Integer)))
          right2 (r/make-FnIntersection
                  (r/make-Function
                    [(r/make-F 'a)]
                    (r/make-F 'b)))
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1 left2] [right1 right2])
          ]
      true))
  (is-clj
    (let [left1 (c/RClass-of Boolean)
          right1 (r/make-F 'b)
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1] [right1])
          ]
      true))
  (is-clj
    (let [left1 (c/RClass-of Seqable [(c/RClass-of Boolean)])
          right1 (c/RClass-of Seqable [(r/make-F 'b)])
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1] [right1])
          ]
      true))
  (is-clj
    (let [left1 (r/make-FnIntersection
                  (r/make-Function
                    [(r/make-FnIntersection
                       (r/make-Function
                         [(r/make-F 'a1)]
                         (r/make-F 'b1)))]
                    (r/make-FnIntersection
                      (r/make-Function
                        [(c/RClass-of Seqable [(r/make-F 'a1)])]
                        (c/RClass-of Seqable [(r/make-F 'b1)])))))
          right1 (r/make-FnIntersection
                   (r/make-Function
                     [(r/make-FnIntersection
                        (r/make-Function
                          [(c/RClass-of Integer)]
                          (c/RClass-of Boolean))
                        (r/make-Function
                          [(c/In (r/make-F 'a) (c/-not
                                                 (c/RClass-of Integer)))]
                          (c/In (r/make-F 'a) (c/-not
                                                 (c/RClass-of Integer)))))]
                     (r/make-F 'gamma)))
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1] [right1])
          ]
      true))
  (is-clj
    (let [left1 (r/make-FnIntersection
                  (r/make-Function
                    [(r/make-F 'x)]
                    (r/make-F 'x)))
          right1 (r/make-FnIntersection
                   (r/make-Function
                     [(r/-val 1)]
                     (r/make-F 'result)))
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1] [right1])
          ]
      true))
  (is-clj
    (cs-gen-normalized-no-tvar #{} [r/-nothing] #{}))
  (is-clj
    (let [left1  r/-nothing
          right1 (r/make-F 'result)
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1] [right1])
          ]
      true))
  (is-clj
    (let [left1  (r/make-F 'result)
          right1 r/-nothing
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1] [right1])
          ]
      true))
  (is-clj
    (let [
          left1  (r/make-F 'chain1)
          right1 (r/make-F 'chain2)
          left2  (r/make-F 'chain2)
          right2 (r/make-F 'chain3)
          left3  (c/RClass-of Integer)
          right3 (r/make-F 'chain3)
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1 left2 left3] [right1 right2 right3])
          ]
      true))
  (is-clj
    (let [
          left1  (c/RClass-of Integer)
          right1 (r/make-F 'chain1)
          left2  (r/make-F 'chain1)
          right2 (r/make-F 'chain2)
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1 left2 ] [right1 right2 ])
          ]
      true))
  (is-clj
    (let [
          left1  (c/RClass-of Integer)
          right1 r/-nothing
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1] [right1])
          ]
      true))
  (is-clj
    (let [
          left1  (c/RClass-of Integer)
          right1 r/-nothing
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1] [right1])
          ]
      true))
  (is-clj
    (let [left1 (r/make-FnIntersection
                  (r/make-Function
                    [r/-nothing]
                    r/-nothing))
          right1 (r/make-FnIntersection
                   (r/make-Function
                     [(r/-val 1)]
                     (r/make-F 'result)))
          no-mentions #{}
          css (ppinfer-substs no-mentions [left1] [right1])
          ]
      true))
)

(comment
(impl/with-clojure-impl
  (norm2
    #{}
    (prs/parse-type '(t/I (clojure.lang.APersistentVector t/Num) (t/ExactCount 1)))
    (c/RClass-of clojure.lang.Seqable [(r/make-F 'x)])
    #{}))

(impl/with-clojure-impl
  (norm
    #{}
    (c/RClass-of Integer)
    #{}))

(c/flatten-intersections
  [(c/In (c/In (r/make-F 'b) (c/-not (r/make-F 'a)))
        (c/-not (c/RClass-of Integer)))])

(fully-resolve-under-Not
  (c/In (c/In (r/make-F 'b) (c/-not (r/make-F 'a)))
        (c/-not (c/RClass-of Integer))))

(c/In (r/make-F 'b) (c/-not (r/make-F 'a))
      (c/-not (c/RClass-of Integer)))
(clj
  (c/In (r/-val 1)
        (c/-not 
          (c/In (r/make-F 'a)
                (c/-not (c/RClass-of Integer))))))
(clj
  (c/-not 
    (c/In (r/make-F 'a)
          (c/-not (c/RClass-of Integer)))))

(clj
  (c/In (r/-val 1)
        (c/-not 
          (c/In (r/make-F 'a)
                (c/-not (c/RClass-of Integer))))))
(clj
  (norm2 #{}
         (c/In (r/make-F 'a)
               (c/-not (c/RClass-of Integer))
               (c/-not (c/RClass-of Byte))
               )
         (r/-val 'b)
         #{}))
(clj
  (norm2 #{}
         (r/-val 'b)
         (c/In (r/make-F 'a)
               (c/-not (c/Un (c/RClass-of Integer)
                             (c/RClass-of Byte)))
               #_(c/-not (r/Name-maker `t/Int)))
         #{}))
(clj
  (norm2 #{}
         (r/-val 'b)
         (c/-not (c/RClass-of Integer))
         #{}))
(is
  (= fail-css
     (clj
       (norm2 #{}
              (r/-val 'b)
              r/-nothing
              #{}))
     ))
(clj
  (cs-gen-normalized-no-tvar
    #{}
    [(c/RClass-of Integer)]
    #{}))
(clj
  (cs-gen-normalized-no-tvar
    #{}
    [(c/RClass-of Integer)
     (c/RClass-of Boolean)]
    #{}))
(clj
  (norm2
    #{}
    (c/RClass-of Integer)
    (c/RClass-of Boolean)
    #{}))

(clj
  (norm2
    #{}
    (c/RClass-of Integer)
    r/-nothing
    #{}))
(clj
  (cs-gen-normalized-no-tvar
    #{}
    [(c/RClass-of Integer) r/-nothing]
    #{}))
;"(I" (Val 1) "(Not" (I (Not Integer) (Not BigInteger) (Not BigInt) (Not Long) (Not Short) (Not Byte) a) "))" 

(clj
  (c/In (r/-val 1)
        (c/-not (c/In (c/-not (c/RClass-of Integer))
                      (c/-not (c/RClass-of BigInteger))
                      (c/-not (c/RClass-of clojure.lang.BigInt))
                      (c/-not (c/RClass-of Long))
                      (r/make-F 'a)))))
(clj
  (c/In (r/-val 1)
        (c/Un (c/RClass-of Integer)
              (c/RClass-of BigInteger)
              (c/RClass-of clojure.lang.BigInt)
              (c/RClass-of Long)
              (c/-not (r/make-F 'a)))))
(clj
  (c/Un (c/In (r/-val 1) (c/RClass-of Integer))
        (c/In (r/-val 1) (c/RClass-of BigInteger))
        (c/In (r/-val 1) (c/RClass-of clojure.lang.BigInt))
        (c/In (r/-val 1) (c/RClass-of Long))
        (c/In (r/-val 1) (c/-not (r/make-F 'a)))))
(clj
  (= fail-css
     (norm2
       #{}
       (r/-val 'a)
       (c/RClass-of Long)
       #{})))
(clj
  (norm
    #{}
    (clj (c/In (r/-val 'a)
               (c/RClass-of Long)))
    #{}))
(clj
  (= fail-css
     (norm
       #{}
       r/-any
       #{})))
(clj
  (= success-css
     (norm
       #{}
       r/-nothing
       #{})))
(clj
  (= fail-css
     (csmerge
       #{}
       (constraint-set
         (constraint r/-any 'x r/-nothing))
       #{})))
;; this must work to implement (I [a -> c] [b -> c]) <: [(U a b) -> c]
(clj
  (norm2 #{}
         (r/make-FnIntersection
           (r/make-Function
             [(c/RClass-of Long)]
             (c/RClass-of Boolean))
           (r/make-Function
             [(c/RClass-of clojure.lang.Symbol)]
             (c/RClass-of Boolean)))
         (r/make-FnIntersection
           (r/make-Function
             [(c/Un (c/RClass-of Long)
                    (c/RClass-of clojure.lang.Symbol))]
             (c/RClass-of Boolean)))
         #{}))

(clj
  (norm2 #{}
         (c/RClass-of clojure.lang.IPersistentVector [(r/make-F 'b)])
         (c/RClass-of Seqable [(r/make-F  'a)])
         #{}))
)
