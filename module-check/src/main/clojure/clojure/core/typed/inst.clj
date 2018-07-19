(ns ^:skip-wiki clojure.core.typed.inst
  (:require [clojure.core.typed.utils :as u]
            [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.errors :as err]
            [clojure.core.typed.parse-unparse :as prs]
            [clojure.core.typed.type-rep :as r]
            [clojure.core.typed.type-ctors :as c]
            [clojure.core.typed.free-ops :as free-ops]
            [clojure.core.typed.subtype :as sub]
            [clojure.core.typed.subst :as subst]
            [clojure.core.typed.trans :as trans]
            [clojure.string :as string]
            [clojure.pprint :as pprint])
  (:import (clojure.core.typed.type_rep Poly Bounds PolyDots F)))

(alter-meta! *ns* assoc :skip-wiki true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Polymorphic type instantiation

(defn same-or-narrower-bounds?
  "True if arg-bounds is inside bounds, false otherwise"
  [bounds arg-bounds]
  {:pre [(r/Bounds? bounds)
         (r/Bounds? arg-bounds)]
   :post [(con/boolean? %)]}
  (and (sub/subtype? (:lower-bound bounds) (:lower-bound arg-bounds))
       (sub/subtype? (:upper-bound arg-bounds) (:upper-bound bounds))
       ; make sure bounds make sense
       (sub/subtype? (:lower-bound bounds) (:upper-bound bounds))
       (sub/subtype? (:lower-bound arg-bounds) (:upper-bound arg-bounds))))

(defn satisfies-bounds?
  "True if type t is inside bounds"
  [t bnds]
  (and (sub/subtype? t (:upper-bound bnds))
       (sub/subtype? (:lower-bound bnds) t)))

(defn manual-inst 
  "Poly (Vec Type) (Map Sym Type) -> Type
  Substitute the type parameters of the polymorphic type
  with given types"
  [ptype argtys named]
  {:pre [((some-fn r/Poly? r/PolyDots?) ptype)
         (vector? argtys)
         (every? r/Type? argtys)
         (every? symbol? (keys named))
         (every? r/Type? (vals named))]
   :post [(r/Type? %)]}
  (let [dotted? (r/PolyDots? ptype)
        nrequired ((if dotted? dec identity)
                   (- (:nbound ptype) (count (:named ptype))))
        _ (when-not ((if dotted? <= =) nrequired (count argtys))
            (err/int-error
              (str "Wrong number of arguments to instantiate polymorphic type (expected " 
                   (when dotted? "at least ")
                   nrequired
                   ", actual " (count argtys)
                   "\n\nTarget:\n" (prs/unparse-type ptype)
                   "\n\nActual arguments:\n" (string/join " " (map prs/unparse-type argtys)))))
        expected-named (:named ptype)
        _ (when (empty? expected-named)
            (when (seq named)
              (err/int-error (str "Passed :named types to instantiate first argument of inst, but this type doesn't have :named arguments: "
                                  (pr-str ptype)))))
        ;; splice :named arguments between fixed and dotted params
        argtys-before-named-subst (let [[fixedtys dottedtys] [(subvec argtys 0 nrequired)
                                                              (subvec argtys nrequired)]]
                                    ;; :named arguments default to t/Any
                                    (into fixedtys
                                          (concat (repeat (count expected-named) r/-any)
                                                  dottedtys)))
        ;; fill in provided :named arguments
        argtys (reduce (fn [argtys [k v]]
                         (if-let [i (get expected-named k)]
                           (assoc argtys i v)
                           (err/int-error (str "Unrecognized :named variable passed to inst, "
                                               "given: " (pr-str k)
                                               " expected one of: " (pr-str (keys expected-named))))))
                       argtys-before-named-subst
                       named)]
    (cond
      (r/Poly? ptype)
      (let [names (c/Poly-fresh-symbols* ptype)
            body (c/Poly-body* names ptype)
            bbnds (c/Poly-bbnds* names ptype)]
        (free-ops/with-bounded-frees (zipmap (map r/make-F names) bbnds)
          (doseq [[nme ty bnds] (map vector names argtys bbnds)]
            (assert (not (:higher-kind bnds)))
            (let [lower-bound (subst/substitute-many (:lower-bound bnds) argtys names)
                  upper-bound (subst/substitute-many (:upper-bound bnds) argtys names)]
              (when-not (sub/subtype? lower-bound upper-bound)
                (err/int-error
                  (str "Lower-bound " (prs/unparse-type lower-bound)
                       " is not below upper-bound " (prs/unparse-type upper-bound))))
              (when-not (and (sub/subtype? ty upper-bound)
                             (sub/subtype? lower-bound ty))
                (err/int-error
                  (str "Manually instantiated type " (prs/unparse-type ty)
                       " is not between bounds " (prs/unparse-type lower-bound)
                       " and " (prs/unparse-type upper-bound))))))
          (subst/substitute-many body argtys names)))

      (r/PolyDots? ptype)
      (let [names (c/PolyDots-fresh-symbols* ptype)
            body (c/PolyDots-body* names ptype)
            bbnds (c/PolyDots-bbnds* names ptype)]
        (free-ops/with-bounded-frees (zipmap (-> (map r/make-F names) butlast) (butlast bbnds))
          (doseq [[nme ty bnds] (map vector names argtys bbnds)]
            (let [lower-bound (subst/substitute-many (:lower-bound bnds) argtys names)
                  upper-bound (subst/substitute-many (:upper-bound bnds) argtys names)]
              (when-not (sub/subtype? lower-bound upper-bound)
                (err/int-error
                  (str "Lower-bound " (prs/unparse-type lower-bound)
                       " is not below upper-bound " (prs/unparse-type upper-bound))))
              (when-not (and (sub/subtype? ty upper-bound)
                             (sub/subtype? lower-bound ty))
                (err/int-error
                  (str "Manually instantiated type " (prs/unparse-type ty)
                       " is not between bounds " (prs/unparse-type lower-bound)
                       " and " (prs/unparse-type upper-bound))))))
          (-> body
            ; expand dotted pre-types in body
            (trans/trans-dots (last names) ;the bound
                              (drop (dec (:nbound ptype)) argtys)) ;the types to expand pre-type with
            ; substitute normal variables
            (subst/substitute-many (take nrequired argtys) (butlast names))))))))
