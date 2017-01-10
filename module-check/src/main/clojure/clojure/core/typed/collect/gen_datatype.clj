(ns clojure.core.typed.collect.gen-datatype
  (:require [clojure.core.typed.current-impl :as impl]
            [clojure.repl :as repl]
            [clojure.core.typed.util-vars :as vs]
            [clojure.core.typed.parse-unparse :as prs]
            [clojure.core.typed.datatype-ancestor-env :as ancest]))

(defn parse-field [[n _ t]] 
  [n (prs/parse-type t)])

(defn gen-datatype* [current-env current-ns provided-name fields vbnd opt record?]
  {:pre [(symbol? current-ns)]}
  (impl/with-clojure-impl
    (let [{ancests :unchecked-ancestors} opt
          ancests (or ancests (:extends opt))
          parsed-binders (when vbnd
                           (delay
                             (let [_ (require 'clojure.core.typed.parse-unparse)
                                   parse-free-binder-with-variance 
                                   (impl/v 'clojure.core.typed.parse-unparse/parse-free-binder-with-variance)
                                   with-parse-ns* (impl/v 'clojure.core.typed.parse-unparse/with-parse-ns*)]
                               (with-parse-ns* current-ns
                                 #(parse-free-binder-with-variance vbnd)))))
          ;variances
          vs (when parsed-binders
               (delay (seq (map :variance (force parsed-binders)))))
          args (when parsed-binders
                 (delay (seq (map :fname (force parsed-binders)))))
          bnds (when parsed-binders
                 (delay (seq (map :bnd (force parsed-binders)))))]
      (let [provided-name-str (str provided-name)
            ;_ (prn "provided-name-str" provided-name-str)
            munged-ns-str (if (some #(= \. %) provided-name-str)
                            (apply str (butlast (apply concat (butlast (partition-by #(= \. %) provided-name-str)))))
                            (str (munge current-ns)))
            ;_ (prn "munged-ns-str" munged-ns-str)
            demunged-ns-str (str (repl/demunge munged-ns-str))
            ;_ (prn "demunged-ns-str" demunged-ns-str)
            local-name (if (some #(= \. %) provided-name-str)
                         (symbol (apply str (last (partition-by #(= \. %) (str provided-name-str)))))
                         provided-name-str)
            ;_ (prn "local-name" local-name)
            s (symbol (str munged-ns-str \. local-name))
            fs (delay
                 (let [_ (require 'clojure.core.typed.parse-unparse
                                  'clojure.core.typed.type-rep
                                  'clojure.core.typed.type-ctors
                                  'clojure.core.typed.free-ops)
                       with-parse-ns* (impl/v 'clojure.core.typed.parse-unparse/with-parse-ns*)
                       parse-type (impl/v 'clojure.core.typed.parse-unparse/parse-type)
                       make-F (impl/v 'clojure.core.typed.type-rep/make-F)
                       abstract-many (impl/v 'clojure.core.typed.type-ctors/abstract-many)
                       with-frees* (impl/v 'clojure.core.typed.free-ops/with-frees*)
                       parse-field (fn [[n _ t]] [n (parse-type t)])
                       ]
                   (apply array-map (apply concat (with-frees* (mapv make-F (force args))
                                                    (fn []
                                                      (binding [vs/*current-env* current-env]
                                                        (with-parse-ns* current-ns
                                                          #(mapv parse-field (partition 3 fields))))))))))
            as (into {}
                     (map
                       (fn [an]
                         [an (delay
                               (let [_ (require 'clojure.core.typed.parse-unparse
                                                'clojure.core.typed.type-rep
                                                'clojure.core.typed.type-ctors
                                                'clojure.core.typed.free-ops)
                                     with-parse-ns* (impl/v 'clojure.core.typed.parse-unparse/with-parse-ns*)
                                     parse-type (impl/v 'clojure.core.typed.parse-unparse/parse-type)
                                     make-F (impl/v 'clojure.core.typed.type-rep/make-F)
                                     with-frees* (impl/v 'clojure.core.typed.free-ops/with-frees*)
                                     abstract-many (impl/v 'clojure.core.typed.type-ctors/abstract-many)]
                                 (with-frees* (mapv make-F (force args))
                                   (fn []
                                     (binding [vs/*current-env* current-env]
                                       (with-parse-ns* current-ns
                                         #(let [t (parse-type an)]
                                            (abstract-many (force args) t))))))))]))
                     ancests)
            ;_ (prn "collected ancestors" as)
            _ (ancest/add-datatype-ancestors s as)
            pos-ctor-name (symbol demunged-ns-str (str "->" local-name))
            map-ctor-name (symbol demunged-ns-str (str "map->" local-name))
            dt (delay 
                 (let [_ (require 'clojure.core.typed.type-ctors
                                  'clojure.core.typed.type-rep)
                       DataType* (impl/v 'clojure.core.typed.type-ctors/DataType*)
                       make-F (impl/v 'clojure.core.typed.type-rep/make-F)]
                   (DataType* (force args) (force vs) (map make-F (force args)) s (force bnds) (force fs) record?)))
            _ (impl/add-datatype s dt)
            pos-ctor (delay
                       (let [_ (require 'clojure.core.typed.subtype
                                        'clojure.core.typed.type-rep
                                        'clojure.core.typed.frees
                                        'clojure.core.typed.type-ctors)
                             Poly* (impl/v 'clojure.core.typed.type-ctors/Poly*)
                             make-FnIntersection (impl/v 'clojure.core.typed.type-rep/make-FnIntersection)
                             make-Function (impl/v 'clojure.core.typed.type-rep/make-Function)
                             make-F (impl/v 'clojure.core.typed.type-rep/make-F)
                             DataType-of (impl/v 'clojure.core.typed.type-ctors/DataType-of)
                             ]
                         (if args
                           (Poly* (force args) (force bnds)
                                  (make-FnIntersection
                                    (make-Function (vec (vals (force fs))) (DataType-of s (map make-F (force args))))))
                           (make-FnIntersection
                             (make-Function (vec (vals (force fs))) (DataType-of s))))))
            map-ctor (delay
                       (let [_ (require 'clojure.core.typed.subtype
                                        'clojure.core.typed.type-rep
                                        'clojure.core.typed.frees
                                        'clojure.core.typed.type-ctors)
                             subtype? (impl/v 'clojure.core.typed.subtype/subtype?)
                             -val (impl/v 'clojure.core.typed.type-rep/-val)
                             -nil (impl/v 'clojure.core.typed.type-rep/-nil)
                             fv (impl/v 'clojure.core.typed.frees/fv)
                             fi (impl/v 'clojure.core.typed.frees/fi)
                             make-HMap (impl/v 'clojure.core.typed.type-ctors/make-HMap)
                             Poly* (impl/v 'clojure.core.typed.type-ctors/Poly*)
                             make-FnIntersection (impl/v 'clojure.core.typed.type-rep/make-FnIntersection)
                             make-Function (impl/v 'clojure.core.typed.type-rep/make-Function)
                             make-F (impl/v 'clojure.core.typed.type-rep/make-F)
                             DataType-of (impl/v 'clojure.core.typed.type-ctors/DataType-of)]
                         (when record?
                           (let [hmap-arg ; allow omission of keys if nil is allowed and field is monomorphic
                                 (let [{optional true mandatory false} 
                                       (group-by (fn [[_ t]] (and (empty? (fv t))
                                                                  (empty? (fi t))
                                                                  (subtype? -nil t)))
                                                 (zipmap (map (comp -val keyword) (keys (force fs)))
                                                         (vals (force fs))))]
                                   (make-HMap :optional (into {} optional)
                                              :mandatory (into {} mandatory)))]
                             (if args
                               (Poly* (force args) (force bnds)
                                      (make-FnIntersection
                                        (make-Function [hmap-arg] (DataType-of s (map make-F (force args))))))
                               (make-FnIntersection
                                 (make-Function [hmap-arg] (DataType-of s))))))))]
        (do 
          ;(when vs
          ;  (let [f (mapv r/make-F (repeatedly (count vs) gensym))]
          ;    ;TODO replacements and unchecked-ancestors go here
          ;    (rcls/alter-class* s (c/RClass* (map :name f) (force vs) f s {} {} (force bnds)))))
          (impl/add-tc-var-type pos-ctor-name pos-ctor)
          (impl/add-nocheck-var pos-ctor-name)
          (when record?
            (impl/add-method-override (symbol (str s) "create") map-ctor)
            (impl/add-tc-var-type map-ctor-name map-ctor)))))))
