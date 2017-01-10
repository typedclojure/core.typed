(ns clojure.core.typed.collect.gen-protocol
  (:require [clojure.core.typed.errors :as err]
            [clojure.core.typed.current-impl :as impl]
            [clojure.core.typed.util-vars :as vs]))

(defn gen-protocol* [current-env current-ns vsym binder mths]
  {:pre [(symbol? current-ns)
         ((some-fn nil? map?) mths)]}
  (let [_ (when-not (symbol? vsym)
            (err/int-error
              (str "First argument to ann-protocol must be a symbol: " vsym)))
        s (if (namespace vsym)
            (symbol vsym)
            (symbol (str current-ns) (name vsym)))
        protocol-defined-in-nstr (namespace s)
        _ (when-let [[m] (seq (remove symbol? (keys mths)))]
            (err/int-error (str "Method names to ann-protocol must be symbols, found: " (pr-str m))))
        _ (doseq [n1 (keys mths)
                  n2 (keys mths)]
            (when (and (not= n1 n2)
                       (= (munge n1) (munge n2)))
              (err/int-error 
                (str "Protocol methods for " vsym " must have distinct representations: "
                     "both " n1 " and " n2 " compile to " (munge n1)))))
        ; add a Name so the methods can be parsed
        _ (impl/declare-protocol* s)
        parsed-binder (when binder 
                        (delay
                          (let [_ (require 'clojure.core.typed.parse-unparse)
                                parse-free-binder-with-variance 
                                (impl/v 'clojure.core.typed.parse-unparse/parse-free-binder-with-variance)
                                with-parse-ns* (impl/v 'clojure.core.typed.parse-unparse/with-parse-ns*)]
                            (with-parse-ns* current-ns
                              #(parse-free-binder-with-variance binder)))))
        fs (when parsed-binder
             (delay 
               (let [_ (require 'clojure.core.typed.type-rep)
                     make-F (impl/v 'clojure.core.typed.type-rep/make-F)]
                 (map (comp make-F :fname) (force parsed-binder)))))
        bnds (when parsed-binder
               (delay (map :bnd (force parsed-binder))))
        ms (into {} (for [[knq v] mths]
                      (let [_ (when (namespace knq)
                                (err/int-error "Protocol method should be unqualified"))
                            mtype 
                            (delay
                              (let [_ (require 'clojure.core.typed.free-ops
                                               'clojure.core.typed.parse-unparse)
                                    with-bounded-frees* (impl/v 'clojure.core.typed.free-ops/with-bounded-frees*)
                                    with-parse-ns* (impl/v 'clojure.core.typed.parse-unparse/with-parse-ns*)
                                    unparse-type (impl/v 'clojure.core.typed.parse-unparse/unparse-type)
                                    parse-type (impl/v 'clojure.core.typed.parse-unparse/parse-type)
                                    mtype (with-bounded-frees* (zipmap (force fs) (force bnds))
                                            #(binding [vs/*current-env* current-env]
                                               (with-parse-ns* current-ns
                                                 (fn []
                                                   (parse-type v)))))
                                    _ (let [_ (require 'clojure.core.typed.type-ctors
                                                       'clojure.core.typed.type-rep)
                                            fully-resolve-type (impl/v 'clojure.core.typed.type-ctors/fully-resolve-type)
                                            Poly? (impl/v 'clojure.core.typed.type-rep/Poly?)
                                            Poly-fresh-symbols* (impl/v 'clojure.core.typed.type-ctors/Poly-fresh-symbols*)
                                            Poly-body* (impl/v 'clojure.core.typed.type-ctors/Poly-body*)
                                            PolyDots? (impl/v 'clojure.core.typed.type-rep/PolyDots?)
                                            PolyDots-fresh-symbols* (impl/v 'clojure.core.typed.type-ctors/PolyDots-fresh-symbols*)
                                            PolyDots-body* (impl/v 'clojure.core.typed.type-ctors/PolyDots-body*)
                                            FnIntersection? (impl/v 'clojure.core.typed.type-rep/FnIntersection?)
                                            rt (fully-resolve-type mtype)
                                            fin? (fn [f]
                                                   (let [f (fully-resolve-type f)]
                                                     (boolean
                                                       (when (FnIntersection? f)
                                                         (every? seq (map :dom (:types f)))))))]
                                        (when-not 
                                          (or
                                            (fin? rt)
                                            (when (Poly? rt) 
                                              (let [names (Poly-fresh-symbols* rt)]
                                                (fin? (Poly-body* names rt))))
                                            (when (PolyDots? rt) 
                                              (let [names (PolyDots-fresh-symbols* rt)]
                                                (fin? (PolyDots-body* names rt)))))
                                          ;(prn "throwing method type")
                                          (err/int-error (str "Protocol method " knq " should be a possibly-polymorphic function intersection"
                                                              " taking at least one fixed argument: "
                                                              (unparse-type mtype)))))]
                                mtype))]
                         [knq mtype])))
        ;_ (prn "collect protocol methods" (into {} ms))
        t (delay
            (let [_ (require 'clojure.core.typed.type-ctors)
                  Protocol* (impl/v 'clojure.core.typed.type-ctors/Protocol*)
                  Protocol-var->on-class (impl/v 'clojure.core.typed.type-ctors/Protocol-var->on-class)]
              (Protocol* (map :name (force fs)) (map :variance (force parsed-binder) )
                         (force fs) s (Protocol-var->on-class s) 
                         (into {} (map (fn [[k v]] [k (force v)])) ms) 
                         (map :bnd (force parsed-binder)))))]
    ;(prn "Adding protocol" s t)
    (impl/add-protocol s t)
    ; annotate protocol var as Any
    (impl/add-nocheck-var s)
    (impl/add-tc-var-type s (delay 
                              (let [_ (require 'clojure.core.typed.type-rep)
                                    -any (impl/v 'clojure.core.typed.type-rep/-any)]
                                -any)))
    (doseq [[kuq mt] ms]
      (assert (not (namespace kuq))
              "Protocol method names should be unqualified")
      ;qualify method names when adding methods as vars
      (let [kq (symbol protocol-defined-in-nstr (name kuq))
            mt-ann (delay 
                     (let [_ (require 'clojure.core.typed.collect-utils)
                           protocol-method-var-ann (impl/v 'clojure.core.typed.collect-utils/protocol-method-var-ann)]
                       (protocol-method-var-ann (force mt) (map :name (force fs)) (force bnds))))]
        (impl/add-nocheck-var kq)
        (impl/add-tc-var-type kq mt-ann)))
    ;(prn "end gen-protocol" s)
    nil))
