(ns clojure.core.typed.collect.gen-protocol
  (:require [clojure.core.typed.errors :as err]
            [clojure.core.typed.type-ctors :as c]
            [clojure.core.typed.name-env :as nme-env]
            [clojure.core.typed.parse-unparse :as prs]
            [clojure.core.typed.type-rep :as r]
            [clojure.core.typed.free-ops :as free-ops]
            [clojure.core.typed.util-vars :as vs]
            [clojure.core.typed.protocol-env :as ptl-env]
            [clojure.core.typed.var-env :as var-env]
            [clojure.core.typed.collect-utils :as clt-u]))

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
        _ (nme-env/declare-protocol* s)
        parsed-binder (when binder 
                        (delay
                          (binding [prs/*parse-type-in-ns* current-ns]
                            (prs/parse-free-binder-with-variance binder))))
        fs (when parsed-binder
             (delay (map (comp r/make-F :fname) (force parsed-binder))))
        bnds (when parsed-binder
               (delay (map :bnd (force parsed-binder))))
        ms (into {} (for [[knq v] mths]
                      (let [_ (when (namespace knq)
                                (err/int-error "Protocol method should be unqualified"))
                            mtype 
                            (delay
                              (let [mtype (free-ops/with-bounded-frees (zipmap (force fs) (force bnds))
                                            (binding [vs/*current-env*       current-env
                                                      prs/*parse-type-in-ns* current-ns]
                                              ;(prn "parsing" v current-ns *ns*)
                                              (prs/parse-type v)))
                                    _ (let [rt (c/fully-resolve-type mtype)
                                            fin? (fn [f]
                                                   (let [f (c/fully-resolve-type f)]
                                                     (boolean
                                                       (when (r/FnIntersection? f)
                                                         (every? seq (map :dom (:types f)))))))]
                                        (when-not 
                                          (or
                                            (fin? rt)
                                            (when (r/Poly? rt) 
                                              (let [names (c/Poly-fresh-symbols* rt)]
                                                (fin? (c/Poly-body* names rt))))
                                            (when (r/PolyDots? rt) 
                                              (let [names (c/PolyDots-fresh-symbols* rt)]
                                                (fin? (c/PolyDots-body* names rt)))))
                                          ;(prn "throwing method type")
                                          (err/int-error (str "Protocol method " knq " should be a possibly-polymorphic function intersection"
                                                              " taking at least one fixed argument: "
                                                              (prs/unparse-type mtype)))))]
                                mtype))]
                         [knq mtype])))
        ;_ (prn "collect protocol methods" (into {} ms))
        t (delay
            (c/Protocol* (map :name (force fs)) (map :variance (force parsed-binder) )
                         (force fs) s (c/Protocol-var->on-class s) 
                         (into {} (map (fn [[k v]] [k (force v)])) ms) 
                         (map :bnd (force parsed-binder))))]
    ;(prn "Adding protocol" s t)
    (ptl-env/add-protocol s t)
    ; annotate protocol var as Any
    (var-env/add-nocheck-var s)
    (var-env/add-var-type s (delay r/-any))
    (doseq [[kuq mt] ms]
      (assert (not (namespace kuq))
              "Protocol method names should be unqualified")
      ;qualify method names when adding methods as vars
      (let [kq (symbol protocol-defined-in-nstr (name kuq))
            mt-ann (delay (clt-u/protocol-method-var-ann (force mt) (map :name (force fs)) (force bnds)))]
        (var-env/add-nocheck-var kq)
        (var-env/add-var-type kq mt-ann)))
    ;(prn "end gen-protocol" s)
    nil))
