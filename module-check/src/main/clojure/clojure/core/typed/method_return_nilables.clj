(ns clojure.core.typed.method-return-nilables
  (:require [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.env :as env]
            [clojure.core.typed.type-rep :as r]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Method Return non-nilables

(def method-return-nonnilable-env-kw ::method-return-nonnilable-env)

(defn add-nonnilable-method-return [sym m]
  {:pre [((every-pred namespace symbol?) sym)
         ((some-fn #(= :all %)
                   (con/set-c? con/znat?))
          m)]}
  (env/swap-checker! assoc-in [method-return-nonnilable-env-kw sym] m)
  nil)

(defn reset-nonnilable-method-return-env! [m]
  (reset! METHOD-RETURN-NONNILABLE-ENV m)
  nil)

(defn nonnilable-method-return-env [sym m]
  {:post [(map? %)]}
  (get (env/deref-checker) method-return-nonnilable-env-kw {}))

(defn nonnilable-return? [sym arity]
  (let [as (get (nonnilable-method-return-env) sym)]
    (boolean (or (= :all as)
                 (when as
                   (as arity))))))
