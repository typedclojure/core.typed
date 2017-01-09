(ns clojure.core.typed.method-return-nilables
  (:require [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.env :as env]
            [clojure.core.typed.current-impl :as impl]
            [clojure.core.typed.type-rep :as r]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Method Return non-nilables

(def add-nonnilable-method-return impl/add-nonnilable-method-return)

(defn reset-nonnilable-method-return-env! [m]
  (reset! METHOD-RETURN-NONNILABLE-ENV m)
  nil)

(defn nonnilable-method-return-env [sym m]
  {:post [(map? %)]}
  (get (env/deref-checker) impl/method-return-nonnilable-env-kw {}))

(defn nonnilable-return? [sym arity]
  (let [as (get (nonnilable-method-return-env) sym)]
    (boolean (or (= :all as)
                 (when as
                   (as arity))))))
