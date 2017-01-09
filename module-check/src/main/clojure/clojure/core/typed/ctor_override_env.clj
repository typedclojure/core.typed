(ns clojure.core.typed.ctor-override-env
  (:require [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.env :as env]
            [clojure.core.typed.current-impl :as impl]
            [clojure.core.typed.type-rep :as r]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructor Override Env

(def add-constructor-override impl/add-constructor-override)

(defn reset-constructor-override-env! [m]
  (env/swap-checker! assoc impl/constructor-override-env-kw m)
  nil)

(defn constructor-override-env []
  {:post [(map? %)]}
  (get (env/deref-checker) impl/constructor-override-env-kw {}))

(defn get-constructor-override [sym]
  {:post [((some-fn delay? r/Type?) %)]}
  (force (get (constructor-override-env) sym)))
