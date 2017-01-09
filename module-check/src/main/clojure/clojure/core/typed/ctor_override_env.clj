(ns clojure.core.typed.ctor-override-env
  (:require [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.env :as env]
            [clojure.core.typed.type-rep :as r]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructor Override Env

(def constructor-override-env-kw ::constructor-override-env)

(defn add-constructor-override [sym t]
  {:pre [(symbol? sym)
         ((some-fn delay? r/Type?) t)]}
  (env/swap-checker! assoc-in [constructor-override-env-kw sym] t)
  nil)

(defn reset-constructor-override-env! [m]
  (env/swap-checker! assoc constructor-override-env-kw m)
  nil)

(defn constructor-override-env []
  {:post [(map? %)]}
  (get (env/deref-checker) constructor-override-env-kw {}))

(defn get-constructor-override [sym]
  {:post [((some-fn delay? r/Type?) %)]}
  (force (get (constructor-override-env) sym)))
