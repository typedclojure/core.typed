(ns clojure.core.typed.method-override-env
  (:require [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.env :as env]
            [clojure.core.typed.current-impl :as impl]
            [clojure.core.typed.type-rep :as r]))

; Should only override a method with a more specific type
; eg. 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Method Override Env

(def method-override-env-kw ::method-override-env)

(defonce METHOD-OVERRIDE-ENV 
  (atom {}
        :validator (con/hash-c? (every-pred namespace symbol?)
                                (some-fn r/Poly? r/FnIntersection?))))

(defn add-method-override [sym t]
  {:pre [((every-pred symbol? namespace) sym)
         ;; checked at `get-method-override`
         #_
         ((some-fn delay? r/Poly? r/FnIntersection?)
          t)]}
  (env/swap-checker! assoc-in [method-override-env-kw sym] t)
  nil)

(defn reset-method-override-env! [m]
  (env/swap-checker! assoc method-override-env-kw m)
  nil)

(defn method-override-env []
  {:post [(map? %)]}
  (get (env/deref-checker) method-override-env-kw {}))

(defn get-method-override [m]
  {:post [((some-fn r/Poly? r/FnIntersection? nil?) %)]}
  (force (get (method-override-env) m)))
