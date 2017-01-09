(ns clojure.core.typed.method-param-nilables
  (:require [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.env :as env]
            [clojure.core.typed.type-rep :as r]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Method Param nilables

(def method-param-nilable-env-kw ::method-param-nilable-env)

(defn reset-method-nilable-param-env! [m]
  (reset! METHOD-PARAM-NILABLE-ENV m)
  nil)

(defn add-method-nilable-param [sym a]
  {:pre [((every-pred namespace symbol?) sym)
         ((con/hash-c? (some-fn #{:all} con/znat?)
                       (some-fn #{:all} (con/set-c? con/znat?)))
          a)]}
  (env/swap-checker! assoc-in [method-param-nilable-env-kw sym] a)
  nil)

(defn nilable-param-env []
  {:post [(map? %)]}
  (get (env/deref-checker) method-param-nilable-env-kw {}))

(defn nilable-param? [sym arity param]
  (boolean 
    (when-let [nilables (get (nilable-param-env) sym)]
      (when-let [params (or (nilables :all)
                            (nilables arity))]
        (or (#{:all} params)
            (params param))))))
