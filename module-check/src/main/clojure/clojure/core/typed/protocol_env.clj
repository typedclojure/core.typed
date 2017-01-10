(ns ^:skip-wiki clojure.core.typed.protocol-env
  (:require [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.contract-ann]
            [clojure.core.typed.errors :as err]
            [clojure.core.typed.errors-ann]
            [clojure.core.typed.util-vars :as vs]
            [clojure.core.typed.type-rep :as r]
            [clojure.core.typed :as t]
            [clojure.core.typed.env :as env]))

(t/tc-ignore
(alter-meta! *ns* assoc :skip-wiki true)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Protocol Env

(t/defalias ProtocolEnv 
  "A map mapping protocol symbols their types."
  (t/Map t/Sym r/Type))

(def current-protocol-env-kw ::current-protocol-env)

(t/ann protocol-env? [t/Any -> t/Any])
(def protocol-env? (con/hash-c? (every-pred symbol? namespace)
                                (some-fn delay? r/Protocol? r/TypeFn?)))

(t/ann ^:no-check protocol-env [-> ProtocolEnv])
(defn protocol-env []
  {:post [(map? %)
          #_(protocol-env? %)]}
  (get (env/deref-checker) current-protocol-env-kw {}))

(t/ann ^:no-check reset-protocol-env! [ProtocolEnv -> nil])
(defn reset-protocol-env! [e]
  {:pre [#_(protocol-env? e)]}
  (env/swap-checker! assoc current-protocol-env-kw e)
  nil)

(t/ann ^:no-check add-protocol [t/Sym r/Type -> nil])
(defn add-protocol [sym t]
  {:pre [(symbol? sym)
         ((some-fn delay? r/Type?) t)]}
  (env/swap-checker! assoc-in [current-protocol-env-kw sym] t)
  nil)

(t/ann get-protocol [t/Sym -> (t/U nil r/Type)])
(defn get-protocol 
  "Returns the protocol with var symbol sym.
  Returns nil if not found."
  [sym]
  {:pre [(symbol? sym)]
   :post [((some-fn nil? r/Protocol? r/TypeFn?) %)]}
  (force (get (protocol-env) sym)))

(t/ann resolve-protocol [t/Sym -> r/Type])
(defn resolve-protocol [sym]
  {:post [(r/Type? %)]}
  (let [p (get-protocol sym)]
    (when-not p 
      (err/int-error (str "Could not resolve Protocol: " sym
                          "\n\nHint: Add protocol annotations with ann-protocol")))
    p))
