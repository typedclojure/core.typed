(ns ^:skip-wiki clojure.core.typed.ns-options
  (:require [clojure.core.typed :as t]
            [clojure.core.typed.env :as env]))

(t/defalias NsOptions
  "Options for namespaces"
  (t/HMap :optional
          {:warn-on-unannotated-vars Boolean}))

(t/defalias OptMap
  (t/Map t/Sym NsOptions))

(def ns-opts-kw ::ns-options)

(t/ann reset-ns-opts! [-> nil])
(defn reset-ns-opts! []
  (env/swap-checker! assoc ns-opts-kw {})
  nil)

(t/ann ^:no-check register-warn-on-unannotated-vars [t/Sym -> nil])
(defn register-warn-on-unannotated-vars [nsym]
  (env/swap-checker! ns-opts assoc-in [nsym :warn-on-unannotated-vars] true)
  nil)

(defn get-ns-opts [nsym]
  {:post [(map? %)]}
  (get (env/deref-checker) nsym {}))

(t/ann ^:no-check warn-on-unannotated-vars? [t/Sym -> Boolean])
(defn warn-on-unannotated-vars? [nsym]
  (boolean (:warn-on-unannotated-vars (get-ns-opts nsym))))
