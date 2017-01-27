(ns cljs.core.typed.test.ympbyc.ast-nodes
  (:require-macros [cljs.core.typed :refer [ann] :as ct])
  (:require [cljs.core.typed :as t]))

(def ^:dynamic *dyn* "foo")


(ann x t/Number)
(def x
  #_(binding [*dyn* 1]
      *dyn*)
  (let [x 1] x))
