(ns clojure.core.typed.analyzer2.passes.jvm.classify-invoke
  (:require [clojure.core.typed.analyzer2.passes.jvm.validate :as validate]
            [clojure.tools.analyzer.passes.jvm.classify-invoke :as classify-invoke]))

;;redefine passes mainly to move dependency on `uniquify-locals`
;; to `uniquify2/uniquify-locals`
(defn classify-invoke
  "If the AST node is an :invoke, check the node in function position,
   * if it is a keyword, transform the node in a :keyword-invoke node;
   * if it is the clojure.core/instance? var and the first argument is a
     literal class, transform the node into a :instance? node to be inlined by
     the emitter
   * if it is a protocol function var, transform the node into a :protocol-invoke
     node
   * if it is a regular function with primitive type hints that match a
     clojure.lang.IFn$[primitive interface], transform the node into a :prim-invoke
     node"
  {:pass-info {:walk :post :depends #{#'validate/validate}}} ;; use this validate
  [& args]
   (apply classify-invoke/classify-invoke args))

