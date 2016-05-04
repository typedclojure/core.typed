(ns clojure.core.typed.check-ns-common
  (:require [clojure.core.typed.profiling :as p]
            [clojure.core.typed.load1 :as load]
            [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.current-impl :as impl])
  (:import (clojure.lang ExceptionInfo)))

;; returns a map with keys
;; - :delayed errors    a vector of ExceptionInfo instances representing type errors
;;
;; Optional
;; - :file-mapping      a map from namespace symbols to vectors of AST nodes
;;                      Added if true :file-mapping keyword is passed as an option
(defn check-ns-info
  [impl ns-or-syms & {:keys [collect-only trace profile file-mapping]}]
  (p/profile-if profile
    (let [start (. System (nanoTime))]
      ;(reset-caches/reset-caches)
      (let [nsym-coll (map #(if (symbol? %)
                              ; namespace might not exist yet, so ns-name is not appropriate
                              ; to convert to symbol
                              %
                              (ns-name %))
                           (if ((some-fn symbol? con/namespace?)
                                ns-or-syms)
                             [ns-or-syms]
                             ns-or-syms))]
        (impl/with-full-impl impl
          (impl/impl-case
            :clojure (doseq [sym nsym-coll]
                       (with-redefs [load load/typed-load1]
                         (require sym :reload)))
            :cljs (assert nil "check-ns NYI")))))))

(defn check-ns
  [impl ns-or-syms & opt]
  (apply check-ns-info impl ns-or-syms opt)
  :ok)
