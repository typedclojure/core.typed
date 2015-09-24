(ns clojure.core.typed.test.coerce-utils-test
  (:require [clojure.test :refer :all]
            [clojure.core.typed.coerce-utils :as cu]
            [clojure.core.typed.current-impl :as impl]
            [clojure.core.typed.var-env]
            [clojure.core.typed.name-env]
            [clojure.core.typed.datatype-ancestor-env]
            [clojure.core.typed.all-envs]
            [clojure.core.typed.ns-deps]))

(deftest coerce-utils-test
  (impl/with-clojure-impl
    (is
     (=
      "clojure/core/typed/test/dummy_clj.clj"
      (cu/ns->file (symbol "clojure.core.typed.test.dummy-clj"))))
    (is
     (=
      "clojure/core/typed/test/dummy_cljc.cljc"
      (cu/ns->file (symbol "clojure.core.typed.test.dummy-cljc")))))
  (impl/with-cljs-impl
    (is
     (=
      "clojure/core/typed/test/dummy_cljs.cljs"
      (cu/ns->file (symbol "clojure.core.typed.test.dummy-cljs"))))))
