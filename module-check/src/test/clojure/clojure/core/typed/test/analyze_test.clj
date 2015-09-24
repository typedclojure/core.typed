(ns clojure.core.typed.test.analyze-test
  (:require [clojure.test :refer :all]
            [clojure.core.typed.analyze-clj :as ana]))

(let [{:keys [a]} nil])

(deftest analyze-test
  (testing "ast-for-file-for-cljc"
    (is
      (not
        (nil?
          (ana/ast-for-file "clojure/core/typed/test/dummy_clj.clj"))))
    (is
      (not
        (nil?
          (ana/ast-for-file "clojure/core/typed/test/dummy_cljc.cljc"))))))
