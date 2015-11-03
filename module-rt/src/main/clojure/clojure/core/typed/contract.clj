(ns clojure.core.typed.contract
  (:require [clojure.test :refer :all]))

(defrecord Contract [name first-order projection])
(defrecord Blame [positive negative location name contract])

(defn throw-blame [{:keys [positive negative] :as b}]
  (throw
    (ex-info
      (str "Positive blame: " positive "\n"
           "Negative blame: " negative "\n")
      (into {} b))))

(defn make-contract [& {:keys [name first-order projection]}]
  (let [name (or name 
                 'anonymous-contract)
        first-order (or first-order 
                        (fn [x] true))
        projection (or projection
                       (fn [b]
                         (fn [x]
                           (if (first-order x)
                             x
                             (throw-blame b)))))]
    (map->Contract
      {:name name
       :first-order first-order
       :projection projection})))

(defn make-blame [& {:as bls}]
  (map->Blame bls))


(def int-c (make-contract :name 'int-c :first-order integer?))

(defmacro contract [c x]
  (let [b (make-blame :positive (str (ns-name *ns*))
                      :negative (str "Not " (ns-name *ns*)))]
    `(((:projection ~c) ~b) ~x)))

(deftest int-c-test
  (is (= (contract int-c 1) 1))
  (is (thrown? clojure.lang.ExceptionInfo (contract int-c nil))))

(comment
        )
