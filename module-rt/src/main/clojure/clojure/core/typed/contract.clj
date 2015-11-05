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


(defmacro contract [c x b] ; take +ve -ve blame
  (let [b (or b
              (make-blame :positive (str (ns-name *ns*))
                          :negative (str "Not " (ns-name *ns*))))]
    `(((:projection ~c) ~b) ~x)))

(defn swap-blame [x] x) ;TODO

(def int-c (make-contract :name 'int-c :first-order integer?))
(defn ifn-c [c1 c2]
  (make-contract
    :name 'ifn-c
    :first-order ifn?
    :projection (fn [b]
                  (fn [f]
                    ; returning a contracted function
                    (with-meta
                      (fn [x]
                        (contract c2
                                  (f (contract c1 x (swap-blame b)))
                                  b))
                      nil
                      #_(meta f))))))


(deftest int-c-test
  (is (= (contract int-c 1 nil) 1))
  (is (thrown? clojure.lang.ExceptionInfo (contract int-c nil nil))))

(deftest ifn-test
  (is (= ((contract (ifn-c int-c int-c) (fn [x] x) nil) 1)
         1))
  (is (thrown? clojure.lang.ExceptionInfo
               ((contract (ifn-c int-c int-c) (fn [x] x) nil) nil))))

(comment
        )
