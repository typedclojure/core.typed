(ns clojure.core.typed.contract
  (:require [clojure.test :refer :all]))

(defrecord Contract [name first-order projection flat?])
(defrecord Blame [positive negative location name contract])

(defn throw-blame [{:keys [positive negative] :as b}]
  (throw
    (ex-info
      (str "Positive blame: " positive "\n"
           "Negative blame: " negative "\n")
      (into {:blame true} b))))

(defn make-contract [& {:keys [name first-order projection flat?]
                        :or {flat? false}}]
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
       :projection projection
       :flat? flat?})))

(defn make-flat-contract [& args]
  (apply make-contract :flat? true args))

(defn make-blame [& {:as bls}]
  (map->Blame bls))

(defmacro contract 
  ([c x] `(contract ~c ~x nil))
  ([c x b]
   (let [b (or b
               (make-blame :positive (str (ns-name *ns*))
                           :negative (str "Not " (ns-name *ns*))))]
     `(((:projection ~c) ~b) ~x))))

(defn swap-blame [x] 
  (-> x
      (assoc :positive (:negative x))
      (assoc :negative (:positive x))))

(def int-c (make-flat-contract :name 'int-c :first-order integer?))

;; macro to allow instance? specialisation
(defmacro instance-c [c]
  `(make-flat-contract :name (str ~c)
                       :first-order #(instance? ~c %)))

(def Object-c (instance-c Object))
(defn flat-val-c [name pred]
  (make-flat-contract :name name :first-order pred))

(def nil-c (flat-val-c 'nil-c nil?))
(def true-c (flat-val-c 'true-c true?))
(def false-c (flat-val-c 'false-c false?))

(def any-c (make-flat-contract :name any-c))

(defn count-range-c [lower upper]
  (make-flat-contract :name 'count-range-c
                      :first-order (fn [x]
                                     (and (or (nil? x)
                                              (coll? x))
                                          (if upper
                                            (<= lower (count x) upper)
                                            (<= lower (count x)))))))

(defn equiv-c [y]
  (make-flat-contract :name 'equiv-c
                      :first-order (fn [x]
                                     (= x y))))

(defn identical-c [y]
  (make-flat-contract :name 'identical-c
                      :first-order (fn [x]
                                     (identical? x y))))


(defn ifn-c [cs c2]
  {:pre [(every? #(instance? Contract %) cs)
         (instance? Contract c2)]
   :post [(instance? Contract %)]}
  (make-contract
    :name 'ifn-c
    :first-order ifn?
    :projection (fn [b]
                  (fn [f]
                    ; returning a contracted function
                    (contract (make-contract :name 'ifn?
                                             :first-order ifn?)
                              f
                              b)
                    (with-meta
                      (fn [& xs]
                        (contract c2
                                  (apply f
                                         (map #(contract %1
                                                         %2
                                                         (swap-blame b))
                                              cs
                                              xs))
                                  b))
                      (if (fn? f)
                        (meta f)
                        nil))))))

(declare ->CheckedISeq)

(deftype CheckedISeq [s c b]
  clojure.lang.Sequential
  clojure.lang.ISeq
  (first [this]
    (contract c (first s) b))
  (next [this]
    (when-let [n (next s)]
      (->CheckedISeq n c b)))
  (cons [this x]
    (->CheckedISeq (conj s x) c b))
  (empty [this]
    (empty s))
  (seq [this]
    (when (seq s)
      this))
  (equiv [this o]
    (if (or (not (instance? clojure.lang.Sequential o))
            (not (instance? java.util.List o)))
      false
      (loop [ms this
             s (seq o)]
        (if (and s (= (first ms)
                      (first s)))
          (recur (next ms) (next s))
          (not ms))))))


(defn seqable-c [c]
  {:pre [(instance? Contract c)]
   :post [(instance? Contract %)]}
  (make-contract
    :name 'seqable-c
    :projection (fn [b]
                  (fn [s]
                    (contract Object-c s b)
                    (reify
                      clojure.lang.Seqable
                      (seq [this]
                        (->CheckedISeq s c b)))))))

(defn or-c [& cs]
  {:pre [(every? #(instance? Contract %) cs)]
   :post [(instance? Contract %)]}
  (let [{flat true hoc false} (group-by :flat? cs)
        _ (prn "flat" (mapv :name flat))
        _ (prn "hoc" (mapv :name hoc))
        flat-checks (apply some-fn (or (seq (map :first-order flat))
                                       ;; (U) always fails
                                       [(fn [_] false)]))
        choose-hoc
        (fn [x b]
          {:pre [(instance? Blame b)]}
          (let [hs (filter (fn [{:keys [first-order]}]
                             (first-order x))
                           hoc)]
            ;; don't realise more than needed, though chunking will
            ;; probably negate most of the benefit.
            (cond
              ;; more than one higher-order contract matched
              (second hs) (throw-blame b)
              ;; exactly one matched
              (first hs)  (contract (first hs) x b)
              ;; no contracts matched
              :else       (throw-blame b))))]
    (make-contract
      :name 'or-c
      :flat? (not (seq hoc))
      ; needed?
      :first-order (apply some-fn flat-checks (map :first-order hoc))
      :projection (fn [b]
                    (fn [x]
                      (if (flat-checks x)
                        x
                        (choose-hoc x b)))))))

(defn and-c [& cs]
  {:pre [(every? #(instance? Contract %) cs)]
   :post [(instance? Contract %)]}
  (let [{flat true hoc false} (group-by (comp boolean :flat?) cs)
        ;_ (prn "flat" (mapv :name flat))
        ;_ (prn "hoc" (mapv :name hoc))
        ]
    (if (< (count hoc) 2)
      (let [h (first hoc)]
        (make-contract
          :name 'and-c
          :flat? (not h)
          :first-order (apply every-pred (or (seq (map :first-order cs))
                                             ;; (I) always passes
                                             (fn [_] true)))
          :projection (fn [b]
                        (fn [x]
                          (doseq [f flat]
                            (contract f x b))
                          ;; could stage this conditional
                          (if h
                            (contract h x b)
                            x)))))
      (throw (ex-info 
               "Cannot create and-c contract with more than one higher-order contract"
               {:hoc (map :name hoc)})))))

(deftest int-c-test
  (is (= (contract int-c 1) 1))
  (is (thrown? clojure.lang.ExceptionInfo (contract int-c nil))))

(deftest ifn-test
  (is (= ((contract (ifn-c [int-c] int-c) (fn [x] x)) 1)
         1))
  (is (thrown? clojure.lang.ExceptionInfo
               ((contract (ifn-c [int-c] int-c) (fn [x] x)) nil))))

(deftest Object-c-test
  (is (= (contract Object-c 1) 1))
  (is (thrown? clojure.lang.ExceptionInfo
               (= (contract Object-c nil) 1))))

(deftest val-c-test
  (is (= (contract nil-c nil) nil))
  (is (thrown? clojure.lang.ExceptionInfo (contract nil-c 1))))

(deftest seqable-c-test
  (is (= (contract (seqable-c int-c) (list 1 2 3)) (list 1 2 3)))
  (is (thrown? clojure.lang.ExceptionInfo (doall (contract (seqable-c int-c) (list nil 2 3))))))
