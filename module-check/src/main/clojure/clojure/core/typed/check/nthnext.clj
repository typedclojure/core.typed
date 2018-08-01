(ns ^:skip-wiki clojure.core.typed.check.nthnext
  (:require [clojure.core.typed.utils :as u]
            [clojure.core.typed.type-ctors :as c]
            [clojure.core.typed.type-rep :as r]
            [clojure.core.typed :as t]
            [clojure.core.typed.filter-ops :as fo]
            [clojure.core.typed.indirect-ops :as ind]
            [clojure.core.typed.cs-gen :as cgen]
            [clojure.core.typed.errors :as err]
            [clojure.core.typed.check.utils :as cu]))

(defn drop-HSequential
  "Drop n elements from HSequential t."
  [n t]
  {:pre [(nat-int? n)
         (r/HSequential? t)]
   :post [(r/Type? %)]}
  (let [shift (fn [k]
                {:pre [(keyword? k)]
                 :post [(vector? %)]}
                (let [e (k t)]
                  (if (:repeat t)
                    (vec (take (count e)
                               (nthrest (cycle e) n)))
                    (vec (nthrest e n)))))]
    (r/-hseq (shift :types)
             :filters (shift :fs)
             :objects (shift :objects)
             :rest (:rest t)
             :drest (:drest t)
             :repeat (:repeat t))))

(defn nthnext-hsequential [t n]
  {:pre [(r/HSequential? t)
         (nat-int? n)]
   :post [(r/Type? %)]}
  (let [res (drop-HSequential n t)]
    (cond
      (or (:rest res)
          (:drest res)
          (:repeat res))
      (c/Un r/-nil res)

      (empty? (:types res)) r/-nil
      :else res)))

(defn nthrest-hsequential [t n]
  {:pre [(r/HSequential? t)
         (nat-int? n)]
   :post [(r/Type? %)]}
  (drop-HSequential n t))

(defn nthrest-type [t n]
  {:pre [(r/Type? t)
         (nat-int? n)]
   :post [((some-fn nil? r/Type?) %)]}
  (if (zero? n)
    t
    (let [t (c/fully-resolve-type t)]
      (cond
        (r/Union? t) (let [ts (map #(nthrest-type % n) (:types t))]
                       (when (every? identity ts)
                         (apply c/Un ts)))
        (r/Intersection? t) (when-let [ts (seq (keep #(nthrest-type % n) (:types t)))]
                              (apply c/In ts))
        (r/Nil? t) (r/-hseq [])
        (r/HSequential? t) (nthrest-hsequential t n)
        :else (when-let [res (cgen/unify-or-nil
                               {:fresh [x]
                                :out x}
                               t
                               (c/Un r/-nil (c/-name `t/Seqable x)))]
                (c/-name `t/Seq res))))))

(defn nthnext-type [t n]
  {:pre [(r/Type? t)
         (nat-int? n)]
   :post [((some-fn nil? r/Type?) %)]}
  (let [t (c/fully-resolve-type t)]
    (cond
      (r/Union? t) (let [ts (map #(nthnext-type % n) (:types t))]
                     (when (every? identity ts)
                       (apply c/Un ts)))
      (r/Intersection? t) (when-let [ts (seq (keep #(nthnext-type % n) (:types t)))]
                            (apply c/In ts))
      (r/Nil? t) r/-nil
      (r/HSequential? t) (nthnext-hsequential t n)
      :else (when-let [res (cgen/unify-or-nil
                             {:fresh [x]
                              :out x}
                             t
                             (c/Un r/-nil (c/-name `t/Seqable x)))]
              (c/-name `t/NilableNonEmptySeq res)))))

(defn seq-type [t]
  {:pre [(r/Type? t)]
   :post [((some-fn nil? r/Type?) %)]}
  (nthnext-type t 0))

(defn check-specific-rest [check-fn {:keys [args] :as expr} expected
                           & {:keys [cargs nrests nargs
                                     target-t]}]
  {:pre [(integer? nrests)
         (vector? cargs)
         (integer? nargs)
         ((some-fn r/Type? nil?) target-t)]}
  (if-not (#{nargs} (count cargs))
    cu/not-special
    (if-let [t (nthrest-type target-t nrests)]
      (-> expr
          (update-in [:fn] check-fn)
          (assoc
            :args cargs
            u/expr-type (r/ret t (fo/-true-filter))))
      cu/not-special)))

(defn check-specific-next [check-fn {:keys [args] :as expr} expected
                           & {:keys [cargs nnexts nargs
                                     target-t]}]
  {:pre [(integer? nnexts)
         (vector? cargs)
         (integer? nargs)
         ((some-fn r/Type? nil?) target-t)]}
  (if-not (#{nargs} (count cargs))
    cu/not-special
    (if-let [t (nthnext-type target-t nnexts)]
      (-> expr
          (update-in [:fn] check-fn)
          (assoc
            :args cargs
            u/expr-type (r/ret t
                               (cond
                                 (ind/subtype? t r/-nil) (fo/-false-filter)
                                 (not (ind/subtype? r/-nil t)) (fo/-true-filter)
                                 :else (fo/-simple-filter)))))
      cu/not-special)))

(defn check-nthnext [check-fn {:keys [args] :as expr} expected & {:keys [cargs]}]
  (assert (vector? cargs))
  (if-not (#{2} (count cargs))
    cu/not-special
    (let [[ctarget cn :as cargs] cargs
          target-t (c/fully-resolve-type (-> ctarget u/expr-type r/ret-t))
          num-t (-> cn u/expr-type r/ret-t)]
      (if (and (r/Value? num-t)
               (integer? (:val num-t)))
        (check-specific-next
          check-fn expr expected
          :nnexts (:val num-t) 
          :nargs 2
          :target-t (r/ret-t (u/expr-type ctarget))
          :cargs cargs)
        cu/not-special))))

(defn check-next [check-fn {:keys [args] :as expr} expected & {:keys [cargs]}]
  (assert (vector? cargs))
  (check-specific-next check-fn expr expected 
                       :nnexts 1 
                       :nargs 1 
                       :target-t (when (seq cargs)
                                   (r/ret-t (u/expr-type (first cargs))))
                       :cargs cargs))

(defn check-seq [check-fn {:keys [args] :as expr} expected & {:keys [cargs]}]
  (assert (vector? cargs))
  (check-specific-next check-fn expr expected 
                       :nnexts 0
                       :nargs 1
                       :target-t (when (seq cargs)
                                   (r/ret-t (u/expr-type (first cargs))))
                       :cargs cargs))

(defn check-rest [check-fn {:keys [args] :as expr} expected & {:keys [cargs]}]
  (assert (vector? cargs))
  (check-specific-rest check-fn expr expected 
                       :nrests 1 
                       :nargs 1 
                       :target-t (when (seq cargs)
                                   (r/ret-t (u/expr-type (first cargs))))
                       :cargs cargs))
