(ns clojure.core.typed.array-ops
  (:require [clojure.core.typed.type-rep :as r]
            [clojure.core.typed.type-ctors :as c]))

;Return a Class that generalises what this Clojure type will look like from Java,
;suitable  for use as a Java primitive array member type.
; 
; (Type->array-member-Class (parse-type 'nil)) => Object
; (Type->array-member-Class (parse-type '(U nil Number))) => Number
; (Type->array-member-Class (parse-type '(Array (U nil Number)))) =~> (Array Number)

;(ann Type->array-member-Class (Fn [Type -> (Option Class)]
;                                  [Type t/Any -> (Option Class)]))
(defn Type->array-member-Class 
  ([ty] (Type->array-member-Class ty false))
  ([ty nilok?]
   {:pre [(r/Type? ty)]}
   (cond
     (c/requires-resolving? ty) (Type->array-member-Class (c/-resolve ty) nilok?)
     (r/Nil? ty) (if nilok?
                 nil
                 Object)
     (r/Value? ty) (c/Value->Class ty)
     ;; handles most common case of (U nil Type)
     (r/Union? ty) (let [clss (map #(Type->array-member-Class % true) (:types ty))
                         prim-and-nil? (and (some nil? clss)
                                            (some #(when % (.isPrimitive ^Class %)) clss))
                         nonil-clss (remove nil? clss)]
                     (if (and (= 1 (count nonil-clss))
                              (not prim-and-nil?))
                       (first nonil-clss)
                       Object))
     (r/Intersection? ty) Object
     (r/RClass? ty) (r/RClass->Class ty)
     (r/PrimitiveArray? ty) (class (make-array (Type->array-member-Class (:jtype ty) false) 0))
     :else Object)))

