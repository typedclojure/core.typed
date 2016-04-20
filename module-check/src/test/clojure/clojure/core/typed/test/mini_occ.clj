(ns clojure.core.typed.test.mini-occ
  {:lang :core.typed
   :core.typed {:features #{:runtime-infer}}
   }
  (:require [clojure.test :refer [deftest is]]
            [clojure.core.typed :as t]))

;;  e  ::= x | (if e e e) | (lambda (x :- t) e) | (e e*) | #f | n? | add1
;;  t  ::= [x : t -> t] | (not t) | (or t t) | (and t t) | #f | N | (refine [x] p) | Any
;;  p  ::= (is e t) | (not p) | (or p p) | (and p p) | (= e e)
;;  ps ::= p*

#_
(defalias E
  "Expressions"
  (U '{:E :var, :name Sym}
     '{:E :if, :test E, :then E, :else E}
     '{:E :lambda, :arg Sym, :arg-type T, :body E}
     '{:E :app, :fun E, :args (Vec E)}
     '{:E :false}
     '{:E :n?}
     '{:E :add1}))
#_
(defalias T
  "Types"
  (U '{:T :fun, :params (Vec '{:name Sym :type T}), :return T}
     '{:T :not, :type T}
     '{:T :union, :types (Set T)}
     '{:T :intersection, :types (Set T)}
     '{:T :false}
     '{:T :num}
     '{:T :refine, :name Sym, :prop P}))
#_
(defalias P
  "Propositions"
  (U '{:P :is, :exp E, :type T}
     '{:P :=, :exps (Set E)}
     '{:P :or, :ps (Set P)}
     '{:P :and, :ps (Set P)}
     '{:P :not, :p P}))
#_
(defalias Ps
  "Proposition environments"
  (Set P))

;n? : [x :- Any -> (is (n? x) Int)]
;+  : [x :- Int, y : Int -> Int]

#_(tc (lambda (x)
      (if (n? x)
        (add1 x)
        x)))

; ps p -> List List ass
(defn prove [ps p]
  )

(declare parse-exp parse-type)

; Any -> P
(defn parse-prop [p]
  (assert (list? p) p)
  (case (first p)
    is (let [[_ e t] p]
         {:P :is
          :exp (parse-exp e)
          :type (parse-type t)})
    = (let [[_ & es] p]
        {:P :=
         :exps (set (map parse-exp es))})
    or (let [[_ & ps] p]
         {:P :or
          :ps (set (map parse-prop ps))})
    and (let [[_ & ps] p]
          {:P :and
           :ps (set (map parse-prop ps))})
    not (let [[_ np] p]
          {:P :not
           :p (parse-prop np)})))

(deftest parse-prop-test
  (is (= (parse-prop '(is x Any))
         {:P :is, 
          :exp {:name 'x, :E :var}, 
          :type {:T :intersection, :types #{}}}))
  (is (= (parse-prop '(= (x y) z))
         '{:P :=, :exps #{{:name z, :E :var} 
                          {:args [{:name y, :E :var}], :fun {:name x, :E :var}, :E :app}}}))
  (is (= (parse-prop '(or (= (x y) z)
                          (is x Any)))
         '{:P :or, 
           :ps #{{:P :=, :exps #{{:name z, :E :var} {:args [{:name y, :E :var}], :fun {:name x, :E :var}, :E :app}}} 
                 {:exp {:name x, :E :var}, :P :is, :type {:T :intersection, :types #{}}}}}))
  (is (= (parse-prop '(and (= (x y) z)
                           (is x Any)))
         '{:P :and, 
           :ps #{{:P :=, :exps #{{:name z, :E :var} {:args [{:name y, :E :var}], :fun {:name x, :E :var}, :E :app}}} 
                 {:exp {:name x, :E :var}, :P :is, :type {:T :intersection, :types #{}}}}}
         ))
  (is (= (parse-prop '(not (= (x y) z)))
         '{:P :not, 
           :p {:P :=, :exps #{{:name z, :E :var} {:args [{:name y, :E :var}], :fun {:name x, :E :var}, :E :app}}}}))
  )

(declare unparse-exp unparse-type)

; P -> Any
(defn unparse-prop [p]
  {:pre [(contains? p :P)]}
  (case (:P p)
    :is `(~'is ~(unparse-exp (:exp p))
               ~(unparse-type (:type p)))
    := `(~'= ~@(map unparse-exp (:exps p)))
    :or `(~'or ~@(map unparse-prop (:ps p)))
    :and `(~'and ~@(map unparse-prop (:ps p)))
    :not `(~'not ~(unparse-prop (:p p)))))

(deftest unparse-prop-test
  (is (unparse-prop (parse-prop '(is x Any))))
  (is (unparse-prop (parse-prop '(= (x y) z))))
  (is (unparse-prop (parse-prop '(or (= (x y) z)
                                     (is x Any)))))
  (is (unparse-prop (parse-prop '(and (= (x y) z)
                                      (is x Any)))))
  (is (unparse-prop (parse-prop '(not (= (x y) z))))))

; Any -> T
(defn parse-type [t]
  (cond
    (vector? t) (let [[args [_ ret]] (split-at (- (count t) 2) t)
                      args (map (fn [[x _ t]]
                                  {:name x 
                                   :type (parse-type t)})
                                (partition 3 args))]
                  (assert (#{'->} (get t (- (count t) 2)))
                          (get t (- (count t) 2)))
                  {:T :fun
                   :params (vec args)
                   :return (parse-type ret)})
    (list? t) (case (first t)
                not (let [[_ t1] t]
                      {:T :not
                       :type (parse-type t)})
                or (let [[_ & ts] t]
                      {:T :union
                       :types (set (map parse-type ts))})
                and (let [[_ & ts] t]
                      {:T :intersection
                       :types (set (map parse-type ts))})
                refine (let [[_ [x] p] t]
                         (assert (symbol? x))
                         {:T :refine
                          :name x
                          :prop (parse-prop t)}))
    (false? t) {:T :false}
    ('#{Num} t) {:T :num}
    ('#{Any} t) {:T :intersection :types #{}}
    :else (assert false t)))

(defn unparse-type [t]
  {:pre [(contains? t :T)]}
  (case (:T t)
    :fun `[~@(mapcat (fn [{:keys [name type]}]
                       [name :- (unparse-type type)])
                     (:params t))
           ~'->
           ~(unparse-type (:return t))]
    :not `(~'not (unparse-type (:type t)))
    :union `(~'or ~@(map unparse-type (:types t)))
    :intersection (if (zero? (count (:types t)))
                    'Any
                    `(~'and ~@(map unparse-type (:types t))))
    :false false
    :num 'Num
    :refine `(~'refine [~(:name t)]
                       ~(unparse-prop (:prop t)))))

; parse-exp : Any -> E
(defn parse-exp [e]
  (cond
    (symbol? e) {:E :var, :name e}
    (false? e)  {:E :false}
    (= 'n? e)   {:E :n?}
    (= 'add1 e) {:E :add1}
    (list? e) (case (first e)
                if (let [[_ e1 e2 e3] e]
                     (assert (= 4 (count e)))
                     {:E :if 
                      :test (parse-exp e1)
                      :then (parse-exp e2)
                      :else (parse-exp e3)})
                lambda (let [[_ [x _ t :as param] b] e]
                         (assert (= 3 (count e)))
                         (assert (= 3 (count param)))
                         (assert (symbol? x))
                         {:E :lambda
                          :arg x
                          :arg-type (parse-type t)
                          :body (parse-exp b)})
                (let [[f & args] e]
                  (assert (<= 1 (count e)))
                  {:E :app
                   :fun (parse-exp f)
                   :args (mapv parse-exp args)}))
    :else (assert false e)))

(deftest parse-exp-test
  (is (= (parse-exp 'x)
         '{:name x, :E :var}))
  (is (= (parse-exp '(lambda (x :- Any) x))
         '{:E :lambda, 
           :arg x, 
           :body {:name x, :E :var}, 
           :arg-type {:T :intersection, :types #{}}}))
  (is (= (parse-exp '(if x y z))
         '{:E :if, 
           :test {:name x, :E :var},
           :then {:name y, :E :var}, 
           :else {:name z, :E :var}}))
  (is (= (parse-exp '(x y z))
         '{:E :app,
           :fun {:name x, :E :var}, 
           :args [{:name y, :E :var} {:name z, :E :var}]}))
  (is (= (parse-exp 'false)
         {:E :false}))
  (is (= (parse-exp 'add1)
         '{:name add1, :E :var}
         ))
  )

; E -> Any
(defn unparse-exp [e]
  {:pre [(:E e)]}
  (case (:E e)
    :var (:name e)
    :if `(~'if ~(unparse-exp (:test e))
           ~(unparse-exp (:then e))
           ~(unparse-exp (:else e)))
    :lambda `(~'lambda (~(:arg e) :- ~(unparse-type (:arg-type e)))
               ~(unparse-exp (:body e)))
    :app `(~(unparse-exp (:fun e))
                         ~@(map unparse-exp (:args e)))
    :false false
    :n? 'n?
    :add1 'add1
    (throw (Exception. (str "No matching clause: " (pr-str (:E e)))))))

; eval-exp : E -> Any
#_
(defn eval-exp [e]
  (case))

; tc : Ps E -> T
(defn check [ps e]
  {:pre [(set? ps)
         (every? :P ps)
         (:E e)]
   :post [(:T %)]}
  (case (:E e)
    :false {:T :false}
    :lambda {:T :fun
             :params [{:name (:arg e), :type (:arg-type e)}]
             :return (check (conj ps {:P :is, :exp (:arg e), :type (:arg-type e)})
                            (:body e))}
    :add1   (parse-type '[x :- Num -> Num])
    :n?     (parse-type '[x :- Any -> (refine [r]
                                              (or (and (is r true)
                                                       (is x Num))
                                                  (and (is r false)
                                                       (is x (not Num)))))])
    :app    (let [[e1 e2] e
                  t1 (check ps e1)
                  t2 (check ps e2)]
              (assert (#{:fun} (:T t1)) t1)
              ;; TODO check argument
              (assert false)
              {:T :intersection}
                            )))
;    ))
    ;:var (prove ps {:P :is, :exp e, :type t})

; Any Any -> Any
(defn tc [ps e]
  (->
    (check (into #{} (map parse-prop ps))
           (parse-exp e))
    unparse-type))

(deftest tc-test
  (is (= false
         (tc [] false)))
  #_(is (= false
         (tc [] '(lambda (x :- Num) (add1 x))))))

