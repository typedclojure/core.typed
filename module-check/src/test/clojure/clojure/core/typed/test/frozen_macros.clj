(ns clojure.core.typed.test.frozen-macros
  (:require 
    ; this loads the type system, must go first
    [clojure.core.typed.test.test-utils :as tu]
    [clojure.test :refer :all]
    [clojure.core.typed.analyzer2.pre-analyze :as pre]
    [clojure.core.typed.analyzer2.jvm :as ana]
    [clojure.core.typed.analyze-clj :as ana-clj]
    [clojure.tools.analyzer.passes.jvm.emit-form :refer [emit-form]]
    [clojure.tools.analyzer.jvm :as taj]
    [clojure.tools.analyzer.jvm.utils :as ju]))

(defmacro tc-e [frm & opts]
  `(tu/tc-e ~frm ~@opts
            :ns-meta {:core.typed {:experimental #{:custom-expansions}}}))

(defmacro tc-err [frm & opts]
  `(tu/tc-err ~frm ~@opts
              :ns-meta {:core.typed {:experimental #{:custom-expansions}}}))

(defmacro is-tc-e [& body]
  `(is (do (tc-e ~@body)
           true)))

(defmacro is-tc-err [& body]
  `(is (tc-err ~@body)))

(deftest ns-test
  (is-tc-e (ns foo) nil)
  (is-tc-err (ns foo) Symbol))

(deftest ann-form-test
  (is-tc-e (ann-form 1 Integer))
  ;; blames ann-form form
  ;; FIXME add types in msg
  (is-tc-err (ann-form 1 Integer) nil)
  (is-tc-err (ann-form 1 nil)))

(deftest tc-ignore-test
  (is-tc-e (tc-ignore #(/ nil nil)))
  (is-tc-err (tc-ignore #(/ nil nil)) nil))

(deftest typed-fn-test
  (is-tc-e (fn [a :- (U nil Number)]))
  ;; inherits column from outer expression
  ;; FIXME use entire form if single arity
  (is-tc-err (fn [] :- Number))
  ;; exact column number
  (is-tc-err (fn ([] :- Number))))

(deftest when-test
  (is-tc-e (fn [a :- (U nil Number)]
             (when a (inc a))))
  (is-tc-e (fn [a :- (U nil Number)]
             (when a (inc a))))
  (is-tc-e (fn [a :- Number] :- Number
             (when a (inc a))))
  ;; better error
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when a (inc a))))
  ;; 'else' expected error
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when a 1)))
  ;; 'then+else' expected error
  ; FIXME duplicated error
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when a))))

(deftest when-not-test
  (is-tc-e (fn [a :- (U nil Number)]
             (when-not (not a) (inc a))))
  (is-tc-e (fn [a :- (U nil Number)]
             (when-not (not a) (inc a))))
  (is-tc-e (fn [a :- Number] :- Number
             (when-not (not a) (inc a))))
  ;; better error
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when-not (not a) (inc a))))
  ;; 'then' expected error
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when-not (not a) 1)))
  ;; 'then+else' expected error
  (is-tc-err (fn [a :- (U nil Number)] :- Number,
               (when-not (not a)))))

(deftest let-test
  ;; better error
  (is-tc-err (let [a 1]) Number)
  (is-tc-e (let [a 1]
             (inc a)))
  (is-tc-e #(let [a (throw (Exception.))]
              (/ nil nil)))
  (is-tc-e #(let [a 1
                  b 2]
              (/ a b)))
  (is-tc-e #(let [a (throw (Exception.))
                  b (/ nil nil)]))
  (is-tc-err #(let [a (/ nil nil)
                    b (throw (Exception.))]
                (/ a b)))
  (is-tc-err #(let [a (/ nil nil)]
                (inc a)))
  (is-tc-err #(let [a 1]
                (/ nil nil)))
  ;destructuring
  (is-tc-e (let [{:keys [a]} {:a 1}]
             (inc a)))
  (is-tc-err (let [{:keys [a]} []]
               (inc a)))

  ;; locals shadow vars
  (is-tc-e (let [identity identity]
             (identity 1))))

(deftest when-let-test
  (is-tc-e (when-let [_ 1]
             (inc 1)))
  (is-tc-e (when-let [a 1]
             (inc a)))
  (is-tc-e (when-let [a (ann-form 1 (U nil Number))]
             (inc a)))
  (is-tc-err (when-let [a (ann-form 1 (U nil Number String))]
               (inc a)))
  (is-tc-err (when-let [a "a"]
               (inc a)))
  (is-tc-err (when-let [a (ann-form nil (U nil Number))]
               (inc a))
             Number)
  )

(deftest if-let-test
  (is-tc-e (if-let [_ 1]
             (inc 1)))
  (is-tc-e (if-let [a (ann-form 1 (U nil Number))]
             (inc a)))
  ; improved error
  (is-tc-err (if-let [a (ann-form 1 (U nil Number))]
               (inc a))
             Number)
  (is-tc-e (if-let [{:keys [a]} {:a 1}]
             (inc a)
             1))
  (is-tc-err (if-let [a (ann-form 1 (U nil Number String))]
               (inc a)))
  (is-tc-err (if-let [a "a"]
               (inc a)))
  )

(deftest assert-test
  (binding [*assert* true]
    (is-tc-e #(assert 1)))
  (binding [*assert* true]
    (is-tc-e #(assert 1 "foo")))
  (binding [*assert* false]
    (is-tc-e #(assert (/ nil nil) "foo")))
  (binding [*assert* false]
    (is-tc-e #(assert (/ nil nil "foo"))))
  (is-tc-err #(assert (/ nil) "foo"))
  (is-tc-err #(assert (/ nil nil) "foo"))
  ;; unreachable message
  (is-tc-e #(assert "foo" (/ nil)))
  (is-tc-err #(assert nil (/ nil))))

(deftest with-open-test
	(is-tc-e #(with-open [r (java.io.FileInputStream. "some/dir")] 
              (.available r)))
  ;; better error
  (is-tc-err #(with-open [r (java.io.FileInputStream. "some/dir")])
             [-> Number]))

(deftest fn-test
  (is-tc-e (clojure.core/fn [a]))
  (is-tc-e (clojure.core/fn [a] a))
  (is-tc-e (clojure.core/fn [a]
             {:pre [(-> a identity)]}
             a))
  (is-tc-e (clojure.core/fn [a]
             {:post [(symbol? %)]}
             a))
  ;; approximates line number from outer form
  (is-tc-err (clojure.core/fn [a])
             [Number -> Number])
  ;; exact line number
  (is-tc-err (clojure.core/fn ([a]))
             [Number -> Number])
  )

(deftest for-test
  (is-tc-e #(clojure.core/for [a [1 2]] a))
  (is-tc-e #(clojure.core/for [a [1 2]] a) [-> (Seqable Number)])
  (is-tc-err #(clojure.core/for [a [1 2]] a) [-> (Seqable Boolean)])
  ;; FIXME improve error
  (is-tc-err #(clojure.core/for [a [1 2]] a) [-> Number])
  ;; FIXME improve error
  (is-tc-err #(clojure.core/for [a [1 2]] a) [-> nil])
  (is-tc-e #(clojure.core/for [a [1 2] b [2 3]] [a b]))
  (is-tc-e #(clojure.core/for [a [1 2] b [2 3]] [a b]) [-> (Seq '[Num Num])])
  ;FIXME use t/fn instead of fn*
  ;; propagates expected type to body
  (is-tc-e #(clojure.core/for [a [1 2] b [2 3]] (fn* [c] (+ c a b)))
           [-> (Seq [Num -> Num])])
  ;; example of bad type propagating to body
  (is-tc-err #(clojure.core/for [a [1 2] b [2 3]] (fn* [c] (+ c a b))) [-> (Seq [nil -> Num])])
)

(deftest assoc-in-inline-test
  (is-tc-e (assoc-in {} [:a] 1) '{:a Num})
  ;; improved msg
  (is-tc-err (assoc-in {} [:a :b] 1) '{:a Num})
  ;; improved msg
  (is-tc-err (assoc-in 'a [:a] 1))
  ;; improved msg
  (is-tc-err (assoc-in {:a (ann-form 'a Sym)} [:a :b] 1))
  (is-tc-err (assoc-in {:a {:b (ann-form 'a Sym)}} [:a :b :c] 1))
  (is-tc-err (assoc-in {:a []} [:a :b] 1))
  (is-tc-e (assoc-in {:a []} [:a 0] 1) '{:a '[Num]}))

(deftest get-in-test
  (is-tc-e (get-in {:a {:b 1}} [:a :b])
           Num)
  ; improved error
  (is-tc-err (get-in {:a {:b 1}} [:a :b])
             Sym)
  ;; FIXME need better messages for 'default'
  (is-tc-err (get-in {:a {:b 1}} [:a :b] 1))
  (is-tc-err (get-in {:a {:b 1}} [:a :b] 1)
             Sym))

(deftest update-in-inline-test
  (is-tc-e (update-in {:a {:b 1}} [:a :b] identity)
           '{:a '{:b Num}})
  (is-tc-e (update-in {:a {:b 1 :c 2}} [:a] dissoc :b)
           '{:a '{:c Num}})
  (is-tc-e (let [m {:a {:b {:c 3}}}]
             (update-in m [:a] update-in [:b] update-in [:c] str))
           '{:a '{:b '{:c Str}}})
  ;; error is the second 'update-in' call
  ;; FIXME garbled error
  (is-tc-err (let [m {:a {:b 1}}]
               (update-in m [:a] update-in [:b] update-in [:c] inc)))
  ;; error is (inc "a") call
  ;; FIXME garbled error
  (is-tc-err (let [m {:a {:b {:c "a"}}}]
               (update-in m [:a] update-in [:b] update-in [:c] inc)))
  (is-tc-e (update-in {:a {:b 1}} [:a :b] inc)
           '{:a '{:b Num}})
  (is-tc-e (update-in {:a {:b 1}} [:a :b] str)
           '{:a '{:b Str}})
  (is-tc-err (update-in {:a []} [:a :b] identity))
  (is-tc-err (let [m {:a []}]
               (update-in m [:a :b] identity))))

(deftest map-test
  (is-tc-e (map identity [1 2 3]))
  (is-tc-e (map identity [1 2 3])
           (t/Seq t/Num))
  (is-tc-err (map identity [1 2 3])
             (t/Seq t/Bool))
  ;; FIXME better column number
  (is-tc-err (map identity 'a))

  ;               ;vvvvvvvvvvvvvv
  ;; (map identity ('a asdlfsdf
  ;;                 ;lsdl;fsdlf) 
  ;;              ;^^^^^^^^^^^^^^
  ;;      :a :b)
  ;               ;vv
  ;; (map identity 'a
  ;;              ;^^
  ;;      :a :b)

  (is-tc-e (map identity)
					 (t/Transducer t/Num t/Num))
  (is-tc-e (map boolean)
					 (t/Transducer t/Num t/Bool))
  ;; FIXME better error needed
  (is-tc-err (map boolean)
             (t/Transducer t/Bool t/Num))
)

(deftest ->-test
  (is-tc-e (-> identity
               (map [1 2 3])))
  (is-tc-err (-> identity
                 (map [1 2 3]))
             (t/Seq t/Bool))
  ; FIXME big error
  (is-tc-err (-> identity
                 (map [1 2 3])
                 (map [1 2 3]))
             (t/Seq t/Bool))
  ; FIXME line number
  (is-tc-err (-> identity
                 (map [1 2 3])
                 vec)
             (t/Seq t/Bool)))

(comment
  (defn timet
    [expr]
    (let [start (. System (nanoTime))
          ret (expr)]
      (/ (double (- (. System (nanoTime)) start)) 1000000.0)))

  (clojure.pprint/pprint
  (sort-by val
           (into {} (map (fn [v]
                           [v (timet #(clojure.test/test-vars [v]))]))
                 (filter (every-pred var? (comp :test meta)) (vals (ns-publics *ns*)))))
  )
; no custom expansion
	'([#'clojure.core.typed.test.frozen-macros/tc-ignore-test 171.394456]
		[#'clojure.core.typed.test.frozen-macros/with-open-test 181.161775]
		[#'clojure.core.typed.test.frozen-macros/typed-fn-test 233.531726]
		[#'clojure.core.typed.test.frozen-macros/ann-form-test 235.352863]
		[#'clojure.core.typed.test.frozen-macros/ns-test 240.44296]
		[#'clojure.core.typed.test.frozen-macros/get-in-test 341.253694]
		[#'clojure.core.typed.test.frozen-macros/fn-test 495.774091]
		[#'clojure.core.typed.test.frozen-macros/when-not-test 542.922632]
		[#'clojure.core.typed.test.frozen-macros/when-test 546.166276]
		[#'clojure.core.typed.test.frozen-macros/when-let-test 609.879237]
		[#'clojure.core.typed.test.frozen-macros/if-let-test 631.63356]
		[#'clojure.core.typed.test.frozen-macros/assoc-in-inline-test 676.056304]
		[#'clojure.core.typed.test.frozen-macros/assert-test 694.094945]
		[#'clojure.core.typed.test.frozen-macros/update-in-inline-test 765.674776]
		[#'clojure.core.typed.test.frozen-macros/let-test 992.088318]
		[#'clojure.core.typed.test.frozen-macros/for-test 5778.336702])
; yes custom expansion
'([#'clojure.core.typed.test.frozen-macros/ns-test 182.167286]
	[#'clojure.core.typed.test.frozen-macros/tc-ignore-test 188.358344]
	[#'clojure.core.typed.test.frozen-macros/with-open-test 221.02634]
	[#'clojure.core.typed.test.frozen-macros/ann-form-test 274.636581]
	[#'clojure.core.typed.test.frozen-macros/typed-fn-test 330.160597]
	[#'clojure.core.typed.test.frozen-macros/get-in-test 388.410054]
	[#'clojure.core.typed.test.frozen-macros/fn-test 682.037165]
	[#'clojure.core.typed.test.frozen-macros/assert-test 774.38307]
	[#'clojure.core.typed.test.frozen-macros/if-let-test 793.200128]
	[#'clojure.core.typed.test.frozen-macros/when-not-test 807.979324]
	[#'clojure.core.typed.test.frozen-macros/when-let-test 816.350961]
	[#'clojure.core.typed.test.frozen-macros/for-test 819.305905]
	[#'clojure.core.typed.test.frozen-macros/assoc-in-inline-test 820.942907]
	[#'clojure.core.typed.test.frozen-macros/when-test 865.453885]
	[#'clojure.core.typed.test.frozen-macros/let-test 1221.219269]
	[#'clojure.core.typed.test.frozen-macros/update-in-inline-test 1641.337323])

)
