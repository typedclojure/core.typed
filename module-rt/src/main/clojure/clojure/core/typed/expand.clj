(ns clojure.core.typed.expand
  "Rewriting rules for custom expansions and undoing those
  custom expansions (\"unexpansions\"), mainly to improve type checking
  error messages."
  (:require [clojure.core.typed :as t]
            [clojure.core.typed.internal :as internal]))

(defmulti -expand-macro (fn [form {:keys [vsym]}] vsym))
(defmulti -unexpand-macro (fn [form {:keys [vsym]}] vsym))

(def expand-macro -expand-macro)
(defn unexpand-macro [form {:keys [original-form] :as opts}]
  (let [out (-unexpand-macro form opts)]
    (vary-meta out #(merge (meta original-form) %))))

(defn do-form? [b]
  (and (seq? b) (= 'do (first b))))

;; preserves empty bodies like (let []), even if
;; they are expanded to (do nil), preventing (let [] nil)
(defn splice-body-forms [original-body new-do-body]
  (assert (do-form? new-do-body) (pr-str new-do-body))
  (when (seq original-body) (rest new-do-body)))

(defn splice-checked-body-forms
  [[_check-if-empty-body_ new-do-body {:keys [original-body]} :as checked-body]]
  {:pre [(= 3 (count checked-body))]}
  (splice-body-forms original-body new-do-body))

(defmacro check-let-destructure [{:keys [expression]}] expression)
(defmacro check-let-destructure-no-op [_] nil)

(defn expand-ann-form
  [[_ e ty :as form] _]
  e)

(defn unexpand-ann-form
  [e {[mop _ ty] :original-form}]
  (list mop e ty))

(defmethod -expand-macro 'clojure.core.typed/ann-form [& args] (apply expand-ann-form args))
(defmethod -expand-macro 'clojure.core.typed.macros/ann-form [& args] (apply expand-ann-form args))
(defmethod -unexpand-macro 'clojure.core.typed/ann-form [& args] (apply unexpand-ann-form args))
(defmethod -unexpand-macro 'clojure.core.typed.macros/ann-form [& args] (apply unexpand-ann-form args))

(defn expand-tc-ignore
  [[_ & body] _]
  `(do ~@body))

(defn unexpand-tc-ignore
  [[_do_ & body] {[mop & _] :original-form}]
  {:pre [(= 'do _do_)]}
  (list* mop body))

(defmethod -expand-macro 'clojure.core.typed/tc-ignore [& args] (apply expand-tc-ignore args))
(defmethod -expand-macro 'clojure.core.typed.macros/tc-ignore [& args] (apply expand-tc-ignore args))
(defmethod -unexpand-macro 'clojure.core.typed/tc-ignore [& args] (apply unexpand-tc-ignore args))
(defmethod -unexpand-macro 'clojure.core.typed.macros/tc-ignore [& args] (apply unexpand-tc-ignore args))

(defmethod -expand-macro `check-let-destructure [[_ {:keys [expression]} :as form] _] expression)
(defmethod -unexpand-macro `check-let-destructure [expression {[mop opts] :original-form}] (list mop (assoc opts :expression expression)))

(defmethod -expand-macro `check-let-destructure-no-op [_ _] nil)
(defmethod -unexpand-macro `check-let-destructure-no-op [_ {:keys [original-form]}] original-form)

(def clojure-core-let-expansions
  {:plain {:expand-macro 
           (fn [[_ bindings-form & body-forms :as form] _]
             (let [gs (gensym "b")]
               (reduce
                 (fn [form [expression binding]]
                   `(let* [~gs ~expression
                           ~@(destructure [binding gs])]
                      ~form))
                 [`(do ~@body-forms)]
                 (partition 2 (rseq bindings-form)))))
           :unexpand-macro
           (fn [[_ bindings-form & body-forms :as form] {:keys [original-form]}]
             (let [bindings (loop [original-bindings (second original-form)
                                   form form
                                   bindings []]
                              (if (empty? original-bindings)
                                bindings
                                (let [[binding _ & original-bindings] original-bindings
                                      [_let*_ [_gs_ expression & _dstruct_] form] form]
                                  (recur original-bindings
                                         form
                                         (conj bindings-form binding expression)))))
                   [_ _ & original-body] original-form]
               (list* (first original-form)
                      bindings
                      (splice-body-forms original-body (list* 'do body-forms)))))}
   :typed {:expand-macro 
           (fn [[_ bindings-form & body-forms :as form] _]
             (let [gs (gensym "b")]
               (reduce
                 (fn [form [expression binding]]
                   `(let* [~gs ^::t/freeze (check-let-destructure
                                           {:binding ~binding
                                            :expression ~expression})
                           ~@(destructure [binding gs])]
                      ~form))
                 `^::t/freeze
                 (check-if-empty-body
                    (do ~@body-forms)
                    {:msg-fn (fn [_#]
                               "This 'let' expression returns nil with an empty body, which does not agree with the expected type")
                     :blame-form ~form
                     :original-body ~body-forms})
                 (partition 2 (rseq bindings-form)))))
           :unexpand-macro
           (fn [form {:keys [original-form]}]
             ;(prn "start of let :unexpand-macro" form original-form)
             (let [[mop original-bindings & original-body] original-form
                   ;_ (prn "original-body" original-body)
                   [bindings body] (loop [original-bindings original-bindings
                                          form form
                                          bindings []]
                                     ;(prn "form" form)
                                     (if (empty? original-bindings)
                                       [bindings form]
                                       (let [[_ _ & original-bindings] original-bindings
                                             [_let*_ [_gs_ [_check-let-destructure_ {:keys [binding expression]}] & _dstruct_] form] form]
                                         (recur original-bindings
                                                form
                                                (conj bindings binding expression)))))]
               ;(prn "end of let :unexpand-macro" body)
               (list* (first original-form)
                      bindings
                      (splice-checked-body-forms body))))}})

(defmethod -expand-macro 'clojure.core/let
  [& args]
  (apply (-> clojure-core-let-expansions :typed :expand-macro) args))

(defmethod -unexpand-macro 'clojure.core/let
  [& args]
  (apply (-> clojure-core-let-expansions :typed :unexpand-macro) args))

(defmacro check-if-empty-body [e opts]
  e)

(defmethod -expand-macro `check-if-empty-body
  [[_ e {:keys [msg blame-form]} :as form] {{:keys [expected]} :clojure.core.typed/type-opts}]
  e)

(defmethod -unexpand-macro `check-if-empty-body
  [e {[mop _ opt] :original-form}]
  (list mop e opt))

(defmacro check-expected [e opts]
  e)

(defmethod -expand-macro `check-expected
  [[_ e {:keys [msg blame-form]} :as form] {{:keys [expected]} :clojure.core.typed/type-opts}]
  e)

(defmethod -unexpand-macro `check-expected
  [e {[mop _ opt] :original-form}]
  (list mop e opt))

(defmethod -expand-macro 'clojure.core/when
  [[_ test & bodys :as form] _]
  `(if ~test
     ^::t/freeze
     (check-if-empty-body
       (do ~@bodys)
       {:msg-fn (fn [_#]
                  "This 'when' expression returns nil if the test is true, which does not agree with the expected type.")
        :blame-form ~form
        :original-body ~bodys})
     ^::t/freeze
     (check-expected
       nil
       {:msg-fn (fn [_#]
                  "This 'when' expression returns nil if the test is false, which does not agree with the expected type.")
        :blame-form ~form})))

(defmethod -unexpand-macro 'clojure.core/when
  [[_if_ test then-checked-body :as form]
   {[mop _ & original-bodys :as original-form] :original-form}]
  (list* mop test (splice-checked-body-forms then-checked-body)))

(defmethod -expand-macro 'clojure.core/when-not
  [[_ test & bodys :as form] _]
  `(if ~test
     ^::t/freeze
     (check-expected
       nil
       {:msg-fn (fn [_#]
                  "This 'when-not' expression returns nil if the test is true, which does not agree with the expected type.")
        :blame-form ~form})
     ^::t/freeze
     (check-if-empty-body
       (do ~@bodys)
       {:msg-fn (fn [_#]
                  "This 'when-not' expression returns nil if the test is false, which does not agree with the expected type.")
        :blame-form ~form
        :original-body ~bodys})))

(defmethod -unexpand-macro 'clojure.core/when-not
  [[_if_ test _ else-checked-body :as form]
   {[mop _ & original-bodys :as original-form] :original-form}]
  (list* mop test (splice-checked-body-forms else-checked-body)))

(defmethod -expand-macro 'clojure.core/if-let
  [[_ bindings then else :as original-form] _]
	(let [form (bindings 0) tst (bindings 1)]
		`^::t/freeze
     (let [temp# ~tst]
			 (if temp#
				 ^::t/freeze
         (let [_# ^::t/freeze (check-let-destructure-no-op
                              {:binding ~form
                               :expression ~tst})
               ;TODO avoid repeated destructuring checks ^::no-check-destructure
               ~form temp#]
					 ~then)
         ~(if (= 3 (count original-form))
            `^::t/freeze
            (check-expected
               nil
               {:msg-fn (fn [_#]
                          "This 'if-let' expression returns nil if the test is false, which does not agree with the expected type.")
                :blame-form ~original-form})
            else)))))

(defmethod -unexpand-macro 'clojure.core/if-let
  [form {:keys [original-form]}]
	(let [[_let_ [_tmp_ tst]
         [_if _tmp
          [_let_ [_ _no-op_ binding _tmp_]
           then]
          else]]
        form
        [mop] original-form]
    (list* mop [binding tst] then
           (when (= 4 (count original-form))
             [else]))))

(defmethod -expand-macro 'clojure.core/when-let
  [[_ test & bodys :as form] _]
  ^::t/freeze
  `(if-let ~test
     ^::t/freeze
     (check-if-empty-body
       (do ~@bodys)
       {:msg-fn (fn [_#]
                  "This 'when-let' expression returns nil if the test is true, which does not agree with the expected type.")
        :blame-form ~form
        :original-body ~bodys})
     ^::t/freeze
     (check-expected
       nil
       {:msg-fn (fn [_#]
                  "This 'when-let' expression returns nil if the test is false, which does not agree with the expected type.")
        :blame-form ~form})))

(defmethod -unexpand-macro 'clojure.core/when-let
  [[_if-let_ test then-checked-body :as form]
   {[mop] :original-form}]
  (list* mop test (splice-checked-body-forms then-checked-body)))

(defmethod -expand-macro 'clojure.core/with-open
  [[_ bindings & body :as form] _]
	(let [expand-with-open (fn expand-with-open [bindings body]
                           (cond
                             (= (count bindings) 0) `^::t/freeze (check-if-empty-body
                                                                 (do ~@body)
                                                                 {:msg-fn (fn [_#]
                                                                            (str "This 'with-open' expression returns nil, "
                                                                                 "which does not agree with the expected type."))
                                                                  :blame-form ~form
                                                                  :original-body ~body})
                             (symbol? (bindings 0)) `^:freeze (let ~(subvec bindings 0 2)
                                                                (try
                                                                  ~(expand-with-open (subvec bindings 2) body)
                                                                  (finally
                                                                    (. ~(bindings 0) close))))
                             :else (throw (IllegalArgumentException. "with-open only allows Symbols in bindings"))))]
    (expand-with-open bindings body)))

(defmethod -unexpand-macro 'clojure.core/with-open
  [form {[mop original-bindings & original-body] :original-form}]
  (let [[bindings body] (loop [bindings-left (/ (count original-bindings) 2)
                               form form
                               bindings []]
                          (if (zero? bindings-left)
                            [bindings form]
                            (let [[_let_ [binding expression]
                                   [_try form]] form]
                              (recur (dec bindings-left)
                                     form
                                     (conj bindings binding expression)))))]
    (list* mop bindings (splice-checked-body-forms body))))

(defmethod -expand-macro 'clojure.core/assert
  [[_ x message :as form] _]
	(let [msg? (= 3 (count form))
        erase-assert? (not *assert*)
        assert-expand (fn
                        ([x]
                         (when-not erase-assert?
													 `^::t/freeze
                            (when-not ~x
                              (throw (new AssertionError (str "Assert failed: " (pr-str '~x)))))))
                        ([x message]
                         (when-not erase-assert?
													 `^::t/freeze
                            (when-not ~x
                              (throw (new AssertionError (str "Assert failed: " ~message "\n" (pr-str '~x))))))))]
		(apply assert-expand (rest form))))

(defmethod -unexpand-macro 'clojure.core/assert
  [form {:keys [original-form]}]
	(if (some? form)
    (let [msg? (= 3 (count original-form))
          [mop] original-form]
      (if msg?
        (let [[_when-not_ x [_throw_ [_new _AssertionError_ [_str_ _ message]]]] form]
          (list mop x message))
        (let [[_when-not_ x] form]
          (list mop x))))
    original-form))

(defn parse-fn-sigs [sigs]
	(let [name (if (symbol? (first sigs)) (first sigs) nil)
				sigs (if name (next sigs) sigs)
        single-arity-syntax? (vector? (first sigs))
				sigs (if (vector? (first sigs))
							 (list sigs)
							 (if (seq? (first sigs))
								 sigs
								 ;; Assume single arity syntax
								 (throw (IllegalArgumentException.
													(if (seq sigs)
														(str "Parameter declaration "
																 (first sigs)
																 " should be a vector")
														(str "Parameter declaration missing"))))))
        process-sigs (fn [[params & body :as sig]]
                       (assert (vector? params) params)
                       (let [conds (when (and (next body) (map? (first body)))
                                     (first body))
                             body (if conds (next body) body)
                             conds-from-params-meta? (not conds)
                             conds (or conds (meta params))
                             pre (:pre conds)
                             post (:post conds)]
                         {;; inherit positional information from params
                          :sig-form (with-meta sig (meta params))
                          :pre pre
                          :post post
                          :conds-from-params-meta? conds
                          :params params
                          :body body}))]
    {:single-arity-syntax? single-arity-syntax?
     :sigs (mapv process-sigs sigs)
     :name name}))

(defmethod -unexpand-macro 'clojure.core/fn
  [[_fn*_ & sigs] {:keys [original-form]}]
  (let [name (let [s (first sigs)]
               (when (symbol? s)
                 s))
        sigs (if (symbol? name) (next sigs) sigs)
        {original-sigs :sigs, :keys [single-arity-syntax?]} (parse-fn-sigs (next original-form))
        unexpand-sig (fn [[params [_let_ dbindings & body]] old-sig]
                       {:pre [(map? old-sig)]}
                       (let [rest-arg? (boolean
                                         (when (<= 2 (count params))
                                           (= '& (nth params (- count 2)))))
                             [dbindings rst-dparam] (if rest-arg?
                                                      [(-> dbindings pop pop) (peek dbindings)]
                                                      [dbindings nil])
                             fixed-dparams (mapv first (partition 2 dbindings))
                             [asserts body] ((juxt pop peek) (vec body))
                             exp-pre (when (:pre old-sig)
                                       (mapv second asserts))
                             _ (assert (= (count (:pre old-sig))
                                          (count exp-pre)))
                             [exp-post body] (if (:post old-sig)
                                               (let [[_let_ [_%_ body] & posts+%] body]
                                                 [(butlast posts+%) body])
                                               [nil body])
                             _ (assert (= (count (:post old-sig))
                                          (count exp-post)))
                             pre-post-meta-map (merge (when exp-pre
                                                        {:pre exp-pre})
                                                      (when exp-post
                                                        {:post exp-post}))
                             fn-params (with-meta (into fixed-dparams 
                                                        (when rst-dparam ['& rst-dparam]))
                                                  (merge (meta params)
                                                         (when (:conds-from-params-meta? old-sig)
                                                           pre-post-meta-map)))]
                         `(~fn-params
                            ~@(when-not (:conds-from-params-meta? old-sig)
                                (when (seq pre-post-meta-map)
                                  [pre-post-meta-map]))
                            ~@(splice-checked-body-forms body))))
        unexpanded-sigs (map unexpand-sig sigs original-sigs)]
    (list* (first original-form)
           (concat (when (symbol? name) [name])
                   ((if single-arity-syntax? first identity) unexpanded-sigs)))))

(defmethod -expand-macro 'clojure.core/fn
  [[_ & sigs :as form] _]
  (let [{:keys [sigs name]} (parse-fn-sigs sigs)
        expand-sig (fn [{:keys [conds-from-params-meta? pre post params body sig-form]}]
                     (assert (vector? params))
                     (let [gsyms (mapv (fn [a]
                                         (if (= '& a)
                                           a
                                           (gensym "a")))
                                       params)
                           fn*-params (with-meta gsyms (meta params))
                           assert-form (fn [p] `^::t/freeze (assert ~p))]
                       `(~fn*-params
                         ^::t/freeze
                         (let [~@(mapcat (fn [param gsym]
                                           (when-not (= '& param)
                                             [param gsym]))
                                         params
                                         gsyms)]
                           ~@(map assert-form pre)
                           ~(let [body `^::t/freeze (check-if-empty-body
                                                    (do ~@body)
                                                    {:msg-fn (fn [_#]
                                                               (str "This 'fn' body returns nil, "
                                                                    "which does not agree with the expected type."))
                                                     :blame-form ~sig-form
                                                     :original-body ~body})]
                              (if post
                                `^::t/freeze (let [~'% ~body]
                                             ~@(map assert-form post)
                                             ~'%)
                                body))))))]
    `(fn* ~@(when name [name])
          ~@(map expand-sig sigs))))

(defmacro check-for-seq [{:keys [expr]}]
  (throw (Exception. "Cannot expand check-for-seq")))

(defmethod -expand-macro `check-for-seq [[_ {:keys [expr]} :as form] _]
  `(rand-nth (seq ~expr)))

(defmethod -unexpand-macro `check-for-seq [[_rand-nth_ [_seq_ expr]] {:keys [original-form]}]
  (let [[mop opt] original-form]
    (list mop (assoc opt :expr expr))))

(defmacro expected-as [s body]
  body)

(defmethod -expand-macro `expected-as [[_ s body] _]
  `(let* [~s 'nil] ~body))

(defmethod -unexpand-macro `expected-as [[_let*_ [s _] body] {:keys [original-form]}]
  (list (first original-form) s body))

(defmacro gather-for-return-type [ret]
  (throw (Exception. "gather-for-return-type Not for expansion")))

(defmethod -expand-macro `gather-for-return-type [[_ ret] _]
  ret)

(defmethod -unexpand-macro `gather-for-return-type [ret {:keys [original-form]}]
  (list (first original-form) ret))

(defmacro check-for-expected [{:keys [expr expected-local]}]
  (throw (Exception. "check-for-expected Not for expansion")))

(defmethod -expand-macro `check-for-expected [[_ {:keys [expr expected-local]}] _]
  expr)

(defmethod -unexpand-macro `check-for-expected [expr {:keys [original-form]}]
  (let [[mop opt] original-form]
    (list mop (assoc opt :expr expr))))

(def clojure-core-for-expansions
  {:reduce-based {:expand-macro 
                  (fn [[_ seq-forms body-form :as form] _]
                    (let [acc (gensym "acc")]
                      (reduce
                        (fn [body [expr binding]]
                          (with-meta
                            (case binding
                              :let `(let ~expr ~body)
                              :when `(if ~expr ~body ~acc)
                              :while `(if ~expr ~body (reduced ~acc))
                              (if (keyword? binding)
                                (throw (Exception. (str "Invalid 'for' keyword: " binding)))
                                `(reduce (fn [~acc ~binding] ~body) ~acc ~expr)))
                            {::t/freeze true}))
                        `(concat ~acc (list ~body-form))
                        (partition 2 (rseq seq-forms)))))
                  :unexpand-macro
                  (fn [form {:keys [original-form]}]
                    (let [[seq-forms body] original-form]
                      (loop [seq-forms seq-forms
                             new-seq-forms []
                             form form]
                        (if (empty? seq-forms)
                          (let [[_concat _ [_list_ body]] form]
                            (list (first original-form)
                                  new-seq-forms
                                  body))
                          (let [[binding _ & seq-forms] seq-forms
                                [expr form] (case binding
                                              :let (let [[_let_ expr form] form]
                                                     [expr form])
                                              (:when :while) (let [[_if_ expr form] form]
                                                               [expr form])
                                              (let [[_reduce_ [_fn_ _ form] _ expr] form]
                                                [expr form]))]
                            (recur seq-forms
                                   (conj new-seq-forms binding expr)
                                   form))))))}
   :typed {:expand-macro 
           (fn [[_ seq-forms body-form :as form] _]
             (let [expg (gensym 'expected)
                   ret (reduce
                         (fn [body [expr binding]]
                           (with-meta
                             (case binding
                               :let `(let ~expr ~body)
                               (:while :when) `(when ~expr ~body)
                               (if (keyword? binding)
                                 (throw (Exception. (str "Invalid 'for' keyword: " binding)))
                                 `(let [~binding ^::t/freeze (check-for-seq
                                                             {:expr ~expr
                                                              :binding ~binding})]
                                    ~body)))
                             {::t/freeze true}))
                         `[^::t/freeze (check-for-expected
                                       {:expr ~body-form
                                        ;; FIXME should we blame an outer form (if it exists)
                                        ;; if the expected type is incompatible with Seq?
                                        :form ~form
                                        :expected-local ~expg})]
                         (partition 2 (rseq seq-forms)))]
               `^::t/freeze
                (expected-as ~expg
                  ^::t/freeze (gather-for-return-type ~ret))))
           :unexpand-macro
           (fn [form {:keys [original-form]}]
             (let [[mop original-seq-forms _] original-form
                   [_expected-as_ _ [_gather-for-return-type_ form]] form]
               (loop [original-seq-forms original-seq-forms
                      seq-forms []
                      form form]
                 (if (empty? original-seq-forms)
                   (let [[[_check-for-expected {form :expr}]] form]
                     (list mop seq-forms form))
                   (let [[binding _ & original-seq-forms] original-seq-forms
                         [seq-forms form]
                         (case binding
                           :let (let [[_let_ expr body] form]
                                  [(conj seq-forms binding expr) body])
                           (:while :when) (let [[_when_ expr body] form]
                                            [(conj seq-forms binding expr) body])
                           (let [[_let_ [_ [_check-for-seq_ {:keys [expr]}]] body] form]
                             [(conj seq-forms binding expr) body]))]
                     (recur original-seq-forms
                            seq-forms
                            form))))))}})

(defmethod -unexpand-macro 'clojure.core/for
  [& args]
  (apply (-> clojure-core-for-expansions :typed :unexpand-macro) args))

(defmethod -expand-macro 'clojure.core/for
  [& args]
  (apply (-> clojure-core-for-expansions :typed :expand-macro) args))

(defmethod -expand-macro 'clojure.core.typed/fn
  [[_ & forms :as form] _]
  (let [{:keys [poly fn ann]} (internal/parse-fn* forms)]
    (with-meta fn {::t/freeze true})))

(defmethod -unexpand-macro 'clojure.core.typed/fn
  [[_fn_ & sigs] {:keys [original-form]}]
  (let [[mop & forms] original-form
        {:keys [poly fn ann single-arity-syntax?]} (internal/parse-fn* forms)]
    (list* mop
           (concat (apply concat poly)
           ))))

(defmethod -expand-macro 'clojure.core/ns [form _]
  (prn "expand ns" form)
  `^::t/freeze
  (check-expected
    nil
    {:msg-fn (fn [_#]
               "This 'ns' expression returns nil, which does not agree with the expected type.")
     :blame-form ~form}))

(defmethod -unexpand-macro 'clojure.core/ns
  [_ {:keys [original-form]}]
  original-form)
