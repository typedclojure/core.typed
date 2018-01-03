(ns clojure.core.typed.expand
  "Rewriting rules for custom expansions and undoing those
  custom expansions (\"unexpansions\"), mainly to improve type checking
  error messages."
  (:require [clojure.core.typed :as t]
            [clojure.core.typed.special-form :as spc]
            [clojure.core.typed.internal :as internal]))

(defmulti -expand-macro (fn [form {:keys [vsym]}] vsym))

(defn custom-expansion? [vsym]
  {:pre [(symbol? vsym)
         (namespace vsym)]}
  (contains? (methods -expand-macro) vsym))

(defn expand-macro [form opts]
  (-expand-macro form opts))

(defmacro check-let-destructure [{:keys [expression]}] expression)
(defmacro check-let-destructure-no-op [_] nil)

(defmethod -expand-macro `check-let-destructure [[_ {:keys [expression]} :as form] _] expression)

(defmethod -expand-macro `check-let-destructure-no-op [_ _] nil)

(defmethod -expand-macro 'clojure.core/let
  [[_ bindings-form & body-forms :as form] _]
  (let [gs (gensym "b")]
    (reduce
      (fn [form [expression binding]]
        `(let* [~gs (check-let-destructure
                      {:binding ~binding
                       :expression ~expression})
                ~@(destructure [binding gs])]
           ~form))
      `(check-if-empty-body
         (do ~@body-forms)
         {:msg-fn (fn [_#]
                     "This 'let' expression returns nil with an empty body, which does not agree with the expected type")
          :blame-form '~form
          :original-body '~body-forms})
      (partition 2 (rseq bindings-form)))))

(defmacro check-if-empty-body [e opts]
  {:pre [(map? opts)]}
  `(do ~spc/special-form
       ::check-if-empty-body
       '~opts
       ~e))

(defmacro check-expected [e opts]
  {:pre [(map? opts)]}
  `(do ~spc/special-form
       ::check-expected
       '~opts
       ~e))

(defmethod -expand-macro 'clojure.core/when
  [[_ test & bodys :as form] _]
  `(if ~test
     (check-if-empty-body
       (do ~@bodys)
       {:msg-fn (fn [_#]
                  "This 'when' expression returns nil if the test is true, which does not agree with the expected type.")
        :blame-form ~form
        :original-body ~bodys})
     (check-expected
       nil
       {:msg-fn (fn [_#]
                  "This 'when' expression returns nil if the test is false, which does not agree with the expected type.")
        :blame-form ~form})))

(defmethod -expand-macro 'clojure.core/when-not
  [[_ test & bodys :as form] _]
  `(if ~test
     (check-expected
       nil
       {:msg-fn (fn [_#]
                  "This 'when-not' expression returns nil if the test is true, which does not agree with the expected type.")
        :blame-form ~form})
     (check-if-empty-body
       (do ~@bodys)
       {:msg-fn (fn [_#]
                  "This 'when-not' expression returns nil if the test is false, which does not agree with the expected type.")
        :blame-form ~form
        :original-body ~bodys})))

(defmethod -expand-macro 'clojure.core/if-let
  [[_ bindings then else :as original-form] _]
  (let [form (bindings 0) tst (bindings 1)]
    `(let [temp# ~tst]
       (if temp#
         (let [_# (check-let-destructure-no-op
                    {:binding ~form
                     :expression ~tst})
               ;TODO avoid repeated destructuring checks ^::no-check-destructure
               ~form temp#]
           ~then)
         ~(if (= 3 (count original-form))
            `(check-expected
               nil
               {:msg-fn (fn [_#]
                          "This 'if-let' expression returns nil if the test is false, which does not agree with the expected type.")
                :blame-form ~original-form})
            else)))))

(defmethod -expand-macro 'clojure.core/when-let
  [[_ test & bodys :as form] _]
  `(if-let ~test
     (check-if-empty-body
       (do ~@bodys)
       {:msg-fn (fn [_#]
                  "This 'when-let' expression returns nil if the test is true, which does not agree with the expected type.")
        :blame-form ~form
        :original-body ~bodys})
     (check-expected
       nil
       {:msg-fn (fn [_#]
                  "This 'when-let' expression returns nil if the test is false, which does not agree with the expected type.")
        :blame-form ~form})))

(defmethod -expand-macro 'clojure.core/with-open
  [[_ bindings & body :as form] _]
  (let [expand-with-open (fn expand-with-open [bindings body]
                           (cond
                             (= (count bindings) 0) `(check-if-empty-body
                                                       (do ~@body)
                                                       {:msg-fn (fn [_#]
                                                                  (str "This 'with-open' expression returns nil, "
                                                                       "which does not agree with the expected type."))
                                                        :blame-form ~form
                                                        :original-body ~body})
                             (symbol? (bindings 0)) `(let ~(subvec bindings 0 2)
                                                       (try
                                                         ~(expand-with-open (subvec bindings 2) body)
                                                         (finally
                                                           (. ~(bindings 0) close))))
                             :else (throw (IllegalArgumentException. "with-open only allows Symbols in bindings"))))]
    (expand-with-open bindings body)))

(defmethod -expand-macro 'clojure.core/assert
  [[_ x message :as form] _]
  (let [msg? (= 3 (count form))
        erase-assert? (not *assert*)
        assert-expand (fn
                        ([x]
                         (when-not erase-assert?
                           `(when-not ~x
                              (throw (new AssertionError (str "Assert failed: " (pr-str '~x)))))))
                        ([x message]
                         (when-not erase-assert?
                           `(when-not ~x
                              (throw (new AssertionError (str "Assert failed: " ~message "\n" (pr-str '~x))))))))]
    (apply assert-expand (rest form))))

(defn parse-fn-sigs [[_ & sigs :as form]]
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
                         {;; inherit positional information from params, or
                          ;; overall fn if unavailable. If multi-arity, sig might
                          ;; also have meta.
                          :sig-form (vary-meta sig #(merge (meta form) (meta params) %))
                          :pre pre
                          :post post
                          :conds-from-params-meta? conds
                          :params params
                          :body body}))]
    {:single-arity-syntax? single-arity-syntax?
     :sigs (mapv process-sigs sigs)
     :name name}))

(defmethod -expand-macro 'clojure.core/fn
  [[_ & sigs :as form] _]
  (let [{:keys [sigs name]} (parse-fn-sigs form)
        expand-sig (fn [{:keys [conds-from-params-meta? pre post params body sig-form]}]
                     (assert (vector? params))
                     (let [gsyms (mapv (fn [a]
                                         (if (= '& a)
                                           a
                                           (gensym "a")))
                                       params)
                           fn*-params (with-meta gsyms (meta params))
                           assert-form (fn [p] `(assert ~p))]
                       `(~fn*-params
                         (let [~@(mapcat (fn [param gsym]
                                           (when-not (= '& param)
                                             [param gsym]))
                                         params
                                         gsyms)]
                           ~@(map assert-form pre)
                           ~(let [body `(check-if-empty-body
                                          (do ~@body)
                                          {:msg-fn (fn [_#]
                                                     (str "This 'fn' body returns nil, "
                                                          "which does not agree with the expected type."))
                                           :blame-form ~sig-form
                                           :original-body ~body})]
                              (if post
                                `(let [~'% ~body]
                                   ~@(map assert-form post)
                                   ~'%)
                                body))))))]
    `(fn* ~@(when name [name])
          ~@(map expand-sig sigs))))

(defmacro check-for-seq [{:keys [expr]}]
  (throw (Exception. "Cannot expand check-for-seq")))

(defmethod -expand-macro `check-for-seq [[_ {:keys [expr]} :as form] _]
  `(rand-nth (seq ~expr)))

(defmacro expected-as [s body]
  body)

(defmethod -expand-macro `expected-as [[_ s body] _]
  `(let* [~s 'nil] ~body))

(defmacro gather-for-return-type [ret]
  (throw (Exception. "gather-for-return-type Not for expansion")))

(defmethod -expand-macro `gather-for-return-type [[_ ret] _]
  ret)

(defmacro check-for-expected [{:keys [expr expected-local]}]
  (throw (Exception. "check-for-expected Not for expansion")))

(defmethod -expand-macro `check-for-expected [[_ {:keys [expr expected-local]}] _]
  expr)

(defmethod -expand-macro 'clojure.core/for
  [[_ seq-forms body-form :as form] _]
  (time
  (let [expg (gensym 'expected)
        ret (reduce
              (fn [body [expr binding]]
                (case binding
                  :let `(let ~expr ~body)
                  (:while :when) `(when ~expr ~body)
                  (if (keyword? binding)
                    (throw (Exception. (str "Invalid 'for' keyword: " binding)))
                    `(let [~binding (check-for-seq
                                      {:expr ~expr
                                       :binding ~binding})]
                       ~body))))
              `[(check-for-expected
                  {:expr ~body-form
                   ;; FIXME should we blame an outer form (if it exists)
                   ;; if the expected type is incompatible with Seq?
                   :form ~form
                   :expected-local ~expg})]
              (partition 2 (rseq seq-forms)))]
    `(expected-as ~expg
                  (gather-for-return-type ~ret)))))

(defmacro ignore-expected-if [tst body] body)

(defmethod -expand-macro `ignore-expected-if
  [[_ tst body :as form] _]
  {:pre [(= 3 (count form))]}
  body)

(defn expand-typed-fn-macro
  [form _]
  (let [{:keys [parsed-methods name poly ann]} (internal/parse-fn* form)
        reassembled-fn-type `(t/IFn ~@(map (fn [{:keys [rest drest dom rng] :as method-ann}]
                                             {:pre [(map? method-ann)]
                                              :post [(vector? %)]}
                                             (vec
                                               (concat
                                                 (map :type dom)
                                                 (cond
                                                   rest [(:type rest) '*]
                                                   drest [(-> drest :pretype :type) '... (:bound drest)])
                                                 [:-> (:type rng)])))
                                           (map :ann parsed-methods)))
        reassembled-fn-type (if-let [forall (:forall poly)]
                              `(t/All ~forall ~reassembled-fn-type)
                              reassembled-fn-type)]
    `(t/ann-form
       (fn ~@(concat
               (when name
                 [name])
               (for [{:keys [original-method body pvec ann]} parsed-methods]
                 (list pvec
                       `(ignore-expected-if ~(boolean (-> ann :rng :default))
                         (check-if-empty-body
                           (do ~@body)
                           {:msg-fn (fn [_#]
                                      "This 't/fn' method returns nil, which does not agree with the expected type.")
                            :blame-form ~original-method
                            :original-body ~body}))))))
      ~reassembled-fn-type)))

(defmethod -expand-macro `t/fn [& args] (apply expand-typed-fn-macro args))
(defmethod -expand-macro 'clojure.core.typed.macros/fn [& args] (apply expand-typed-fn-macro args))

(defmethod -expand-macro 'clojure.core/ns [form _]
  `(check-expected
     nil
     {:msg-fn (fn [_#]
                "This 'ns' expression returns nil, which does not agree with the expected type.")
      :blame-form ~form}))
