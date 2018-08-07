(ns clojure.core.typed.rule
  (:require [clojure.core.typed :as t]
            [clojure.core.typed.internal :as internal]))

(defmulti -type-rules (fn [&form &env & args]
                        (when (and (seq? &form)
                                   (seq &form))
                          (first &form))))

(defn custom-type-rule? [vsym]
  (contains? (methods -type-rules) vsym))

(defn check
  "Type checks a form "
  ([form] (check form nil))
  ([form expected]
   (assert nil "TODO check")))

(defmacro deftyperule
  "Takes a qualified symbol naming the var or macro whoes invocation
  will trigger the type rule, and a binding vector like defn/defmacro.
  Also binds &form and &env like defmacro.
  
  Most type information can be derived from &form -- for convenience,
  &expected is (form-expected &form) and &tenv is (form-tenv &form).
  
  eg. (form-expected &form) is the expected type-result of the current type rule.
  eg. (form-tenv &form) is the initial type environment of the current type rule.

  "
  [name args & body]
  {:pre [(symbol? name)]}
  `(defmethod -type-rules '~name
     [~'&form ~'&env ~@args]
     (let [~'&expected (form-expected ~'&form)
           ~'&tenv (form-tenv ~'&form)
           res# (do ~@body)]
       ;; output must be unifiable with input
       (assert
         (= (unexpand-from-template
              (fn ~args
                (list* (first ~'&form) ~@args))
              ~'&form
              res#)
            res#))
       (vary-meta res# assoc ::t/untyped true))))

(defn form-expected [form]
  (-> form meta ::t/expected))

(defn form-tenv [form]
  (-> form meta ::t/tenv))

(defn add-blame-info [expected info]
  ;; first takes precedence
  (update expected :blame (fnil []) info))

(defn form-result
  "Return the type-result for a type-checked form.
  A type-result is a map with these entries:
  
    :type - The type (syntax) the form type checked as.
    :test - A map of propositions relevant when this form
            is used as a test -- the :then entry applies when
            the form is true, the :else entry applies when the
            form is false.
    :path - Either :unknown, or a form representing how the value
            of form was derived in terms of other values and variables."
  [form]
  {:pre [(seq (meta form))]
   :post [(map? %)]}
  (::t/type-result (meta form)))

(defn annotate-result [form res]
  (let [form (if (instance? form clojure.lang.IObj)
               form
               `(do ~form))]
    (vary-meta form assoc ::t/type-result res)))

#_
(deftyperule clojure.core/when
  [test & body]
  (let [ctest (check test)
        cthen (let [tenv (-> &tenv
                             (refine-tenv (-> ctest form-result :test :then)))
                    expected (cond-> &expected
                               (empty? body) (add-blame-info {:form &form}))]
                (-> `(do ~@body)
                    (use-tenv tenv)
                    (use-expected expected)
                    check))
        celse (let [tenv (-> &tenv
                             (refine-tenv (-> ctest form-result :test :else)))
                    expected (-> &expected
                                 (add-blame-info 
                                   {:msg "This 'when' expression returns nil if the test is false, which does not agree with the expected type."
                                    :form &form}))]
                (-> nil
                    (use-tenv tenv)
                    (use-expected expected)
                    check))]
    (-> (ignore `(when ~ctest ~cbody))
        (annotate-result (combine-results (mapv form-result [cthen celse]))))))

#_
(defrewriterule clojure.core/when
  [test & body]
  `(if ~test
     (do ~@body)
     nil))

(defn make-lvar []
  (with-meta (gensym 'lvar) {::lvar true}))

(defn lvar? [s]
  (and (symbol? s)
       (boolean (-> s meta ::lvar))))

(defn unify
  "Loosely unify template u (can contain lvars) with instantiation v (cannnot contain lvars).

  If u is a lvar not in s, records its value as v; if it's already
  in s, unification fails.

  If u and v are non-empty sequential collections, unifies their
  first's and rest's.

  Otherwise returns s.
  
  Returns a substitution map if unification was successful, otherwise nil."
  [u v s]
  (cond
    (not s) s
    (lvar? u) (when-not (contains? s u)
                (assoc s u v))
    (and (sequential? u)
         (sequential? v)
         (seq u)
         (seq v)) (some->> (unify (first u) (first v) s)
                           (unify (rest u) (rest v)))
    :else s))

(defn unexpand-from-template
  [template-fn [nme & args :as form] expanded]
  {:pre [(seq? form)
         (seq form)]}
  (let [lvars (repeatedly (count args) make-lvar)
        template (template-fn lvars)
        eargs (unify template expanded {})]
    (-> (list* nme (mapv (fn [lvar arg]
                           (if-let [[_ v] (find eargs lvar)]
                             v
                             arg))
                         lvars
                         args))
        (with-meta (meta form)))))

(defmacro defrewriterule [sym args rewrite]
  `(deftyperule ~sym [& args#]
     (let [template-fn# (fn ~args ~rewrite)
           expr# (apply template-fn# args#)
           cexpr# (check expr# ~'&expected)
           uform# (unexpand-from-template
                    template-fn#
                    ~'&form
                    cexpr#)]
       (-> uform#
           (inherit-result cexpr#)))))

#_
(defexpandrule clojure.core/ns
  [& args]
  nil)

#_
(defrewriterule1 clojure.core/update
  [m k f & args]
  `((fn [m# k# f# & args#]
      (assoc m# k# (apply f# (get m# k#) args#)))
    ~m ~k ~f ~@args))

#_
(definlinerule1 clojure.core/update
  [m k f & args]
  (assoc m k (apply f (get m k) args)))

#_
; all args are locals, but how to undo?
(defnrule clojure.core/update
  [m k f & args]
  `(assoc ~m ~k (~f (get ~m ~k) ~@args)))

(comment
  (update {} :a vector 1)
  =>
  (let [[m k f & args] (repeatedly 4 gensym)]
    `(assoc ~m ~k (~f (get ~m ~k) ~@args)))
  =>
  '(assoc m_ k_ (f_ (get m_ k_) arg0_))
  )

#_
(defmacrorule clojure.core/when-let
  {:template-lvars (fn [bindings & body]
                     (cons [(make-lvar) (make-lvar)]
                           (repeatedly (count body) make-lvar)))}
  [bindings & body]
  {:pre [(vector? bindings)
         (= 2 (count bindings))]}
  (let [[b init] bindings]
    `(let [temp# ~b]
       (when temp#
         (let [~init temp#]
           ~@body)))))

#_
(defmacrorule clojure.core/binding
  {:template-lvars (fn [bindings & body]
                     (cons (vec
                             (mapcat (fn [[v init]]
                                       [v (make-lvar)])
                                     (partition 2 bindings)))
                           (repeatedly (count body) make-lvar)))}
  [bindings & body]
  {:pre [(vector? bindings)
         (even? (count bindings))]}
  `(let [~@(mapv (fn [[v init]]
                   [(gensym '_)
                    `(t/ann-form init (t/TypeOf ~v))])
                 (partition 2 bindings))]
     ~@body))

#_
(defmacrorule clojure.core/for
  {:template-lvars (fn [seq-exprs body-expr]
                     [(vec
                        (mapcat (fn [[binding expr]]
                                  [binding (make-lvar)])
                                (partition 2 seq-exprs)))
                      (make-lvar)])}
  [seq-exprs body-expr]
  (reduce
    (fn [body [expr binding]]
      (case binding
        :let `(let ~expr ~body)
        ;; simulate :while with a `when`
        (:while :when) `(when ~expr [~body])
        (if (keyword? binding)
          (throw (Exception. (str "Invalid 'for' keyword: " binding)))
          `(mapcat (fn [~binding]
                     ~body)
                   ~expr))))
    body-expr
    (partition 2 (rseq seq-forms))))

(comment
  (for [a cs
        :when a
        b ds
        :when b]
    d)
  =>
  (mapcat (fn [a]
            (when a
              [(mapcat (fn [b]
                         (when b
                           [d]))
                       ds)]))
          cs)
  )

#_
(deftyperule clojure.core/update-in
  [m ks f & args]
  (let [cm (check m)
        cks (check ks)
        cget (-> `(get-in ~cm ~cks)
                 check)
        v (gensym 'v)
        cf (-> `(~f ~v ~@args)
               (use-tenv (-> &tenv
                             (extend-tenv v (type-result cget))))
               check)]
    (-> 
      `(t/tc-ignore
         (update-in ~cm ~cks (fn [~v] ~cf)))
      (annotate-result {:type `(t/AssocIn ~(form-type cm) ~(form-type ck) ~(form-type cf))})
      (check-form-result &expected))))

#_
(deftyperule clojure.core/assoc-in
  [m ks v]
  (let [cm (check m)
        cks (check ks)
        cv (check v)]
    (->
      `(t/tc-ignore
         (assoc-in ~cm ~cks ~cv))
      (annotate-result {:type `(t/AssocIn ~(form-type cm) ~(form-type ck) ~(form-type cv))})
      (check-form-result &expected))))

;(defspecialrule :map
;  [special]
;  (let [{:keys [keys vals] :as special}
;        (-> special
;            (update :keys #(mapv check %))
;            (update :vals #(mapv check %)))
;        kts (mapv form-result keys)
;        vts (mapv form-result vals)
;        rt (`(t/
;        ]

;(deftyperule `class
;  [x]
;  (let [cx (check x)]
;    (-> `(t/tc-ignore
;           (class ~cx))
;        (annotate-result {:type `(Un nil Class)
;                          :path `(class ~(form-path cx))}))))

;; TODO check expected
#_
(deftyperule clojure.core/seq
  [c]
  (let [cc (check c)
        res-form `(t/tc-ignore (seq ~cc))
        cc-type (-> cc form-result :type)]
    (if-let [memt (infer [x] cctype `(NonEmptyColl ~x))]
      (-> res-form
          (annotate-result {:type `(NonEmptyASeq ~(:type memt))
                            :prop {:else `Never}})
          (check-expected &expected))
      (if-let [memt (infer [x] cctype `(Option (Coll ~x)))]
        (-> res-form
            (annotate-result {:type `(Option (NonEmptyASeq ~(:type memt)))
                              :prop {:then `(Is ~(form-path cc) (I (Not nil) NonEmptyCount))
                                     ; (Is :no-path nil) ;=> Trivial
                                     :else `(Is ~(form-path cc) (U nil EmptyCount))}})
            (check-expected &expected))
        (if-let [memt (infer [x] cctype `(Option Coll ~x))]
          (-> res-form
              (annotate-result {:type `(Option (NonEmptyASeq ~(:type memt)))})
              (check-expected &expected))
          (-> res-form
              (attach-expected &expected)
              (annotate-error {:msg "First argument to seq is the wrong type."
                               :blame-form &form})))))))

#_
(deftyperule clojure.core/let
  [bindings & body]
  (let [[tenv cbindings]
        (reduce (fn [[tenv cbindings] [b init]]
                  (let [cinit (-> init
                                  (use-tenv tenv)
                                  (check init))]
                    [(-> tenv
                         (extend-tenv-destructure b (form-result cinit)))
                     (conj cbindings b cinit)]))
                [(form-tenv &form) bindings]
                (partition 2 bindings))
        cbody (-> `(do ~@body)
                  (use-tenv tenv)
                  (check (some-> (form-expected &form)
                           (cond-> 
                             (empty? body) (add-blame-info {:form &form})))))
        res (-> (form-result cbody)
                (erase-references (map first cbindings)))]
    (-> `(t/tc-ignore (let ~cbindings ~cbody))
        (annotate-result res))))

#_
(deftyperule clojure.core/for
  [seq-exprs body-expr]
  (let [_ (assert (even? (count seq-exprs)))
        check-for (fn check-for [seq-exprs body]
                    (if (empty? seq-exprs)
                      [(check body)]
                      (let [[binding expr & rst] seq-exprs]
                        (case binding
                          :let ()
                          (:while :when) `(when ~expr ~body)
                          (if (keyword? binding)
                            (throw (Exception. (str "Invalid 'for' keyword: " binding)))
                            (let [cexpr (check expr)]
                              body))))))
        [cseq-exprs cbody] ((juxt pop peek) (check-for seq-exprs body-expr))]

      `(t/tc-ignore
         (for ~cseq-exprs ~cbody))))
