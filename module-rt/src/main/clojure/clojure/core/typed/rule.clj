(ns clojure.core.typed.rule
  (:require [clojure.core.typed :as t]
            [clojure.core.typed.internal :as internal]))

; {:op :unanalyzed
;  :form '(update {:a 1} :a inc)}
; =>
; (macroexpand-1 '(update {:a 1} :a inc))
; =>
; (invoke-type-rule 'clojure.core/update '(update {:a 1} :a inc) '{:a 1} ':a 'inc)
; =>
; {:op :unanalyzed
;  ::t/tc-ignore true
;  :form '(update {:a 1} :a inc)
;  :expr-type (ret '{:a Number})}
; (Atom (Map Symbol {:op (U :fn :macro) :rewrite-fn ?}))

(defonce registry (atom {}))

(defn inspect-registry []
  (into {}
        (map (fn [[k {:keys [op] :as v}]]
               (case op
                 :fn (let [{:keys [fixed flat-arg-syms var-arg? rewrite-fn args-vector]} v]
                       [k (list 'fn args-vector (apply rewrite-fn flat-arg-syms))])
                 ; illegible, don't think there's a fix since so much structure gets
                 ; lost in syntax-quote, and we need valid arguments to the macro.
                 :macro [k (:rewrite-fn-form v)])))
        @registry))

(defmacro defmacrorule [sym args rewrite]
  (let [fn-out `(fn ~args ~rewrite)]
    `(swap! registry assoc ~sym
            {:op :macro
             :rewrite-fn-form '~fn-out
             :rewrite-fn ~fn-out})))

(defmacro defnrule [sym args rewrite]
  {:pre [(vector? args)]}
  (let [vararg? (and (<= 2 (count args))
                     (= '& (nth args (- (count args) 2))))
        flatargs (if vararg?
                   (conj (subvec args 0 (- (count args) 2))
                         (peek args))
                   args)
        _ (assert (every? symbol? flatargs)
                  (str "Args vector to defnrule must not use destructuring, only plain symbols allowed. "
                       "If you need destructuring, let-bind the arguments in a let in the syntax returned by your defnrule."))
        ; TODO ensure locals use init's form in errors
        fn-out `(fn ~flatargs ~rewrite)]
    `(swap! registry assoc ~sym
            {:op :fn
             :flat-arg-syms '~flatargs
             :args-vector '~args
             :fixed-args ~((if vararg? dec identity) (count flatargs))
             :var-arg? ~vararg?
             :rewrite-fn ~fn-out})))

#_
(defmacrorule `when
  [test & args]
  `(if ~test
     (do ~@args)
     nil))

; fn arguments evaluate before they are passed (but we
; might delay type checking). Clojure guarantees this, and
; so the body of a fn depends on the side effects (eg. error checking)
; of arguments evaluating. So we set this up for the user implicitly,
; and do our best to delay type checking problematic arguments (like
; lambda's).
#_
(defnrule `clojure.core/update
  [m k f & args]
  `(assoc ~m ~k (apply ~f (get ~m ~k) ~args)))

(defnrule `clojure.core/update
  [m k f]
  `(assoc ~m ~k (~f (get ~m ~k))))

; bindings in rewrite will be lazily resolved, so you'd want
; your ns defs/refers to be stable.
#_
(defmacro defnrule [sym args rewrite]
  (let [vararg? (and (<= 2 (count args))
                     (= '& (nth args (- (count args) 2))))
        flatargs (if vararg?
                   (into (subvec args 0 (- (count args) 2))
                         (peek args))
                   args)
        ; TODO ensure locals use init's form in errors
        rewrite-out '`(let
                        ; bind argument expressions to locals
                        ~(vec (interleave flatargs (map emit-form/emit-form flatargs)))
                        ~rewrite)
        fn-out `(fn ~args ~rewrite-out)]
    `(swap! registry assoc ~sym
            {:op :fn
             ;; used to resolve rewrite-out
             :ns (ns-name *ns*)
             :rewrite-fn '~fn-out})))

#_
(defmacro defnrule* [sym args syntax-quoted-rewrite]
  (let [fn-out `(fn ~args ~syntax-quoted-rewrite)]
    `(swap! registry assoc ~sym
            {:op :fn
             :ns (ns-name *ns*)
             :rewrite-fn '~fn-out})))

#_
(defmacro defmacrorule [sym args rewrite]
  (let [fn-out `(fn ~args ~rewrite)]
    `(swap! registry assoc ~sym
            {:op :macro
             :ns (ns-name *ns*)
             :rewrite-fn '~fn-out})))

(comment

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
  "Takes a qualified symbol naming the var or macro whose invocation
  will trigger the type rule, and a binding vector like defn/defmacro.
  Binds &expr as a local variable, which is a tools.analyzer node that
  represents this invocation (often :unanalyzed or :invoke)."
  [name args & body]
  {:pre [(symbol? name)]}
  `(defmethod -type-rules '~name
     [~'&expr ~@args]
     (let [res# (do ~@body)]
       (assert (:op res#))
       (assoc res# assoc ::t/tc-ignore true))))

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

(defn match
  "Loosely match template u (can contain lvars) with instantiation v (cannnot contain lvars).

  If u is a lvar not in s, records its value as v; if it's already
  in s, unification fails.

  If u and v are non-empty sequential collections, unifies their
  first's and rest's.

  Otherwise returns s.
  
  Returns a substitution map if unification was successful, otherwise nil."
  [u v s]
  (cond
    (not s) s
    (lvar? u) (when (or (not (contains? s u))
                        (= (get s u) v))
                (when (not= (::lvar-default u) v)
                  (assoc s u v)))
    (and (sequential? u)
         (sequential? v)
         (seq u)
         (seq v)) (some->> (match (first u) (first v) s)
                           (match (rest u) (rest v)))
    :else s))

(defn unexpand-from-template
  [template-fn [nme & args :as form] expanded]
  {:pre [(seq? form)
         (seq form)]}
  (let [lvars (map make-lvar args)
        template (template-fn lvars)
        eargs (match template expanded {})]
    (-> (list* nme (mapv (fn [lvar arg]
                           (if-let [[_ v] (find eargs lvar)]
                             v
                             arg))
                         lvars
                         args))
        (with-meta (meta form)))))

(defmacro defmacrorule [sym args rewrite]
  `(defrule ~sym [& args#]
     (let [template-fn# (fn ~args ~rewrite)
           expr# (apply template-fn# args#)
           cexpr# (check expr# (form-expected ~'&form))
           uform# (unexpand-from-template
                    template-fn#
                    ~'&form
                    cexpr#)]
       (-> uform#
           (annotate-result (form-result cexpr#))))))

#_
(defmacro defnrule [sym args rewrite]
  (let [vararg? (and (<= 2 (count args))
                     (= '& (nth args (- (count args) 2))))
        flatargs (if vararg?
                   (into (subvec args 0 (- (count args) 2))
                         (peek args))
                   args)]
    `(defrule ~sym [& args#]
       (let [template-fn# (fn ~args
                            (list `let
                                  ; TODO ensure locals use init's form in errors
                                  (vec (interleave
                                         '~flatargs
                                         (map emit-form/emit-form ~flatargs)))
                                  '~rewrite))
             expr# (apply template-fn# args#)
             cexpr# (check-form expr# (:env ~'&expr))
             uform# (unexpand-from-template
                      template-fn#
                      ~'&form
                      cexpr#)]
         (-> uform#
             (annotate-result (form-result cexpr#)))))))

(defmacrorule clojure.core/when
  [test & body]
  `(if ~test
     (do ~@body)
     nil))

(defmacrorule clojure.core/or
  ([] nil)
  ([x] x)
  ([x & next]
   `(let [or# ~x]
      (if or# or# (or ~@next)))))

(defrule clojure.core.typed/type-cond
  [& args]
  (let [chose (atom 0)
        expr (reduce (fn [_ [test expr]]
                       (if (eval `(let [~@(mapcat (juxt :form :name) &env)]
                                    ~test))
                         (reduced expr)
                         (swap! chose inc)))
                     nil
                     (partition 2 args))
        cexpr (check expr expected)
        ]
    ))

; IDEA: store delayed type checks in the object of a Result
; then we can delay things like (let [[a] [(fn [a] (inc a))]] (a 1))
(defnrule clojure.core/map
  ([f]
   ; TODO automatically require an expected type and blame &form
   (fn [rf]
     (fn
       ([] (rf))
       ([result] (rf result))
       ([result input]
        (rf result (f input))))))
  ([f & colls]
   ; (type-case-as out (first colls)
   ;   `(Map f ~@colls)
   ;   (All [x] [(Seqable x) -> x])
   (lazy-seq
     (t/type-cond
       ;; colls are their local symbols
       (some #(t/subtype? `(t/TypeOf ~'%) `(t/ExactCount 0))
             colls)
       nil
       (and (every? #(t/subtype? `(t/TypeOf ~'%) `(t/CountRange 1))
                    colls)
            (some #(t/subtype? `(t/TypeOf ~'%) `(t/CountRange 1 10))
                  colls))
       (cons (apply f (map first colls))
             (apply map f (map rest colls)))
       :else (-> (apply f (-> colls
                              (t/utransform
                                (t/All [t ...]
                                  [(t/HSequential [(t/U nil (t/Seqable t)) ... t]) :->
                                   (t/HSequential [t ... t])]))))
                 (t/utransform
                   (t/All [t] [t :-> (t/Seq t)])))))))

(defn make-lvar [default]
  (with-meta (gensym 'lvar) {::lvar true
                             ::lvar-default default}))

(defn lvar? [s]
  (and (symbol? s)
       (boolean (-> s meta ::lvar))))


#_
(defexpandrule clojure.core/ns
  [& args]
  nil)

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
                     (cons (map make-lvar bindings)
                           (map make-lvar body)))}
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
                     (cons (mapv make-lvar bindings)
                           (mapv make-lvar body)))}
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
                     [(map make-lvar seq-exprs)
                      (make-lvar body-expr)])}
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
;        ]))

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
)
