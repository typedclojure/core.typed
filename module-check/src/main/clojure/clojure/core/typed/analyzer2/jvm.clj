;; adapted from tools.analyzer.jvm
(ns clojure.core.typed.analyzer2.jvm
  (:refer-clojure :exclude [macroexpand-1])
  (:require [clojure.tools.analyzer.utils :as u]
            [clojure.tools.analyzer.jvm.utils :as ju]
            [clojure.tools.analyzer.env :as env]
            [clojure.tools.analyzer :as ta]
            [clojure.tools.analyzer.ast :as ast]
            [clojure.tools.analyzer.jvm :as taj]
            [clojure.tools.analyzer.passes.jvm.emit-form :as emit-form]
            [clojure.tools.analyzer.passes :as passes]
            [clojure.tools.analyzer.passes.trim :as trim]
            [clojure.tools.analyzer.passes.jvm.box :as box]
            [clojure.tools.analyzer.passes.jvm.warn-on-reflection :as warn-on-reflection]
            [clojure.tools.analyzer.passes.warn-earmuff :as warn-earmuff]
            [clojure.tools.analyzer.passes.add-binding-atom :as add-binding-atom]
            [clojure.tools.analyzer.passes.jvm.fix-case-test :as fix-case-test]
            [clojure.tools.analyzer.passes.jvm.infer-tag :as infer-tag]
            [clojure.tools.analyzer.passes.jvm.annotate-tag :as annotate-tag]
            [clojure.tools.analyzer.passes.jvm.annotate-host-info :as annotate-host-info]
            [clojure.tools.analyzer.passes.jvm.analyze-host-expr :as analyze-host-expr]
            [clojure.tools.analyzer.passes.jvm.validate :as validate]
            [clojure.tools.analyzer.passes.jvm.validate-loop-locals :as validate-loop-locals]
            [clojure.tools.analyzer.passes.jvm.validate-recur :as validate-recur]
            [clojure.tools.analyzer.passes.elide-meta :as elide-meta]
            [clojure.tools.analyzer.passes.source-info :as source-info]
            [clojure.tools.analyzer.passes.jvm.constant-lifter :as constant-lift]
            [clojure.tools.analyzer.passes.jvm.classify-invoke :as classify-invoke]
            [clojure.core.typed.analyzer2.passes.uniquify :as uniquify2]
            [clojure.core.typed.analyzer2 :as ana]
            [clojure.core.typed.analyzer2.pre-analyze :as pre]
            [clojure.core.typed.analyzer2.jvm.pre-analyze :as jpre]
            [clojure.core.memoize :as memo])
  (:import (clojure.lang IObj RT Var)))

(def specials
  "Set of the special forms for clojure in the JVM"
  (into ana/specials
        '#{monitor-enter monitor-exit clojure.core/import* reify* deftype* case*}))

(def ^:dynamic frozen-macros #{})

(defn freeze-macro? [op form env]
  (boolean
    (or (-> form meta ::freeze)
        (when (symbol? op)
          (when-not (specials op)
            (let [^Var v (u/resolve-sym op env)]
              (when (var? v)
                (let [vsym (symbol (str (ns-name (.ns v)))
                                   (str (.sym v)))]
                  (contains? frozen-macros vsym)))))))))

(declare thaw-form rerun-passes)

(defmulti -expand-macro (fn [form {:keys [vsym]}] vsym))
(defmulti -unexpand-macro (fn [form {:keys [vsym]}] vsym))

(def expand-macro -expand-macro)
(defn unexpand-macro [form opts]
  (let [out (-unexpand-macro form opts)]
    (vary-meta out #(merge (meta form) %))))

(defn do-form? [b]
  (and (seq? b) (= 'do (first b))))

;; preserves empty bodies like (let []), even if
;; they are expanded to (do nil), preventing (let [] nil)
(defn splice-body-forms [original-body new-do-body]
  (assert (do-form? new-do-body) (pr-str new-do-body))
  (when (seq original-body) (rest new-do-body)))

(defn splice-checked-body-forms
  [[_check-if-empty-body_ new-do-body {:keys [original-body]} :as checked-body]]
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
  [[_do_ & body] {[mop] :original-form}]
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
                   `(let* [~gs ^::freeze (check-let-destructure
                                           {:binding ~binding
                                            :expression ~expression})
                           ~@(destructure [binding gs])]
                      ~form))
                 `^::freeze
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
     ^::freeze
     (check-if-empty-body
       (do ~@bodys)
       {:msg-fn (fn [_#]
                  "This 'when' expression returns nil if the test is true, which does not agree with the expected type.")
        :blame-form ~form
        :original-body ~bodys})
     ^::freeze
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
     ^::freeze
     (check-expected
       nil
       {:msg-fn (fn [_#]
                  "This 'when-not' expression returns nil if the test is true, which does not agree with the expected type.")
        :blame-form ~form})
     ^::freeze
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
		`^::freeze
     (let [temp# ~tst]
			 (if temp#
				 ^::freeze
         (let [_# ^::freeze (check-let-destructure-no-op
                              {:binding ~form
                               :expression ~tst})
               ;TODO avoid repeated destructuring checks ^::no-check-destructure
               ~form temp#]
					 ~then)
         ~(if (= 3 (count original-form))
            `^::freeze
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
  ^::freeze
  `(if-let ~test
     ^::freeze
     (check-if-empty-body
       (do ~@bodys)
       {:msg-fn (fn [_#]
                  "This 'when-let' expression returns nil if the test is true, which does not agree with the expected type.")
        :blame-form ~form
        :original-body ~bodys})
     ^::freeze
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
                             (= (count bindings) 0) `^::freeze (check-if-empty-body
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
													 `^::freeze
                            (when-not ~x
                              (throw (new AssertionError (str "Assert failed: " (pr-str '~x)))))))
                        ([x message]
                         (when-not erase-assert?
													 `^::freeze
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
  (let [name (first sigs)
        sigs (if (symbol? sigs) (next sigs) sigs)
        {original-sigs :sigs, :keys [single-arity-syntax?]} (parse-fn-sigs (next original-form))
        unexpand-sig (fn [[params [_let_ dbindings & body]] old-sig]
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
                         (prn "body" body)
                         `(~fn-params
                            ~@(when-not (:conds-from-params-meta? old-sig)
                                (when (seq pre-post-meta-map)
                                  [pre-post-meta-map]))
                            ~@(splice-checked-body-forms body))))]
    (list* (first original-form)
           (concat (when name [name])
                   ((if single-arity-syntax? first identity)
                    (map unexpand-sig sigs original-sigs))))))

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
                           assert-form (fn [p] `^::freeze (assert ~p))]
                       `(~fn*-params
                         ^::freeze
                         (let [~@(mapcat (fn [param gsym]
                                           (when-not (= '& param)
                                             [param gsym]))
                                         params
                                         gsyms)]
                           ~@(map assert-form pre)
                           ~(let [body `^::freeze (check-if-empty-body
                                                    (do ~@body)
                                                    {:msg-fn (fn [_#]
                                                               (str "This 'fn' body returns nil, "
                                                                    "which does not agree with the expected type."))
                                                     :blame-form ~sig-form
                                                     :original-body ~body})]
                              (if post
                                `^::freeze (let [~'% ~body]
                                             ~@(map assert-form post)
                                             ~'%)
                                body))))))]
    `(fn* ~@(when name [name])
          ~@(map expand-sig sigs))))

(defmacro check-for-seq [{:keys [expr]}]
  (throw (Exception. "Cannot expand check-for-seq")))

(defmethod -expand-macro `check-for-seq [{:keys [expr]}]
  `(rand-nth (seq expr)))

(def clojure-core-for-expansions
  {:reduce-based {:expand-macro 
                  (fn [[_ seq-forms body-form :as form] _]
                    (let [acc (gensym "acc")]
                      (reduce
                        (fn [body [expr binding]]
                          (case binding
                            :let `(let ~expr ~body)
                            :when `(if ~expr ~body ~acc)
                            :while `(if ~expr ~body (reduced ~acc))
                            (if (keyword? binding)
                              (throw (Exception. (str "Invalid 'for' keyword: " binding)))
                              `(reduce (fn [~acc ~binding] ~body) ~acc ~expr))))
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
;  {:typed {:expand-macro 
;           (fn [[_ seq-forms body-form :as form] {:keys [:clojure.core.typed/type-opts]}]
;             (reduce
;               (fn [body [expr binding]]
;                 (->
;                   (case binding
;                     :let `(let ~expr ~body)
;                     (:while :when) `(when ~expr ~body)
;                     `(let [~binding ^::freeze (check-for-seq
;                                                 {:expr ~expr
;                                                  :binding ~binding})]
;                        ~body))
;                   (with-meta {::pre/freeze true})))
;               `[^::freeze (check-for-expected
;                             {:expr ~body-form
;                              :expected ~(-> type-opts :expected)})]
;               (partition 2 (rseq seq-forms))))
})

(defmethod -unexpand-macro 'clojure.core/for
  [& args]
  (apply (-> clojure-core-for-expansions :reduce-based :unexpand-macro) args))

(defmethod -expand-macro 'clojure.core/for
  [& args]
  (apply (-> clojure-core-for-expansions :reduce-based :expand-macro) args))

(defn unexpand-ast [vsym ast]
  (unexpand-macro (emit-form/emit-form ast) {:vsym vsym}))

(defn freeze-macro [op form env]
  (let [^Var v (u/resolve-sym op env)
        _ (assert (var? v))
        sym (symbol (-> v .ns ns-name str)
                    (-> v .sym str))
        env (assoc env :thread-bindings (get-thread-bindings))
        expanded-form (expand-macro form {:vsym sym})
        _ (prn "expanded-form" expanded-form)
        {:keys [tag] :as expanded} (thaw-form expanded-form env)
        unexpanded-form (unexpand-macro (emit-form/emit-form expanded)
                                        {:vsym sym :original-form form})]
    {:op :frozen-macro
     :form unexpanded-form
     :unexpanded-form unexpanded-form
     :expanded-form expanded-form
     :macro v
     :tag tag
     :env env}))

(defn macroexpand-1
  "If form represents a macro form or an inlineable function, returns its expansion,
   else returns form."
  ([form] (macroexpand-1 form (taj/empty-env)))
  ([form env]
       (cond

        (seq? form)
        (let [[op & args] form]
          (if (specials op)
            form
            (let [v (u/resolve-sym op env)
                  m (meta v)
                  local? (-> env :locals (get op))
                  macro? (and (not local?) (:macro m)) ;; locals shadow macros
                  inline-arities-f (:inline-arities m)
                  inline? (and (not local?)
                               (or (not inline-arities-f)
                                   (inline-arities-f (count args)))
                               (:inline m))
                  t (:tag m)]
              (cond

               macro?
               (let [res (apply v form (:locals env) (rest form))] ; (m &form &env & args)
                 (if (u/obj? res)
                   (vary-meta res merge (meta form))
                   res))

               inline?
               (let [res (apply inline? args)]
                 (if (u/obj? res)
                   (vary-meta res merge
                              (and t {:tag t})
                              (meta form))
                   res))

               :else
               (taj/desugar-host-expr form env)))))

        (symbol? form)
        (taj/desugar-symbol form env)

        :else
        form)))

;;redefine passes mainly to move dependency on `uniquify-locals`
;; to `uniquify2/uniquify-locals`

(defn add-binding-atom
  "Adds an atom-backed-map to every local binding,the same
   atom will be shared between all occurences of that local.

   The atom is put in the :atom field of the node."
  {:pass-info {:walk :pre :depends #{#'uniquify2/uniquify-locals}
               :state (fn [] (atom {}))}}
  [state ast]
  (add-binding-atom/add-binding-atom state ast))

(defn fix-case-test
  "If the node is a :case-test, annotates in the atom shared
  by the binding and the local node with :case-test"
  {:pass-info {:walk :pre :depends #{#'add-binding-atom}}}
  [& args]
  (apply fix-case-test/fix-case-test args))

(defn infer-tag
  "Performs local type inference on the AST adds, when possible,
   one or more of the following keys to the AST:
   * :o-tag      represents the current type of the
                 expression represented by the node
   * :tag        represents the type the expression represented by the
                 node is required to have, possibly the same as :o-tag
   * :return-tag implies that the node will return a function whose
                 invocation will result in a object of this type
   * :arglists   implies that the node will return a function with
                 this arglists
   * :ignore-tag true when the node is untyped, does not imply that
                 all untyped node will have this

  Passes opts:
  * :infer-tag/level  If :global, infer-tag will perform Var tag
                      inference"
  {:pass-info {:walk :post :depends #{#'annotate-tag/annotate-tag 
                                      #'annotate-host-info/annotate-host-info 
                                      #'fix-case-test 
                                      #'analyze-host-expr/analyze-host-expr} 
               ; trim is incompatible with core.typed
               #_#_:after #{#'trim}}}
  [& args]
  (apply infer-tag/infer-tag args))

(defn validate
  "Validate tags, classes, method calls.
   Throws exceptions when invalid forms are encountered, replaces
   class symbols with class objects.

   Passes opts:
   * :validate/throw-on-arity-mismatch
      If true, validate will throw on potential arity mismatch
   * :validate/wrong-tag-handler
      If bound to a function, will invoke that function instead of
      throwing on invalid tag.
      The function takes the tag key (or :name/tag if the node is :def and
      the wrong tag is the one on the :name field meta) and the originating
      AST node and must return a map (or nil) that will be merged into the AST,
      possibly shadowing the wrong tag with Object or nil.
   * :validate/unresolvable-symbol-handler
      If bound to a function, will invoke that function instead of
      throwing on unresolvable symbol.
      The function takes three arguments: the namespace (possibly nil)
      and name part of the symbol, as symbols and the originating
      AST node which can be either a :maybe-class or a :maybe-host-form,
      those nodes are documented in the tools.analyzer quickref.
      The function must return a valid tools.analyzer.jvm AST node."
  {:pass-info {:walk :post :depends #{#'infer-tag
                                      #'analyze-host-expr/analyze-host-expr
                                      ;; validate-recur doesn't seem to play nicely with core.async/go
                                      #_#'validate-recur/validate-recur}}}
  [& args]
  (apply validate/validate args))

(defn box
  "Box the AST node tag where necessary"
  {:pass-info {:walk :pre :depends #{#'infer-tag} 
               :after #{#'validate}}}
  [& args]
  (apply box/box args))

(defn validate-loop-locals
  "Returns a pass that validates the loop locals, calling analyze on the loop AST when
   a mismatched loop-local is found"
  {:pass-info {:walk :post :depends #{#'validate} 
               :affects #{#'analyze-host-expr/analyze-host-expr
                          #'infer-tag
                          #'validate}
               :after #{#'classify-invoke/classify-invoke}}}
  [& args]
  (apply validate-loop-locals/validate-loop-locals args))

(defn classify-invoke
  "If the AST node is an :invoke, check the node in function position,
   * if it is a keyword, transform the node in a :keyword-invoke node;
   * if it is the clojure.core/instance? var and the first argument is a
     literal class, transform the node in a :instance? node to be inlined by
     the emitter
   * if it is a protocol function var, transform the node in a :protocol-invoke
     node
   * if it is a regular function with primitive type hints that match a
     clojure.lang.IFn$[primitive interface], transform the node in a :prim-invoke
     node"
  {:pass-info {:walk :post :depends #{#'validate}}} ;; use this validate
  [& args]
   (apply classify-invoke/classify-invoke args))

(defn compile-passes [pre-passes post-passes info]
  (let [with-state (filter (comp :state info) (concat pre-passes post-passes))
        state      (zipmap with-state (mapv #(:state (info %)) with-state))

        pfns-fn    (fn [passes direction]
                     (reduce (fn [f p]
                               (let [i (info p)
                                     p (cond
                                         (:state i)
                                         (fn [_ s ast] 
                                           ;(prn (str "before state " direction " pass" p))
                                           ;(clojure.pprint/pprint ast)
                                           (let [ast (p (s p) ast)]
                                             ;(prn (str "after state " direction " pass" p))
                                             ;(clojure.pprint/pprint ast)
                                             ast))
                                         (:affects i)
                                         (fn [a _ ast]
                                           (assert nil "affects not allowed, single pass only")
                                           ;(prn (str "before affects " direction " pass" p))
                                           ;(clojure.pprint/pprint ast)
                                           (let [ast ((p a) ast)]
                                             ;(prn (str "after affects " direction " pass" p))
                                             ;(clojure.pprint/pprint ast)
                                             ast))
                                         :else
                                         (fn [_ _ ast] 
                                           ;(prn (str "before normal " direction " pass" p))
                                           ;(prn (:op ast) (emit-form/emit-form ast))
                                           (let [ast (p ast)]
                                             ;(prn (str "after normal " direction " pass" p))
                                             ;(prn (:op ast) (emit-form/emit-form ast))
                                             ast)))]
                                 (fn [a s ast]
                                   (p a s (f a s ast)))))
                             (fn [_ _ ast] ast)
                             passes))
        pre-pfns  (pfns-fn pre-passes :pre)
        post-pfns  (pfns-fn post-passes :post)]
    (fn analyze [ast]
      (ast/walk ast
                (partial pre-pfns analyze (u/update-vals state #(%)))
                (partial post-pfns analyze (u/update-vals state #(%)))))))

(defn schedule
  "Takes a set of Vars that represent tools.analyzer passes and returns a function
   that takes an AST and applies all the passes and their dependencies to the AST,
   trying to compose together as many passes as possible to reduce the number of
   full tree traversals.

   Each pass must have a :pass-info element in its Var's metadata and it must point
   to a map with the following parameters (:before, :after, :affects and :state are
   optional):
   * :after    a set of Vars, the passes that must be run before this pass
   * :before   a set of Vars, the passes that must be run after this pass
   * :depends  a set of Vars, the passes this pass depends on, implies :after
   * :walk     a keyword, one of:
                 - :none if the pass does its own tree walking and cannot be composed
                         with other passes
                 - :post if the pass requires a postwalk and can be composed with other
                         passes
                 - :pre  if the pass requires a prewalk and can be composed with other
                         passes
                 - :any  if the pass can be composed with other passes in both a prewalk
                         or a postwalk
   * :affects  a set of Vars, this pass must be the last in the same tree traversal that all
               the specified passes must partecipate in
               This pass must take a function as argument and return the actual pass, the
               argument represents the reified tree traversal which the pass can use to
               control a recursive traversal, implies :depends
   * :state    a no-arg function that should return an atom holding an init value that will be
               passed as the first argument to the pass (the pass will thus take the ast
               as the second parameter), the atom will be the same for the whole tree traversal
               and thus can be used to preserve state across the traversal
   An opts map might be provided, valid parameters:
   * :debug?   if true, returns a vector of the scheduled passes rather than the concrete
               function"
  [passes & [opts]]
  {:pre [(set? passes)
         (every? var? passes)]}
  (let [info        (@#'passes/indicize (mapv (fn [p] (merge {:name p} (:pass-info (meta p)))) passes))
        passes+deps (into passes (mapcat :depends (vals info)))]
    (if (not= passes passes+deps)
      (recur passes+deps [opts])
      (let [[{pre-passes  :passes :as pre}
             {post-passes :passes :as post}
             :as ps]
            (-> (passes/schedule-passes info)
                (update-in [0 :passes] #(vec (cons #'jpre/pre-analyze %))))

            _ (assert (= 2 (count ps)))
            _ (assert (= :pre (:walk pre)))
            _ (assert (= :post (:walk post)))]
        (if (:debug? opts)
          (mapv #(select-keys % [:passes :walk]) ps)
          (compile-passes pre-passes post-passes info))))))

(def default-passes
  "Set of passes that will be run by default on the AST by #'run-passes"
  ;taj/default-passes
  #{;#'warn-on-reflection
    ;#'warn-earmuff

    #'uniquify2/uniquify-locals

;KEEP
    #'source-info/source-info
    #'elide-meta/elide-meta
    #'constant-lift/constant-lift
;KEEP

    ; not compatible with core.typed
    ;#'trim/trim

    ; FIXME is this needed? introduces another pass
    ; TODO does this still introduce another pass with `uniquify2/uniquify-locals`?
    ;#'box
    ;#'box/box

;KEEP
    #'analyze-host-expr/analyze-host-expr
    ;#'validate-loop-locals
    #'validate
    #'infer-tag
;KEEP

;KEEP
    #'classify-invoke
;KEEP
    })

(def scheduled-default-passes
  (schedule default-passes))

(comment
  (clojure.pprint/pprint
    (schedule default-passes
                     {:debug? true}))
  )

(defn ^:dynamic run-passes
  "Function that will be invoked on the AST tree immediately after it has been constructed,
   by default runs the passes declared in #'default-passes, should be rebound if a different
   set of passes is required.

   Use #'clojure.tools.analyzer.passes/schedule to get a function from a set of passes that
   run-passes can be bound to."
  [ast]
  (scheduled-default-passes ast))

(def default-passes-opts
  "Default :passes-opts for `analyze`"
  {:collect/what                    #{:constants :callsites}
   :collect/where                   #{:deftype :reify :fn}
   :collect/top-level?              false
   :collect-closed-overs/where      #{:deftype :reify :fn :loop :try}
   :collect-closed-overs/top-level? false})

(defn analyze
  "Analyzes a clojure form using tools.analyzer augmented with the JVM specific special ops
   and returns its AST, after running #'run-passes on it.

   If no configuration option is provides, analyze will setup tools.analyzer using the extension
   points declared in this namespace.

   If provided, opts should be a map of options to analyze, currently the only valid
   options are :bindings and :passes-opts (if not provided, :passes-opts defaults to the
   value of `default-passes-opts`).
   If provided, :bindings should be a map of Var->value pairs that will be merged into the
   default bindings for tools.analyzer, useful to provide custom extension points.
   If provided, :passes-opts should be a map of pass-name-kw->pass-config-map pairs that
   can be used to configure the behaviour of each pass.

   E.g.
   (analyze form env {:bindings  {#'ana/macroexpand-1 my-mexpand-1}})"
  ([form] (analyze form (taj/empty-env) {}))
  ([form env] (analyze form env {}))
  ([form env opts]
     (with-bindings (merge {Compiler/LOADER     (RT/makeClassLoader)
                            #'ana/macroexpand-1 macroexpand-1
                            #'ana/freeze-macro? freeze-macro?
                            #'ana/freeze-macro  freeze-macro
                            #'ana/create-var    taj/create-var
                            ;#'ana/parse         parse
                            #'pre/pre-parse  jpre/pre-parse
                            #'pre/expand-macro   expand-macro
                            #'pre/unexpand-macro unexpand-macro
                            #'ana/var?          var?
                            #'*ns*              (the-ns (:ns env))}
                           (:bindings opts))
       (env/ensure (taj/global-env)
         (doto (env/with-env (u/mmerge (env/deref-env) {:passes-opts (get opts :passes-opts default-passes-opts)})
                 (run-passes (pre/pre-analyze-child form env)))
           (do (taj/update-ns-map!)))))))

(defn thaw-frozen-macro [{:keys [op form env] :as expr}]
  {:pre [(= :frozen-macro op)]}
  (let [thread-bindings (or (:thread-bindings env) {})]
    (with-bindings thread-bindings
      (let [env (dissoc env :thread-bindings)]
        (analyze (macroexpand-1 form env) env
                 {:bindings thread-bindings})))))

(defn thaw-form [form env]
  {:pre []}
  (analyze form (dissoc env :thread-bindings)
           {:bindings (:thread-bindings env)}))

(defn rerun-passes [{:keys [env] :as ast}]
  (let [thread-bindings (:thread-bindings env)]
    (assert (map? thread-bindings))
    (with-bindings thread-bindings
      (doto (run-passes ast)
        (do (taj/update-ns-map!))))))

(deftype ExceptionThrown [e ast])

(defn ^:private throw! [e]
  (throw (.e ^ExceptionThrown e)))

(defmethod emit-form/-emit-form :unanalyzed
  [{:keys [analyzed-atom form] :as ast} opts]
  (if-some [ast @analyzed-atom]
    (emit-form/emit-form ast)
    (do (assert (not (#{:hygienic :qualified-symbols} opts))
                "Cannot support emit-form options on unanalyzed form")
        #_(throw (Exception. "Cannot emit :unanalyzed form"))
        (prn (str "WARNING: emit-form: did not analyze: " form))
        form)))

(defmethod emit-form/-emit-form :frozen-macro
  [{:keys [form] :as ast} opts]
  (do (assert (not (#{:hygienic :qualified-symbols} opts))
              "Cannot support emit-form options on :frozen-macro form")
      form))

(defn eval-ast [a {:keys [handle-evaluation-exception] 
                   :or {handle-evaluation-exception throw!}
                   :as opts}]
  (let [frm (emit-form/emit-form a)
        ;_ (prn "frm" frm)
        result (try (eval frm) ;; eval the emitted form rather than directly the form to avoid double macroexpansion
                    (catch Exception e
                      (handle-evaluation-exception (ExceptionThrown. e a))))]
    (merge a {:result result})))

(defn analyze+eval
  "Like analyze but evals the form after the analysis and attaches the
   returned value in the :result field of the AST node.

   If evaluating the form will cause an exception to be thrown, the exception
   will be caught and wrapped in an ExceptionThrown object, containing the
   exception in the `e` field and the AST in the `ast` field.

   The ExceptionThrown object is then passed to `handle-evaluation-exception`,
   which by defaults throws the original exception, but can be used to provide
   a replacement return value for the evaluation of the AST.

   Unrolls `do` forms to handle the Gilardi scenario.

   Useful when analyzing whole files/namespaces."
  ([form] (analyze+eval form (taj/empty-env) {}))
  ([form env] (analyze+eval form env {}))
  ([form env {:keys [additional-gilardi-condition
                     eval-fn
                     annotate-do
                     statement-opts-fn
                     analyze-opts-fn
                     analyze-env-fn]
              :or {additional-gilardi-condition (fn [_] true)
                   eval-fn eval-ast
                   annotate-do (fn [a _ _] a)
                   statement-opts-fn identity
                   analyze-opts-fn identity
                   analyze-env-fn identity}
              :as opts}]
     (env/ensure (taj/global-env)
       (taj/update-ns-map!)
       (let [env (merge env (u/-source-info form env))
             [mform raw-forms] (with-bindings {Compiler/LOADER     (RT/makeClassLoader)
                                               #'*ns*              (the-ns (:ns env))
                                               #'ana/macroexpand-1 (get-in opts [:bindings #'ana/macroexpand-1] 
                                                                           macroexpand-1)
                                               #'frozen-macros     (get-in opts [:bindings #'frozen-macros] 
                                                                           frozen-macros)
                                               #'ana/freeze-macro? (get-in opts [:bindings #'ana/freeze-macro?] 
                                                                           freeze-macro?)}
                                 (loop [form form raw-forms []]
                                   (let [freeze? (when (seq? form)
                                                   (ana/freeze-macro? (first form) form env))
                                         mform (if freeze?
                                                 form
                                                 (ana/macroexpand-1 form env))]
                                     (if (= mform form)
                                       [mform (seq raw-forms)]
                                       (recur mform (conj raw-forms
                                                          (if-let [[op & r] (and (seq? form) form)]
                                                            (if (or (ju/macro? op  env)
                                                                    (ju/inline? op r env))
                                                              (vary-meta form assoc ::ana/resolved-op (u/resolve-sym op env))
                                                              form)
                                                            form)))))))]
         (if (and (seq? mform) (= 'do (first mform)) (next mform)
                  (additional-gilardi-condition mform))
           ;; handle the Gilardi scenario
           (let [[statements ret] (u/butlast+last (rest mform))
                 statements-expr (mapv (fn [s] (analyze+eval s (-> env
                                                                (u/ctx :ctx/statement)
                                                                (assoc :ns (ns-name *ns*)))
                                                            (statement-opts-fn opts)))
                                       statements)
                 ret-expr (analyze+eval ret (assoc env :ns (ns-name *ns*)) opts)]
             (annotate-do
               {:op         :do
                :top-level  true
                :form       mform
                :statements statements-expr
                :ret        ret-expr
                :children   [:statements :ret]
                :env        env
                :result     (:result ret-expr)
                :raw-forms  raw-forms}
               statements-expr
               ret-expr))
           (let [a (analyze mform (analyze-env-fn env) (analyze-opts-fn opts))
                 e (eval-fn a opts)]
             (merge e {:raw-forms raw-forms})))))))
