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

(defn freeze-macro? [op env]
  ;(prn "freeze-macro?" op)
  (boolean
    (when (symbol? op)
      (when-not (specials op)
        (let [^Var v (u/resolve-sym op env)]
          (when (var? v)
            (let [vsym (symbol (str (ns-name (.ns v)))
                               (str (.sym v)))]
              (contains? frozen-macros vsym))))))))

(declare thaw-form rerun-passes)

(defmulti -reconstruct-form (fn [{:keys [vsym]}] vsym))
(defmulti -reconstruct-tag (fn [{:keys [vsym]}] vsym))

(def reconstruct-form -reconstruct-form)
(def reconstruct-tag -reconstruct-tag)

(defmulti -freeze-macro (fn [op form env] op))

(defn reconstruct-tag+form [expr]
  (let [tag (reconstruct-tag expr)
        form (reconstruct-form expr)]
    (merge (assoc expr :form form)
           (when tag
             {:tag tag}))))

(defmethod -reconstruct-tag 'clojure.core/let
  [{[_ body] :args}]
  (:tag body))

(defn do-form? [form]
  (and (seq? form)
       (= 'do (first form))))

(defn thaw-synthetic-body-forms [body-forms env]
  (thaw-form `(do ~@body-forms) env))

;; preserves empty bodies like (let []), even if
;; they are expanded to (do nil), preventing (let [] nil)
(defn splice-body-forms [original-body new-do-body]
  {:pre [(do-form? new-do-body)]}
  (when (seq original-body) (rest new-do-body)))

(defn let-bindings-info [{:keys [args op vsym]}]
  {:pre [(= :frozen-macro op)
         (= 'clojure.core/let vsym)]
   :post [(vector? %)
          (every? map? %)]}
  (first args))

(defn let-body [{:keys [args op vsym]}]
  {:pre [(= :frozen-macro op)
         (= 'clojure.core/let vsym)]
   :post [(map? %)
          (= :do (:op %))]}
  (second args))

;; throw away precalculated destructuring
(defn emit-bindings-info [bindings-form bindings-info]
  {:pre [(vector? bindings-form)
         (vector? bindings-info)]
   :post [(vector? %)]}
  (into (empty bindings-form)
        (mapcat (juxt :b-form (comp emit-form/emit-form :init)))
        bindings-info))

(defn emit+splice-body-forms [old-body-forms body]
  (splice-body-forms old-body-forms (emit-form/emit-form body)))

(defmethod -reconstruct-form 'clojure.core/let
  [{[mform bindings-form & body-forms] :form
    [bindings-info body] :args}]
  (list* mform
         (emit-bindings-info bindings-form bindings-info)
         (emit+splice-body-forms body-forms body)))

(defmethod -freeze-macro 'clojure.core/let
  [vsym [_ bindings-form & body-forms :as form] env]
  (let [_ (assert (and (vector? bindings-form) (even? (count bindings-form))))
        [env bindings-info]
        (reduce
          (fn [[env bindings-info] [b-form old-init-form]]
            (let [;; macroexpand up to frozen macros
                  init (thaw-form old-init-form env)
                  ;; emit to plug into `destructure`
                  init-form (emit-form/emit-form init)
                  ;; simulate the destructuring of b-form to gather :tag
                  ;; and :locals information.
                  [env d-bindings] (reduce (fn [[env d-bindings] [b-form init-form]]
                                             {:pre [(map? env)
                                                    (vector? d-bindings)]
                                              :post [(vector? %)]}
                                             (let [{unhygienic-name :form :keys [env] :as expr}
                                                   (rerun-passes
                                                     {:op :binding
                                                      :env env
                                                      :local :let
                                                      :init (pre/pre-analyze-child init-form env)
                                                      :form b-form
                                                      :name b-form
                                                      :children [:init]})]
                                               ;; FIXME many of these names will pollute the local environment
                                               ;; we eventually return, since we return forms that
                                               ;; undo the expansion of this simulated `destructure`.
                                               [(assoc-in env [:locals unhygienic-name] (dissoc expr :env))
                                                (conj d-bindings expr)]))
                                           [env []]
                                           (partition 2 (destructure [b-form init-form])))
                  _ (assert (map? env))
                  _ (assert (vector? d-bindings))]
              ;; remember original destructuring lhs (b-form) and analyzed rhs (init)
              [env (conj bindings-info {:init init
                                        :b-form b-form 
                                        :d-bindings d-bindings})]))
          [env []]
          (partition 2 bindings-form))
        body (thaw-synthetic-body-forms body-forms env)
        args [bindings-info body]]
    (-> 
      {:op :frozen-macro
       :env env
       :args args
       :vsym vsym
       :form form}
      reconstruct-tag+form)))

(defn when-test [{[wexpr] :args}]
  {:post [(map? %)]}
  (:test wexpr))

(defn when-then-body [{[wexpr] :args}]
  {:post [(= :do (:op %))]}
  (:then wexpr))

(defmethod -reconstruct-form 'clojure.core/when
  [{[mform test-form & then-forms] :form :as wexpr}]
  (list* mform 
         (emit-form/emit-form (when-test wexpr))
         (splice-body-forms then-forms
                            (emit-form/emit-form
                              (when-then-body wexpr)))))

(defmethod -reconstruct-tag 'clojure.core/when
  [{[wexpr] :args}]
  (:tag wexpr))

(defmethod -freeze-macro 'clojure.core/when
  [vsym [_ test-form & body-form :as form] env]
  ;; TODO spec check macro first
  (assert (<= 2 (count form)))
  (let [wexpr (thaw-form `(if ~test-form (do ~@body-form)) env)
        args [wexpr]]
    (-> 
      {:op :frozen-macro
       :env env
       :args args
       :vsym vsym
       :form form}
      reconstruct-tag+form)))

(defn when-not-test [{[wnot-expand] :args}]
  {:pre [(= :if (:op wnot-expand))]}
  (:test wnot-expand))

(defn when-not-then-body [{[wnot-expand] :args}]
  ;; branches are flipped
  (:else wnot-expand))

(defmethod -reconstruct-form 'clojure.core/when-not
  [{[mform test-form & body] :form :as wnot}]
  (list* mform
         (emit-form/emit-form (when-not-test wnot))
         (splice-body-forms body (emit-form/emit-form (when-not-then-body wnot)))))

(defmethod -reconstruct-tag 'clojure.core/when-not
  [{[wnot-expand] :args}]
  (:tag wnot-expand))

(defmethod -freeze-macro 'clojure.core/when-not
  [vsym [_ test-form & body-form :as form] env]
  ;; TODO spec check macro first
  (assert (<= 2 (count form)))
  (let [wnot-expand (thaw-form `(if ~test-form nil (do ~@body-form)) env)
        args [wnot-expand]]
    (-> 
      {:op :frozen-macro
       :env env
       :args args
       :vsym vsym
       :form form}
      reconstruct-tag+form)))

(declare freeze-macro)

(defn when-let-bindings-info [wlet]
  (let [binding-info (-> wlet let-bindings-info first)
        inner-binding-info (-> wlet let-body :ret when-then-body :ret let-bindings-info first)]
    [(assoc inner-binding-info
            :init (:init binding-info))]))

(defn when-let-then [wlet]
  {:post [(map? %)]}
  (-> wlet let-body :ret when-then-body :ret let-body))

(defmethod -reconstruct-form 'clojure.core/when-let
  [{[mform bindings-form & body-forms] :form
    [wlet] :args}]
  (list* mform
         (emit-bindings-info bindings-form (when-let-bindings-info wlet))
         (emit+splice-body-forms body-forms (when-let-then wlet))))

(defmethod -reconstruct-tag 'clojure.core/when-let
  [{[wlet] :args}]
  (:tag wlet))

(defmethod -freeze-macro 'clojure.core/when-let
  [vsym [_ [b-form tst-form :as bindings-form] & then-forms :as form] env]
  (let [_ (assert (and (vector? bindings-form) (= 2 (count bindings-form))))
        wlet (thaw-form `(let [temp# ~tst-form]
                           (when temp#
                             (let [~b-form temp#]
                               ~@then-forms)))
                        env)
        args [wlet]]
    (-> 
      {:op :frozen-macro
       :env env
       :args args
       :vsym vsym
       :form form}
      reconstruct-tag+form)))

(defn if-let-bindings-info [ilet]
  (let [binding-info (-> ilet let-bindings-info first)
        inner-binding-info (-> ilet let-body :ret :then let-bindings-info first)]
    [(assoc inner-binding-info
            :init (:init binding-info))]))

(defn if-let-then [ilet]
  {:post [(map? %)]}
  (-> ilet let-body :ret :then let-body :ret))

(defn if-let-else [ilet]
  {:post [(map? %)]}
  (-> ilet let-body :ret :else))

(defmethod -reconstruct-form 'clojure.core/if-let
  [{[mform bindings-form & then+else-forms :as form] :form
    [wlet] :args}]
  (list* mform
         (emit-bindings-info bindings-form (if-let-bindings-info wlet))
         (emit-form/emit-form (if-let-then wlet))
         (when (= 4 (count form))
           [(emit-form/emit-form (if-let-else wlet))])))

(defmethod -reconstruct-tag 'clojure.core/if-let
  [{[ilet] :args}]
  (:tag ilet))

(defmethod -freeze-macro 'clojure.core/if-let
  [vsym [_ [b-form tst-form :as bindings-form] then-form else-form :as form] env]
  (let [_ (assert (#{3 4} (count form)))
        else-provided? (= 4 (count form))
        _ (assert (and (vector? bindings-form) (= 2 (count bindings-form))))
        ilet (thaw-form `(let [temp# ~tst-form]
                           (if temp#
                             (let [~b-form temp#]
                               ~then-form)
                             ~else-form))
                        env)
        args [ilet]]
    (-> 
      {:op :frozen-macro
       :env env
       :args args
       :vsym vsym
       :form form}
      reconstruct-tag+form)))

(defn with-open-bindings-info+body [{:keys [form] :as wopen}]
  {:pre [(map? wopen)]
   :post [(vector? (first %))
          (every? map? (first %))
          (= :do (-> % second :op)) (-> % second ((juxt :vsym :op)))]}
  (assert form form)
  (let [bindings-form (second form)
        _ (assert (and (vector? bindings-form)
                       (even? (count bindings-form))))]
    (loop [bindings-info []
           wopen wopen
           nbinds (/ (count bindings-form) 2)]
      (if (zero? nbinds)
        [bindings-info (-> wopen :args first)]
        (recur (into bindings-info (-> wopen :args first let-bindings-info))
               (-> wopen :args first let-body :ret :body :ret)
               (dec nbinds))))))

(defn with-open-bindings-info [wopen]
  (first (with-open-bindings-info+body wopen)))

(defn with-open-body [wopen]
  (second (with-open-bindings-info+body wopen)))

(defmethod -reconstruct-form 'clojure.core/with-open
  [{[mform bindings-form & body-forms] :form
    :as wopen}]
  (let [[bindings-info body] (with-open-bindings-info+body wopen)]
    (list* mform
           (emit-bindings-info bindings-form bindings-info)
           (emit+splice-body-forms body-forms body))))

(defmethod -reconstruct-tag 'clojure.core/with-open
  [{[wopen] :args}]
  (:tag wopen))

(defmethod -freeze-macro 'clojure.core/with-open
  [vsym [_ bindings-form & body-forms :as form] env]
  (let [_ (assert (<= 2 (count form)))
        _ (assert (and (vector? bindings-form) (even? (count bindings-form))))
        wopen (thaw-form 
                (if (zero? (count bindings-form))
                  `(do ~@body-forms)
                  (let [b-form (subvec bindings-form 0 2)
                        _ (assert (symbol? (b-form 0)))]
                    `(let ~b-form
                       (try
                         (with-open ~(subvec bindings-form 2) ~@body-forms)
                         (finally
                           (. ~(bindings-form 0) close))))))
                env)
        args [wopen]]
    (->
      {:op :frozen-macro
       :env env
       :args args
       :vsym vsym
       :form form}
      reconstruct-tag+form)))

(defn erased-assert? [{[erase-assert?] :args}]
  erase-assert?)

(defn assert-has-message? [{:keys [form]}]
  (= 3 (count form)))

(defn assert-test [{[_ exp] :args :as aexpr}]
  {:pre [(not (erased-assert? aexpr))]
   :post [(map? %)]}
  (when-not-test exp))

(defn assert-message [{[_ exp] :args :as aexpr}]
  {:pre [(not (erased-assert? aexpr))
         (assert-has-message? aexpr)]
   :post [(map? %)]}
  (-> exp when-not-then-body :ret :exception :args first :args second))

(defmethod -reconstruct-form 'clojure.core/assert
  [{[mform x message :as form] :form :as aexpr}]
  (if (erased-assert? aexpr)
    form
    (list* mform
           (emit-form/emit-form (assert-test aexpr))
           (when (assert-has-message? aexpr)
             [(emit-form/emit-form (assert-message aexpr))]))))

(defmethod -reconstruct-tag 'clojure.core/assert
  [{[exp] :args}]
  (:tag exp))

(defmethod -freeze-macro 'clojure.core/assert
  [vsym [_ x message :as form] env]
  (let [_ (assert (#{2 3} (count form)))
        msg? (= 3 (count form))
        erase-assert? (not *assert*)
        assert-expand (fn
                        ([x]
                         (when-not erase-assert?
                           `(when-not ~x
                              (throw (new AssertionError (str "Assert failed: " (pr-str '~x)))))))
                        ([x message]
                         (when-not erase-assert?
                           `(when-not ~x
                              (throw (new AssertionError (str "Assert failed: " ~message "\n" (pr-str '~x))))))))
        exp (thaw-form (apply assert-expand (rest form)) env)
        args [erase-assert? exp]]
    (->
      {:op :frozen-macro
       :env env
       :args args
       :vsym vsym
       :form form}
      reconstruct-tag+form)))

(defn fn-methods [{[fnexpr] :args}]
  {:post [(vector? %)
          (every? (comp #{:fn-method} :op) %)]}
  (:methods fnexpr))

(defn fn-method-body [fn-method]
  (-> fn-method :body :ret))


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
        process-sigs (fn [[params & body]]
                       (assert (vector? params))
                       (let [conds (when (and (next body) (map? (first body)))
                                     (first body))
                             body (if conds (next body) body)
                             conds-from-params-meta? (boolean conds)
                             conds (or conds (meta params))
                             pre (:pre conds)
                             post (:post conds)]
                         {:pre pre
                          :post post
                          :conds-from-params-meta? conds
                          :params params
                          :body body}))]
    {:single-arity-syntax? single-arity-syntax?
     :sigs (mapv process-sigs sigs)
     :name name}))

(defmethod -reconstruct-form 'clojure.core/fn
  [{[mform & sigs :as form] :form
    [fnexpr] :args
    :as fmap}]
  (let [{:keys [single-arity-syntax? sigs name]} (parse-fn-sigs sigs)
        _ (when single-arity-syntax?
            (assert (= 1 (count sigs))))
        sigs (map (fn [method {:keys [pre post params body conds-from-params-meta?]}]
                    (let [[pre-forms body-no-pre-form] (split-at (count pre) (emit-form/emit-form (fn-method-body method)))
                          [post-forms body-no-pre+post-form] (if post
                                                               [(mapv emit-form/emit-form (-> body-no-pre-form let-body :statements butlast))
                                                                (-> body-no-pre-form let-bindings-info first :init)]
                                                               [[] body-no-pre-form])
                          new-meta-map (merge (when pre-form
                                                {:pre pre-form})
                                              (when post-form
                                                {:post post-form}))
                          params (if conds-from-params-meta?
                                   (vary-meta params merge new-meta-map)
                                   params)]
                      (prn "params" params)
                      (prn "body-no-pre+post-form" body-no-pre+post-form)
                      `(~params
                         ~@(when-not conds-from-params-meta?
                             [new-meta-map])
                         ~@(splice-body-forms body (emit-form/emit-form body-no-pre+post-form)))))
                  (fn-methods fmap)
                  sigs)]
    (list* mform
           (concat (when name [name])
                   (if single-arity-syntax?
                     (first sigs)
                     [sigs])))))

(defmethod -reconstruct-tag 'clojure.core/fn
  [_]
  clojure.lang.AFunction)

(defmethod -freeze-macro 'clojure.core/fn
  [vsym [_ & sigs :as form] env]
;; TODO clojure.spec check 
  (let [{:keys [sigs name]} (parse-fn-sigs sigs)
        process-sig (fn [{:keys [pre post params body]}]
                      (assert (vector? params))
                      (let [gsyms (mapv (fn [a]
                                          (if (= '& a)
                                            a
                                            (gensym "a")))
                                        params)]
                      `([~@gsyms]
                         ~@(map (fn [p] `(assert ~p)) pre)
                         (let [~@(mapcat (fn [param gsym]
                                           (when-not (= '& param)
                                             [param gsym]))
                                         params
                                         gsyms)]
                           ~@(if post
                              `((let [~'% (do ~@body)]
                                 ~@(map (fn* [c] `(assert ~c)) post)
                                 ~'%))
                               body)))))
         fnexpr (thaw-form `(fn* ~@(when name [name])
                              ~@(map process-sig sigs))
                           env)
         args [fnexpr]]
    (->
      {:op :frozen-macro
       :env env
       :args args
       :vsym vsym
       :form form}
      reconstruct-tag+form)))

;(defn for-seq-bindings-info+body [{[fexpand] :args
;                                   [_ seq-forms] :form}]
;  (loop [seq-forms (seq seq-forms)
;         seq-bindings-info []
;         fexpand fexpand]
;    (if-not seq-forms
;      [seq-bindings-info fexpand]
;      (let [[binding expr & seq-forms]
;            [seq-bindings-info fexpand]
;            (case binding
;              :let [(conj seq-bindings-info
;                          {:for-op :let 
;                           :bindings-info (let-bindings-info fexpand)})
;                    (let-body fexpand)]
;              (:when :while) [(conj seq-bindings-info
;                                    {:for-op binding 
;                                     :test (:test fexpand)})
;                              (:then fexpand)]
;              [(conj seq-bindings-info
;                     {:for-op binding 
;                      :binding-info {
;                      :test (:test fexpand)})
;               (:then fexpand)]
;
;
;            seq-bindings-info (conj seq-bindings-info
;                                    )]
;        (recur seq-forms


;(defmethod -freeze-macro 'clojure.core/for
;  [vsym [_ seq-forms body-form :as form] env]
;  (let [acc (gensym "acc")
;        out-form (reduce
;                   (fn [body [expr binding]]
;                     (case b
;                       :let `(let ~expr ~body)
;                       :when `(if ~expr ~body ~acc)
;                       :while `(if ~expr ~body (reduced ~acc))
;                       (if (keyword? b)
;                         (err/int-error (str "Invalid 'for' keyword: " b))
;                         `(reduce (fn [~acc ~binding] ~body) ~acc ~expr))))
;                   body-form
;                   (partition 2 (rseq seq-forms)))
;        thawed (thaw-form out-form env)
;        args [thawed]]
;    (->
;      {:op :frozen-macro
;       :env env
;       :args args
;       :vsym vsym
;       :form form}
;      reconstruct-tag+form)))


(defn freeze-macro [op form env]
  (let [^Var v (u/resolve-sym op env)
        _ (assert (var? v))
        sym (symbol (-> v .ns ns-name str)
                    (-> v .sym str))]
    (assoc (-freeze-macro sym form (assoc env :thread-bindings (get-thread-bindings)))
           :macro v)))

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
                                                   (ana/freeze-macro? (first form) env))
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
