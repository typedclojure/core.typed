(ns clojure.core.typed.rules
  (:require [clojure.core.typed :as t]
            [clojure.core.typed.internal :as internal]))

(t/defalias TCType t/Any)
(t/defalias MsgFnOpts (t/HMap))

(t/defalias AST (t/Map t/Any t/Any))

(t/defalias ExprType
  (t/HMap :mandatory
          {;; the type
           :type TCType}
          ;; filter set
          :optional 
          {:filters (t/HMap :optional
                            {:then t/Any
                             :else t/Any})
           ;; the object
           :object t/Any
           ;; the flow filter
           :flow t/Any
           :opts (t/HMap :optional
                         {:msg-fn [MsgFnOpts -> t/Str]
                          :blame-form t/Any})}))

(t/defalias ErrorOpts (t/HMap
                        :optional
                        {:expected (t/U nil ExprType)}))

(t/defalias RuleOpts
  (t/HMap :mandatory
          {; FIXME docs
           :expr AST
           ; FIXME docs
           :opts t/Any
           ;; the fully qualified symbol of the current
           ;; macro being type checked
           :vsym t/Sym
           ;; Map of current tools.analyzer local scope
           :locals (t/Map t/Sym t/Any)
           ;; expected type of the current form
           :expected (t/U nil ExprType)
           ;; (fn [actual maybe-expected] ..)
           ;; if provided, checks actual is compatible with the expected type
           :maybe-check-expected [ExprType (t/U nil ExprType) -> ExprType]
           ;; (fn ([form] ..) ([form expected-type] ..))
           ;; type checks form with an optional expected-type
           :check (t/IFn [t/Any -> ExprType]
                         [t/Any (t/U nil ExprType) -> ExprType])
           ;; (fn [vs f] ..)
           ;; FIXME docs
           ;:solve-subtype [(t/Vec t/Sym) [t/Sym * :-> [TCType TCType]] :-> (t/U nil (t/Map t/Sym TCType))]
           ;; (fn [t1 t2] ..)
           ;; true if t1 is a subtype of t2
           :subtype? [TCType TCType :-> Boolean]
           ;; given a tools.analyzer AST form, returns its Clojure representation
           :emit-form [t/Any :-> t/Any]
           ;; compacts a type so it is suitable to use in an error message
           :abbreviate-type [TCType :-> TCType]
           ;;TODO document
           :expected-error [TCType TCType ErrorOpts :-> t/Any]
           :delayed-error [t/Str ErrorOpts :-> t/Any]
           :internal-error [t/Str ErrorOpts :-> t/Any]
           }))

(t/ann typing-rule [RuleOpts -> '{:op t/Kw, ::expr-type ExprType}])
(defmulti typing-rule (fn [{:keys [vsym]}] vsym))

#_
(defmethod typing-rule 'clojure.core.typed.expand/gather-for-return-type
  [{[_ ret] :form, :keys [expected check solve]}]
  (assert nil "FIXME args etc.")
  (let [{:keys [::expr-type] :as m} (check ret)
        {:keys [x] :as solved?} (solve-subtype '[x]
                                               (fn [x]
                                                 [(:type expr-type) `(t/U nil '[~x])]))
        _ (assert solved?)
        ret {:type `(t/Seq ~x)
             :filters {:else 'ff}}]
    (assoc m ::expr-type ret)))

(defmethod typing-rule 'clojure.core.typed.expand/expected-type-as
  [{:keys [expr opts expected check delayed-error form with-updated-locals]}]
  (let [{:keys [sym msg-fn blame-form]} opts]
    (if expected
      (with-updated-locals {sym (:type expected)}
        #(check expr expected))
      (do
        (delayed-error (if msg-fn
                         ((eval msg-fn) {})
                         "Must provide expected to this expression")
                       {:form (if (contains? opts :blame-form)
                                blame-form
                                form)})
        (assoc expr ::expr-type {:type `t/TCError})))))

;; (solve
;;   coll
;;   {:query (t/All [a] [(t/U nil (t/Seqable a)) :-> a])
;;    :msg-fn (fn [_#]
;;             (str "Argument number " ~(inc i)
;;                  " to 'map' must be Seqable"))
;;    :blame-form ~coll})
(defmethod typing-rule 'clojure.core.typed.expand/solve
  [{:keys [expr opts expected check solve delayed-error form maybe-check-expected]}]
  (let [{:keys [::expr-type] :as m} (check expr)
        {:keys [query msg-fn blame-form]} opts
        res (solve expr-type query)]
    (when-not res
      (let [form (if (contains? opts :blame-form)
                   blame-form
                   form)]
        ;; msg-fn should provide message
        (delayed-error nil (merge {:form form :actual (:type expr-type)}
                                  (select-keys opts [:msg-fn :blame-form])))))
    (assoc m
           ::expr-type (maybe-check-expected
                         (or res {:type `t/TCError})
                         expected))))

(defmethod typing-rule 'clojure.core.typed.expand/require-expected
  [{:keys [expr opts expected check solve delayed-error form maybe-check-expected subtype?]}]
  (let [sub-check (:subtype opts)
        msg-fn (:msg-fn opts)]
    (cond
      (or (not expected)
          (and expected
               (contains? opts :subtype)
               (not (subtype? (:type expected) sub-check))))
      (let [form (if-let [[_ bf] (find opts :blame-form)]
                   bf
                   form)
            msg (if msg-fn
                  ((eval msg-fn) {})
                  (str "An expected type "
                       (when (contains? opts :subtype)
                         (str "which is a subtype of " (pr-str sub-check)))
                       " is required for this expression."))]
        (delayed-error msg {:form form})
        (assoc expr ::expr-type {:type `t/TCError}))

      :else (check expr expected))))

#_
(defmethod typing-rule 'clojure.core.typed.expand/check-for-expected
  [{[_ {:keys [expr expected-local] :as form-opts} :as form] :form,
    :keys [expr opts expected check locals solve-subtype subtype? delayed-error abbreviate-type
           emit-form] :as opt}]
  (assert nil "FIXME update args above and defmacro")
  (assert (not (:expected opt)))
  (let [{:keys [expected-local]} opts
        l (get locals expected-local)
        _ (assert l expected-local)
        [qut expected] (-> l :init emit-form)
        _ (assert (= 'quote qut))
        {:syms [x] :as solved?} (when expected
                                  (solve-subtype '[x]
                                                 (fn [x]
                                                   [(:type expected) `(t/U nil (t/Seqable ~x))])))
        ;; TODO check-below of filters/object/flow
        errored? (when expected
                   (when-not (subtype? `(t/Seq t/Nothing) (:type expected))
                     (delayed-error (str "'for' expression returns a seq, but surrounding context expected it to return "
                                         (pr-str (abbreviate-type (:type expected))))
                                    {:form (:form form-opts)})
                     true))
        _ (assert (or solved? errored? (not expected)))]
    (check expr (when expected
                  (when solved?
                    (when (not errored?)
                      {:type x}))))))

(defmethod typing-rule 'clojure.core.typed.expand/check-expected
  [{:keys [expr opts expected check]}]
  (check expr (when-let [expected (or expected (:default-expected opts))]
                (update expected :opts 
                        ;; earlier messages override later ones
                        #(merge
                           (select-keys opts [:blame-form :msg-fn])
                           %)))))

(defmethod typing-rule 'clojure.core.typed.expand/check-if-empty-body
  [{:keys [expr opts expected check]}]
  (check expr (when expected
                (if (empty? (:original-body opts))
                  (update expected :opts 
                          ;; earlier messages override later ones
                          #(merge
                             (select-keys opts [:blame-form :msg-fn])
                             %))
                  expected))))

(defmethod typing-rule 'clojure.core.typed.expand/type-error
  [{:keys [expr opts delayed-error]}]
  (let [{:keys [msg-fn form]} opts]
    (delayed-error ((eval msg-fn) {}) {:form form})
    (assoc expr ::expr-type {:type `t/TCError})))

(defmethod typing-rule 'clojure.core.typed.expand/with-post-blame-context
  [{:keys [expr opts env expected check]} ]
  (let [ce (check expr expected)]
    (update-in ce [::expr-type :opts]
               ;; earlier messages override later ones
               #(merge
                  (select-keys opts [:blame-form :msg-fn])
                  %))))

#_
(defn ann-form-typing-rule 
  [{:keys [expr opts expected check subtype? expected-error]}]
  ;; FIXME use check-below
  (assert nil "TYPING_RULE ann-form-typing-rule")
  (let [ty (:type opts)
        ;; FIXME I don't think this `form` is initialized and/or used properly here, revisit!!
        form (:form expr)
        _ (when expected
            (when-not (subtype? ty (:type expected))
              (expected-error ty (:type expected)
                              {:expected (update expected :opts
                                                 ;; prefer earlier blame-form
                                                 #(merge {:blame-form form}
                                                         %))})))]
    (check expr (merge expected {:type ty}))))
#_#_
(defmethod typing-rule `t/ann-form [& args] (apply ann-form-typing-rule args))
(defmethod typing-rule 'clojure.core.typed.macros/ann-form [& args] (apply ann-form-typing-rule args))

(defn tc-ignore-typing-rule 
  [{:keys [expr expected maybe-check-expected]}]
  (assoc expr
         ::expr-type (maybe-check-expected
                       {:type `t/Any}
                       expected)))

(defmethod typing-rule `t/tc-ignore [& args] (apply tc-ignore-typing-rule args))
(defmethod typing-rule 'clojure.core.typed.macros/tc-ignore [& args] (apply tc-ignore-typing-rule args))

(defmethod typing-rule 'clojure.core.typed.expand/ignore-expected-if
  [{[_ ignore? body :as form] :form, :keys [expected check]}]
  {:pre [(boolean? ignore?)]}
  (assert nil "FIXME args etc.")
  (check body (when-not ignore? expected)))

(defmethod typing-rule :default
  [{:keys [form internal-error]}]
  (internal-error (str "No such internal form: " form)))
