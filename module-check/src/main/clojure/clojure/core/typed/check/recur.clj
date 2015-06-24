(ns clojure.core.typed.check.recur
  (:require [clojure.core.typed.utils :as u]
            [clojure.core.typed.type-rep :as r]
            [clojure.core.typed.util-vars :as vs]
            [clojure.core.typed.check.recur-utils :as recur-u]
            [clojure.core.typed.errors :as err]
            [clojure.core.typed.current-impl :as impl]
            [clojure.core.typed.type-ctors :as c]))

;Arguments passed to recur must match recur target exactly. Rest parameter
;equals 1 extra argument, either a Seqable or nil.
(defn check-recur [args env recur-expr expected check]
  (binding [vs/*current-env* env]
    (let [{:keys [dom rest] :as recur-target} (if-let [r recur-u/*recur-target*]
                                                r
                                                (err/int-error (str "No recur target")))
          _ (assert (not ((some-fn :drest :kw) recur-target)) "NYI")
          fixed-args (if rest
                       (butlast args)
                       args)
          rest-arg (when rest
                     (last args))
          rest-arg-type (when rest-arg
                          (impl/impl-case
                            :clojure (c/Un r/-nil (c/In (c/RClass-of clojure.lang.ISeq [rest])
                                                        (r/make-CountRange 1)))
                             :cljs (c/Un r/-nil (c/In (c/Protocol-of 'cljs.core/ISeq [rest])
                                                      (r/make-CountRange 1)))))
          cargs (mapv check args (map r/ret
                                      (concat dom 
                                              (when rest-arg-type
                                                [rest-arg-type]))))
          _ (when-not (and (= (count fixed-args) (count dom))
                           (= (boolean rest) (boolean rest-arg)))
              (err/tc-delayed-error 
                (str "Wrong number of arguments to recur:"
                     " Expected: " ((if rest inc identity) 
                                    (count dom))
                     " Given: " ((if rest-arg inc identity)
                                 (count fixed-args)))))]
      (assoc recur-expr
             :exprs cargs
             u/expr-type (r/ret (c/Un))))))
