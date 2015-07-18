(ns clojure.core.typed.check.invoke-kw
  (:require [clojure.core.typed.type-rep :as r]
            [clojure.core.typed.check-below :as below]
            [clojure.core.typed.contract-utils :as con]
            [clojure.core.typed.util-vars :as vs]
            [clojure.core.typed.utils :as u]
            [clojure.core.typed.type-ctors :as c]
            [clojure.core.typed.path-rep :as pe]
            [clojure.core.typed.subtype :as sub]
            [clojure.core.typed.check.utils :as cu]
            [clojure.core.typed.filter-rep :as fl]
            [clojure.core.typed.filter-ops :as fo]
            [clojure.core.typed.object-rep :as obj]
            [clojure.core.typed.parse-unparse :as prs]
            [clojure.core.typed.debug :as b]
            [clojure.core.typed.errors :as err]))

; also copied to clojure.core.typed.update
(defn immutable-lookup? [t]
  {:pre [(r/Type? t)]
   :post [(con/boolean? %)]}
  (sub/subtype? t (c/Un (c/RClass-of clojure.lang.IPersistentMap [r/-any r/-any]) r/-nil)))

;[(U nil Expr) TCResult TCResult (Option TCResult) (Option TCResult) -> TCResult]
(defn invoke-keyword 
  "Return the type looking up kw-ret in target-ret, with default default-ret
  and expected result expected-ret.
  
  Only attach accurate object and propositions if target-ret is a nilable 
  immutable map. Once we understand how to deal with objects that don't necessarily hold
  in the lexical environment, we can relax this restriction and remember paths
  to possibly-mutable things that are updated to immutable."
  [expr kw-ret target-ret default-ret expected-ret]
  {:pre [(r/TCResult? kw-ret)
         (r/TCResult? target-ret)
         ((some-fn nil? r/TCResult?) default-ret)
         ((some-fn nil? r/TCResult?) expected-ret)
         ((some-fn nil? map?) expr)]
   :post [(r/TCResult? %)]}
  (u/p :check/invoke-keyword
  (let [targett (c/fully-resolve-type (r/ret-t target-ret))
        kwt (c/fully-resolve-type (r/ret-t kw-ret))
        defaultt (or (when default-ret
                       (c/fully-resolve-type (r/ret-t default-ret)))
                     r/-nil)]
    (cond
      ;Keyword must be a singleton with no default
      (c/keyword-value? kwt)
      (let [{path-hm :path id-hm :id :as o} (when (obj/Path? (r/ret-o target-ret))
                                              (r/ret-o target-ret))
            add-prop-and-obj? (immutable-lookup? targett)
            o (or o (r/ret-o target-ret))
            _ (assert ((some-fn obj/Path? obj/EmptyObject?) o))
            this-pelem (pe/-kpe (:val kwt))
            val-type (c/find-val-type targett kwt defaultt)]
        (binding [vs/*current-expr* (or expr vs/*current-expr*)]
          ;; 
          (below/maybe-check-below
            (if (not= (c/Un) val-type)
              (r/ret val-type
                     (if (and ;; we don't want to generate HMap types for HVecs and other non-persistent-map things
                              add-prop-and-obj?
                              (obj/Path? o)
                              ;; only handle nil defaults
                              (= r/-nil defaultt))
                       (fo/-FS ;; if val-type is false, this will simplify to ff
                               (fo/-filter-at
                                 (c/make-HMap :mandatory {kwt (c/In val-type r/-logically-true)})
                                 o)
                               (fo/-filter-at
                                 (c/Un (c/make-HMap :absent-keys #{kwt}); this map doesn't have a kwt key or...
                                       (c/make-HMap :mandatory {kwt r/-logically-false})) ; this map has a false kwt key
                                 o))
                       (fo/-FS fl/-top fl/-top))
                     (if (and add-prop-and-obj? (obj/Path? o) (= r/-nil defaultt))
                       (update-in o [:path] #(seq (concat % [this-pelem])))
                       obj/-empty))
              (do (u/tc-warning (str "Keyword lookup gave bottom type: "
                                     (:val kwt) " " (prs/unparse-type targett)))
                  (r/ret r/-any)))
            expected-ret)))

      :else (err/int-error (str "keyword-invoke only supports keyword lookup, no default. Found " 
                              (prs/unparse-type kwt)))))))
