;;   Copyright (c) Ambrose Bonnaire-Sergeant, Rich Hickey & contributors.
;;   The use and distribution terms for this software are covered by the
;;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;;   which can be found in the file epl-v10.html at the root of this distribution.
;;   By using this software in any fashion, you are agreeing to be bound by
;;   the terms of this license.
;;   You must not remove this notice, or any other, from this software.

(ns clojure.core.typed.check.quote
  (:require [clojure.core.typed.utils :as u]
            [clojure.core.typed.check.const :as const]))

(defn check-quote [check constant-type {:keys [expr] :as quote-expr} expected]
  (let [cexpr (const/check-const constant-type true expr expected)]
    (assoc quote-expr
           :expr cexpr
           u/expr-type (u/expr-type cexpr))))
