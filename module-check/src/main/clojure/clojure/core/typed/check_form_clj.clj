(ns ^:skip-wiki clojure.core.typed.check-form-clj
  (:require [clojure.core.typed.check-form-common :as chk-form]
            [clojure.core.typed.analyze-clj :as ana-clj]
            [clojure.tools.analyzer.jvm :as taj]
            [clojure.core.typed.check :as chk-clj]
            [clojure.core.typed.collect-phase :as collect-clj]
            [clojure.tools.analyzer :as ta]
            [clojure.tools.analyzer.passes.jvm.emit-form :as emit-form]
            [clojure.core.typed.runtime-check :as rt-chk]
            [clojure.core.typed.compiler-ast :as compiler]
            [clojure.core.typed.current-impl :as impl]))

(defn config-map
  ([] (config-map nil))
  ([ns-meta]
   (let [{:keys [analyzer] :as opts} (:core.typed ns-meta)]
     {:impl impl/clojure
      :ast-for-form ana-clj/ast-for-form
      :unparse-ns *ns*
      :collect-expr collect-clj/collect-ast
      :check-expr chk-clj/check-expr
      :runtime-check-expr rt-chk/runtime-check-expr
      :eval-out-ast (partial ana-clj/eval-ast {})
      :emit-form emit-form/emit-form
      :thread-bindings-fn (case analyzer
                            :core.typed ana-clj/thread-bindings-compiler
                            :t.a.jvm  ana-clj/thread-bindings-taj 
                            ana-clj/thread-bindings-taj)
      :macroexpand-1-var (case analyzer
                           :core.typed clojure.core.typed.Compiler/MACROEXPAND_ONE
                           :t.a.jvm #'ta/macroexpand-1
                           #'ta/macroexpand-1)
      :analyze-fn (case analyzer
                    :core.typed compiler/analyze
                    :t.a.jvm taj/analyze
                    taj/analyze)})))

(defn check-form-info
  [form & opt]
  (let [config (config-map)]
    (impl/with-full-impl (:impl config)
      (apply chk-form/check-form-info config
             form opt))))

(defn check-form*
  [form expected type-provided?]
  (let [config (config-map)]
    (impl/with-full-impl (:impl config)
      (chk-form/check-form* config
        form expected type-provided?))))
