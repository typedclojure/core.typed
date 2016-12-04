(ns clojure.core.typed.test.gradual.export
  {:lang :clojure.core.typed
   :core.typed {:gradual true}}
  (:require [clojure.core.typed :as t]))

(t/ann my-plus [t/Num t/Num :-> t/Num])
(defn my-plus [x y]
  (+ x y))

(t/ann no-contract (t/All [x] [x :-> x]))
(defn ^::t/no-contract
  no-contract [x]
  x)

(my-plus 1 2)
;(my-plus 1 nil)

#_
(t/tc-ignore
  (my-plus nil nil))
(comment


(defmacro foo [x]
  (my-plus x 1)
  `nil)

(foo nil)



)
