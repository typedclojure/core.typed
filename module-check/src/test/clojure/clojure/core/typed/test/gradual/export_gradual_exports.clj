(ns clojure.core.typed.test.gradual.export-gradual-exports
  {:lang :core.typed
   :core.typed {:gradual-exports true}
   }
  (:require [clojure.core.typed :as t]))

(t/ann my-plus [t/Num t/Num :-> t/Num])
(defn my-plus [x y]
  (+ x y))







(comment

(my-plus 1 2)
;(my-plus 1 nil)

;(t/tc-ignore
;  (my-plus nil nil))

(defmacro foo [x]
  (my-plus x 1)
  `nil)

(foo nil 1)



)
