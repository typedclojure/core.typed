(ns clojure.core.typed.test.gradual.export
  {:lang :core.typed/gradual
   ;; or use this instead of :lang
   ;:core.typed {:gradual-exports true}
   }
  (:require [clojure.core.typed :as t]))

(t/ann my-plus [t/Num t/Num :-> t/Num])
(defn my-plus [x y]
  (+ x y))







(my-plus 1 2)
;(my-plus 1 nil)

#_(t/tc-ignore
  (my-plus nil nil))
(comment


(defmacro foo [x]
  (my-plus x 1)
  `nil)

(foo nil 1)



)
