(ns clojure.core.typed.test.duplicated
  (:require [clojure.core.typed :as t]))

(throw (Throwable. "This file should never be loaded"))
