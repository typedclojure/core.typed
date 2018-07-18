(ns clojure.core.typed.test.transducer
  (:refer-clojure :exclude [map sequence take drop into])
  (:require [clojure.core.typed :as t]
            [clojure.core :as core]))

;; based on https://hypirion.com/musings/haskell-transducers

;; TODO c.c.t alias for Reduced
(t/defalias Reducer
  (t/TFn [[a :variance :contravariant]
          [b :variance :invariant]]
    (t/IFn 
      ;init
      [:-> b]
      ;complete
      [b :-> b]
      ;step
      [b a :-> (t/U b (clojure.lang.Reduced b))])))

(t/defalias Transducer
  (t/TFn [[a :variance :covariant]
          [b :variance :contravariant]]
    (t/All [r]
      [(Reducer a r) :-> (Reducer b r)])))

(t/ann ^:no-check map
       (t/All [a b]
         [[a :-> b] :-> (Transducer b a)]))
(defn map [& args]
  (apply core/map args))

(t/ann ^:no-check sequence
       (t/All [a b]
         [(Transducer b a) (t/Seqable a) :-> (t/Seqable b)]))
(defn sequence [& args]
  (apply core/sequence args))

(let [map (t/inst map t/Num t/Num)
      m (map (t/inst identity t/Num))
      sequence (t/inst sequence t/Num t/Num)
      _ (t/print-env "debug map")]
  (sequence m [1 2 3]))

(t/ann ^:no-check take
       (t/All [a]
         [t/Int :-> (Transducer a a)]))
(defn take [& args]
  (apply core/take args))

(let [take (t/inst take t/Num)
      m (take 5)
      sequence (t/inst sequence t/Num t/Num)
      _ (t/print-env "debug take")]
  (sequence m [1 2 3]))

(t/ann ^:no-check drop
       (t/All [a]
         [t/Int :-> (Transducer a a)]))
(defn drop [& args]
  (apply core/drop args))

(let [drop (t/inst drop t/Num)
      m (drop 5)
      sequence (t/inst sequence t/Num t/Num)
      _ (t/print-env "debug drop")]
  (sequence m [1 2 3]))

(t/ann ^:no-check into
       (t/All [x y a b]
              (t/IFn 
                [(t/Map x y) 
                 (Transducer (t/U nil '[x y] (clojure.lang.IMapEntry x y))
                             (t/U nil '[a b] (clojure.lang.IMapEntry a b)))
                 (t/U nil 
                      (t/Seqable (t/U nil
                                      (t/Seqable (clojure.lang.IMapEntry a b)) 
                                      (clojure.lang.IMapEntry a b)
                                      '[a b])))
                 -> (t/Map x y)]
                [(t/Vec x) (Transducer x y) (t/U nil (t/Seqable y)) -> (t/Vec x)]
                [(t/Set x) (Transducer x y) (t/U nil (t/Seqable y)) -> (t/Set x)]
                [(t/Coll t/Any) (Transducer t/Any y) (t/U nil (t/Seqable y)) -> (t/Coll t/Any)])))
(defn into [& args]
  (apply core/into args))

(let [drop (t/inst drop t/Num)
      m (drop 5)
      into (t/inst into t/Num t/Num t/Any t/Any)
      _ (t/print-env "debug into non-map")]
  (t/ann-form (into [] m [1 2 3]) (t/Vec t/Num))
  (t/ann-form (into #{} m [1 2 3]) (t/Set t/Num))
  (t/ann-form (into '() m [1 2 3]) (t/Coll t/Any))
)

(let [drop (t/inst drop (t/U nil '[t/Num t/Num]
                             (clojure.lang.IMapEntry t/Num t/Num)))
      m (drop 5)
      into (t/inst into t/Num t/Num t/Num t/Num)
      _ (t/print-env "debug into map")]
  (t/ann-form (into {} m {1 2 3 4})
              (t/Map t/Num t/Num))
)

#_
(let [map (t/inst map
                  (t/U nil '[t/Num t/Num])
                  (t/U nil '[t/Num t/Bool]))
      m (map (fn [[k v]]
               [k (boolean v)]))
      into (t/inst into t/Num t/Num t/Num t/Num)
      _ (t/print-env "debug into map using core/map")]
  (t/ann-form (into {} m {1 2 3 4})
              (t/Map t/Num t/Bool))
)

