(ns bewl.util)

(defn map-map
  "Do what update-in supposedly does, but simpler"
  [f m]
  (apply hash-map (apply concat (for [[k v] m] [k (f v)])))
)

(defn arity
  "simplistic measure of the arity of a function, using Java reflection"
  [f]
  (let [m (first (.getDeclaredMethods (class f)))
        p (.getParameterTypes m)]
    (alength p))
)

(defmacro arity-enforcer-helper [n] (let [
    syms (repeatedly n gensym)                                           
  ] `(fn [f#] (fn [~@syms] (f# [~@syms])))
))

(def arity-enforcer-helper-opt
  (memoize #(eval (concat [`arity-enforcer-helper] [%])))
)
   
(defn enforce-arity [n f]
  ((arity-enforcer-helper-opt n)  f)
)    

(defn unpack-bindings [bindings] ( let [
   pairs (partition 2 bindings)
   vars (map first pairs)
   ranges (map last pairs)
   ] [vars ranges]
))
