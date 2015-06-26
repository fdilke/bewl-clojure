(ns bewl.topos-util
  (:use swank.util 
        [clojure.contrib.fcase :only [case] :rename {case x-case}]
        [bewl util object-wrap]
  )
)

(defn id 
  "Build the identity arrow at a given dot/object"
  [X]
  (((topos-of X) :id) X)
)

(defn exponential-object
  "Pick out the exponential object from an exponential diagram"
  [exponential] (let [
     [evaluation transpose] exponential 
     [exp-x-Y-diagram ev] evaluation
     [exp-x-Y [exp Y] projections multiply] exp-x-Y-diagram
  ] exp
)) 

(defn canonical-exp-iso
  "Construct the canonical iso between exponentials on the same parameters"
  [Y-exp-X-1 Y-exp-X-2] (let [
    [eval-1 _] Y-exp-X-1
    [_ transpose-2] Y-exp-X-2
  ] (transpose-2 eval-1) 
))  

(defn regularize
  "Premultiply a bunch of arrows as necessary to make sure they all have the same source"
  [arrows] (if (empty? arrows) arrows 
  (let [
     topos (topos-of (first arrows))                 
     [the-1 to-1] (topos :terminator)
     sources       (map #(% :src) arrows)
     common-source (find-first #(not= the-1 %) sources)
  ] (if common-source (let [common-to-1 (to-1 common-source)
        ] (doall (for [arrow arrows] 
                 (x-case (arrow :src)
                       common-source   arrow
                       the-1          (arrow common-to-1)
                       (throw (IllegalArgumentException. 
                           (str "multiple non-global elements with different sources: " 
                                (arrow :src) " not " common-source "::>" (= (arrow :src) common-source))))
                       )
           )))
        arrows   ; all are global, leave as they are
))))

(defn multiarize 
  "Construct a function of appropriate arity from a multiarrow"
  [[product multiarrow]] (let [
      [product-object components projections multiply] product
      num-args (count components)
   ] (enforce-arity num-args 
        (fn [arrows] (multiarrow (multiply arrows))
))))

(defn arrow-name
   "Compute the 'name' of an arrow X->Y in the context of an exponential Y^X" 
   [exp arrow] (let [
      X     (arrow :src)
      topos (topos-of X)                     
      [the-1 _] (topos :terminator)
      [_ transpose] exp
      [_ _ [_ piX] _ :as prod1X] ((topos :product) [the-1 X])
   ] (transpose [prod1X (arrow piX)]) 
))

(defn compare-multiary
  "Tell if 2 multiary operations are the same"
  [components op1 op2] (let [
    topos (topos-of (first components))                             
    [_ _ projections _ :as product] ((topos :product) components)
  ] (= (apply op1 projections) (apply op2 projections))
))

(defn remultiarize
  "Turn a computation into a genuine multiary arrow, executing it only once"
  [components op-fn] (let [
    topos (topos-of (first components))                           
    [_ _ projections _ :as product] ((topos :product) components)
  ] (multiarize [product (apply op-fn projections)])
))

(defmacro build-multiary
  "remultiarize repackaged as a macro - uses 'for'-style syntax to let elements range over an object"
  [bindings & body] (let [
    [args components] (unpack-bindings bindings)
  ] `(remultiarize [~@components] (fn [~@args] ~@body))
))

(defn for-all-1-1-sub
  [X Y op-fn] (let [
    topos (topos-of X)                    
    [truth-arrow characteristic] (topos :subobject-classifier)
    [_ to-1] (topos :terminator)
    omega (truth-arrow :tgt)
    [_ transpose :as exp]  ((topos :exponential) omega Y)
    [_ _ projections _ :as XxY] ((topos :product) [X Y])
    X-oY (transpose [XxY (apply op-fn projections)])
    Y-true (truth-arrow (to-1 Y))
    [for-all-arrow _] (characteristic (arrow-name exp Y-true))
  ] (for-all-arrow X-oY)
))

(defmacro for-all-1-1
  "Univariate universal quantifier. Given an expression in x, y, return an arrow X->omega 
   expressing the truth of this being universally true (in topos logic) for all y"
  [[x X] [y Y] & body]
  `(for-all-1-1-sub ~X ~Y (fn [~x ~y] ~@body))
)

(defmacro for-all
  "Multivariate universal quantifier. Given an expression in x1, x2... and y1, y2... return a
  multiarrow from the product of the x's expressing the truth of this being true for all
  elements in the product of the y's"
  [outer-bindings inner-bindings & body] (let [
    [outer-args outer-components] (unpack-bindings outer-bindings)
    [inner-args inner-components] (unpack-bindings inner-bindings)
    first-arg (first (concat outer-args inner-args))
  ] `(let [
        topos# (topos-of ~(first outer-components))
        [P# _# outer-projections# outer-multiply#] ((topos# :product) [~@outer-components])                                           
        [Q# _# inner-projections# _#] ((topos# :product) [~@inner-components])                                           
        A# (for-all-1-1 [p# P#] [q# Q#] (let [
             [~@outer-args] (for [o# outer-projections#] (o# p#))                                                  
             [~@inner-args] (for [i# inner-projections#] (i# q#))                                                  
            ] ~@body))
     ] (build-multiary [~@outer-bindings]
          (A# (outer-multiply# [~@outer-args]))
))))

(defn to-true
  "Build the arrow sending X via the truth arrow"
  [X] (let [
     topos (topos-of X)
     [truth-arrow _] (topos :subobject-classifier)                  
     [_ to-1] (topos :terminator)                  
  ](truth-arrow (to-1 X))
))

(defn truthful?
  "Tell if an arrow to omega factors through the truth arrow"
  [arrow]
  (= arrow (to-true (arrow :src)))
)

(defn subobject-sub
  [X condition] (let [
    topos (topos-of X)                             
    [the-eq factorize] ((topos :equalizer) condition (to-true X))
  ] [(the-eq :src) the-eq factorize]
))

(defmacro subobject
  "construct a subobject, with its embedding monic and factorizer"
  [[x X] & body] 
  `(let [X# ~X] 
      (subobject-sub X# (let [~x (id X#)] ~@body))
))  

(defn equals-over
  "Calculate a multiary operator expressing equality over X via tha diagonal"
  [X] (let [
    topos (topos-of X)
    [the-1 _] (topos :terminator)
    id-X  (id X)
    [truth-arrow characteristic] (topos :subobject-classifier)
    [_ _ _ multiply :as XxX] ((topos :product) [X X])
    [diag-eq factorize] (characteristic (multiply [id-X id-X]))      
  ] (multiarize [XxX diag-eq])
))

(defn monic?
  "Tell if an arrow is monic"
  [f] (let [
    topos (topos-of f)
    [the-1 to-1] (topos :terminator)
    [truth-arrow characteristic] (topos :subobject-classifier)
    X (f :src)
    Y (f :tgt)
    {:keys [implies]} (topos :truth)
    id-1  (id the-1)
    eq-X (equals-over X)
    eq-Y (equals-over Y)
  ] (truthful? ((for-all [_ the-1] [a X b X]  
         (implies (eq-Y (f a) (f b)) (eq-X a b))                 
      ) id-1)
)))
