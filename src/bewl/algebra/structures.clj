(ns bewl.algebra.structures
  (:use [bewl object-wrap util topos-util]
))

; Functions for manipulating algebraic structures in a topos

(defn- retarget
  "Retarget the unary operators of an algebra from a given source object"
  [algebra source] (let [
     signature ((algebra :theory) :signature)
     [the-1 to-1] ((topos-of (algebra :carrier)) :terminator)
     source-to-1 (to-1 source)
     ] (into algebra (concat (for [[op-name op-arity] signature]
        [op-name (let [raw-op (algebra op-name)] 
           (if (> op-arity 0) raw-op (raw-op source-to-1)
        ))])
        (for [key ((algebra :theory) :param-spaces)]
           [key (retarget (algebra key) source)]
        )
     ))
))

(defn verify-law [algebra law] (let [
     topos (topos-of (algebra :carrier))                                    
     num-vars (dec (arity law))
     types (or (:types (meta law)) (repeat num-vars -))
     get-carrier (fn [type] (:carrier
       (if (keyword? type) (algebra type) algebra)
     ))
     type-carriers (map get-carrier types)
     ; multiply up the type carriers
     [source-product _ projections _] ((topos :product) type-carriers)  
  ] (apply law (retarget algebra source-product) projections)
))

(defn verify-algebra
  "Verify that an algebraic structure has the required operations and obeys the required laws.
  If it doesn't, throw an appropriate exception."
  [algebra] (let [
     {:keys [signature laws]} (algebra :theory)  
  ; Check that non-nullary/unary ops have the right arities
  ] (doall (for [[op-name op-arity] signature] (let [
       op (algebra op-name)
       ] (cond (nil? op)
                 (throw (IllegalArgumentException. (str "operator missing: " op-name)))
               (and (> op-arity 1) (not= op-arity (arity op)))
                 (throw (IllegalArgumentException. 
                    (str "operator has wrong arity: " op-name " ; expected" op-arity)))
  ))))  
  ; check the laws
  (if (every? identity (for [law laws] (verify-law algebra law)))
     true
    (throw (IllegalArgumentException. "law failed!"))
)))

(defn morphism?
  "Tell if an arrow between algebra carriers is a morphism, i.e. respects the operators of some theory"
  [theory src-algebra tgt-algebra f] (let [
    A (src-algebra :carrier)                                                
    B (tgt-algebra :carrier)                                                
    topos (topos-of A)                                               
    {:keys [signature]} theory
  ] (if (or (not= A (f :src)) (not= B (f :tgt)))
      (throw (IllegalArgumentException. "arrow should map source algebra to target one"))
    (every? identity (for [[op-name op-arity] signature] (let [
        [A-n _ A-projections mul-A] ((topos :product) (repeat op-arity A))                                                               
        [B-n _ B-projections mul-B] ((topos :product) (repeat op-arity B))
        op-of (fn [algebra args] (let [op (algebra op-name)]                                             
          (if (> op-arity 0) (apply op args) op)))  ; tell if the arrow respects this operation
        ] (= (f (op-of src-algebra A-projections)) 
           (op-of tgt-algebra (for [p A-projections] (f p)))
)))))))

; A^n ---> B^n
;  I      I
;  I      I
;  v      v
;  A ---> B

(defmacro define-law
  "Define an algebraic law schema given specified operations and bound variables"
  ([name ops vars body] (let [
      types (repeat (count vars) -)
    ] `(define-law ~name ~ops ~types ~vars ~body)
  ))
  ([name ops types vars body]
  `(defn ~name [& op-keys#]
     ^ {:types [~@types]}
     (fn [op-map# ~@vars] (let [
         ~ops (map op-map# op-keys#)
    ] ~body)
  )))
)

; patterns for building algebraic laws

(define-law commutative-law [op] [x y]
  (= (op x y) (op y x))
)

(define-law associative-law [op] [x y z]
  (= (op (op x y) z) (op x (op y z)))
)

(define-law unit-law [unit op] [x] 
  (= x (op unit x) (op x unit))
)

(define-law inverse-law [unit inverse op] [x]
  (= unit (op (inverse x) x)) ; implies they are right inverses too
)

(define-law left-distributive-law [over under] [x y z]
  (= (over x (under y z)) (under (over x y) (over x z)))
)

(define-law right-distributive-law [over under] [x y z]
  (= (over (under x y) z) (under (over x z) (over y z)))
)

(define-law absorptive-law [over under] [x y]
  (= (over x (under x y)) x)
)

(define-law preservation-law [op binop] [x y]
  (= (op (binop x y)) (binop (op x) (op y)))
)

(define-law right-monoid-action-multiply-law
    [scalars right-multiply]
    [- :scalars :scalars]
    [x r s]   (let [
       {:keys [multiply]} scalars                                                                 
    ] (= (right-multiply (right-multiply x r) s)
              (right-multiply x (multiply r s)))
))

(define-law right-monoid-action-unit-law
   [scalars right-multiply]
   [x] (let [
     {:keys [unit]} scalars                                                                
   ] (= x (right-multiply x unit))
))

(define-law right-module-additivity-law
  [scalars plus right-multiply]
  [- :scalars :scalars]
  [x r s] (=
     (right-multiply x ((scalars :plus) r s))
     (plus (right-multiply x r) (right-multiply x s))
))

; the somewhat more specialized "implication laws" for Heyting algebras

(define-law self-implication-law [truth implies] [x]
   (= truth (implies x x))
)

(define-law modus-ponens [and implies] [x y]
   (= (and x (implies x y)) (and x y))
)

(define-law implication-supersedes [and implies] [x y]
   (= (and x (implies y x)) x)
)

; the 'default theory' with explicitly no ops, laws, parameter spaces

(def default-theory { 
             :signature {} 
             :laws [] 
             :param-spaces [] 
})

; a utility for extending algebraic theories

(defn extend-theory ([base-theory extension]  
  (into {} 
       (for [[key base] (into default-theory base-theory)] 
          [key (into base (extension key))]) 
)) ([p q r & more]
     (reduce extend-theory (concat [p q r] more))
))

; Some standard algebraic theories, described via signatures and laws with optional utility functions

(def magma {:signature { :multiply 2 }  ; a binary product
            :laws      []               ; no laws
})

(def monoid {:signature { :unit 0 :multiply 2 }   ; a binary product with 2-sided unit
             :laws [    (unit-law :unit :multiply)
                        (associative-law :multiply)
]})

(def group (extend-theory monoid            ; a monoid with inverses
           {:signature { :inverse 1 }
            :laws [ (inverse-law :unit :inverse :multiply)  
]}))

(def abelian-group {
     :signature { :zero 0 :minus 1 :plus 2 }   
     :laws [    (unit-law :zero :plus)
                (commutative-law :plus)
                (associative-law :plus)
                (inverse-law :zero :minus :plus)  ]
})

(def ring (extend-theory abelian-group monoid {   ; an abelian group and monoid, with distributive laws
     :laws [    (left-distributive-law :multiply :plus)
                (right-distributive-law :multiply :plus)
]}))

(def right-monoid-action { 
        :signature { :right-multiply 2 }
        :laws [ right-monoid-action-multiply-law 
                right-monoid-action-unit-law]
        :param-spaces [:scalars]
})

(def right-module (extend-theory right-monoid-action {
        :laws [ right-module-additivity-law ]                                 
}))

(def lattice {
     :signature { :false 0 :true 0 :and 2 :or 2 }
     :laws [ (unit-law :true :and)
             (commutative-law :and)
             (associative-law :and)
             (unit-law :false :or)
             (commutative-law :or)
             (associative-law :or)
             (absorptive-law :or :and)
             (absorptive-law :and :or)
]})

(def heyting-algebra (extend-theory lattice {
     :signature { :implies 2}
     :laws [ (self-implication-law :true :implies)
             (modus-ponens :and :implies)
             (implication-supersedes :and :implies)
             (left-distributive-law :implies :and)                
]}))

; function that applies to groups, monoids, rings, or anything else with a binary "multiply" operation
(defn commutative? [algebra]
  (verify-law algebra (commutative-law :multiply))
)
