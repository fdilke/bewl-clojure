(ns bewl.algebra.constructions
  (:use bewl.algebra.structures
        [bewl object-wrap topos-of-sets topos-util]
))

; some standard constructions

(defn Z-mod-n 
  "The ring of integers mod n"
  [n] (let [
        X (apply set-of (range n))
     ] {:carrier X :theory ring 
        :zero (set-element X 0) 
        :unit  (set-element X 1) 
        :minus (set-arrow X X (fn [x] (mod (- n x) n))) 
        :plus (binary-set-op X (fn [x y] (mod (+ x y) n))) 
        :multiply (binary-set-op X (fn [x y] (mod (* x y) n)))
}))

(defn group-of-units
  "The group of units of a monoid, and its embedding morphism"
  [MM] (let [
      {:keys [carrier unit multiply]} MM
      topos (topos-of carrier)
      {:keys [truth]} topos
      [the-1 to-1] (topos :terminator)
      M (MM :carrier)
      eq-M (equals-over M)
      [MxM _ [pi1 pi2] mulMxM :as square] ((topos :product) [M M])
      [G embed factorize] (subobject [m-n MxM] (let [
        m (pi1 m-n)                                                           
        n (pi2 m-n)
        unit-src (unit (to-1 (m :src)))
        ] ((truth :and) (eq-M unit-src (multiply m n)) 
                        (eq-M unit-src (multiply n m))) 
      ))
      extract (fn [m-n] (let [e (embed m-n)] [(pi1 e) (pi2 e)]))
    ] [{ :theory group :carrier G
         :unit (factorize (mulMxM [unit unit])) 
         :multiply (build-multiary [m-n G p-q G] (let [
            [m n] (extract m-n)                                           
            [p q] (extract p-q)                                           
         ] (factorize (mulMxM [(multiply m p) (multiply q n)]))                            
      )) 
        :inverse (build-multiary [m-n G] (let [
          [m n] (extract m-n)                                           
        ] (factorize (mulMxM [n m]))                            
      ))} (pi1 embed) ]
))

(defn endomorphism-action
  "The monoid of endomorphisms of an object, and its associated action"
  [X] (let [
    topos (topos-of X)            
    [ev-multiarrow transpose :as exp]  ((topos :exponential) X X)
    E (exponential-object exp)
    ev-multiary (multiarize ev-multiarrow)
    mul-endos (build-multiary [f E g E] (let [
	      S (f :src)
	      [_ _ [piS piX] _ :as SxX] ((topos :product) [S X])
	      fx (ev-multiary (f piS) piX)
	      gfx (ev-multiary (g piS) fx)
    ] (transpose [SxX gfx])
    ))
    right-multiply (fn [x e] (ev-multiary e x))
    unit (arrow-name exp (id X))
    EndX { :carrier E :theory monoid
        :unit unit :multiply mul-endos }
  ] { :carrier X :theory right-monoid-action
      :scalars EndX :right-multiply right-multiply
}))

(defn automorphism-action
  [X] (let [
    endo-action (endomorphism-action X)
    endos (endo-action :scalars)
    [autos embed] (group-of-units endos)
    ] { :carrier X :theory right-monoid-action 
      :scalars autos :right-multiply (build-multiary 
       [x X a (autos :carrier)]
       ((endo-action :right-multiply) x (embed a))                                   
    )})
)
