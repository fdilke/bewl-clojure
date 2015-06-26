(ns bewl.enhance
  (:use bewl.algebra.structures
        [bewl topos-util object-wrap]
))

(defn- build-truth [topos] (let [
     [truth-arrow characteristic] (topos :subobject-classifier)
     omega (truth-arrow :tgt)
     id-omega (id omega)
     [the-1 _] (topos :terminator) 
     [o2 _ [pi1 pi2] multiply :as o-squared] ((topos :product) [omega omega])
     [chi-and _] (characteristic (multiply [truth-arrow truth-arrow]))
     binop-and (multiarize [o-squared chi-and])
     [chi-eq  _] (characteristic (multiply [id-omega id-omega]))
     binop-eq (multiarize [o-squared chi-eq])
     ; a implies b if a ^ b == a
     binop-implies (build-multiary [a omega b omega]
                     (binop-eq a (binop-and a b)))
     false-arrow (for-all-1-1 [_ the-1] [w omega] w)
     binop-or (for-all [a omega b omega] [w omega] 
                    (binop-implies (binop-and (binop-implies a w)
                                              (binop-implies b w))
                     w))
   ] { :carrier omega :theory heyting-algebra 
       :and binop-and :or binop-or :implies binop-implies 
       :true truth-arrow :false false-arrow 
}))

(defn enhance-topos
  "'enhance' a topos by adding new derived functions"
  [topos] (add-layer topos 
        :truth (build-truth topos)
))

