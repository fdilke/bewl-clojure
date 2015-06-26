(ns bewl.topos-of-sets
  (:use clojure.math.combinatorics
        clojure.set  
        [bewl util enhance topos-util object-wrap]
))

(declare set-arrow)

; map between Clojure sets and our representation of them

(represent-topos set-of [& members]
  :set (set members)          
)

(defn set-members
  "Extract members of a topos-set-object as a Clojure set"
  [X]
  (X :set)
)

(defn set-arrow-raw
  "Represent an arrow in the topos of sets"
  [src tgt f] (let [
    src-s (set-members src)                    
    tgt-s (set-members tgt)                    
  ]
  (if (and (map? f) (not= (set (keys f)) src-s))
        (throw (java.lang.IllegalArgumentException. (str "Map keys do not match source: " 
                                                         (set (keys f)) " vs " src-s)))
  (if (and (map? f) (not (subset? (set (vals f)) tgt-s)))
        (throw (java.lang.IllegalArgumentException. (str "Map values are not in target: " 
                                                         (vals f) " vs " tgt-s)))
   (letfn [(do-invoke [x]
     (let [the-map { :src src :tgt tgt :fn f :get-topos-ref (src :get-topos-ref)}
             ] (cond (keyword? x) (the-map x)
	            :default ; assume this is set arrow composition
             (if (= (x :tgt) src) 
                (set-arrow (x :src) tgt (comp f (x :fn)))
                (throw (java.lang.IllegalArgumentException. "Arrows not composable: source/target don't match"))
     ))))
  ] (proxy [clojure.lang.AFn] []
     (invoke [& x]
        (if (= 1 (count x))
            (do-invoke (first x))
            (do-invoke (apply (first x) (rest x)))
        ))
     (equals [that]
            (and (instance? clojure.lang.IFn that)
                 (= src (that :src))
                 (= tgt (that :tgt))
                 (let [that-f (that :fn)]
                   (every? (fn [x] (= (f x) (that-f x))) src-s)
      )))
     (toString [] (str "<" src-s "=>" tgt-s ":" 
            (into {} (for [x src-s] [x (f x)])) ">"))
))))))

(defn set-arrow
  "Represent an arrow in the topos of sets, wrapping the function"
  [src tgt f]
  (set-arrow-raw src tgt
      (if (map? f) f
          (memoize f)
)))    

(def sets (let [
    one-element []                
    the-1 (set-of one-element)
    omega (set-of true false)
    truth (set-arrow-raw the-1 omega (constantly true))
    reverse-map #(into {} (map (fn [[k v]] [v k]) %))
    to-1 (fn [X]
      (set-arrow-raw X the-1 (constantly one-element))
    ) characteristic (fn [monic] (let [
         src (monic :src)                              
         tgt (monic :tgt)
         src-s (set-members src)
         img-s (set (map (monic :fn) src-s))
         monic-fn (monic :fn)
         monic-fn-map (apply hash-map (apply concat (for [x src-s] [x (monic-fn x)]))) 
         rev-lookup (reverse-map monic-fn-map) 
         chi (fn [x] (if (img-s x) true false))
         the-char (set-arrow tgt omega chi)
         factorize (fn [nx] (let [
           pre-src (nx :src)
           do-lookup (fn [x] (rev-lookup ((nx :fn) x)))
           ] (set-arrow pre-src src do-lookup)
         ))] [the-char factorize]
    )) set-product (fn [components] (let [
	      the-product (apply set-of (apply cartesian-product (map set-members components)))
	      the-projections  (for [n (range (count components))]
	        (let [component (nth components n)
	        ] (set-arrow the-product component #(nth % n)) 
	     ))] (letfn [(multiply
        ([arrows] (multiply ((first arrows) :src) arrows))
        ([source arrows]
          (if (every? #(= % source) (map #(% :src) arrows))
	          (letfn [(build-tuple [s] (for [arrow arrows] ((arrow :fn) s)))]
	            (set-arrow source the-product build-tuple)
	          ) (throw (IllegalArgumentException. (str "product multiply failed: bad arrow sources:"
                 (vec (map #(% :src) arrows))        
              ))))))]
        [the-product components the-projections multiply])
  	  ))] (enhance-topos {
      :terminator 
      [the-1 to-1]
	    :subobject-classifier 
        [truth characteristic]
      :product set-product
	    :equalizer (fn [arrow1 arrow2] (let [
	         src (arrow1 :src)
	         fn1 (arrow1 :fn)
	         fn2 (arrow2 :fn)
	         act-same (fn [x] (= (fn1 x) (fn2 x)))
	         pre-src (apply set-of (filter act-same (set-members src)))
	         the-equalizer (set-arrow-raw pre-src src identity)
	         factorize (fn [equalizing-arrow]
	              (set-arrow (equalizing-arrow :src) pre-src
	                  (equalizing-arrow :fn))
	       )] [the-equalizer factorize]
	    ))
	    :exponential (fn [tgt src] (let [
	        src-as-list (apply list (set-members src))
	        the-exponent (apply set-of (selections (set-members tgt) (count src-as-list)))
	        exp-x-src (set-product [the-exponent src])
	        [prd _ _ _] exp-x-src
	        eval-pair (fn [[exp-tuple s]] (nth exp-tuple (.indexOf src-as-list s)))
	        ev (set-arrow prd tgt eval-pair)
	        the-eval [exp-x-src ev]
	        transpose (fn [[Xxsrc multiarrow]] (let [
	               [_ [X _src] _ _] Xxsrc
	               multiarrow-fn (multiarrow :fn)
	               x-to-exp (fn [x] (map #(multiarrow-fn [x %]) src-as-list))
	             ] (if (not= src _src)
	                (throw (java.lang.IllegalArgumentException. "Cannot transpose, bad product"))
	                (set-arrow X the-exponent x-to-exp)
	      )))] [the-eval transpose]
	    ))
	    :id (fn [dot] (set-arrow-raw dot dot identity))
})))       

(defn heterogeneous-binary-set-op 
  "Create a binary operation from 2 sets to another set"
  [X Y Z op-fn] (let [
    [XxY [_ _] _ _ :as XxY-prod] ((sets :product) [X Y])
    ] (multiarize [XxY-prod (set-arrow XxY Z (partial apply op-fn))]) 
))

(defn binary-set-op 
  "Create a multiarized binary operation on a single set"
  [X op-fn]
  (heterogeneous-binary-set-op X X X op-fn)
)

(defn set-element
  "Express an element x of a set X as an arrow 1->X"
  [X x] (let [
   [the-1 _] (sets :terminator)
  ] (set-arrow the-1 X (constantly x))
))

