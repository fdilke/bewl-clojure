(ns bewl-test.test-topos-util
  (:use clojure.test 
        [bewl util topos-util topos-of-sets]
))

(deftest test-regularize (let [
    X (set-of 0 1 2)
    Y (set-of true false)
    H (set-of :p :q :r)
    K (set-of :s :t :u)
    X-H (set-arrow X H { 0 :p 1 :r 2 :r})
    Y-H (set-arrow Y H { true :p false :r })
    Y-K (set-arrow Y K { true :s false :u })
    [the-1 make-constant] (sets :terminator)
    one-H (set-arrow the-1 H (constantly :r))
 ] (is (= [] (regularize [])))
   (is (= [X-H] (regularize [X-H])))
   (is (= [one-H one-H] (regularize [one-H one-H])))
   (is (= [X-H (set-arrow X H (constantly :r))] (regularize [X-H one-H])))
   ; check the arrows don't have to have the same destinations
   (is (= [Y-K (set-arrow Y H (constantly :r))] (regularize [Y-K one-H])))
   ; check we detect if there are multiple non-global sources
   (is (thrown? IllegalArgumentException (regularize [X-H Y-H])))
))

(deftest test-multiarize (let [
     [the-1 make-constant] (sets :terminator)                          
     V (set-of true false)
     X (set-of 1 2 3)
     Y (set-of :a :b)
     Z (set-of "p" "q" "r")
     W (set-of 5.0 6.0 7.0)
     V-X (set-arrow V X { true 3 false 1 })
     V-Y (set-arrow V Y { true :b false :a })
     V-Z (set-arrow V Z { true "q" false "p" })
     [XxY _ _ _ :as XxY-prod] ((sets :product) [X Y])
     XxY-Z [XxY-prod (set-arrow XxY Z { [1 :a] "p" [1 :b] "q" 
                                        [2 :a] "q" [2 :b] "p"
                                        [3 :a] "r" [3 :b] "r"
                             })] ; a sample 'multiarrow' XxY -> Z
     multiop-X-Y (multiarize XxY-Z)                         
     [XxYxZ _ _ _ :as XxYxZ-prod] ((sets :product) [X Y Z])
     XxYxZ-W [XxYxZ-prod (set-arrow XxYxZ W (fn [[x y z]] (case [x y z]
                                [3 :b "q"] 5.0
                                [1 :a "p"] 7.0
                                6.0) 
                             ))] ; a sample 'multiarrow' XxY -> Z
     multiop-X-Y-Z (multiarize XxYxZ-W)                         
   ] (is (= 2 (arity multiop-X-Y)))
     (is (= (set-arrow V Z {true "r" false "p"}) 
            (multiop-X-Y V-X V-Y) 
     ))
     (is (= 3 (arity multiop-X-Y-Z)))
     (is (= (set-arrow V W {true 5.0 false 7.0}) 
            (multiop-X-Y-Z V-X V-Y V-Z) 
     ))
))

(deftest test-build-multiary (let [
   X (set-of 0 1 2)
   Y (set-of :p :q)
   Z (set-of true false)
   V (set-of "a" "b" "c")
   op-fn (fn [x y] ({ [0 :p] true  [1 :p] false [2 :p] true
          [0 :q] false [1 :q] true  [2 :q] false } [x y] ))
   binop (heterogeneous-binary-set-op X Y Z op-fn)
   invocations (ref 0)
   binop2 (build-multiary [x X y Y]
             (dosync (alter invocations inc) (binop x y)))
   V-X (set-arrow V X { "a" 2 "b" 0 "c" 0 })
   V-Y (set-arrow V Y { "a" :q "b" :p "c" :p })
   ] (is (= 1 @invocations)) ; binop invoked during remultiarization
     (is ( = (binop2 V-X V-Y) (binop V-X V-Y)))
     (is (= 1 @invocations)) ; check binop was invoked only once
 ))

(deftest test-compare-multiary (let [
  X (set-of 0 1)
  Y (set-of :p :q)
  Z (set-of 7 8)
  h (heterogeneous-binary-set-op X Y Z (fn [x y]
        (if (or (= x 0) (= y :p)) 7 8)                                            
    ))
  k (fn [x y] (h x y))
  l (heterogeneous-binary-set-op X Y Z (fn [x y]
        (if (or (= x 1) (= y :p)) 7 8)                                            
    ))
  ] (is (= true  (compare-multiary [X Y] h h)))
    (is (= true  (compare-multiary [X Y] h k)))
    (is (= false (compare-multiary [X Y] h l)))
))

(deftest test-for-all-1-1 (let [
  X (set-of 0 1 2)
  Y (set-of :p :q)
  [truth-arrow char] (sets :subobject-classifier)
  omega (truth-arrow :tgt)
  h (heterogeneous-binary-set-op X Y omega (fn [x y]
        (if (or (= x 0) (= y :p)) true false)                                            
    )) 
  X-to-o (for-all-1-1 [x X] [y Y] (h x y))
  ](is (= (set-arrow X omega {
            0 true 1 false 2 false                                
          }) X-to-o))
))

(deftest test-for-all (let [
  X (set-of 0 1)
  Y (set-of :p :q)
  Z (set-of 7 8)
  W (set-of :s :t)
  [truth-arrow char] (sets :subobject-classifier)
  omega (truth-arrow :tgt)
  hh (build-multiary [x X y Y z Z w W] (let [
        S (x :src)
        ] (set-arrow S omega (fn [s] (let [
             xx ((x :fn) s)
          ] (if (= xx 1) true false)
     )))))
  X-Y-to-o (for-all [x X y Y] [z Z w W] (hh x y z w))
  ] (is (= true (compare-multiary [X Y]
        X-Y-to-o (heterogeneous-binary-set-op X Y omega (fn [x y]
        (if (= x 1) true false)                                            
    )))))
))

(deftest test-subobject (let [
   X (set-of 4 5 6)
   omega ((sets :truth) :carrier)
   [S embed factorize] (subobject [x X] 
      (set-arrow (x :src) omega (fn [s] (even? ((x :fn) s)))))
   S-s (set-members S)
   ](is (= 2 (count S-s)))
    (is (= S (embed :src)))                          
    (is (= X (embed :tgt)))                          
    (is (= #{4 6} (set (map (embed :fn) S-s))))
    (is (= true (monic? embed)))
))

(deftest test-truthful? (let [
  X (set-of 4 5 6)
  omega ((sets :truth) :carrier)
  ] (is (= false (truthful? (id omega))))
    (is (= true  (truthful? (to-true X))))
))

(deftest test-equals-over (let [
  X (set-of 0 1 2)
  eq-X (equals-over X)
  ] (= true (compare-multiary [X X] eq-X
     (build-multiary [x X y X] (let [
        S (x :src)                                     
        ] (set-arrow S #{true false} (fn [s]
             (= ((x :fn) s) ((y :fn) s))                            
    ))))))
))
