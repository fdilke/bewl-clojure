(ns bewl-test.test-topos-of-sets
  (:use clojure.test
        [bewl util topos-util topos-of-sets]
        bewl-test.generic-tests
))

(deftest test-set-arrow
  (testing "basic properties"
     (let [src (set-of 0)
           tgt (set-of 1 2)
           f (set-arrow src tgt { 0 1 })
           g (set-arrow src tgt { 0 2 })
           h (set-arrow src tgt { 0 1 })
       ] (is (= src (f :src)))
         (is (= tgt (f :tgt)))
         (is (= 1 ((f :fn) 0)))
         (is (= true (= f f)))
         (is (= false (= f g)))
         (is (= true (= f h)))
         (is (thrown? IllegalArgumentException (set-arrow src tgt {}))) 
         (is (thrown? IllegalArgumentException (set-arrow src tgt { 0 1 "z" 1}))) 
         (is (thrown? IllegalArgumentException (set-arrow src tgt { 0 "z" }))) 
) (testing "composition"
    (let [src (set-of :a :b)
          mid (set-of 1 2 3)
          tgt (set-of true false)
          beyond (set-of "x" "y" "z")
          f (set-arrow src mid {:a 1 :b 2})
          g (set-arrow mid tgt {1 false 2 true 3 false})
          h (set-arrow tgt beyond {true "y" false "z"})
          gf (g f)
          hgf (h g f)
         ]
   (is (= src (gf :src)))
   (is (= tgt (gf :tgt)))
   (is (= [false true] (map (gf :fn) [:a :b])))
   (is (= ["z" "y"] (map (hgf :fn) [:a :b])))
   (is (thrown? IllegalArgumentException (f g))) 
))))

(deftest test-binary-set-op (let [
  X (set-of 0 1 2)
  op-fn (fn [x y] (max x y))
  binop (binary-set-op X op-fn)
  Y (apply set-of (range 9))
  div3 (set-arrow Y X #(.intValue (/ % 3)))
  mod3 (set-arrow Y X #(mod % 3))
  id-X (id X)
  ] (is (= 2 (arity binop)))
    (is (= (set-arrow Y X #(max (.intValue (/ % 3)) (mod % 3)))
       (binop div3 mod3)))
    (is (= id-X (binop id-X id-X))) ; max(x,x) === x
))

(deftest test-heterogeneous binary-set-op (let [
  X (set-of 0 1 2)
  Y (set-of :p :q)
  Z (set-of true false)
  op-fn (fn [x y] ({ [0 :p] true  [1 :p] false [2 :p] true
          [0 :q] false [1 :q] true  [2 :q] false } [x y] ))
  binop (heterogeneous-binary-set-op X Y Z op-fn)
  W (set-of "a" "b" "c")
  W-X (set-arrow W X { "a" 0 "b" 2 "c" 1 })
  W-Y (set-arrow W Y { "a" :q "b" :p "c" :p })
  id-X (id X)
  ] (is (= 2 (arity binop)))
    (is (= (set-arrow W Z { "a" false "b" true "c" false})
       (binop W-X W-Y)))
))

(def sets-fixtures (let [
     X (set-of 0 1 2)         ; some sample objects
     Y (set-of :a :b :c :d)
     Z (set-of "s" "t" "u" "v" "w")
     W (set-of true false)
     X-Y  (set-arrow X Y { 0 :a 1 :c 2 :c})       ; a non-monic, non-epic arrow from X to Y
     X-Z  (set-arrow X Z { 0 "t" 1 "t" 2 "u"})    ; a non-monic, non-epic arrow from X to Z
     Y-Z  (set-arrow Y Z { :a "t" :b "s" :c "s" :d "t"})         ; a non-monic, non-epic arrow from Y to Z
     monic-Y-Z (set-arrow Y Z { :a "t" :b "s" :c "u" :d "w"})    ; a monic from Y to Z
     X-Y-Z (set-arrow X Z { 0 "t" 1 "s" 2 "s" })    ; the intended composite of X-Y and Y-Z
     [XxY _ _ _ :as XxY-prod] ((sets :product) [X Y])
     XxY-Z [XxY-prod (set-arrow XxY Z { [0 :a] "s" [0 :b] "t" [0 :c] "u" [0 :d] "s"
                                             [1 :a] "t" [1 :b] "u" [1 :c] "s" [1 :d] "t"
                                             [2 :a] "u" [2 :b] "s" [2 :c] "t" [2 :d] "u"
                             })] ; a sample 'multiarrow' XxY -> Z
     Z-W  (set-arrow Z W { "s" true "t" true "u" false "v" true "w" false}) ; arrow from Z to W
     ; an "equalizer situation": triple r,s,t with rs = rt
     rt-equals-st [
       (set-arrow Y Z { :a "s" :b "s" :c "t" :d "u"})
       (set-arrow Y Z { :a "s" :b "u" :c "t" :d "u"})
       X-Y
     ]
   ] {
   :X X    
   :Y Y
   :Z Z
   :X-Y X-Y
   :X-Z X-Z
   :Y-Z Y-Z
   :monic-Y-Z monic-Y-Z
   :X-Y-Z X-Y-Z
   :XxY-Z XxY-Z
   :Z-W Z-W
   :rt-equals-st rt-equals-st
}))

(deftest test-sets
  (generic-topos-tests sets sets-fixtures)
  (testing "Logical operators for sets" (let [
    truth (sets :truth)
    omega (truth :carrier)
    check-same (fn [op f] (is (= true 
         (compare-multiary [omega omega] 
            (truth op) (binary-set-op omega f)
       ))))
    ]  (check-same :and (fn [x y] (and x y)))
       (check-same :or  (fn [x y] (or x y)))
       (check-same :implies (fn [x y] (or (not x) y)))
)))

