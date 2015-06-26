(ns bewl-test.generic-tests
  (:use clojure.test
        [bewl topos-util object-wrap]
        bewl.algebra.structures        
))

(defn generic-topos-tests
  "Test a topos, given a map of 'standard fixtures'"
  [E fixtures]
  (let [{:keys [X Y Z X-Y Y-Z Z-W X-Z X-Y-Z XxY-Z monic-Y-Z rt-equals-st]} fixtures
        idX (id X)
        idY (id Y)
        [the-1 to-1] (E :terminator)
  ] (testing "Object wrapping"
    (is (= E (topos-of X)))
    (is (= E (topos-of X-Y)))
  ) (testing "Identity arrows" 
  (is (= X (idX :src)))
  (is (= X (idX :tgt)))
  (is (= idX (idX idX)))
  (is (= X-Y (X-Y idX)))
  (is (= X-Y (idY X-Y)))
  (is (thrown? IllegalArgumentException (X-Y Y-Z))) 
  (is (= X-Y-Z (Y-Z X-Y)))
) (testing "Associativity"
  (is (= (Z-W (Y-Z X-Y)) ((Z-W Y-Z) X-Y) (Z-W Y-Z X-Y)))
) (testing "Products"
    (let [[YxZ [_Y _Z] [piY piZ] multiply] ((E :product) [Y Z])
          X-YxZ (multiply [X-Y X-Z])
      ] (is (= _Y Y))
        (is (= _Z Z))
        (is (= Y (piY :tgt)))
        (is (= Z (piZ :tgt)))
        (is (= X-Y (piY X-YxZ))) 
        (is (= X-Z (piZ X-YxZ))) 
        (is (thrown? IllegalArgumentException (multiply [X-Y Y-Z])))
)) (testing "Terminator"
     (let [X-1 (to-1 X)
           Y-1 (to-1 Y)
       ] (is (= X (X-1 :src)))
         (is (= X-1 (Y-1 X-Y))) 
   (testing "Canonical iso between terminator and empty product"
     (let [[p0-obj _ _ mul-p0] ((E :product) [])
           p0-to-the-1 (to-1 p0-obj)
           the-1-to-p0 (mul-p0 the-1 [])
           ] (is (= (id p0-obj) (the-1-to-p0 p0-to-the-1)))
             (is (= (id the-1) (p0-to-the-1 the-1-to-p0)))
             ; and as a technical convenience, we require them to be the same object
             (is (= p0-obj the-1))
)))) (testing "Equalizers"
        (let [[r s t] rt-equals-st
              [the-equalizer factorize] ((E :equalizer) r s)
              t-factor (factorize t)
           ] (is (= (r t) (s t)))
             (is (not= r s))      ; testing the fixture
             (is (= (r the-equalizer) (s the-equalizer)))
             (is (= t (the-equalizer t-factor))
))) (testing "Exponentials" (let [ 
         [[XxY _ [piX piY] _] multiarrow] XxY-Z
         [ev-multiarrow transpose]  ((E :exponential) Z Y)
         [[_ _ _ mul-exp] ev] ev-multiarrow 
         X-ZexpY (transpose XxY-Z)
       ] (is (= multiarrow (ev (mul-exp [(X-ZexpY piX) piY]))))
)) (testing "Canonical isomorphism of exponentials" (let [
         Y-exp-X-1 ((E :exponential) Y X)                                                 
         Y-exp-X-2 ((E :exponential) Y X)
         Y-exp-X-1-o (exponential-object Y-exp-X-1)
         Y-exp-X-2-o (exponential-object Y-exp-X-2)
         iso1 (canonical-exp-iso Y-exp-X-1 Y-exp-X-2)
         iso2 (canonical-exp-iso Y-exp-X-2 Y-exp-X-1)
       ] (is (= (id Y-exp-X-1-o) (iso1 iso2))                                                      
         (is (= (id Y-exp-X-2-o) (iso2 iso1))                                                      
)))) (testing "Subobject classifier" (let [
         [truth characteristic] (E :subobject-classifier)
         [chi factorize] (characteristic monic-Y-Z)
       ] (is (= (chi monic-Y-Z) (truth (to-1 Y))))
         (is (= the-1 (truth :src)))
         (is (= X-Y (factorize (monic-Y-Z X-Y)))) 
))
    ; and test the 'enhancement layer' of this topos
    (testing "Arrow names" (let [
      [ev-multiarrow transpose :as exp]  ((E :exponential) Y X)
      [[prd [exp-object _] _ _] ev] ev-multiarrow
      X-Y-name (arrow-name exp X-Y)
    ] (is (= the-1 (X-Y-name :src)))
      (is (= exp-object (X-Y-name :tgt)))
      (is (= X-Y ((multiarize ev-multiarrow) (X-Y-name (to-1 X)) idX)))
  )) (testing "The truth object" (let [
        truth (E :truth)
        [truth-arrow characteristic] (E :subobject-classifier)
        omega (truth :carrier)
      ] (is (= heyting-algebra (truth :theory)))
        (is (= (truth-arrow :tgt) omega))
        (is (= true (verify-algebra truth)))
        (is (= false (= (truth :true) (truth :false))))
     (testing "The to-true utility" (let [
       true-X (to-true X)
       ttt (for-all [_ the-1] [x X] (true-X x))
     ] (is (= truth-arrow (ttt (id the-1))))
))))
 (println "MEMO speed up monic?, reinstate tests!")
 '(testing "Testing monicity"
   (is (= false (monic? Y-Z)))    
   (is (= true (monic? monic-Y-Z)))
   (is (= false (monic? (to-true Z))))
   (is (= true (monic? (id Z)))))
))
