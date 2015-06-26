(ns bewl-test.algebra.test-constructions
  (:use [clojure test set] 
        [bewl topos-util util topos-of-sets]
        bewl.algebra.structures
        bewl.algebra.constructions
))

(deftest test-constructions
  (testing "Constructing the ring of integers mod n" (let [
         Z-5 (Z-mod-n 5)
      ] (is (= ring (Z-5 :theory)))
        (is (= (set-of 0 1 2 3 4) (Z-5 :carrier)))                                                           
        (is (= true (verify-algebra Z-5)))                                                           
  ))
  (testing "Endomorphism monoid actions" (let [
    T (set-of :a :b)
    A (endomorphism-action T)
    E (A :scalars)
    ] (is (= true (map? A)))
      (is (= right-monoid-action (A :theory)))
      (is (= T (A :carrier)))
      (is (= monoid (E :theory)))
      (is (= 4 (count (set-members (E :carrier)))))  ; 2^2
      (is (= true (verify-algebra A)))
      (is (= true (verify-algebra E)))
      (is (= false (commutative? E)))
	  (testing "Constructing the group of units" (let [
      [G embed] (group-of-units E)                                                    
      ] (is (= (G :carrier) (embed :src)))                                                    
        (is (= (E :carrier) (embed :tgt)))
        (is (= group (G :theory)))
        (is (= 2 (count (set-members (G :carrier)))))
        (is (= true (verify-algebra G)))
        (is (= true (morphism? monoid G E embed)))
	  ))
  ))
  (testing "Automorphism actions" (let [
     T (set-of :p :q :r)
     A (automorphism-action T)
     G (A :scalars)
     ] (is (= true (map? A)))
       (is (= right-monoid-action (A :theory)))
       (is (= T (A :carrier)))
       (is (= group (G :theory)))
       (is (= 6 (count (set-members (G :carrier)))))
       (is (= true (verify-algebra A)))
       (is (= true (verify-algebra G)))
       (is (= false (commutative? G)))
  ))                                         
)

