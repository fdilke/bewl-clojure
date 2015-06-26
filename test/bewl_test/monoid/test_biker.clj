(ns bewl-test.monoid.test-biker
  (:use [clojure test set]
        bewl.monoid.biker
))

; Functions to compute operations in the bicyclic semigroup

(deftest test-bike-mul 
  (testing "Basic multiplication" (let [
    p [0 1]
    q [1 0]
  ] (are [x y z] (= x (bike-mul y z))
	  p p bike-1
    bike-1 p q
	  [1 1] q p
    [0 2] p p
    [2 0] q q
) (doseq [k (range 3)
        l (range 3)
        m (range 3)
        n (range 3)
        o (range 3)
        p (range 3)
     ] (let [
        x [k l]
        y [m n]
        z [o p] 
     ] (is (= (bike-mul (bike-mul x y) z)
              (bike-mul x (bike-mul y z))
)))))))

(deftest test-bike-o-mul
  (testing "omega multiplication" (let [
    p [0 1]
    q [1 0]
  ] (are [x y z] (= (bike-o-mul x y) z)
   0 p 0
   0 q 0
   1 q 0
   1 p 2
   2 q 1
   2 p 3
) (doseq [k (range 5)
        m (range 3)
        n (range 3)
        o (range 3)
        p (range 3)
     ] (let [
        y [m n]
        z [o p] 
     ] (is (= (bike-o-mul (bike-o-mul k y) z)
              (bike-o-mul k (bike-mul y z))
)))))))

  