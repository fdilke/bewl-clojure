(ns bewl-test.test-util
  (:use clojure.test 
        [bewl util])
)

(deftest test-map-map
  (let [m { :x 1 :y 3 }]
  (is (= { :x 2 :y 4 } (map-map inc m)))
))

(deftest test-arity
  (is (= 0 (arity #(1))))
  (is (= 1 (arity #(%))))
  (is (= 2 (arity #(%1 %2))))
  (is (= 2 (arity (fn [x y] 0))))
)

(deftest test-enforce-arity (let [
  sum (fn [summands] (apply + summands))
  two 2
  three 3 ; checking this works with non-constant/literal arguments
  sum2 (enforce-arity two sum)
  sum3 (enforce-arity three sum)
  ] (is (= 2 (arity sum2)))
    (is (= 3 (arity sum3)))
    (is (= 7 (sum2 2 5)))
    (is (= 8 (sum3 3 2 3)))
))

(deftest test-unpack-bindings
  (is (= [[:a :b :c] [1 2 3]]
         (unpack-bindings [:a 1 :b 2 :c 3])))
)