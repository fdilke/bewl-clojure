(ns bewl-test.core
  (:use [bewl.core])
  (:use [clojure.test])
)

(deftest test-add-two-numbers
  (is (= 7 (add-two-numbers 2 5)))
)
