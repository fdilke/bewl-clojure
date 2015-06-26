(ns bewl-test.algebra.test-structures
  (:use [clojure test set] 
        [bewl topos-util util topos-of-sets]
        bewl.algebra.structures
        bewl.algebra.constructions
))

(deftest test-structures 
  (testing "Experiments with magmas" (let [
     X (set-of :a :b :c)
     dud-multiply (id X)
     good-multiply (binary-set-op X { 
         [:a :a] :b [:a :b] :c [:a :c] :a
         [:b :a] :b [:b :b] :b [:b :c] :b
         [:c :a] :a [:c :b] :b [:c :c] :c
     }) ; a sample 'multiarrow' binary op XxX-> Z
   ] ; check you have to define all the operations
   (is (thrown? IllegalArgumentException (verify-algebra {:carrier X :theory magma})))
   ; check they have to have the right arity
   (is (thrown? IllegalArgumentException (verify-algebra {:carrier X :theory magma
                                                          :multiply dud-multiply})))
   ; check we can build a magma if we supply a multiplication, and it's ok to include non-magma-related keys
   (is (= true (verify-algebra {:carrier X :theory magma 
                                :multiply good-multiply :extra-key []})))
  )) (testing "Experiments with monoids" (let [
    X (set-of 1 :x :y)            
    good-unit (set-element X 1)
    bad-unit (set-element X :x)
    good-multiply (binary-set-op X 
      (fn [x y] (if (= x 1) y x))
    ) bad-multiply (binary-set-op X   ; a multiplication that makes 1 a unit, but isn't associative 
      (fn [x y] (cond (= x 1) y (= y 1) x :default 1)) ; not associative: 1 :y = :x :x :y = :x 1
    )
    good-monoid {:carrier X :theory monoid
                 :multiply good-multiply :unit good-unit }
    ] 
    (is (= true (verify-algebra good-monoid)))
    (is (= false (commutative? good-monoid)))
    (is (thrown? IllegalArgumentException (verify-algebra 
        {:carrier X :theory monoid
         :multiply good-multiply :unit bad-unit })))
    (is (thrown? IllegalArgumentException (verify-algebra
        {:carrier X :theory monoid
         :multiply bad-multiply :unit good-unit})))
 )) (testing "Experiments with groups/abelian groups/rings" (let [
        X (apply set-of (range 7))
        unit (set-element X 0)
        one  (set-element X 1)
        multiply (binary-set-op X (fn [x y] (mod (* x y) 7)))
        plus (binary-set-op X (fn [x y] (mod (+ x y) 7)))
        minus (set-arrow X X (fn [x] (mod (- 7 x) 7)))
        Z-7 {:carrier X }
        Z-7-monoid (into Z-7 {:theory monoid :unit unit :multiply plus})
        Z-7-group (into Z-7 {:theory group :unit unit :inverse minus :multiply plus})
        Z-7-abelian-group (into Z-7 {:theory abelian-group :zero unit :minus minus :plus plus})
        Z-7-ring (into Z-7 {:theory ring :zero unit :unit one :minus minus :plus plus :multiply multiply})
        ] (is (= true (verify-algebra Z-7-monoid)))
          (is (= true (verify-algebra Z-7-group))) 
          (is (= true (verify-algebra Z-7-abelian-group))) 
          (is (= true (verify-algebra Z-7-ring))) 
          (is (= true (commutative? Z-7-group)))
          (is (= true (commutative? Z-7-ring)))
          ; sanity check: verify some derived laws
          (is (= true (verify-law Z-7-monoid (fn [{:keys [unit multiply]}]
                 (= unit (multiply unit unit))))))
          (is (= true (verify-law Z-7-group (preservation-law :inverse :multiply))))
          (is (= true (verify-law Z-7-ring  (fn [{:keys [zero multiply]} x]
                 (= zero (multiply x zero)))))))
          ; Sanity tests on the theory of rings, now it's expressed in terms of abelian groups / monoids
          (is (= 5 (count (ring :signature))))
          (is (= 8 (count (ring :laws))))
    ) (testing "Experiments with Heyting algebras" (let [
        X (set-of #{} #{:a} #{:b} #{:c} #{:a :b} #{:b :c} #{:a :c} #{:a :b :c})
        the-false (set-element X #{})
        the-true (set-element X #{:a :b :c})
        the-and (binary-set-op X intersection)
        the-or  (binary-set-op X union)
        implies (binary-set-op X (fn [x y] (union (difference #{:a :b :c} x) y)))
        H-alg   {:carrier X :theory heyting-algebra
                 :false the-false :true the-true :and the-and :or the-or
                 :implies implies }
    ] (is (= true (verify-algebra H-alg)))
      ; verify that implies DOESN'T right-distribute over and
      (is (= false (verify-law H-alg (right-distributive-law :implies :and)))) 
      ; and that and, or DO distribute over each other
      (is (= true (verify-law H-alg (left-distributive-law :or :and)))) 
      (is (= true (verify-law H-alg (left-distributive-law :and :or)))) 
)) (testing "Extending algebraic theories" (let [
       recover-components-law (fn [{:keys [left right join]} x y]
						                     (and (= x (left  (join x y)))
						                          (= y (right (join x y)))))
       rejoin-law (fn [{:keys [left right join]} x]
                          (= x (join (left x) (right x))))
       tree { :signature { :left 1 :right 1 :join 2}
              :laws [recover-components-law rejoin-law]
              :param-spaces [:pig]
            }
       X (set-of 0)
       left  (id X)
       right (id X)
       join  (binary-set-op X (fn [x y] 0))
       T     {:carrier X :theory tree 
              :pig (Z-mod-n 3)
              :left left :right right :join join}
       atomic-root-law (fn [{:keys [left right join root]}]
                           (= root (join root root)))
       rooted-tree (extend-theory tree {
             :signature { :root 0 }                                        
             :laws      [atomic-root-law]
             :param-spaces [:dog] 
       })
       rooted-T     {:carrier X :theory rooted-tree
                     :pig (Z-mod-n 3) :dog (Z-mod-n 2)
                     :left left :right right :join join :root (set-element X 0)}
       ; test we can extend an empty theory and get sensible defaults
       extensions { :signature { :yada 1 } :laws [ atomic-root-law ] :param-spaces [:hog]}
       more-extensions { :signature { :foofoo 3 } :laws [atomic-root-law] :param-spaces [:yo :dawg] }
    ] (is (= true (verify-algebra T))) ; sanity check
      (is (= true (verify-algebra rooted-T)))
      (is (= rooted-tree { :signature {:left 1 :right 1 :join 2 :root 0 }
                           :laws [ recover-components-law rejoin-law atomic-root-law ] 
                           :param-spaces [:pig :dog]
      }))
      (is (= (extend-theory {} extensions) extensions))
      (is (= (extend-theory {} extensions more-extensions) {
          :signature { :yada 1 :foofoo 3 }
          :laws [ atomic-root-law atomic-root-law ]
          :param-spaces [ :hog :yo :dawg ]
      }))
   )) (testing "Monoid actions, modules and parameter spaces" (let [
       Z-6 (Z-mod-n 6)
       R (Z-6 :carrier)
       M (set-of 0 3)
       right-multiply  (heterogeneous-binary-set-op M R M (fn [x y] (mod (* x y) 6)))
       good-action { :carrier M :theory right-monoid-action
                     :scalars Z-6 :right-multiply right-multiply}
       good-module { :carrier M :theory right-module
                     :scalars Z-6 :right-multiply right-multiply}
      ] (is (= true (verify-algebra good-action)))
        (is (= true (verify-algebra good-module)))
)) (testing "Detecting whether an arrow is a morphism relative to some algebraic theory" (let [
    Z-6 (Z-mod-n 6)
    Z-3 (Z-mod-n 3)
    mod-3 (set-arrow (Z-6 :carrier) (Z-3 :carrier) #(mod % 3))
    only-group-morphism (set-arrow (Z-6 :carrier) (Z-3 :carrier) { 0 0 1 2 2 1 3 0 4 2 5 1 })
   ] (is (= true (morphism? ring Z-6 Z-3 mod-3)))                                                                                               
     (is (= false (morphism? ring Z-6 Z-3 only-group-morphism)))                                                                                               
     (is (= true (morphism? abelian-group Z-6 Z-3 only-group-morphism)))                                                                                               
)))
