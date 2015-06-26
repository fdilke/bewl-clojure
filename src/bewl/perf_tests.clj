(ns bewl.perf-tests
  (:gen-class)
  (:use [bewl topos-of-sets topos-util]
        bewl.algebra.structures
        bewl.algebra.constructions
))

(defn run []
  (println "Running Bewl performance tests.")
  (let [
    X (set-of :a :b :c :d :e)
    Y (set-of 1 2 3 4 5 6 7 8 9 10)
    _ (println "Calculating " Y "^" X "...")
    X-exp-X (time ((sets :exponential) Y X))
  ] (println "Done")
) (let [
        X (set-of 0 1 2)
        S (endomorphism-action X)
        M (S :scalars)
   ] (println "verifying End(3)")
     (time (verify-algebra M))
     (println "Done!!")
))

; 10^5 takes at least 10 seconds using "non-lazy sets"
(defn -main []
  (run)
)

