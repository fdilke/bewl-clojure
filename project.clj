(defproject bewl "1.0.0-SNAPSHOT"
  :description "Felix's topos crunching 1000 year project"
  :url "http://github.com/fdilke/bewl-clojure"
  :main bewl.perf-tests
  :license {
     :name "Eclipse Public License"
     :url "http://www.eclipse.org/legal/epl-v10.html"
  }
  :dependencies [
    [org.clojure/clojure "1.6.0"]
    [org.clojure/math.combinatorics "0.1.1"]
    [swank-clojure "1.4.2"]
  ]
  :jvm-opts ["-Xmx1g" "-server"]
  :repl-init bewl.bewl
  :target-path "target/%s"
)
