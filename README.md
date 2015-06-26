Bewl (Clojure version)
======================

This is the Clojure version of Bewl from 2011-2012, which I ported from
Java and then to Scala when the limitations of Clojure became evident.

Clojure is wonderful, but in the end I missed types and classes too much.
There were also some worries about performance, given how compute-intensive
Bewl computations can be.  

This is a Leiningen project. You can run all the tests with:

    lein test

Or to run the performance tests:

    lein run

To get a console with the main Bewl namespaces imported:

    lein repl

There are some (very) rough notes about the history and motivation of the 
project [here](https://github.com/fdilke/bewl-java/tree/master/doc).

In brief:

- I define a Topos "protocol" and a FiniteSets which implements it.
- You can do calculations with products, equalizers, exponentials and subobject classifiers.
- There is also a way to define algebraic structures and their theories (Group, Monoid etc.)
and some simple constructions using these (automorphism group of an object, etc).

So I replicated more or less everything the Java version could do, mostly with
more expressive and elegant (if slower) code.

It's much easier to define algebraic structures in the Clojure version. See
the "algebra" package for neat definitions of theories and laws.

I moved to Scala mainly because it seemed clear that the whole project 
needed to be typesafe, but also in the hope of better IDE support. It also
seemed that a more 'traditionally algebraic' DSL might be better for Bewl than
Clojure's homoiconic approach.

In particular, constructions.clj (building new algebraic structures out of 
existing ones) should be significantly easier to write and understand in Scala.
 
See the [Scala version](http://github.com/fdilke/bewl) and judge for yourself.
