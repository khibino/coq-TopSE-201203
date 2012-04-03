Definition x := 3.
Definition foo x y := x * x + y.

Extraction Language Ocaml.
Extraction "foo.ml" foo.

Extraction Language Haskell.
Extraction "foo.hs" foo.

Extraction Language Scala.
Extraction "foo.scala" foo.
