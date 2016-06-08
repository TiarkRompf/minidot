## Type Soundness for Dependent Object Types (DOT) ##

### Mechanization in Coq ###

The Coq scripts compile with the command `make`, using `coqc --version` 8.4pl6 (July 2015).

- [`dot.v`](dot.v) -- model and common infrastructure and lemmas
- [`dot_soundness.v`](dot_soundness.v) -- main soundness proof, based on subtyping transitivity pushback
- [`dot_soundness_alt.v`](dot_soundness_alt.v) -- alternative soundness proof, based on directly invertible value typing aka possible types
- [`dot_exs.v`](dot_exs.v) -- some examples, just sanity checks for expressivity
