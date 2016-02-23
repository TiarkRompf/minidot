_A good proof is one that makes us wiser._ -- Yuri Manin

The DOT Calculus and its Variations
===================================

Formalizations of the Dependent Object Types (DOT) calculus, from the bottom up, with soundness proofs at each step.

- From F to DOT: Type Soundness Proofs with Definitional Interpreters [[pdf]](http://arxiv.org/pdf/1510.05216.pdf)
  - [simply typed lambda calculus](/dev2015/nano0.v)
  - [F_<:](/dev2015/fsub0.v)
  - [D_<:](/dev2015/fsub2.v) (F_<: with first-class types and lower bounds)
  - [D_<: with state](dev2015/fsub4.v) (add mutable references to D_<:)
  - [full DOT](/dev2015/dot24.v) (D_<: plus intersection and union types, recursive self types, compound objects, ...)
  - [back to small-step](/dev2015/dot-smallstep1.v) (soundness for full DOT with respect to small-step semantics)

- Foundations of Path-Dependent Types (OOPSLA'14) [[pdf]](http://lampwww.epfl.ch/~amin/dot/fpdt.pdf)
  - [muDOT](/oopsla/dot.elf)
