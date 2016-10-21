_A good proof is one that makes us wiser._ -- Yuri Manin

The DOT Calculus and its Variations
===================================

Formalizations of the Dependent Object Types (DOT) calculus, from the bottom up, with soundness proofs at each step.

- From F to DOT: Type Soundness Proofs with Definitional Interpreters (POPL'17) [[pdf preprint]](https://www.cs.purdue.edu/homes/rompf/papers/amin-draft2016a.pdf)
  - [STLC](http://sound-big-step-stlc.namin.net)
  - [F<:](http://sound-big-step-fsub.namin.net)
  - [F<: equivalence with Small-Step](./big/fsub_equiv.v)
  - [F<: with Mutable References](http://sound-big-step-mut.namin.net)
  - [F<: with Exceptions](http://sound-big-step-exceptions.namin.net)
  - [F<:> from the System D Square](http://sound-big-step-fsubsup.namin.net)
  - [D<:> from the System D Square](http://sound-big-step-dsubsup.namin.net)
  - [DOT in big-step](http://sound-big-step-dot.namin.net)
  - [older developments from 2015](./dev2015)

- Type Soundness for Dependent Object Types (OOPSLA'16) [[pdf]](http://lampwww.epfl.ch/~amin/dot/soundness_oopsla16.pdf)
  - [DOT in small-step](./oopsla16)

- Foundations of Path-Dependent Types (OOPSLA'14) [[pdf]](http://lampwww.epfl.ch/~amin/dot/fpdt.pdf)
  - [muDOT](./oopsla/dot.elf)
