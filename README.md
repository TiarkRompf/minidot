_A good proof is one that makes us wiser._ -- Yuri Manin

The DOT Calculus and its Variations
===================================

Formalizations of the Dependent Object Types (DOT) calculus, from the bottom up, with soundness proofs at each step.

- Towards Strong Normalization for Dependent Object Types (ECOOP'17) [[pdf]](https://www.cs.purdue.edu/homes/rompf/papers/wang-ecoop17.pdf)
  - [D<:> with extensions](./ecoop17/dsubsup_total_rec.v)

- From F to DOT: Type Soundness Proofs with Definitional Interpreters (POPL'17) [[pdf]](https://www.cs.purdue.edu/homes/rompf/papers/amin-popl17a.pdf)
  - [STLC](./popl17/stlc.v)
  - [F<:](./popl17/fsub.v)
  - [F<: Equivalence with Small-Step](./popl17/fsub_equiv.v)
  - [F<: with Mutable References](./popl17/fsub_mut.v)
  - [F<: with Exceptions](./popl17/fsub_exn.v)
  - [F<:> from the System D Square](./popl17/fsubsup.v)
  - [D<:> from the System D Square](./popl17/dsubsup.v)
  - [DOT in Big-Step](./popl17/dot.v)
  - [older developments from 2015](./dev2015)

- Type Soundness for Dependent Object Types (OOPSLA'16) [[pdf]](http://lampwww.epfl.ch/~amin/dot/soundness_oopsla16.pdf)
  - [DOT in small-step](./oopsla16)

- Foundations of Path-Dependent Types (OOPSLA'14) [[pdf]](http://lampwww.epfl.ch/~amin/dot/fpdt.pdf)
  - [muDOT](./oopsla14)
