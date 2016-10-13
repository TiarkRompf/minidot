Type Soundness Proofs with Definitional Interpreters
====================================================

Paper draft: [[pdf](http://cs.purdue.edu/~rompf/papers/amin-draft2016a.pdf)]

The Coq scripts compile with the command `make`, using `coqc --version` 8.4pl6 (July 2015).

- [STLC](stlc.v)
- [F<:](fsub.v)
- [F<: Equivalence with Small-Step](fsub_equiv.v)
- [F<: with Mutable References](fsub_mut.v)
- [F<: with Exceptions](fsub_exn.v)
- [F<:> from the System D Square](fsubsup.v)
- [D<:> from the System D Square](dsubsup.v)
- [DOT in Big-Step](dot.v)

For Step-by-Step Instructions, please see Appendix B of the paper (_Type Soundness Proofs with Definitional Interpreters_, forthcoming), which outlines a correspondence between the formalisms in the paper and in Coq. 
