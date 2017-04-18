## Strong Normalization for Dependent Object Types (DOT) ##

Paper (ECOOP 2017): [[pdf](https://www.cs.purdue.edu/homes/rompf/papers/wang-ecoop17.pdf)]

### Mechanization in Coq ###

The Coq scripts compile with the command `make`, using `coqc --version` 8.4pl6 (July 2015).

- [`dsubsup_total.v`](dsubsup_total.v) -- termination proof for plain D<:> (Section 3) 
- [`dsubsup_total_rec.v`](dsubsup_total_rec.v) -- termination proof for D<:> plus recursive self types and intersection types (Section 4)

### Artifact Guide ###

Appendix A of the paper, _Strong Normalization for Dependent Object Types (DOT)_ ([PDF](https://www.cs.purdue.edu/homes/rompf/papers/wang-ecoop17.pdf)), describes the correspondence between the formalism on paper and the development in Coq.