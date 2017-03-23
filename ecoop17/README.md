## Strong Normalization for Dependent Object Types (DOT) ##

### Mechanization in Coq ###

The Coq scripts compile with the command `make`, using `coqc --version` 8.4pl6 (July 2015).

- [`dsubsup_total.v`](dsubsup_total.v) -- termination proof for D<:> as described in the submission (Section 3) 
- [`dsubsup_total_alt.v`](dsubsup_total_alt.v) -- alternative proof for D<:> plus recursive self types and intersection types (see artifact guide below)

### Artifact Guide ###

An artifact guide is available here (PDF)[https://www.cs.purdue.edu/homes/rompf/papers/wang-draft2017a.pdf], which describes the correspondence with the paper as well as the new alternative proof.