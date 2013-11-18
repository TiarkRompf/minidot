_A good proof is one that makes us wiser._ -- Yuri Manin

minidot
=======

We are formalizing the Dependent Object Types (DOT) calculus, from the bottom up, proving it sound at each step.

* [dev/dot.elf](dev/dot.elf) is the latest development in Twelf, complete with a full type safety proof.

* We auto-generate the typesetted rules ([PDF highlight](http://lampwww.epfl.ch/~amin/dot/minidot.pdf)) from the Twelf code.

* We also use Twelf as a backend to run queries to test the expressivity of our calculus:
  test [data](src/test/dot/) and [queries](src/main/elf/tests.elf).
