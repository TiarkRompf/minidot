POT 
===


### Syntax

    Var     x, y, z
    Label   a, b, c, f, l, m
    Term              t ::= x                      variable
                            lambda(x:T)t           function
                            [T]                    type tag ("wrapped type")
                            {z => (l: T = i)...}   object construction
                            t.l
                            t t
    Value*            v ::= lambda(x:T)t           function     
                            [T]                    type tag ("wrapped type")
                            {z => (l: T = v)...}   object value
    Initialization*   i ::= x
                            v
    Path*          p, q ::= x
                            [T]
                            {z => (l: T = v)...}
                            p.l
    Type        S, T, U ::= Top
                            Bot
                            {a: T}                 record with one val/def/type member
                            all(x:T)U              function type
                            [T..U]                 type of type tags, with bounds
                            p!                     unwrap type tag
                            {z => T}               bind type
                            T /\ T                 intersection
                            T \/ T                 union

    * = predicate on terms defining a subset of the terms

Note that contrary to previous DOT versions, there's no distinction between type/method/value members on objects, but there are only value members, and lambdas and type tags are separate kinds of terms. This has the following advantages:

- It helps disentangle the dependencies between the various features of the calculus. In particular, we can remove objects from the calculus (or from a subset of the language for which we attempt to prove termination) without losing lambdas and dependent types.
- The proofs become simpler: In the current proofs, we often have a case "type member" and a case "def member". The former mixes aspects of "selecting a member" with aspects of dependent types, and the latter duplicates the code dealing with "selecting a member" and mixes it with aspects of lambdas. If we have separate term forms for selection, type tags, and lambdas, there's no more mixing of different aspects and no more code duplication.


### Reduction rules

Reduction:

    (lambda(x:T)t1) v -> [v/x]t1
        
    {z => (l: T = v); d...}.l -> [{z => (l: T = v); d...}/z]v
    

Congruence:
    
    t -> t'
    -----------
    t.l -> t'.l
        
    t1 -> t1'
    -----------------
    t1 t2 -> t1' t2

    t -> t'
    -----------
    v t -> v t'

    
### Goals

1. In current DOT, the only terms allowed in front of type selections are vars: `x.T`. We want to allow a bigger subset of terms, ultimately allowing lambdas, so that higher kinded types could be encoded as term-level lambdas: Eg given `Pair: all(T: [Bot..Top])[{ fst: T!, snd: T! }..{ fst: T!, snd: T! }]`, we could define `let NestedPair = lambda(T: [Bot..Top])(Pair (Pair T)) in NestedPair [Int]`. But for now, lambdas are out of reach, but let's at least try to have paths of length > 1 and see what we learn from it.
2. Encode and explain nominality in a simple way, also for mutually recursive classes. This requires paths of length > 1 (see slides 32/33 of Samuel's semester project [presentation](https://github.com/samuelgruetter/dot-calculus/blob/master/doc/Connecting-Scala-to-DOT/slides.pdf)).


### Constructing nested objects / The right-hand side of val defs

In order for paths to make sense, objects must have val defs initialized with an rhs term.
Allowing arbitrary terms in the rhs has problems:

- The reduction rules become more complex (more complex congruence rules needed), and this distracts us from the more interesting aspects. Even uniquness of the small step reduction rules is not so easy any more (see https://github.com/TiarkRompf/minidot/commit/4f133a1).
- We have to deal with initialization order problems and circular dependencies. These are interesting problems, but it's not yet the time to tackle them.
- If the rhs starts with the self reference, we can get non-terminating paths such as `{z => l = z.l}.l`, and if we select a type member on such a path, we can get unsoundness.

Instead, it is much simpler to rewrite object constructions with terms in val def rhs, such as `{z => l = t}`, to `let x = t in {z => l = x}`. On rhs of val defs, we then only allow values or variables, and we call these "initializations", and refer to them with the non-terminal `i`.

Now maybe there's still a problem:

- What if the rhs is just a self ref, such as `{z => l = z}`?

But maybe that's not a problem, or at least I can't see right now why it should.


### The new soundness problem

However, there's still one serious problem which cannot be solved with restrictions to the grammar, because it can also occur if the self ref never occurs in the unsound *term*, but only in its unsound *typing derivation*: For instance, this typechecks, because to typecheck the rhs of `f`, we can use subtyping transitivity over `a.f.C`, which has bad bounds:

    let a = new { a =>
      val f: { type C: Top..Bot } = new { type C = Top }
      def bad(x1: Top): Bot = let x2: a.f.C = x1 in x2
    } in ...

Note that it still typechecks (assuming non-algorithmic typechecking rules) if we remove the type annotations, and then the self ref `a` is never used anywhere, so that's why syntactic restrictions don't help.

We will have to fix this with "restricted vars" or another trick.


### Type annotations for val defs?

So let's repeat once more that whether we have type annotations in val defs does not matter for the new soundness problem. However, it does matter for Goal 2: We need the annotation in order to upcast a concrete type member to an abstract one, lower-bounded by bottom. Because of this, and for simplicity, let's decide to always put a type annotation in val defs.


### "Restricted vars": A possible solution for the "new soundness problem"

In order to prevent the above unsound example from typechecking, we have to restrict the usage of self refs in typing derivations.
Consider this:

    { a =>
       val Bad1: { type C: Top..Bot } = new { type C = Top }
       val l = { b =>
          val m: T1 = v
          val f: T2 -> T3 = lambda(x: T2)t
          val Bad2: { type C: Top..Bot } = new { type C = Top }
       }
    }

While typechecking `v`, we should not be able to use the self refs `a` and `b`, because otherwise we can prove that bad bounds are good, since putting `a` and `b` into `G` means assuming that `a` and/or `b` are actual instantiated objects with good bounds.

On the other hand, as soon as we're "behind" one more lambda-bound variable, as when typechecking `t`, we can use `a` and `b`, because `t` will only be run *after* the instantiation of the objects, so it's safe to assume that they are actual instantiated objects with good bounds.

To formalize this intuition, we can use *restricted vars*: They are self ref variables which have to be put into the environment `G`, but are not yet safe for use. We keep track of them by putting them into a set of variables `R`, which is always a subset of `dom G`.

The judgments which were `G |- ...` before now become `G R |- ...`.

The typechecking rule `T-NEW` now declares the self ref as a restricted var:

    (G, z: T) (R union {z}) |- ds : T
    ---------------------------------
    G R |- { z => ds } : { z => T}

and `T-VAR` basically disallows the usage of restricted vars:

    (x: T) in G    x notin R
    ------------------------
    G R |- x: T

But there are two ways to use them anyways: The first is in the following three subtyping rules:

       x in (dom G)            x in (dom G)           x in (dom G)
    -----------------       -----------------       -----------------
    G R |- x.A <: Top       G R |- Bot <: x.A       G R |- x.A <: x.A

And the second is by entering the body of a lambda, which makes all vars unrestricted:

    (G, x: T) (empty) |- u: U
    ---------------------------------
    G R |- lambda(x: T)u : all(x: T)U

The subtyping rules don't create new restricted vars (not even for "bind" types), but just keep the existing ones:

    (G, x: T2) R |- T2 <: T1, U1 <: U2
    -----------------------------------
    G R |- all(x: T1)U1 <: all(x: T2)U2
    
    (G, z: T1) R |- T1 <: T2
    ---------------------------------
    G R |- { z => T1 } <: { z => T2 }

Note: This solution is just an idea, and I believe that it makes POT sound, but I have not (yet) proved anything about it.

