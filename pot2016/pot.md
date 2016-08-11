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

1. In currently DOT, the only terms allowed in front of type selections are vars: `x.T`. We want to allow a bigger subset of terms, ultimately allowing lambdas, so that higher kinded types could be encoded as term-level lambdas: Eg given `Pair: all(T: [Bot..Top])[{ fst: T!, snd: T! }..{ fst: T!, snd: T! }]`, we could define `let NestedPair = lambda(T: [Bot..Top])(Pair (Pair T)) in NestedPair [Int]`. But for now, lambdas are out of reach, but let's at least try to have paths of length > 1 and see what we learn from it.
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

TODO copy from INR331 whiteboard


## Notes

pty, dty, tty

ty_pth, ty_def, ty_trm

Substitution:
    [v/x]x.l!  =  v.l!    must be a valid type

    
## Garbage

    {z => (l: T = v)...}:Term -> {z => (l: T = v)...}:Value         [needed in Coq only]

This is a type, and types don't step:
    x.l!  ->  {z => d...}.l!  ->  [T]!

