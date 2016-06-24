POT 
===


### Syntax

    Var          x, y, z
    Label        a, b, c, f, l, m
    Term         t ::= x                      variable
                       lambda(x:T)t           function
                       [T]                    type tag ("wrapped type")
                       {z => (l: T = i)...}   object construction (rhs in defs must be terms with z not at top-level)
                       t.l
                       t t
    Value*       v ::= lambda(x:T)t           function
                       [T]                    type tag ("wrapped type")
                       {z => (l: T = v)...}   object (rhs in defs must be values)
    Init'zation* i ::= x
                       v
    Path*     p, q ::= x
                       [T]
                       {z => (l: T = v)...}
                       p.l
    Type   S, T, U ::= Top
                       Bot
                       {a: T}                 record with one val/def/type member
                       all(x:T)U              function type
                       [T..U]                 type of type tags, with bounds
                       p!                     unwrap type tag
                       {z => T}               bind type
                       T /\ T                 intersection
                       T \/ T                 union

    * = predicate on terms

Substitution: Only var-by-value (during evaluation) and var-by-path (during typing)
The isValue judgment is needed to define the reduction relation.
No isPath judgment is needed, but we use a path typing ("htp" or "pty") judgment, which tells us what a path is.

Var-by-Path substitution:

    p : {z => T}
    -------------
    p : [p/z]T

Problem: Define selection 2x? once p.l, once t.l, define step for it 2x?
That's why we don't have path as a real syntactic construct  p ::= x | v | p.l

Note: This version of POT is not sound:

    let a = new { a =>
      val f: { type C: Top..Bot } = new { type C = Top }
      def bad(x1: Top): Bot = let x2: a.f.C = x1 in x2
    } in ...

We will have to fix this with "restricted vars" or another trick.


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

    
    
## Notes

pty, dty, tty

ty_pth, ty_def, ty_trm

Substitution:
    [v/x]x.l!  =  v.l!    must be a valid type

    
## Garbage

    {z => (l: T = v)...}:Term -> {z => (l: T = v)...}:Value         [needed in Coq only]

This is a type, and types don't step:
    x.l!  ->  {z => d...}.l!  ->  [T]!

