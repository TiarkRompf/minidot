
Require Export SfLib.
Require Export Arith.EqNat.
Require Export Arith.Lt.

Require Import dot_storeless_tidy.

Definition Label := nat.

Inductive Var : Type :=
  | VarFr: nat (*absolute position in context, from origin, invariant under context extension*) -> Var
  | VarBd: nat (*bound variable, de Bruijn, locally nameless style -- see open *) -> Var.

Inductive Pth: Set :=
| PthVar: Var -> Pth
| PthSel: Var -> Label -> Pth (* prefix is not (yet) a path *).

Inductive Typ: Set :=
| TypCls: Pth -> Typ (* reference to a type *)
| TypMtd: Typ -> Typ -> Typ (* (x: S)T        where x is locally nameless and can occur in T *)
| TypOfCls: Defs -> Typ (* class { z => (l: T)...}
                                   the type of a path referencing a class, "ClassInfo" in dotty *)
with Trm: Set :=
| TrmVar: Var -> Trm
| TrmApp: Trm -> Label -> Trm -> Trm
| TrmNew: Pth -> Trm
| TrmBlock: Def -> Trm -> Trm (* def is bound to a locally nameless var *)
with Def: Set := (* on paper, Def also contains label, but in Coq, it's given by position (if in
  class body) or by locally nameless (if in term) *)
| DefVal: Typ -> Trm -> Def (* val l: T = t *)
| DefDef: Typ -> Typ -> Trm -> Def (* def m(x: S): T = t     where x is locally nameless *)
| DefCls: Defs -> Def (* class l { z => ds }      where z is a locally nameless self ref *)
| DefNone: Def (* label at this position undefined *)
with Defs: Set := (* labels are given implicitly by position *)
| DefsNil: Defs
| DefsCons: Def -> Defs -> Defs.


Definition Ctx := list Typ.

Hint Unfold Ctx.

Fixpoint index {X : Type} (n : nat) (l : list X) : option X := match l with
| [] => None
| a :: l'  => if beq_nat n (length l') then Some a else index n l'
end.

Fixpoint DefsLength(ds: Defs): nat := match ds with
| DefsNil => 0
| DefsCons _ ds0 => S (DefsLength ds0)
end.

Fixpoint DefsIndex(n: nat)(ds: Defs): option Def := match ds with
| DefsNil => None
| DefsCons d ds0 => if beq_nat n (DefsLength ds0) then Some d else DefsIndex n ds0
end.

Fixpoint open_Var (k: nat) (u: Var) (v: Var) { struct v }: Var := match v with
| VarFr x => VarFr x
| VarBd x => if beq_nat k x then u else VarBd x
end.

Fixpoint open_Pth (k: nat) (u: Var) (p: Pth) { struct p }: Pth := match p with
| PthVar v => PthVar (open_Var k u v)
| PthSel v l => PthSel (open_Var k u v) l
end.

Fixpoint open_Typ (k: nat) (u: Var) (T: Typ) { struct T }: Typ := match T with
| TypCls p => TypCls (open_Pth k u p)
| TypMtd T1 T2 => TypMtd (open_Typ k u T1) (open_Typ (S k) u T2)
| TypOfCls ds => TypOfCls (open_Defs (S k) u ds)
end
with open_Trm (k: nat) (u: Var) (t: Trm) { struct t }: Trm := match t with
| TrmVar v => TrmVar (open_Var k u v)
| TrmApp t0 l t1 => TrmApp (open_Trm k u t0) l (open_Trm k u t1)
| TrmNew p => TrmNew (open_Pth k u p)
| TrmBlock d t0 => TrmBlock (open_Def k u d) (open_Trm (S k) u t0)
end
with open_Def (k: nat) (u: Var) (d: Def) { struct d }: Def := match d with
| DefVal T t => DefVal (open_Typ k u T) (open_Trm k u t)
| DefDef T1 T2 t2 => DefDef (open_Typ k u T1) (open_Typ (S k) u T2) (open_Trm (S k) u t2)
| DefCls ds => DefCls (open_Defs (S k) u ds)
| DefNone => DefNone
end
with open_Defs (k: nat) (u: Var) (ds: Defs) { struct ds }: Defs := match ds with
| DefsNil => DefsNil
| DefsCons d ds0 => DefsCons (open_Def k u d) (open_Defs k u ds0)
end.

Definition openTyp u T := open_Typ 0 u T.
Definition openTrm u t := open_Trm 0 u t.
Definition openDef u d := open_Def 0 u d.
Definition openDefs u ds := open_Defs 0 u ds.


Inductive closedTrm: Trm -> Prop := . (* TODO *)
Inductive closedTyp: Typ -> Prop := . (* TODO *)


Example MutRecExample: Trm :=
(TrmBlock
  (DefCls (*Lib1*) (*z =>*)
    (DefsCons DefNone
    (DefsCons (DefCls (*U*) 
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      DefsNil)))))))))
    )
    (DefsCons (DefCls (*Author*) 
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons (DefDef (*book*) (*u*) (TypCls (PthSel (VarBd 1 (*z*)) 1 (*U*))) (TypCls (PthSel (VarBd 2 (*z*)) 4 (*Book*))) (TrmNew (PthSel (VarBd 2 (*z*)) 4 (*Book*))))
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      DefsNil)))))))))
    )
    (DefsCons DefNone
    (DefsCons (DefCls (*Book*) 
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons (DefDef (*author*) (*u*) (TypCls (PthSel (VarBd 1 (*z*)) 1 (*U*))) (TypCls (PthSel (VarBd 2 (*z*)) 2 (*Author*))) (TrmNew (PthSel (VarBd 2 (*z*)) 2 (*Author*))))
      (DefsCons DefNone
      (DefsCons DefNone
      (DefsCons DefNone
      DefsNil)))))))))
    )
    (DefsCons DefNone
    (DefsCons (DefDef (*run*) (*u*) (TypCls (PthSel (VarBd 0 (*z*)) 1 (*U*))) (TypCls (PthSel (VarBd 1 (*z*)) 4 (*Book*))) (TrmBlock
      (DefVal (*a*) (TypCls (PthSel (VarBd 1 (*z*)) 2 (*Author*))) (TrmApp (TrmNew (PthSel (VarBd 1 (*z*)) 4 (*Book*))) 5 (*author*) (TrmNew (PthSel (VarBd 1 (*z*)) 1 (*U*)))))
      (TrmApp (TrmVar (VarBd 0 (*a*))) 3 (*book*) (TrmNew (PthSel (VarBd 2 (*z*)) 1 (*U*))))
    ))
    (DefsCons DefNone
    (DefsCons DefNone
    DefsNil)))))))))
  )
  (TrmBlock
    (DefVal (*lib1*) (TypCls (PthVar (VarBd 0 (*Lib1*)))) (TrmNew (PthVar (VarBd 0 (*Lib1*)))))
    (TrmApp (TrmVar (VarBd 0 (*lib1*))) 6 (*run*) (TrmNew (PthSel (VarBd 0 (*lib1*)) 1 (*U*))))
  )
).


(* We give typechecking rules in miniscala, which gives us more freedom than relying on DOT's rules,
   and no need to encode nominality, just implement it in these typechecking rules.
   For reduction, however, we use DOT's reduction rules.
   So there are no values in miniscala, we reuse those of DOT.
   We do typechecking & translation to DOT at once, so that we have a Ctx with all necessary
   information the translation might need. *)

(* (trTrm G t T t'), or on paper "G |- t : T ~> t'", means that in context G, the miniscala term t
   typechecks as miniscala type T and translates to DOT term t' *)
Inductive trTrm: Ctx -> Trm -> Typ -> tm -> Prop :=
| trVar: forall G x T,
    x < length G ->
    trTrm G (TrmVar (VarFr x)) T (tvar (VarF x))
(*
| trAppXX: forall,
    trTrm G (TrmApp t1 l t2) 
*)

(* Class lookup, on paper "G |- class p { z => d...}", means that in context G, 
   the path p refers to a class whose definition is { z => d...}. *)
with clLookup: Ctx -> Pth -> Defs -> Prop :=
| clLookup1: forall x G ds,
    index x G = Some (TypOfCls ds) ->
    clLookup G (PthVar (VarFr x)) ds
| clLookup2: forall G x p ds ds0 l,
    trTrm G (TrmVar (VarFr x)) (TypCls p) (tvar (VarF x)) ->
    clLookup G p ds0 ->
    DefsIndex l (openDefs (VarFr x) ds0) = Some (DefCls ds) ->
    clLookup G (PthSel (VarFr x) l) ds.

(*
| TrmApp: Trm -> Trm -> Trm
| TrmNew: Pth -> Trm
| TrmBlock: Def -> Trm -> Trm (* def is bound to a locally nameless var *)
with Def: Set := (* on paper, Def also contains label, but in Coq, it's given by position (if in
  class body) or by locally nameless (if in term) *)
| DefVal: Typ -> Trm -> Def (* val l: T = t *)
| DefDef: Typ -> Typ -> Trm -> Def (* def m(x: S): T = t     where x is locally nameless *)
| DefCls: Defs -> Def (* class l { z => ds }      where z is a locally nameless self ref *)
with Defs: Set := (* labels are given implicitly by position *)
| DefsNil: Defs
| DefsSkip: Defs -> Defs (* label at this position undefined *)
| DefsCons: Def -> Defs -> Defs.

with trTyp: Ctx -> Typ -> ty -> Prop :=
| trTypCls: forall,
    trTrm G (Pth2Trm p) 

: Pth -> Typ (* reference to a type *)
| trTypMtd: Typ -> Typ -> Typ (* (x: S)T        where x is locally nameless and can occur in T *)
| trTypOfCls: Decls -> Typ (* class { z => (l: T)...}    the type of a class, "ClassInfo" in dotty *)
with trDecls: Ctx -> Decls -> ty -> Prop :=
| trDeclsNil: Decls
| trDeclsSkip: Decls -> Decls (* label at this position undefined *)
| trDeclsCons: Typ -> Decls -> Decls.


trTrm
trDef
trTyp
*)



