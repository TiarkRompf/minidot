
Require Export SfLib.
Require Export Arith.EqNat.
Require Export Arith.Lt.

(*
TODO give nuDOT this signature (same var binding scheme as dot_storeless_tidy.v),
then just import it instead of redefining
Require Import nuDOT.
*)

Module nuDOT.

Definition lb := nat.

Inductive vr : Type :=
  | VarF: nat (*absolute position in context, from origin, invariant under context extension*) -> vr
  | VarB: nat (*bound variable, de Bruijn, locally nameless style -- see open *) -> vr
  | VObj: dms(*self is bound, de Bruijn, var*) -> vr
with ty : Type :=
  | TCls   : ty -> ty -> ty (* [x: S | T], T intersection type *)
  | TBot   : ty
  | TTop   : ty
  | TFun   : lb -> ty -> ty -> ty
  | TMem   : lb -> ty -> ty -> ty
  | TSel   : vr -> lb -> ty
  | TBind  : ty -> ty
  | TAnd   : ty -> ty -> ty
  | TOr    : ty -> ty -> ty
with  tm : Type :=
  | tvar  : vr -> tm
  | tsel  : tm -> lb -> tm (* TODO split tapp into tsel & tapp in nuDOT, like here *)
  | tapp  : tm -> tm -> tm
  | tnew  : tm -> tm  (* new t, where t must be of type TCls *)
  | tcls  : ty -> dms -> tm
  | tmix  : tm -> tm -> tm
with dm : Type :=
  | dnone : dm
  | dfun : ty -> ty -> tm -> dm
  | dty  : ty -> dm
with dms : Type :=
  | dnil : dms
  | dcons : dm -> dms -> dms.

End nuDOT.

Module miniscala.

Definition Label := nat.

Inductive Var : Type :=
  | VarF: nat (*absolute position in context, from origin, invariant under context extension*) -> Var
  | VarB: nat (*bound variable, de Bruijn, locally nameless style -- see open *) -> Var.

Inductive Pth: Set :=
| PthVar: Var -> Pth
| PthSel: Var -> Label -> Pth (* prefix is not (yet) a path *).

Inductive Typ: Set :=
| TypCls: Pth -> Typ (* reference to a type *)
| TypMtd: Typ -> Typ -> Typ (* (x: S)T        where x is locally nameless and can occur in T *)
| TypOfCls: Decls -> Typ (* class { z => (l: T)...}    the type of a class, "ClassInfo" in dotty *)
with Decls: Set := (* labels are given implicitly by position *)
| DeclsNil: Decls
| DeclsSkip: Decls -> Decls (* label at this position undefined *)
| DeclsCons: Typ -> Decls -> Decls.

Inductive Trm: Set :=
| TrmVar: Var -> Trm
| TrmSel: Trm -> Label -> Trm
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


Definition Ctx := list Typ.

Hint Unfold Ctx.

Fixpoint index {X : Type} (n : nat) (l : list X) : option X := match l with
| [] => None
| a :: l'  => if beq_nat n (length l') then Some a else index n l'
end.

Fixpoint DeclsLength(Ds: Decls): nat := match Ds with
| DeclsNil => 0
| DeclsSkip Ds0 => S (DeclsLength Ds0)
| DeclsCons _ Ds0 => S (DeclsLength Ds0)
end.

Fixpoint DeclsIndex(n: nat)(Ds: Decls): option Typ := match Ds with
| DeclsNil => None
| DeclsSkip Ds0 => if beq_nat n (DeclsLength Ds0) then None else DeclsIndex n Ds0
| DeclsCons T Ds0 => if beq_nat n (DeclsLength Ds0) then Some T else DeclsIndex n Ds0
end.

Fixpoint open_Var (k: nat) (u: Var) (v: Var) { struct v }: Var := match v with
| VarF x => VarF x
| VarB x => if beq_nat k x then u else VarB x
end.

Fixpoint open_Pth (k: nat) (u: Var) (p: Pth) { struct p }: Pth := match p with
| PthVar v => PthVar (open_Var k u v)
| PthSel v l => PthSel (open_Var k u v) l
end.

Fixpoint open_Typ (k: nat) (u: Var) (T: Typ) { struct T }: Typ := match T with
| TypCls p => TypCls (open_Pth k u p)
| TypMtd T1 T2 => TypMtd (open_Typ k u T1) (open_Typ (S k) u T2)
| TypOfCls Ds => TypOfCls (open_Decls (S k) u Ds)
end
with open_Decls (k: nat) (u: Var) (Ds: Decls) { struct Ds }: Decls := match Ds with
| DeclsNil => DeclsNil
| DeclsSkip Ds0 => DeclsSkip (open_Decls k u Ds0)
| DeclsCons T Ds0 => DeclsCons (open_Typ k u T) (open_Decls k u Ds0)
end.

Fixpoint open_Trm (k: nat) (u: Var) (t: Trm) { struct t }: Trm := match t with
| TrmVar v => TrmVar (open_Var k u v)
| TrmSel t0 l => TrmSel (open_Trm k u t0) l
| TrmApp t0 t1 => TrmApp (open_Trm k u t0) (open_Trm k u t1)
| TrmNew p => TrmNew (open_Pth k u p)
| TrmBlock d t0 => TrmBlock (open_Def k u d) (open_Trm (S k) u t0)
end
with open_Def (k: nat) (u: Var) (d: Def) { struct d }: Def := match d with
| DefVal T t => DefVal (open_Typ k u T) (open_Trm k u t)
| DefDef T1 T2 t2 => DefDef (open_Typ k u T1) (open_Typ (S k) u T2) (open_Trm (S k) u t2)
| DefCls ds => DefCls (open_Defs (S k) u ds)
end
with open_Defs (k: nat) (u: Var) (ds: Defs) { struct ds }: Defs := match ds with
| DefsNil => DefsNil
| DefsSkip ds0 => DefsSkip (open_Defs k u ds0)
| DefsCons d ds0 => DefsCons (open_Def k u d) (open_Defs k u ds0)
end.

Definition openTyp u T := open_Typ 0 u T.
Definition openTrm u t := open_Trm 0 u t.

Fixpoint Pth2Trm (p: Pth): Trm := match p with
| PthVar x => TrmVar x
| PthSel x l => TrmSel (TrmVar x) l
end.

Inductive closedTrm: Trm -> Prop := . (* TODO *)
Inductive closedTyp: Typ -> Prop := . (* TODO *)

(* We give typechecking rules in miniscala, which gives us more freedom than relying on nuDOT's rules,
   and no need to encode nominality, just implement it in these typechecking rules.
   For reduction, however, we use nuDOT's reduction rules.
   So there are no values in miniscala, we reuse those of nuDOT.
   We do typechecking & translation to nuDOT at once, so that we have a Ctx with all necessary
   information the translation might need. *)

(* (trTrm G t T t'), or on paper "G |- t : T ~> t'", means that in context G, the miniscala term t
   typechecks as miniscala type T and translates to nuDOT term t' *)
Inductive trTrm: Ctx -> Trm -> Typ -> nuDOT.tm -> Prop :=
| trVar: forall G x T,
    x < length G ->
    trTrm G (TrmVar (VarF x)) T (nuDOT.tvar (nuDOT.VarF x))
| trSel1: forall G l Ds U p x x' c,
    DeclsIndex l Ds = Some U ->
    trTrm G (Pth2Trm p) (TypOfCls Ds) c ->
    trTrm G (TrmVar x) (TypCls p) x' ->
    trTrm G (TrmSel (TrmVar x) l) (openTyp x U) (nuDOT.tsel x' l)
| trSel2: forall G l Ds U p t t' c,
    DeclsIndex l Ds = Some U ->
    closedTyp U ->
    trTrm G (Pth2Trm p) (TypOfCls Ds) c ->
    trTrm G t (TypCls p) t' ->
    trTrm G (TrmSel t l) U (nuDOT.tsel t' l)

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

with trTyp: Ctx -> Typ -> nuDOT.ty -> Prop :=
| trTypCls: forall,
    trTrm G (Pth2Trm p) 

: Pth -> Typ (* reference to a type *)
| trTypMtd: Typ -> Typ -> Typ (* (x: S)T        where x is locally nameless and can occur in T *)
| trTypOfCls: Decls -> Typ (* class { z => (l: T)...}    the type of a class, "ClassInfo" in dotty *)
with trDecls: Ctx -> Decls -> nuDOT.ty -> Prop :=
| trDeclsNil: Decls
| trDeclsSkip: Decls -> Decls (* label at this position undefined *)
| trDeclsCons: Typ -> Decls -> Decls.


trTrm
trDef
trTyp
*)


End miniscala.
