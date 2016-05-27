
Require Export SfLib.
Require Export Arith.EqNat.
Require Export Arith.Lt.

Require Import dot_storeless_tidy.

Definition Label := nat.

Inductive Var: Set :=
  | VarFr: nat (*absolute position in context, from origin, invariant under context extension*) -> Var
  | VarBd: nat (*bound variable, de Bruijn, locally nameless style -- see open *) -> Var.

Inductive Pth: Set :=
| PthVar: Var -> Pth
| PthSel: Var -> Label -> Pth (* prefix is not (yet) a path *).

Inductive Typ: Set :=
| TypCls: Pth -> Typ (* reference to a type *)
| TypMtd: Typ -> Typ -> Typ (* (x: S)T        where x is locally nameless and can occur in T *) (* unused *)
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

Definition trVar(v: Var): vr := match v with
| VarFr i => VarF i
| VarBd i => VarB i
end.

(* Note: The only types which can occur in user-written programs are paths referring to a class def *)
Definition trTyp(T: Pth): ty := match T with
| PthVar v => TSel (trVar v) 0 (* class was defined in an expr and thus put into a wrapper
                                  whose 0-th member is the type whose 1-st member is the constructor *)
| PthSel v l => TSel (trVar v) (l*2) (* class was defined inside another class,
                                        multiply by 2 to get free slots to insert the constructors *)
end.

Definition trCtorUse(c: Pth): tm := match c with
(* the new{} is just an ignored dummy argument because each method has to take exactly 1 argument *)
| PthVar v   => tapp (tvar (trVar v))    1      (tvar (VObj dnil)) (* v.create(new {})     *)
| PthSel v l => tapp (tvar (trVar v)) (S (l*2)) (tvar (VObj dnil)) (* v.create_l(new {})   *)
end.

Definition TAlias(l: lb)(T: ty) := TMem l T T.

Definition dnone := dty TTop. (* TODO it would cleaner to add a dnone to DOT's Inductive dm *)

(* TODO need to shift VarBd indices because we move them under the VObj binder! *)
Definition tlet(t1: tm)(T1: ty)(t2: tm)(T2: ty): tm :=
  tapp (tvar (VObj (dcons (dfun T1 T2 t2) dnil))) 0 t1.

(* OLD (with explicit y)
   "trTypOfDef d y (T1, T2)" means that the type of definition d (inside a class with self ref y),
   translates to types T1 and T2 (note that a class def generates two defs in DOT, one for the type
   and one for the constructor, so we need two types T1 and T2 here; if only one is needed, T2 = TTop).
   --> Turns out we can do it without any opening. *)

(* "trTypOfDef (l, d) (T1, T2)" means that the type of definition d (with label l) translates to types T1 and T2
   (note that a class def generates two defs in DOT, one for the type and one for the constructor,
   so we need two types T1 and T2 here; if only one is needed, T2 = TTop). *)
Inductive trTypOfDef: (Label * Def) -> (ty * ty) -> Prop :=
| trTypOfDefCls: forall l ds T,
    trTypOfDefs ds T ->
    trTypOfDef (l, (DefCls ds)) ((TAlias (2*l) (TBind T)), (TFun (S (2*l)) TTop (TSel (VarB 1) (2*l))))
    (*                          (type C_l = { z => /\...}) (def create_l(dummy: Top): outerSelf.C_l)   *)
| trTypOfDefDef: forall m T U u,
    trTypOfDef (m, (DefDef (TypCls T) (TypCls U) u)) ((TFun (2*m) (trTyp T) (trTyp U)), TTop)
| trTypOfDefNone: forall m,
    trTypOfDef (m, DefNone) (TTop, TTop)
(* Note: no rule for val defs yet *)
with trTypOfDefs: Defs -> ty -> Prop :=
| trTypOfDefsNil:
    trTypOfDefs DefsNil TTop
| trTypOfDefsCons: forall l d ds T1 T2 T3,
    l = DefsLength ds ->
    trTypOfDef (l, d) (T1, T2) ->
    trTypOfDefs ds T3 ->
    trTypOfDefs (DefsCons d ds) (TAnd T1 (TAnd T2 T3)).


(* (trTrm G t T t'), or on paper "G |- t : T ~> t'", means that in context G, the miniscala term t
   typechecks as miniscala type T and translates to DOT term t' *)
Inductive trTrm: Ctx -> Trm -> Typ -> tm -> Prop :=
| trTrmVar: forall G x T,
    x < length G ->
    trTrm G (TrmVar (VarFr x)) T (tvar (VarF x))
| trAppXX: forall G x1 x2 T2 T3 T3' l ds p t3,
    trTrm G (TrmVar (VarFr x1)) (TypCls p) (tvar (VarF x1)) ->
    clLookup G p ds ->
    DefsIndex l (openDefs (VarFr x1) ds) = Some (DefDef T2 T3 t3) ->
    open_Typ 1 (VarFr x2) T3 = T3' ->
    trTrm G (TrmVar (VarFr x2)) T2 (tvar (VarF x2)) ->
    trTrm G (TrmApp (TrmVar (VarFr x1)) l (TrmVar (VarFr x2))) T3'
          (tapp (tvar (VarF x1)) (2*l) (tvar (VarF x2)))
| trAppXT: forall G x1 t2 t2' T2 T3 l ds p t3,
    trTrm G (TrmVar (VarFr x1)) (TypCls p) (tvar (VarF x1)) ->
    clLookup G p ds ->
    DefsIndex l (openDefs (VarFr x1) ds) = Some (DefDef T2 T3 t3) ->
    closedTyp T3 ->
    trTrm G t2 T2 t2' ->
    trTrm G (TrmApp (TrmVar (VarFr x1)) l t2) T3
          (tapp (tvar (VarF x1)) (2*l) t2')
| trAppTX: forall G t1 t1' x2 T2 T3 T3' l ds p t3,
    trTrm G t1 (TypCls p) t1' ->
    clLookup G p ds ->
    DefsIndex l ds = Some (DefDef T2 T3 t3) ->
    open_Typ 1 (VarFr x2) T3 = T3' ->
    closedTyp T2 ->
    closedTyp T3' ->
    trTrm G (TrmVar (VarFr x2)) T2 (tvar (VarF x2)) ->
    trTrm G (TrmApp t1 l (TrmVar (VarFr x2))) T3'
          (tapp t1' (2*l) (tvar (VarF x2)))
| trAppTT: forall G t1 t1' t2 t2' T2 T3 l ds p t3,
    trTrm G t1 (TypCls p) t1' ->
    clLookup G p ds ->
    DefsIndex l ds = Some (DefDef T2 T3 t3) ->
    closedTyp T2 ->
    closedTyp T3 ->
    trTrm G t2 T2 t2' ->
    trTrm G (TrmApp t1 l t2) T3
          (tapp t1' (2*l) t2')
(*
| trSeqVal: forall,
    

| trSeqCls: forall,
    trDef
    trTrm G (TrmBlock (DefCls ds) t2) T2 (tlet (tvar (VObj (dcons (dty 
*)

(* (trDef G (l, d) (d', d'')), on paper "G |- d ~y~> d'; d''" means that the definition d (with label l)
   translates to DOT definitions d' and d'' (note that two are needed defs are needed for type & constructor).
   It also performs typechecking, but there's no need to assign a type, because all the type information is
   contained in the def. *)
with trDef: Ctx -> (Label * Def) -> (dm * dm) -> Prop :=
| trDefDef: forall G m T1 T2 t2 t2',
    trTrm ((TypCls T1) :: G) t2 (TypCls T2) t2' ->
    trDef G (m, (DefDef (TypCls T1) (TypCls T2) t2)) (dfun (trTyp T1) (trTyp T2) t2', dnone)
| trDefCls: forall y G l ds ds' T,
    S y = length G ->
    trTypOfDefs ds T ->
    trDefs ((TypCls (PthSel (VarFr y) l)) :: G) (openDefs (VarFr (S y)) ds) (dms_open 0 (VarF (S y)) ds') ->
    trDef G (l, (DefCls ds))
      (dty (TBind T)          , dfun TTop (TSel (VarF y) (2*l)) (tvar (VObj ds'))) 
   (* type C_l = { z => /\...}, def create_l(x: Top): outerSelf.C_l = new { z => ds'} *)
| trDefNone: forall G m,
    trDef G (m, DefNone) (dnone, dnone)

with trDefs: Ctx -> Defs -> dms -> Prop :=
| trDefsNil: forall G,
    trDefs G DefsNil dnil
| trDefsCons: forall G d ds d1' d2' ds' l,
    l = DefsLength ds ->
    trDef G (l, d) (d1', d2') -> 
    trDefs G ds ds' ->
    trDefs G (DefsCons d ds) (dcons d1' (dcons d2' ds'))

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



