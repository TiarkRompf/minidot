(*
DOT
T ::= Bot | Top | T1 /\ T2 | T1 \/ T2 |
      { def m(x: S): U^x } | { type A: S..U } | x.A | { z => T^z }
t ::= x | { y => d^y... } | t.m(t)
d ::= { def m(x: S): U^x = t^x } | { type A = T }
*)

(* in small-step *)
Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Lt.

(*# Syntax #*)

Definition id := nat. (* identifiers for variables: x,y,z *)
Definition lb := nat. (* labels for records: L, m *)

Inductive vr : Type :=
  | TVar   : bool(*true for concrete context, false for abstract context *) ->
             id(*absolute position in context, from origin, invariant under context extension*) -> vr
  | TVarB  : id(*bound variable, de Bruijn, locally nameless style -- see open *) -> vr
.

Inductive ty : Type :=
  | TBot   : ty (* bottom type *)
  | TTop   : ty (* top type *)
  | TFun   : lb -> ty -> ty -> ty (* dependent function / method member type:
                                     { def m(x: S): U^x },
                                     where x is locally bound in U *)
  | TTyp   : lb -> ty -> ty -> ty (* type member type: { type L: S..U } *)
  | TSel   : vr -> lb -> ty (* type selection: x.L *)
  | TBind  : ty -> ty (* Recursive binder: { z => T^z },
                         where z is locally bound in T *)
  | TAnd   : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *)
  | TOr    : ty -> ty -> ty (* Union Type: T1 \/ T2 *)
.

Inductive tm : Type :=
  | tvar  : bool(*like TVar: true for concrete, false for hypothetical *) -> id -> tm (* variable: x *)
  (* N.B.: no varB -- terms just use absolute identifers directly *)
  | tobj  : dms(*self is next slot in abstract context -- see subst_tm*) -> tm (* new object instance: { z => d... } *)
  | tapp  : tm -> lb -> tm -> tm (* method invocation: t.m(t) *)

with dm : Type := (* initialization / member definition --
                     the labels, e.g. m & A, are determined from the position in member list, dms *)
  | dfun : option ty -> option ty -> tm -> dm (* method: { def m(x[: S])[: U] = t }, where the types [: S] and [: U] are optional *)
  (* Church vs Curry: we show that all options work, by making parameter and return types optional,
     when defining a method. *)
  | dty  : ty -> dm (* type: { type L = T } *)

(* we use our own list-like structure for easy recursion, e.g. in subst_tm *)
with dms : Type := (* list of member defs *)
  | dnil : dms
  | dcons : dm -> dms -> dms
.

Fixpoint dms_to_list (ds: dms) : list dm :=
  match ds with
    | dnil => []
    | dcons d ds => d :: dms_to_list ds
  end.

Inductive vl : Type :=
  | vobj  : dms -> vl
.

Definition venv := list vl. (*rho G*)
Definition tenv := list ty. (*Gamma GH*)

Hint Unfold venv.
Hint Unfold tenv.

(*# Variable Binding #*)

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

(*
   closed i j k -- well-bound in
   an abstract environment GH of size >= i
   a concrete environment G of size >= j
   under >= k binders/de Bruijn levels
*)
Inductive vr_closed: nat(*abstract, TVar false i*) -> nat(*concrete, TVar true j*) -> nat(*bound, TVarB k*) -> vr -> Prop :=
| cl_var0: forall i j k x,
    i > x ->
    vr_closed i j k (TVar false x)
| cl_var1: forall i j k x,
    j > x ->
    vr_closed i j k (TVar true x)
| cl_varB: forall i j k x,
    k > x ->
    vr_closed i j k (TVarB x).

Inductive closed: nat(*abstract, TVar false i*) -> nat(*concrete, TVar true j*) -> nat(*bound, TVarB k*) -> ty -> Prop :=
| cl_bot: forall i j k,
    closed i j k TBot
| cl_top: forall i j k,
    closed i j k TTop
| cl_fun: forall i j k l T1 T2,
    closed i j k T1 ->
    closed i j (S k) T2 ->
    closed i j k (TFun l T1 T2)
| cl_typ: forall i j k l T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TTyp l T1 T2)
| cl_sel: forall i j k p1 l,
    vr_closed i j k p1 ->
    closed i j k (TSel p1 l)
| cl_bind: forall i j k T1,
    closed i j (S k) T1 ->
    closed i j k (TBind T1)
| cl_and: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TAnd T1 T2)
| cl_or: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TOr T1 T2)
.

(* substitute a locally bound variable at de Brujin level k with variable u in type T *)
Definition vr_open (k: nat) (u: vr) (p: vr) : vr :=
  match p with
    | TVar b x => TVar b x (* free var remains free. functional, so we can't check for conflict *)
    | TVarB x => if beq_nat k x then u else TVarB x
  end.
Fixpoint open (k: nat) (u: vr) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TSel p1 l     => TSel (vr_open k u p1) l
    | TFun l T1 T2  => TFun l (open k u T1) (open (S k) u T2)
    | TTyp l T1 T2  => TTyp l (open k u T1) (open k u T2)
    | TBind T1    => TBind (open (S k) u T1)
    | TAnd T1 T2  => TAnd (open k u T1) (open k u T2)
    | TOr T1 T2   => TOr (open k u T1) (open k u T2)
  end.

(* substitute the first abstract variable (id 0) with variable u in type T --
   all other abstract variables are shifted (id decremented) to fit the shrinked abstract context
*)
Definition vr_subst (u : vr) (X : vr): vr :=
  match X with
    | TVarB i      => TVarB i
    | TVar true i  => TVar true i
    (* subst the _first_ aka _oldest_ abstract variables,
       the other abstract variables are shifted to resolve in the shrinked context *)
    | TVar false i => if beq_nat i 0 then u else TVar false (i-1)
  end.
Fixpoint subst (u : vr) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TTyp l T1 T2 => TTyp l (subst u T1) (subst u T2)
    | TSel p1 l    => TSel (vr_subst u p1) l
    | TFun l T1 T2 => TFun l (subst u T1) (subst u T2)
    | TBind T2     => TBind (subst u T2)
    | TAnd T1 T2   => TAnd (subst u T1) (subst u T2)
    | TOr T1 T2    => TOr (subst u T1) (subst u T2)
  end.

(* substitute the first hypothetical variable with term u in term t --
   like subst, shifts other hypothetical variables *)
Fixpoint subst_tm (u:nat) (t : tm) {struct t} : tm :=
  match t with
    | tvar true i         => tvar true i
    | tvar false i        => if beq_nat i 0 then (tvar true u) else tvar false (i-1)
    | tobj ds             => tobj (subst_dms u ds)
    | tapp t1 l t2          => tapp (subst_tm u t1) l (subst_tm u t2)
  end
with subst_dm (u:nat) (d: dm) {struct d} : dm :=
  match d with
    | dty T        => dty (subst (TVar true u) T)
    | dfun T1 T2 t => dfun (option_map (subst (TVar true u)) T1) (option_map (subst (TVar true u)) T2) (subst_tm u t)
  end
with subst_dms (u:nat) (ds: dms) {struct ds} : dms :=
  match ds with
    | dnil        => dnil
    | dcons d ds1  => dcons (subst_dm u d) (subst_dms u ds1)
  end.

(* Shortcut for the common case of replacing abstract with concrete. *)
Definition substt x T := (subst (TVar true x) T).
Hint Immediate substt.

(*# Operational Semantics #*)

(* Reduction semantics  *)
Inductive step : venv -> tm -> venv -> tm -> Prop :=
(* Computation Rules *)
| ST_Obj : forall G1 D,
    step G1 (tobj D) (vobj (subst_dms (length G1) D)::G1) (tvar true (length G1))
| ST_AppAbs : forall G1 f l x ds T1 T2 t12,
    index f G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dfun T1 T2 t12) ->
    step G1 (tapp (tvar true f) l (tvar true x)) G1 (subst_tm x t12)
(* Congruence Rules *)
| ST_App1 : forall G1 G1' t1 t1' l t2,
    step G1 t1 G1' t1' ->
    step G1 (tapp t1 l t2) G1' (tapp t1' l t2)
| ST_App2 : forall G1 G1' f t2 l t2',
    step G1 t2 G1' t2' ->
    step G1 (tapp (tvar true f) l t2) G1' (tapp (tvar true f) l t2')
.

(*# Static Semantics #*)

Definition eq_some {X} (OT:option X) (T:X) := OT=None \/ OT=Some T.

(* : -- typing *)
Inductive has_type : tenv -> venv -> tm -> ty -> nat -> Prop :=
  | T_Vary : forall GH G1 x ds ds' T T' n1,
      index x G1 = Some (vobj ds) ->
      dms_has_type [T'] G1 ds' T' n1 ->
      subst_dms x ds' = ds ->
      substt x T' = T ->
      closed 0 (length G1) 0 T ->
      has_type GH G1 (tvar true x) T (S n1)
  | T_Varz : forall G1 GH x T n1,
      index x GH = Some T ->
      closed (length GH) (length G1) 0 T ->
      has_type GH G1 (tvar false x) T (S n1)
  | T_VarPack : forall GH G1 b x T1 T1' n1,
      has_type GH G1 (tvar b x) T1' n1 ->
      T1' = (open 0 (TVar b x) T1) ->
      closed (length GH) (length G1) 1 T1 ->
      has_type GH G1 (tvar b x) (TBind T1) (S n1)
  | T_VarUnpack : forall GH G1 b x T1 T1' n1,
      has_type GH G1 (tvar b x) (TBind T1) n1 ->
      T1' = (open 0 (TVar b x) T1) ->
      closed (length GH) (length G1) 0 T1' ->
      has_type GH G1 (tvar b x) T1' (S n1)
  | T_Obj : forall GH G1 ds T T' n1,
      dms_has_type (T'::GH) G1 ds T' n1 ->
      T' = open 0 (TVar false (length GH)) T ->
      closed (length GH) (length G1) 1 T ->
      has_type GH G1 (tobj ds) (TBind T) (S n1)
  | T_App : forall l T1 T2 GH G1 t1 t2 n1 n2,
      has_type GH G1 t1 (TFun l T1 T2) n1 ->
      has_type GH G1 t2 T1 n2 ->
      closed (length GH) (length G1) 0 T2 ->
      has_type GH G1 (tapp t1 l t2) T2 (S (n1+n2))
  | T_AppVar : forall l T1 T2 T2' GH G1 t1 b2 x2 n1 n2,
      has_type GH G1 t1 (TFun l T1 T2) n1 ->
      has_type GH G1 (tvar b2 x2) T1 n2 ->
      T2' = (open 0 (TVar b2 x2) T2) ->
      closed (length GH) (length G1) 0 T2' ->
      has_type GH G1 (tapp t1 l (tvar b2 x2)) T2' (S (n1+n2))
  | T_Sub : forall GH G1 t T1 T2 n1 n2,
      has_type GH G1 t T1 n1 ->
      stp GH G1 T1 T2 n2 ->
      has_type GH G1 t T2 (S (n1 + n2))

(* : -- member initialization *)
with dms_has_type: tenv -> venv -> dms -> ty -> nat -> Prop :=
  | D_Nil : forall GH G1 n1,
      dms_has_type GH G1 dnil TTop (S n1)
  | D_Typ : forall GH G1 l T11 ds TS T n1,
      dms_has_type GH G1 ds TS n1 ->
      closed (length GH) (length G1) 0 T11 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TTyp l T11 T11) TS ->
      dms_has_type GH G1 (dcons (dty T11) ds) T (S n1)
  | D_Fun : forall GH G1 l OT11 T11 OT12 T12 T12' t12 ds TS T n1 n2,
      dms_has_type GH G1 ds TS n1 ->
      has_type (T11::GH) G1 t12 T12' n2 ->
      T12' = (open 0 (TVar false (length GH)) T12) ->
      closed (length GH) (length G1) 0 T11 ->
      closed (length GH) (length G1) 1 T12 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TFun l T11 T12) TS ->
      eq_some OT11 T11 ->
      eq_some OT12 T12 ->
      dms_has_type GH G1 (dcons (dfun OT11 OT12 t12) ds) T (S (n1+n2))

(* <: -- subtyping *)
with stp: tenv -> venv -> ty -> ty -> nat -> Prop :=
| stp_bot: forall GH G1 T n1,
    closed (length GH) (length G1) 0  T ->
    stp GH G1 TBot T (S n1)
| stp_top: forall GH G1 T n1,
    closed (length GH) (length G1) 0 T ->
    stp GH G1 T  TTop (S n1)
| stp_fun: forall GH G1 l T1 T2 T3 T4 T2' T4' n1 n2,
    T2' = (open 0 (TVar false (length GH)) T2) ->
    T4' = (open 0 (TVar false (length GH)) T4) ->
    closed (length GH) (length G1) 1 T2 ->
    closed (length GH) (length G1) 1 T4 ->
    stp GH G1 T3 T1 n1 ->
    stp (T3::GH) G1 T2' T4' n2 ->
    stp GH G1 (TFun l T1 T2) (TFun l T3 T4) (S (n1+n2))
| stp_typ: forall GH G1 l T1 T2 T3 T4 n1 n2,
    stp GH G1 T3 T1 n2 ->
    stp GH G1 T2 T4 n1 ->
    stp GH G1 (TTyp l T1 T2) (TTyp l T3 T4) (S (n1+n2))

| stp_strong_sel1: forall GH G1 l T2 ds TX x n1,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] G1 TX T2 n1 ->
    stp GH G1 (TSel (TVar true x) l) T2 (S n1)
| stp_strong_sel2: forall GH G1 l T1 ds TX x n1,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] G1 T1 TX n1 ->
    stp GH G1 T1 (TSel (TVar true x) l) (S n1)

| stp_sel1: forall GH G1 l T2 x n1,
    htp  GH G1 x (TTyp l TBot T2) n1 ->
    stp GH G1 (TSel (TVar false x) l) T2 (S n1)

| stp_sel2: forall GH G1 l T1 x n1,
    htp  GH G1 x (TTyp l T1 TTop) n1 ->
    stp GH G1 T1 (TSel (TVar false x) l) (S n1)

| stp_selx: forall GH G1 l p1 n1,
    vr_closed (length GH) (length G1) 0 p1 ->
    stp GH G1 (TSel p1 l) (TSel p1 l) (S n1)

| stp_bind1: forall GH G1 T1 T1' T2 n1,
    stp (T1'::GH) G1 T1' T2 n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp GH G1 (TBind T1) T2 (S n1)

| stp_bindx: forall GH G1 T1 T1' T2 T2' n1,
    stp (T1'::GH) G1 T1' T2' n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    T2' = (open 0 (TVar false (length GH)) T2) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 1 T2 ->
    stp GH G1 (TBind T1) (TBind T2) (S n1)

| stp_and11: forall GH G1 T1 T2 T n1,
    stp GH G1 T1 T n1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp GH G1 (TAnd T1 T2) T (S n1)
| stp_and12: forall GH G1 T1 T2 T n1,
    stp GH G1 T2 T n1 ->
    closed (length GH) (length G1) 0 T1 ->
    stp GH G1 (TAnd T1 T2) T (S n1)
| stp_and2: forall GH G1 T1 T2 T n1 n2,
    stp GH G1 T T1 n1 ->
    stp GH G1 T T2 n2 ->
    stp GH G1 T (TAnd T1 T2) (S (n1+n2))

| stp_or21: forall GH G1 T1 T2 T n1,
    stp GH G1 T T1 n1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp GH G1 T (TOr T1 T2) (S n1)
| stp_or22: forall GH G1 T1 T2 T n1,
    stp GH G1 T T2 n1 ->
    closed (length GH) (length G1) 0 T1 ->
    stp GH G1 T (TOr T1 T2) (S n1)
| stp_or1: forall GH G1 T1 T2 T n1 n2,
    stp GH G1 T1 T n1 ->
    stp GH G1 T2 T n2 ->
    stp GH G1 (TOr T1 T2) T (S (n1+n2))

| stp_trans: forall GH G1 T1 T2 T3 n1 n2,
    stp GH G1 T1 T2 n1 ->
    stp GH G1 T2 T3 n2 ->
    stp GH G1 T1 T3 (S (n1+n2))

(* :! -- typing for type selection in subtyping *)
with htp: tenv -> venv -> id -> ty -> nat -> Prop :=
| htp_var: forall GH G1 x TX n1,
    index x GH = Some TX ->
    closed (S x) (length G1) 0 TX ->
    htp GH G1 x TX (S n1)
| htp_unpack: forall GH G1 x TX n1,
    htp GH G1 x (TBind TX) n1 ->
    closed (S x) (length G1) 1 TX ->
    htp GH G1 x (open 0 (TVar false x) TX) (S n1)
| htp_sub: forall GH GU GL G1 x T1 T2 n1 n2,
    (* use restricted GH. note: this is slightly different
    from the big-step version b/c here we do not distinguish
    if variables are bound in terms vs types. it would be easy
    to do exactly the same thing by adding this distinction. *)
    htp GH G1 x T1 n1 ->
    stp GL G1 T1 T2 n2 ->
    length GL = S x ->
    GH = GU ++ GL ->
    htp GH G1 x T2 (S (n1+n2)).

Definition has_typed GH G1 x T1 := exists n, has_type GH G1 x T1 n.

Definition stpd GH G1 T1 T2 := exists n, stp GH G1 T1 T2 n.

Definition htpd GH G1 x T1 := exists n, htp GH G1 x T1 n.

Hint Constructors stp.

Ltac ep := match goal with
             | [ |- stp ?GH ?G1 ?T1 ?T2 ?N ] => assert (exists (n:nat), stp GH G1 T1 T2 n) as EEX
           end.

Ltac eu := match goal with
             | H: has_typed _ _ _ _ |- _ => destruct H as [? H]
             | H: stpd _ _ _ _ |- _ => destruct H as [? H]
             | H: htpd _ _ _ _ |- _ => destruct H as [? H]
           end.

Lemma stpd_bot: forall GH G1 T,
    closed (length GH) (length G1) 0 T ->
    stpd GH G1 TBot T.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd_top: forall GH G1 T,
    closed (length GH) (length G1) 0 T ->
    stpd GH G1 T TTop.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd_fun: forall GH G1 l T1 T2 T3 T4 T2' T4',
    T2' = (open 0 (TVar false (length GH)) T2) ->
    T4' = (open 0 (TVar false (length GH)) T4) ->
    closed (length GH) (length G1) 1 T2 ->
    closed (length GH) (length G1) 1 T4 ->
    stpd GH G1 T3 T1 ->
    stpd (T3::GH) G1 T2' T4' ->
    stpd GH G1 (TFun l T1 T2) (TFun l T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.
Lemma stpd_typ: forall GH G1 l T1 T2 T3 T4,
    stpd GH G1 T3 T1 ->
    stpd GH G1 T2 T4 ->
    stpd GH G1 (TTyp l T1 T2) (TTyp l T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.



Lemma stpd_trans: forall GH G1 T1 T2 T3,
    stpd GH G1 T1 T2 ->
    stpd GH G1 T2 T3 ->
    stpd GH G1 T1 T3.
Proof. intros. repeat eu. eexists. eauto. Qed.




Hint Constructors ty.
Hint Constructors vl.


Hint Constructors stp.
Hint Constructors htp.
Hint Constructors has_type.

Hint Unfold has_typed.
Hint Unfold stpd.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.


Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.


(*# Regularity #*)

Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  Case "nil". intros. inversion H.
  Case "cons".
  intros. inversion H.
  case_eq (beq_nat n (length vs)); intros E.
  SCase "hit".
  rewrite E in H1. inversion H1. subst.
  eapply beq_nat_true in E.
  unfold length. unfold length in E. rewrite E. eauto.
  SCase "miss".
  rewrite E in H1.
  assert (n < length vs). eapply IHvs. apply H1.
  compute. eauto.
Qed.

Lemma index_exists : forall X vs n,
                       n < length vs ->
                       exists (T:X), index n vs = Some T.
Proof.
  intros X vs. induction vs.
  Case "nil". intros. inversion H.
  Case "cons".
  intros. inversion H.
  SCase "hit".
  assert (beq_nat n (length vs) = true) as E. eapply beq_nat_true_iff. eauto.
  simpl. subst n. rewrite E. eauto.
  SCase "miss".
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff. omega.
  simpl. rewrite E. eapply IHvs. eauto.
Qed.


Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply index_max. eauto.
  assert (n <> length vs). omega.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff; eauto.
  unfold index. unfold index in H. rewrite H. rewrite E. reflexivity.
Qed.

Lemma plus_lt_contra: forall a b,
  a + b < b -> False.
Proof.
  intros a b H. induction a.
  - simpl in H. apply lt_irrefl in H. assumption.
  - simpl in H. apply IHa. omega.
Qed.

Lemma index_extend_mult: forall {X} G0 G2 x0 (T:X),
    index x0 G0 = Some T ->
    index x0 (G2++G0) = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl. assumption.
  - simpl.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E.
      apply index_max in H. subst.
      rewrite app_length in H. apply plus_lt_contra in H. inversion H.
    + apply IHG2. assumption.
Qed.

Lemma vr_closed_extend : forall p X (a:X) i k G,
                       vr_closed i (length G) k p ->
                       vr_closed i (length (a::G)) k p.
Proof.
  intros. inversion H; subst; econstructor; eauto. simpl. omega.
Qed.

Lemma closed_extend : forall T X (a:X) i k G,
                       closed i (length G) k T ->
                       closed i (length (a::G)) k T.
Proof.
  intros T. induction T; intros; inversion H;  econstructor; eauto using vr_closed_extend.
Qed.

Lemma all_extend: forall ni,
  (forall GH  v1 G1 T1 T2 n,
     stp GH G1 T1 T2 n -> n < ni ->
     stp GH (v1::G1) T1 T2 n) /\
  (forall v1 x GH G1 T2 n,
     htp GH G1 x T2 n -> n < ni ->
     htp GH (v1::G1) x T2 n) /\
  (forall GH G1 t T v n,
     has_type GH G1 t T n -> n < ni ->
     has_type GH (v::G1) t T n) /\
  (forall GH G1 ds T v n,
     dms_has_type GH G1 ds T n -> n < ni ->
     dms_has_type GH (v::G1) ds T n).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H.
  (* stp *)
  - econstructor. eapply closed_extend. eauto.
  - econstructor. eapply closed_extend. eauto.
  - econstructor. eauto. eauto.
    eapply closed_extend. eauto. eapply closed_extend. eauto.
    eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eapply index_extend. eauto. eauto. eapply IHn. eauto. omega.
  - econstructor. eapply index_extend. eauto. eauto. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply vr_closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto. eapply closed_extend. eauto.
  - eapply stp_bindx. eapply IHn. eauto. omega. eauto. eauto. eapply closed_extend. eauto. eapply closed_extend. eauto.
  - eapply stp_and11. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply stp_and12. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply stp_and2. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - eapply stp_or21. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply stp_or22. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply stp_or1. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - eapply stp_trans. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  (* htp *)
  - econstructor. eauto. eapply closed_extend. eauto.
  - eapply htp_unpack. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply htp_sub. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eauto. eauto.
  (* has_type *)
  - econstructor. eapply index_extend. eauto. eapply IHn. eauto. omega. eauto. eauto. eapply closed_extend. eauto.
  - econstructor. eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto.
  - econstructor. subst. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply T_AppVar. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  (* dms_has_type *)
  - econstructor.
  - econstructor. eapply IHn. eauto. omega. eapply closed_extend. eauto. eauto. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eauto.
    eapply closed_extend. eauto. eapply closed_extend. eauto. eauto. eauto. eauto. eauto.
Qed.

Lemma vr_closed_upgrade_gh: forall i i1 j k p1,
  vr_closed i j k p1 -> i <= i1 -> vr_closed i1 j k p1.
Proof.
  intros. inversion H; subst; econstructor; eauto. omega.
Qed.
Lemma closed_upgrade_gh: forall i i1 j k T1,
  closed i j k T1 -> i <= i1 -> closed i1 j k T1.
Proof.
  intros. generalize dependent i1. induction H; intros; econstructor; eauto using vr_closed_upgrade_gh.
Qed.

Lemma vr_closed_extend_mult : forall p i j j' k,
                             vr_closed i j k p -> j <= j' ->
                             vr_closed i j' k p.
Proof.
  intros. inversion H; subst; econstructor; eauto. omega.
Qed.
Lemma closed_extend_mult : forall T i j j' k,
                             closed i j k T -> j <= j' ->
                             closed i j' k T.
Proof.
  intros. generalize dependent j'. induction H; intros; econstructor; eauto using vr_closed_extend_mult.
Qed.

Lemma vr_closed_upgrade: forall i j k k1 p1,
  vr_closed i j k p1 -> k <= k1 -> vr_closed i j k1 p1.
Proof.
  intros. inversion H; subst; econstructor; eauto. omega.
Qed.
Lemma closed_upgrade: forall i j k k1 T1,
  closed i j k T1 -> k <= k1 -> closed i j k1 T1.
Proof.
  intros. generalize dependent k1. induction H; intros; econstructor; eauto using vr_closed_upgrade.
  eapply IHclosed2. omega.
  eapply IHclosed. omega.
Qed.

Lemma vr_closed_open: forall j k n b V p, vr_closed k n (j+1) p -> vr_closed k n j (TVar b V) -> vr_closed k n j (vr_open j (TVar b V) p).
Proof.
  intros. inversion H; try econstructor; eauto; subst.
  - Case "TVarB". simpl.
    case_eq (beq_nat j x); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
Qed.

Lemma closed_open: forall j k n b V T, closed k n (j+1) T -> vr_closed k n j (TVar b V) -> closed k n j (open j (TVar b V) T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H;
   try econstructor; try eapply IHT1; try eapply IHT2; eauto; try eapply IHT; eauto using vr_closed_open; subst;
   eapply vr_closed_upgrade; eauto.
Qed.

Lemma all_closed: forall ni,
  (forall GH G1 T1 T2 n,
     stp GH G1 T1 T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T1) /\
  (forall GH G1 T1 T2 n,
     stp GH G1 T1 T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T2) /\
  (forall x GH G1 T2 n,
     htp GH G1 x T2 n -> n < ni ->
     x < length GH) /\
  (forall x GH G1 T2 n,
     htp GH G1 x T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T2) /\
  (forall GH G1 t T n,
     has_type GH G1 t T n -> n < ni ->
     closed (length GH) (length G1) 0 T) /\
  (forall GH G1 ds T n,
     dms_has_type GH G1 ds T n -> n < ni ->
     closed (length GH) (length G1) 0 T).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H; destruct IHn as [IHS1 [IHS2 [IHH1 [IHH2 [IHT IHD]]]]].
  (* stp left *)
  - econstructor.
  - eauto.
  - econstructor. eapply IHS2. eauto. omega. eauto.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS1. eauto. omega.
  - econstructor. econstructor. eapply index_max. eauto.
  - eapply closed_upgrade_gh. eapply IHS1. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. eauto.
  - econstructor. eauto.
  - econstructor. eauto.
  - econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. eauto. eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  - econstructor. eapply IHS1. eauto. omega. eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  (* stp right *)
  - eauto.
  - econstructor.
  - econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHS2. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply index_max. eauto.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - econstructor. eauto.
  - eauto.
  - econstructor. eauto.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS2. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eauto.
  - econstructor. eauto. eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  (* htp left *)
  - eapply index_max. eauto.
  - eapply IHH1. eauto. omega.
  - eapply IHH1. eauto. omega.
  (* htp right *)
  - eapply closed_upgrade_gh. eauto. subst. eapply index_max in H1. omega.
  - eapply IHH1 in H1. eapply closed_open. simpl. eapply closed_upgrade_gh. eauto. omega. econstructor. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHS2. eauto. omega. rewrite H4. rewrite app_length. omega.
  (* has_type *)
  - subst. eapply closed_upgrade_gh. eauto. omega.
  - eauto.
  - econstructor. eapply closed_upgrade_gh. eauto. omega.
  - eapply IHT in H1. inversion H1; subst. eauto. omega.
  - econstructor. eauto.
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHS2. eauto. omega.
  (* dms_has_type *)
  - econstructor.
  - subst. econstructor. econstructor. eauto. eauto. eapply IHD. eauto. omega.
  - subst. econstructor. econstructor. eauto. eauto. eapply IHD. eauto. omega.
Qed.

Lemma htp_extend : forall v1 x GH G1 T2 n,
                      htp GH G1 x T2 n ->
                      htp GH (v1::G1) x T2 n.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma stp_extend : forall GH  v1 G1 T1 T2 n,
                      stp GH G1 T1 T2 n ->
                      stp GH (v1::G1) T1 T2 n.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma stp_extend_mult : forall GH G1 G' T1 T2 n,
                      stp GH G1 T1 T2 n ->
                      stp GH (G'++G1) T1 T2 n.
Proof. intros. induction G'. simpl. eauto. simpl. eapply stp_extend. eauto. Qed.

Lemma has_type_extend: forall GH G1 t T v n1,
  has_type GH G1 t T n1 ->
  has_type GH (v::G1) t T n1.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma dms_has_type_extend: forall GH G1 t T v n1,
  dms_has_type GH G1 t T n1 ->
  dms_has_type GH (v::G1) t T n1.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma has_type_extend_mult: forall GH G1 t T G' n1,
  has_type GH G1 t T n1 ->
  has_type GH (G'++G1) t T n1.
Proof. intros. induction G'. simpl. eauto. simpl. eapply has_type_extend. eauto. Qed.

Lemma htp_closed: forall x GH G1 T2 n,
  htp GH G1 x T2 n ->
  closed (length GH) (length G1) 0 T2.
Proof. intros. eapply all_closed with (x:=x). eauto. eauto. Qed.

Lemma htp_closed1: forall x GH G1 T2 n,
  htp GH G1 x T2 n ->
  x < length GH.
Proof. intros. eapply all_closed with (x:=x). eauto. eauto. Qed.

Lemma has_type_closed: forall GH G1 t T n1,
  has_type GH G1 t T n1 ->
  closed (length GH) (length G1) 0 T.
Proof. intros. eapply all_closed with (t:=t). eauto. eauto. Qed.

Lemma dms_has_type_closed: forall GH G1 t T n1,
  dms_has_type GH G1 t T n1 ->
  closed (length GH) (length G1) 0 T.
Proof. intros. eapply all_closed with (ds:=t). eauto. eauto. Qed.

Lemma has_type_closed_z: forall GH G1 z T n1,
  has_type GH G1 (tvar false z) T n1 ->
  z < length GH.
Proof.
  intros. remember (tvar false z) as t. generalize dependent z.
  induction H; intros; inversion Heqt; subst; eauto using index_max.
Qed.


Lemma has_type_closed1: forall GH G1 x T n1,
  has_type GH G1 (tvar true x) T n1 ->
  x < length G1.
Proof.
  intros. remember (tvar true x) as t. generalize dependent x.
  induction H; intros; inversion Heqt; subst; eauto using index_max.
Qed.

Lemma has_type_closed_b: forall G1 b x T n1,
  has_type [] G1 (tvar b x) T n1 ->
  b = true /\ x < length G1.
 Proof.
 intros.
 remember [] as GH.
 remember (tvar b x) as t.
 generalize dependent x. generalize dependent b. generalize HeqGH. clear HeqGH.
 induction H; intros; inversion Heqt; subst; eauto using index_max.
 - simpl in H. inversion H.
Qed.

Lemma stp_closed1 : forall GH G1 T1 T2 n1,
                      stp GH G1 T1 T2 n1 ->
                      closed (length GH) (length G1) 0 T1.
Proof. intros. edestruct all_closed. eapply H0. eauto. eauto. Qed.

Lemma stp_closed2 : forall GH G1 T1 T2 n1,
                      stp GH G1 T1 T2 n1 ->
                      closed (length GH) (length G1) 0 T2.
Proof. intros. edestruct all_closed. destruct H1. eapply H1. eauto. eauto. Qed.

Lemma stpd_closed1 : forall GH G1 T1 T2,
                      stpd GH G1 T1 T2 ->
                      closed (length GH) (length G1) 0 T1.
Proof. intros. eu. eapply stp_closed1. eauto. Qed.


Lemma stpd_closed2 : forall GH G1 T1 T2,
                      stpd GH G1 T1 T2 ->
                      closed (length GH) (length G1) 0 T2.
Proof. intros. eu. eapply stp_closed2. eauto. Qed.


Lemma beq_nat_true_eq: forall A, beq_nat A A = true.
Proof. intros. eapply beq_nat_true_iff. eauto. Qed.


Fixpoint tsize (T: ty) { struct T }: nat :=
  match T with
    | TTop        => 1
    | TBot        => 1
    | TSel T1 l   => 1
    | TFun l T1 T2 => S (tsize T1 + tsize T2)
    | TTyp l T1 T2 => S (tsize T1 + tsize T2)
    | TBind T1    => S (tsize T1)
    | TAnd T1 T2  => S (tsize T1 + tsize T2)
    | TOr T1 T2   => S (tsize T1 + tsize T2)
  end.

Lemma open_preserves_size: forall T b x j,
  tsize T = tsize (open j (TVar b x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
Qed.

Lemma stpd_refl_aux: forall n GH G1 T1,
  closed (length GH) (length G1) 0 T1 ->
  tsize T1 < n ->
  stpd GH G1 T1 T1.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst; simpl in H0.
  - Case "bot". exists 1. eauto.
  - Case "top". exists 1. eauto.
  - Case "fun". eapply stpd_fun; eauto.
    eapply IHn; eauto; omega.
    eapply IHn; eauto.
    simpl. apply closed_open. simpl. eapply closed_upgrade_gh. eauto. omega.
    econstructor. omega.
    rewrite <- open_preserves_size. omega.
  - Case "typ". eapply stpd_typ; try eapply IHn; eauto; try omega.
  - Case "sel". exists 1. eapply stp_selx. eauto.
  - Case "bind".
    remember (open 0 (TVar false (length GH)) T0) as T0'.
    destruct (IHn (T0'::GH) G1 T0').
    subst. eapply closed_open. eapply closed_upgrade_gh. eauto.
    simpl. omega. simpl. econstructor. omega.
    subst. rewrite <- open_preserves_size. omega.
    eexists. eapply stp_bindx; eauto.
  - Case "and".
    destruct (IHn GH G1 T0 H1). omega.
    destruct (IHn GH G1 T2 H2). omega.
    eexists. eapply stp_and2. eapply stp_and11. eauto. eauto. eapply stp_and12. eauto. eauto.
  - Case "or".
    destruct (IHn GH G1 T0 H1). omega.
    destruct (IHn GH G1 T2 H2). omega.
    eexists. eapply stp_or1. eapply stp_or21. eauto. eauto. eapply stp_or22. eauto. eauto.
Qed.

Lemma stpd_refl: forall GH G1 T1,
  closed (length GH) (length G1) 0 T1 ->
  stpd GH G1 T1 T1.
Proof.
  intros. apply stpd_refl_aux with (n:=S (tsize T1)); eauto.
Qed.

Lemma stpd_reg1 : forall GH G1 T1 T2,
                      stpd GH G1 T1 T2 ->
                      stpd GH G1 T1 T1.
Proof. intros. eapply stpd_refl. eapply stpd_closed1. eauto. Qed.

Lemma stpd_reg2 : forall GH G1 T1 T2,
                      stpd GH G1 T1 T2 ->
                      stpd GH G1 T2 T2.
Proof. intros. eapply stpd_refl. eapply stpd_closed2. eauto. Qed.


(*# Infrastructure Lemmas #*)

Ltac index_subst := match goal with
                      | H1: index ?x ?G = ?V1 , H2: index ?x ?G = ?V2 |- _ => rewrite H1 in H2; inversion H2; subst
                      | _ => idtac
                    end.

Ltac invty := match goal with
                | H1: TBot     = _ |- _ => inversion H1
                | H1: TSel _ _   = _ |- _ => inversion H1
                | H1: TTyp _ _ _ = _ |- _ => inversion H1
                | H1: TVar _ _ = _ |- _ => inversion H1
                | H1: TFun _ _ _ = _ |- _ => inversion H1
                | H1: TBind  _ = _ |- _ => inversion H1
                | H1: TAnd _ _ = _ |- _ => inversion H1
                | H1: TOr _ _ = _ |- _ => inversion H1
                | _ => idtac
              end.

Ltac invstp_var := match goal with
  | H1: stp _ true _ _ TBot        (TVar _ _) _ |- _ => inversion H1
  | H1: stp _ true _ _ TTop        (TVar _ _) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TFun _ _ _)  (TVar _ _) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TTyp _ _ _)  (TVar _ _) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TAnd _ _)  (TVar _ _) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TOr _ _)  (TVar _ _) _ |- _ => inversion H1
  | _ => idtac
end.

Lemma map_eq_some: forall {X} {Y} (f: X -> Y) OT (T: X),
  eq_some OT T ->
  eq_some (option_map f OT) (f T).
Proof.
  intros. destruct H as [EN | ES]; subst; unfold eq_some; simpl; auto.
Qed.

Lemma subst_eq_some: forall OT T U,
  eq_some OT T ->
  eq_some (option_map (subst U) OT) (subst U T).
Proof.
  intros. apply map_eq_some; auto.
Qed.

Lemma vr_closed_no_open: forall p b x k l j,
  vr_closed l k j p ->
  p = vr_open j (TVar b x) p.
Proof.
  intros. inversion H; eauto; subst.
  simpl.
  assert (j <> x0) as A. omega.
  apply beq_nat_false_iff in A.
  rewrite A. auto.
Qed.

Lemma closed_no_open: forall T b x k l j,
  closed l k j T ->
  T = open j (TVar b x) T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed; rewrite <-IHclosed; auto];
  try solve [compute; compute in IHclosed1; compute in IHclosed2; rewrite <-IHclosed1; rewrite <-IHclosed2; auto].
  simpl. f_equal. erewrite <- vr_closed_no_open; eauto.
Qed.

Lemma vr_closed_no_subst: forall p j k TX,
   vr_closed 0 j k p ->
   vr_subst TX p = p.
Proof.
  intros. inversion H; simpl; eauto; subst. omega.
Qed.

Lemma closed_no_subst: forall T j k TX,
   closed 0 j k T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
    try rewrite (IHT j (S k) TX); eauto;
    try rewrite (IHT j k TX); eauto;
    try rewrite (IHT1 j k TX); eauto; subst.

  rewrite (IHT2 j (S k) TX); eauto.
  rewrite (IHT2 j k TX); eauto.
  erewrite vr_closed_no_subst; eauto.
  rewrite (IHT2 j k TX); eauto.
  rewrite (IHT2 j k TX); eauto.
Qed.

Lemma vr_closed_subst: forall j n k V p, vr_closed (n+1) k j p -> vr_closed n k 0 V -> vr_closed n k j (vr_subst V p).
Proof.
  intros. inversion H; subst; try econstructor; eauto. simpl.
  case_eq (beq_nat x 0); intros E.
  eapply vr_closed_upgrade. eapply vr_closed_upgrade_gh. eauto. eauto. omega. econstructor. subst.
  assert (x > 0). eapply beq_nat_false_iff in E. omega. omega.
Qed.

Lemma closed_subst: forall j n k V T, closed (n+1) k j T -> vr_closed n k 0 V -> closed n k j (subst V T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H;
  try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto using vr_closed_subst.
Qed.

Lemma vr_subst_open_commute_m: forall j k n m V p2, vr_closed (n+1) k (j+1) p2 -> vr_closed m k 0 V ->
    vr_subst V (vr_open j (TVar false (n+1)) p2) = vr_open j (TVar false n) (vr_subst V p2).
Proof.
  intros. inversion H; simpl; eauto; subst.
  simpl. case_eq (beq_nat x 0); intros E.
  eapply vr_closed_no_open. eapply vr_closed_upgrade. eauto. omega.
  simpl. eauto.

  simpl. case_eq (beq_nat j x); intros E.
  simpl. case_eq (beq_nat (n+1) 0); intros E2. eapply beq_nat_true_iff in E2. omega.
  assert (n+1-1 = n) as A. omega. rewrite A. eauto.
  eauto.
Qed.

Lemma subst_open_commute_m: forall j k n m V T2, closed (n+1) k (j+1) T2 -> vr_closed m k 0 V ->
    subst V (open j (TVar false (n+1)) T2) = open j (TVar false n) (subst V T2).
Proof.
  intros. generalize dependent j. generalize dependent n.
  induction T2; intros; inversion H; simpl; eauto;
          try rewrite IHT2_1; try rewrite IHT2_2; try rewrite IHT2; subst; eauto.
  erewrite vr_subst_open_commute_m; eauto.
Qed.

Lemma subst_open_commute: forall j k n V T2, closed (n+1) k (j+1) T2 -> vr_closed 0 k 0 V ->
    subst V (open j (TVar false (n+1)) T2) = open j (TVar false n) (subst V T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_commute0: forall T0 n j TX,
  closed 0 n (j+1) T0 ->
  (subst TX (open j (TVar false 0) T0)) = open j TX T0.
Proof.
  intros T0 n. induction T0; intros.
  eauto. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. inversion H. subst. inversion H4; subst. omega. eauto. simpl.
  case_eq (beq_nat j x); intros E; simpl; eauto.
  simpl. inversion H. rewrite IHT0. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
Qed.

Lemma subst_open_commute1: forall T0 x x0 j,
 (open j (TVar true x0) (subst (TVar true x) T0))
 = (subst (TVar true x) (open j (TVar true x0) T0)).
Proof.
  induction T0; intros.
  eauto. eauto. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto.
  simpl. f_equal. destruct v; simpl.
  simpl. destruct b. simpl. eauto.
  case_eq (beq_nat i 0); intros E. simpl. eauto. simpl. eauto.
  simpl. case_eq (beq_nat j i); intros E. simpl. eauto. simpl. eauto.
  simpl. rewrite IHT0. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto.
Qed.

Lemma subst_closed_id: forall x j k T2,
  closed 0 j k T2 ->
  substt x T2 = T2.
Proof. intros. eapply closed_no_subst. eauto. Qed.

Lemma closed_subst0: forall i j k x T2,
  closed (i + 1) j k T2 -> x < j ->
  closed i j k (substt x T2).
Proof. intros. eapply closed_subst. eauto. econstructor. eauto. Qed.

Lemma closed_subst1: forall i j k x T2,
  closed i j k T2 -> x < j -> i <> 0 ->
  closed (i-1) j k (substt x T2).
Proof.
  intros. eapply closed_subst.
  assert ((i - 1 + 1) = i) as R. omega.
  rewrite R. eauto. econstructor. eauto.
Qed.

Lemma index_subst: forall GH TX T0 T3 x,
  index (length (GH ++ [TX])) (T0 :: GH ++ [TX]) = Some T3 ->
  index (length GH) (map (substt x) (T0 :: GH)) = Some (substt x T3).
Proof.
  intros GH. induction GH; intros; inversion H.
  - eauto.
  - rewrite beq_nat_true_eq in H1. inversion H1. subst. simpl.
    rewrite map_length. rewrite beq_nat_true_eq. eauto.
Qed.

Lemma index_subst1: forall GH TX T3 x x0,
  index x0 (GH ++ [TX]) = Some T3 -> x0 <> 0 ->
  index (x0-1) (map (substt x) GH) = Some (substt x T3).
Proof.
  intros GH. induction GH; intros; inversion H.
  - eapply beq_nat_false_iff in H0. rewrite H0 in H2. inversion H2.
  - simpl.
    assert (beq_nat (x0 - 1) (length (map (substt x) GH)) = beq_nat x0 (length (GH ++ [TX]))). {
      case_eq (beq_nat x0 (length (GH ++ [TX]))); intros E.
      eapply beq_nat_true_iff. rewrite map_length. eapply beq_nat_true_iff in E. subst x0.
      rewrite app_length. simpl. omega.
      eapply beq_nat_false_iff. eapply beq_nat_false_iff in E.
      rewrite app_length in E. simpl in E. rewrite map_length.
      destruct x0. destruct H0. reflexivity. omega.
    }
    rewrite H1. case_eq (beq_nat x0 (length (GH ++ [TX]))); intros E; rewrite E in H2.
    inversion H2. subst. eauto. eauto.
Qed.

Lemma index_hit0: forall (GH:tenv) TX T2,
 index 0 (GH ++ [TX]) = Some T2 -> T2 = TX.
Proof.
  intros GH. induction GH; intros; inversion H.
  - eauto.
  - rewrite app_length in H1. simpl in H1.
    remember (length GH + 1) as L. destruct L. omega. eauto.
Qed.

Lemma subst_open: forall TX n x j,
  (substt x (open j (TVar false (n+1)) TX)) =
  (open j (TVar false n) (substt x TX)).
Proof.
  intros TX. induction TX; intros; eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
  - unfold substt. simpl. destruct v. destruct b. eauto.
    simpl. case_eq (beq_nat i 0); intros E. eauto. eauto.
    simpl. case_eq (beq_nat j i); intros E. simpl.
    assert (beq_nat (n + 1) 0 = false). eapply beq_nat_false_iff. omega.
    assert ((n + 1 - 1 = n)). omega.
    rewrite H. rewrite H0. eauto. eauto.
  - unfold substt. simpl. unfold substt in IHTX. erewrite <-IHTX. eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
Qed.

Lemma subst_open3: forall TX0 (GH:tenv) TX  x,
  (substt x (open 0 (TVar false (length (GH ++ [TX]))) TX0)) =
  (open 0 (TVar false (length GH)) (substt x TX0)).
Proof. intros. rewrite app_length. simpl. eapply subst_open. Qed.

Lemma subst_open4: forall T0 (GH:tenv) TX x,
  substt x (open 0 (TVar false (length (GH ++ [TX]))) T0) =
  open 0 (TVar false (length (map (substt x) GH))) (substt x T0).
Proof. intros. rewrite map_length. eapply subst_open3. Qed.

Lemma subst_open5: forall (GH:tenv) T0 x xi,
  xi <> 0 -> substt x (open 0 (TVar false xi) T0) =
  open 0 (TVar false (xi-1)) (substt x T0).
Proof.
  intros. remember (xi-1) as n. assert (xi=n+1) as R. omega. rewrite R.
  eapply subst_open.
Qed.

Lemma subst_open_commute0b: forall x T1 n,
  substt x (open n (TVar false 0) T1) = open n (TVar true x) (substt x T1).
Proof.
  unfold substt.
  intros x T1.
  induction T1; intros n; simpl;
  try rewrite IHT1; try rewrite IHT1_1; try rewrite IHT1_2;
  eauto.
  destruct v. destruct b; eauto. simpl.
  case_eq (beq_nat i 0); intros; simpl; eauto. simpl.
  case_eq (beq_nat n i); intros; simpl; eauto.
Qed.

Lemma subst_open_commute_z: forall x T1 z n,
 subst (TVar true x) (open n (TVar false (z + 1)) T1) =
 open n (TVar false z) (subst (TVar true x) T1).
Proof.
  intros x T1 z.
  induction T1; intros n; simpl;
  try rewrite IHT1; try rewrite IHT1_1; try rewrite IHT1_2;
  eauto.
  destruct v. destruct b; eauto. simpl.
  case_eq (beq_nat i 0); intros; simpl; eauto. simpl.
  case_eq (beq_nat n i); intros; simpl; eauto.
  assert (beq_nat (z + 1) 0 = false) as A. {
    apply false_beq_nat. omega.
  }
  rewrite A. f_equal. f_equal. omega.
Qed.

Lemma gh_match1: forall (GU:tenv) GH GL TX,
  GH ++ [TX] = GU ++ GL ->
  length GL > 0 ->
  exists GL1, GL = GL1 ++ [TX] /\ GH = GU ++ GL1.
Proof.
  intros GU. induction GU; intros.
  - eexists. simpl in H. eauto.
  - destruct GH. simpl in H.
    assert (length [TX] = 1). eauto.
    rewrite H in H1. simpl in H1. rewrite app_length in H1. omega.
    destruct (IHGU GH GL TX).
    simpl in H. inversion H. eauto. eauto.
    eexists. split. eapply H1. simpl. destruct H1. simpl in H. inversion H. subst. eauto.
Qed.

Lemma gh_match: forall (GH:tenv) GU GL TX T0,
  T0 :: GH ++ [TX] = GU ++ GL ->
  length GL = S (length (GH ++ [TX])) ->
  GU = [] /\ GL = T0 :: GH ++ [TX].
Proof.
  intros. edestruct gh_match1. rewrite app_comm_cons in H. eapply H. omega.
  assert (length (T0 :: GH ++ [TX]) = length (GU ++ GL)). rewrite H. eauto.
  assert (GU = []). destruct GU. eauto. simpl in H.
  simpl in H2. rewrite app_length in H2. simpl in H2. rewrite app_length in H2.
  simpl in H2. rewrite H0 in H2. rewrite app_length in H2. simpl in H2.
  omega.
  split. eauto. rewrite H3 in H1. simpl in H1. subst. simpl in H1. eauto.
Qed.

Lemma sub_env1: forall (GL:tenv) GU GH TX,
  GH ++ [TX] = GU ++ GL ->
  length GL = 1 ->
  GL = [TX].
Proof.
  intros.
  destruct GL. inversion H0. destruct GL.
  eapply app_inj_tail in H. destruct H. subst. eauto.
  inversion H0.
Qed.

Lemma app_cons1: forall (G1:venv) v,
  v::G1 = [v]++G1.
Proof.
  intros. simpl. eauto.
Qed.

Lemma index_at_index: forall {A} x0 GH0 GH1 (v:A),
  beq_nat x0 (length GH1) = true ->
  index x0 (GH0 ++ v :: GH1) = Some v.
Proof.
  intros. apply beq_nat_true in H. subst.
  induction GH0.
  - simpl. rewrite <- beq_nat_refl. reflexivity.
  - simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    rewrite false_beq_nat. assumption. omega.
Qed.

Lemma index_same: forall {A} x0 (v0:A) GH0 GH1 (v:A) (v':A),
  beq_nat x0 (length GH1) = false ->
  index x0 (GH0 ++ v :: GH1) = Some v0 ->
  index x0 (GH0 ++ v' :: GH1) = Some v0.
Proof.
  intros ? ? ? ? ? ? ? E H.
  induction GH0.
  - simpl. rewrite E. simpl in H. rewrite E in H. apply H.
  - simpl.
    rewrite app_length. simpl.
    case_eq (beq_nat x0 (length GH0 + S (length GH1))); intros E'.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite H. reflexivity.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite IHGH0. reflexivity. assumption.
Qed.

Lemma exists_GH1L: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GH0 <= length GL ->
  exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ GH0.
Proof.
  intros X GU. induction GU; intros.
  - eexists. rewrite app_nil_l. split. reflexivity. simpl in H0. assumption.
  - induction GH1.

    simpl in H.
    assert (length (a :: GU ++ GL) = length GH0) as Contra. {
      rewrite H. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H. inversion H.
    specialize (IHGU GL GH1 GH0 H3 H0).
    destruct IHGU as [GH1L [IHA IHB]].
    exists GH1L. split. simpl. rewrite IHA. reflexivity. apply IHB.
Qed.

Lemma exists_GH0U: forall {X} (GH1: list X) (GH0: list X) (GU: list X) (GL: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GL < S (length GH0) ->
  exists GH0U, GH0 = GH0U ++ GL.
Proof.
  intros X GH1. induction GH1; intros.
  - simpl in H. exists GU. symmetry. assumption.
  - induction GU.

    simpl in H.
    assert (length GL = length (a :: GH1 ++ GH0)) as Contra. {
      rewrite H. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H. inversion H.
    specialize (IHGH1 GH0 GU GL H3 H0).
    destruct IHGH1 as [GH0U IH].
    exists GH0U. apply IH.
Qed.

(*# Regularity II -- Abstract Context Weakening #*)

(* upgrade_gh interlude begin *)

(* splicing -- for stp_extend. *)

Definition splice_var n i := if le_lt_dec n i then (i+1) else i.
Hint Unfold splice_var.

Definition vr_splice n (v: vr) :=
  match v with
    | TVarB i      => TVarB i
    | TVar true i  => TVar true i
    | TVar false i => TVar false (splice_var n i)
  end.
Fixpoint splice n (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TTyp l T1 T2 => TTyp l (splice n T1) (splice n T2)
    | TSel p1 l    => TSel (vr_splice n p1) l
    | TFun l T1 T2 => TFun l (splice n T1) (splice n T2)
    | TBind T2     => TBind (splice n T2)
    | TAnd T1 T2   => TAnd (splice n T1) (splice n T2)
    | TOr T1 T2    => TOr (splice n T1) (splice n T2)
  end.

Definition spliceat n (V: (venv*ty)) :=
  match V with
    | (G,T) => (G,splice n T)
  end.

Lemma splice_open_permute: forall {X} (G0:list X) T2 n j,
(open j (TVar false (n + S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open j (TVar false (n + length G0)) T2)).
Proof.
  intros X G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto.
  destruct v. destruct b; eauto. simpl.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  unfold splice_var. simpl.
  case_eq (le_lt_dec (length G) (n + length G)); intros EL LE.
  assert (n + S (length G) = n + length G + 1). omega.
  rewrite H. eauto.
  omega.
Qed.

Lemma splice_open_permute0: forall {X} (G0:list X) T2 j,
(open j (TVar false (S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open j (TVar false (length G0)) T2)).
Proof.
  intros.
  change (TVar false (length G0)) with (TVar false (0 + (length G0))).
  rewrite <- splice_open_permute. reflexivity.
Qed.

Lemma index_splice_hi: forall G0 G2 x0 v1 T,
    index x0 (G2 ++ G0) = Some T ->
    length G0 <= x0 ->
    index (x0 + 1) (map (splice (length G0)) G2 ++ v1 :: G0) = Some (splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply index_max in H. simpl in H. omega.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply index_extend. eapply H. eauto.
Qed.

Lemma index_spliceat_hi: forall G0 G2 x0 v1 G T,
    index x0 (G2 ++ G0) = Some (G, T) ->
    length G0 <= x0 ->
    index (x0 + 1) (map (spliceat (length G0)) G2 ++ v1 :: G0) =
    Some (G, splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply index_max in H. simpl in H. omega.
  - simpl in H. destruct a.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply index_extend. eapply H. eauto.
Qed.

Lemma index_splice_lo0: forall {X} G0 G2 x0 (T:X),
    index x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    index x0 G0 = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl in H. apply H.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E. subst.
      rewrite app_length in H0. apply plus_lt_contra in H0. inversion H0.
    + rewrite E in H. apply IHG2. apply H. apply H0.
Qed.

Lemma index_splice_lo: forall G0 G2 x0 v1 T f,
    index x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    index x0 (map (splice f) G2 ++ v1 :: G0) = Some T.
Proof.
  intros.
  assert (index x0 G0 = Some T). eapply index_splice_lo0; eauto.
  eapply index_extend_mult. eapply index_extend. eauto.
Qed.

Lemma index_spliceat_lo: forall G0 G2 x0 v1 G T f,
    index x0 (G2 ++ G0) = Some (G, T) ->
    x0 < length G0 ->
    index x0 (map (spliceat f) G2 ++ v1 :: G0) = Some (G, T).
Proof.
  intros.
  assert (index x0 G0 = Some (G, T)). eapply index_splice_lo0; eauto.
  eapply index_extend_mult. eapply index_extend. eauto.
Qed.

Lemma vr_closed_splice: forall i j k p n,
  vr_closed i j k p ->
  vr_closed (S i) j k (vr_splice n p).
Proof.
  Hint Constructors vr_closed.
  intros. inversion H; simpl; subst; eauto.
  unfold splice_var.
  case_eq (le_lt_dec n x); intros E LE;
  econstructor; omega.
Qed.
Lemma closed_splice: forall i j k T n,
  closed i j k T ->
  closed (S i) j k (splice n T).
Proof.
  intros.
  Hint Constructors closed.
  induction H; simpl; eauto using vr_closed_splice.
Qed.

Lemma map_splice_length_inc: forall G0 G2 v1,
   (length (map (splice (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma map_spliceat_length_inc: forall G0 G2 v1,
   (length (map (spliceat (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_inc_mult: forall i j k T,
  closed i j k T ->
  forall i' j' k',
  i' >= i -> j' >= j -> k' >= k ->
  closed i' j' k' T.
Proof.
  intros.
  eapply closed_upgrade_gh.
  eapply closed_upgrade.
  eapply closed_extend_mult.
  eauto. eauto. eauto. eauto.
Qed.

Lemma closed_inc: forall i j k T,
  closed i j k T ->
  closed (S i) j k T.
Proof.
  intros. apply (closed_inc_mult i j k T H (S i) j k); omega.
Qed.

Lemma vr_closed_splice_idem: forall i j k p n,
                            vr_closed i j k p ->
                            n >= i ->
                            vr_splice n p = p.
Proof.
  intros. inversion H; eauto; subst. simpl.
  unfold splice_var.
  case_eq (le_lt_dec n x); intros E LE.
  omega. reflexivity.
Qed.

Lemma closed_splice_idem: forall i j k T n,
                            closed i j k T ->
                            n >= i ->
                            splice n T = T.
Proof.
  intros. induction H; eauto;
  simpl; try rewrite IHclosed; try rewrite IHclosed1; try rewrite IHclosed2; eauto.
  erewrite vr_closed_splice_idem; eauto.
Qed.

Lemma stp_splice_aux: forall ni, (forall GX G0 G1 T1 T2 v1 n,
   stp (G1++G0) GX T1 T2 n -> n < ni ->
   stp ((map (splice (length G0)) G1) ++ v1::G0) GX
   (splice (length G0) T1) (splice (length G0) T2) n) /\
  (forall GX G0 G1 x1 T1 v1 n,
   htp (G1++G0) GX x1 T1 n -> n < ni ->
   htp ((map (splice (length G0)) G1) ++ v1::G0) GX
   (splice_var (length G0) x1) (splice (length G0) T1) n).
Proof.
  intro ni. induction ni. split; intros; omega.
  destruct IHni as [IHstp IHhtp].
  split; intros; inversion H; subst.
  - Case "bot".
    eapply stp_bot.
    rewrite map_splice_length_inc.
    simpl. apply closed_splice.
    assumption.
  - Case "top".
    eapply stp_top.
    rewrite map_splice_length_inc.
    apply closed_splice.
    assumption.
  - Case "fun".
    eapply stp_fun.
    eauto. eauto.
    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.
    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.
    eapply IHstp. eauto. omega.
    specialize (IHstp GX G0 (T4::G1)).
    simpl in IHstp. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    eapply IHstp. rewrite <- app_length. eauto. omega.
  - Case "typ".
    eapply stp_typ.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "ssel1".
    eapply stp_strong_sel1. eauto. eauto.
    assert (splice (length G0) T2=T2) as A. {
      eapply closed_splice_idem. eapply stp_closed2. eapply H3. simpl. omega.
    }
    rewrite A. assumption.
  - Case "ssel2".
    eapply stp_strong_sel2. eauto. eauto.
    assert (splice (length G0) T1=T1) as A. {
      eapply closed_splice_idem. eapply stp_closed1. eapply H3. simpl. omega.
    }
    rewrite A. assumption.
  - Case "sel1".
    eapply stp_sel1.
    specialize (IHhtp GX G0 G1 x (TTyp l TBot T2)). simpl in IHhtp.
    eapply IHhtp. eauto. omega.
  - Case "sel2".
    eapply stp_sel2.
    specialize (IHhtp GX G0 G1 x (TTyp l T1 TTop)). simpl in IHhtp.
    eapply IHhtp. eauto. omega.
  - Case "selx".
    eapply stp_selx.
    rewrite map_splice_length_inc. eapply vr_closed_splice. eauto.
  - Case "bind1".
    eapply stp_bind1.
    specialize (IHstp GX G0 ((open 0 (TVar false (length (G1 ++ G0))) T0)::G1)).
    simpl in IHstp. eapply IHstp. eauto. omega.
    rewrite app_length. rewrite <- splice_open_permute.
    rewrite map_splice_length_inc. rewrite app_length.
    assert (length G1 + S (length G0)=(S (length G1 + length G0))) as B by omega.
    rewrite B. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "bindx".
    eapply stp_bindx.
    specialize (IHstp GX G0 ((open 0 (TVar false (length (G1 ++ G0))) T0)::G1)).
    simpl in IHstp. eapply IHstp. eauto. omega.
    rewrite app_length. rewrite <- splice_open_permute.
    rewrite map_splice_length_inc. rewrite app_length.
    assert (length G1 + S (length G0)=(S (length G1 + length G0))) as B by omega.
    rewrite B. eauto.
    rewrite app_length. rewrite <- splice_open_permute.
    rewrite map_splice_length_inc. rewrite app_length.
    assert (length G1 + S (length G0)=(S (length G1 + length G0))) as B by omega.
    rewrite B. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "and11".
    simpl. eapply stp_and11.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "and12".
    simpl. eapply stp_and12.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "and2".
    simpl. eapply stp_and2.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "or21".
    simpl. eapply stp_or21.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "or22".
    simpl. eapply stp_or22.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "or1".
    simpl. eapply stp_or1.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "trans".
    eapply stp_trans.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "htp_var".
    unfold splice_var.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + eapply htp_var.
      apply index_splice_hi. eauto. eauto.
      eapply closed_splice.
      assert (S x1 = x1 + 1) as A by omega.
      rewrite <- A. eauto.
    + assert (splice (length G0) T1=T1) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      eapply htp_var.
      eapply index_splice_lo.
      rewrite A. eauto. omega.
      rewrite A. eauto.
  - Case "htp_unpack".
    unfold splice_var.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + remember (x1 - (length G0)) as n.
      assert (x1 = n + length G0) as A. {
        clear LE. apply le_plus_minus in E.
        rewrite E. unfold id in *. omega.
      }
      rewrite A at 2.
      rewrite <- splice_open_permute.
      assert (n + S (length G0)=x1+1) as B. {
        rewrite Heqn. omega.
      }
      rewrite B.
      eapply htp_unpack.
      specialize (IHhtp GX G0 G1 x1 (TBind TX)).
      simpl in IHhtp. unfold splice_var in IHhtp. rewrite LE in IHhtp.
      eapply IHhtp. eauto. omega.
      assert (S x1 = x1 + 1) as C by omega. rewrite <- C.
      eapply closed_splice. eauto.
    + assert (splice (length G0) TX = TX) as A. {
        eapply closed_splice_idem. eauto. omega.
      }
      assert (splice (length G0) (open 0 (TVar false x1) TX)=open 0 (TVar false x1) TX) as B. {
        eapply closed_splice_idem.
        eapply closed_open. eapply closed_upgrade_gh. eauto.
        instantiate (1:=S x1). omega.
        econstructor. omega. omega.
      }
      rewrite B.
      eapply htp_unpack.
      specialize (IHhtp GX G0 G1 x1 (TBind TX)).
      simpl in IHhtp. unfold splice_var in IHhtp. rewrite LE in IHhtp.
      rewrite <- A. eapply IHhtp. eauto. omega. eauto.
  - Case "htp_sub".
    unfold splice_var.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + assert (S x1 = x1 + 1) as A by omega.
      assert (exists GH1L, G1 = GU ++ GH1L /\ GL = GH1L ++ G0) as EQGH. {
        eapply exists_GH1L. eauto. omega.
      }
      destruct EQGH as [GH1L [EQGH1 EQGL]].
      assert (splice_var (length G0) x1=x1+1) as B. {
        unfold splice_var. rewrite LE. reflexivity.
      }
      rewrite <- B.
      eapply htp_sub.
      eapply IHhtp. eauto. omega.
      eapply IHstp. subst. eauto. omega.
      rewrite app_length. rewrite map_length. simpl.
      unfold splice_var. rewrite LE. subst. rewrite app_length in *. omega.
      subst. rewrite map_app. simpl. rewrite app_assoc. reflexivity.
    + assert (splice (length G0) T1=T1) as A1. {
        eapply closed_splice_idem. eapply stp_closed2. eauto. omega.
      }
      assert (splice (length G0) T0=T0) as A0. {
        eapply closed_splice_idem. eapply stp_closed1. eauto. omega.
      }
      assert (exists GH0U, G0 = GH0U ++ GL) as EQGH. {
        eapply exists_GH0U. eauto. omega.
      }
      destruct EQGH as [GH0U EQGH].
      assert (splice_var (length G0) x1=x1) as C. {
        unfold splice_var. rewrite LE. reflexivity.
      }
      rewrite <- C.
      eapply htp_sub.
      eapply IHhtp. eauto. omega.
      rewrite A1. rewrite A0. eauto.
      rewrite C. eauto.
      instantiate (1:=(map (splice (length G0)) G1 ++ v1 :: GH0U)).
      rewrite <- app_assoc. simpl. rewrite EQGH. reflexivity.
Qed.

Lemma stp_splice: forall GX G0 G1 T1 T2 v1 n,
   stp (G1++G0) GX T1 T2 n ->
   stp ((map (splice (length G0)) G1) ++ v1::G0) GX
   (splice (length G0) T1) (splice (length G0) T2) n.
Proof. intros. eapply stp_splice_aux. eauto. eauto. Qed.

Lemma htp_splice: forall GX G0 G1 x1 T1 v1 n,
   htp (G1++G0) GX x1 T1 n ->
   htp ((map (splice (length G0)) G1) ++ v1::G0) GX
   (splice_var (length G0) x1) (splice (length G0) T1) n.
Proof. intros. eapply stp_splice_aux. eauto. eauto. Qed.

Lemma stp_upgrade_gh_aux: forall ni,
  (forall GH T G1 T1 T2 n,
     stp GH G1 T1 T2 n -> n < ni ->
     stp (T::GH) G1 T1 T2 n) /\
  (forall T x GH G1 T2 n,
     htp GH G1 x T2 n -> n < ni ->
     htp (T::GH) G1 x T2 n).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H.
  (* stp *)
  - econstructor. eapply closed_upgrade_gh. eauto. simpl. omega.
  - econstructor. eapply closed_upgrade_gh. eauto. simpl. omega.
  - econstructor. eauto. eauto.
    eapply closed_upgrade_gh. eauto. simpl. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply IHn. eauto. omega.
    subst.
    assert (splice (length GH) T0 = T0) as A. {
      eapply closed_splice_idem. eapply stp_closed2. eauto. omega.
    }
    assert (splice (length GH) T4 = T4) as B. {
      eapply closed_splice_idem. eapply stp_closed1. eauto. omega.
    }
    assert (splice (length GH) T3 = T3) as C. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length GH) T5 = T5) as D. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (map (splice (length GH)) [T4] ++ T::GH =
          (T4::T::GH)) as HGX. {
      simpl. rewrite B. eauto.
    }
    simpl. change (S (length GH)) with (0 + (S (length GH))).
    rewrite <- C. rewrite <- D.
    rewrite splice_open_permute. rewrite splice_open_permute.
    rewrite <- HGX.
    apply stp_splice. simpl. eauto.

  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eauto. eauto. eauto.
  - econstructor. eauto. eauto. eauto.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply vr_closed_upgrade_gh. eauto. simpl. omega.
  - subst.
    assert (splice (length GH) T0 = T0) as A. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length GH) T2 = T2) as B. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (length (T :: GH)=splice_var (length GH) (length GH)) as C. {
      unfold splice_var. simpl.
      case_eq (le_lt_dec (length GH) (length GH)); intros E LE; omega.
    }
    assert (map (splice (length GH)) [(open 0 (TVar false (length GH)) T0)] ++ T::GH =
          (((open 0 (TVar false (S (length GH))) (splice (length GH) T0)))::T::GH)) as HGX. {
      simpl. rewrite <- splice_open_permute0. reflexivity.
    }
    eapply stp_bind1.
    rewrite <- B.
    instantiate (1:=(open 0 (TVar false (S (length GH))) (splice (length GH) T0))).
    rewrite <- HGX. rewrite splice_open_permute0.
    apply stp_splice. simpl. eauto. simpl. rewrite A. reflexivity.
    eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply closed_upgrade_gh. eauto. simpl. omega.

  - subst.
    assert (splice (length GH) T0 = T0) as A. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length GH) T3 = T3) as B. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (length (T :: GH)=splice_var (length GH) (length GH)) as C. {
      unfold splice_var. simpl.
      case_eq (le_lt_dec (length GH) (length GH)); intros E LE; omega.
    }
    assert (map (splice (length GH)) [(open 0 (TVar false (length GH)) T0)] ++ T::GH =
          (((open 0 (TVar false (S (length GH))) (splice (length GH) T0)))::T::GH)) as HGX. {
      simpl. rewrite <- splice_open_permute0. reflexivity.
    }
    eapply stp_bindx.
    instantiate (2:=(open 0 (TVar false (S (length GH))) (splice (length GH) T0))).
    rewrite <- HGX. rewrite splice_open_permute0.
    apply stp_splice. simpl. eauto. simpl. rewrite A. reflexivity.
    simpl. rewrite <- splice_open_permute0. rewrite B. reflexivity.
    eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply closed_upgrade_gh. eauto. simpl. omega.

  - eapply stp_and11. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_and12. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_and2. eapply IHn. eauto. omega. eapply IHn. eauto. omega.

  - eapply stp_or21. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_or22. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_or1. eapply IHn. eauto. omega. eapply IHn. eauto. omega.

  - eapply stp_trans. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  (* htp *)
  - econstructor. eapply index_extend. eauto. eapply closed_upgrade_gh. eauto. omega.
  - eapply htp_unpack. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. omega.
  - eapply htp_sub. eapply IHn. eauto. omega. eauto. eauto. subst GH.
    instantiate (1:=T::GU). eauto.
Qed.

Lemma stp_upgrade_gh : forall GH T G1 T1 T2 n,
                      stp GH G1 T1 T2 n ->
                      stp (T::GH) G1 T1 T2 n.
Proof. intros. eapply stp_upgrade_gh_aux. eauto. eauto. Qed.

Lemma stp_upgrade_gh_mult : forall GH GH' G1 T1 T2 n,
                      stp GH G1 T1 T2 n ->
                      stp (GH'++GH) G1 T1 T2 n.
Proof. intros. induction GH'. simpl. eauto. simpl. eapply stp_upgrade_gh. eauto. Qed.

Lemma stp_upgrade_gh_mult0 : forall GH G1 T1 T2 n,
                      stp [] G1 T1 T2 n ->
                      stp GH G1 T1 T2 n.
Proof. intros. rewrite <- (app_nil_r GH). eapply stp_upgrade_gh_mult. eauto. Qed.

Lemma hastp_upgrade_gh_var: forall G1 GH x T n1,
  has_type [] G1 (tvar true x) T n1 ->
  has_type GH G1 (tvar true x) T n1.
Proof.
  intros.
  remember (tvar true x) as t.  remember [] as GH0.
  induction H; eauto; inversion Heqt; subst.
  - eapply T_VarPack. eauto. eauto. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply T_VarUnpack. eauto. eauto. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply T_Sub. eauto. eapply stp_upgrade_gh_mult0. eauto.
Qed.

Lemma hastp_upgrade_gh: forall G1 GH x T n1,
  has_type [] G1 (tvar true x) T n1 ->
  exists n, has_type GH G1 (tvar true x) T n.
Proof.
  intros. exists n1.
  induction GH. simpl. eauto. simpl. eapply hastp_upgrade_gh_var. eauto.
Qed.

(* upgrade_gh interlude ends *)

(*# Narrowing in Abstract Context #*)

Lemma stp_narrow_aux: forall n,
  (forall GH G x T n0,
  htp GH G x T n0 -> n0 <= n ->
  forall GH1 GH0 GH' TX1 TX2,
    GH=GH1++[TX2]++GH0 ->
    GH'=GH1++[TX1]++GH0 ->
    stpd ([TX1]++GH0) G TX1 TX2 ->
    htpd GH' G x T) /\
  (forall GH G T1 T2 n0,
  stp GH G T1 T2 n0 -> n0 <= n ->
  forall GH1 GH0 GH' TX1 TX2,
    GH=GH1++[TX2]++GH0 ->
    GH'=GH1++[TX1]++GH0 ->
    stpd ([TX1]++GH0) G TX1 TX2 ->
    stpd GH' G T1 T2).
Proof.
  intros n.
  induction n.
  - Case "z". split; intros; inversion H0; subst; inversion H; eauto.
  - Case "s n". destruct IHn as [IHn_htp IHn_stp].
    split.
    {
    intros GH G x T n0 H NE. inversion H; subst;
    intros GH1 GH0 GH' TX1 TX2 EGH EGH' HX.
    + SCase "var".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (index x ([TX2]++GH0) = Some TX2) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (index x GH = Some TX2) as A2'. {
          rewrite EGH. eapply index_extend_mult. apply A2.
        }
        rewrite A2' in H0. inversion H0. subst.
        destruct HX as [nx HX].
        eexists. eapply htp_sub. eapply htp_var. eapply index_extend_mult.
        simpl. rewrite E. reflexivity.
        eapply stp_closed1 in HX. simpl in HX. eapply closed_upgrade_gh.
        eapply HX. apply beq_nat_true in E. subst. omega.
        eauto. simpl. f_equal. apply beq_nat_true in E. subst. reflexivity.
        simpl. reflexivity.
      * assert (index x GH' = Some T) as A. {
          subst.
          eapply index_same. apply E. eassumption.
        }
        eexists. eapply htp_var. eapply A.
        subst. eauto.
    + SCase "unpack".
      edestruct IHn_htp with (GH:=GH) (GH':=GH').
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply htp_unpack; eauto.
    + SCase "sub".
      edestruct IHn_htp as [? Htp].
      eapply H0. omega. eapply EGH. eapply EGH'. assumption.
      case_eq (le_lt_dec (S (length GH0)) (length GL)); intros E' LE'.
      assert (exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ (TX2) :: GH0) as EQGH. {
        eapply exists_GH1L. eassumption. simpl. eassumption.
      }
      destruct EQGH as [GH1L [EQGH1 EQGL]].
      edestruct IHn_stp as [? Hsub].
      eapply H1. omega. simpl. eapply EQGL. simpl. reflexivity. eapply HX.

      eexists. eapply htp_sub. eapply Htp. eapply Hsub.
      subst. rewrite app_length in *. simpl in *. eauto.
      rewrite EGH'. simpl. rewrite EQGH1. rewrite <- app_assoc. reflexivity.
      assert (exists GH0U, TX2::GH0 = GH0U ++ GL) as EQGH. {
        eapply exists_GH0U. eassumption. simpl. omega.
      }
      destruct EQGH as [GH0U EQGH].
      destruct GH0U. simpl in EQGH.
      assert (length (TX2::GH0)=length GL) as Contra. {
        rewrite EQGH. reflexivity.
      }
      simpl in Contra. rewrite <- Contra in H2. subst. omega.
      simpl in EQGH. inversion EQGH.
      eexists. eapply htp_sub. eapply Htp. eassumption. eauto.
      instantiate (1:=GH1 ++ [TX1] ++ GH0U). subst.
      rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
    }

    intros GH G T1 T2 n0 H NE. inversion H; subst;
    intros GH1 GH0 GH' TX1 TX2 EGH EGH' HX;
    assert (length GH' = length GH) as EGHLEN by solve [
      subst; repeat rewrite app_length; simpl; reflexivity
    ].
    + SCase "bot". eapply stpd_bot. rewrite EGHLEN; assumption.
    + SCase "top". eapply stpd_top. rewrite EGHLEN; assumption.
    + SCase "fun". eapply stpd_fun.
      reflexivity. reflexivity.
      rewrite EGHLEN; assumption. rewrite EGHLEN; assumption.
      eapply IHn_stp; try eassumption. omega.
      eapply IHn_stp with (GH1:=(T4::GH1)); try eassumption.
      rewrite EGHLEN. eauto. omega.
      subst. simpl. reflexivity. subst. simpl. reflexivity.
    + SCase "typ". eapply stpd_typ.
      eapply IHn_stp; try eassumption. omega.
      eapply IHn_stp; try eassumption. omega.
    + SCase "ssel1". eexists. eapply stp_strong_sel1; try eassumption.
    + SCase "ssel2". eexists. eapply stp_strong_sel2; try eassumption.
    + SCase "sel1".
      edestruct IHn_htp as [? Htp]; eauto. omega.
    + SCase "sel2".
      edestruct IHn_htp as [? Htp]; eauto. omega.
    + SCase "selx".
      eexists. eapply stp_selx.
      subst. rewrite app_length in *. simpl in *. assumption.
    + SCase "bind1".
      edestruct IHn_stp with (GH1:=(open 0 (TVar false (length GH)) T0 :: GH1)) as [? IH].
      eapply H0. omega. rewrite EGH. reflexivity. reflexivity. eapply HX.
      eexists. eapply stp_bind1.
      subst. simpl. simpl in IH. eapply IH.
      rewrite EGHLEN. subst. simpl. reflexivity.
      rewrite EGHLEN. assumption. rewrite EGHLEN. assumption.
    + SCase "bindx".
      edestruct IHn_stp with (GH1:=(open 0 (TVar false (length GH)) T0 :: GH1)) as [? IH].
      eapply H0. omega. rewrite EGH. reflexivity. reflexivity. eapply HX.
      eexists. eapply stp_bindx.
      subst. simpl. simpl in IH. eapply IH.
      rewrite EGHLEN. subst. simpl. reflexivity.
      rewrite EGHLEN. subst. simpl. reflexivity.
      rewrite EGHLEN. assumption. rewrite EGHLEN. assumption.
    + SCase "and11".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_and11. eapply IH. rewrite EGHLEN. assumption.
    + SCase "and12".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_and12. eapply IH. rewrite EGHLEN. assumption.
    + SCase "and2".
      edestruct IHn_stp as [? IH1].
      eapply H0. omega. eauto. eauto. eauto.
      edestruct IHn_stp as [? IH2].
      eapply H1. omega. eauto. eauto. eauto.
      eexists. eapply stp_and2. eapply IH1. eapply IH2.
    + SCase "or21".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_or21. eapply IH. rewrite EGHLEN. assumption.
    + SCase "or22".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_or22. eapply IH. rewrite EGHLEN. assumption.
    + SCase "or1".
      edestruct IHn_stp as [? IH1].
      eapply H0. omega. eauto. eauto. eauto.
      edestruct IHn_stp as [? IH2].
      eapply H1. omega. eauto. eauto. eauto.
      eexists. eapply stp_or1. eapply IH1. eapply IH2.
    + SCase "trans".
      edestruct IHn_stp as [? IH1].
      eapply H0. omega. eauto. eauto. eauto.
      edestruct IHn_stp as [? IH2].
      eapply H1. omega. eauto. eauto. eauto.
      eexists. eapply stp_trans. eapply IH1. eapply IH2.
Grab Existential Variables.
apply 0. apply 0. apply 0.
Qed.

Lemma stp_narrow: forall TX1 TX2 GH0 G T1 T2 n nx,
  stp ([TX2]++GH0) G T1 T2 n ->
  stp ([TX1]++GH0) G TX1 TX2 nx ->
  stpd ([TX1]++GH0) G T1 T2.
Proof.
  intros. eapply stp_narrow_aux. eapply H. reflexivity.
  instantiate(3:=nil). simpl. reflexivity. simpl. reflexivity.
  eauto.
Qed.

Lemma stp_narrow_norec: forall TX1 TX2 GH0 G T1 T2 n nx,
  stp ([TX2]++GH0) G T1 T2 n ->
  stp GH0 G TX1 TX2 nx ->
  stpd ([TX1]++GH0) G T1 T2.
Proof.
  intros. eapply stp_narrow; eauto using stp_upgrade_gh.
Qed.

Lemma stp_narrow0: forall TX1 TX2 G T1 T2 n nx,
  stp [TX2] G T1 T2 n ->
  stp [TX1] G TX1 TX2 nx ->
  stpd [TX1] G T1 T2.
Proof.
  intros. eapply stp_narrow; eauto.
Qed.

Lemma length_subst_dms: forall ds x,
  (length (dms_to_list ds))=(length (dms_to_list (subst_dms x ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma index_subst_dms: forall ds ds0 D ds1 x,
  dms_to_list ds = ds0 ++ dms_to_list (dcons D ds1) ->
  index (length (dms_to_list ds1)) (dms_to_list (subst_dms x ds)) = Some (subst_dm x D).
Proof.
  intros. generalize dependent ds1. generalize dependent ds. induction ds0; intros.
  - simpl in H. destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite <- length_subst_dms. rewrite beq_nat_true_eq. reflexivity.
  - destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite false_beq_nat. eapply IHds0. eauto.
    rewrite <- length_subst_dms. rewrite H2. rewrite app_length. simpl.
    omega.
Qed.
