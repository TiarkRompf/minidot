(*
DOT without recursion, storeless
T ::= Bot | Top | T1 /\ T2 | T1 \/ T2 |
      { def m(x: S): U^x } | { type A: S..U } | p.A
t ::= p | new { d... } | t.m(t)
d ::= { def m(x: S): U^x = t^x } | { type A = T }
v ::= { d... }
p ::= x | v
*)

(* in small-step *)
Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Lt.

Definition id := nat.
Definition lb := nat.

Inductive vr : Type :=
  | VAbs: id(*absolute position in context, from origin, invariant under context extension*) -> vr
  | VObj: dms -> vr
with ty : Type :=
  | TBot   : ty
  | TTop   : ty
  | TFun   : lb -> ty -> ty -> ty
  | TMem   : lb -> ty -> ty -> ty
  | TVar   : vr -> ty
  | TVarB  : id(*bound variable, de Bruijn, locally nameless style -- see open *) -> ty
  | TSel   : ty -> lb -> ty
  | TAnd   : ty -> ty -> ty
  | TOr    : ty -> ty -> ty
with  tm : Type :=
  | tvar  : vr -> tm
  | tobj  : dms(*NO self*) -> tm
  | tapp  : tm -> lb -> tm -> tm

with dm : Type :=
  | dfun : ty -> ty -> tm -> dm
  | dty  : ty -> dm

(* we need our own list-like structure for stuctural recursion, e.g. in subst_tm *)
with dms : Type :=
  | dnil : dms
  | dcons : dm -> dms -> dms
.

Fixpoint dms_to_list (ds: dms) : list dm :=
  match ds with
    | dnil => []
    | dcons d ds => d :: dms_to_list ds
  end.

Definition tenv := list ty.

Hint Unfold tenv.

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

Inductive closed: nat(*abstract, TVar false i*) -> nat(*bound, TVarB k*)
                  -> ty -> Prop :=
| cl_bot: forall i k,
    closed i k TBot
| cl_top: forall i k,
    closed i k TTop
| cl_fun: forall i k l T1 T2,
    closed i k T1 ->
    closed i (S k) T2 ->
    closed i k (TFun l T1 T2)
| cl_mem: forall i k l T1 T2,
    closed i k T1 ->
    closed i k T2 ->
    closed i k (TMem l T1 T2)
| cl_var0: forall i k x,
    i > x ->
    closed i k (TVar (VAbs x))
| cl_var1: forall i k ds,
    closed i k (TVar (VObj ds))
| cl_varB: forall i k x,
    k > x ->
    closed i k (TVarB x)
| cl_sel: forall i k T1 l,
    closed i k T1 ->
    closed i k (TSel T1 l)
| cl_and: forall i k T1 T2,
    closed i k T1 ->
    closed i k T2 ->
    closed i k (TAnd T1 T2)
| cl_or: forall i k T1 T2,
    closed i k T1 ->
    closed i k T2 ->
    closed i k (TOr T1 T2)
.


Fixpoint open (k: nat) (u: ty) (T: ty) { struct T }: ty :=
  match T with
    | TVar v => TVar v (* free var remains free. functional, so we can't check for conflict *)
    | TVarB x => if beq_nat k x then u else TVarB x
    | TTop        => TTop
    | TBot        => TBot
    | TSel T1 l     => TSel (open k u T1) l
    | TFun l T1 T2  => TFun l (open k u T1) (open (S k) u T2)
    | TMem l T1 T2  => TMem l (open k u T1) (open k u T2)
    | TAnd T1 T2  => TAnd (open k u T1) (open k u T2)
    | TOr T1 T2   => TOr (open k u T1) (open k u T2)
  end.

Fixpoint subst (U : ty) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TMem l T1 T2 => TMem l (subst U T1) (subst U T2)
    | TSel T1 l    => TSel (subst U T1) l
    | TVarB i      => TVarB i
    | TVar (VObj ds)  => TVar (VObj ds)
    (* subst the _first_ aka _oldest_ abstract variables,
       the other abstract variables are shifted to resolve in the shrinked context *)
    | TVar (VAbs i) => if beq_nat i 0 then U else TVar (VAbs (i-1))
    | TFun l T1 T2 => TFun l (subst U T1) (subst U T2)
    | TAnd T1 T2   => TAnd (subst U T1) (subst U T2)
    | TOr T1 T2    => TOr (subst U T1) (subst U T2)
  end.


Fixpoint subst_tm (u:dms) (T : tm) {struct T} : tm :=
  match T with
    | tvar (VObj i)         => tvar (VObj i)
    | tvar (VAbs i)        => if beq_nat i 0 then (tvar (VObj u)) else tvar (VAbs (i-1))
    | tobj ds             => tobj (subst_dms u ds)
    | tapp t1 l t2          => tapp (subst_tm u t1) l (subst_tm u t2)
  end
with subst_dm (u:dms) (d: dm) {struct d} : dm :=
  match d with
    | dty T        => dty (subst (TVar (VObj u)) T)
    | dfun T1 T2 t => dfun (subst (TVar (VObj u)) T1) (subst (TVar (VObj u)) T2) (subst_tm u t)
  end
with subst_dms (u:dms) (ds: dms) {struct ds} : dms :=
  match ds with
    | dnil        => dnil
    | dcons d ds1  => dcons (subst_dm u d) (subst_dms u ds1)
  end.

Definition substt x T := (subst (TVar (VObj x)) T).
Hint Immediate substt.

Inductive has_type : tenv -> tm -> ty -> nat -> Prop :=
  | T_Vary : forall GH ds T n1,
      dms_has_type [] ds T n1 ->
      has_type GH (tvar (VObj ds)) T (S n1)
  | T_Varz : forall GH x T n1,
      index x GH = Some T ->
      closed (length GH) 0 T ->
      has_type GH (tvar (VAbs x)) T (S n1)
  | T_Obj : forall GH ds T n1,
      dms_has_type GH ds T n1 ->
      has_type GH (tobj ds) T (S n1)
  | T_App : forall l T1 T2 GH t1 t2 n1 n2,
      has_type GH t1 (TFun l T1 T2) n1 ->
      has_type GH t2 T1 n2 ->
      closed (length GH) 0 T2 ->
      has_type GH (tapp t1 l t2) T2 (S (n1+n2))
  | T_AppVar : forall l T1 T2 T2' GH t1 v2 n1 n2,
      has_type GH t1 (TFun l T1 T2) n1 ->
      has_type GH (tvar v2) T1 n2 ->
      T2' = (open 0 (TVar v2) T2) ->
      closed (length GH) 0 T2' ->
      has_type GH (tapp t1 l (tvar v2)) T2' (S (n1+n2))
  | T_Sub : forall GH t T1 T2 n1 n2,
      has_type GH t T1 n1 ->
      stp GH T1 T2 n2 ->
      has_type GH t T2 (S (n1 + n2))
with dms_has_type: tenv -> dms -> ty -> nat -> Prop :=
  | D_Nil : forall GH n1,
      dms_has_type GH dnil TTop (S n1)
  | D_Mem : forall GH l T11 ds TS T n1,
      dms_has_type GH ds TS n1 ->
      closed (length GH) 0 T11 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TMem l T11 T11) TS ->
      dms_has_type GH (dcons (dty T11) ds) T (S n1)
  | D_Abs : forall GH l T11 T12 T12' t12 ds TS T n1 n2,
      dms_has_type GH ds TS n1 ->
      has_type (T11::GH) t12 T12' n2 ->
      T12' = (open 0 (TVar (VAbs (length GH))) T12) ->
      closed (length GH) 0 T11 ->
      closed (length GH) 1 T12 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TFun l T11 T12) TS ->
      dms_has_type GH (dcons (dfun T11 T12 t12) ds) T (S (n1+n2))

with stp: tenv -> ty -> ty -> nat -> Prop :=
| stp_bot: forall GH T n1,
    closed (length GH) 0  T ->
    stp GH TBot T (S n1)
| stp_top: forall GH T n1,
    closed (length GH) 0 T ->
    stp GH T  TTop (S n1)
| stp_fun: forall GH l T1 T2 T3 T4 T2' T4' n1 n2,
    T2' = (open 0 (TVar (VAbs (length GH))) T2) ->
    T4' = (open 0 (TVar (VAbs (length GH))) T4) ->
    closed (length GH) 1 T2 ->
    closed (length GH) 1 T4 ->
    stp GH T3 T1 n1 ->
    stp (T3::GH) T2' T4' n2 ->
    stp GH (TFun l T1 T2) (TFun l T3 T4) (S (n1+n2))
| stp_mem: forall GH l T1 T2 T3 T4 n1 n2,
    stp GH T3 T1 n2 ->
    stp GH T2 T4 n1 ->
    stp GH (TMem l T1 T2) (TMem l T3 T4) (S (n1+n2))

| stp_varx: forall GH ds n1,
    stp GH (TVar (VObj ds)) (TVar (VObj ds)) (S n1)
| stp_varax: forall GH x n1,
    x < length GH ->
    stp GH (TVar (VAbs x)) (TVar (VAbs x)) (S n1)

| stp_strong_sel1: forall GH l T2 ds TX n1,
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] TX T2 n1 ->
    stp GH (TSel (TVar (VObj ds)) l) T2 (S n1)
| stp_strong_sel2: forall GH l T1 ds TX n1,
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] T1 TX n1 ->
    stp GH T1 (TSel (TVar (VObj ds)) l) (S n1)

| stp_sel1: forall GH l T2 x n1,
    htp  GH x (TMem l TBot T2) n1 ->
    stp GH (TSel (TVar (VAbs x)) l) T2 (S n1)

| stp_sel2: forall GH l T1 x n1,
    htp  GH x (TMem l T1 TTop) n1 ->
    stp GH T1 (TSel (TVar (VAbs x)) l) (S n1)

| stp_selx: forall GH l T1 n1,
    closed (length GH) 0 T1 ->
    stp GH (TSel T1 l) (TSel T1 l) (S n1)

| stp_and11: forall GH T1 T2 T n1,
    stp GH T1 T n1 ->
    closed (length GH) 0 T2 ->
    stp GH (TAnd T1 T2) T (S n1)
| stp_and12: forall GH T1 T2 T n1,
    stp GH T2 T n1 ->
    closed (length GH) 0 T1 ->
    stp GH (TAnd T1 T2) T (S n1)
| stp_and2: forall GH T1 T2 T n1 n2,
    stp GH T T1 n1 ->
    stp GH T T2 n2 ->
    stp GH T (TAnd T1 T2) (S (n1+n2))

| stp_or21: forall GH T1 T2 T n1,
    stp GH T T1 n1 ->
    closed (length GH) 0 T2 ->
    stp GH T (TOr T1 T2) (S n1)
| stp_or22: forall GH T1 T2 T n1,
    stp GH T T2 n1 ->
    closed (length GH) 0 T1 ->
    stp GH T (TOr T1 T2) (S n1)
| stp_or1: forall GH T1 T2 T n1 n2,
    stp GH T1 T n1 ->
    stp GH T2 T n2 ->
    stp GH (TOr T1 T2) T (S (n1+n2))

| stp_trans: forall GH T1 T2 T3 n1 n2,
    stp GH T1 T2 n1 ->
    stp GH T2 T3 n2 ->
    stp GH T1 T3 (S (n1+n2))


with htp: tenv -> id -> ty -> nat -> Prop :=
| htp_var: forall GH x TX n1,
    index x GH = Some TX ->
    closed (S x) 0 TX ->
    htp GH x TX (S n1)
| htp_sub: forall GH GU GL x T1 T2 n1 n2,
    (* use restricted GH. note: this is slightly different
    from the big-step version b/c here we do not distinguish
    if variables are bound in terms vs types. it would be easy
    to do exactly the same thing by adding this distinction. *)
    htp GH x T1 n1 ->
    stp GL T1 T2 n2 ->
    length GL = S x ->
    GH = GU ++ GL ->
    htp GH x T2 (S (n1+n2)).


(* Reduction semantics  *)
Fixpoint stepf (t: tm): option tm :=
  match t with
    | tvar _ => None
    | tobj D => Some (tvar (VObj D))
    | tapp t1 l t2 =>
      match t1 with
        | tvar (VObj f) =>
          match t2 with
            | tvar (VObj x) =>
              match index l (dms_to_list f) with
                | Some (dfun T1 T2 t12) => Some (subst_tm x t12)
                | _ => None
              end
            | _ =>
              match (stepf t2) with
                | Some t2' => Some (tapp t1 l t2')
                | None => None
              end
          end
        | _ =>
          match (stepf t1) with
            | Some t1' => Some (tapp t1' l t2)
            | None => None
          end
      end
  end.

Definition step t t' := stepf t = Some t'.

Lemma ST_Obj : forall D,
    step (tobj D) (tvar (VObj D)).
Proof.
  intros. unfold step. simpl. reflexivity.
Qed.

Lemma ST_AppAbs : forall f l x T1 T2 t12,
    index l (dms_to_list f) = Some (dfun T1 T2 t12) ->
    step (tapp (tvar (VObj f)) l (tvar (VObj x))) (subst_tm x t12).
Proof.
  intros. unfold step. simpl. rewrite H. reflexivity.
Qed.

Lemma inv_step_var : forall t t',
  step t t' -> forall v, t <> tvar v.
Proof.
  intros t t' H. unfold step in H.
  destruct t; simpl in H; inversion H; subst; intros; eauto;
  congruence.
Qed.

Lemma ST_App1 : forall t1 t1' l t2,
  step t1 t1' ->
  step (tapp t1 l t2) (tapp t1' l t2).
Proof.
  intros. unfold step. simpl.
  assert (forall v1, t1 <> tvar v1) as A. {
    eapply inv_step_var. eauto.
  }
  destruct t1.
  - specialize (A v). congruence.
  - unfold step in *. simpl in *. inversion H. subst. reflexivity.
  - unfold step in *. rewrite H. reflexivity.
Qed.

Lemma ST_App2 : forall f t2 l t2',
  step t2 t2' ->
  step (tapp (tvar (VObj f)) l t2) (tapp (tvar (VObj f)) l t2').
Proof.
  intros. unfold step. simpl.
  assert (forall v2, t2 <> tvar v2) as A. {
    eapply inv_step_var. eauto.
  }
  destruct t2.
  - specialize (A v). congruence.
  - unfold step in *. simpl in *. inversion H. subst. reflexivity.
  - unfold step in *. rewrite H. reflexivity.
Qed.

Inductive step_star : tm -> tm -> Prop :=
| s_refl : forall t, step_star t t
| s_step : forall t1 t2 t3, step t1 t2 -> step_star t2 t3 -> step_star t1 t3.

Lemma s_trans : forall t1 t2 t3,
  step_star t1 t2 -> step_star t2 t3 -> step_star t1 t3.
Proof.
  intros t1 t2 t3 H12 H23. generalize dependent t3.
  induction H12; intros; eauto.
  eapply s_step. eapply H. eapply IHstep_star. eapply H23.
Qed.

Lemma s_step1: forall t1 t2,
  step t1 t2 -> step_star t1 t2.
Proof.
  intros. eapply s_step. eassumption. eapply s_refl.
Qed.

Lemma step_star_App1: forall t1 t2 l t1',
  step_star t1 t1' ->
  step_star (tapp t1 l t2) (tapp t1' l t2).
Proof.
  intros. induction H.
  - eapply s_refl.
  - eapply s_step. eapply ST_App1. eassumption. eassumption.
Qed.

Lemma step_star_App2: forall f t2 l t2',
  step_star t2 t2' ->
  step_star (tapp (tvar (VObj f)) l t2) (tapp (tvar (VObj f)) l t2').
Proof.
  intros. induction H.
  - eapply s_refl.
  - eapply s_step. eapply ST_App2. eassumption. eassumption.
Qed.

Lemma step_star_AppAbs: forall f l x r T1 T2 t,
  step_star (subst_tm x t) (tvar (VObj r)) ->
  index l (dms_to_list f) = Some (dfun T1 T2 t) ->
  step_star (tapp (tvar (VObj f)) l (tvar (VObj x))) (tvar (VObj r)).
Proof.
  intros. remember (subst_tm x t) as tr. remember (tvar (VObj r)) as vr.
  induction H; subst.
  - eapply s_step1. eapply ST_AppAbs. eauto.
  - eapply s_step. eapply ST_AppAbs. eauto. eapply s_step. eauto. eauto.
Qed.

Lemma step_star_app: forall f l x r tf tx T1 T2 t,
  step_star tf (tvar (VObj f)) ->
  step_star tx (tvar (VObj x)) ->
  index l (dms_to_list f) = Some (dfun T1 T2 t) ->
  step_star (subst_tm x t) (tvar (VObj r)) ->
  step_star (tapp tf l tx) (tvar (VObj r)).
Proof.
  intros f l x r tf tx T1 T2 t Hf Hx Hl Hr.
  eapply s_trans. eapply s_trans.
  eapply step_star_App1. eapply Hf.
  eapply step_star_App2. eapply Hx.
  eapply step_star_AppAbs. eapply Hr. eapply Hl.
Qed.

Lemma step_star_var: forall v ds,
  step_star (tvar v) (tvar (VObj ds)) ->
  v = VObj ds.
Proof.
  intros. inversion H; subst; eauto; solve by inversion.
Qed.

Definition irreducible t := stepf t = None.
Definition normalizing t t' := step_star t t' /\ irreducible t'.

Lemma irreducible_step_star_refl: forall t t',
  step_star t t' ->
  irreducible t ->
  t = t'.
Proof.
  intros t t' Hs Hi. inversion Hs; subst; eauto.
  unfold irreducible in Hi. unfold step in H. rewrite Hi in H.
  inversion H.
Qed.

Lemma step_unique: forall t t1 t2,
  step t t1 -> step t t2 ->
  t1 = t2.
Proof.
  intros t t1 t2 H1 H2. unfold step in *.
  rewrite H1 in H2. inversion H2. subst.
  reflexivity.
Qed.

Lemma irreducible_step_contra: forall t t',
  step t t' ->
  irreducible t ->
  False.
Proof.
  intros t t' Hs Hi. unfold step in Hs. unfold irreducible in Hi.
  rewrite Hi in Hs. inversion Hs.
Qed.

Lemma normalizing_unique: forall t t1 t2,
  normalizing t t1 -> normalizing t t2 ->
  t1 = t2.
Proof.
  intros t t1 t2 H1 H2. unfold normalizing in *.
  destruct H1 as [Hs1 Hn1]. destruct H2 as [Hs2 Hn2].
  induction Hs1.
  - eapply irreducible_step_star_refl; eauto.
  - specialize (IHHs1 Hn1).
    inversion Hs2; subst.
    + elimtype False. eapply irreducible_step_contra.
      eapply H. eapply Hn2.
    + assert (t0 = t5) as Eq. {
        eapply step_unique; eauto.
      }
      subst. eapply IHHs1; eauto.
Qed.

Inductive vtp(*possible types*) : nat(*pack count*) -> dms -> ty -> nat(*size*) -> Prop :=
| vtp_top: forall m ds n1,
    vtp m ds TTop (S n1)
| vtp_mem: forall m l ds TX T1 T2 n1 n2,
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] T1 TX n1 ->
    stp [] TX T2 n2 ->
    vtp m ds (TMem l T1 T2) (S (n1+n2))
| vtp_fun: forall m l ds T1 T2 T3 T4 T2' T4' t T' n1 n2 n3 n4,
    index l (dms_to_list ds) = Some (dfun T1 T2 t) ->
    dms_has_type [] ds T' n4 ->
    has_type [T1] t T2' n3 ->
    stp [] T3 T1 n1 ->
    T2' = (open 0 (TVar (VAbs 0)) T2) ->
    T4' = (open 0 (TVar (VAbs 0)) T4) ->
    closed 0 1 T2 ->
    closed 0 1 T4 ->
    stp [T3] T2' T4' n2 ->
    (forall dsa na, has_type [] (tvar (VObj dsa)) T1 na ->
                    exists dsr nr, step_star (subst_tm dsa t) (tvar (VObj dsr)) /\
                    has_type [] (tvar (VObj dsr)) (substt dsa T2') nr) ->
    vtp m ds (TFun l T3 T4) (S (n1+n2+n3+n4))
| vtp_sel: forall m ds dsy l TX n1,
    index l (dms_to_list dsy) = Some (dty TX) ->
    vtp m ds TX n1 ->
    vtp m ds (TSel (TVar (VObj dsy)) l) (S (n1))
| vtp_and: forall m m1 m2 ds T1 T2 n1 n2,
    vtp m1 ds T1 n1 ->
    vtp m2 ds T2 n2 ->
    m1 <= m -> m2 <= m ->
    vtp m ds (TAnd T1 T2) (S (n1+n2))
| vtp_or1: forall m m1 m2 ds T1 T2 n1,
    vtp m1 ds T1 n1 ->
    closed 0 0 T2 ->
    m1 <= m -> m2 <= m ->
    vtp m ds (TOr T1 T2) (S (n1))
| vtp_or2: forall m m1 m2 ds T1 T2 n1,
    vtp m1 ds T2 n1 ->
    closed 0 0 T1 ->
    m1 <= m -> m2 <= m ->
    vtp m ds (TOr T1 T2) (S (n1))
.

Definition has_typed GH x T1 := exists n, has_type GH x T1 n.

Definition stpd2 GH T1 T2 := exists n, stp GH T1 T2 n.

Definition htpd GH x T1 := exists n, htp GH x T1 n.

Definition vtpd m x T1 := exists n, vtp m x T1 n.

Definition vtpdd m x T1 := exists m1 n, vtp m1 x T1 n /\ m1 <= m.

Hint Constructors stp.
Hint Constructors vtp.

Ltac ep := match goal with
             | [ |- stp ?GH ?T1 ?T2 ?N ] => assert (exists (n:nat), stp GH T1 T2 n) as EEX
           end.

Ltac eu := match goal with
             | H: has_typed _ _ _ |- _ => destruct H as [? H]
             | H: stpd2 _ _ _ |- _ => destruct H as [? H]
             | H: htpd _ _ _ |- _ => destruct H as [? H]
             | H: vtpd _ _ _ |- _ => destruct H as [? H]
             | H: vtpdd _ _ _ |- _ => destruct H as [? [? [H ?]]]
           end.

Lemma stpd2_bot: forall GH T,
    closed (length GH) 0 T ->
    stpd2 GH TBot T.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_top: forall GH T,
    closed (length GH) 0 T ->
    stpd2 GH T TTop.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_fun: forall GH l T1 T2 T3 T4 T2' T4',
    T2' = (open 0 (TVar (VAbs (length GH))) T2) ->
    T4' = (open 0 (TVar (VAbs (length GH))) T4) ->
    closed (length GH) 1 T2 ->
    closed (length GH) 1 T4 ->
    stpd2 GH T3 T1 ->
    stpd2 (T3::GH) T2' T4' ->
    stpd2 GH (TFun l T1 T2) (TFun l T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.
Lemma stpd2_mem: forall GH l T1 T2 T3 T4,
    stpd2 GH T3 T1 ->
    stpd2 GH T2 T4 ->
    stpd2 GH (TMem l T1 T2) (TMem l T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.



Lemma stpd2_trans: forall GH T1 T2 T3,
    stpd2 GH T1 T2 ->
    stpd2 GH T2 T3 ->
    stpd2 GH T1 T3.
Proof. intros. repeat eu. eexists. eauto. Qed.




Hint Constructors ty.

Hint Constructors stp.
Hint Constructors vtp.
Hint Constructors htp.
Hint Constructors has_type.

Hint Unfold has_typed.
Hint Unfold stpd2.
Hint Unfold vtpd.
Hint Unfold vtpdd.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.


Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.





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

Lemma closed_upgrade_gh: forall i i1 k T1,
  closed i k T1 -> i <= i1 -> closed i1 k T1.
Proof.
  intros. generalize dependent i1. induction H; intros; econstructor; eauto. omega.
Qed.

Lemma closed_upgrade: forall i k k1 T1,
  closed i k T1 -> k <= k1 -> closed i k1 T1.
Proof.
  intros. generalize dependent k1. induction H; intros; econstructor; eauto.
  eapply IHclosed2. omega.
  omega.
Qed.

Lemma closed_open: forall j k v T, closed k (j+1) T -> closed k j (TVar v) -> closed k j (open j (TVar v) T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H; try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - eapply closed_upgrade; eauto.
  - Case "TVarB". simpl.
    case_eq (beq_nat j i); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
Qed.

Lemma all_closed: forall ni,
  (forall GH T1 T2 n,
     stp GH T1 T2 n -> n < ni ->
     closed (length GH) 0 T1) /\
  (forall GH T1 T2 n,
     stp GH T1 T2 n -> n < ni ->
     closed (length GH) 0 T2) /\
  (forall m x T2 n,
     vtp m x T2 n -> n < ni ->
     closed 0 0 T2) /\
  (forall x GH T2 n,
     htp GH x T2 n -> n < ni ->
     x < length GH) /\
  (forall x GH T2 n,
     htp GH x T2 n -> n < ni ->
     closed (length GH) 0 T2) /\
  (forall GH t T n,
     has_type GH t T n -> n < ni ->
     closed (length GH) 0 T) /\
  (forall GH ds T n,
     dms_has_type GH ds T n -> n < ni ->
     closed (length GH) 0 T).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H; destruct IHn as [IHS1 [IHS2 [IHV2 [IHH1 [IHH2 [IHT IHD]]]]]].
  (* stp left *)
  - econstructor.
  - eauto.
  - econstructor. eapply IHS2. eauto. omega. eauto.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS1. eauto. omega.
  - econstructor.
  - econstructor. eauto.
  - econstructor. econstructor.
  - eapply closed_upgrade_gh. eapply IHS1. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
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
  - econstructor.
  - econstructor. eauto.
  - eapply closed_upgrade_gh. eapply IHS2. eauto. omega. simpl. omega.
  - econstructor. econstructor.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - econstructor. eauto.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS2. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eauto.
  - econstructor. eauto. eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  (* vtp right *)
  - econstructor.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. econstructor.
  - econstructor. eapply IHV2. eauto. omega. eapply IHV2. eauto. omega.
  - econstructor. eapply IHV2. eauto. omega. eauto.
  - econstructor. eauto. eapply IHV2. eauto. omega.
  (* htp left *)
  - eapply index_max. eauto.
  - eapply IHH1. eauto. omega.
  (* htp right *)
  - eapply closed_upgrade_gh. eauto. subst. eapply index_max in H1. omega.
  - eapply closed_upgrade_gh. eapply IHS2. eauto. omega. rewrite H4. rewrite app_length. omega.
  (* has_type *)
  - eapply IHD in H1. subst. eapply closed_upgrade_gh. eauto. simpl. omega. omega.
  - eauto.
  - eapply IHD in H1. eauto. omega.
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHS2. eauto. omega.
  (* dms_has_type *)
  - econstructor.
  - subst. econstructor. econstructor. eauto. eauto. eapply IHD. eauto. omega.
  - subst. econstructor. econstructor. eauto. eauto. eapply IHD. eauto. omega.
Qed.

Lemma htp_closed: forall x GH T2 n,
  htp GH x T2 n ->
  closed (length GH) 0 T2.
Proof. intros. eapply all_closed with (x:=x). eauto. eauto. Qed.

Lemma vtp_closed: forall m x T2 n1,
  vtp m x T2 n1 ->
  closed 0 0 T2.
Proof. intros. eapply all_closed. eauto. eauto. Qed.

Lemma has_type_closed: forall GH t T n1,
  has_type GH t T n1 ->
  closed (length GH) 0 T.
Proof. intros. eapply all_closed with (t:=t). eauto. eauto. Qed.

Lemma dms_has_type_closed: forall GH t T n1,
  dms_has_type GH t T n1 ->
  closed (length GH) 0 T.
Proof. intros. eapply all_closed with (ds:=t). eauto. eauto. Qed.

Lemma has_type_closed_z: forall GH z T n1,
  has_type GH (tvar (VAbs z)) T n1 ->
  z < length GH.
Proof.
  intros. remember (tvar (VAbs z)) as t. generalize dependent z.
  induction H; intros; inversion Heqt; subst; eauto using index_max.
Qed.

Lemma has_type_closed_b: forall v T n1,
  has_type [] (tvar v) T n1 ->
  exists ds, v = VObj ds.
 Proof.
 intros.
 remember [] as GH.
 remember (tvar v) as t.
 generalize HeqGH. clear HeqGH.
 induction H; intros; inversion Heqt; subst; eauto using index_max.
 - simpl in H. inversion H.
Qed.

Lemma stp_closed1 : forall GH T1 T2 n1,
                      stp GH T1 T2 n1 ->
                      closed (length GH) 0 T1.
Proof. intros. edestruct all_closed. eapply H0. eauto. eauto. Qed.

Lemma stp_closed2 : forall GH T1 T2 n1,
                      stp GH T1 T2 n1 ->
                      closed (length GH) 0 T2.
Proof. intros. edestruct all_closed. destruct H1. eapply H1. eauto. eauto. Qed.

Lemma stpd2_closed1 : forall GH T1 T2,
                      stpd2 GH T1 T2 ->
                      closed (length GH) 0 T1.
Proof. intros. eu. eapply stp_closed1. eauto. Qed.


Lemma stpd2_closed2 : forall GH T1 T2,
                      stpd2 GH T1 T2 ->
                      closed (length GH) 0 T2.
Proof. intros. eu. eapply stp_closed2. eauto. Qed.


Lemma beq_nat_true_eq: forall A, beq_nat A A = true.
Proof. intros. eapply beq_nat_true_iff. eauto. Qed.


Fixpoint tsize (T: ty) { struct T }: nat :=
  match T with
    | TVar _ => 1
    | TVarB x => 1
    | TTop        => 1
    | TBot        => 1
    | TSel T1 l   => S (tsize T1)
    | TFun l T1 T2 => S (tsize T1 + tsize T2)
    | TMem l T1 T2 => S (tsize T1 + tsize T2)
    | TAnd T1 T2  => S (tsize T1 + tsize T2)
    | TOr T1 T2   => S (tsize T1 + tsize T2)
  end.

Lemma open_preserves_size: forall T v j,
  tsize T = tsize (open j (TVar v) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  - destruct (beq_nat j i); eauto.
Qed.

Lemma stpd2_refl_aux: forall n GH T1,
  closed (length GH) 0 T1 ->
  tsize T1 < n ->
  stpd2 GH T1 T1.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst; simpl in H0.
  - Case "bot". exists 1. eauto.
  - Case "top". exists 1. eauto.
  - Case "fun". eapply stpd2_fun; eauto.
    eapply IHn; eauto; omega.
    eapply IHn; eauto.
    simpl. apply closed_open. simpl. eapply closed_upgrade_gh. eauto. omega.
    econstructor. omega.
    rewrite <- open_preserves_size. omega.
  - Case "mem". eapply stpd2_mem; try eapply IHn; eauto; try omega.
  - Case "var0". exists 1. eauto.
  - Case "var1". exists 1. eauto.
  - Case "varb". omega.
  - Case "sel". exists 1. eapply stp_selx. eauto.
  - Case "and".
    destruct (IHn GH T0 H1). omega.
    destruct (IHn GH T2 H2). omega.
    eexists. eapply stp_and2. eapply stp_and11. eauto. eauto. eapply stp_and12. eauto. eauto.
  - Case "or".
    destruct (IHn GH T0 H1). omega.
    destruct (IHn GH T2 H2). omega.
    eexists. eapply stp_or1. eapply stp_or21. eauto. eauto. eapply stp_or22. eauto. eauto.
Qed.

Lemma stpd2_refl: forall GH T1,
  closed (length GH) 0 T1 ->
  stpd2 GH T1 T1.
Proof.
  intros. apply stpd2_refl_aux with (n:=S (tsize T1)); eauto.
Qed.

Lemma stpd2_reg1 : forall GH T1 T2,
                      stpd2 GH T1 T2 ->
                      stpd2 GH T1 T1.
Proof. intros. eapply stpd2_refl. eapply stpd2_closed1. eauto. Qed.

Lemma stpd2_reg2 : forall GH T1 T2,
                      stpd2 GH T1 T2 ->
                      stpd2 GH T2 T2.
Proof. intros. eapply stpd2_refl. eapply stpd2_closed2. eauto. Qed.



Ltac index_subst := match goal with
                      | H1: index ?x ?G = ?V1 , H2: index ?x ?G = ?V2 |- _ => rewrite H1 in H2; inversion H2; subst
                      | _ => idtac
                    end.

Ltac invty := match goal with
                | H1: TBot     = _ |- _ => inversion H1
                | H1: TSel _ _   = _ |- _ => inversion H1
                | H1: TMem _ _ _ = _ |- _ => inversion H1
                | H1: TVar _ = _ |- _ => inversion H1
                | H1: TFun _ _ _ = _ |- _ => inversion H1
                | H1: TAnd _ _ = _ |- _ => inversion H1
                | H1: TOr _ _ = _ |- _ => inversion H1
                | _ => idtac
              end.

Ltac invstp_var := match goal with
  | H1: stp _ true _ _ TBot        (TVar _ ) _ |- _ => inversion H1
  | H1: stp _ true _ _ TTop        (TVar _ ) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TFun _ _ _)  (TVar _) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TMem _ _ _)  (TVar _) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TAnd _ _)  (TVar _ ) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TOr _ _)  (TVar _) _ |- _ => inversion H1
  | _ => idtac
end.

Lemma closed_no_open: forall T x l j,
  closed l j T ->
  T = open j (TVar (VAbs x)) T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed; rewrite <-IHclosed; auto];
  try solve [compute; compute in IHclosed1; compute in IHclosed2; rewrite <-IHclosed1; rewrite <-IHclosed2; auto].

  Case "TSelB".
    simpl.
    assert (k <> x0). omega.
    apply beq_nat_false_iff in H0.
    rewrite H0. auto.
Qed.


Lemma closed_no_subst: forall T k TX,
   closed 0 k T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
    try rewrite (IHT (S k) TX); eauto;
    try rewrite (IHT k TX); eauto;
    try rewrite (IHT1 k TX); eauto; subst.

  rewrite (IHT2 (S k) TX); eauto.
  rewrite (IHT2 k TX); eauto.
  omega.
  eapply closed_upgrade; eauto.
  rewrite (IHT2 k TX); eauto.
  rewrite (IHT2 k TX); eauto.
Qed.

Lemma closed_subst: forall j n V T, closed (n+1) j T -> closed n 0 V -> closed n j (subst V T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H; try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - Case "TSelH". simpl.
    case_eq (beq_nat x 0); intros E. eapply closed_upgrade. eapply closed_upgrade_gh. eauto. omega. omega. econstructor. subst.
    assert (x > 0). eapply beq_nat_false_iff in E. omega. omega.
Qed.

Lemma subst_open_commute0: forall T0 j TX,
  closed 0 (j+1) T0 ->
  (subst TX (open j (TVar (VAbs 0)) T0)) = open j TX T0.
Proof.
  intros T0. induction T0; intros.
  eauto. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. inversion H. omega. eauto.
  simpl. inversion H. subst. destruct i. case_eq (beq_nat j 0); intros E; simpl; eauto.
  case_eq (beq_nat j (S i)); intros E; simpl; eauto.

  simpl. inversion H. rewrite IHT0. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
Qed.


Lemma subst_open_commute1: forall T0 x x0 j,
 (open j (TVar (VObj x0)) (subst (TVar (VObj x)) T0))
 = (subst (TVar (VObj x)) (open j (TVar (VObj x0)) T0)).
Proof.
  induction T0; intros.
  eauto. eauto. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. destruct v; eauto.
  case_eq (beq_nat i 0); intros E. simpl. eauto. simpl. eauto.

  simpl. case_eq (beq_nat j i); intros E. simpl. eauto. simpl. eauto.

  simpl. rewrite IHT0. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto.
Qed.


Lemma subst_closed_id: forall x k T2,
  closed 0 k T2 ->
  substt x T2 = T2.
Proof. intros. eapply closed_no_subst. eauto. Qed.

Lemma closed_subst0: forall i k x T2,
  closed (i + 1) k T2 ->
  closed i k (substt x T2).
Proof. intros. eapply closed_subst. eauto. econstructor. Qed.

Lemma closed_subst1: forall i k x T2,
  closed i k T2 -> i <> 0 ->
  closed (i-1) k (substt x T2).
Proof.
  intros. eapply closed_subst.
  assert ((i - 1 + 1) = i) as R. omega.
  rewrite R. eauto. econstructor.
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
  (substt x (open j (TVar (VAbs (n+1))) TX)) =
  (open j (TVar (VAbs n)) (substt x TX)).
Proof.
  intros TX. induction TX; intros; eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
  - unfold substt. simpl. destruct v; eauto.
    case_eq (beq_nat i 0); intros E. eauto. eauto.
  - unfold substt. simpl.
    case_eq (beq_nat j i); intros E. simpl.
    assert (beq_nat (n + 1) 0 = false). eapply beq_nat_false_iff. omega.
    assert ((n + 1 - 1 = n)). omega.
    rewrite H. rewrite H0. eauto. eauto.
  - unfold substt. simpl. unfold substt in IHTX. erewrite <-IHTX. eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
Qed.

Lemma subst_open3: forall TX0 (GH:tenv) TX  x,
  (substt x (open 0 (TVar (VAbs (length (GH ++ [TX])))) TX0)) =
  (open 0 (TVar (VAbs (length GH))) (substt x TX0)).
Proof. intros. rewrite app_length. simpl. eapply subst_open. Qed.

Lemma subst_open4: forall T0 (GH:tenv) TX x,
  substt x (open 0 (TVar (VAbs (length (GH ++ [TX])))) T0) =
  open 0 (TVar (VAbs (length (map (substt x) GH)))) (substt x T0).
Proof. intros. rewrite map_length. eapply subst_open3. Qed.

Lemma subst_open5: forall (GH:tenv) T0 x xi,
  xi <> 0 -> substt x (open 0 (TVar (VAbs xi)) T0) =
  open 0 (TVar (VAbs (xi-1))) (substt x T0).
Proof.
  intros. remember (xi-1) as n. assert (xi=n+1) as R. omega. rewrite R.
  eapply subst_open.
Qed.

Lemma subst_open_commute0b: forall x T1 n,
  substt x (open n (TVar (VAbs 0)) T1) = open n (TVar (VObj x)) (substt x T1).
Proof.
  unfold substt.
  intros x T1.
  induction T1; intros n; simpl;
  try rewrite IHT1; try rewrite IHT1_1; try rewrite IHT1_2;
  eauto.
  destruct v; eauto.
  case_eq (beq_nat i 0); intros; simpl; eauto.
  case_eq (beq_nat n i); intros; simpl; eauto.
Qed.

Lemma subst_open_commute_z: forall x T1 z n,
 subst (TVar (VObj x)) (open n (TVar (VAbs (z + 1))) T1) =
 open n (TVar (VAbs z)) (subst (TVar (VObj x)) T1).
Proof.
  intros x T1 z.
  induction T1; intros n; simpl;
  try rewrite IHT1; try rewrite IHT1_1; try rewrite IHT1_2;
  eauto.
  destruct v; eauto.
  case_eq (beq_nat i 0); intros; simpl; eauto.
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

Lemma stp_subst_narrow0: forall n, forall GH T1 T2 TX x n2,
   stp (GH++[TX]) T1 T2 n2 -> n2 < n ->
   (forall GH (T3 : ty) (n1 : nat),
      htp (GH++[TX]) 0 T3 n1 -> n1 < n ->
      exists m2, vtpd m2 x (substt x T3)) ->
   stpd2 (map (substt x) GH) (substt x T1) (substt x T2).
Proof.
  intros n. induction n. intros. omega.
  intros ? ? ? ? ? ? ? ? narrowX.

  (* helper lemma for htp *)
  assert (forall ni n2, forall GH T2 xi,
    htp (GH ++ [TX]) xi T2 n2 -> xi <> 0 -> n2 < ni -> ni < S n ->
    htpd (map (substt x) GH) (xi-1) (substt x T2)) as htp_subst_narrow02. {
      induction ni. intros. omega.
      intros. inversion H1.
      + (* var *) subst.
        repeat eexists. eapply htp_var. eapply index_subst1. eauto. eauto.
        eapply closed_subst0. eapply closed_upgrade_gh. eauto. omega.
      + (* sub *) subst.
        assert (exists GL0, GL = GL0 ++ [TX] /\ GH0 = GU ++ GL0) as A. eapply gh_match1. eauto. omega.
        destruct A as [GL0 [? ?]]. subst GL.
        assert (htpd (map (substt x) GH0) (xi-1) (substt x T3)) as AA.
        eapply IHni. eauto. eauto. omega. omega.
        assert (stpd2 (map (substt x) GL0) (substt x T3) (substt x T0)) as BB.
        eapply IHn. eauto. eauto. omega. { intros. eapply narrowX. eauto. eauto. }
        eu. eu. repeat eexists. eapply htp_sub. eauto. eauto.
        (* - *)
        rewrite map_length. rewrite app_length in H7. simpl in H7. unfold id in *. omega.
        subst GH0. rewrite map_app. eauto.
  }
  (* special case *)
  assert (forall ni n2, forall T0 T2,
    htp (T0 :: GH ++ [TX]) (length (GH ++ [TX])) T2 n2 -> n2 < ni -> ni < S n ->
    htpd (map (substt x) (T0::GH)) (length GH) (substt x T2)) as htp_subst_narrow0. {
      intros.
      rewrite app_comm_cons in H1.
      remember (T0::GH) as GH1. remember (length (GH ++ [TX])) as xi.
      rewrite app_length in Heqxi. simpl in Heqxi.
      assert (length GH = xi-1) as R. omega.
      rewrite R. eapply htp_subst_narrow02. eauto. omega. eauto. eauto.
  }


  (* main logic *)
  inversion H.
  - Case "bot". subst.
    eapply stpd2_bot; eauto. rewrite map_length. simpl. eapply closed_subst0. rewrite app_length in H1. simpl in H1. eapply H1.
  - Case "top". subst.
    eapply stpd2_top; eauto. rewrite map_length. simpl. eapply closed_subst0. rewrite app_length in H1. simpl in H1. eapply H1.
  - Case "fun". subst.
    eapply stpd2_fun. eauto. eauto.
    rewrite map_length. eapply closed_subst0. rewrite app_length in *. simpl in *. eauto.
    rewrite map_length. eapply closed_subst0. rewrite app_length in *. simpl in *. eauto.
    eapply IHn; eauto. omega.
    rewrite <- subst_open_commute_z. rewrite <- subst_open_commute_z.
    specialize (IHn (T4::GH)). simpl in IHn.
    unfold substt in IHn at 2.  unfold substt in IHn at 3. unfold substt in IHn at 3.
    simpl in IHn. eapply IHn.
    rewrite map_length. rewrite app_length in *. eassumption.
    omega. eauto.
  - Case "mem". subst.
    eapply stpd2_mem. eapply IHn; eauto. omega. eapply IHn; eauto. omega.


  - Case "varx". subst.
    eexists. eapply stp_varx.
  - Case "varax". subst.
    case_eq (beq_nat x0 0); intros E.
    + (* hit *)
      assert (x0 = 0). eapply beq_nat_true_iff. eauto.
      repeat eexists. unfold substt. subst x0. simpl. eapply stp_varx.
    + (* miss *)
      assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      repeat eexists. unfold substt. simpl. rewrite E. eapply stp_varax. rewrite map_length. rewrite app_length in H1. simpl in H1. omega.
  - Case "ssel1". subst.
    assert (substt x T2 = T2) as R. eapply subst_closed_id. eapply stpd2_closed2 with (GH:=[]). eauto.
    eexists. eapply stp_strong_sel1. eauto. rewrite R. eauto.

  - Case "ssel2". subst.
    assert (substt x T1 = T1) as R. eapply subst_closed_id. eapply stpd2_closed1 with (GH:=[]). eauto.
    eexists. eapply stp_strong_sel2. eauto. rewrite R. eauto.

  - Case "sel1". subst. (* invert htp to vtp and create strong_sel node *)
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0.
      assert (exists m0, vtpd m0 x (substt x (TMem l TBot T2))) as A. eapply narrowX. eauto. omega.
      destruct A as [? A]. eu. inversion A. subst.
      repeat eexists. eapply stp_strong_sel1. eauto. eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      eapply htp_subst_narrow02 in H1.
      eu. repeat eexists. unfold substt. simpl. rewrite E. eapply stp_sel1. eapply H1. eauto. eauto. eauto.

  - Case "sel2". subst. (* invert htp to vtp and create strong_sel node *)
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0.
      assert (exists m0, vtpd m0 x (substt x (TMem l T1 TTop))) as A. eapply narrowX. eauto. omega.
      destruct A as [? A]. eu. inversion A. subst.
      repeat eexists. eapply stp_strong_sel2. eauto. eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      eapply htp_subst_narrow02 in H1.
      eu. repeat eexists. unfold substt. simpl. rewrite E. eapply stp_sel2. eapply H1. eauto. eauto. eauto.
  - Case "selx".
    eexists. eapply stp_selx. eapply closed_subst0. rewrite app_length in H1. simpl in H1. rewrite map_length. eauto.

  - Case "and11".
    assert (stpd2 (map (substt x) GH) (substt x T0) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_and11. eauto. eapply closed_subst0. rewrite app_length in H2. rewrite map_length. eauto.
  - Case "and12".
    assert (stpd2 (map (substt x) GH) (substt x T3) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_and12. eauto. eapply closed_subst0. rewrite app_length in H2. rewrite map_length. eauto.
  - Case "and2".
    assert (stpd2 (map (substt x) GH) (substt x T1) (substt x T0)). eapply IHn. eauto. eauto. omega. eauto.
    assert (stpd2 (map (substt x) GH) (substt x T1) (substt x T3)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eu. eexists. eapply stp_and2. eauto. eauto.

  - Case "or21".
    assert (stpd2 (map (substt x) GH) (substt x T1) (substt x T0)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_or21. eauto. eapply closed_subst0. rewrite app_length in H2. rewrite map_length. eauto.
  - Case "or22".
    assert (stpd2 (map (substt x) GH) (substt x T1) (substt x T3)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_or22. eauto. eapply closed_subst0. rewrite app_length in H2. rewrite map_length. eauto.
  - Case "or1".
    assert (stpd2 (map (substt x) GH) (substt x T0) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    assert (stpd2 (map (substt x) GH) (substt x T3) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eu. eexists. eapply stp_or1. eauto. eauto.

  - Case "trans".
    assert (stpd2 (map (substt x) GH) (substt x T1) (substt x T3)).
    eapply IHn; eauto. omega.
    assert (stpd2 (map (substt x) GH) (substt x T3) (substt x T2)).
    eapply IHn; eauto. omega.
    eu. eu. repeat eexists. eapply stp_trans. eauto. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


Lemma stp_subst_narrowX: forall ml, forall nl, forall m GH T2 TX x n1 n2,
   vtp m x (substt x TX) n1 ->
   htp (GH++[TX]) 0 T2 n2 -> m < ml -> n2 < nl ->
   (forall (m0 : nat) x (T2 T3 : ty) (n1 n2 : nat),
        vtp m0 x T2 n1 ->
        stp [] T2 T3 n2 -> m0 <= m ->
        vtpdd m0 x T3) ->
   vtpdd m x (substt x T2). (* decrease b/c transitivity *)
Proof.
  intros ml. (* induction ml. intros. omega. *)
  intros nl. induction nl. intros. omega.
  intros.
  inversion H0.
  - Case "var". subst.
    assert (T2 = TX). eapply index_hit0. eauto.
    subst T2.
    repeat eexists. eauto. eauto.
  - Case "sub". subst.
    destruct GL.

    assert (vtpdd m x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    eu.
    assert (stpd2 [] (substt x T1) (substt x T2)) as B.
    erewrite subst_closed_id. erewrite subst_closed_id. eexists. eassumption.
    eapply stp_closed2 in H5. simpl in H5. eapply H5.
    eapply stp_closed1 in H5. simpl in H5. eapply H5.
    simpl in B. eu.
    assert (vtpdd x0 x (substt x T2)).
    eapply H3. eauto. eauto. eauto.
    eu. repeat eexists. eauto. omega.

    assert (length GL = 0) as LenGL. simpl in *. omega.
    assert (GL = []). destruct GL. reflexivity. simpl in LenGL. inversion LenGL.
    subst GL.
    assert (TX = t). eapply proj2. apply app_inj_tail. eassumption.
    subst t.
    assert (vtpdd m x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    eu.
    assert (stpd2 (map (substt x) []) (substt x T1) (substt x T2)) as B.
    eapply stp_subst_narrow0. eauto. eauto. eauto. {
      intros. eapply IHnl in H. eu. repeat eexists. eauto. eauto. eauto. eauto. omega. eauto.
    }
    simpl in B. eu.
    assert (vtpdd x0 x (substt x T2)).
    eapply H3. eauto. eauto. eauto.
    eu. repeat eexists. eauto. omega.
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

(* upgrade_gh interlude begin *)

(* splicing -- for stp_extend. *)

Definition splice_var n i := if le_lt_dec n i then (i+1) else i.
Hint Unfold splice_var.

Fixpoint splice n (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TMem l T1 T2 => TMem l (splice n T1) (splice n T2)
    | TSel T1 l    => TSel (splice n T1) l
    | TVarB i      => TVarB i
    | TVar (VObj ds)  => TVar (VObj ds)
    | TVar (VAbs i) => TVar (VAbs (splice_var n i))
    | TFun l T1 T2 => TFun l (splice n T1) (splice n T2)
    | TAnd T1 T2   => TAnd (splice n T1) (splice n T2)
    | TOr T1 T2    => TOr (splice n T1) (splice n T2)
  end.

Lemma splice_open_permute: forall {X} (G0:list X) T2 n j,
(open j (TVar (VAbs (n + S (length G0)))) (splice (length G0) T2)) =
(splice (length G0) (open j (TVar (VAbs (n + length G0))) T2)).
Proof.
  intros X G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto.
  destruct v; eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  unfold splice_var.
  case_eq (le_lt_dec (length G) (n + length G)); intros EL LE.
  assert (n + S (length G) = n + length G + 1). omega.
  rewrite H. eauto.
  omega.
Qed.

Lemma splice_open_permute0: forall {X} (G0:list X) T2 j,
(open j (TVar (VAbs (S (length G0)))) (splice (length G0) T2)) =
(splice (length G0) (open j (TVar (VAbs (length G0))) T2)).
Proof.
  intros.
  change (TVar (VAbs (length G0))) with (TVar (VAbs (0 + (length G0)))).
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

Lemma closed_splice: forall i k T n,
  closed i k T ->
  closed (S i) k (splice n T).
Proof.
  intros.
  Hint Constructors closed.
  induction H; simpl; eauto.
  unfold splice_var.
  case_eq (le_lt_dec n x); intros E LE;
  econstructor; omega.
Qed.

Lemma map_splice_length_inc: forall G0 G2 v1,
   (length (map (splice (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_inc_mult: forall i k T,
  closed i k T ->
  forall i' k',
  i' >= i -> k' >= k ->
  closed i' k' T.
Proof.
  intros i k T H. induction H; intros; eauto; try solve [constructor; omega].
  - econstructor. apply IHclosed1; omega. apply IHclosed2; omega.
Qed.

Lemma closed_inc: forall i k T,
  closed i k T ->
  closed (S i) k T.
Proof.
  intros. apply (closed_inc_mult i k T H (S i) k); omega.
Qed.

Lemma closed_splice_idem: forall i k T n,
                            closed i k T ->
                            n >= i ->
                            splice n T = T.
Proof.
  intros. induction H; eauto;
  simpl; try rewrite IHclosed; try rewrite IHclosed1; try rewrite IHclosed2; eauto.
  unfold splice_var.
  case_eq (le_lt_dec n x); intros E LE.
  omega. reflexivity.
Qed.

Lemma stp_splice_aux: forall ni, (forall G0 G1 T1 T2 v1 n,
   stp (G1++G0) T1 T2 n -> n < ni ->
   stp ((map (splice (length G0)) G1) ++ v1::G0)
   (splice (length G0) T1) (splice (length G0) T2) n) /\
  (forall G0 G1 x1 T1 v1 n,
   htp (G1++G0) x1 T1 n -> n < ni ->
   htp ((map (splice (length G0)) G1) ++ v1::G0)
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
    specialize (IHstp G0 (T4::G1)).
    simpl in IHstp. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    eapply IHstp. rewrite <- app_length. eauto. omega.
  - Case "mem".
    eapply stp_mem.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "varx".
    simpl. eapply stp_varx.
  - Case "varax". simpl.
    unfold splice_var.
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_varax.
      rewrite map_splice_length_inc. omega.
    + eapply stp_varax.
      rewrite map_splice_length_inc. omega.
  - Case "ssel1".
    eapply stp_strong_sel1. eauto. eauto.
    assert (splice (length G0) T2=T2) as A. {
      eapply closed_splice_idem. eapply stp_closed2. eapply H2. simpl. omega.
    }
    rewrite A. assumption.
  - Case "ssel2".
    eapply stp_strong_sel2. eauto. eauto.
    assert (splice (length G0) T1=T1) as A. {
      eapply closed_splice_idem. eapply stp_closed1. eapply H2. simpl. omega.
    }
    rewrite A. assumption.
  - Case "sel1".
    eapply stp_sel1.
    specialize (IHhtp G0 G1 x (TMem l TBot T2)). simpl in IHhtp.
    eapply IHhtp. eauto. omega.
  - Case "sel2".
    eapply stp_sel2.
    specialize (IHhtp G0 G1 x (TMem l T1 TTop)). simpl in IHhtp.
    eapply IHhtp. eauto. omega.
  - Case "selx".
    eapply stp_selx.
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

Lemma stp_splice: forall G0 G1 T1 T2 v1 n,
   stp (G1++G0) T1 T2 n ->
   stp ((map (splice (length G0)) G1) ++ v1::G0)
   (splice (length G0) T1) (splice (length G0) T2) n.
Proof. intros. eapply stp_splice_aux. eauto. eauto. Qed.

Lemma htp_splice: forall G0 G1 x1 T1 v1 n,
   htp (G1++G0) x1 T1 n ->
   htp ((map (splice (length G0)) G1) ++ v1::G0)
   (splice_var (length G0) x1) (splice (length G0) T1) n.
Proof. intros. eapply stp_splice_aux. eauto. eauto. Qed.

Lemma stp_upgrade_gh_aux: forall ni,
  (forall GH T T1 T2 n,
     stp GH T1 T2 n -> n < ni ->
     stp (T::GH) T1 T2 n) /\
  (forall T x GH T2 n,
     htp GH x T2 n -> n < ni ->
     htp (T::GH) x T2 n).
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
  - econstructor.
  - econstructor. simpl. omega.
  - econstructor. eauto. eauto.
  - econstructor. eauto. eauto.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_and11. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_and12. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_and2. eapply IHn. eauto. omega. eapply IHn. eauto. omega.

  - eapply stp_or21. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_or22. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_or1. eapply IHn. eauto. omega. eapply IHn. eauto. omega.

  - eapply stp_trans. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  (* htp *)
  - econstructor. eapply index_extend. eauto. eapply closed_upgrade_gh. eauto. omega.
  - eapply htp_sub. eapply IHn. eauto. omega. eauto. eauto. subst GH.
    instantiate (1:=T::GU). eauto.
Qed.

Lemma stp_upgrade_gh : forall GH T T1 T2 n,
                      stp GH T1 T2 n ->
                      stp (T::GH) T1 T2 n.
Proof. intros. eapply stp_upgrade_gh_aux. eauto. eauto. Qed.

Lemma stp_upgrade_gh_mult : forall GH GH' T1 T2 n,
                      stp GH T1 T2 n ->
                      stp (GH'++GH) T1 T2 n.
Proof. intros. induction GH'. simpl. eauto. simpl. eapply stp_upgrade_gh. eauto. Qed.

Lemma stp_upgrade_gh_mult0 : forall GH T1 T2 n,
                      stp [] T1 T2 n ->
                      stp GH T1 T2 n.
Proof. intros. rewrite <- (app_nil_r GH). eapply stp_upgrade_gh_mult. eauto. Qed.

Lemma hastp_upgrade_gh_var: forall GH x T n1,
  has_type [] (tvar (VObj x)) T n1 ->
  has_type GH (tvar (VObj x)) T n1.
Proof.
  intros.
  remember (tvar (VObj x)) as t.  remember [] as GH0.
  induction H; eauto; inversion Heqt; subst.
  - eapply T_Sub. eauto. eapply stp_upgrade_gh_mult0. eauto.
Qed.

Lemma hastp_upgrade_gh: forall GH x T n1,
  has_type [] (tvar (VObj x)) T n1 ->
  exists n, has_type GH (tvar (VObj x)) T n.
Proof.
  intros. exists n1.
  induction GH. simpl. eauto. simpl. eapply hastp_upgrade_gh_var. eauto.
Qed.

(* upgrade_gh interlude ends *)

Lemma stp_narrow_aux: forall n,
  (forall GH x T n0,
  htp GH x T n0 -> n0 <= n ->
  forall GH1 GH0 GH' TX1 TX2,
    GH=GH1++[TX2]++GH0 ->
    GH'=GH1++[TX1]++GH0 ->
    stpd2 GH0 TX1 TX2 ->
    htpd GH' x T) /\
  (forall GH T1 T2 n0,
  stp GH T1 T2 n0 -> n0 <= n ->
  forall GH1 GH0 GH' TX1 TX2,
    GH=GH1++[TX2]++GH0 ->
    GH'=GH1++[TX1]++GH0 ->
    stpd2 GH0 TX1 TX2 ->
    stpd2 GH' T1 T2).
Proof.
  intros n.
  induction n.
  - Case "z". split; intros; inversion H0; subst; inversion H; eauto.
  - Case "s n". destruct IHn as [IHn_htp IHn_stp].
    split.
    {
    intros GH x T n0 H NE. inversion H; subst;
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
        eapply stp_closed1 in HX. eapply closed_upgrade_gh.
        eapply HX. apply beq_nat_true in E. subst. omega.
        eapply stp_upgrade_gh. eauto. simpl.
        f_equal. apply beq_nat_true in E. subst. reflexivity.
        simpl. reflexivity.
      * assert (index x GH' = Some T) as A. {
          subst.
          eapply index_same. apply E. eassumption.
        }
        eexists. eapply htp_var. eapply A.
        subst. eauto.
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

    intros GH T1 T2 n0 H NE. inversion H; subst;
    intros GH1 GH0 GH' TX1 TX2 EGH EGH' HX;
    assert (length GH' = length GH) as EGHLEN by solve [
      subst; repeat rewrite app_length; simpl; reflexivity
    ].
    + SCase "bot". eapply stpd2_bot. rewrite EGHLEN; assumption.
    + SCase "top". eapply stpd2_top. rewrite EGHLEN; assumption.
    + SCase "fun". eapply stpd2_fun.
      reflexivity. reflexivity.
      rewrite EGHLEN; assumption. rewrite EGHLEN; assumption.
      eapply IHn_stp; try eassumption. omega.
      eapply IHn_stp with (GH1:=(T4::GH1)); try eassumption.
      rewrite EGHLEN. eauto. omega.
      subst. simpl. reflexivity. subst. simpl. reflexivity.
    + SCase "mem". eapply stpd2_mem.
      eapply IHn_stp; try eassumption. omega.
      eapply IHn_stp; try eassumption. omega.
    + SCase "varx". eexists. eapply stp_varx.
    + SCase "varax". eexists. eapply stp_varax.
      subst. rewrite app_length in *. simpl in *. omega.
    + SCase "ssel1". eexists. eapply stp_strong_sel1; try eassumption.
    + SCase "ssel2". eexists. eapply stp_strong_sel2; try eassumption.
    + SCase "sel1".
      edestruct IHn_htp as [? Htp]; eauto. omega.
    + SCase "sel2".
      edestruct IHn_htp as [? Htp]; eauto. omega.
    + SCase "selx".
      eexists. eapply stp_selx.
      subst. rewrite app_length in *. simpl in *. assumption.
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
apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stp_narrow: forall TX1 TX2 GH0 T1 T2 n nx,
  stp ([TX2]++GH0) T1 T2 n ->
  stp GH0 TX1 TX2 nx ->
  stpd2 ([TX1]++GH0) T1 T2.
Proof.
  intros. eapply stp_narrow_aux. eapply H. reflexivity.
  instantiate(3:=nil). simpl. reflexivity. simpl. reflexivity.
  eauto.
Qed.

(* possible types closure *)
Lemma vtp_widen: forall l, forall n, forall k, forall m1 x T2 T3 n1 n2,
  vtp m1 x T2 n1 ->
  stp [] T2 T3 n2 ->
  m1 < l -> n2 < n -> n1 < k ->
  vtpdd m1 x T3.
Proof.
  intros l. induction l. intros. solve by inversion.
  intros n. induction n. intros. solve by inversion.
  intros k. induction k; intros. solve by inversion.
  inversion H.
  - Case "top". inversion H0; subst; invty.
    + SCase "top". repeat eexists; eauto.
    + SCase "ssel2".
      assert (vtpdd m1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H7. omega.
    + SCase "and".
      assert (vtpdd m1 x T1). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T0). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T1). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T0). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T0) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "mem". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eauto.
    + SCase "mem". invty. subst.
      repeat eexists. eapply vtp_mem. eauto.
      eapply stp_trans. eauto. eauto.
      eapply stp_trans. eauto. eauto.
      eauto.
    + SCase "sel2".
      assert (vtpdd m1 x TX0). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H10. omega.
    + SCase "and".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T5). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T5). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T5) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "fun". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eauto.
    + SCase "fun". invty. subst.
      assert (stpd2 [T8] (open 0 (TVar (VAbs 0)) T0) (open 0 (TVar (VAbs 0)) T5)) as A. {
        eapply stp_narrow. simpl. eassumption. simpl. eassumption.
      }
      destruct A as [na A].
      repeat eexists. eapply vtp_fun. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      eapply stp_trans. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      assert (vtpdd m1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. subst. inversion H15. omega.
    + SCase "and".
      assert (vtpdd m1 x T6). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T7). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T6). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T7). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T7) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "ssel2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eauto.
    + SCase "ssel1". index_subst. index_subst. eapply IHn. eapply H5. eauto. eauto. omega. eauto.
    + SCase "ssel2".
      assert (vtpdd m1 x TX0). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto.
    + SCase "sel1".
      assert (closed (length ([]:tenv)) 0 (TSel (TVar (VAbs x0)) l1)) as A.
      eapply stpd2_closed2. eauto.
      simpl in A. inversion A. inversion H10. omega.
    + SCase "selx".
      eauto.
    + SCase "and".
      assert (vtpdd m1 x T1). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T1). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T2) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "and". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eauto.
    + SCase "sel2".
      assert (vtpdd m1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and11". eapply IHn in H4. eu. repeat eexists. eauto. omega. eauto. omega. omega. eauto.
    + SCase "and12". eapply IHn in H5. eu. repeat eexists. eauto. omega. eauto. omega. omega. eauto.
    + SCase "and".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T4) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.

  - Case "or1". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eauto.
    + SCase "sel2".
      assert (vtpdd m1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "or...".
      eapply IHn in H4. eu.
      repeat eexists. eapply H4. omega. eauto. omega. omega. eauto.
    + SCase "or...".
      assert (vtpdd m1 x T4) as A. eapply IHn. eapply H. eauto. omega. omega. eauto. eu.
      eapply IHn in A. eu.
      repeat eexists. eauto. omega. eauto. omega. omega. eauto.

  - Case "or2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eauto.
    + SCase "sel2".
      assert (vtpdd m1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "or...".
      eapply IHn in H4. eu.
      repeat eexists. eapply H4. omega. eauto. omega. omega. eauto.
    + SCase "or...".
      assert (vtpdd m1 x T4) as A. eapply IHn. eapply H. eauto. omega. omega. eauto. eu.
      eapply IHn in A. eu.
      repeat eexists. eauto. omega. eauto. omega. omega. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stp_subst_narrow_z: forall GH0 TX T1 T2 x m n1 n2,
  stp (GH0 ++ [TX]) T1 T2 n2 ->
  vtp m x (substt x TX) n1 ->
  stpd2 (map (substt x) GH0) (substt x T1) (substt x T2).
Proof.
  intros.
  edestruct stp_subst_narrow0. eauto. eauto.
  { intros. edestruct stp_subst_narrowX. eauto. eauto. eauto. eauto.
    { intros. eapply vtp_widen; eauto. }
    ev. repeat eexists. eauto.
  }
  eexists. eassumption.
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

Lemma index_dms: forall ds ds0 D ds1,
  dms_to_list ds = ds0 ++ dms_to_list (dcons D ds1) ->
  index (length (dms_to_list ds1)) (dms_to_list ds) = Some D.
Proof.
  intros. generalize dependent ds1. generalize dependent ds. induction ds0; intros.
  - simpl in H. destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite beq_nat_true_eq. reflexivity.
  - destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite false_beq_nat. eapply IHds0. eauto.
    rewrite H2. rewrite app_length. simpl.
    omega.
Qed.

Lemma dms_hastp_inv: forall ds' T' n,
  dms_has_type [] ds' T' n ->
  exists m n, vtp m ds' T' n.
Proof.
  intros ds' T' n H.
  assert (closed (length (@nil ty)) 0 T') as HC. {
    eapply dms_has_type_closed. eauto.
  }
  simpl in HC.
  remember T' as T0. remember H as HT0. clear HeqHT0.
  rewrite HeqT0 in H. rewrite HeqT0. rewrite HeqT0 in HC. clear HeqT0.
  remember ds' as ds0. rewrite Heqds0 in H.
  assert (exists dsa, dms_to_list ds0 = dsa ++ dms_to_list ds') as Hds. {
    exists []. rewrite app_nil_l. subst. reflexivity.
  }
  clear Heqds0.
  remember n as n0. rewrite Heqn0 in *. rewrite <- Heqn0 in HT0. clear Heqn0.
  remember [] as GH. generalize dependent T0. generalize dependent HeqGH.
  induction H; intros.
  - repeat eexists. eapply vtp_top.
  - subst.
    assert (closed 0 0 TS) as HCS. {
      simpl in HC. inversion HC; subst.
      eauto.
    }
    assert (closed 0 0 T11) as HC11. {
      simpl in HC. inversion HC; subst.
      inversion H5; subst. eauto.
    }
    assert (stpd2 [] T11 T11) as A. {
      eapply stpd2_refl. eauto.
    }
    eu.
    destruct Hds as [dsa Hdsa]. simpl in Hdsa.
    edestruct IHdms_has_type as [? [? AS]]. eauto. eauto. eauto. exists (dsa ++ [dty T11]). rewrite <- app_assoc. simpl. eauto. eauto. eauto.
    unfold substt in *. simpl.
    repeat eexists. eapply vtp_and. eapply vtp_mem.
    erewrite index_dms with (D:=dty T11). simpl. reflexivity. eauto.
    eauto. eauto. eauto. eauto. eauto.
  - subst.
    assert (closed 0 0 TS) as HCS. {
      simpl in HC. inversion HC; subst.
      eauto.
    }
    assert (closed 0 0 T11) as HC11. {
      simpl in HC. inversion HC; subst.
      inversion H7; subst. eauto.
    }
    assert (closed 1 0 (open 0 (TVar (VAbs 0)) T12)) as HC12. {
      simpl in HC. inversion HC; subst. inversion H7; subst.
      eapply closed_open. eapply closed_upgrade_gh. eauto. omega.
      econstructor. omega.
    }
    assert (stpd2 [] T11 T11) as A. {
      eapply stpd2_refl. eauto.
    }
    eu.
    assert (stpd2 [T11] (open 0 (TVar (VAbs 0)) T12) (open 0 (TVar (VAbs 0)) T12)) as B. {
      eapply stpd2_refl. eauto.
    }
    eu.
    destruct Hds as [dsa Hdsa]. simpl in Hdsa.
    edestruct IHdms_has_type as [? [? AS]]. eauto. exists (dsa ++ [dfun T11 T12 t12]). rewrite <- app_assoc. simpl. eauto. eauto. eauto.
    unfold substt in *. simpl.
    repeat eexists. eapply vtp_and. eapply vtp_fun.
    erewrite index_dms with (D:=dfun T11 T12 t12). simpl. reflexivity. eauto.
    eapply HT0. eauto. eauto. simpl. reflexivity. reflexivity.
    eauto. eauto. eauto. admit. eauto. eauto. eauto.
Grab Existential Variables.
apply 0. apply 0.
Qed.

Lemma hastp_inv: forall x T n1,
  has_type [] (tvar (VObj x)) T n1 ->
  exists m n1, vtp m x T n1.
Proof.
  intros. remember [] as GH. remember (tvar (VObj x)) as t.
  induction H; subst; try inversion Heqt.
  - Case "var". subst. eapply dms_hastp_inv; eauto.
  - Case "sub".
    destruct IHhas_type. eauto. eauto. ev.
    assert (exists m0, vtpdd m0 x T2). eexists. eapply vtp_widen; eauto.
    ev. eu. repeat eexists. eauto.
Qed.

Lemma hastp_subst_aux_z: forall ni, (forall GH TX T x t n1 n2,
  has_type (GH++[TX]) t T n2 -> n2 < ni ->
  has_type [] (tvar (VObj x)) (substt x TX) n1 ->
  exists n3, has_type (map (substt x) GH) (subst_tm x t) (substt x T) n3) /\
  (forall GH TX T x ds n1 n2,
  dms_has_type (GH++[TX]) ds T n2 -> n2 < ni ->
  has_type [] (tvar (VObj x)) (substt x TX) n1 ->
  exists n3, dms_has_type (map (substt x) GH) (subst_dms x ds) (substt x T) n3).
Proof.
  intro ni. induction ni. split; intros; omega. destruct IHni as [IHniT IHniD].
  split;
  intros; remember (GH++[TX]) as GH0; revert GH HeqGH0; inversion H; intros.
  - Case "vary".
    subst.
    assert (substt x T = T) as EqT. {
      erewrite subst_closed_id. reflexivity.
      eapply dms_has_type_closed in H2. eauto.
    }
    simpl. eexists. rewrite EqT. eapply T_Vary. eauto.
  - Case "varz". subst. simpl.
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0.
      eapply index_hit0 in H2. subst.
      eapply hastp_upgrade_gh. eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff; eauto.
      eexists. eapply T_Varz. eapply index_subst1. eauto. eauto. rewrite map_length. eapply closed_subst0. rewrite app_length in H3. simpl in H3. eapply H3.
  - Case "obj".
    edestruct IHniD with (GH:=GH1) as [? IH]. subst. eauto. omega. subst. eauto.
    subst. simpl.
    eexists. eapply T_Obj. eauto.
  - Case "app". subst. simpl.
    edestruct IHniT as [? IH1]. eapply H2. omega. eauto.
    edestruct IHniT as [? IH2]. eapply H3. omega. eauto.
    eexists. eapply T_App. eauto. eauto. eapply closed_subst.
    subst. rewrite map_length. rewrite app_length in *. simpl in *. eauto.
    subst. rewrite map_length. econstructor.
  - Case "appvar". subst. simpl.
    edestruct IHniT as [? IH1]. eapply H2. omega. eauto.
    edestruct IHniT as [? IH2]. eapply H3. omega. eauto.
    destruct v2.

    case_eq (beq_nat i 0); intros E.

    eapply beq_nat_true in E. subst.
    rewrite subst_open_commute0b.
    eexists. eapply T_AppVar. eauto. eauto. eauto.
    rewrite map_length. rewrite <- subst_open_commute0b.
    eapply closed_subst. eapply closed_upgrade_gh. eassumption.
    rewrite app_length. simpl. omega.
    econstructor.

    rewrite subst_open5.
    simpl in *. rewrite E in *.
    eexists. eapply T_AppVar. eauto. eauto. eauto.
    rewrite <- subst_open5. eapply closed_subst.
    subst. rewrite map_length. rewrite app_length in *. simpl in *. eassumption.
    subst. rewrite map_length. econstructor.
    apply []. apply beq_nat_false. apply E. apply []. apply beq_nat_false. apply E.

    eexists. eapply T_AppVar. eauto. eauto.
    rewrite subst_open_commute1. eauto.
    eapply closed_subst. subst. rewrite map_length. rewrite app_length in *. simpl in *.
    eapply closed_upgrade_gh. eassumption. omega.
    subst. rewrite map_length. econstructor.
  - Case "sub". subst.
    edestruct hastp_inv as [? [? HV]]; eauto.
    edestruct stp_subst_narrow_z. eapply H3. eapply HV.
    edestruct IHniT as [? IH]. eapply H2. omega. eauto.
    eexists. eapply T_Sub. eauto. eauto.
  - Case "dnil". subst. simpl.
    eexists. eapply D_Nil.
  - Case "mem". subst. simpl.
    edestruct IHniD as [? IH]. eapply H2. omega. eauto.
    eexists. eapply D_Mem. eauto. eapply closed_subst0. rewrite app_length in H3. rewrite map_length. eauto.
    unfold substt. simpl. rewrite <- length_subst_dms. reflexivity.
    eauto.
  - Case "abs". subst. simpl.
    edestruct IHniD as [? IHD]. eapply H2. omega. eauto.
    edestruct IHniT with (GH:=T11::GH1) as [? HI] . eauto. omega. eauto.
    simpl in HI.
    eexists. eapply D_Abs. eapply IHD. eapply HI.
    rewrite map_length. rewrite app_length. simpl.
    rewrite subst_open. unfold substt. reflexivity.
    eapply closed_subst0. rewrite map_length. rewrite app_length in H5. simpl in H5. eauto. eauto.
    eapply closed_subst0. rewrite map_length. rewrite app_length in H6. simpl in H6. eauto.
    unfold substt. simpl. rewrite <- length_subst_dms. reflexivity.
    eauto.
Grab Existential Variables.
apply 0. apply 0.
Qed.

Lemma hastp_subst_z: forall GH TX T x t n1 n2,
  has_type (GH++[TX]) t T n2 ->
  has_type [] (tvar (VObj x)) (substt x TX) n1 ->
  exists n3, has_type (map (substt x) GH) (subst_tm x t) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_aux_z with (t:=t). eauto. eauto. eauto.
Qed.

Lemma hastp_subst: forall GH TX T x t n1 n2,
  has_type (GH++[TX]) t T n2 ->
  has_type [] (tvar (VObj x)) TX n1 ->
  exists n3, has_type (map (substt x) GH) (subst_tm x t) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_z with (t:=t). eauto.
  erewrite subst_closed_id. eauto. eapply has_type_closed in H0. eauto.
Qed.

Lemma stp_subst_narrow: forall GH0 TX T1 T2 x m n1 n2,
  stp (GH0 ++ [TX]) T1 T2 n2 ->
  vtp m x TX n1 ->
  stpd2 (map (substt x) GH0) (substt x T1) (substt x T2).
Proof.
  intros. eapply stp_subst_narrow_z. eauto.
  erewrite subst_closed_id. eauto. eapply vtp_closed in H0. eauto.
Qed.

Theorem type_safety : forall t T n1,
  has_type [] t T n1 ->
  (exists x, t = tvar (VObj x)) \/
  (exists t' n2, step t t' /\ has_type [] t' T n2).
Proof.
  intros.
  assert (closed (length ([]:tenv)) 0 T) as CL. eapply has_type_closed. eauto.
  remember [] as GH. remember t as tt. remember T as TT.
  revert T t HeqTT HeqGH Heqtt CL.
  induction H; intros.
  - Case "vary". eauto.
  - Case "varz". subst GH. inversion H.
  - Case "obj". subst. right.
    repeat eexists.
    eapply T_Vary. eapply H.
  - Case "app". subst.
    assert (closed (length ([]:tenv)) 0 (TFun l T1 T)) as TF. eapply has_type_closed. eauto.
    assert ((exists x, t2 = tvar (VObj x)) \/
                (exists (t' : tm) n2,
                   step t2 t' /\ has_type [] t' T1 n2)) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto.
    assert ((exists x, t1 = tvar (VObj x)) \/
                (exists (t' : tm) n2,
                   step t1 t' /\ has_type [] t' (TFun l T1 T) n2)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      destruct HX.
      * SSCase "arg-val".
        ev. ev. subst.
        assert (exists m n1, vtp m x (TFun l T1 T) n1). eapply hastp_inv. eauto.
        assert (exists m n1, vtp m x0 T1 n1). eapply hastp_inv. eauto.
        ev. inversion H2. subst.
        assert (vtpdd x1 x0 T0). eapply vtp_widen. eauto. eauto. eauto. eauto. eauto.
        eu.
        assert (exists n1, has_type [] (tvar (VObj x)) T' n1) as A. eexists. eapply T_Vary. eauto.
        destruct A as [na A].
        assert (has_typed (map (substt x0) []) (subst_tm x0 t) (substt x0 (open 0 (TVar (VAbs 0)) T2))) as HIx0.
        eapply hastp_subst. rewrite app_nil_l. eauto. eauto.
        eu. simpl in HIx0.
        assert (has_typed [] (subst_tm x0 t) (substt x0 (open 0 (TVar (VAbs 0)) T2))) as HI. {
          subst. eauto.
        }
        eu. simpl in HI.
        edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H18. eauto.
        simpl in HI2.
        assert (substt x0 (open 0 (TVar (VAbs 0)) T) = T) as EqT. {
          erewrite <- closed_no_open. erewrite subst_closed_id. reflexivity.
          eassumption. eassumption.
        }
        rewrite EqT in HI2.
        right. repeat eexists. eapply ST_AppAbs. eauto. eauto.
      * SSCase "arg_step".
        ev. subst.
        right. repeat eexists. eapply ST_App2. eauto. eapply T_App.
        eauto. eauto.
        simpl in *. eassumption.
    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply ST_App1. eauto. eapply T_App.
      eauto. eauto.
      simpl in *. eassumption.

  - Case "appvar". subst.
    assert (closed (length ([]:tenv)) 0 (TFun l T1 T2)) as TF. eapply has_type_closed. eauto.
    assert ((exists x, tvar v2 = tvar (VObj x)) \/
                (exists (t' : tm) n2,
                   step (tvar v2) t' /\ has_type [] t' T1 n2)) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto.
    assert (exists x2, v2 = (VObj x2)) as HXeq. {
      destruct HX as [[? HX] | Contra]. inversion HX. eexists. reflexivity.
      destruct Contra as [t' [n' [Hstep Htyp]]].
      inversion Hstep.
    }
    clear HX. destruct HXeq as [x2 HXeq]. subst v2.
    assert ((exists x, t1 = tvar (VObj x)) \/
                (exists (t' : tm) n2,
                   step t1 t' /\ has_type [] t' (TFun l T1 T2) n2)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      ev. ev. subst.
      assert (exists m n1, vtp m x (TFun l T1 T2) n1). eapply hastp_inv. eauto.
      assert (exists m n1, vtp m x2 T1 n1). eapply hastp_inv. eauto.
      ev. inversion H1. subst.
      assert (vtpdd x0 x2 T0). eapply vtp_widen. eauto. eauto. eauto. eauto. eauto.
      eu.
      assert (exists n1, has_type [] (tvar (VObj x)) T' n1) as A. eexists. eapply T_Vary. eauto.
      destruct A as [na A].
      assert (has_typed (map (substt x2) []) (subst_tm x2 t) (substt x2 (open 0 (TVar (VAbs 0)) T3))) as HIx0.
      eapply hastp_subst. rewrite app_nil_l. eauto. eauto.
      eu. simpl in HIx0.
      assert (has_typed [] (subst_tm x2 t) (substt x2 (open 0 (TVar (VAbs 0)) T3))) as HI. {
        subst. eauto.
      }
      eu. simpl in HI.
      edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H18. eauto.
      simpl in HI2.
      assert ((substt x2 (open 0 (TVar (VAbs 0)) T2))=(open 0 (TVar (VObj x2)) T2)) as EqT2. {
        rewrite subst_open_commute0b. erewrite subst_closed_id. reflexivity.
        eassumption.
      }
      rewrite EqT2 in HI2.
      right. repeat eexists. eapply ST_AppAbs. eauto. eauto.
    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply ST_App1. eauto. eapply T_AppVar.
      eauto. eauto. eauto.
      simpl in *. eassumption.

  - Case "sub". subst.
    assert ((exists x, t0 = tvar (VObj x)) \/
               (exists (t' : tm) n2,
                  step t0 t' /\ has_type [] t' T1 n2)) as HH.
    eapply IHhas_type; eauto. change 0 with (length ([]:tenv)) at 1. eapply stpd2_closed1; eauto.
    destruct HH.
    + SCase "val".
      ev. subst. left. eexists. eauto.
    + SCase "step".
      ev. subst.
      right. repeat eexists. eauto. eapply T_Sub. eauto. eauto.
Qed.

Definition reduces (t:tm) (v:tm) (T:ty) :=
  exists ds n,
    v=(tvar (VObj ds)) /\ step_star t v /\ has_type [] (tvar (VObj ds)) T n.

Theorem full_type_safety : forall t T n1,
  has_type [] t T n1 ->
  exists v, reduces t v T.
Proof.
  intros.
  assert (closed (length ([]:tenv)) 0 T) as CL. eapply has_type_closed. eauto.
  remember [] as GH. remember t as tt. remember T as TT.
  revert T t HeqTT HeqGH Heqtt CL.
  induction H; intros.
  - Case "vary". subst. repeat eexists. eapply s_refl. eauto.
  - Case "varz". subst GH. inversion H.
  - Case "obj". subst.
    repeat eexists. eapply s_step. eapply ST_Obj. eapply s_refl. eapply T_Vary. eapply H.
  - Case "app". subst.
    assert (closed (length ([]:tenv)) 0 (TFun l T1 T)) as TF. eapply has_type_closed. eauto.
    assert (exists v, reduces t2 v T1) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto.
    assert (exists v, reduces t1 v (TFun l T1 T)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF as [vf [dsf [? [Eqf [Hsf Htf]]]]].
    destruct HX as [va [dsa [? [Eqa [Hsa Hta]]]]].
    assert (exists m n1, vtp m dsf (TFun l T1 T) n1). eapply hastp_inv. eauto.
    assert (exists m n1, vtp m dsa T1 n1). eapply hastp_inv. eauto.
    ev. inversion H2. subst.
    assert (vtpdd x1 dsa T0). eapply vtp_widen. eauto. eauto. eauto. eauto. eauto.
    eu.
    assert (exists n1, has_type [] (tvar (VObj dsf)) T' n1) as A. eexists. eapply T_Vary. eauto.
    destruct A as [na A].
    assert (has_typed (map (substt dsa) []) (subst_tm dsa t) (substt dsa (open 0 (TVar (VAbs 0)) T2))) as HIx0.
    eapply hastp_subst. rewrite app_nil_l. eauto. eauto.
    eu. simpl in HIx0.
    assert (has_typed [] (subst_tm dsa t) (substt dsa (open 0 (TVar (VAbs 0)) T2))) as HI. {
      subst. eauto.
    }
                                                                                           eu. simpl in HI.
   edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H18. eauto.
   simpl in HI2.
   assert (substt dsa (open 0 (TVar (VAbs 0)) T) = T) as EqT. {
     erewrite <- closed_no_open. erewrite subst_closed_id. reflexivity.
     eassumption. eassumption.
   }
   rewrite EqT in HI2.
   assert (exists dsr nr, step_star (subst_tm dsa t) (tvar (VObj dsr)) /\
                          has_type [] (tvar (VObj dsr)) (substt dsa (open 0 (TVar (VAbs 0)) T2)) nr) as HR. {
     eapply H19; eauto.
   }
   ev. repeat eexists. eapply step_star_app; eauto. eauto.

  - Case "appvar". subst.
    assert (closed (length ([]:tenv)) 0 (TFun l T1 T2)) as TF. eapply has_type_closed. eauto.
    assert (exists v, reduces (tvar v2) v T1) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto.
    assert (exists v, reduces t1 v (TFun l T1 T2)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF as [vf [dsf [? [Eqf [Hsf Htf]]]]].
    destruct HX as [va [dsa [? [Eqa [Hsa Hta]]]]].
    assert (v2 = VObj dsa) as HXeq. {
      subst. eapply step_star_var; eauto.
    }
    subst v2.
    assert (exists m n1, vtp m dsf (TFun l T1 T2) n1). eapply hastp_inv. eauto.
    assert (exists m n1, vtp m dsa T1 n1). eapply hastp_inv. eauto.
    ev. inversion H1. subst.
    assert (vtpdd x1 dsa T0). eapply vtp_widen. eauto. eauto. eauto. eauto. eauto.
    eu.
    assert (exists n1, has_type [] (tvar (VObj dsf)) T' n1) as A. eexists. eapply T_Vary. eauto.
    destruct A as [na A].
    assert (has_typed (map (substt dsa) []) (subst_tm dsa t) (substt dsa (open 0 (TVar (VAbs 0)) T3))) as HIx0.
    eapply hastp_subst. rewrite app_nil_l. eauto. eauto.
    eu. simpl in HIx0.
    assert (has_typed [] (subst_tm dsa t) (substt dsa (open 0 (TVar (VAbs 0)) T3))) as HI. {
      subst. eauto.
    }
    eu. simpl in HI.
    edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H18. eauto.
    simpl in HI2.
    assert ((substt dsa (open 0 (TVar (VAbs 0)) T2))=(open 0 (TVar (VObj dsa)) T2)) as EqT2. {
      rewrite subst_open_commute0b. erewrite subst_closed_id. reflexivity.
      eassumption.
    }
    rewrite EqT2 in HI2.
    assert (exists dsr nr, step_star (subst_tm dsa t) (tvar (VObj dsr)) /\
                           has_type [] (tvar (VObj dsr)) (substt dsa (open 0 (TVar (VAbs 0)) T3)) nr) as HR. {
      eapply H19; eauto.
    }
    ev. repeat eexists. eapply step_star_app; eauto. eapply T_Sub. eauto. eauto.

  - Case "sub". subst.
    assert (exists v, reduces t0 v T1) as HH.
    eapply IHhas_type; eauto. change 0 with (length ([]:tenv)) at 1. eapply stpd2_closed1; eauto.
    destruct HH as [v [ds [? [Eq [Hs Ht]]]]]. subst.
    repeat eexists. eauto. eapply T_Sub. eauto. eauto.

Qed.
