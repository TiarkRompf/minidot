(* ############################################################ *)
(*                                                              *)
(*               Language definition for STLC 1/2               *)
(*                                                              *)
(* ############################################################ *)

(* Starting point: https://github.com/TiarkRompf/minidot/blob/master/dev2015/nano2.v *)
(* Starting point: https://github.com/TiarkRompf/scala-escape/blob/master/coq/stlc1.v *)


Require Export Arith.EqNat.
Require Export Arith.Le.
From Coq Require Import omega.Omega.
Require Import Coq.Lists.List.

Import ListNotations.


(* ############################################################ *)
(* Definitions                                                  *)
(* ############################################################ *)

(* ### Syntax ### *)

Definition id := nat.

Inductive class : Type :=
  | First  : class
  | Second : class
.

(* types *)
Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> class -> ty -> ty
  | TRec   : ty -> ty (* NEW: wrapper indicates recursive occurrence *)
  | TCap   : ty      (* NEW: capability to unwrap TRec values *)
.

(* variables: 1st or 2nd class, using DeBrujin levels *)
Inductive var : Type :=
  | V : class -> id -> var
.

(* terms *)
Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : var -> tm
  | tapp   : tm -> tm -> tm     (* f(x) *)
  | tabs   : class -> tm -> tm  (* \f x.y *)
  | tunrec : tm -> tm -> tm     (* NEW: unwrap a recursive value, given a capability *)
.

(* environments, split according to 1st/2nd class *)
Inductive env (X: Type) :=
  | Def : list X -> list X -> nat -> env X.

(* values *)
Inductive vl : Type :=
  | vbool : bool -> vl
  | vabs  : env vl -> class -> tm -> vl
  | vrec  : vl -> vl (* NEW: recursive wrapper *)
  | vcap  : vl      (* NEW: capability *)
.

Definition venv := env vl.  (* value environments *)
Definition tenv := env ty.  (* type environments  *)

Hint Unfold venv.
Hint Unfold tenv.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.


(* environment lookup *)
Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

Definition lookup {X : Type} (n : var) (l : env X) : option X :=
  match l with
    | Def _ l1 l2 m =>
         match n with
           | V First idx  => index idx l1
           | V Second idx => if ble_nat m idx then index idx l2 else None
         end
   end
.

(* restrict visible bindings in environment *)
Definition sanitize_any {X : Type} (l : env X) (n:nat): env X :=
  match l with
    | Def _ l1 l2 _ => Def X l1 l2 n
  end.

Definition sanitize_env {X : Type} (c : class) (l : env X) : env X :=
  match c,l  with
    | First, Def _ _ l2 _ => sanitize_any l (length l2)
    | Second, _ => l
  end.

(* add new binding to environment *)
Definition expand_env {X : Type} (l : env X) (x : X) (c : class) : (env X) :=
match l with
| Def _ l1 l2 m =>
   match c with
   | First => Def X (x::l1) l2 m
   | Second => Def X l1 (x::l2) m
   end
end
.


(* ### Type Assignment ### *)

Inductive has_type : tenv -> tm -> class -> ty -> Prop :=
| t_true: forall n env,
           has_type env ttrue n TBool
| t_false: forall n env,
           has_type env tfalse n TBool
| t_var: forall n x env T1,
           lookup x (sanitize_env n env) = Some T1 ->
           has_type env (tvar x) n T1
| t_app: forall m n env f x T1 T2,
           has_type env f Second (TFun T1 m T2) ->
           has_type env x m T1 ->
           has_type env (tapp f x) n T2
| t_abs: forall m n env y T1 T2,  (* NEW: wrap recursive binding *)
           has_type (expand_env (expand_env (sanitize_env n env) (TRec (TFun T1 m T2)) Second) T1 m) y First T2 ->
           has_type env (tabs m y) n (TFun T1 m T2)
| t_unrec: forall n env tr tc T1, (* NEW: unrec case *)
           has_type env tr n (TRec T1) ->
           has_type env tc n TCap ->
           has_type env (tunrec tr tc) n T1 
.

Definition get_inv_idx {X : Type} (env : env X) :=
match env with
| Def _ l1 l2 idx => idx
end
.


(* ### Operational Semantics ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

Fixpoint teval(k: nat)(env: venv)(t: tm)(n: class){struct k}: option (option vl) :=
  match k with
    | 0 => None
    | S k' =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (lookup x (sanitize_env n env))
        | tabs m y   => Some (Some (vabs (sanitize_env n env) m y))
        | tapp ef ex   =>
           match teval k' env ef Second with
             | None => None
             | Some None => Some None
             | Some (Some (vbool _)) => Some None
             | Some (Some (vrec _)) => Some None (* NEW *)
             | Some (Some vcap) => Some None (* NEW *)
             | Some (Some (vabs env2 m ey)) => (* NEW: vrec wrapper *)
                match teval k' env ex m with
                  | None => None
                  | Some None => Some None
                  | Some (Some vx) =>
                       teval k' (expand_env (expand_env env2 (vrec (vabs env2 m ey)) Second) vx m) ey First
                end
           end
        | tunrec er ec => (* NEW *)
          match teval k' env er n with
          | None => None
          | Some None => Some None
          | Some (Some (vbool _)) => Some None
          | Some (Some (vabs _ _ _)) => Some None
          | Some (Some vcap) => Some None
          | Some (Some (vrec v)) =>
            match teval k' env ec n with (* should use Second instead of n? *)
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs _ _ _)) => Some None
            | Some (Some (vrec _)) => Some None
            | Some (Some vcap) =>
              Some (Some v)
            end
          end
      end
  end.


(* ############################################################ *)
(* Proofs                                                       *)
(* ############################################################ *)

(* ### Some helper lemmas ### *)

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.

Hint Constructors option.
Hint Constructors list.
Hint Constructors env.

Hint Unfold index.
Hint Unfold length.
Hint Unfold expand_env.
Hint Unfold lookup.
Hint Unfold index.
Hint Unfold sanitize_env.
Hint Unfold sanitize_any.

Hint Resolve ex_intro.

Definition length_env {X : Type} (c : class) (env : env X): nat :=
match env, c with
| Def _ l1 l2 n, First => length l1
| Def _ l1 l2 n, Second => length l2
end
.

Definition get_class (x : var): class :=
match x with
| V c _ => c
end
.

Definition get_idx (x : var): nat :=
match x with
| V _ n => n
end
.

Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  - (* nil *) intros. inversion H.
  - (* case *) intros. inversion H.
    case_eq (beq_nat n (length vs)); intros E.
    + (* SCase "hit". *)
      rewrite E in H1. inversion H1. subst.
      eapply beq_nat_true in E.
      unfold length. unfold length in E. rewrite E. eauto.
    + (* SCase "miss". *)
      rewrite E in H1.
      assert (n < length vs). eapply IHvs. apply H1.
      compute. eauto.
Qed.

Hint Immediate index_max.

Lemma lookup_max : forall X vs x (T: X),
                       lookup x vs = Some T ->
                       get_idx x < length_env (get_class x) vs.
Proof.
  intros X vs; destruct vs as [l1 l2 n].
  intros x T H.
  destruct x. destruct c; simpl.
  - (* Case "VFst". *) inversion H; eauto.
  - (* Case "VSnd". *) inversion H.
    destruct (ble_nat n i); inversion H1; eauto.
Qed.

(* ############################################################ *)
(*                                                              *)
(*                 Type soundness for STLC 1/2                  *)
(*                                                              *)
(* ############################################################ *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.


(* ############################################################ *)
(* Definitions                                                  *)
(* ############################################################ *)

(* ### Value typing and well-typed runtime environments ### *)

Inductive wf_env : venv -> tenv -> Prop := 
| wfe_nil : forall n, wf_env (Def vl nil nil n) (Def ty nil nil n)
| wfe_cons : forall v t vs ts n,
    val_type (expand_env vs v n) v t ->
    wf_env vs ts ->
    get_inv_idx vs = get_inv_idx ts ->
    wf_env (expand_env vs v n) (expand_env ts t n)

with val_type : venv -> vl -> ty -> Prop := 
| v_bool: forall venv b,
    val_type venv (vbool b) TBool
| v_abs: forall env venv tenv y T1 T2 m, (* NEW: TRec wrapper *)
    wf_env venv tenv ->
    has_type (expand_env (expand_env tenv (TRec (TFun T1 m T2)) Second) T1 m) y First T2 ->
    val_type env (vabs venv m y) (TFun T1 m T2)
| v_rec: forall env v T,  (* NEW *)
    val_type env v T ->
    val_type env (vrec v) (TRec T)
| v_cap: forall env,
    val_type env vcap TCap (* NEW *)
.


(* type equivalence: only via reflexivity *)
Inductive stp: venv -> ty -> venv -> ty -> Prop :=
| stp_refl: forall G1 G2 T,
   stp G1 T G2 T.

Hint Constructors val_type.
Hint Constructors wf_env.

Hint Unfold expand_env.

Lemma length_env_incr : forall (X : Type) n m env (x : X),
   n = m ->
   length_env n (expand_env env x m) = 1 + length_env n env.
Proof.
  intros. destruct env0; destruct n; inversion H; auto.
Qed.
   
Lemma length_env_same : forall (X : Type) n m env (x : X),
   n <> m ->
   length_env n (expand_env env x m) = length_env n env.
Proof.
  intros. destruct env0; destruct n; destruct m.
      apply ex_falso_quodlibet; auto.
      auto.
      auto.
      apply ex_falso_quodlibet; auto.
Qed.

Hint Rewrite length_env_incr.
Hint Rewrite length_env_same.
Hint Unfold not.

Lemma wf_length : forall vs ts,
      wf_env vs ts ->
      length_env First vs = length_env First ts /\ length_env Second vs = length_env Second ts.
Proof.
  intros. induction H; auto.
  destruct IHwf_env as [L R].
  destruct n. 
  - (* Case "First" *) split.
    repeat rewrite length_env_incr; auto.
    repeat rewrite length_env_same; auto.
    unfold not; intros. inversion H2. unfold not; intros. inversion H2.
  - (* Case "Second" *) split.
    repeat rewrite length_env_same; auto.
    unfold not; intros. inversion H2. unfold not; intros. inversion H2.
    repeat rewrite length_env_incr; auto.
Qed.

Hint Immediate wf_length.



Lemma wf_idx : forall vs ts,
      wf_env vs ts ->
      get_inv_idx vs = get_inv_idx ts.
Proof.
  intros. induction H; auto.
  destruct vs; destruct ts; destruct n; auto.
Qed.

Hint Immediate wf_idx.


Lemma valtp_extend : forall vs v v1 T n,
                       val_type vs v T ->
                       val_type (expand_env vs v1 n) v T.
Proof. intros. induction H; eauto. Qed.

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

Hint Immediate index_extend.

Lemma lookup_extend : forall X vs x a (T: X) n,
                       lookup x vs = Some T ->
                       lookup x (expand_env vs a n) = Some T.

Proof.
  intros.
  assert (get_idx x < length_env (get_class x) vs). eapply lookup_max. eauto.
  assert (get_idx x <> length_env (get_class x) vs). omega.
  assert (beq_nat (get_idx x) (length_env (get_class x) vs) = false) as E. eapply beq_nat_false_iff; eauto.
  destruct vs.
  destruct n; destruct x; destruct c; simpl in E;
    inversion H; simpl; try rewrite E; auto.
Qed.

(*
Lemma index_safe_ex: forall Hl1 Hl2 Gl1 Gl2 Hidx Gidx TF i,
   wf_env (Def vl Hl1 Hl2 Hidx) (Def ty Gl1 Gl2 Gidx) ->
   index i Gl1 = Some TF ->
   exists v, index i Hl1 = Some v.
Proof. intros.
  apply wf_length in H. destruct H as [L _]. simpl in L.
  
Qed.
*)

Lemma lookup_safe_ex: forall H1 G1 TF x,
             wf_env H1 G1 ->
             lookup x G1 = Some TF ->
             exists v, lookup x H1 = Some v /\ val_type H1 v TF.
Proof. intros. induction H.
  - (* Case "nil". *) inversion H0. destruct x; destruct c; destruct (ble_nat n i); inversion H1.
  - (* Case "cons". *) destruct vs as [vl1 vl2 vidx]. destruct ts as [tl1 tl2 tidx].
    apply wf_length in H1. destruct H1 as [H1l H1r].
    destruct x; destruct c; inversion H0.
    + (* SCase "VFst". *) destruct n; simpl in H0 ; simpl in H2.
      * (* SSCase "First". *)
        case_eq (beq_nat i (length tl1)).
        { (* SSSCase "hit". *)
          intros E.
          rewrite E in H0. inversion H0. subst t. simpl.
          assert (beq_nat i (length vl1) = true). eauto.
          rewrite H1. eauto. }
        { (* SSSCase "miss". *)
          intros E.
          assert (beq_nat i (length vl1) = false). eauto.
          assert (exists v0, lookup (V First i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type (Def vl vl1 vl2 vidx) v0 TF) as HI.
          eapply IHwf_env. simpl. rewrite E in H0. eauto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto. }
     * (* SSCase "Second". *)
       assert (exists v0, lookup (V First i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type (Def vl vl1 vl2 vidx) v0 TF) as HI.
       eapply IHwf_env. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto.
   + (* SCase "VSnd". *) destruct n; simpl in H0; simpl in H2.
     * (* SSCase "First". *)
       assert (exists v0, lookup (V Second i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type (Def vl vl1 vl2 vidx) v0 TF) as HI.
       eapply IHwf_env. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto.
     * (* SSCase "Second". *)
       case_eq (beq_nat i (length tl2)).
        { (* SSSCase "hit". *)
          intro E.
          rewrite E in H0. simpl. destruct (ble_nat tidx i); inversion H0.
          subst t.
          assert (beq_nat i (length vl2) = true). eauto.
          rewrite H1. inversion H3. subst vidx. destruct (ble_nat tidx i); eauto. inversion H5. }
        { (* SSSCase "miss". *)
          intro E.
          assert (beq_nat i (length vl2) = false). eauto.
          assert (exists v0, lookup (V Second i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type (Def vl vl1 vl2 vidx) v0 TF) as HI.
          eapply IHwf_env. simpl. destruct (ble_nat tidx i). inversion H0. rewrite E in H0. rewrite H0. rewrite E. auto. auto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend; eauto. }
Qed.
  
Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.


Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stp H1 T1 H2 T2 ->
  val_type H2 vf T2.
Proof.
  intros. generalize dependent T2. induction H; intros.
  - inversion H0. eauto.
  - inversion H1. eauto.
  - inversion H0. eapply v_rec. eapply IHval_type. eapply stp_refl.
  - inversion H0. eauto. 
Qed.

Lemma invert_abs: forall venv vf vx T1 n T2,
  val_type venv vf (TFun T1 n T2) ->
  exists env tenv y T3 T4,
    vf = (vabs env n y) /\
    wf_env env tenv /\
    has_type (expand_env (expand_env tenv (TRec (TFun T3 n T4)) Second) T3 n) y First T4 /\
    stp venv T1 (expand_env (expand_env env (vrec vf) Second) vx n) T3 /\
    stp (expand_env (expand_env env (vrec vf) Second) vx n) T4 venv T2.
Proof.
  intros. inversion H. repeat eexists; repeat eauto.
Qed.


Lemma ext_sanitize_commute : forall {T} n venv (v:T) c,
   expand_env (sanitize_any venv n) v c = sanitize_any (expand_env venv v c) n.
Proof.
  intros. destruct venv0. destruct c; simpl; eauto. 
Qed.

Lemma val_type_sanitize_any : forall n venv res T,
  val_type venv res T ->
  val_type (sanitize_any venv n) res T.
Proof.
  intros. induction H; eauto. 
Qed.

Lemma val_type_sanitize : forall env res T n,
  val_type (sanitize_env n env) res T ->
  val_type env res T.
Proof.
  intros. induction H; eauto.
Qed.

Lemma wf_sanitize_any : forall n venv tenv,
   wf_env venv tenv ->
   wf_env (sanitize_any venv n) (sanitize_any tenv n).
Proof.
  intros. induction H.
  - simpl. eapply wfe_nil.
  - eapply wfe_cons in IHwf_env.
    rewrite <-ext_sanitize_commute. rewrite <-ext_sanitize_commute.
    eauto. eauto. rewrite ext_sanitize_commute.
    eapply val_type_sanitize_any in H. eauto. eauto.
Qed.  

Lemma wf_sanitize : forall n venv tenv,
   wf_env venv tenv ->
   wf_env (sanitize_env n venv) (sanitize_env n tenv).
Proof.
  intros. destruct n; unfold sanitize_env. destruct venv0. destruct tenv0.
  assert (length l0 = length l2). apply wf_length in H; destruct H as [L R]; eauto.
  rewrite H0. eapply wf_sanitize_any. eauto.
  eauto.
Qed.
  

Hint Immediate wf_sanitize.
   

(* ### Theorem 3.5 ### *)
(* if result of STLC 1/2 evaluation is not a timeout, then *)
(* it is not stuck, and well-typed *)

Theorem full_safety : forall k e n tenv venv res T,
  teval k venv e n = Some res -> has_type tenv e n T -> wf_env venv tenv ->
  res_type venv res T.

Proof.
  intros k. induction k.
  (* 0 *)   intros. inversion H.
  (* S n *) intros. destruct e; inversion H; inversion H0. 
  
  - (* Case "True". *)  eapply not_stuck. eapply v_bool.
  - (* Case "False". *) eapply not_stuck. eapply v_bool.

  - (* Case "Var". *)
    subst.
    destruct (lookup_safe_ex (sanitize_env n venv0) (sanitize_env n tenv0) T v) as [va [I V]]; eauto. 

    rewrite I. eapply not_stuck. eapply val_type_sanitize. eapply V.

  - (* Case "App". *)
    remember (teval k venv0 e1 Second) as tf.
    subst T. subst n0.
    
    destruct tf as [rf|]; try inversion H3. 
    assert (res_type venv0 rf (TFun T1 m T2)) as HRF. (* SCase "HRF". *) subst. eapply IHk; eauto.
    inversion HRF as [? vf].

    subst rf. remember vf as rvf. destruct vf; subst rvf; inversion H7. (* try (subst rvf; solve inversion). *)
    assert (c = m). destruct m; destruct c; try inversion H18; eauto. (* try (subst rvf; solve inversion); eauto.*) subst c. (* subst rvf. *)
    remember (teval k venv0 e2 m0) as tx.

    destruct tx as [rx|]; try inversion H3.
    assert (res_type venv0 rx T1) as HRX. (* SCase "HRX". *) subst. eapply IHk; eauto.
    inversion HRX as [? vx]. 

    destruct (invert_abs venv0 (vabs e m t) vx T1 m T2) as
        [env1' [tenv1' [y0 [T3' [T4' [EF [WF [HTY [STX STY]]]]]]]]]. eauto.
    (* now we know it's a closure, and we have has_type evidence *)

    inversion EF. subst e. subst y0. clear EF.
    subst rx.

    assert (res_type (expand_env (expand_env env1' (vrec (vabs venv2 m t)) Second) vx m) res T4') as HRY.
        (* SSSCase "HRY". *)
          subst. eapply IHk; eauto.
        (* wf_env f x *) econstructor. eapply valtp_widen; eauto.
        (* wf_env f   *) econstructor. eapply v_rec. eapply v_abs; eauto.
          eauto.
          apply wf_idx. assumption.
          apply wf_idx. econstructor. eauto. assumption. apply wf_idx. assumption.

    inversion HRY as [? vy].

    eapply not_stuck. eapply valtp_widen; eauto.
    
  - (* Case "Abs". *) intros. inversion H. inversion H0.
    eapply not_stuck. eapply v_abs; eauto.
    eauto.
  - (* Case "Rec". *)
    remember (teval k venv0 e1 n) as tevr.

    destruct tevr as [revr|]; try inversion H3.
    assert (res_type venv0 revr (TRec T)) as HRR. {
     subst. eapply IHk; eauto.
    }

    inversion HRR as [? vr]. inversion H10. subst.

    remember (teval k venv0 e2 n) as tevc. 
    destruct tevc as [revc|]; try inversion H11.
    assert (res_type venv0 revc TCap) as HRC. {
      subst. eapply IHk; eauto.
    }
    inversion HRC as [? vc]. inversion H2. subst.
    (* NOTE: if there is no val_type case for vcap this inversion fails
    and recursion is impossible in well-formed envs *)
    
    inversion H4. subst. eauto. 
Qed.


(* Strong Normalization for STLC *)

(* copied from nano0.v *)
(* copied from dev2017/nano0-total.v *)

(* This version prohibits recursion, and we prove that   *)
(* evaluation always terminates with a well-typed value. *)
(* From this follows both type soundness and strong      *)
(* normalization for STLC.                               *)

Definition tevaln env e cl v := exists nm, forall n, n > nm -> teval n env e cl = Some (Some v).


(* need to use Fixpoint because of positivity restriction *)
Fixpoint val_type_tnt (env:venv) (v:vl) (T:ty): Prop := match v, T with
| vbool b, TBool => True
| vabs env clv y, TFun T1 clt T2 => (clv = clt) /\
  (forall vx, val_type_tnt env vx T1 ->
     exists v, tevaln (expand_env (expand_env env (vrec (vabs env clv y)) Second) vx clv) y First v /\ val_type_tnt env v T2)
| vrec v, TRec T => True (* NEW: rec, but we can't do anything with it *)
| _,_ => False
end.


Inductive wf_env_tnt : venv -> tenv -> Prop := 
| wfe_tnt_nil : forall n, wf_env_tnt (Def vl nil nil n) (Def ty nil nil n)
| wfe_tnt_env : forall v t vs ts n,
    val_type_tnt (expand_env vs v n) v t ->
    (* val_type (expand_env vs v n) v t ?? *) (* vrec v ?? *)
    wf_env_tnt vs ts ->
    get_inv_idx vs = get_inv_idx ts ->
    wf_env_tnt (expand_env vs v n) (expand_env ts t n)
.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
(* Hint Constructors val_type. *)
Hint Constructors wf_env_tnt.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.

Lemma wf_length_tnt : forall vs ts,
      wf_env_tnt vs ts ->
      length_env First vs = length_env First ts /\ length_env Second vs = length_env Second ts.
Proof.
  intros. induction H; auto.
  destruct IHwf_env_tnt as [L R].
  destruct n. 
  - (* Case "First" *) split.
    repeat rewrite length_env_incr; auto.
    repeat rewrite length_env_same; auto.
    unfold not; intros. inversion H2. unfold not; intros. inversion H2.
  - (* Case "Second" *) split.
    repeat rewrite length_env_same; auto.
    unfold not; intros. inversion H2. unfold not; intros. inversion H2.
    repeat rewrite length_env_incr; auto.
Qed.

Hint Immediate wf_length_tnt.

Lemma valtp_extend_tnt : forall vs v v1 T n,
                       val_type_tnt vs v T ->
                       val_type_tnt (expand_env vs v1 n) v T.
Proof.
  intros. induction v; destruct T; try (simpl in H; inversion H); auto.
Qed.

(* NOTE: will needed (closed T vs) ! *)
Lemma valtp_shrink_tnt : forall vs v v1 T n,
                       val_type_tnt (expand_env vs v1 n) v T ->
                       val_type_tnt vs v T.
Proof.
  intros. induction v; destruct T; try (simpl in H; inversion H); auto.
Qed.

Lemma lookup_safe_ex_tnt: forall H1 G1 TF x,
             wf_env_tnt H1 G1 ->
             lookup x G1 = Some TF ->
             exists v, lookup x H1 = Some v /\ val_type_tnt H1 v TF.
Proof. intros. induction H.
  - (* Case "nil". *) inversion H0. destruct x; destruct c; destruct (ble_nat n i); inversion H1.
  - (* Case "cons". *) destruct vs as [vl1 vl2 vidx]. destruct ts as [tl1 tl2 tidx].
    apply wf_length_tnt in H1. destruct H1 as [H1l H1r].
    destruct x; destruct c; inversion H0.
    + (* SCase "VFst". *) destruct n; simpl in H0 ; simpl in H2.
      * (* SSCase "First". *)
        case_eq (beq_nat i (length tl1)).
        { (* SSSCase "hit". *)
          intros E.
          rewrite E in H0. inversion H0. subst t. simpl.
          assert (beq_nat i (length vl1) = true). eauto.
          rewrite H1. eauto. }
        { (* SSSCase "miss". *)
          intros E.
          assert (beq_nat i (length vl1) = false). eauto.
          assert (exists v0, lookup (V First i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type_tnt (Def vl vl1 vl2 vidx) v0 TF) as HI.
          eapply IHwf_env_tnt. simpl. rewrite E in H0. eauto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend_tnt; eauto. }
     * (* SSCase "Second". *)
       assert (exists v0, lookup (V First i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type_tnt (Def vl vl1 vl2 vidx) v0 TF) as HI.
       eapply IHwf_env_tnt. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend_tnt; eauto.
   + (* SCase "VSnd". *) destruct n; simpl in H0; simpl in H2.
     * (* SSCase "First". *)
       assert (exists v0, lookup (V Second i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type_tnt (Def vl vl1 vl2 vidx) v0 TF) as HI.
       eapply IHwf_env_tnt. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend_tnt; eauto.
     * (* SSCase "Second". *)
       case_eq (beq_nat i (length tl2)).
        { (* SSSCase "hit". *)
          intro E.
          rewrite E in H0. simpl. destruct (ble_nat tidx i); inversion H0.
          subst t.
          assert (beq_nat i (length vl2) = true). eauto.
          rewrite H1. inversion H3. subst vidx. destruct (ble_nat tidx i); eauto. inversion H5. }
        { (* SSSCase "miss". *)
          intro E.
          assert (beq_nat i (length vl2) = false). eauto.
          assert (exists v0, lookup (V Second i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type_tnt (Def vl vl1 vl2 vidx) v0 TF) as HI.
          eapply IHwf_env_tnt. simpl. destruct (ble_nat tidx i). inversion H0. rewrite E in H0. rewrite H0. rewrite E. auto. auto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eapply valtp_extend_tnt; eauto. }
Qed.



  
Lemma invert_abs_tnt: forall venv vf T1 cl T2,
  val_type_tnt venv vf (TFun T1 cl T2) ->
  exists env y,
    vf = (vabs env cl y) /\ 
    (forall vx, val_type_tnt venv vx T1 ->
       exists v, tevaln (expand_env (expand_env env (vrec vf) Second) vx cl) y First v /\ val_type_tnt venv v T2).
Proof.
  intros. simpl in H. destruct vf.
  - inversion H.
  - destruct H. subst c. exists e. exists t. split. eauto. admit. (* wrong env, need widen *)
  - inversion H.
  - inversion H.
Admitted.

Lemma val_type_sanitize_any_tnt : forall n venv res T,
  val_type_tnt venv res T ->
  val_type_tnt (sanitize_any venv n) res T.
Proof.
  intros. induction res; destruct T; try (simpl in H; inversion H); auto.
Qed.

Lemma val_type_sanitize_tnt : forall env res T n,
  val_type_tnt (sanitize_env n env) res T ->
  val_type_tnt env res T.
Proof.
  intros. induction res; destruct T; try (simpl in H; inversion H); auto.
Qed.

Lemma wf_idx_tnt : forall vs ts,
      wf_env_tnt vs ts ->
      get_inv_idx vs = get_inv_idx ts.
Proof.
  intros. induction H; auto.
  destruct vs; destruct ts; destruct n; auto.
Qed.

Hint Immediate wf_idx_tnt.

Lemma wf_sanitize_any_tnt : forall n venv tenv,
   wf_env_tnt venv tenv ->
   wf_env_tnt (sanitize_any venv n) (sanitize_any tenv n).
Proof.
  intros. induction H.
  - simpl. eapply wfe_tnt_nil.
  - eapply wfe_tnt_env in IHwf_env_tnt.
    rewrite <-ext_sanitize_commute. rewrite <-ext_sanitize_commute.
    eauto. eauto. rewrite ext_sanitize_commute.
    eapply val_type_sanitize_any_tnt in H. eauto. eauto.
Qed.  

Lemma wf_sanitize_tnt : forall n venv tenv,
   wf_env_tnt venv tenv ->
   wf_env_tnt (sanitize_env n venv) (sanitize_env n tenv).
Proof.
  intros. destruct n; unfold sanitize_env. destruct venv0. destruct tenv0.
  assert (length l0 = length l2). apply wf_length_tnt in H; destruct H as [L R]; eauto.
  rewrite H0. eapply wf_sanitize_any_tnt. eauto.
  eauto.
Qed.
  

Hint Immediate wf_sanitize_tnt.


(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall e cl tenv T,
  has_type tenv e cl T -> forall venv, wf_env_tnt venv tenv ->
  exists v, tevaln venv e cl v /\ val_type_tnt venv v T.

Proof.
  intros ? ? ? ? W.
  induction W; intros ? WFE.
  
  - (* Case "True". *) eexists. split.
    exists 0. intros. destruct n0. omega. simpl. eauto. simpl. eauto. 
  - (* Case "False". *) eexists. split.
    exists 0. intros. destruct n0. omega. simpl. eauto. simpl. eauto. 

  - (* Case "Var". *)
    destruct (lookup_safe_ex_tnt (sanitize_env n venv0) (sanitize_env n env0) T1 x) as [v IV]. eauto. eauto. 
    inversion IV as [I V]. 

    exists v. split. exists 0. intros. destruct n0. omega. simpl. rewrite I. eauto. eapply val_type_sanitize_tnt. eapply V.

  - (* Case "App". *)
    destruct (IHW1 venv0 WFE) as [vf [IW1 HVF]].
    destruct (IHW2 venv0 WFE) as [vx [IW2 HVX]].
    
    eapply invert_abs_tnt in HVF.
    destruct HVF as [venv1 [y [HF IHF]]].

    destruct (IHF vx HVX) as [vy [IW3 HVY]].

    exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n0. omega. simpl.
      rewrite IWF. subst vf. rewrite IWX. rewrite IWY. eauto.
      omega. omega. omega.
    }
    eapply HVY.
    
  - (* Case "Abs". *)
    eexists. split. exists 0. intros. destruct n0. omega. simpl. eauto.
    simpl. repeat split; eauto.  intros. 
(*    assert (stpd2 true venv0 T1 (vx::venv0) T1). eapply stpd2_extend2. eapply stpd2_refl; eauto. eu.
    assert (stpd2 true (vx::venv0) T2 venv0 T2). eapply stpd2_extend1. eapply stpd2_refl; eauto. eu. *)

    remember (expand_env
         (expand_env (sanitize_env n venv0)
            (vrec
               (vabs (sanitize_env n venv0) m y))
            Second) vx m) as venv1.

    remember (expand_env
             (expand_env (sanitize_env n env0)
                (TRec (TFun T1 m T2)) Second) T1
             m) as tenv1.
    
    assert (val_type_tnt venv1 vx T1). { subst. eapply valtp_extend_tnt. eapply valtp_extend_tnt. eauto. }
    assert (wf_env_tnt venv1 tenv1). { subst. eapply wfe_tnt_env. eauto. eapply wfe_tnt_env. simpl. auto. eauto. eapply wf_idx_tnt. eapply wf_sanitize_tnt. eauto. eapply wf_idx_tnt. eapply wfe_tnt_env. simpl. auto. eauto. eapply wf_idx_tnt. eapply wf_sanitize_tnt. eauto. }
    specialize (IHW venv1 H1). destruct IHW as [v [? ?]]. exists v. split. eauto. eapply valtp_shrink_tnt. eapply valtp_shrink_tnt. subst. eauto. 
  - (* Case tunrec *)
    destruct (IHW2 _ WFE) as [v [HEV HVL]].
    simpl in HVL. destruct v; inversion HVL.
Qed.
