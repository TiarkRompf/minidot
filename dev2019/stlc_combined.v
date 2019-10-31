(* ############################################################ *)
(*                                                              *)
(*               Language definition for STLC 1/2               *)
(*                                                              *)
(* ############################################################ *)

(* Starting point: https://github.com/TiarkRompf/minidot/blob/master/dev2015/nano2.v *)
(* Starting point: https://github.com/TiarkRompf/scala-escape/blob/master/coq/stlc1.v *)

(* The goal of this version is to be as simple as possible. 
   No subtyping, env not part of val_type relation. *)

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

Definition classOf v := match v with V cl i => cl end.

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
  | vabs  : env vl -> class -> class -> tm -> vl (* the first class field describes the closure itself, the second one the class of the argument *)
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
        | tabs m y   => Some (Some (vabs (sanitize_env n env) n m y))
        | tapp ef ex   =>
           match teval k' env ef Second with
             | None => None
             | Some None => Some None
             | Some (Some (vbool _)) => Some None
             | Some (Some (vrec _)) => Some None (* NEW *)
             | Some (Some vcap) => Some None (* NEW *)
             | Some (Some (vabs env2 n m ey)) => (* NEW: vrec wrapper *)
                match teval k' env ex m with
                  | None => None
                  | Some None => Some None
                  | Some (Some vx) =>
                       teval k' (expand_env (expand_env env2 (vrec (vabs env2 n m ey)) Second) vx m) ey First
                end
           end
        | tunrec er ec => (* NEW *)
          match teval k' env er n with
          | None => None
          | Some None => Some None
          | Some (Some (vbool _)) => Some None
          | Some (Some (vabs _ _ _ _)) => Some None
          | Some (Some vcap) => Some None
          | Some (Some (vrec v)) =>
            match teval k' env ec n with (* should use Second instead of n? *)
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs _ _ _ _)) => Some None
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
    val_type v t ->
    wf_env vs ts ->
    get_inv_idx vs = get_inv_idx ts ->
    wf_env (expand_env vs v n) (expand_env ts t n)

with val_type : vl -> ty -> Prop := 
| v_bool: forall b,
    val_type (vbool b) TBool
| v_abs: forall venv tenv y T1 T2 n m, (* NEW: TRec wrapper *)
    wf_env venv tenv ->
    has_type (expand_env (expand_env tenv (TRec (TFun T1 m T2)) Second) T1 m) y First T2 ->
    val_type (vabs venv n m y) (TFun T1 m T2)
| v_rec: forall v T,  (* NEW *)
    val_type v T ->
    val_type (vrec v) (TRec T)
| v_cap:
    val_type vcap TCap (* NEW *)
.


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


Lemma lookup_safe_ex: forall H1 G1 TF x,
             wf_env H1 G1 ->
             lookup x G1 = Some TF ->
             exists v, lookup x H1 = Some v /\ val_type v TF.
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
          assert (exists v0, lookup (V First i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type v0 TF) as HI.
          eapply IHwf_env. simpl. rewrite E in H0. eauto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eauto. }
     * (* SSCase "Second". *)
       assert (exists v0, lookup (V First i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type v0 TF) as HI.
       eapply IHwf_env. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eauto.
   + (* SCase "VSnd". *) destruct n; simpl in H0; simpl in H2.
     * (* SSCase "First". *)
       assert (exists v0, lookup (V Second i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type v0 TF) as HI.
       eapply IHwf_env. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eauto.
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
          assert (exists v0, lookup (V Second i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type v0 TF) as HI.
          eapply IHwf_env. simpl. destruct (ble_nat tidx i). inversion H0. rewrite E in H0. rewrite H0. rewrite E. auto. auto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eauto. }
Qed.
  
Inductive res_type: option vl -> ty -> Prop :=
| not_stuck: forall v T,
      val_type v T ->
      res_type (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.


Lemma invert_abs: forall vf T1 n T2,
  val_type vf (TFun T1 n T2) ->
  exists env tenv y T3 T4 nf,
    vf = (vabs env nf n y) /\
    wf_env env tenv /\
    has_type (expand_env (expand_env tenv (TRec (TFun T3 n T4)) Second) T3 n) y First T4.
Proof.
  intros. inversion H. repeat eexists; repeat eauto.
Qed.


Lemma ext_sanitize_commute : forall {T} n venv (v:T) c,
   expand_env (sanitize_any venv n) v c = sanitize_any (expand_env venv v c) n.
Proof.
  intros. destruct venv0. destruct c; simpl; eauto. 
Qed.

Lemma wf_sanitize_any : forall n venv tenv,
   wf_env venv tenv ->
   wf_env (sanitize_any venv n) (sanitize_any tenv n).
Proof.
  intros. induction H.
  - simpl. eapply wfe_nil.
  - eapply wfe_cons in IHwf_env.
    rewrite <-ext_sanitize_commute. rewrite <-ext_sanitize_commute.
    eauto. eauto. eauto. 
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
  res_type res T.

Proof.
  intros k. induction k.
  (* 0 *)   intros. inversion H.
  (* S n *) intros. destruct e; inversion H; inversion H0. 
  
  - (* Case "True". *)  eapply not_stuck. eapply v_bool.
  - (* Case "False". *) eapply not_stuck. eapply v_bool.

  - (* Case "Var". *)
    subst.
    destruct (lookup_safe_ex (sanitize_env n venv0) (sanitize_env n tenv0) T v) as [va [I V]]; eauto. 

    rewrite I. eapply not_stuck. eapply V. 

  - (* Case "App". *)
    subst T. subst. remember (teval k venv0 e1 Second) as tf.
    destruct tf as [rf|]; try inversion H3. 
    assert (res_type rf (TFun T1 m T2)) as HRF. { eapply IHk; eauto. }
    inversion HRF as [vf TF HVF]. inversion HVF.
    subst rf. subst vf. 

    remember (teval k venv0 e2 m0) as tx.
    destruct tx as [rx|]; try inversion H3.
    assert (res_type rx T1) as HRX. { subst. eapply IHk; eauto. }
    inversion HRX as [vx]. subst rx T.

    subst. eapply IHk. eauto. eauto.
    (* WF on expanded env *)
    constructor. eauto. constructor. eauto. eauto. eauto. apply wf_idx. eauto. 

  - (* Case "Abs". *) intros. inversion H. inversion H0.
    eapply not_stuck. eapply v_abs; eauto.
    eauto.
  - (* Case "Rec". *)
    remember (teval k venv0 e1 n) as tevr.

    destruct tevr as [revr|]; try inversion H3.
    assert (res_type revr (TRec T)) as HRR. {
     subst. eapply IHk; eauto.
    }

    inversion HRR as [? vr]. inversion H10. subst.

    remember (teval k venv0 e2 n) as tevc. 
    destruct tevc as [revc|]; try inversion H11.
    assert (res_type revc TCap) as HRC. {
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
Fixpoint val_type_tnt (v:vl) (T:ty): Prop := match v, T with
| vbool b, TBool => True
| vabs env clf clv y, TFun T1 clt T2 => (clv = clt) /\
  (forall vx, val_type_tnt vx T1 ->
     exists v, tevaln (expand_env (expand_env env (vrec (vabs env clf clv y)) Second) vx clv) y First v /\ val_type_tnt v T2)
| vrec v, TRec T => True (* NEW: rec, but we can't do anything with it *)
| _,_ => False
end.


Inductive wf_env_tnt : venv -> tenv -> Prop := 
| wfe_tnt_nil : forall n, wf_env_tnt (Def vl nil nil n) (Def ty nil nil n)
| wfe_tnt_env : forall v t vs ts n,
    val_type_tnt v t ->
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



Lemma lookup_safe_ex_tnt: forall H1 G1 TF x,
             wf_env_tnt H1 G1 ->
             lookup x G1 = Some TF ->
             exists v, lookup x H1 = Some v /\ val_type_tnt v TF.
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
          assert (exists v0, lookup (V First i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type_tnt  v0 TF) as HI.
          eapply IHwf_env_tnt. simpl. rewrite E in H0. eauto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eauto. }
     * (* SSCase "Second". *)
       assert (exists v0, lookup (V First i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type_tnt v0 TF) as HI.
       eapply IHwf_env_tnt. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eauto. 
   + (* SCase "VSnd". *) destruct n; simpl in H0; simpl in H2.
     * (* SSCase "First". *)
       assert (exists v0, lookup (V Second i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type_tnt v0 TF) as HI.
       eapply IHwf_env_tnt. simpl. eauto.
       inversion HI as [v0 HI1]. inversion HI1.
       eexists. econstructor. eapply lookup_extend; eauto. eauto.
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
          assert (exists v0, lookup (V Second i) (Def vl vl1 vl2 vidx) = Some v0 /\ val_type_tnt v0 TF) as HI.
          eapply IHwf_env_tnt. simpl. destruct (ble_nat tidx i). inversion H0. rewrite E in H0. rewrite H0. rewrite E. auto. auto.
          inversion HI as [v0 HI1]. inversion HI1.
          eexists. econstructor. eapply lookup_extend; eauto. eauto. }
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
    eauto. eauto. eauto. 
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
  exists v, tevaln venv e cl v /\ val_type_tnt v T.

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

    exists v. split. exists 0. intros. destruct n0. omega. simpl. rewrite I. eauto. eapply V.

  - (* Case "App". *)
    destruct (IHW1 venv0 WFE) as [vf [IW1 HVF]].
    destruct (IHW2 venv0 WFE) as [vx [IW2 HVX]].

    simpl in HVF. destruct vf; try contradiction.    
    destruct HVF  as [? IHF].

    destruct (IHF vx HVX) as [vy [IW3 HVY]].

    exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n0. omega. simpl. subst c0.
      rewrite IWF. rewrite IWX. rewrite IWY. eauto.
      omega. omega. omega.
    }
    eapply HVY.
    
  - (* Case "Abs". *)
    eexists. split. exists 0. intros. destruct n0. omega. simpl. eauto.
    simpl. repeat split; eauto. intros. 

    eapply IHW.
    constructor. eauto. constructor. simpl; eauto. eauto.
    eapply wf_idx_tnt. eauto. eapply wf_idx_tnt.
    constructor. simpl; eauto. eauto. eapply wf_idx_tnt. eauto. 
    
  - (* Case tunrec *)
    destruct (IHW2 _ WFE) as [v [HEV HVL]].
    simpl in HVL. destruct v; inversion HVL.
Qed.


(* ############################################################ *)
(*                                                              *)
(*         Combined soundness and termination proof             *)
(*                                                              *)
(* ############################################################ *)


(* ### Value typing and well-typed runtime environments ### *)
(*
(* Termination part *)
(* need to use Fixpoint because of positivity restriction *)
Fixpoint val_type_tnt (v:vl) (T:ty): Prop := match v, T with
| vbool b, TBool => True
| vabs env clv y, TFun T1 clt T2 => (clv = clt) /\
  (forall vx, val_type_tnt vx T1 ->
     exists v, tevaln (expand_env (expand_env env (vrec (vabs env clv y)) Second) vx clv) y First v /\ val_type_tnt v T2)
| vrec v, TRec T => True (* NEW: rec, but we can't do anything with it *)
| _,_ => False
end.



Inductive wf_env : venv -> tenv -> Prop := 
| wfe_nil : forall n, wf_env (Def vl nil nil n) (Def ty nil nil n)
| wfe_cons : forall v t vs ts n,
    val_type v t ->
    wf_env vs ts ->
    get_inv_idx vs = get_inv_idx ts ->
    wf_env (expand_env vs v n) (expand_env ts t n)

with val_type : vl -> ty -> Prop := 
| v_bool: forall b,
    val_type (vbool b) TBool
| v_abs: forall venv tenv y T1 T2 m, (* NEW: TRec wrapper *)
    wf_env venv tenv ->
    has_type (expand_env (expand_env tenv (TRec (TFun T1 m T2)) Second) T1 m) y First T2 ->
    val_type (vabs venv m y) (TFun T1 m T2)
| v_rec: forall v T,  (* NEW *)
    val_type v T ->
    val_type (vrec v) (TRec T)
| v_cap:
    val_type vcap TCap (* NEW *)
.
*)


Inductive wf_env_comb : venv -> tenv -> Prop := 
| wfe_comb_nil : forall n, wf_env_comb (Def vl nil nil n) (Def ty nil nil n)
| wfe_comb_env : forall v t vs ts n,
    val_type_snd v t /\ ((n = Second) \/ val_type_tnt v t) ->
    wf_env_comb vs ts ->
    get_inv_idx vs = get_inv_idx ts ->
    wf_env_comb (expand_env vs v n) (expand_env ts t n)
with val_type_snd : vl -> ty -> Prop := 
| v_bool2: forall b,
    val_type_snd (vbool b) TBool
| v_abs2: forall venv tenv y T1 T2 n m, (* NEW: TRec wrapper *)
    wf_env_comb venv tenv ->
    has_type (expand_env (expand_env tenv (TRec (TFun T1 m T2)) Second) T1 m) y First T2 ->
    val_type_snd (vabs venv n m y) (TFun T1 m T2)
| v_rec2: forall v T,  (* NEW *)
    val_type_snd v T ->
    val_type_snd (vrec v) (TRec T)
| v_cap2:
    val_type_snd vcap TCap (* NEW *)
.


Definition val_type_comb n v T := val_type_snd v T /\ ((n = Second) \/ val_type_tnt v T).


Inductive res_type_snd: option vl -> ty -> Prop :=
| not_stuck2: forall v T,
      val_type_snd v T ->
      res_type_snd (Some v) T.

Hint Constructors res_type_snd.
Hint Resolve not_stuck2.


Lemma wf_length_comb : forall vs ts,
      wf_env_comb vs ts ->
      length_env First vs = length_env First ts /\ length_env Second vs = length_env Second ts.
Proof.
  intros. induction H; auto.
  destruct IHwf_env_comb as [L R].
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

Lemma lookup_safe_ex_comb: forall H1 G1 TF cl x,
             wf_env_comb (sanitize_env cl H1) (sanitize_env cl G1) ->
             lookup x (sanitize_env cl G1) = Some TF ->
             exists v, lookup x (sanitize_env cl H1) = Some v /\ val_type_comb (classOf x) v TF.
Proof. admit. Admitted.

Lemma wf_idx_comb : forall vs ts,
      wf_env_comb vs ts ->
      get_inv_idx vs = get_inv_idx ts.
Proof.
  intros. induction H; auto.
  destruct vs; destruct ts; destruct n; auto.
Qed.

Hint Immediate wf_idx_comb.

Lemma wf_sanitize_any_comb : forall n venv tenv,
   wf_env_comb venv tenv ->
   wf_env_comb (sanitize_any venv n) (sanitize_any tenv n).
Proof.
  intros. induction H.
  - simpl. eapply wfe_comb_nil.
  - eapply wfe_comb_env in IHwf_env_comb.
    rewrite <-ext_sanitize_commute. rewrite <-ext_sanitize_commute.
    eauto. eauto. eauto. 
Qed.  

Lemma wf_sanitize_comb : forall n venv tenv,
   wf_env_comb venv tenv ->
   wf_env_comb (sanitize_env n venv) (sanitize_env n tenv).
Proof.
  intros. destruct n; unfold sanitize_env. destruct venv0. destruct tenv0.
  assert (length l0 = length l2). apply wf_length_comb in H; destruct H as [L R]; eauto.
  rewrite H0. eapply wf_sanitize_any_comb. eauto.
  eauto.
Qed.
  

Hint Immediate wf_sanitize_comb.

(*
Theorem full_total_safety : forall e cl tenv T,
  has_type tenv e cl T -> forall venv, wf_env_tnt venv tenv ->
  exists v, tevaln venv e cl v /\ val_type_tnt v T.
 *)

Definition is_sanitized {X} (env: env X) := exists env', env = sanitize_env First env'.


Theorem full_combined_safety : forall k e n tenv T,
  has_type tenv e n T -> forall venv, wf_env_comb venv tenv ->
  (forall res, teval k venv e n = Some res -> res_type_snd res T) /\
  (k = 0 \/ (is_sanitized tenv -> is_sanitized venv ->
            exists v, tevaln venv e n v /\ val_type_tnt v T)).
Proof.
  intros k. induction k.
  (* 0 *)   split. intros. inversion H1. left. auto. 
  (* S n *) intros e n tenv t H. induction H; (intros; split; [intros; subst|subst;right;intros;subst]).
  - (* True *) inversion H0. eapply not_stuck2. constructor.
  - eexists. split. exists 0. intros. destruct n0. omega. simpl. eauto. simpl. eauto.
  - (* False *) inversion H0. eapply not_stuck2. constructor.
  - eexists. split. exists 0. intros. destruct n0. omega. simpl. eauto. simpl. eauto.
  - (* Var *)
    destruct (lookup_safe_ex_comb venv0 env0 T1 n x) as [vl [IL [VLS VLT]]]. eauto. eauto.
    inversion H1. rewrite IL. eapply not_stuck2. eauto.
  - destruct (lookup_safe_ex_comb venv0 env0 T1 n x) as [vl [IL [VLS VLT]]]. eauto. eauto.
    (* n = Second --> can't happen! *)
    (* helpers: *)
    assert (forall {X} (env: env X) n, is_sanitized env -> sanitize_env n env = env) as L1. admit.
    assert (forall {X} (env: env X) x v, is_sanitized env -> lookup x env = Some v -> classOf x = First) as L2. admit. 
    destruct VLT as [FALSE|VLT]. { rewrite L1 in IL; eauto. rewrite (L2 _ venv0 _ vl) in FALSE. inversion FALSE. eauto. eauto. }
    exists vl. split. exists 0. intros. destruct n0. omega. unfold teval. rewrite IL. eauto. eauto. 
  - (* App *) simpl in  H2.
    (* function *)
    remember (teval k venv0 f Second) as tf.
    destruct tf as [rf|]; try inversion H2. 
    assert (res_type_snd rf (TFun T1 m T2)) as HRF. { eapply IHk; eauto. }
    inversion HRF as [vf TF HVF]. inversion HVF.
    subst rf. subst vf. 

    (* argument *)
    remember (teval k venv0 x m0) as tx.
    destruct tx as [rx|]; try inversion H2.
    assert (res_type_snd rx T1) as HRX. { subst. eapply IHk; eauto. }
    inversion HRX as [vx]. subst rx T.

    (* termination part for argument *)
    assert (m0 = Second \/ val_type_tnt vx T1) as HRXT. { subst. 
      destruct (IHk _ _ _ _ H0 _ H1) as [IHS [|]].
      destruct k. simpl in Heqtf. inversion Heqtf. inversion H5.
      admit.
      (* NEED: is_sanitized evidence in function *)
      (* NEED: deterministic execution *)
      (* destruct IHT as [vx2 [TEV VTT]].
      unfold tevaln in TEV.
      assert (vx = vx2). admit. (* TODO! need a deterministc exec theorem, or extend IH ? *)
      subst. eauto. *)
    }
    
    (* body *)
    subst. eapply IHk. eauto. 
    (* WF on expanded env *)
    constructor. split; eauto. constructor. split; eauto.
    eapply v_rec2. eauto. eauto. apply wf_idx_comb. eauto.
    eapply wf_idx_comb. constructor. split. constructor. eauto.
    (* NOTE: rec ref always 2nd class here! *)
    left. eauto. eauto.
    eauto. eauto. 
    
  - rename H1 into WFE.
    (* --- OLD ATTEMPT NOTES (trying to prov term only for 1st cl context --- *)
    (* PROBLEM: fun evaluated as 2nd class --> no termination evidence *)
    (* PROBLEM: same for argument if 2nd class --> proof idea doesn't work!*)
    (* We can't restrict to 1st-class contexts. 1st-class just means that
       this expression cannot _leak_ a capability, but it can _use_ a
       capability through 2nd-class subexpressions (and thus diverge).  
       
       What we (most likely) want is slightly different: in an environment
       that's _restricted_ to only 1st class bindings (which is what we use
       for closures and most likely need for terms in types as well)
       everything terminates.
     *)
    
    destruct (IHhas_type1 venv0 WFE) as [IHS1 [FALSE|IHT1]].
    inversion FALSE. destruct (IHT1 H2 H3) as [vf [IW1 HVF]].
    destruct (IHhas_type2 venv0 WFE) as [IHS2 [FALSE|IHT2]].
    inversion FALSE. destruct (IHT2 H2 H3) as [vx [IW2 HVX]].

    simpl in HVF. destruct vf; try contradiction.    
    destruct HVF  as [? IHF].

    destruct (IHF vx HVX) as [vy [IW3 HVY]].

    exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n0. omega. simpl. subst c0.
      rewrite IWF. rewrite IWX. rewrite IWY. eauto.
      omega. omega. omega.
    }
    eapply HVY.

  - (* ABS *)
    inversion H1. eapply not_stuck2.  eapply v_abs2. eapply wf_sanitize_comb. eauto.
    eauto. 
    
  - eexists. split. exists 0. intros. destruct n0. omega. simpl. eauto.
    simpl. repeat split; eauto. intros. 

    assert (val_type_snd vx T1). admit.
    (* PROBLEM: we have no evidence of the soundness val_type for the arg!
       Cannot do induction. We need this for the extended wf_env. *)

    assert (val_type_snd (vrec (vabs (sanitize_env n venv0) n m y))
                         (TRec (TFun T1 m T2))). {
      eapply v_rec2. eapply v_abs2. eapply wf_sanitize_comb. eauto. eauto.
    }
    
    destruct (IHhas_type  (expand_env
         (expand_env (sanitize_env n venv0)
            (vrec (vabs (sanitize_env n venv0) n m y)) Second) vx
         m)) as [HHS HHT]. 
    constructor. split. eauto. right. eauto. constructor. eauto. eauto. 
    eapply wf_idx_comb. eauto. eapply wf_idx_comb.
    constructor. split. eauto. left. eauto. eauto.
    eapply wf_idx_comb. eauto. 

    destruct HHT as [FALSE|HHT]. inversion FALSE.

    eapply HHT.
    (* PROBLEM/QUESTION: need is_sanitized for IH, don't know if can be expanded. *)
    (* Of course a function can diverge if the argument itself is a cap. *)

    admit. admit. 

  - (* Rec *)
    inversion H2.
    remember (teval k venv0 tr n) as tevr.

    destruct tevr as [revr|]; try inversion H4.
    assert (res_type_snd revr (TRec T1)) as HRR. {
      subst. eapply IHk. eauto. eauto. eauto. 
    }

    inversion HRR as [? vr]. inversion H3. subst.

    remember (teval k venv0 tc n) as tevc. 
    destruct tevc as [revc|]; try inversion H5.
    assert (res_type_snd revc TCap) as HRC. {
      subst. eapply IHk; eauto.
    }
    inversion HRC as [? vc]; inversion H6. subst.
    (* NOTE: if there is no val_type case for vcap this inversion fails
    and recursion is impossible in well-formed envs *)
    
    inversion H4. subst. eauto. 
  - destruct (IHhas_type2 _ H1) as [IHS [FALSE|HVL]]. inversion FALSE.
    destruct (HVL H2 H3) as [v [? FALSE]].
    simpl in FALSE. destruct v; inversion FALSE.
Admitted.
    
(* TODO:
- remaining easy cases
- try recursive def of valtp-snd/tnt
- switch gears, try d_sub with full term dep 
*)


(* New attempt: inductively translate val_type to val_type_tnt *)

Check val_type_ind. 

Scheme Induction for val_type Sort Prop
  with Induction for wf_env Sort Prop. 

Check val_type_ind_dep.

Theorem strengthen_tnt:
  (forall v T, val_type v T -> val_type_tnt v T).
  (* (forall venv tenv, wf_env venv tenv -> wf_env_tnt venv tenv). *)
Proof.
  apply (val_type_ind_dep
           (fun v T vt => val_type_tnt v T)
           (fun venv tenv wt => wf_env_tnt venv tenv)
        )
  ; intros.
  - (* bool *) simpl. eauto.
  - (* abs *) simpl.  
    split. eauto. intros.
    eapply full_total_safety. eauto. constructor. eauto. constructor.
    simpl. eauto. eauto. eauto. eapply wf_idx_tnt.
    constructor. simpl. eauto. eauto. eauto.
  - (* rec *) simpl. eauto.
  - (* cap *) admit. (* NOT SUPPORTED! *)
  - (* wf nil *) eauto.
  - (* wf cons *) eauto. 
Admitted.
