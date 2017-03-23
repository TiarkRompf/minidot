(* Full safety for STLC *)
(* values well-typed with respect to runtime environment *)
(* inversion lemma structure *)
(* subtyping (in addition to nano2.v) *)
(* singleton types (in addtion to nano4-1.v *)

(* full proof for singleton types! *)
(* added stp_vary rule *)

(* TODO: type members *)
(* TODO: dependent application *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Module STLC.

Definition id := nat.


Inductive ty : Type :=
  | TBool  : ty           
  | TFun   : ty -> ty -> ty
  | TVar   : id -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.

Hint Unfold venv.
Hint Unfold tenv.

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.


Inductive closed: nat -> ty -> Prop :=
| cl_bool: forall k,
    closed k TBool
| cl_fun: forall k T1 T2,
    closed k T1 ->
    closed k T2 ->
    closed k (TFun T1 T2)
| cl_selb: forall k x,
    k > x ->
    closed k (TVar x)
.

Inductive stp: tenv -> ty -> ty -> Prop :=
| stp_bool: forall G1,
    stp G1 TBool TBool
| stp_fun: forall G1 T1 T2 T3 T4,
    stp G1 T3 T1 ->
    stp G1 T2 T4 ->
    stp G1 (TFun T1 T2) (TFun T3 T4)
| stp_varx: forall G1 x,
    x < length G1 ->
    stp G1 (TVar x) (TVar x)
| stp_vary: forall G1 x y,
    index x G1 = Some (TVar y) ->
    y < length G1 ->
    stp G1 (TVar y) (TVar x)
| stp_var1: forall G1 x T1,
    index x G1 = Some T1 ->
    stp G1 (TVar x) T1
.


Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_varx: forall x env T1,
    index x env = Some T1 -> (* could use closed *)
    has_type env (tvar x) (TVar x)
(*| t_var: forall x env T1,
    index x env = Some T1 ->
    has_type env (tvar x) T1*)
| t_app: forall env f x T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env x T1 ->
    has_type env (tapp f x) T2
| t_abs: forall env y T1 T2,
    has_type (T1::(TFun T1 T2)::env) y T2 ->
    closed (length env) (TFun T1 T2) ->       
    has_type env (tabs y) (TFun T1 T2)
| t_sub: forall env x T1 T2,
    has_type env x T1 ->
    stp env T1 T2 ->
    has_type env x T2
.

Inductive stp2: venv -> ty -> venv -> ty -> nat -> Prop :=
| stp2_bool: forall G1 G2 n1,
    stp2 G1 TBool G2 TBool (S n1)
| stp2_fun: forall G1 G2 T1 T2 T3 T4 n1 n2,
    stp2 G2 T3 G1 T1 n1 ->
    stp2 G1 T2 G2 T4 n2 ->
    stp2 G1 (TFun T1 T2) G2 (TFun T3 T4) (S (n1+n2))
| stp2_varx: forall G1 G2 x1 x2 v n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 G1 (TVar x1) G2 (TVar x2) (S n1)
| stp2_var1: forall G1 GX TX G2 x T2 v n1,
    index x G1 = Some v ->
    val_type0 GX v TX -> (* slack for: val_type G2 v T2 *)
    stp2 GX TX G2 T2 n1 ->
    stp2 G1 (TVar x) G2 T2 (S n1)

         
with wf_env : venv -> tenv -> Prop := 
| wfe_nil : wf_env nil nil
| wfe_cons : forall v t vs ts,
    val_type (v::vs) v t ->
    wf_env vs ts ->
    wf_env (cons v vs) (cons t ts)

with val_type0 : venv -> vl -> ty -> Prop :=
| v_bool: forall b,
    val_type0 [] (vbool b) TBool
| v_abs: forall venv tenv y T1 T2,
    wf_env venv tenv ->
    has_type (T1::(TFun T1 T2)::tenv) y T2 ->
    val_type0 venv (vabs venv y) (TFun T1 T2)
| v_var: forall venv x v,
    index x venv = Some v ->
    val_type0 venv v (TVar x)

with val_type : venv -> vl -> ty -> Prop :=
| v_sub: forall G1 T1 G2 T2 v,
    val_type0 G1 v T1 ->
    (exists n, stp2 G1 T1 G2 T2 n) ->
    val_type G2 v T2
.
              


Definition stpd2 G1 T1 G2 T2 := exists n, stp2 G1 T1 G2 T2 n.

Hint Constructors stp2.

Ltac ep := match goal with
             | [ |- stp2 ?G1 ?T1 ?G2 ?T2 ?N ] => assert (exists (n:nat), stp2 G1 T1 G2 T2 n) as EEX
           end.

Ltac eu := match goal with
             | H: stpd2 _ _ _ _ |- _ => destruct H as [? H]
           end.

Lemma stpd2_bool: forall G1 G2,
    stpd2 G1 TBool G2 TBool.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_fun: forall G1 G2 T1 T2 T3 T4,
    stpd2 G2 T3 G1 T1 ->
    stpd2 G1 T2 G2 T4 ->
    stpd2 G1 (TFun T1 T2) G2 (TFun T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.
Lemma stpd2_varx: forall G1 G2 x1 x2 v,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stpd2 G1 (TVar x1) G2 (TVar x2).
Proof. intros. repeat eu. exists 1. eauto. Qed.
Lemma stpd2_var1: forall G1 GX TX G2 x T2 v,
    index x G1 = Some v ->
    val_type0 GX v TX -> (* slack for: val_type G2 v T2 *)
    stpd2 GX TX G2 T2 ->
    stpd2 G1 (TVar x) G2 T2.
Proof. intros. repeat eu. eexists. eauto. Qed.




(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v

Could use do-notation to clean up syntax.
*)

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (index x env)
        | tabs y     => Some (Some (vabs env y))
        | tapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vbool _)) => Some None
                | Some (Some (vabs env2 ey)) =>
                  teval n (vx::(vabs env2 ey)::env2) ey
              end
          end
      end
  end.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
Hint Constructors stp2.
Hint Constructors val_type.
Hint Constructors wf_env.

Hint Unfold stpd2.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.


Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.





Lemma wf_length : forall vs ts,
                    wf_env vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  assert ((length (v::vs)) = 1 + length vs). constructor.
  assert ((length (t::ts)) = 1 + length ts). constructor.
  rewrite IHwf_env in H1. auto.
Qed.

Hint Immediate wf_length.

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


Lemma stp2_extend : forall v1 G1 G2 T1 T2 n,
                      stp2 G1 T1 G2 T2 n ->
                      stp2 (v1::G1) T1 G2 T2 n /\
                      stp2 G1 T1 (v1::G2) T2 n /\
                      stp2 (v1::G1) T1 (v1::G2) T2 n.
Proof.
  intros. induction H; repeat split; econstructor; try eapply IHstp2_1; try eapply IHstp2_2; try eapply index_extend; eauto; try eapply IHstp2; eauto.
Qed.

Lemma stpd2_extend : forall v1 G1 G2 T1 T2,
                      stpd2 G1 T1 G2 T2 ->
                      stpd2 (v1::G1) T1 G2 T2 /\
                      stpd2 G1 T1 (v1::G2) T2 /\
                      stpd2 (v1::G1) T1 (v1::G2) T2.
Proof.
  intros. repeat eu. repeat split; eexists; eapply stp2_extend; eauto.
Qed.


Lemma stp2_extend1 : forall v1 G1 G2 T1 T2 n, stp2 G1 T1 G2 T2 n -> stp2 (v1::G1) T1 G2 T2 n.
Proof. intros. eapply stp2_extend. eauto. Qed.

Lemma stp2_extend2 : forall v1 G1 G2 T1 T2 n, stp2 G1 T1 G2 T2 n -> stp2 G1 T1 (v1::G2) T2 n.
Proof. intros. eapply stp2_extend. eauto. Qed.

Lemma stpd2_extend1 : forall v1 G1 G2 T1 T2, stpd2 G1 T1 G2 T2 -> stpd2 (v1::G1) T1 G2 T2.
Proof. intros. eapply stpd2_extend. eauto. Qed.

Lemma stpd2_extend2 : forall v1 G1 G2 T1 T2, stpd2 G1 T1 G2 T2 -> stpd2 G1 T1 (v1::G2) T2.
Proof. intros. eapply stpd2_extend. eauto. Qed.



Lemma stpd2_closed : forall G1 G2 T1 T2,
                      stpd2 G1 T1 G2 T2 ->
                      closed (length G1) T1 /\
                      closed (length G2) T2.
Proof.
  intros. eu. induction H; repeat split; try  econstructor; try eapply IHstp2_1; try eapply IHstp2_2; eauto; try eapply IHstp2; eauto; try eapply index_max; eauto.
Qed.



Lemma valtp_extend : forall vs v v1 T,
                       val_type vs v T ->
                       val_type (v1::vs) v T.
Proof.
  intros. induction H; econstructor; eauto; try eapply stpd2_extend; eauto; try eapply index_extend; eauto. 
Qed.



Lemma index_safe_ex: forall H1 G1 TF i,
             wf_env H1 G1 ->
             index i G1 = Some TF ->
             exists v, index i H1 = Some v /\ val_type H1 v TF.
Proof. intros. induction H.
       Case "nil". inversion H0.
       Case "cons". inversion H0.
         case_eq (beq_nat i (length ts)).
           SCase "hit".
             intros E.
             rewrite E in H3. inversion H3. subst t.
             assert (beq_nat i (length vs) = true). eauto.
             assert (index i (v :: vs) = Some v). eauto.  unfold index. rewrite H2. eauto.
             eauto.
           SCase "miss".
             intros E.
             assert (beq_nat i (length vs) = false). eauto.
             rewrite E in H3.
             assert (exists v0, index i vs = Some v0 /\ val_type vs v0 TF) as HI. eapply IHwf_env. eauto.
           inversion HI as [v0 HI1]. inversion HI1. 
           eexists. econstructor. eapply index_extend; eauto. eapply valtp_extend; eauto.
Qed.

  
Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.


Lemma stpd2_refl: forall G1 T1,
  closed (length G1) T1 ->
  stpd2 G1 T1 G1 T1.
Proof.
  intros. induction T1; inversion H.
  - Case "bool". eapply stpd2_bool; eauto.
  - Case "fun". eapply stpd2_fun; eauto.
  - Case "var".
    assert (exists v, index i G1 = Some v) as E. eapply index_exists; eauto.
    destruct E.
    eapply stpd2_varx; eauto.
Qed.


Lemma stpd2_reg1 : forall G1 G2 T1 T2,
                      stpd2 G1 T1 G2 T2 ->
                      stpd2 G1 T1 G1 T1.
Proof.
  intros. eapply stpd2_refl. eapply (stpd2_closed G1 G2). eauto.
Qed.

Lemma stpd2_reg2 : forall G1 G2 T1 T2,
                      stpd2 G1 T1 G2 T2 ->
                      stpd2 G2 T2 G2 T2.
Proof.
  intros. eapply stpd2_refl. eapply (stpd2_closed G1 G2). eauto.
Qed.



Lemma stp2_trans: forall n, forall G1 G2 G3 T1 T2 T3 n1 n2,
  stp2 G1 T1 G2 T2 n1 -> 
  stp2 G2 T2 G3 T3 n2 ->
  (n1+n2) < n ->
  stpd2 G1 T1 G3 T3.
Proof.
  intros n. induction n; intros. solve by inversion.
  inversion H.
  - Case "bool". inversion H0; subst; try solve by inversion.
    + SCase "bool". eapply stpd2_bool; eauto.
  - Case "fun". inversion H0; subst; try solve by inversion.
    + SCase "fun". inversion H12. subst. eapply stpd2_fun; eauto; try eapply IHn; eauto; try omega.
  - Case "varx". inversion H0; subst; try solve by inversion.
    + SCase "varx". inversion H12. subst. rewrite H3 in H9. inversion H9. subst. eapply stpd2_varx; eauto.
    + SCase "var1". inversion H13. subst. rewrite H3 in H9. inversion H9. subst. eapply stpd2_var1; eauto.
  - Case "var1".
    eapply stpd2_var1; eauto. eapply IHn; eauto. omega.
Qed.

Lemma stpd2_trans: forall G1 G2 G3 T1 T2 T3,
  stpd2 G1 T1 G2 T2 ->
  stpd2 G2 T2 G3 T3 ->
  stpd2 G1 T1 G3 T3.
Proof.
  intros. repeat eu. eapply stp2_trans; eauto.
Qed.

Lemma invert_var1: forall n, forall venv v x GX TX n1,
  val_type0 GX v TX -> stp2 GX TX venv (TVar x) n1 -> n1 < n ->
  index x venv = Some v.
Proof.
  intros n. induction n; intros. solve by inversion.
  inversion H; subst. 
  - Case "bool". solve by inversion.
  - Case "fun". solve by inversion.
  - Case "var". subst. inversion H0; subst.
    + SCase "varx".
      assert (v = v0) as A. rewrite H2 in H6. inversion H6. eauto.
      rewrite A. eauto.
    + SCase "var1".
      assert (v = v0) as A. rewrite H2 in H4. inversion H4. eauto.
      rewrite A. eapply IHn; eauto. omega.
Qed.

Lemma invert_var: forall venv v x,
  val_type venv v (TVar x) ->
  index x venv = Some v.
Proof.
  intros. inversion H. ev. eapply invert_var1; eauto.
Qed.

Lemma stp_to_stpd2: forall G1 T1 T2,
  stp G1 T1 T2 ->
  forall GX, wf_env GX G1 -> 
  stpd2 GX T1 GX T2.
Proof.
  intros G1 T1 T2 H. induction H; intros.
  - Case "bool". eapply stpd2_bool; eauto.
  - Case "fun".  eapply stpd2_fun; eauto.
  - Case "varx".
    assert (exists v, index x GX = Some v) as E. eapply index_exists. rewrite (wf_length GX G1). eauto. eauto. 
    destruct E.
    eapply stpd2_varx; eauto.
  - Case "vary".
    assert (exists v, index x GX = Some v /\ val_type GX v (TVar y)) as E. eapply index_safe_ex; eauto.
    destruct E. destruct H2. inversion H3. subst.
    eapply stpd2_varx. eapply invert_var. eauto. eauto.
  - Case "var1".
    assert (exists v, index x GX = Some v /\ val_type GX v T1) as E. eapply index_safe_ex; eauto. 
    destruct E. destruct H1. destruct H2. 
    eapply stpd2_var1. eauto. eauto. eauto.
Qed.


Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stpd2 H1 T1 H2 T2 ->
  val_type H2 vf T2.
Proof.
  intros.  inversion H.
  - econstructor; eauto. eapply stpd2_trans; eauto.
Qed.

Lemma restp_widen: forall vf H1 H2 T1 T2,
  res_type H1 vf T1 ->
  stpd2 H1 T1 H2 T2 ->
  res_type H2 vf T2.
Proof.
  intros. inversion H. eapply not_stuck. eapply valtp_widen; eauto.
Qed.


Lemma invert_abs1: forall n, forall venv vf T1 T2 GX TX n1,
  val_type0 GX vf TX -> stp2 GX TX venv (TFun T1 T2) n1 -> n1 < n ->
  exists env tenv y T3 T4,
    vf = (vabs env y) /\ 
    wf_env env tenv /\
    has_type (T3::(TFun T3 T4)::tenv) y T4 /\
    stpd2 venv T1 env T3 /\
    stpd2 env T4 venv T2.
Proof.
  intros n. induction n; intros. solve by inversion.
  inversion H; subst. 
  - Case "bool". solve by inversion.
  - Case "fun". subst. inversion H0. subst. repeat eexists; eauto.
  - Case "var". subst. inversion H0. subst.
    assert (vf = v) as A. rewrite H2 in H4. inversion H4. eauto.
    rewrite A. eapply IHn; eauto. omega.
Qed.


Lemma invert_abs: forall venv vf T1 T2,
  val_type venv vf (TFun T1 T2) ->
  exists env tenv y T3 T4,
    vf = (vabs env y) /\ 
    wf_env env tenv /\
    has_type (T3::(TFun T3 T4)::tenv) y T4 /\
    stpd2 venv T1 env T3 /\
    stpd2 env T4 venv T2.
Proof.
  intros. inversion H. ev. eapply invert_abs1; eauto. 
Qed.


(* if not a timeout, then result not stuck and well-typed *)

Theorem full_safety : forall n e tenv venv res T,
  teval n venv e = Some res -> has_type tenv e T -> wf_env venv tenv ->
  res_type venv res T.

Proof.
  intros n. induction n.
  (* 0 *)   intros. inversion H.
  (* S n *) intros. destruct e; inversion H.

  - Case "True".
    remember (ttrue) as e. induction H0; inversion Heqe; subst.
    + eapply not_stuck. eapply v_sub; eauto. eapply v_bool; eauto.
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stp_to_stpd2; eauto. 

  - Case "False".
    remember (tfalse) as e. induction H0; inversion Heqe; subst.
    + eapply not_stuck. eapply v_sub; eauto. eapply v_bool; eauto.
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stp_to_stpd2; eauto. 
  
  - Case "Var".
    remember (tvar i) as e. induction H0; inversion Heqe; subst.
    + destruct (index_safe_ex venv0 env T1 i) as [v [I V]]; eauto. (* Var *)
      rewrite I. eapply not_stuck. destruct V. eapply v_sub. eapply v_var. eauto. eapply stpd2_varx. eauto. eauto. 
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stp_to_stpd2; eauto. 

  - Case "App".
    remember (tapp e1 e2) as e. induction H0; inversion Heqe; subst.
    +
      remember (teval n venv0 e1) as tf.
      remember (teval n venv0 e2) as tx. 
    
      destruct tx as [rx|]; try solve by inversion.
      assert (res_type venv0 rx T1) as HRX. SCase "HRX". subst. eapply IHn; eauto.
      inversion HRX as [? vx]. 

      destruct tf as [rf|]; subst rx; try solve by inversion.  
      assert (res_type venv0 rf (TFun T1 T2)) as HRF. SCase "HRF". subst. eapply IHn; eauto.
      inversion HRF as [? vf].

      destruct (invert_abs venv0 vf T1 T2) as
          [env1 [tenv [y0 [T3 [T4 [EF [WF [HTY [STX STY]]]]]]]]]. eauto.
      (* now we know it's a closure, and we have has_type evidence *)

      assert (res_type (vx::vf::env1) res T4) as HRY.
        SCase "HRY".
          subst. eapply IHn. eauto. eauto.
          (* wf_env f x *) econstructor. eapply valtp_widen; eauto. eapply stpd2_extend2; eauto. eapply stpd2_extend2; eauto.
          (* wf_env f   *) econstructor. eapply v_sub. eapply v_abs; eauto. eapply stpd2_extend2. eapply stpd2_fun. eapply stpd2_reg2; eauto. eapply stpd2_reg1; eauto.
          eauto.

      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto. eapply stpd2_extend1. eapply stpd2_extend1. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stp_to_stpd2; eauto. 

    
  - Case "Abs". 
    remember (tabs e) as xe. induction H0; inversion Heqxe; subst.
    + eapply not_stuck. eapply v_sub. eapply v_abs; eauto. eapply stpd2_refl. rewrite (wf_length venv0 env). eauto. eauto. 
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stp_to_stpd2; eauto. 

Grab Existential Variables.
apply 0. apply 0. 
Qed.

End STLC.