(* Full safety for STLC *)

(* copied from nano0.v *)

(* This version prohibits recursion, and we prove that   *)
(* evaluation always terminates with a well-typed value. *)
(* From this follows both type soundness and strong      *)
(* normalization for STLC.                               *)

(* copied from nano0-total.v *)
(* copied from nano0-total-lr.v *)

(* This version enables recursion again, and we use a    *)
(* step-indexed logical relation to show soundness only. *)

(* Note: we need actual step-indexes, not depth fuel !!! *)


Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Module STLC.

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> ty -> ty
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

Fixpoint length {X: Type} (l : list X): nat :=
  match l with
    | [] => 0
    | _::l' => 1 + length l'
  end.

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if eq_nat_dec n (length l') then Some a else index n l'
  end.


Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           index x env = Some T1 ->
           has_type env (tvar x) T1
| t_app: forall env f x T1 T2,
           has_type env f (TFun T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
| t_abs: forall env y T1 T2,
           has_type (T1::(TFun T1 T2)::env) y T2 -> 
           has_type env (tabs y) (TFun T1 T2)
.


(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

(* this step-indexed version returns the number of steps taken (always <= fuel) *)

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: (nat * option (option vl)) :=
  match n with
    | 0 => (0,None)
    | S n =>
      match t with
        | ttrue                                => (1, Some (Some (vbool true)))
        | tfalse                               => (1, Some (Some (vbool false)))
        | tvar x                               => (1, Some (index x env))
        | tabs y                               => (1, Some (Some (vabs env y)))
        | tapp ef ex                           =>
          match teval n env ef with
            | (df, None)                       => (1+df, None)
            | (df, Some None)                  => (1+df, Some None)
            | (df, Some (Some (vbool _)))      => (1+df, Some None)
            | (df, Some (Some (vabs env2 ey))) =>
              match teval (n-df) env ex with
                | (dx, None)                   => (1+df+dx, None)
                | (dx, Some None)              => (1+df+dx, Some None)
                | (dx, Some (Some vx))         =>
                  match teval (n-df-dx) (vx::(vabs env2 ey)::env2) ey with
                    | (dy, res)                => (1+df+dx+dy, res)
                  end
              end
          end
      end
end.


(* some facts about evaluation. we need evaluation to be deterministic so that
   we can "downgrade" our logical relation val_type below. instead of proving
   this fact here, it could also be possible to encode it in the LR itself. *)

Lemma eval_deterministic: forall m n, n < m -> forall H t n1 r j,
  teval n H t = (n1, Some r) -> j >= n ->
  teval j H t = (n1, Some r).
Proof.
  intros m. induction m. intros. inversion H.
  intros. destruct n. inversion H1. destruct j. inversion H2.
  destruct t; simpl; simpl in H1; try eauto.
  remember (teval n H0 t1) as tf. destruct tf as [nf [rf|]].
  rewrite IHm with (n:=n) (n1:=nf) (r:=rf).
  destruct rf; try destruct v; try solve [inversion H1; eauto]. 
  remember (teval (n-nf) H0 t2) as tx. destruct tx as [nx [rx|]].
  rewrite IHm with (n:=n-nf) (n1:=nx) (r:=rx).
  destruct rx; try solve [destruct v; inversion H1; eauto].
  remember (teval (n-nf-nx) (v :: vabs l t :: l) t) as ty. destruct ty as [ny [ry|]].
  rewrite IHm with (n:=n-nf-nx) (n1:=ny) (r:=ry).

  eauto. omega. eauto. omega.
  inversion H1. inversion H1.
  eauto. omega. eauto. omega.
  inversion H1.
  omega. eauto. omega.
  inversion H1.
Qed.


(* original termination and determinism def: *)
(* Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v). *)

(* if we want to encode determinism directly, we'd need something like this: *)
Definition tevaln nm env e n1 v :=
  teval nm env e = (nm, None) \/
  forall n, n > nm -> teval n env e = (n1, Some (Some v)).



(* need to use Fixpoint because of positivity restriction *)
Fixpoint val_type n v T : Prop := match v, T with
| vbool b, TBool => True
| vabs env y, TFun T1 T2 =>
  (* forall n nx, R n nx H tx vx T1 -> R (n-nx) ny (vx::vf::H) vy T2 *)
  (* NOTE: trouble b/c R does not include vx!! *)
  forall nx vx, 
      val_type (n-nx) vx T1 -> forall ry ny,
      (* R nm (vx::(vabs env y)::env) y T2 *)
      teval (n-nx) (vx::(vabs env y)::env) y = (ny, Some ry) ->
      exists vy,
        ny <> 0 /\ ry = Some vy /\ val_type (n-nx-ny) vy T2
| _,_ => False
end.

Definition R n H t T := 
  (* tevaln H t v /\ val_type v T. *)
  forall r n1, teval n H t = (n1,Some r) ->
    exists v, n1 <> 0 /\ r = Some v /\ val_type (n-n1) v T.

Definition R_env nm venv tenv :=
  length venv = length tenv /\
  forall x T1, index x tenv = Some T1 ->
    R nm venv (tvar x) T1.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
(* Hint Constructors val_type. *)

Hint Constructors option.
Hint Constructors list.


Lemma V_down: forall n j v T, j <= n -> val_type n v T -> val_type j v T.
Proof.
  intros n. induction n.
  intros. destruct j. eauto. inversion H.
  intros.
  case_eq (eq_nat_dec j (S n)); intros E _. subst j. eauto.
  assert (val_type n v T). {
    destruct T; destruct v; try  eauto.
    simpl. intros. simpl in H0. specialize (H0 (S nx) vx H1 ry ny H2). eapply H0.
  }
  eapply IHn. omega. eauto. 
Qed.

Lemma R_down: forall n j H t T, j <= n -> R n H t T -> R j H t T.
Proof.
  intros.
  unfold R. unfold R in H1. intros. eapply eval_deterministic in H2.
  specialize (H1 r n1 H2).
  destruct H1 as [v [N [R ?]]].
  eapply V_down in H1. eauto. omega. eauto. omega. 
Qed.
                  
Lemma R_env_down: forall n j H G, j <= n -> R_env n H G -> R_env j H G.
Proof.
  intros.
  unfold R_env. unfold R_env in H1. destruct H1.
  split. eauto. intros.
  eapply R_down in H2. eauto. eauto. eauto.
Qed.


(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall nn, forall n, n < nn -> forall e tenv T,
  has_type tenv e T -> forall venv, R_env n venv tenv ->
  R n venv e T.

Proof.
  intros nn. induction nn.
  (* z *) intros. solve [inversion H].
  (* S n *)
  intros n NB ? ? ? W.
  destruct n. unfold R. intros. inversion H0.
  
  inversion W; intros ? WFE.
  
  - Case "True". 
    eexists. simpl in H2. inversion H2. repeat split; simpl; eauto.

  - Case "False".
    eexists. simpl in H2. inversion H2. repeat split; simpl; eauto.

  - Case "Var".
    eapply WFE. eauto.

  - Case "App".
    unfold R. intros ? n1 EVY.
    simpl in EVY.
    
    assert (R n venv0 f (TFun T1 T)) as RF. eapply IHnn. omega. eauto.
    eapply R_env_down. instantiate (1 := S n). omega. eauto. 
    unfold R in RF.

    remember (teval n venv0 f) as EF. symmetry in HeqEF.
    destruct EF as [nf [rf|]]; try solve [inversion EVY].
    destruct (RF rf nf) as [vf [? [EQVF VTF]]]. eauto.
    subst rf.
    
    simpl in VTF. destruct vf. contradiction.
    

    assert (R (n-nf) venv0 x T1) as RX. eapply IHnn. omega. eauto. eauto.
    eapply R_env_down. instantiate (1 := S n). omega. eauto. 
    unfold R in RX.

    remember (teval (n-nf) venv0 x) as EX. symmetry in HeqEX.
    destruct EX as [nx [rx|]]; try solve [inversion EVY].
    destruct (RX rx nx) as [vx [? [EQVX VTX]]]. eauto.
    subst rx. 

    remember (teval (n - nf - nx) (vx :: vabs l t :: l) t) as EY. symmetry in HeqEY.
    destruct EY as [ny [ry|]]; try solve [inversion EVY].
    inversion EVY. subst r n1. clear EVY.

    specialize (VTF _ _ VTX _ _ HeqEY).
    assert ((n - nf - nx - ny = S n - S (nf + nx + ny))) as RW. omega.
    rewrite <-RW.
    destruct VTF as [? [? [? ?]]]. eexists. repeat split; eauto. 

  - Case "Abs".

    (* goal:  R (S n) venv0 (tabs y) (TFun T1 T2) *)
    unfold R. intros ? ? EV.
    inversion EV.
    simpl in EV. inversion EV. subst n1 r. clear EV.
    exists (vabs venv0 y). split. eauto. split. eauto.
    assert (S n - 1 = n). omega. rewrite H3.

    (* goal val_type n (vabs venv0 y) (TFun T1 T2) *)

    (* internal induction *)
    assert (forall nm1, nm1 <= n -> forall nm, nm <= nm1 ->
                       val_type nm (vabs venv0 y) (TFun T1 T2)) as IND.
    intros nm1. induction nm1.
    (* z *) simpl. intros. destruct nm. solve [inversion H9]. solve [inversion H5].
    (* s n *) intros ? ? ?. 

    (* goal val_type n (vabs venv0 y) (TFun T1 T2) *)
    simpl. intros ? ? ?.
    
    eapply IHnn. omega. eauto. 

    (* now downgrade and extend R_env *)
    (* goal: (R_env (n-nx) (vx :: vabs venv0 y :: venv0) (T1::TFun T1 T2::tenv0)) as WFE1. *)

    unfold R_env. split. simpl. unfold R_env in WFE. destruct WFE as [L IX]. rewrite L. eauto.
      intros ? ? IX.
      
      unfold R. intros ? ? EVX.
      remember (nm-nx) as nx2.
      destruct nx2. solve [inversion EVX].
      simpl in EVX. destruct WFE as [L WX].
      simpl in IX. rewrite <-L in IX.
      (* is it the arg? *)
      destruct (eq_nat_dec x (S (length venv0))).
      inversion EVX. subst n1 r.
      exists vx. split. eauto. split. eauto. simpl.
      inversion IX. subst T0.
      eapply V_down. instantiate (1:= S nx2). omega. eauto.
      (* is it the fun? *)
      destruct (eq_nat_dec x (length venv0)).
      inversion EVX. subst n1 r.
      inversion IX. subst T0.
      rewrite Heqnx2.

      exists (vabs venv0 y). split. eauto. split. eauto.
      (* goal:  val_type (n-nx-1) (vabs venv0  y) (TFun T1 T2) *)
      (* induction! *) 
      eapply IHnm1. eauto. omega. omega. 

      (* default case *)
      eapply R_down. instantiate (1:= S n). omega. eapply WX. eauto. simpl. eauto.

      (* done with indunction *)
      eapply IND. eauto. eauto.
Qed.

End STLC.