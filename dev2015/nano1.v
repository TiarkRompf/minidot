(* Full safety for STLC *)
(* values well-typed with respect to runtime environment *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Module DOT.

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
  | tabs : id -> id -> tm -> tm (* \f x.y *)
.


Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : list (id*vl) -> id -> id -> tm -> vl
.

Definition env := list (id*vl).
Definition tenv := list (id*ty).

Hint Unfold env.
Hint Unfold tenv.

Fixpoint length {X: Type} (l : list X): nat :=
  match l with
    | [] => 0
    | _::l' => 1 + length l'
  end.

Fixpoint index {X : Type} (n : id) (l : list (id * X)) : option X :=
  match l with
    | [] => None
    (* ignore binding value n' !!! *)
    | (n',a) :: l'  => if beq_nat n (length l') then Some a else index n l'
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
| t_abs: forall env f x y T1 T2,
           has_type ((x,T1)::(f,TFun T1 T2)::env) y T2 -> 
           has_type env (tabs f x y) (TFun T1 T2)
.

Inductive wf_env : env -> tenv -> Prop := 
| wfe_nil : wf_env nil nil
| wfe_cons : forall n v t vs ts,
    val_type ((n,v)::vs) v t ->
    wf_env vs ts ->
    wf_env (cons (n,v) vs) (cons (n,t) ts)                                    

with val_type : env -> vl -> ty -> Prop :=
| v_bool: forall venv b,
    val_type venv (vbool b) TBool
| v_abs: forall env venv tenv f x y T1 T2,
    wf_env env tenv ->
    has_type ((x,T1)::(f,TFun T1 T2)::tenv) y T2 ->
    val_type venv (vabs env f x y) (TFun T1 T2)
.




(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v

Could use do-notation to clean up syntax.
 *)

Fixpoint teval(n: nat)(env: env)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (index x env)
        | tabs f x y => Some (Some (vabs env f x y))
        | tapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 f x ey)) =>
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n ((x,vx)::(f,vabs env2 f x ey)::env2) ey
              end
          end
      end
  end.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
Hint Constructors val_type.
Hint Constructors wf_env.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.

Require Import LibTactics.
(*
Require Import Coq.Program.Equality.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.
*)
Lemma wf_length : forall vs ts,
                    wf_env vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  assert ((length ((n,v)::vs)) = 1 + length vs). constructor.
  assert ((length ((n,t)::ts)) = 1 + length ts). constructor.
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
  intros. inversion H. destruct a.
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

Lemma valtp_extend : forall vs x v v1 T,
                       val_type vs v T ->
                       val_type ((x,v1)::vs) v T.
Proof. intros. induction H; eauto. Qed.

Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply index_max. eauto.
  assert (n <> length vs). omega.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff; eauto.
  unfold index. unfold index in H. rewrite H. rewrite E. destruct a. reflexivity.
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
             assert (index i ((n, v) :: vs) = Some v). eauto.  unfold index. rewrite H2. eauto.
             eauto.
           SCase "miss".
             intros E.
             assert (beq_nat i (length vs) = false). eauto.
             rewrite E in H3.
             assert (exists v0, index i vs = Some v0 /\ val_type vs v0 TF) as HI. eapply IHwf_env. eauto.
           inversion HI as [v0 HI1]. inversion HI1. 
           eexists. econstructor. eapply index_extend; eauto. eapply valtp_extend; eauto.
Qed.

  
Inductive res_type: env -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.

(* if not a timeout, then result not stuck and well-typed *)

Theorem full_safety : forall n e tenv venv res T,
  teval n venv e = Some res -> has_type tenv e T -> wf_env venv tenv ->
  res_type venv res T.

Proof.
  intros n. induction n. intros. inversion H. (* 0 *)
  intros. destruct e.
  
  Case "True".  intros. inversion H. inversion H0. eapply not_stuck. eapply v_bool.
  Case "False". intros. inversion H. inversion H0. eapply not_stuck. eapply v_bool.

  Case "Var". intros. inversion H. inversion H0.
    destruct (index_safe_ex venv tenv0 T i) as [v IV]. eauto. eauto. 
    inversion IV as [I V]. 

    rewrite I. eapply not_stuck. eapply V.

  Case "App". intros. inversion H. inversion H0.
    remember (teval n venv e1) as tf. (* not stuck *)
    remember (teval n venv e2) as tx. 
    subst T.
    
    destruct tf as [rf|]; destruct tx as [rx|]; try solve by inversion.

    assert (res_type venv rf (TFun T1 T2)) as HRF. subst. eapply IHn; eauto.
    assert (res_type venv rx T1) as HRX. subst. eapply IHn; eauto.

    inversion HRX as [venv'  vx T1' HVX].
    inversion HRF as [venv'' vf TF  HVF].
    inversion HVF. (* now we know it's a closure, and we have has_type evidence *)

    assert (res_type ((x0,vx)::(f0,vf)::env1) res T2) as HRY. SCase "HRY". subst. eapply IHn; eauto.
    (*wf_env*) econstructor; eauto. (*extend val_type*)inversion HVX; econstructor; eauto.

    inversion HRY as [env1xf vy T2' HVY].

    eapply not_stuck. (*shrink val_type*)inversion HVY; econstructor; eauto.

    (* other case: tx = None *) 

    assert (res_type venv rf (TFun T1 T2)) as HRF. subst. eapply IHn; eauto.

    inversion HRF. subst. inversion H7. subst. inversion H3. (* contradiction *)


    
  Case "Abs". intros. inversion H. inversion H0.
    eapply not_stuck. eapply v_abs; eauto.
Qed.

End DOT.