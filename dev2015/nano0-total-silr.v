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

(* TODO!! *)


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
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 ey)) =>
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n (vx::(vabs env2 ey)::env2) ey
              end
          end
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).





(* need to use Fixpoint because of positivity restriction *)
Fixpoint val_type v T : Prop := match v, T with
| vbool b, TBool => True
| vabs env y, TFun T1 T2 => 
  (forall H tx vx, tevaln H tx vx /\ val_type vx T1 -> (* R H tx vx T1 *)
     exists vy, tevaln (vx::env) y vy /\ val_type vy T2) (* R (vx:env) y vy T2 *)
| _,_ => False
end.

Definition R H t v T := tevaln H t v /\ val_type v T.

Definition R_env venv tenv :=
  length venv = length tenv /\
 forall x T1, index x tenv = Some T1 ->
   exists v : vl, R venv (tvar x) v T1.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
(* Hint Constructors val_type. *)

Hint Constructors option.
Hint Constructors list.


(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall e tenv T,
  has_type tenv e T -> forall venv, R_env venv tenv ->
  exists v, R venv e v T.

Proof.
  intros ? ? ? W. 
  induction W; intros ? WFE.
  
  - Case "True". eexists. split. 
    exists 0. intros. destruct n. omega. simpl. eauto. simpl. eauto. 
  - Case "False". eexists. split.
    exists 0. intros. destruct n. omega. simpl. eauto. simpl. eauto. 

  - Case "Var".
    eapply WFE. eauto.

  - Case "App".
    destruct (IHW1 venv0 WFE) as [vf [IW1 HVF]].
    destruct (IHW2 venv0 WFE) as [vx [IW2 HVX]].
    destruct vf. solve [inversion HVF]. 
    simpl in HVF.
    specialize (HVF venv0 x vx (conj IW2 HVX)).
    destruct HVF as [vy [IW3 HVY]].
    exists vy. split.
    destruct IW1 as [n1 IW1].
    destruct IW2 as [n2 IW2].
    destruct IW3 as [n3 IW3].
    exists (S (n1+n2+n3)).
    intros.
    destruct n. omega. simpl. rewrite IW1. rewrite IW2. rewrite IW3. eauto.
    omega. omega. omega.
    eauto. 
    
  - Case "Abs".
    eexists. split. exists 0. intros. destruct n. omega. simpl. eauto. simpl.
    intros.

    assert (exists v : vl, R (vx::venv0) y v T2).
    eapply IHW. unfold R_env.
    split. simpl. destruct WFE. eauto. 
    intros.
    simpl in H1. 
    destruct (eq_nat_dec x (length env)). 
    inversion H1. subst T0.
    exists vx. split.
    exists 0. intros. destruct n. omega. simpl.
    destruct WFE. subst. rewrite H3.
    destruct (eq_nat_dec (length env) (length env)). eauto. contradiction n0. eauto.
    eauto.
    destruct H0. eauto.
    destruct WFE. 
    specialize (H3 _ _ H1). destruct H3. destruct H3. destruct H3. 
    exists x0. split. exists x1. intros. destruct n0. omega. simpl.
    rewrite H2. destruct (eq_nat_dec x (length env)). contradiction. specialize (H3 (S n0) H5).
    simpl in H3. eapply H3.
    eauto.

    eapply H1. 
Qed.

End STLC.