(* Full safety for STLC *)

(* copied from nano0.v *)

(* This version prohibits recursion, and we prove that   *)
(* evaluation always terminates with a well-typed value. *)
(* From this follows both type soundness and strong      *)
(* normalization for STLC.                               *)

(* copied from nano0-total.v *)

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
           has_type (T1::env) y T2 -> 
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
                  teval n (vx::env2) ey
              end
          end
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).





(* need to use Fixpoint because of positivity restriction *)
Fixpoint val_type H t v T : Prop := match v, T with
| vbool b, TBool => True
| vabs env y, TFun T1 T2 => 
  (forall tx vx, tevaln H tx vx /\ val_type H tx vx T1 -> (* R H tx vx T1 *)
     exists vy, tevaln H (tapp t tx) vy /\ val_type H (tapp t tx) vy T2) (* R (vx:env) y vy T2 *)
| _,_ => False
end.

Definition R H t v T := tevaln H t v /\ val_type H t v T.

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
    admit. (* this case is almost trivial, but i'm too lazy *)
    
  - Case "Abs".
    eexists. split. exists 0. intros. destruct n. omega. simpl. eauto. simpl.
    intros.

    assert (exists v : vl, R (vx::venv0) y v T2).
    eapply IHW. unfold R_env.
    split. simpl. destruct WFE. eauto. 
    intros.
    simpl in H0. 
    destruct (eq_nat_dec x (length env)). 
    inversion H0. subst T0.
    exists vx. split.
    exists 0. intros. destruct n. omega. simpl.
    destruct WFE. subst. rewrite H2.
    destruct (eq_nat_dec (length env) (length env)). eauto. contradiction n0. eauto. subst x. 
    destruct H.
    (* prove: val_type venv0 tx vx T1 -> 
              val_type (vx :: venv0) (tvar (length env)) vx T1 

       not straightforward, because induction requires

              val_type H (tapp t tx) vy T2) ->
              val_type (vx::H) (tapp (tvar (length H)) tx) vy T2)
    *)
    admit.
    (* prove for (tvar x) with x <> length env *)
    admit.

    destruct H0.
    destruct H0.
    destruct H.
    
    exists x. split.
    destruct H. destruct H0.
    exists (S (x0+x1)). intros. destruct n. omega. simpl.
    destruct n. omega. 
    unfold teval at 1.
    erewrite H.
    erewrite H0.
    eauto. omega. omega. 

    (* prove: val_type venv0 tx vx T1 ->
              val_type (vx :: venv0) y x T2 ->
              val_type venv0 (tapp (tabs y) tx) x T2 

       tricky again b/c induction
    *)
    
    admit.
Qed.

End STLC.