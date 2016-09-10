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
Fixpoint val_type nm v T : Prop := match v, T with
| vbool b, TBool => True
| vabs env y, TFun T1 T2 => 
  forall vx, val_type nm vx T1 -> (* extend to R ? H tx vx T1 ? *)
    exists vy,
      (* R nm (vx::(vabs env y)::env) y vy T2 *)
      
        forall r, teval nm (vx::(vabs env y)::env) y = Some r ->
    r = Some vy /\ val_type nm vy T2
| _,_ => False
end.

Definition R nm H t v T := 
  (* tevaln H t v /\ val_type v T. *)
  forall r, teval nm H t = Some r ->
    r = Some v /\ val_type nm v T.

Definition R_env nm venv tenv :=
  length venv = length tenv /\
 forall x T1, index x tenv = Some T1 ->
   exists v : vl, R nm venv (tvar x) v T1.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
(* Hint Constructors val_type. *)

Hint Constructors option.
Hint Constructors list.


(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall n, forall e tenv T,
  has_type tenv e T -> forall venv, R_env n venv tenv ->
  exists v, R n venv e v T.

Proof.
  intros n. induction n.
  (* z *) intros. eexists. unfold R. intros. inversion H1.
  (* S n *)
  intros ? ? ? W. 
  inversion W; intros ? WFE.
  
  - Case "True". eexists. split.
    simpl in H2. inversion H2. eauto. simpl. eauto.
  - Case "False". eexists. split.
    simpl in H2. inversion H2. eauto. simpl. eauto. 

  - Case "Var".
    eapply WFE. eauto.

  - Case "App".
    (* downgrade R_env *)
    assert (R_env n venv0 tenv0) as WFE0. admit.
    
    destruct (IHn f _ _ H  venv0 WFE0) as [vf RF].
    destruct (IHn x _ _ H0 venv0 WFE0) as [vx RX].

    remember (teval n venv0 f) as EF.
    remember (teval n venv0 x) as EX.
    destruct EF as [rf|]. symmetry in HeqEF. specialize (RF _ HeqEF).
    destruct EX as [rx|]. symmetry in HeqEX. specialize (RX _ HeqEX).

    destruct RF as [? VF]. destruct RX as [? VX]. subst rf rx.
    
    destruct vf. solve [contradiction].
    simpl in VF.
    specialize (VF vx VX).
    destruct VF as [vy VY]. 

    exists vy. unfold R. intros vy1 VA.
    simpl in VA.
    rewrite HeqEF in VA.
    rewrite HeqEX in VA.
    specialize (VY vy1 VA).
    destruct VY as [? VTY].
    split. eauto.
    (* upgrade val_type -- DOES NOT HOLD *)
    assert (val_type (S n) vy T). admit.
    eauto.

    (* timeout case x *)
    eexists. unfold R. intros vy1 VA.
    simpl in VA.
    rewrite <-HeqEX in VA. rewrite HeqEF in VA.
    destruct RF. subst rf. 
    destruct vf. solve [contradiction].
    solve [inversion VA].
    (* timeout case f *)
    eexists. unfold R. intros vy1 VA.
    simpl in VA.
    rewrite <-HeqEF in VA.
    solve [inversion VA].

  - Case "Abs".
    eexists. split. exists 0. intros. destruct n. omega. simpl. eauto. simpl.
    intros.

    assert (exists v : vl, R (vx :: vabs venv0 y :: venv0) y v T2). {
    eapply IHW. unfold R_env.
    split. simpl. destruct WFE. eauto. 
    intros.
    simpl in H1.
    (* is it the arg? *)
    destruct (eq_nat_dec x (S (length env))). 
    inversion H1. subst T0.
    exists vx. split.
    exists 0. intros. destruct n. omega. simpl.
    destruct WFE. subst. rewrite H3.
    destruct (eq_nat_dec (S (length env)) (S (length env))). eauto. contradiction n0. eauto.
    eauto.
    destruct H0. eauto.
    (* is it the function? *)
    destruct (eq_nat_dec x (length env)). 
    inversion H1. subst T0.
    exists (vabs venv0 y). split.
    exists 0. intros. destruct n0. omega. simpl.
    destruct WFE. subst. rewrite H3.
    destruct (eq_nat_dec (length env) (S (length env))). contradiction. 
    destruct (eq_nat_dec (length env) (length env)). eauto. destruct n2. eauto. 
    (* now create the val_type for the vabs *)
    admit. (* WE CANNOT, SINCE THIS IS THE MAIN GOAL *)
    (* continue *)
    destruct WFE. subst. 
    specialize (H3 _ _ H1). destruct H3. destruct H3. destruct H3. 
    exists x0. split. exists x1. intros. destruct n1. omega. simpl.
    rewrite H2.
    destruct (eq_nat_dec x (S (length env))). contradiction. specialize (H3 (S n1) H5).
    destruct (eq_nat_dec x (length env)). contradiction.
    simpl in H3. eapply H3.
    eauto.
    }

    eapply H1. 
Qed.

End STLC.