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


(* TODO -- fix & adapt old code below *)


(* original termination and determinism def: *)
(* Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v). *)

(* if we want determinism, too, we'd need something like this: *)
Definition tevaln nm env e n1 v :=
  teval nm env e = (nm, None) \/
  forall n, n > nm -> teval n env e = (n1, Some (Some v)).



(* need to use Fixpoint because of positivity restriction *)
Fixpoint val_type n v T : Prop := match v, T with
| vbool b, TBool => True
| vabs env y, TFun T1 T2 =>
  (* forall n nx, R n nx H tx vx T1 -> R (n-nx) ny (vx::vf::H) vy T2 *)
  (* NOTE: trouble b/c R does not include vx!! *)
  forall nx envx tx vx, 
    teval (n) envx tx = (nx, Some (Some vx)) ->
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


(* if well-typed, then result is an actual value (not stuck and not a timeout),
   for large enough n *)

Theorem full_total_safety : forall n, forall e tenv T,
  has_type tenv e T -> forall venv, R_env n venv tenv ->
  exists v, R n venv e v T.

Proof.
  intros n. induction n.
  (* z *) intros. eexists. unfold R. intros. inversion H1. subst. inversion H2.
  (* S n *)
  intros ? ? ? W. 
  inversion W; intros ? WFE.
  
  - Case "True". eexists. split.
    destruct n0. inversion H3. simpl in H3. inversion H3. eauto. simpl. eauto.

  - Case "False". eexists. split.
    destruct n0. inversion H3. simpl in H3. inversion H3. eauto. simpl. eauto.

  - Case "Var".
    eapply WFE. eauto.

  - Case "App".
    (* downgrade R_env *)
    assert (R_env n venv0 tenv0) as WFE0. {
      unfold R_env.
      destruct WFE.
      split. eauto. intros.
      specialize (H5 _ _ H6).
      destruct H5.
      admit. (* should be ok ... *)
      }
    
    destruct (IHn f _ _ H  venv0 WFE0) as [vf RF].
    destruct (IHn x _ _ H0 venv0 WFE0) as [vx RX].

    
(*    destruct vf. solve [contradiction].
    simpl in VF.
    specialize (VF vx VX).
    destruct VF as [vy VY]. *)

    eexists. unfold R. intros vy1 n0 ? VA.
    destruct n0. solve [inversion VA].

    remember (teval n0 venv0 f) as EF.
    remember (teval n0 venv0 x) as EX.
    assert (n0 <= n) as HN. omega.
    destruct EF as [rf|]. symmetry in HeqEF. specialize (RF _ n0 HN HeqEF).
    destruct EX as [rx|]. symmetry in HeqEX. specialize (RX _ n0 HN HeqEX).

    destruct RF as [? VF]. destruct RX as [? VX]. subst rf rx.

    simpl in VA.
    rewrite HeqEF in VA.
    rewrite HeqEX in VA.
    destruct vf. solve [contradiction].
    simpl in VF.
    specialize (VF vx VX).
    destruct VF as [vy VY].
    assert (n0<=n-n0) as HDN. admit. 
    specialize (VY vy1 _ HDN VA).
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
    exists (vabs venv0 y).
    unfold R. intros. split. simpl in H3. inversion H3. eauto.
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