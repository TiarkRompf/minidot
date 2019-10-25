(* ############################################################ *)
(*                                                              *)
(*               Language definition for STLC 1/2               *)
(*                                                              *)
(* ############################################################ *)

(* Starting point: https://github.com/TiarkRompf/minidot/blob/master/dev2015/nano2.v *)
(* Starting point: https://github.com/TiarkRompf/scala-escape/blob/master/coq/stlc1.v *)


Require Export Arith.EqNat.
Require Export Arith.Le.
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
| Def l1 l2 n, First => length l1
| Def l1 l2 n, Second => length l2
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

Hint Immediate index_max.

Lemma lookup_max : forall X vs x (T: X),
                       lookup x vs = Some T ->
                       get_idx x < length_env (get_class x) vs.
Proof.
  intros X vs; destruct vs as [l1 l2 n].
  intros x T H.
  destruct x. destruct c; simpl.
  Case "VFst". inversion H; eauto.
  Case "VSnd". inversion H.
    destruct (ble_nat n i); inversion H1; eauto.
Qed.
