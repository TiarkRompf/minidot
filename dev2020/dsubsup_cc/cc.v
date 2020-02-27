(* Target language (inspired by https://docs.racket-lang.org/pie/index.html):

 t ::= x | Unit | Type
     | (z: T) -> T^z  | lambda x:T.t | t t
     | Sigma z:T. T^z | (t, t)  | fst t | snd t *)
Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import variables.

Declare Scope cc_scope.

Module CC.

Inductive kind : Type :=
| Box :  kind
| Star : kind
.

Inductive tm : Type := (* TODO what about equality types? *)
| Kind : kind -> tm
| TTop : tm (* TODO really needed? *)
| TBot : tm (* TODO really needed? *)
| TAll : tm -> tm -> tm
| TSig : tm -> tm -> tm
| tvar : var -> tm
| tabs : tm -> tm -> tm
| tapp : tm -> tm -> tm
| tsig : tm -> tm -> tm
| tfst : tm -> tm
| tsnd : tm -> tm
.

Module Notations.

(* \square *)
Notation "◻" := (Kind Box) : cc_scope.
(* \star *)
Notation "⋆" := (Kind Star) : cc_scope.

End Notations.

Import Notations.

Definition tenv := list tm.

Open Scope cc_scope.

(*TODO: is it ok if we generalize opening w. arbitrary terms? *)
Fixpoint open_rec (k: nat) (u: tm) (T: tm) { struct T }: tm :=
  match T with
  | ⋆           => ⋆
  | ◻           => ◻
  | TTop        => TTop
  | TBot        => TBot
  | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
  | TSig T1 T2  => TSig (open_rec k u T1) (open_rec (S k) u T2)
  | tvar (varF x) => tvar (varF x)
  | tvar (varB x) =>
    if beq_nat k x then u else (tvar (varB x))
  | tabs ty tm => tabs (open_rec k u ty) (open_rec (S k) u tm)
  | tapp tm1 tm2 => tapp (open_rec k u tm1) (open_rec k u tm2)
  | tsig tm1 tm2 => tsig (open_rec k u tm1) (open_rec (S k) u tm2)
  | tfst tm => tfst (open_rec k u tm)
  | tsnd tm => tsnd (open_rec k u tm)
  end.

Definition open u T := open_rec 0 (tvar u) T.
Definition open' t T := open_rec 0 t T.

Inductive tenv_wf: tenv -> Prop :=
| tenv_wf_empty:
    tenv_wf []

| tenv_wf_kind: forall Gamma T U,
    tenv_wf Gamma ->
    has_type Gamma T (Kind U) ->
    tenv_wf (T :: Gamma)

with has_type : tenv -> tm -> tm -> Prop :=
| t_box: forall Gamma,
    has_type Gamma ⋆ ◻

| t_var: forall x Gamma T,
    tenv_wf Gamma ->
    indexr x Gamma = Some T ->
    has_type Gamma (tvar (varF x)) T

| t_allt: forall Gamma T1 T2 U U',
    has_type Gamma T1 (Kind U) -> (* not strictly necessary  *)
    has_type (T1 :: Gamma) (open (varF (length Gamma)) T2) (Kind U') ->
    has_type Gamma (TAll T1 T2) (Kind U') (* TODO is U' = Box needed at all? *)

| t_sigt: forall Gamma T1 T2 U U',
    (* TODO this leads to logical inconsistency,
       should fix U to ⋆, or try infinite hierarchy of kinds
       (cf. Luo's ECC resp. LEGO system). Arthur's libln model of CC shows how to model hierarchy in Coq) *)
    has_type Gamma T1 (Kind U) -> (* not strictly necessary here*)
    has_type (T1 :: Gamma) (open (varF (length Gamma)) T2) (Kind U') ->
    has_type Gamma (TSig T1 T2) (Kind U') (* TODO is U' = Box needed at all? *)

| t_topt: forall Gamma,
    has_type Gamma TTop ⋆

| t_bott: forall Gamma,
    has_type Gamma TBot ⋆

| t_abs: forall Gamma t T1 T2 U U',
    has_type Gamma T1 (Kind U) -> (* not strictly necessary *)
    has_type Gamma (TAll T1 T2) (Kind U') ->
    has_type (T1 :: Gamma) t (open (varF (length Gamma)) T2) ->
    has_type Gamma (tabs T1 t) (TAll T1 T2)

| t_app: forall Gamma f e T1 T2 T,
    has_type Gamma f (TAll T1 T2) ->
    has_type Gamma e T1 ->
    T = (open' e T2) ->
    has_type Gamma (tapp f e) T

| t_sig: forall Gamma e1 e2 T1 T2,
    has_type Gamma e1 T1 ->
    has_type Gamma e2 (open' e1 T2) ->
    has_type Gamma (tsig e1 e1) (TSig T1 T2) (* TODO: type annotation required? *)

| t_fst: forall Gamma e T1 T2,
    has_type Gamma e (TSig T1 T2) ->
    has_type Gamma (tfst e) T1

| t_snd: forall Gamma e T1 T2 T,
    has_type Gamma e (TSig T1 T2) ->
    T = (open' (tfst e) T2) ->
    has_type Gamma (tsnd e) T
.

(* TODO: define reduction/evaluation *)
(* TODO: define strong normalization *)

End CC.
