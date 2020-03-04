(* Source language (currently missing: T ::=  T1 /\ T2 | { z => T^z }):

  DSubSup (D<:>)
  T ::= Top | Bot | t.Type | { Type: S..U } | (z: T) -> T^z
  t ::= x | { Type = T } | lambda x:T.t | t t *)
Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

(* ### Syntax ### *)

Definition id := nat.

(* term variables occurring in types *)
Inductive var : Type :=
| varF : id -> var (* free, in concrete environment *)
| varB : id -> var (* locally-bound variable *)
.

(* An environment is a list of values, indexed by decrementing ids. *)

Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.

Module D.

Inductive ty : Type :=
| TTop : ty
| TBot : ty
(* (z: T) -> T^z *)
| TAll : ty -> ty -> ty
(* We generalize x.Type to tm.type for arbitrary terms tm.  *)
| TSel : tm -> ty
(* { Type: S..U } *)
| TMem : ty(*S*) -> ty(*U*) -> ty
| TBind  : ty -> ty (* Recursive binder: { z => T^z },
                         where z is locally bound in T *)
| TAnd : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *)


with tm : Type :=
(* x -- free variable, matching concrete environment *)
| tvar : var -> tm
(* { Type = T } *)
| ttyp : ty -> tm
(* lambda x:T.t *)
| tabs : ty -> tm -> tm
(* t t *)
| tapp : tm -> tm -> tm
(* unpack(e) { x => ... } *)
| tunpack : tm -> tm -> tm
.

Inductive vl : Type :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> ty -> tm -> vl
(* a closure for a first-class type *)
| vty : list vl (*H*) -> ty -> vl
.

Definition tenv := list ty. (* Gamma environment: static *)
Definition venv := list vl. (* H environment: run-time *)


(* ### Representation of Bindings ### *)


Inductive closed: nat(*B*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall i j,
    closed i j TTop
| cl_bot: forall i j,
    closed i j TBot
| cl_all: forall i j T1 T2,
    closed i j T1 ->
    closed (S i) j T2 ->
    closed i j (TAll T1 T2)
(* Now we have mutually recursive definitions for closedness on types and terms! *)
| cl_sel_tm: forall i j t,
    closed_tm i j t ->
    closed i j (TSel t)
| cl_mem: forall i j T1 T2,
    closed i j T1 ->
    closed i j T2 ->
    closed i j (TMem T1 T2)
| cl_bind: forall i j T,
    closed (S i) j T ->
    closed i j (TBind T)
| cl_and: forall i j T1 T2,
    closed i j T1 ->
    closed i j T2 ->
    closed i j (TAnd T1 T2)


with closed_tm: nat(*B*) -> nat(*F*) -> tm -> Prop :=
| cl_tvarb: forall i j x,
    i > x ->
    closed_tm i j (tvar (varB x))
| cl_tvarf: forall i j x,
    j > x ->
    closed_tm i j (tvar (varF x))
| cl_ttyp:  forall i j ty,
    closed i j ty ->
    closed_tm i j (ttyp ty)
| cl_tabs:  forall i j ty tm,
    closed i j ty ->
    closed_tm (S i) j tm ->
    closed_tm i j (tabs ty tm)
| cl_tapp:  forall i j tm1 tm2,
    closed_tm i j tm1 ->
    closed_tm i j tm2 ->
    closed_tm i j (tapp tm1 tm2)
| cl_tunpack: forall i j tm1 tm2,
    closed_tm i j tm1 ->
    closed_tm (S i) j tm2 ->
    closed_tm i j (tunpack tm1 tm2)
.

(* open define a locally-nameless encoding wrt to TVarB type variables. *)
(* substitute var u for all occurrences of (varB k) *)
Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TSel tm => TSel (open_rec_tm k u tm)
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
    | TBind T => TBind (open_rec (S k) u T)
    | TAnd T1 T2 => TAnd (open_rec k u T1) (open_rec k u T2)
  end

with open_rec_tm (k: nat) (u: var) (t: tm) { struct t }: tm :=
       match t with
       | tvar (varF x) => tvar (varF x)
       | tvar (varB x) =>
         if beq_nat k x then (tvar u) else (tvar (varB x))
       | ttyp ty => ttyp (open_rec k u ty)
       | tabs ty tm => tabs (open_rec k u ty) (open_rec_tm (S k) u tm)
       | tapp tm1 tm2 => tapp (open_rec_tm k u tm1) (open_rec_tm k u tm2)
       | tunpack tm1 tm2 => tunpack (open_rec_tm k u tm1) (open_rec_tm (S k) u tm2)
       end.

Definition open u T := open_rec 0 u T.
Definition open_tm u t := open_rec_tm 0 u t.

(* ### Type Assignment ### *)
Inductive is_type: tenv -> ty -> Set :=
| t_top: forall G, is_type G TTop
| t_bot: forall G, is_type G TBot
| t_mem: forall G T1 T2, is_type G T1 -> is_type G T2 -> is_type G (TMem T1 T2)
| t_all: forall G T1 T2,
    is_type G T1 ->
    is_type (T1::G) (open (varF (length G)) T2) ->
    is_type G (TAll T1 T2)
| t_sel: forall G e T1 T2,
    is_type G T1 -> (* redundant, but needed for induction(?) *)
    is_type G T2 ->
    has_type G e (TMem T1 T2) ->
    is_type G (TSel e)

with has_type : tenv -> tm -> ty -> Set :=
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           is_type env T1 ->
           has_type env (tvar (varF x)) T1

(*
(* pack a recursive type  *)
| t_var_pack : forall G1 x T1 T1',
           (* has_type G1 (tvar x) T1' -> *)
           indexr x G1 = Some (open (varF x) T1) ->
           T1' = (open (varF x) T1) ->
           closed 1 0 (length G1) T1 ->
           has_type G1 (tvar (varF x)) (TBind T1)
(* unpack a recursive type: unpack(x:{z=>T^z}) { x:T^x => ... }  *)
| t_unpack: forall env x y T1 T1' T2,
           has_type env x (TBind T1) ->
           T1' = (open (varF (length env)) T1) ->
           has_type (T1'::env) y T2 ->
           closed 0 0 (length env) T2 ->
           has_type env (tunpack x y) T2
 *)

(* type selection intro and elim forms *)
| t_sel2: forall env e a T1,
          has_type env a T1 ->
          has_type env e (TMem T1 TTop) ->
          has_type env a (TSel e)

| t_sel1: forall env e a T1,
          has_type env a (TSel e) ->
          has_type env e (TMem TBot T1) ->
          has_type env a T1


(* intersection typing *)
(*
| t_and : forall env x T1 T2,
           has_type env (tvar x) T1 ->
           has_type env (tvar x) T2 ->
           has_type env (tvar x) (TAnd T1 T2)
*)

| t_typ: forall env T1,
           is_type env T1 ->
           has_type env (ttyp T1) (TMem T1 T1)

| t_app: forall env f x T1 T2,
           has_type env f (TAll T1 T2) ->
           has_type env x T1 ->
           closed 0 (length env) T2 -> (* TODO: dependent app! *)
           has_type env (tapp f x) T2
(*
| t_dapp:forall env f x T1 T2 T,
           has_type env f (TAll T1 T2) ->
           has_type env (tvar (varF x)) T1 ->
           T = open (varF x) T2 ->
           closed 0 0 (length env) T ->
           has_type env (tapp f (tvar (varF x))) T
*)
| t_abs: forall env y T1 T2,
           is_type env T1 ->
           has_type (T1::env) y (open (varF (length env)) T2) ->
           has_type env (tabs T1 y) (TAll T1 T2)
(*
| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2
*)
.

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
      | tvar (varF x) => Some (indexr x env)
      (* remove varH *)
        (* | tvar (varH x) => Some None *)
        | tvar (varB x) => Some None
        | ttyp T       => Some (Some (vty env T))
        | tabs T y     => Some (Some (vabs env T y))
        | tapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vabs env2 _ ey)) =>
                  teval n (vx::env2) ey
              end
          end
        | tunpack ex ey =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              teval n (vx::env) ey
          end
      end
  end.

Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).

End D.

(* Target language (inspired by https://docs.racket-lang.org/pie/index.html):

 t ::= x | Unit | Type
     | (z: T) -> T^z  | lambda x:T.t | t t
     | Sigma z:T. T^z | (t, t)  | fst t | snd t *)

Declare Scope cc_scope.

Require Import FunInd.
Require Import Recdef.

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

(* Note: pairs are *not* values, because we allow sigma types at the type-level only atm *)
Inductive vl : Type :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> tm -> tm -> vl. (* TODO: do we need to ensure that a proper type is put into the first tm arg?  *)

Module Notations.

(* \square *)
Notation "◻" := (Kind Box) : cc_scope.
(* \star *)
Notation "⋆" := (Kind Star) : cc_scope.

End Notations.

Import Notations.

Definition tenv := list tm.
Definition venv := list vl.

Open Scope cc_scope.

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

Inductive closed: nat(*B*) -> nat(*F*) -> tm -> Prop :=
| cl_kind: forall i j U,
    closed i j (Kind U)
| cl_top: forall i j,
    closed i j TTop
| cl_bot: forall i j,
    closed i j TBot
| cl_all: forall i j T1 T2,
    closed i j T1 ->
    closed (S i) j T2 ->
    closed i j (TAll T1 T2)
| cl_sig: forall i j T1 T2,
    closed i j T1 ->
    closed (S i) j T2 ->
    closed i j (TSig T1 T2)
| cl_tvarb: forall i j x,
    i > x ->
    closed i j (tvar (varB x))
| cl_tvarf: forall i j x,
    j > x ->
    closed i j (tvar (varF x))
| cl_tabs:  forall i j ty tm,
    closed i j ty ->
    closed (S i) j tm ->
    closed i j (tabs ty tm)
| cl_tapp:  forall i j tm1 tm2,
    closed i j tm1 ->
    closed i j tm2 ->
    closed i j (tapp tm1 tm2)
| cl_tsig:  forall i j tm1 tm2,
    closed i j tm1 ->
    closed i j tm2 ->
    closed i j (tsig tm1 tm2)
| cl_tfst:  forall i j tm,
    closed i j tm ->
    closed i j (tfst tm)
| cl_tsnd:  forall i j tm,
    closed i j tm ->
    closed i j (tsnd tm)
.

Inductive has_type : tenv -> tm -> tm -> Prop :=
| t_box: forall Gamma,
    has_type Gamma ⋆ ◻

| t_var: forall x Gamma T,
    indexr x Gamma = Some T ->
    has_type Gamma (tvar (varF x)) T

| t_allt: forall Gamma T1 T2 U U',
    has_type Gamma T1 (Kind U) ->
    has_type (T1 :: Gamma) (open (varF (length Gamma)) T2) (Kind U') ->
    has_type Gamma (TAll T1 T2) (Kind U')

| t_sigt: forall Gamma T1 T2, (* support strong Sigma-types consistently, for now, have them at the type level *)
    has_type Gamma T1 ◻ ->
    has_type (T1 :: Gamma) (open (varF (length Gamma)) T2) ◻ ->
    has_type Gamma (TSig T1 T2) ◻

| t_topt: forall Gamma,
    has_type Gamma TTop ⋆

| t_bott: forall Gamma,
    has_type Gamma TBot ⋆

| t_abs: forall Gamma t T1 T2 U U',
    has_type Gamma T1 (Kind U) ->
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
    has_type Gamma (tsig e1 e1) (TSig T1 T2)

| t_fst: forall Gamma e T1 T2,
    has_type Gamma e (TSig T1 T2) ->
    has_type Gamma (tfst e) T1

| t_snd: forall Gamma e T1 T2 T,
    has_type Gamma e (TSig T1 T2) ->
    T = (open' (tfst e) T2) ->
    has_type Gamma (tsnd e) T

(* TODO equality/tconv? *)
.

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
  | 0 => None
  | S n =>
    match t with
    | tvar (varF x) => Some (indexr x env)
    | tvar (varB x) => Some None
    | tabs T y     =>  Some (Some (vabs env T y))
    | tapp ef ex   =>
      match teval n env ex with
      | None => None
      | Some None => Some None
      | Some (Some vx) =>
        match teval n env ef with
        | None => None
        | Some None => Some None
        | Some (Some (vabs env2 _ ey)) => teval n (vx::env2) ey
        end
      end
    | _ => None
    end
  end.

Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).

Fixpoint tsize_flat(T: tm) :=
  match T with
    | TTop => 1
    | TBot => 1
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSig T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | _ => 0
  end.
Lemma open_preserves_size: forall T x j,
    tsize_flat T = tsize_flat (open_rec j (tvar (varF x)) T).
Proof.
  intros T. induction T; intros; simpl; eauto. simpl.
  - destruct k; auto.
  - destruct v; eauto.  simpl; destruct (beq_nat j i); eauto.
Qed.

(* Definition vset k := *)
(*   match k with *)
(*   | Box => _ *)
(*   | Star => vl -> Prop *)
(*   end *)

Definition vset: Type := vl -> Prop.
Definition renv := list vset.

Function val_type (rho: renv) (T: tm) (v: vl) {measure tsize_flat T} : Prop :=
  match T, v with
  | TTop, _ => True
  (* | TAll x x0 => _ *)
  (* | TSig x x0 => _ *)
  (* | tvar x => _ *)
  (* | tabs x x0 => _ *)
  (* | tapp x x0 => _ *)
  (* | tsig x x0 => _ *)
  (* | tfst x => _ *)
  (* | tsnd x => _ *)
  | _, _ => False
  end.
Qed.

(* TODO val_type_unfold *)
(* TODO: define strong normalization *)

End CC.
