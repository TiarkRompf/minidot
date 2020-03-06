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

(* term variables occurring in types, both languages share the same variables definition *)
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

(* ### Type Formation & Assignment ### *)
Inductive ty_wf: tenv -> ty -> Set :=
| wf_top: forall Gamma,
    ty_wf Gamma TTop
| wf_bot: forall Gamma,
    ty_wf Gamma TBot
| wf_mem: forall Gamma T1 T2,
    ty_wf Gamma T1 ->
    ty_wf Gamma T2 ->
    ty_wf Gamma (TMem T1 T2)
| wf_all: forall Gamma T1 T2,
    ty_wf Gamma T1 ->
    ty_wf (T1::Gamma) (open (varF (length Gamma)) T2) ->
    ty_wf Gamma (TAll T1 T2)
| wf_sel: forall Gamma e T1 T2,
    ty_wf Gamma T1 -> (* redundant, but needed for induction(?) *)
    ty_wf Gamma T2 ->
    has_type Gamma e (TMem T1 T2) ->
    ty_wf Gamma (TSel e)

with has_type : tenv -> tm -> ty -> Set :=
| t_var: forall x Gamma T1,
    indexr x Gamma = Some T1 ->
    ty_wf Gamma T1 ->
    has_type Gamma (tvar (varF x)) T1

(*
(* pack a recursive type  *)
| t_var_pack : forall G1 x T1 T1',
           (* has_type G1 (tvar x) T1' -> *)
           indexr x G1 = Some (open (varF x) T1) ->
           T1' = (open (varF x) T1) ->
           closed 1 0 (length G1) T1 ->
           has_type G1 (tvar (varF x)) (TBind T1)
(* unpack a recursive type: unpack(x:{z=>T^z}) { x:T^x => ... }  *)
| t_unpack: forall Gamma x y T1 T1' T2,
           has_type Gamma x (TBind T1) ->
           T1' = (open (varF (length Gamma)) T1) ->
           has_type (T1'::Gamma) y T2 ->
           closed 0 0 (length Gamma) T2 ->
           has_type Gamma (tunpack x y) T2
 *)

(* type selection intro and elim forms *)
| t_seli: forall Gamma e a T1,
          has_type Gamma a T1 ->
          has_type Gamma e (TMem T1 TTop) ->
          has_type Gamma a (TSel e)

| t_sele: forall Gamma e a T1,
          has_type Gamma a (TSel e) ->
          has_type Gamma e (TMem TBot T1) ->
          has_type Gamma a T1


(* intersection typing *)
(*
| t_and : forall Gamma x T1 T2,
           has_type Gamma (tvar x) T1 ->
           has_type Gamma (tvar x) T2 ->
           has_type Gamma (tvar x) (TAnd T1 T2)
*)

| t_typ: forall Gamma T1,
           ty_wf Gamma T1 ->
           has_type Gamma (ttyp T1) (TMem T1 T1)

| t_app: forall Gamma f x T1 T2,
           has_type Gamma f (TAll T1 T2) ->
           has_type Gamma x T1 ->
           closed 0 (length Gamma) T2 -> (* TODO: dependent app! *)
           has_type Gamma (tapp f x) T2
(*
| t_dapp:forall Gamma f x T1 T2 T,
           has_type Gamma f (TAll T1 T2) ->
           has_type Gamma (tvar (varF x)) T1 ->
           T = open (varF x) T2 ->
           closed 0 0 (length Gamma) T ->
           has_type Gamma (tapp f (tvar (varF x))) T
*)
| t_abs: forall Gamma y T1 T2,
           ty_wf Gamma T1 ->
           has_type (T1::Gamma) y (open (varF (length Gamma)) T2) ->
           has_type Gamma (tabs T1 y) (TAll T1 T2)
(*
| t_sub: forall Gamma e T1 T2,
           has_type Gamma e T1 ->
           stp Gamma [] T1 T2 ->
           has_type Gamma e T2
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

Inductive sort : Type :=
| Star : sort (* Universe of CC types *)
| Box :  sort (* Universe of CC kinds  *)
.

Definition sort_max (s s' : sort): sort :=
  match s, s' with
  | Box, _ | _, Box => Box
  | _, _ => Star
  end.

Inductive tm : Type := (* TODO what about equality types? *)
| Sort : sort -> tm
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

Inductive vl : Type :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> tm -> tm -> vl (* TODO: do we need to ensure that a proper type is put into the first tm arg?  *)
| vsig : vl -> vl -> vl
.

Definition tenv := list tm.
Definition venv := list vl.

Module Notations.

(* \square *)
Notation "◻" := (Sort Box) : cc_scope.
(* \star *)
Notation "⋆" := (Sort Star) : cc_scope.

End Notations.

Import Notations.
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
    closed i j (Sort U)
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

(* TODO: not clear if needed *)
(* Inductive ctx_wf: tenv -> Prop := *)
(* | wf_empty: *)
(*     ctx_wf [] *)
(* | wf_sort: forall Gamma T U, *)
(*     ctx_wf Gamma -> *)
(*     has_type Gamma T (Sort U) -> *)
(*     ctx_wf (T :: Gamma) *)
(* with *)

Inductive has_type : tenv -> tm -> tm -> Type :=
| t_box: forall Gamma,
    has_type Gamma ⋆ ◻

| t_var: forall x Gamma T U,
    (* ctx_wf Gamma -> *)
    indexr x Gamma = Some T ->
    has_type Gamma T (Sort U) ->
    has_type Gamma (tvar (varF x)) T

| t_allt: forall Gamma T1 T2 U U',
    has_type Gamma T1 (Sort U) ->
    has_type (T1 :: Gamma) (open (varF (length Gamma)) T2) (Sort U') ->
    has_type Gamma (TAll T1 T2) (Sort U')

(* Enable consistent strong Sigma-types, (cf. Definition 5.1 in [Geuvers '94]),
   forbidding (◻, ⋆, ⋆), (⋆, ◻, ⋆), (◻, ◻, ⋆), (⋆, ⋆, ◻) in the formation rule.*)
| t_sigt: forall Gamma T1 T2 U1 U2 U3,
    U3 = sort_max U1 U2 ->
    has_type Gamma T1 (Sort U1) ->
    has_type (T1 :: Gamma) (open (varF (length Gamma)) T2) (Sort U2) ->
    has_type Gamma (TSig T1 T2) (Sort U3)

| t_topt: forall Gamma,
    has_type Gamma TTop ⋆

| t_bott: forall Gamma,
    has_type Gamma TBot ⋆

| t_abs: forall Gamma t T1 T2 U U',
    has_type Gamma T1 (Sort U) ->
    has_type Gamma (TAll T1 T2) (Sort U') ->
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
        | Some None => Some None
        | Some (Some (vabs env2 _ ey)) => teval n (vx::env2) ey
        | _ => None
        end
      end
    | tsig t1 t2 =>
      match teval n env t1 with
      | None => None
      | Some None => Some None
      | Some (Some v1) =>
        match teval n env t2 with
        | None => None
        | Some None => Some None
        | Some (Some v2) => Some (Some (vsig v1 v2))
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
  - destruct s; auto.
  - destruct v; eauto.  simpl; destruct (beq_nat j i); eauto.
Qed.

Definition vset := vl -> Prop.

(*
  This computes the *types* of the sets that kinds represent (cf. V(_) interp in Geuvers '94),
  i.e., this is a dependent type indexed by the kinds in the system . Since we lump
  everything into one syntactic category, we define it inductively over typing derivations yielding ◻. *)
Fixpoint kind_set Gamma K (proof: has_type Gamma K ◻): Type :=
  match proof with
  | t_box _ => (* ⋆ *)
    vset
  | t_var x Gamma T Box _ T_is_kind =>
    (kind_set Gamma T T_is_kind)
  | t_allt Gamma T1 T2 Box Box T1_is_kind T2_is_kind =>  (* Πα:T1.T2, T1:◻ *)
    let V1 := (kind_set Gamma T1 T1_is_kind) in
    let V2 := (kind_set (T1 :: Gamma) (open (varF (length Gamma)) T2) T2_is_kind) in
    V1 -> V2
  | t_allt Gamma T1 T2 Star Box p1 p2 => (* Πα:T1.T2, T1:⋆ *)
    (kind_set (T1 :: Gamma) (open (varF (length Gamma)) T2) p2)
  | t_sigt Gamma T1 T2 Box Box Box _ T1_is_kind T2_is_kind => (* Σα:T1.T2, T1:◻, T2:◻  *)
    let V1 := (kind_set Gamma T1 T1_is_kind) in
    let V2 := (kind_set (T1 :: Gamma) (open (varF (length Gamma)) T2) T2_is_kind) in
    V1 -> V2 -> Prop (* V1 × V2 *)
  | t_sigt Gamma T1 T2 Star Box Box _ _ T2_is_kind => (* Σα:T1.T2, T1:⋆, T2:◻ *)
    (kind_set (T1 :: Gamma) (open (varF (length Gamma)) T2) T2_is_kind)
  | t_sigt Gamma T1 T2 Box Star Box _ T1_is_kind _ => (* Σα:T1.T2, T1:◻, T2:⋆ *)
    (kind_set Gamma T1 T1_is_kind)
  | _ => False
  end.

(* Design idea:
   terms and types are separate GADTs indexed by their sort, classifying their universe.
   Might yield more concise and readable definitions (such as kind_set).
Inductive ty: sort -> Type :=
| TAll : forall s s',
    ty s -> ty s' -> ty s'
| TSig : forall s s',
    ty s -> ty s' -> ty s'
| TTm: forall s,
    tm s -> ty s
with tm: sort -> Type :=
| tvar : forall s,
    var -> tm s (* TODO: might make sense to index variables with their sort *)
| tabs : forall s s',
    ty s -> tm s' -> tm s'
| tapp : forall s s',
    tm s -> tm s' -> tm s (* TODO: correct? *)
| tsig : forall s s',
    ty s -> tm s' -> tm s'
| tfst : forall s, tm s -> tm s
| tsnd : forall s, tm s -> tm s
| tty: forall s, ty s -> tm s
.

Potentially interesting, since we could define
a sort-indexed evaluator, that describes evaluation/normalization
at runtime and at type level.
*)


Definition renv := list vset.

(* TODO adapt the definitions in Geuvers '94, starting at p. 20 to sets of values *)
Function val_type (rho: renv) (T: tm) (v: vl) {measure tsize_flat T} : Prop :=
  match T, v with
  | TTOP, _ => True
  | _, _ => False
  end.
Qed.

(* TODO val_type_unfold *)

Definition R_env gamma rho Gamma :=
  length gamma = length Gamma /\
  length rho = length Gamma /\
  forall x TX, indexr x Gamma = Some TX ->
          (exists (vsx:vset) vx,
              indexr x gamma = Some vx /\
              indexr x rho = Some vsx /\
              val_type rho TX vx).

Definition strong_normalization := forall e Gamma T,
      has_type Gamma e T ->
      has_type Gamma T ⋆ ->
      forall gamma rho, R_env gamma rho Gamma ->
              exists v, tevaln gamma e v.

(* TODO: prove strong normalization *)

End CC.
