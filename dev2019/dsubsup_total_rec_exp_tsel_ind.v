(* Termination for D<:> with intersection types and recursive self types *)
(* this version includes a proof of totality  *)

(*
 DSub (D<:) + Bot + /\ + { z => ... }
 T ::= Top | Bot | x.Type | { Type: S..U } | (z: T) -> T^z | T1 /\ T2 | { z => T^z }
 t ::= x | { Type = T } | lambda x:T.t | t t | unpack(t) { x => t }
 *)

(* copied from ecoop17/dsubsup_total_rec.v *)

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

(* An environment is a list of values, indexed by decrementing ids. *)

Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.

Inductive closed: nat(*B*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall i k,
    closed i k TTop
| cl_bot: forall i k,
    closed i k TBot
| cl_all: forall i k T1 T2,
    closed i k T1 ->
    closed (S i) k T2 ->
    closed i k (TAll T1 T2)
(* Now we have mutually recursive definitions for closedness on types and terms! *)
| cl_sel_tm: forall i k t,
    closed_tm i k t ->
    closed i k (TSel t)
| cl_mem: forall i k T1 T2,
    closed i k T1 ->
    closed i k T2 ->
    closed i k (TMem T1 T2)
| cl_bind: forall i k T,
    closed (S i) k T ->
    closed i k (TBind T)
| cl_and: forall i k T1 T2,
    closed i k T1 ->
    closed i k T2 ->
    closed i k (TAnd T1 T2)


with closed_tm: nat(*B*) -> nat(*F*) -> tm -> Prop :=
| cl_tvarb: forall i k x,
    i > x ->
    closed_tm i k (tvar (varB x))
| cl_tvarf: forall i k x,
    k > x ->
    closed_tm i k (tvar (varF x))
| cl_ttyp:  forall i k ty,
    closed i k ty ->
    closed_tm i k (ttyp ty)
| cl_tabs:  forall i k ty tm,
    closed i k ty ->
    closed_tm (S i) k tm ->
    closed_tm i k (tabs ty tm)
| cl_tapp:  forall i k tm1 tm2,
    closed_tm i k tm1 ->
    closed_tm i k tm2 ->
    closed_tm i k (tapp tm1 tm2)
| cl_tunpack: forall i k tm1 tm2,
    closed_tm i k tm1 ->
    closed_tm (S i) k tm2 ->
    closed_tm i k (tunpack tm1 tm2)
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

(* (* Locally-nameless encoding with respect to varH variables. *) *)
(* Fixpoint subst (U : var) (T : ty) {struct T} : ty := *)
(*   match T with *)
(*     | TTop         => TTop *)
(*     | TBot         => TBot *)
(*     | TAll T1 T2   => TAll (subst U T1) (subst U T2) *)
(*     | TSel t       => TSel (subst_tm U t) *)
(*     | TMem T1 T2     => TMem (subst U T1) (subst U T2) *)
(*     | TBind T       => TBind (subst U T) *)
(*     | TAnd T1 T2    => TAnd (subst U T1)(subst U T2) *)
(*   end *)

(* with subst_tm (U: var) (t: tm) {struct t} : tm := *)
(*        match t with *)
(*        | tvar (varB i) => (tvar (varB i)) *)
(*        | tvar (varF i) => (tvar (varF i)) *)
(*        | tvar (varH i) => if beq_nat i 0 then tvar U else  (tvar (varH (i-1))) *)
(*        | ttyp ty => ttyp (subst U ty) *)
(*        | tabs ty tm => tabs (subst U ty) (subst_tm U tm) *)
(*        | tapp tm1 tm2 => tapp (subst_tm U tm1) (subst_tm U tm2) *)
(*        | tunpack tm1 tm2 => tunpack (subst_tm U tm1) (subst_tm U tm2) *)
(*        end. *)

(* Fixpoint nosubst (T : ty) {struct T} : Prop := *)
(*   match T with *)
(*     | TTop         => True *)
(*     | TBot         => True *)
(*     | TAll T1 T2   => nosubst T1 /\ nosubst T2 *)
(*     (* | TSel (tvar (varB i)) => True *) *)
(*     (* | TSel (tvar (varF i)) => True *) *)
(*     (* | TSel (tvar (varH i)) => i <> 0 *) *)
(*     | TSel t       => nosubst_tm t *)
(*     | TMem T1 T2    => nosubst T1 /\ nosubst T2 *)
(*     | TBind T       => nosubst T *)
(*     | TAnd T1 T2    => nosubst T1 /\ nosubst T2 *)
(*   end *)

(* with nosubst_tm (t: tm) {struct t} : Prop := *)
(*        match t with *)
(*        | tvar (varB _) => True *)
(*        | tvar (varF _) => True *)
(*        | tvar (varH i) => i <> 0 *)
(*        | ttyp ty =>  nosubst ty *)
(*        | tabs ty tm => (nosubst ty) /\ (nosubst_tm tm) *)
(*        | tapp tm1 tm2 => (nosubst_tm tm1) /\ (nosubst_tm tm2) *)
(*        | tunpack tm1 tm2 => (nosubst_tm tm1) /\ (nosubst_tm tm2) *)
(*        end. *)

(* ### Subtyping ### *)
Inductive stp: tenv -> ty -> ty -> Prop :=
| stp_top: forall Gamma T1,
    closed 0 (length Gamma) T1 ->
    stp Gamma T1 TTop
| stp_bot: forall Gamma T2,
    closed 0 (length Gamma) T2 ->
    stp Gamma TBot T2
| stp_mem: forall Gamma S1 U1 S2 U2,
    stp Gamma U1 U2 ->
    stp Gamma S2 S1 ->
    stp Gamma (TMem S1 U1) (TMem S2 U2)
(* we move type selection into the typing relation has_type below *)
(* | stp_sel1: forall Gamma GH TX T2 tm, *)
(*     has_type Gamma tm TX -> *)
(*     (* TODO: see if we can make the closedness conditions here and elsewhere *)
(*        an invariant of has_type *) *)
(*     closed 0 0 (length Gamma) TX -> *)
(*     closed_tm 0 0 (length Gamma) tm -> *)
(*     stp Gamma GH TX (TMem TBot T2) -> *)
(*     stp Gamma GH (TSel tm) T2 *)
(* | stp_sel2: forall Gamma GH TX T1 tm, *)
(*     has_type Gamma tm TX -> *)
(*     closed 0 0 (length Gamma) TX -> *)
(*     closed_tm 0 0 (length Gamma) tm -> *)
(*     stp Gamma GH TX (TMem T1 TTop) -> *)
(*     stp Gamma GH T1 (TSel tm) *)
| stp_sel: forall Gamma tm,
    closed_tm 0 (length Gamma) tm ->
    stp Gamma (TSel tm) (TSel tm)

(* stp for recursive types and intersection types *)
| stp_bindx: forall  Gamma T1 T1' T2 T2',
    stp (T1'::Gamma) T1' T2' ->
    T1' = (open (varF (length Gamma)) T1) ->
    T2' = (open (varF (length Gamma)) T2) ->
    closed 1 (length Gamma) T1 ->
    closed 1 (length Gamma) T2 ->
    stp Gamma (TBind T1) (TBind T2)

| stp_and11: forall Gamma T1 T2 T,
    stp Gamma T1 T ->
    closed 0 (length Gamma) T2 ->
    stp Gamma (TAnd T1 T2) T

| stp_and12: forall Gamma T1 T2 T,
    stp Gamma T2 T ->
    closed 0 (length Gamma) T1 ->
    stp Gamma (TAnd T1 T2) T

| stp_and2: forall Gamma T1 T2 T,
    stp Gamma T T1 ->
    stp Gamma T T2 ->
    stp Gamma T (TAnd T1 T2)

| stp_all: forall Gamma T1 T2 T3 T4 x,
    stp Gamma T3 T1 ->
    x = length Gamma ->
    closed 1 (length Gamma) T2 ->
    closed 1 (length Gamma) T4 ->
    stp (T3::Gamma) (open (varF x) T2) (open (varF x) T4) ->
    stp Gamma (TAll T1 T2) (TAll T3 T4)

| stp_trans: forall Gamma T1 T2 T3,
    stp Gamma T1 T2 ->
    stp Gamma T2 T3 ->
    stp Gamma T1 T3

(* ### Type Assignment ### *)
with has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x Gamma T1,
           indexr x Gamma = Some T1 ->
           stp Gamma T1 T1 -> (* TODO necessary? *)
           has_type Gamma (tvar (varF x)) T1
(* pack a recursive type  *)
| t_var_pack : forall Gamma x T1,
           has_type Gamma (tvar x) (open x T1) ->
           closed 1 (length Gamma) T1 ->
           has_type Gamma (tvar x) (TBind T1)

           (* (* has_type G1 (tvar x) T1' -> *) *)
           (* indexr x G1 = Some (open (varF x) T1) -> *)
           (* T1' = (open (varF x) T1) -> *)
           (* closed 1 0 (length G1) T1 -> *)
           (* has_type G1 (tvar (varF x)) (TBind T1) *)
(* unpack a recursive type: unpack(x:{z=>T^z}) { x:T^x => ... }  *)
| t_unpack: forall Gamma x y T1 T1' T2,
           has_type Gamma x (TBind T1) ->
           T1' = (open (varF (length Gamma)) T1) ->
           has_type (T1'::Gamma) y T2 ->
           closed 0 (length Gamma) T2 ->
           has_type Gamma (tunpack x y) T2

(* intersection typing *)
| t_and : forall Gamma x T1 T2,
           has_type Gamma (tvar x) T1 ->
           has_type Gamma (tvar x) T2 ->
           has_type Gamma (tvar x) (TAnd T1 T2)


| t_typ: forall Gamma T1,
           closed 0 (length Gamma) T1 ->
           has_type Gamma (ttyp T1) (TMem T1 T1)

| t_app: forall Gamma f x T1 T2,
           has_type Gamma f (TAll T1 T2) ->
           has_type Gamma x T1 ->
           closed 0 (length Gamma) T2 ->
           has_type Gamma (tapp f x) T2
| t_dapp: forall Gamma f x T1 T2 T,
           has_type Gamma f (TAll T1 T2) ->
           has_type Gamma (tvar (varF x)) T1 ->
           T = open (varF x) T2 ->
           closed 0 (length Gamma) T ->
           has_type Gamma (tapp f (tvar (varF x))) T
| t_abs: forall Gamma y T1 T2,
           has_type (T1::Gamma) y (open (varF (length Gamma)) T2) ->
           closed 0 (length Gamma) (TAll T1 T2) ->
           has_type Gamma (tabs T1 y) (TAll T1 T2)
| t_sub: forall Gamma e T1 T2,
           has_type Gamma e T1 ->
           stp Gamma T1 T2 ->
           has_type Gamma e T2

| t_sel_intro: forall Gamma e1 e2 T,
    has_type Gamma e1 T ->
    has_type Gamma e2 (TMem T TTop) ->
    has_type Gamma e1 (TSel e2)
| t_sel_elim: forall Gamma e1 e2 T,
    has_type Gamma e1 (TSel e2) ->
    has_type Gamma e2 (TMem TBot T) ->
    has_type Gamma e1 T
.




(* ### Evaluation (Big-Step Semantics) ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
Could use do-notation to clean up syntax.
*)
(* Type ((Type Int).Type) -> Type Int  *)

(*
unclear: normalization of terms in types, separate from bigstep teval?
*)
Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar (varF x) => Some (indexr x env)
        | tvar (varB x) => Some None
        | ttyp T       => Some (Some (vty env T)) (* TODO: should T be normalized? *)
        | tabs T y     => Some (Some (vabs env T y)) (* TODO: should T be normalized? *)
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

Fixpoint vset n := match n with
                     | 0 => vl -> Prop
                     | S n => vset n -> vl -> Prop
                   end.

Definition vseta := forall n, vset n.

Definition vseta_top: vseta :=
  fun n =>
    match n with
    | 0 => fun _ => True
    | S n => fun _ _ => True
    end.

Definition vseta_bot: vseta :=
  fun n =>
    match n with
    | 0 => fun _ => False
    | S n => fun _ _ => False
    end.

(* Subset relation at given index n. *)
Definition vset_sub_eq {n:nat}: vset n -> vset n -> Prop :=
  match n with
       | 0 => fun vs1 vs2 => True
       | S n => fun vs1 vs2 => forall vs' v, (vs1 vs' v) -> (vs2 vs' v)
       end.

(* Subset relation closing over all n.*)
Definition vseta_sub_eq (vs1: vseta) (vs2: vseta) :=
  forall n, vset_sub_eq (vs1 n) (vs2 n).

Definition renv := list vseta.

Inductive sn: renv -> ty -> venv -> tm -> Prop :=
| SN: forall rho T H t,
    (exists (vs: vseta) v,
      tevaln H t v /\ forall n, logrel_ty rho T n (vs n) v) ->
    sn rho T H t
with
  logrel_ty: renv -> ty -> forall n, vset n -> vl -> Prop :=
| LTop: forall rho n vsn v,
    logrel_ty rho TTop n vsn v

| LTMem: forall rho n T1 vsn1 T2 vsn2 vl1 vl2 H Tx vsn,
    logrel_ty rho T1 n vsn1 vl1 ->
    logrel_ty rho T2 n vsn2 vl2 ->
    vset_sub_eq vsn1 vsn ->
    vset_sub_eq vsn vsn2 ->
    logrel_ty rho (TMem T1 T2) n vsn (vty H Tx)

| LTAll: forall rho n T1 T2 vsn H T0 t,
    (* Rejected due to negative position *)
    (* (forall vsn1 vl1, logrel_ty rho T1 n vsn1 vl1 -> *)
    (* (exists (vs2 : vseta) vl2, *)
    (*   tevaln (vl1 :: H) t vl2 *)
    (*   /\ forall k, logrel_ty (vs2 :: rho) (open (varF (length rho)) T2) k (vs2 k) vl2)) -> *)
    (forall vs1 vl1,
        (forall k, logrel_ty rho T1 k (vs1 k) vl1) ->
        sn (vs1 :: rho) (open (varF (length rho)) T2) (vl1 :: H) t)
    ->
    logrel_ty rho (TAll T1 T2) n vsn (vabs H T0 t)

| LTSel: forall rho n t vsn v,
    logrel_tm rho t n vsn v ->
    logrel_ty rho (TSel t) n vsn v

| LTAnd: forall rho n T1 T2 vsn v,
    logrel_ty rho T1 n vsn v ->
    logrel_ty rho T2 n vsn v ->
    logrel_ty rho (TAnd T1 T2) n vsn v

| LTBind: forall rho n T vsn v,
    (exists (vs: vseta),
        (vs n) = vsn
        /\ forall k, logrel_ty (vs :: rho) (open (varF (length rho)) T) k (vs k) v) ->
    logrel_ty rho (TBind T) n vsn v

with logrel_tm: list vseta -> tm -> forall n, vset n -> vl -> Prop :=
| LVarF: forall rho n x (vs: vseta) vsn v,
    (indexr x rho) = Some vs ->
    vs (S n) vsn v ->
    logrel_tm rho (tvar (varF x)) n vsn v

| LTTyp: forall rho n T vsn v,
    logrel_ty rho T n vsn v ->
    logrel_tm rho (ttyp T) n vsn v
.

(* consistent environment *)
Definition R_env venv rho Gamma :=
  length venv = length Gamma /\
  length rho = length Gamma /\
  forall x TX, indexr x Gamma = Some TX ->
    (exists (vsx:vseta) vx,
       indexr x venv = Some vx /\
       indexr x rho = Some vsx /\
       forall n, logrel_ty rho TX n (vsx n) vx).


(* automation *)
Hint Unfold venv.
Hint Unfold tenv.
Hint Unfold renv.

Hint Unfold open.
Hint Unfold indexr.
Hint Unfold length.

(* Hint Unfold R. *)
Hint Unfold R_env.

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Hint Constructors closed.
Hint Constructors has_type.
Hint Constructors stp.

Hint Constructors option.
Hint Constructors list.

Hint Resolve ex_intro.

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.

Theorem full_total_safety : forall e Gamma T,
  has_type Gamma e T -> forall venv rho, R_env venv rho Gamma ->
  exists (d: vseta) v, tevaln venv e v /\ forall k, logrel_ty rho T k (d k) v.
Proof.
  intros ? ? ? W.
  induction W; intros ? ? WFE.
  5: {
    eexists. exists (vty venv0 T1).
    split. exists 0.
    intros. destruct n. omega. auto.
    unfold R_env in WFE. destruct WFE as [Hlen1 [Hlen2  Hlookup]].
    intros.
    econstructor.

    -
    auto. simpl.
  }

  - unfold R_env in WFE. destruct WFE as [Hlen1 [Hlen2  Hlookup]].
    apply Hlookup in H.
    destruct H as [d0 [v0 [? [? ?]]]].
    exists d0. exists v0.
    split.
    unfold tevaln.
    exists 0. intros.
    destruct n. omega. simpl.
    congruence.
    auto.
  - (* t-var-pack *)
    assert (Wit := WFE).
    apply IHW in Wit.
    destruct Wit as [d0 [v0 [? ?]]].
    unfold R_env in WFE. ev.
    exists d0. exists v0.
    Admitted.
