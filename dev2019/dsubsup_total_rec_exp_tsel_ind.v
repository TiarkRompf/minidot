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
| varH : id -> var (* free, in abstract environment  *)
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

Inductive closed: nat(*B*) -> nat(*H*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall i j k,
    closed i j k TTop
| cl_bot: forall i j k,
    closed i j k TBot
| cl_all: forall i j k T1 T2,
    closed i j k T1 ->
    closed (S i) j k T2 ->
    closed i j k (TAll T1 T2)
(* Now we have mutually recursive definitions for closedness on types and terms! *)
| cl_sel_tm: forall i j k t,
    closed_tm i j k t ->
    closed i j k (TSel t)
| cl_mem: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TMem T1 T2)
| cl_bind: forall i j k T,
    closed (S i) j k T ->
    closed i j k (TBind T)
| cl_and: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TAnd T1 T2)


with closed_tm: nat(*B*) -> nat(*H*) -> nat(*F*) -> tm -> Prop :=
| cl_tvarb: forall i j k x,
    i > x ->
    closed_tm i j k (tvar (varB x))
| cl_tvarh: forall i j k x,
    j > x ->
    closed_tm i j k (tvar (varH x))
| cl_tvarf: forall i j k x,
    k > x ->
    closed_tm i j k (tvar (varF x))
| cl_ttyp:  forall i j k ty,
    closed i j k ty ->
    closed_tm i j k (ttyp ty)
| cl_tabs:  forall i j k ty tm,
    closed i j k ty ->
    closed_tm (S i) j k tm ->
    closed_tm i j k (tabs ty tm)
| cl_tapp:  forall i j k tm1 tm2,
    closed_tm i j k tm1 ->
    closed_tm i j k tm2 ->
    closed_tm i j k (tapp tm1 tm2)
| cl_tunpack: forall i j k tm1 tm2,
    closed_tm i j k tm1 ->
    closed_tm (S i) j k tm2 ->
    closed_tm i j k (tunpack tm1 tm2)
.

(* open define a locally-nameless encoding wrt to TVarB type variables. *)
(* substitute var u for all occurrences of (varB k) *)
Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TSel tm => TSel (open_rec_tm k u tm)
    (* | TSel (tvar (varF x)) => TSel (tvar (varF x)) *)
    (* | TSel (tvar (varH i)) => TSel (tvar (varH i)) *)
    (* | TSel (tvar (varB i)) => if beq_nat k i then TSel (tvar u) else TSel (tvar (varB i)) *)
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
    | TBind T => TBind (open_rec (S k) u T)
    | TAnd T1 T2 => TAnd (open_rec k u T1) (open_rec k u T2)
  end

with open_rec_tm (k: nat) (u: var) (t: tm) { struct t }: tm :=
       match t with
       | tvar (varF x) => tvar (varF x)
       | tvar (varH x) => tvar (varH x)
       | tvar (varB x) =>
         if beq_nat k x then (tvar u) else (tvar (varB x))
       | ttyp ty => ttyp (open_rec k u ty)
       | tabs ty tm => tabs (open_rec k u ty) (open_rec_tm (S k) u tm)
       | tapp tm1 tm2 => tapp (open_rec_tm k u tm1) (open_rec_tm k u tm2)
       | tunpack tm1 tm2 => tunpack (open_rec_tm k u tm1) (open_rec_tm (S k) u tm2)
       end.

Definition open u T := open_rec 0 u T.
Definition open_tm u t := open_rec_tm 0 u t.

(* Locally-nameless encoding with respect to varH variables. *)
Fixpoint subst (U : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TSel t       => TSel (subst_tm U t)
    | TMem T1 T2     => TMem (subst U T1) (subst U T2)
    | TBind T       => TBind (subst U T)
    | TAnd T1 T2    => TAnd (subst U T1)(subst U T2)
  end

with subst_tm (U: var) (t: tm) {struct t} : tm :=
       match t with
       | tvar (varB i) => (tvar (varB i))
       | tvar (varF i) => (tvar (varF i))
       | tvar (varH i) => if beq_nat i 0 then tvar U else  (tvar (varH (i-1)))
       | ttyp ty => ttyp (subst U ty)
       | tabs ty tm => tabs (subst U ty) (subst_tm U tm)
       | tapp tm1 tm2 => tapp (subst_tm U tm1) (subst_tm U tm2)
       | tunpack tm1 tm2 => tunpack (subst_tm U tm1) (subst_tm U tm2)
       end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TBot         => True
    | TAll T1 T2   => nosubst T1 /\ nosubst T2
    (* | TSel (tvar (varB i)) => True *)
    (* | TSel (tvar (varF i)) => True *)
    (* | TSel (tvar (varH i)) => i <> 0 *)
    | TSel t       => nosubst_tm t
    | TMem T1 T2    => nosubst T1 /\ nosubst T2
    | TBind T       => nosubst T
    | TAnd T1 T2    => nosubst T1 /\ nosubst T2
  end

with nosubst_tm (t: tm) {struct t} : Prop :=
       match t with
       | tvar (varB _) => True
       | tvar (varF _) => True
       | tvar (varH i) => i <> 0
       | ttyp ty =>  nosubst ty
       | tabs ty tm => (nosubst ty) /\ (nosubst_tm tm)
       | tapp tm1 tm2 => (nosubst_tm tm1) /\ (nosubst_tm tm2)
       | tunpack tm1 tm2 => (nosubst_tm tm1) /\ (nosubst_tm tm2)
       end.

(* ### Subtyping ### *)
(*
Note: In contrast to the rules on paper, the subtyping
relation has two environments instead of just one.
(The same holds for the semantic types, val_type, below).
This split into an abstract and a concrete environment
was necessary in the D<: soundness development, but is
not required here. We just keep it for consistency with
our earlier Coq files.

The first env is for looking up varF variables.
The first env matches the concrete runtime environment, and is
extended during type assignment.
The second env is for looking up varH variables.
The second env matches the abstract runtime environment, and is
extended during subtyping.
*)
Inductive stp: tenv -> tenv -> ty -> ty -> Prop :=
| stp_top: forall G1 GH T1,
    closed 0 (length GH) (length G1) T1 ->
    stp G1 GH T1 TTop
| stp_bot: forall G1 GH T2,
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH TBot T2
| stp_mem: forall G1 GH S1 U1 S2 U2,
    stp G1 GH U1 U2 ->
    stp G1 GH S2 S1 ->
    stp G1 GH (TMem S1 U1) (TMem S2 U2)
(* we move type selection into the typing relation has_type below *)
(* | stp_sel1: forall G1 GH TX T2 tm, *)
(*     has_type G1 tm TX -> *)
(*     (* TODO: see if we can make the closedness conditions here and elsewhere *)
(*        an invariant of has_type *) *)
(*     closed 0 0 (length G1) TX -> *)
(*     closed_tm 0 0 (length G1) tm -> *)
(*     stp G1 GH TX (TMem TBot T2) -> *)
(*     stp G1 GH (TSel tm) T2 *)
(* | stp_sel2: forall G1 GH TX T1 tm, *)
(*     has_type G1 tm TX -> *)
(*     closed 0 0 (length G1) TX -> *)
(*     closed_tm 0 0 (length G1) tm -> *)
(*     stp G1 GH TX (TMem T1 TTop) -> *)
(*     stp G1 GH T1 (TSel tm) *)
| stp_selx: forall G1 GH tm, (*TODO rename the rule *)
    (* this will also handle the stp_selax case from the previous version *)
    closed_tm 0 (length GH) (length G1) tm ->
    stp G1 GH (TSel tm) (TSel tm)

(* TODO: it seems acceptable to adopt these from the previous version,
since varH occurrences are artifacts of subtyping  *)
| stp_sela1: forall G1 GH TX T2 x,
    indexr x GH = Some TX ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH (TSel (tvar (varH x))) T2
| stp_sela2: forall G1 GH TX T1 x,
    indexr x GH = Some TX ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 (TSel (tvar (varH x)))

(* this has become superfluous:   *)
(* | stp_selax: forall G1 GH v x, *)
(*     indexr x GH = Some v  -> *)
(*     stp G1 GH (TSel (tvar (varH x))) (TSel (tvar (varH x))) *)

(* stp for recursive types and intersection types *)
| stp_bindx: forall GH G1 T1 T1' T2 T2',
    stp G1 (T1'::GH) T1' T2' ->
    T1' = (open (varH (length GH)) T1) ->
    T2' = (open (varH (length GH)) T2) ->
    closed 1 (length GH) (length G1) T1 ->
    closed 1 (length GH) (length G1) T2 ->
    stp G1 GH (TBind T1) (TBind T2)

| stp_and11: forall GH G1 T1 T2 T,
    stp G1 GH T1 T ->
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH (TAnd T1 T2) T

| stp_and12: forall GH G1 T1 T2 T,
    stp G1 GH T2 T ->
    closed 0 (length GH) (length G1) T1 ->
    stp G1 GH (TAnd T1 T2) T

| stp_and2: forall GH G1 T1 T2 T,
    stp G1 GH T T1 ->
    stp G1 GH T T2 ->
    stp G1 GH T (TAnd T1 T2)

| stp_all: forall G1 GH T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G1) T4 ->
    stp G1 (T3::GH) (open (varH x) T2) (open (varH x) T4) ->
    stp G1 GH (TAll T1 T2) (TAll T3 T4)

| stp_trans: forall G1 GH T1 T2 T3,
    stp G1 GH T1 T2 ->
    stp G1 GH T2 T3 ->
    stp G1 GH T1 T3

(* ### Type Assignment ### *)
with has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           stp env [] T1 T1 ->
           has_type env (tvar (varF x)) T1
(* pack a recursive type  *)
| t_var_pack : forall G1 x T1,
           has_type G1 (tvar x) (open x T1) ->
           closed 1 0 (length G1) T1 ->
           has_type G1 (tvar x) (TBind T1)

           (* (* has_type G1 (tvar x) T1' -> *) *)
           (* indexr x G1 = Some (open (varF x) T1) -> *)
           (* T1' = (open (varF x) T1) -> *)
           (* closed 1 0 (length G1) T1 -> *)
           (* has_type G1 (tvar (varF x)) (TBind T1) *)
(* unpack a recursive type: unpack(x:{z=>T^z}) { x:T^x => ... }  *)
| t_unpack: forall env x y T1 T1' T2,
           has_type env x (TBind T1) ->
           T1' = (open (varF (length env)) T1) ->
           has_type (T1'::env) y T2 ->
           closed 0 0 (length env) T2 ->
           has_type env (tunpack x y) T2

(* intersection typing *)
| t_and : forall env x T1 T2,
           has_type env (tvar x) T1 ->
           has_type env (tvar x) T2 ->
           has_type env (tvar x) (TAnd T1 T2)


| t_typ: forall env T1,
           closed 0 0 (length env) T1 ->
           has_type env (ttyp T1) (TMem T1 T1)

| t_app: forall env f x T1 T2,
           has_type env f (TAll T1 T2) ->
           has_type env x T1 ->
           closed 0 0 (length env) T2 ->
           has_type env (tapp f x) T2
| t_dapp: forall env f x T1 T2 T,
           has_type env f (TAll T1 T2) ->
           has_type env (tvar (varF x)) T1 ->
           T = open (varF x) T2 ->
           closed 0 0 (length env) T ->
           has_type env (tapp f (tvar (varF x))) T
| t_abs: forall env y T1 T2,
           has_type (T1::env) y (open (varF (length env)) T2) ->
           closed 0 0 (length env) (TAll T1 T2) ->
           has_type env (tabs T1 y) (TAll T1 T2)
| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2

| t_sel_intro: forall env e1 e2 T,
    has_type env e1 T ->
    has_type env e2 (TMem T TTop) ->
    has_type env e1 (TSel e2)
| t_sel_elim: forall env e1 e2 T,
    has_type env e1 (TSel e2) ->
    has_type env e2 (TMem TBot T) ->
    has_type env e1 T
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
        | tvar (varH x) => Some None
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

(* Requires no termination proof and is invertible *)
Inductive logrel_ty: list vseta -> list vseta -> ty -> forall n, vset n -> vl -> Prop :=
| LTop: forall Gamma GH n vsn v, logrel_ty Gamma GH TTop n vsn v
| LTMem: forall Gamma GH n T1 vsn1 T2 vsn2 vl1 vl2 H Tx vsn,
    logrel_ty Gamma GH T1 n vsn1 vl1 ->
    logrel_ty Gamma GH T2 n vsn2 vl2 ->
    vset_sub_eq vsn1 vsn ->
    vset_sub_eq vsn vsn2 ->
    logrel_ty Gamma GH (TMem T1 T2) n vsn (vty H Tx)
| LTAll: forall Gamma GH n T1 T2 vsn1 vl1 vsn H T0 t,
    logrel_ty Gamma GH T1 n vsn1 vl1 ->
    (exists (vs2 : vseta) vl2,
      tevaln (vl1 :: H) t vl2
       /\ forall k, logrel_ty Gamma (vs2 :: GH) (open (varH (length Gamma)) T2) k (vs2 k) vl2) ->
    logrel_ty Gamma GH (TAll T1 T2) n vsn (vabs H T0 t)
| LTSel: forall Gamma GH n t vsn v,
    logrel_tm Gamma GH t n vsn v ->
    logrel_ty Gamma GH (TSel t) n vsn v
| LTAnd: forall Gamma GH n T1 T2 vsn v,
    logrel_ty Gamma GH T1 n vsn v ->
    logrel_ty Gamma GH T2 n vsn v ->
    logrel_ty Gamma GH (TAnd T1 T2) n vsn v
| LTBind: forall Gamma GH n T vsn v,
    (exists (vs: vseta),
        (vs n) = vsn
        /\ forall k, logrel_ty Gamma (vs :: GH) (open (varH (length GH)) T) k (vs k) v) ->
    logrel_ty Gamma GH (TBind T) n vsn v

with logrel_tm: list vseta -> list vseta -> tm -> forall n, vset n -> vl -> Prop :=
| LVarF: forall Gamma GH n x (vs: vseta) vsn v,
    (indexr x Gamma) = Some vs ->
    vs (S n) vsn v ->
    logrel_tm Gamma GH (tvar (varF x)) n vsn v
| LVarH: forall Gamma GH n x (vs: vseta) vsn v,
    (indexr x GH) = Some vs ->
    vs (S n) vsn v ->
    logrel_tm Gamma GH (tvar (varH x)) n vsn v
| LTTyp: forall Gamma GH n T vsn v,
    logrel_ty Gamma GH T n vsn v ->
    logrel_tm Gamma GH (ttyp T) n vsn v
.


(* consistent environment *)
Definition R_env venv genv tenv :=
  length venv = length tenv /\
  length genv = length tenv /\
  forall x TX, indexr x tenv = Some TX ->
    (exists (jj:vseta) vx,
       indexr x venv = Some vx /\
       indexr x genv = Some jj /\
       forall n, logrel_ty genv [] TX n (jj n) vx).


(* automation *)
Hint Unfold venv.
Hint Unfold tenv.

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


Theorem full_total_safety : forall e tenv T,
  has_type tenv e T -> forall venv renv, R_env venv renv tenv ->
  exists (d: vseta) v, tevaln venv e v /\ forall k, logrel_ty renv [] T k (d k) v.
Proof.
  intros ? ? ? W.
  induction W; intros ? ? WFE.
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
    unfold R_env in WFE. destruct WFE as [Hlen1 [Hlen2  Hlookup]].
    exists d0. exists v0.
    split.
    auto.
    intros k.
    Admitted.
