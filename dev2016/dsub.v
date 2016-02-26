(*
 DSub (D<:)
 T ::= Top | x.Type | { Type = T } | { Type <: T } | (z: T) -> T^z
 t ::= x | { Type = T } | lambda x:T.t | t t
 *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.

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
(* (z: T) -> T^z *)
| TAll : ty -> ty -> ty
(* x.Type *)
| TSel : var -> ty
(* { Type = T } or { Type <: T } *)
| TMem : bool(* whether alias (=: true) vs upper-bounded (<: false) *) -> ty -> ty
.

Inductive tm : Type :=
(* x -- free variable, matching concrete environment *)
| tvar : id -> tm
(* { Type = T } *)
| ttyp : ty -> tm
(* lambda x:T.t *)
| tabs : ty -> tm -> tm
(* t t *)
| tapp : tm -> tm -> tm
.

Inductive vl : Type :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> ty -> tm -> vl
(* a closure for a first-class type *)
| vty : list vl (*H*) -> ty -> vl
.

Definition tenv := list ty. (* Gamma environment: static *)
Definition venv := list vl. (* H environment: run-time *)
Definition aenv := list (venv*ty). (* J environment: abstract at run-time *)

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
| cl_all: forall i j k T1 T2,
    closed i j k T1 ->
    closed (S i) j k T2 ->
    closed i j k (TAll T1 T2)
| cl_sel: forall i j k x,
    k > x ->
    closed i j k (TSel (varF x))
| cl_selh: forall i j k x,
    j > x ->
    closed i j k (TSel (varH x))
| cl_selb: forall i j k x,
    i > x ->
    closed i j k (TSel (varB x))
| cl_mem: forall i j k b T,
    closed i j k T ->
    closed i j k (TMem b T)
.

(* open define a locally-nameless encoding wrt to TVarB type variables. *)
(* substitute var u for all occurrences of (varB k) *)
Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TSel (varF x) => TSel (varF x)
    | TSel (varH i) => TSel (varH i)
    | TSel (varB i) => if beq_nat k i then TSel u else TSel (varB i)
    | TMem b T0  => TMem b (open_rec k u T0)
  end.

Definition open u T := open_rec 0 u T.

(* Locally-nameless encoding with respect to varH variables. *)
Fixpoint subst (U : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TSel (varB i) => TSel (varB i)
    | TSel (varF i) => TSel (varF i)
    | TSel (varH i) => if beq_nat i 0 then TSel U else TSel (varH (i-1))
    | TMem b T0     => TMem b (subst U T0)
  end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TAll T1 T2   => nosubst T1 /\ nosubst T2
    | TSel (varB i) => True
    | TSel (varF i) => True
    | TSel (varH i) => i <> 0
    | TMem b T0     => nosubst T0
  end.

(* ### Static Subtyping ### *)
(*
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
| stp_mem: forall G1 GH b1 T1 b2 T2,
    stp G1 GH T1 T2 ->
    b2 = false \/ (b1 = true /\ b2 = true /\ stp G1 GH T2 T1) ->
    stp G1 GH (TMem b1 T1) (TMem b1 T2)
| stp_sel1: forall G1 GH b T T2 x,
    indexr x G1 = Some (TMem b T) ->
    closed 0 0 (length G1) T ->
    stp G1 GH T T2 ->
    stp G1 GH (TSel (varF x)) T2
| stp_sel2: forall G1 GH T T1 x,
    indexr x G1 = Some (TMem true T) ->
    closed 0 0 (length G1) T ->
    stp G1 GH T1 T ->
    stp G1 GH T1 (TSel (varF x))
| stp_selx: forall G1 GH v x,
    (* This is a bit looser than just being able to select on TMem vars. *)
    indexr x G1 = Some v ->
    stp G1 GH (TSel (varF x)) (TSel (varF x))
| stp_sela1: forall G1 GH b T T2 x,
    indexr x GH = Some (TMem b T) ->
    closed 0 x (length G1) T ->
    stp G1 GH T T2 ->
    stp G1 GH (TSel (varH x)) T2
| stp_sela2: forall G1 GH T T1 x,
    indexr x GH = Some (TMem true T) ->
    closed 0 x (length G1) T ->
    stp G1 GH T1 T ->
    stp G1 GH T1 (TSel (varH x))
| stp_selax: forall G1 GH v x,
    (* This is a bit looser than just being able to select on TMem vars. *)
    indexr x GH = Some v  ->
    stp G1 GH (TSel (varH x)) (TSel (varH x))
| stp_all: forall G1 GH T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G1) T4 ->
    stp G1 (T3::GH) (open (varH x) T2) (open (varH x) T4) ->
    stp G1 GH (TAll T1 T2) (TAll T3 T4)
.

(* ### Type Assignment ### *)
Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           stp env [] T1 T1 ->
           has_type env (tvar x) T1
| t_app: forall env f x T1 T2,
           has_type env f (TAll T1 T2) ->
           has_type env x T1 ->
           closed 0 0 (length env) T2 ->
           has_type env (tapp f x) T2
| t_dapp:forall env f x T1 T2 T,
           has_type env f (TAll T1 T2) ->
           has_type env (tvar x) T1 ->
           T = open (varF x) T2 ->
           closed 0 0 (length env) T ->
           has_type env (tapp f (tvar x)) T
| t_abs: forall env y T1 T2,
           has_type (T1::env) y (open (varF (length env)) T2) ->
           closed 0 0 (length env) (TAll T1 T2) ->
           has_type env (tabs T1 y) (TAll T1 T2)
| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2
.

(* ### Runtime Subtyping ### *)
(* H1 T1 <: H2 T2 -| J *)
Inductive stp2: bool (* whether the last rule may not be transitivity *) ->
                venv -> ty -> venv -> ty -> aenv  ->
                nat (* derivation size *) ->
                Prop :=
| stp2_top: forall G1 G2 GH T n,
    closed 0 (length GH) (length G1) T ->
    stp2 true G1 T G2 TTop GH (S n)
| stp2_mem: forall G1 G2 b1 T1 b2 T2 GH n1 n2,
    stp2 false G1 T1 G2 T2 GH n1 ->
    b2 = false \/ (b1 = true /\ b2 = true /\ stp2 false G2 T2 G1 T1 GH n2) ->
    stp2 true G1 (TMem b1 T1) G2 (TMem b2 T2) GH (S n1)

(* concrete type variables *)
(* vty already marks binding as type binding, so need for additional TMem marker *)
| stp2_sel1: forall G1 G2 GX TX x T2 GH n1,
    indexr x G1 = Some (vty GX TX) ->
    closed 0 0 (length GX) TX ->
    stp2 true GX TX G2 T2 GH n1 ->
    stp2 true G1 (TSel (varF x)) G2 T2 GH (S n1)
| stp2_sel2: forall G1 G2 GX TX x T1 GH n1,
    indexr x G2 = Some (vty GX TX) ->
    closed 0 0 (length GX) TX ->
    stp2 false G1 T1 GX TX GH n1 ->
    stp2 true G1 T1 G2 (TSel (varF x)) GH (S n1)
| stp2_selx: forall G1 G2 v x1 x2 GH n,
    indexr x1 G1 = Some v ->
    indexr x2 G2 = Some v ->
    stp2 true G1 (TSel (varF x1)) G2 (TSel (varF x2)) GH (S n)

(* abstract type variables *)
(* X<:T, one sided *)
| stp2_sela1: forall G1 G2 GX TX x T2 GH n1,
    indexr x GH = Some (GX, TX) ->
    closed 0 x (length GX) TX ->
    stp2 false GX TX G2 T2 GH n1 ->
    stp2 true G1 (TSel (varH x)) G2 T2 GH (S n1)
| stp2_selax: forall G1 G2 v x GH n,
    indexr x GH = Some v ->
    stp2 true G1 (TSel (varH x)) G2 (TSel (varH x)) GH (S n)

| stp2_all: forall G1 G2 T1 T2 T3 T4 x GH n1 n2,
    stp2 false G2 T3 G1 T1 GH n1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G2) T4 ->
    stp2 false G1 (open (varH x) T2) G2 (open (varH x) T4) ((G2, T3)::GH) n2 ->
    stp2 true G1 (TAll T1 T2) G2 (TAll T3 T4) GH (S (n1 + n2))

| stp2_wrapf: forall G1 G2 T1 T2 GH n1,
    stp2 true G1 T1 G2 T2 GH n1 ->
    stp2 false G1 T1 G2 T2 GH (S n1)

| stp2_transf: forall G1 G2 G3 T1 T2 T3 GH n1 n2,
    stp2 true G1 T1 G2 T2 GH n1 ->
    stp2 false G2 T2 G3 T3 GH n2 ->
    stp2 false G1 T1 G3 T3 GH (S (n1+n2))
.

(* consistent environment *)
Inductive wf_env : venv -> tenv -> Prop :=
| wfe_nil : wf_env nil nil
| wfe_cons : forall v t vs ts,
    val_type (v::vs) v t ->
    wf_env vs ts ->
    wf_env (cons v vs) (cons t ts)

(* value type assignment *)
with val_type : venv -> vl -> ty -> Prop :=
| v_ty: forall env venv tenv T1 TE,
    wf_env venv tenv ->
    (exists n, stp2 true venv (TMem T1) env TE [] n) ->
    val_type env (vty venv T1) TE
| v_abs: forall env venv tenv x y T1 T2 TE,
    wf_env venv tenv ->
    has_type (T1::tenv) y T2 ->
    length venv = x ->
    (exists n, stp2 true venv (TFun T1 T2) env TE [] n) ->
    val_type env (vabs venv T1 y) TE
| v_tabs: forall env venv tenv x y T1 T2 TE,
    wf_env venv tenv ->
    has_type ((TMem T1)::tenv) y (open (TVarF x) T2) ->
    length venv = x ->
    (exists n, stp2 true venv (TAll T1 T2) env TE [] n) ->
    val_type env (vtabs venv T1 y) TE
.

Inductive wf_envh : venv -> aenv -> tenv -> Prop :=
| wfeh_nil : forall vvs, wf_envh vvs nil nil
| wfeh_cons : forall t vs vvs ts,
    wf_envh vvs vs ts ->
    wf_envh vvs (cons (vvs,t) vs) (cons (TMem t) ts)
.

Inductive valh_type : venv -> aenv -> (venv*ty) -> ty -> Prop :=
| v_tya: forall aenv venv T1,
    valh_type venv aenv (venv, T1) (TMem T1)
.

(* ### Evaluation (Big-Step Semantics) ### *)

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v

Could use do-notation to clean up syntax.
*)

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tvar x     => Some (indexr x env)
        | tabs T y => Some (Some (vabs env T y))
        | ttabs T y  => Some (Some (vtabs env T y))
        | tapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vtabs _ _ _)) => Some None
                | Some (Some (vabs env2 _ ey)) =>
                  teval n (vx::env2) ey
              end
          end
        | ttapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vty _ _)) => Some None
            | Some (Some (vabs _ _ _)) => Some None
            | Some (Some (vtabs env2 T ey)) =>
              teval n ((vty env ex)::env2) ey
          end
      end
  end.

(* automation *)
Hint Unfold venv.
Hint Unfold tenv.

Hint Unfold open.
Hint Unfold indexr.
Hint Unfold length.

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Hint Constructors closed.
Hint Constructors has_type.
Hint Constructors val_type.
Hint Constructors wf_env.
Hint Constructors stp.
Hint Constructors stp2.

Hint Constructors option.
Hint Constructors list.

Hint Resolve ex_intro.

(* ############################################################ *)
(* Examples *)
(* ############################################################ *)

Ltac crush_has_tp :=
  try solve [eapply stp_selx; compute; eauto; crush_has_tp];
  try solve [eapply stp_selax; compute; eauto; crush_has_tp];
  try solve [eapply cl_selb; compute; eauto; crush_has_tp];
  try solve [(econstructor; compute; eauto; crush_has_tp)].

Ltac crush2 :=
  try solve [(eapply stp_selx; compute; eauto; crush2)];
  try solve [(eapply stp_selax; compute; eauto; crush2)];
  try solve [(eapply stp_sel1; compute; eauto; crush2)];
  try solve [(eapply stp_sela1; compute; eauto; crush2)];
  try solve [(eapply cl_selb; compute; eauto; crush2)];
  try solve [(econstructor; compute; eauto; crush2)];
  try solve [(eapply t_sub; eapply t_var; compute; eauto; crush2)].

(* define polymorphic identity function *)

Definition polyId := TAll TTop (TFun (TVarB 0) (TVarB 0)).

Example ex1: has_type [] (ttabs TTop (tabs (TVarF 0) (tvar 1))) polyId.
Proof.
  crush_has_tp.
Qed.

(* instantiate it to TTop *)
Example ex2: has_type [polyId] (ttapp (tvar 0) TTop) (TFun TTop TTop).
Proof.
  crush2.
Qed.


(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)

Fixpoint tsize(T: ty) :=
  match T with
    | TTop => 1
    | TFun T1 T2 => S (tsize T1 + tsize T2)
    | TAll T1 T2 => S (tsize T1 + tsize T2)
    | TVarF _ => 1
    | TVarH _ => 1
    | TVarB _ => 1
    | TMem T0 => S (tsize T0)
  end.

Lemma open_preserves_size: forall T x j,
  tsize T = tsize (open_rec j (TVarH x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  - simpl. destruct (beq_nat j i); eauto.
Qed.

(* ## Extension, Regularity ## *)

Lemma wf_length : forall vs ts,
                    wf_env vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  compute. eauto.
Qed.

Hint Immediate wf_length.

Lemma wfh_length : forall vvs vs ts,
                    wf_envh vvs vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  compute. eauto.
Qed.

Hint Immediate wfh_length.

Lemma indexr_max : forall X vs n (T: X),
                       indexr n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  - Case "nil". intros. inversion H.
  - Case "cons".
    intros. inversion H.
    case_eq (beq_nat n (length vs)); intros E2.
    + SSCase "hit".
      eapply beq_nat_true in E2. subst n. compute. eauto.
    + SSCase "miss".
      rewrite E2 in H1.
      assert (n < length vs). eapply IHvs. apply H1.
      compute. eauto.
Qed.

Lemma le_xx : forall a b,
                       a <= b ->
                       exists E, le_lt_dec a b = left E.
Proof. intros.
  case_eq (le_lt_dec a b). intros. eauto.
  intros. omega.
Qed.
Lemma le_yy : forall a b,
                       a > b ->
                       exists E, le_lt_dec a b = right E.
Proof. intros.
  case_eq (le_lt_dec a b). intros. omega.
  intros. eauto.
Qed.

Lemma indexr_extend : forall X vs n x (T: X),
                       indexr n vs = Some T ->
                       indexr n (x::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply indexr_max. eauto.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff. omega.
  unfold indexr. unfold indexr in H. rewrite H. rewrite E. reflexivity.
Qed.

(* splicing -- for stp_extend. *)

Fixpoint splice n (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TFun T1 T2   => TFun (splice n T1) (splice n T2)
    | TAll T1 T2   => TAll (splice n T1) (splice n T2)
    | TVarF i      => TVarF i
    | TVarB i      => TVarB i
    | TVarH i      => if le_lt_dec n i then TVarH (i+1) else TVarH i
    | TMem T0      => TMem (splice n T0)
  end.

Definition spliceat n (V: (venv*ty)) :=
  match V with
    | (G,T) => (G,splice n T)
  end.

Lemma splice_open_permute: forall {X} (G0:list X) T2 n j,
(open_rec j (TVarH (n + S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open_rec j (TVarH (n + length G0)) T2)).
Proof.
  intros X G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto.

  case_eq (le_lt_dec (length G) i); intros E LE; simpl; eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  case_eq (le_lt_dec (length G) (n + length G)); intros EL LE.
  assert (n + S (length G) = n + length G + 1). omega.
  rewrite H. eauto.
  omega.
Qed.

Lemma indexr_splice_hi: forall G0 G2 x0 v1 T,
    indexr x0 (G2 ++ G0) = Some T ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (splice (length G0)) G2 ++ v1 :: G0) = Some (splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. omega.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma indexr_spliceat_hi: forall G0 G2 x0 v1 G T,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (spliceat (length G0)) G2 ++ v1 :: G0) =
    Some (G, splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. omega.
  - simpl in H. destruct a.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma plus_lt_contra: forall a b,
  a + b < b -> False.
Proof.
  intros a b H. induction a.
  - simpl in H. apply lt_irrefl in H. assumption.
  - simpl in H. apply IHa. omega.
Qed.

Lemma indexr_splice_lo0: forall {X} G0 G2 x0 (T:X),
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 G0 = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl in H. apply H.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E. subst.
      rewrite app_length in H0. apply plus_lt_contra in H0. inversion H0.
    + rewrite E in H. apply IHG2. apply H. apply H0.
Qed.

Lemma indexr_extend_mult: forall {X} G0 G2 x0 (T:X),
    indexr x0 G0 = Some T ->
    indexr x0 (G2++G0) = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl. assumption.
  - simpl.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E.
      apply indexr_max in H. subst.
      rewrite app_length in H. apply plus_lt_contra in H. inversion H.
    + apply IHG2. assumption.
Qed.

Lemma indexr_splice_lo: forall G0 G2 x0 v1 T f,
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 (map (splice f) G2 ++ v1 :: G0) = Some T.
Proof.
  intros.
  assert (indexr x0 G0 = Some T). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.

Lemma indexr_spliceat_lo: forall G0 G2 x0 v1 G T f,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    x0 < length G0 ->
    indexr x0 (map (spliceat f) G2 ++ v1 :: G0) = Some (G, T).
Proof.
  intros.
  assert (indexr x0 G0 = Some (G, T)). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.

Lemma closed_splice: forall i j k T n,
  closed i j k T ->
  closed i (S j) k (splice n T).
Proof.
  intros. induction H; simpl; eauto.
  case_eq (le_lt_dec n x); intros E LE.
  apply cl_selh. omega.
  apply cl_selh. omega.
Qed.

Lemma map_splice_length_inc: forall G0 G2 v1,
   (length (map (splice (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma map_spliceat_length_inc: forall G0 G2 v1,
   (length (map (spliceat (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_inc_mult: forall i j k T,
  closed i j k T ->
  forall i' j' k',
  i' >= i -> j' >= j -> k' >= k ->
  closed i' j' k' T.
Proof.
  intros i j k T H. induction H; intros; eauto; try solve [constructor; omega].
  - apply cl_all. apply IHclosed1; omega. apply IHclosed2; omega.
Qed.

Lemma closed_inc: forall i j k T,
  closed i j k T ->
  closed i (S j) k T.
Proof.
  intros. apply (closed_inc_mult i j k T H i (S j) k); omega.
Qed.

Lemma closed_splice_idem: forall i j k T n,
                            closed i j k T ->
                            n >= j ->
                            splice n T = T.
Proof.
  intros. induction H; eauto.
  - (* TFun *) simpl.
    rewrite IHclosed1. rewrite IHclosed2.
    reflexivity.
    assumption. assumption.
  - (* TAll *) simpl.
    rewrite IHclosed1. rewrite IHclosed2.
    reflexivity.
    assumption. assumption.
  - (* TVarH *) simpl.
    case_eq (le_lt_dec n x); intros E LE. omega. reflexivity.
  - (* TMem *) simpl.
    rewrite IHclosed.
    reflexivity. assumption.
Qed.

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.

Lemma stp_closed : forall G GH T1 T2,
                     stp G GH T1 T2 ->
                     closed 0 (length GH) (length G) T1 /\ closed 0 (length GH) (length G) T2.
Proof.
  intros. induction H;
    try solve [repeat ev; split; eauto using indexr_max].
Qed.

Lemma stp_closed2 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) (length G1) T2.
Proof.
  intros. apply (proj2 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp_closed1 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) (length G1) T1.
Proof.
  intros. apply (proj1 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp2_closed: forall G1 G2 T1 T2 GH m n,
                     stp2 m G1 T1 G2 T2 GH n ->
                     closed 0 (length GH) (length G1) T1 /\ closed 0 (length GH) (length G2) T2.
  intros. induction H;
    try solve [repeat ev; split; eauto using indexr_max].
Qed.

Lemma stp2_closed2 : forall G1 G2 T1 T2 GH m n,
                       stp2 m G1 T1 G2 T2 GH n ->
                       closed 0 (length GH) (length G2) T2.
Proof.
  intros. apply (proj2 (stp2_closed G1 G2 T1 T2 GH m n H)).
Qed.

Lemma stp2_closed1 : forall G1 G2 T1 T2 GH m n,
                       stp2 m G1 T1 G2 T2 GH n ->
                       closed 0 (length GH) (length G1) T1.
Proof.
  intros. apply (proj1 (stp2_closed G1 G2 T1 T2 GH m n H)).
Qed.

Lemma closed_upgrade: forall i j k i' T,
 closed i j k T ->
 i' >= i ->
 closed i' j k T.
Proof.
 intros. apply (closed_inc_mult i j k T H i' j k); omega.
Qed.

Lemma closed_upgrade_free: forall i j k j' T,
 closed i j k T ->
 j' >= j ->
 closed i j' k T.
Proof.
 intros. apply (closed_inc_mult i j k T H i j' k); omega.
Qed.

Lemma closed_upgrade_freef: forall i j k k' T,
 closed i j k T ->
 k' >= k ->
 closed i j k' T.
Proof.
 intros. apply (closed_inc_mult i j k T H i j k'); omega.
Qed.

Lemma closed_open: forall i j k TX T, closed (i+1) j k T -> closed i j k TX ->
  closed i j k (open_rec i TX T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.
  eapply closed_upgrade. eauto. eauto.
  - Case "TVarB". simpl.
    case_eq (beq_nat i0 i); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
Qed.

Lemma indexr_has: forall X (G: list X) x,
  length G > x ->
  exists v, indexr x G = Some v.
Proof.
  intros. remember (length G) as n.
  generalize dependent x.
  generalize dependent G.
  induction n; intros; try omega.
  destruct G; simpl.
  - simpl in Heqn. inversion Heqn.
  - simpl in Heqn. inversion Heqn. subst.
    case_eq (beq_nat x (length G)); intros E.
    + eexists. reflexivity.
    + apply beq_nat_false in E. apply IHn; eauto.
      omega.
Qed.

Lemma stp_refl_aux: forall n T G GH,
  closed 0 (length GH) (length G) T ->
  tsize T < n ->
  stp G GH T T.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst; eauto;
  try solve [omega];
  try solve [simpl in H0; constructor; apply IHn; eauto; try omega];
  try solve [apply indexr_has in H1; destruct H1; eauto].
  - simpl in H0.
    eapply stp_all.
    eapply IHn; eauto; try omega.
    reflexivity.
    assumption.
    assumption.
    apply IHn; eauto.
    simpl. apply closed_open; auto using closed_inc.
    unfold open. rewrite <- open_preserves_size. omega.
Qed.

Lemma stp_refl: forall T G GH,
  closed 0 (length GH) (length G) T ->
  stp G GH T T.
Proof.
  intros. apply stp_refl_aux with (n:=S (tsize T)); eauto.
Qed.

Definition stpd2 m G1 T1 G2 T2 GH := exists n, stp2 m G1 T1 G2 T2 GH n.

Ltac ep := match goal with
             | [ |- stp2 ?M ?G1 ?T1 ?G2 ?T2 ?GH ?N ] =>
               assert (exists (n:nat), stp2 M G1 T1 G2 T2 GH n) as EEX
           end.

Ltac eu := match goal with
             | H: stpd2 _ _ _ _ _ _ |- _ =>
               destruct H as [? H]
           end.

Hint Unfold stpd2.

Lemma stp2_refl_aux: forall n T G GH,
  closed 0 (length GH) (length G) T ->
  tsize T < n ->
  stpd2 true G T G T GH.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst; eauto; try omega; try simpl in H0.
  - destruct (IHn T1 G GH) as [n1 IH1]; eauto; try omega.
    destruct (IHn T2 G GH) as [n2 IH2]; eauto; try omega.
    eexists; constructor; try constructor; eauto.
  - destruct (IHn T1 G GH) as [n1 IH1]; eauto; try omega.
    destruct (IHn (open (TVarH (length GH)) T2) G ((G,T1)::GH)); eauto; try omega.
    simpl. apply closed_open; auto using closed_inc.
    unfold open. rewrite <- open_preserves_size. omega.
    eexists; econstructor; try constructor; eauto.
  - eapply indexr_has in H1. destruct H1 as [v HI].
    eexists; eapply stp2_selx; eauto.
  - eapply indexr_has in H1. destruct H1 as [v HI].
    eexists; eapply stp2_selax; eauto.
  - destruct (IHn T0 G GH) as [n0 IH0]; eauto; try omega.
Grab Existential Variables. apply 0. apply 0. apply 0.
Qed.

Lemma stp2_refl: forall T G GH,
  closed 0 (length GH) (length G) T ->
  stpd2 true G T G T GH.
Proof.
  intros. apply stp2_refl_aux with (n:=S (tsize T)); eauto.
Qed.

Lemma stp_splice : forall GX G0 G1 T1 T2 v1,
   stp GX (G1++G0) T1 T2 ->
   stp GX ((map (splice (length G0)) G1) ++ v1::G0)
       (splice (length G0) T1) (splice (length G0) T2).
Proof.
  intros GX G0 G1 T1 T2 v1 H. remember (G1++G0) as G.
  revert G0 G1 HeqG.
  induction H; intros; subst GH; simpl; eauto.
  - Case "top".
    eapply stp_top.
    rewrite map_splice_length_inc.
    apply closed_splice.
    assumption.
  - Case "sel1".
    eapply stp_sel1. apply H. assumption.
    assert (splice (length G0) T=T) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp. reflexivity.
  - Case "sela1".
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + apply stp_sela1 with (T:=(splice (length G0) T)).
      assert (TMem (splice (length G0) T)=(splice (length G0) (TMem T))) as B by auto.
      rewrite B. apply indexr_splice_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x = x +1) as A by omega.
      rewrite <- A. eapply H0.
      eapply IHstp. eauto.
    + eapply stp_sela1. eapply indexr_splice_lo. eauto. eauto. eauto. eauto.
      assert (splice (length G0) T=T) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp. eauto.
  - Case "selax".
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_selax.
      eapply indexr_splice_hi. eassumption. assumption.
    + eapply stp_selax. eapply indexr_splice_lo. eauto. eauto.
  - Case "all".
    eapply stp_all.
    eapply IHstp1. eauto. eauto. eauto.

    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.

    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.

    specialize IHstp2 with (G3:=G0) (G4:=(TMem T3) :: G2).
    simpl in IHstp2. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x.
    rewrite app_length in IHstp2. simpl in IHstp2.
    eapply IHstp2. eauto.
Qed.

Lemma stp2_splice : forall G1 T1 G2 T2 GH1 GH0 v1 m n,
   stp2 m G1 T1 G2 T2 (GH1++GH0) n ->
   stp2 m G1 (splice (length GH0) T1) G2 (splice (length GH0) T2)
        ((map (spliceat (length GH0)) GH1) ++ v1::GH0) n.
Proof.
  intros G1 T1 G2 T2 GH1 GH0 v1 m n H. remember (GH1++GH0) as GH.
  revert GH0 GH1 HeqGH.
  induction H; intros; subst GH; simpl; eauto.
  - Case "top".
    eapply stp2_top.
    rewrite map_spliceat_length_inc.
    apply closed_splice.
    assumption.
  - Case "sel1".
    eapply stp2_sel1. apply H. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp2.
    reflexivity.
  - Case "sel2".
    eapply stp2_sel2. apply H. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp2.
    reflexivity.
  - Case "sela1".
    case_eq (le_lt_dec (length GH0) x); intros E LE.
    + eapply stp2_sela1. eapply indexr_spliceat_hi. apply H. eauto.
      eapply closed_splice in H0. assert (S x = x +1) by omega. rewrite <- H2.
      eapply H0.
      eapply IHstp2. eauto.
    + eapply stp2_sela1. eapply indexr_spliceat_lo. apply H. eauto. eauto.
      assert (splice (length GH0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp2. eauto.
  - Case "selax".
    case_eq (le_lt_dec (length GH0) x); intros E LE.
    + destruct v. eapply stp2_selax.
      eapply indexr_spliceat_hi. apply H. eauto.
    + destruct v. eapply stp2_selax.
      eapply indexr_spliceat_lo. apply H. eauto.
  - Case "all".
    apply stp2_all with (x:= length GH1 + S (length GH0)).
    eapply IHstp2_1. reflexivity.

    simpl. rewrite map_spliceat_length_inc. rewrite app_length. omega.
    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.
    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.

    subst x.
    specialize IHstp2_2 with (GH2:=GH0) (GH3:=(G2, T3) :: GH1).
    simpl in IHstp2_2.
    repeat rewrite splice_open_permute with (j:=0).
    rewrite app_length in IHstp2_2.
    eapply IHstp2_2. reflexivity.
Qed.

Lemma stp_extend : forall G1 GH T1 T2 v1,
                       stp G1 GH T1 T2 ->
                       stp G1 (v1::GH) T1 T2.
Proof.
  intros. induction H; eauto using indexr_extend, closed_inc.
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. apply H1. omega.
  }
  assert (splice (length GH) T4 = T4) as A4. {
    eapply closed_splice_idem. apply H2. omega.
  }
  assert (TVarH (S (length GH)) = splice (length GH) (TVarH (length GH))) as AH. {
    simpl. case_eq (le_lt_dec (length GH) (length GH)); intros E LE.
    simpl. rewrite NPeano.Nat.add_1_r. reflexivity.
    clear LE. apply lt_irrefl in E. inversion E.
  }
  assert (closed 0 (length GH) (length G1) T3). eapply stp_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (splice (length GH)) [TMem T3] ++ v1::GH =
          ((TMem T3)::v1::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  apply stp_all with (x:=length (v1 :: GH)).
  apply IHstp1.
  reflexivity.
  apply closed_inc. apply H1.
  apply closed_inc. apply H2.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (TVarH (S (length GH))) with (TVarH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  rewrite <- HGX3.
  apply stp_splice.
  simpl. unfold open in H3. rewrite <- H0. apply H3.
Qed.

Lemma stp_extend_mult : forall G T1 T2 GH GH2,
                       stp G GH T1 T2 ->
                       stp G (GH2++GH) T1 T2.
Proof.
  intros. induction GH2.
  - simpl. assumption.
  - simpl.
    apply stp_extend. assumption.
Qed.

Lemma indexr_at_index: forall {A} x0 GH0 GH1 (v:A),
  beq_nat x0 (length GH1) = true ->
  indexr x0 (GH0 ++ v :: GH1) = Some v.
Proof.
  intros. apply beq_nat_true in H. subst.
  induction GH0.
  - simpl. rewrite <- beq_nat_refl. reflexivity.
  - simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    rewrite false_beq_nat. assumption. omega.
Qed.

Lemma indexr_same: forall {A} x0 (v0:A) GH0 GH1 (v:A) (v':A),
  beq_nat x0 (length GH1) = false ->
  indexr x0 (GH0 ++ v :: GH1) = Some v0 ->
  indexr x0 (GH0 ++ v' :: GH1) = Some v0.
Proof.
  intros ? ? ? ? ? ? ? E H.
  induction GH0.
  - simpl. rewrite E. simpl in H. rewrite E in H. apply H.
  - simpl.
    rewrite app_length. simpl.
    case_eq (beq_nat x0 (length GH0 + S (length GH1))); intros E'.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite H. reflexivity.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite IHGH0. reflexivity. assumption.
Qed.

Inductive venv_ext : venv -> venv -> Prop :=
| venv_ext_refl : forall G, venv_ext G G
| venv_ext_cons : forall T G1 G2, venv_ext G1 G2 -> venv_ext (T::G1) G2.

Inductive aenv_ext : aenv -> aenv -> Prop :=
| aenv_ext_nil : aenv_ext nil nil
| aenv_ext_cons :
    forall T G' G A A',
      aenv_ext A' A -> venv_ext G' G ->
      aenv_ext ((G',T)::A') ((G,T)::A).

Lemma aenv_ext_refl: forall GH, aenv_ext GH GH.
Proof.
  intros. induction GH.
  - apply aenv_ext_nil.
  - destruct a. apply aenv_ext_cons.
    assumption.
    apply venv_ext_refl.
Qed.

Lemma venv_ext__ge_length:
  forall G G',
    venv_ext G' G ->
    length G' >= length G.
Proof.
  intros. induction H; simpl; omega.
Qed.

Lemma aenv_ext__same_length:
  forall GH GH',
    aenv_ext GH' GH ->
    length GH = length GH'.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. rewrite IHaenv_ext. reflexivity.
Qed.

Lemma indexr_at_ext :
  forall GH GH' x T G,
    aenv_ext GH' GH ->
    indexr x GH = Some (G, T) ->
    exists G', indexr x GH' = Some (G', T) /\ venv_ext G' G.
Proof.
  intros GH GH' x T G Hext Hindex. induction Hext.
  - simpl in Hindex. inversion Hindex.
  - simpl. simpl in Hindex.
    case_eq (beq_nat x (length A)); intros E.
    rewrite E in Hindex.  inversion Hindex. subst.
    rewrite <- (@aenv_ext__same_length A A'). rewrite E.
    exists G'. split. reflexivity. assumption. assumption.
    rewrite E in Hindex.
    rewrite <- (@aenv_ext__same_length A A'). rewrite E.
    apply IHHext. assumption. assumption.
Qed.

Lemma indexr_extend_venv : forall G G' x T,
                       indexr x G = Some T ->
                       venv_ext G' G ->
                       indexr x G' = Some T.
Proof.
  intros G G' x T H HV.
  induction HV.
  - assumption.
  - apply indexr_extend. apply IHHV. apply H.
Qed.

Lemma stp2_closure_extend_rec:
  forall G1 G2 T1 T2 GH m n,
    stp2 m G1 T1 G2 T2 GH n ->
    (forall G1' G2' GH',
       aenv_ext GH' GH ->
       venv_ext G1' G1 ->
       venv_ext G2' G2 ->
       stp2 m G1' T1 G2' T2 GH' n).
Proof.
  intros G1 G2 T1 T2 GH m n H.
  induction H; intros; eauto.
  - Case "top".
    eapply stp2_top.
    eapply closed_inc_mult; try eassumption; try omega.
    rewrite (@aenv_ext__same_length GH GH'). omega. assumption.
    apply venv_ext__ge_length. assumption.
  - Case "sel1".
    eapply stp2_sel1. eapply indexr_extend_venv. apply H.
    assumption. assumption.
    apply IHstp2. assumption. apply venv_ext_refl. assumption.
  - Case "sel2".
    eapply stp2_sel2. eapply indexr_extend_venv. apply H.
    assumption. assumption.
    apply IHstp2. assumption. assumption. apply venv_ext_refl.
  - Case "selx".
    eapply stp2_selx.
    eapply indexr_extend_venv. apply H. assumption.
    eapply indexr_extend_venv. apply H0. assumption.
  - Case "sela1".
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_sela1 with (GX:=GX') (TX:=TX).
    assumption.
    eapply closed_inc_mult; try eassumption; try omega.
    apply venv_ext__ge_length. assumption.
    apply IHstp2; assumption.
  - Case "selax".
    destruct v as [GX TX].
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_selax with (v:=(GX',TX)).
    assumption.
  - Case "all".
    eapply stp2_all with (x:=length GH').
    apply IHstp2_1; assumption.
    reflexivity.
    eapply closed_inc_mult; try eassumption; try omega.
    rewrite (@aenv_ext__same_length GH GH'). omega. assumption.
    apply venv_ext__ge_length. assumption.
    eapply closed_inc_mult; try eassumption; try omega.
    rewrite (@aenv_ext__same_length GH GH'). omega. assumption.
    apply venv_ext__ge_length. assumption.
    subst.  rewrite <- (@aenv_ext__same_length GH GH').
    apply IHstp2_2. apply aenv_ext_cons.
    assumption. assumption. assumption. assumption. assumption.
  - Case "trans".
    eapply stp2_transf.
    eapply IHstp2_1.
    assumption. assumption. apply venv_ext_refl.
    eapply IHstp2_2.
    assumption. apply venv_ext_refl. assumption.
Qed.

Lemma stp2_closure_extend : forall G1 T1 G2 T2 GH GX T v m n,
                              stp2 m G1 T1 G2 T2 ((GX,T)::GH) n ->
                              stp2 m G1 T1 G2 T2 ((v::GX,T)::GH) n.
Proof.
  intros. eapply stp2_closure_extend_rec. apply H.
  apply aenv_ext_cons. apply aenv_ext_refl. apply venv_ext_cons.
  apply venv_ext_refl. apply venv_ext_refl. apply venv_ext_refl.
Qed.

Lemma stp2_extend : forall v1 G1 G2 T1 T2 H m n,
                      stp2 m G1 T1 G2 T2 H n ->
                       stp2 m (v1::G1) T1 G2 T2 H n /\
                       stp2 m G1 T1 (v1::G2) T2 H n /\
                       stp2 m (v1::G1) T1 (v1::G2) T2 H n.
Proof.
  intros. induction H0;
    try solve [split; try split; intros; eauto using indexr_extend];
    try solve [split; try split; intros; constructor; simpl; eauto using indexr_extend, closed_upgrade_freef];
    try solve [split; try split; intros;
               inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]]; eauto];
    try solve [split; try split; intros; inversion IHstp2 as [? [? ?]]; eauto];
    try solve [split; try split; intros; inversion IHstp2 as [? [? ?]]; eauto using indexr_extend];
    try solve [split; try split; intros;
               inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]];
               eauto; eapply stp2_all; simpl; eauto using stp2_closure_extend, closed_upgrade_freef].
Qed.

Lemma stp2_extend2 : forall v1 G1 G2 T1 T2 H m n,
                       stp2 m G1 T1 G2 T2 H n ->
                       stp2 m G1 T1 (v1::G2) T2 H n.
Proof.
  intros. apply (proj2 (stp2_extend v1 G1 G2 T1 T2 H m n H0)).
Qed.

Lemma stp2_extend1 : forall v1 G1 G2 T1 T2 H m n,
                       stp2 m G1 T1 G2 T2 H n ->
                       stp2 m (v1::G1) T1 G2 T2 H n.
Proof.
  intros. apply (proj1 (stp2_extend v1 G1 G2 T1 T2 H m n H0)).
Qed.

Lemma stp2_extendH : forall v1 G1 G2 T1 T2 GH m n,
                       stp2 m G1 T1 G2 T2 GH n ->
                       stp2 m G1 T1 G2 T2 (v1::GH) n.
Proof.
  intros.
  induction H;
    try solve [try constructor; simpl; eauto using indexr_extend, closed_upgrade_free];
    try solve [eapply stp2_transf; simpl; eauto].
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. apply H1. omega.
  }
  assert (splice (length GH) T4 = T4) as A4. {
    eapply closed_splice_idem. apply H2. omega.
  }
  assert (TVarH (S (length GH)) = splice (length GH) (TVarH (length GH))) as AH. {
    simpl. case_eq (le_lt_dec (length GH) (length GH)); intros E LE.
    simpl. rewrite NPeano.Nat.add_1_r. reflexivity.
    clear LE. apply lt_irrefl in E. inversion E.
  }
  assert (closed 0 (length GH) (length G2) T3). eapply stp2_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (spliceat (length GH)) [(G2, T3)] ++ v1::GH =
          ((G2, T3)::v1::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  eapply stp2_all.
  apply IHstp2_1.
  reflexivity.
  apply closed_inc. apply H1.
  apply closed_inc. apply H2.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (TVarH (S (length GH))) with (TVarH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite -> splice_open_permute.
  rewrite <- HGX3.
  apply stp2_splice.
  subst x. simpl. unfold open in H3. apply H3.
Qed.

Lemma stp2_extendH_mult : forall G1 G2 T1 T2 H H2 m n,
                       stp2 m G1 T1 G2 T2 H n ->
                       stp2 m G1 T1 G2 T2 (H2++H) n.
Proof.
  intros. induction H2.
  - simpl. assumption.
  - simpl.
    apply stp2_extendH. assumption.
Qed.

Lemma stp2_extendH_mult0 : forall G1 G2 T1 T2 H2 m n,
                       stp2 m G1 T1 G2 T2 [] n ->
                       stp2 m G1 T1 G2 T2 H2 n.
Proof.
  intros.
  assert (H2 = H2++[]) as A by apply app_nil_end. rewrite A.
  apply stp2_extendH_mult. assumption.
Qed.

Lemma stp2_reg  : forall G1 G2 T1 T2 GH m n,
                    stp2 m G1 T1 G2 T2 GH n ->
                    stpd2 true G1 T1 G1 T1 GH /\ stpd2 true G2 T2 G2 T2 GH.
Proof.
  intros.
  apply stp2_closed in H. destruct H as [H1 H2].
  split; apply stp2_refl; assumption.
Qed.

Lemma stp2_reg2 : forall G1 G2 T1 T2 GH m n,
                       stp2 m G1 T1 G2 T2 GH n ->
                       stpd2 true G2 T2 G2 T2 GH.
Proof.
  intros. apply (proj2 (stp2_reg G1 G2 T1 T2 GH m n H)).
Qed.

Lemma stp2_reg1 : forall G1 G2 T1 T2 GH m n,
                       stp2 m G1 T1 G2 T2 GH n ->
                       stpd2 true G1 T1 G1 T1 GH.
Proof.
  intros. apply (proj1 (stp2_reg G1 G2 T1 T2 GH m n H)).
Qed.

Lemma stp_reg  : forall G GH T1 T2,
                    stp G GH T1 T2 ->
                    stp G GH T1 T1 /\ stp G GH T2 T2.
Proof.
  intros.
  apply stp_closed in H. destruct H as [H1 H2].
  split; apply stp_refl; assumption.
Qed.

Lemma stp_reg2 : forall G GH T1 T2,
                       stp G GH T1 T2 ->
                       stp G GH T2 T2.
Proof.
  intros. apply (proj2 (stp_reg G GH T1 T2 H)).
Qed.

Lemma stp_reg1 : forall G GH T1 T2,
                       stp G GH T1 T2 ->
                       stp G GH T1 T1.
Proof.
  intros. apply (proj1 (stp_reg G GH T1 T2 H)).
Qed.

Lemma stpd2_extend2 : forall v1 G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       stpd2 m G1 T1 (v1::G2) T2 H.
Proof.
  intros. destruct H0 as [n Hsub]. eexists n.
  apply stp2_extend2; eauto.
Qed.

Lemma stpd2_extend1 : forall v1 G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       stpd2 m (v1::G1) T1 G2 T2 H.
Proof.
  intros. destruct H0 as [n Hsub]. eexists n.
  apply stp2_extend1; eauto.
Qed.

Lemma stpd2_extendH : forall v1 G1 G2 T1 T2 GH m,
                       stpd2 m G1 T1 G2 T2 GH ->
                       stpd2 m G1 T1 G2 T2 (v1::GH).
Proof.
  intros. destruct H as [n Hsub]. exists n.
  apply stp2_extendH; eauto.
Qed.

Lemma stpd2_extendH_mult : forall G1 G2 T1 T2 GH GH2 m,
                       stpd2 m G1 T1 G2 T2 GH ->
                       stpd2 m G1 T1 G2 T2 (GH2++GH).
Proof.
  intros. destruct H as [n Hsub]. exists n.
  apply stp2_extendH_mult; eauto.
Qed.

Lemma stpd2_closed2 : forall G1 G2 T1 T2 GH m,
                       stpd2 m G1 T1 G2 T2 GH ->
                       closed 0 (length GH) (length G2) T2.
Proof.
  intros. destruct H as [n Hsub].
  eapply stp2_closed2; eauto.
Qed.

Lemma stpd2_closed1 : forall G1 G2 T1 T2 GH m,
                       stpd2 m G1 T1 G2 T2 GH ->
                       closed 0 (length GH) (length G1) T1.
Proof.
  intros. destruct H as [n Hsub].
  eapply stp2_closed1; eauto.
Qed.

Lemma valtp_extend : forall vs v v1 T,
                       val_type vs v T ->
                       val_type (v1::vs) v T.
Proof.
  intros. induction H; eauto; econstructor; eauto; eapply stpd2_extend2; eauto.
Qed.

Lemma indexr_safe_ex: forall H1 G1 TF i,
             wf_env H1 G1 ->
             indexr i G1 = Some TF ->
             exists v, indexr i H1 = Some v /\ val_type H1 v TF.
Proof. intros. induction H.
   - Case "nil". inversion H0.
   - Case "cons". inversion H0.
     case_eq (beq_nat i (length ts)); intros E2.
     * SSCase "hit".
       rewrite E2 in H3. inversion H3. subst. clear H3.
       assert (length ts = length vs). symmetry. eapply wf_length. eauto.
       simpl. rewrite H2 in E2. rewrite E2.
       eexists. split. eauto. assumption.
     * SSCase "miss".
       rewrite E2 in H3.
       assert (exists v0,
                 indexr i vs = Some v0 /\ val_type vs v0 TF). eauto.
       destruct H2. destruct H2.
       eexists. split. eapply indexr_extend. eauto.
       eapply valtp_extend. assumption.
Qed.

Lemma index_safeh_ex: forall H1 H2 G1 GH TF i,
             wf_env H1 G1 -> wf_envh H1 H2 GH ->
             indexr i GH = Some TF ->
             exists v, indexr i H2 = Some v /\ valh_type H1 H2 v TF.
Proof. intros. induction H0.
   - Case "nil". inversion H3.
   - Case "cons". inversion H3.
     case_eq (beq_nat i (length ts)); intros E2.
     * SSCase "hit".
       rewrite E2 in H2. inversion H2. subst. clear H2.
       assert (length ts = length vs). symmetry. eapply wfh_length. eauto.
       simpl. rewrite H1 in E2. rewrite E2.
       eexists. split. eauto. econstructor.
     * SSCase "miss".
       rewrite E2 in H2.
       assert (exists v : venv * ty,
                 indexr i vs = Some v /\ valh_type vvs vs v TF). eauto.
       destruct H1. destruct H1.
       eexists. split. eapply indexr_extend. eauto.
       inversion H4. subst.
       eapply v_tya. (* aenv is not constrained -- bit of a cheat?*)
Qed.

Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.

(* ### Transitivity ### *)

Definition trans_on Q := forall E F S T,
  stp E F S Q -> stp E F Q T -> stp E F S T.

Hint Unfold trans_on.

Lemma stp_narrow_aux : forall Q E F G P S T,
  trans_on Q ->
  stp E (G ++ [(TMem Q)] ++ F) S T ->
  stp E F P Q ->
  stp E (G ++ [(TMem P)] ++ F) S T.
Proof.
  intros Q E F G P S T TransQ SsubT PsubQ.
  dependent induction SsubT; intros; eauto.
  - apply stp_top.
    rewrite app_length. rewrite app_length. simpl.
    rewrite app_length in H. rewrite app_length in H. simpl in H.
    apply H.
  - case_eq (beq_nat x (length F)); intros E2.
    + eapply stp_sela1.
      eapply indexr_at_index. assumption.
      eapply beq_nat_true in E2. subst.
      eapply stp_closed1. eassumption.
      assert (indexr x (G ++ [TMem Q] ++ F) = Some (TMem Q)) as I. {
        simpl. apply indexr_at_index. assumption.
      }
      rewrite I in H. inversion H. subst.
      apply TransQ.
      apply stp_extend_mult. apply stp_extend_mult. assumption.
      eapply IHSsubT. eassumption. eauto. assumption.
    + eapply stp_sela1.
      eapply indexr_same. assumption. eassumption. assumption.
      eapply IHSsubT. eassumption. eauto. assumption.
  - case_eq (beq_nat x (length F)); intros E2.
    + eapply stp_selax.
      eapply indexr_at_index. assumption.
    + eapply stp_selax.
      eapply indexr_same. assumption. eassumption.
  - assert (length (G ++ [TMem P] ++ F) = length (G ++ [TMem Q] ++ F)) as A. {
      simpl. rewrite app_length. rewrite app_length. simpl.
      reflexivity.
    }
    eapply stp_all; eauto.
    rewrite A. assumption.
    rewrite A. assumption.
    rewrite A.
    change (TMem T3 :: G ++ [TMem P] ++ F) with ((TMem T3 :: G) ++ [TMem P] ++ F).
    eapply IHSsubT2; eauto.
Qed.

Lemma stp_trans_aux: forall n G GH T1 T2 T3,
  tsize T2 < n ->
  stp G GH T1 T2 ->
  stp G GH T2 T3 ->
  stp G GH T1 T3.
Proof.
  intros n G GH T1 T2 T3 A S12 S23.
  generalize dependent T3.
  generalize dependent T1.
  generalize dependent GH. generalize dependent G.
  generalize dependent T2.
  induction n; intros T2 LE G GH T1' S12;
  induction S12; try discriminate; try inversion LE; subst;
  intros T3' S23;
  remember S23 as S23'; clear HeqS23'; inversion S23; subst;
  eauto 4 using stp_closed1, stp_closed2.
  - (* TFun - TFun *)
    eapply stp_fun; eauto.
    apply (IHn T3). omega. assumption. assumption.
    apply (IHn T4). omega. assumption. assumption.
  - (* TAll - TAll *)
    eapply stp_all; eauto.
    apply (IHn T3). omega. assumption. assumption.
    apply (IHn (open (TVarH (length GH)) T4)).
    unfold open. rewrite <- open_preserves_size. omega.
    change (TMem T6 :: GH) with ([] ++ [(TMem T6)] ++ GH).
    apply stp_narrow_aux with (Q:=T3).
    unfold trans_on.
    intros. apply (IHn T3). omega. assumption. assumption.
    simpl. assumption. assumption. assumption.
Qed.

Lemma stp_trans: forall G GH T1 T2 T3,
  stp G GH T1 T2 ->
  stp G GH T2 T3 ->
  stp G GH T1 T3.
Proof.
  intros. eapply (stp_trans_aux (S (tsize T2))); eauto.
Qed.

Lemma stp_narrow: forall Q E F G P S T,
  stp E (G ++ [(TMem Q)] ++ F) S T ->
  stp E F P Q ->
  stp E (G ++ [(TMem P)] ++ F) S T.
Proof.
  intros.
  apply stp_narrow_aux with (Q:=Q); eauto.
  unfold trans_on. intros. apply stp_trans with (T2:=Q); eauto.
Qed.

Lemma stpd2_top: forall G1 G2 GH T,
    closed 0 (length GH) (length G1) T ->
    stpd2 true G1 T G2 TTop GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_fun: forall G1 G2 T1 T2 T3 T4 GH,
    stpd2 false G2 T3 G1 T1 GH ->
    stpd2 false G1 T2 G2 T4 GH ->
    stpd2 true G1 (TFun T1 T2) G2 (TFun T3 T4) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_mem: forall G1 G2 T1 T2 GH,
    stpd2 false G1 T1 G2 T2 GH ->
    stpd2 true G1 (TMem T1) G2 (TMem T2) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_sel1_down: forall G1 G2 GX TX x T2 GH,
    indexr x G1 = Some (vty GX TX) ->
    closed 0 0 (length GX) TX ->
    stpd2 true GX TX G2 T2 GH ->
    stpd2 true G1 (TVarF x) G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_sel2: forall G1 G2 GX TX x T1 GH,
    indexr x G2 = Some (vty GX TX) ->
    closed 0 0 (length GX) TX ->
    stpd2 false G1 T1 GX TX GH ->
    stpd2 true G1 T1 G2 (TVarF x) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_selx: forall G1 G2 v x1 x2 GH,
    indexr x1 G1 = Some v ->
    indexr x2 G2 = Some v ->
    stpd2 true G1 (TVarF x1) G2 (TVarF x2) GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_sela1: forall G1 G2 GX TX x T2 GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 x (length GX) TX ->
    stpd2 false GX TX G2 T2 GH ->
    stpd2 true G1 (TVarH x) G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_selax: forall G1 G2 v x GH,
    indexr x GH = Some v ->
    stpd2 true G1 (TVarH x) G2 (TVarH x) GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_all: forall G1 G2 T1 T2 T3 T4 x GH,
    stpd2 false G2 T3 G1 T1 GH ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G2) T4 ->
    stpd2 false G1 (open (TVarH x) T2) G2 (open (TVarH x) T4) ((G2, T3)::GH) ->
    stpd2 true G1 (TAll T1 T2) G2 (TAll T3 T4) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_wrapf: forall G1 G2 T1 T2 GH,
    stpd2 true G1 T1 G2 T2 GH ->
    stpd2 false G1 T1 G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_transf: forall G1 G2 G3 T1 T2 T3 GH,
    stpd2 true G1 T1 G2 T2 GH ->
    stpd2 false G2 T2 G3 T3 GH ->
    stpd2 false G1 T1 G3 T3 GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_trans_aux: forall n, forall G1 G2 G3 T1 T2 T3 H n1,
  stp2 false G1 T1 G2 T2 H n1 -> n1 < n ->
  stpd2 false G2 T2 G3 T3 H ->
  stpd2 false G1 T1 G3 T3 H.
Proof.
  intros n. induction n; intros; try omega; repeat eu; subst; inversion H0.
  - Case "wrapf". eapply stpd2_transf; eauto.
  - Case "transf". eapply stpd2_transf. eauto. eapply IHn. eauto. omega. eauto.
Qed.

Lemma stpd2_trans: forall G1 G2 G3 T1 T2 T3 H,
  stpd2 false G1 T1 G2 T2 H ->
  stpd2 false G2 T2 G3 T3 H ->
  stpd2 false G1 T1 G3 T3 H.
Proof. intros. repeat eu. eapply stpd2_trans_aux; eauto. Qed.

Lemma stp2_narrow_aux: forall n, forall m G1 T1 G2 T2 GH n0,
  stp2 m G1 T1 G2 T2 GH n0 ->
  n0 <= n ->
  forall GH1 GH0 GH' GX1 TX1 GX2 TX2,
    GH=GH1++[(GX2,TX2)]++GH0 ->
    GH'=GH1++[(GX1,TX1)]++GH0 ->
    stpd2 false GX1 TX1 GX2 TX2 GH0 ->
    stpd2 m G1 T1 G2 T2 GH'.
Proof.
  intros n.
  induction n.
  - Case "z". intros. inversion H0. subst. inversion H; eauto.
  - Case "s n". intros m G1 T1 G2 T2 GH n0 H NE. inversion H; subst;
    intros GH1 GH0 GH' GX1 TX1 GX2 TX2 EGH EGH' HX; eauto.
    + SCase "top". eapply stpd2_top.
      subst. rewrite app_length. simpl. rewrite app_length in H0. simpl in H0. apply H0.
    + SCase "fun". eapply stpd2_fun.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "mem". eapply stpd2_mem.
      eapply IHn; try eassumption. omega.
    + SCase "sel1". eapply stpd2_sel1_down; try eassumption.
      eapply IHn; try eassumption. omega.
    + SCase "sel2". eapply stpd2_sel2; try eassumption.
      eapply IHn; try eassumption. omega.
    + SCase "sela1".
      unfold id,venv,aenv in *.
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(GX2, TX2)]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        unfold venv in A2'. rewrite A2' in H0. inversion H0. subst.
        inversion HX as [nx HX'].
        eapply stpd2_sela1.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        apply beq_nat_true in E. rewrite E. eapply stp2_closed1. eassumption.
        eapply stpd2_trans.
        eexists. eapply stp2_extendH_mult. eapply stp2_extendH_mult. eassumption.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_sela1. eapply A. assumption.
        eapply IHn; try eassumption. omega.
    + SCase "selax".
      unfold id,venv,aenv in *.
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(GX2, TX2)]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        unfold venv in A2'. rewrite A2' in H0. inversion H0. subst.
        inversion HX as [nx HX'].
        eapply stpd2_selax.
        eapply indexr_extend_mult. simpl. unfold id,venv,aenv in *. rewrite E.
        reflexivity.
      * assert (indexr x GH' = Some v) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_selax. eapply A.
    + SCase "all".
      assert (length GH = length GH') as A. {
        subst. clear.
        induction GH1.
        - simpl. reflexivity.
        - simpl. simpl in IHGH1. rewrite IHGH1. reflexivity.
      }
      eapply stpd2_all.
      eapply IHn; try eassumption. omega.
      rewrite <- A. reflexivity.
      rewrite <- A. assumption. rewrite <- A. assumption.
      subst.
      eapply IHn with (GH1:=(G2, T4) :: GH1); try eassumption. omega.
      simpl. reflexivity. simpl. reflexivity.
    + SCase "wrapf".
      eapply stpd2_wrapf.
      eapply IHn; try eassumption. omega.
    + SCase "transf".
      eapply stpd2_transf.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
Grab Existential Variables. apply 0.
Qed.

Lemma stpd2_narrow: forall G1 G2 G3 G4 T1 T2 T3 T4 H,
  stpd2 false G1 T1 G2 T2 H -> (* careful about H! *)
  stpd2 false G3 T3 G4 T4 ((G2,T2)::H) ->
  stpd2 false G3 T3 G4 T4 ((G1,T1)::H).
Proof.
  intros. inversion H1 as [n H'].
  eapply (stp2_narrow_aux n) with (GH1:=[]) (GH0:=H). eapply H'. omega.
  simpl. reflexivity. reflexivity.
  assumption.
Qed.

Ltac indexr_contra :=
  match goal with
    | H: indexr ?N [] = Some ?V |- _ => simpl in H; inversion H
  end.

Lemma stpd2_untrans_aux: forall n, forall m G1 G2 G3 T1 T2 T3 GH n1,
  stp2 m G1 T1 G2 T2 GH n1 -> n1 < n ->
  stpd2 true G2 T2 G3 T3 GH ->
  stpd2 true G1 T1 G3 T3 GH.
Proof.
  intros n. induction n; intros; try omega. eu.
  inversion H; subst;
  try solve [inversion H1; eexists; eauto];
  try solve [eapply stpd2_sel1_down; eauto; eapply IHn; eauto; try omega];
  try solve [eapply stpd2_sela1; eauto; eapply stpd2_wrapf; eapply IHn; eauto; try omega];
  try solve [eapply IHn; [eapply H2 | omega | eauto]]; (* wrapf *)
  try solve [eapply IHn; [eapply H2 | omega | (eapply IHn; [ eapply H3 | omega | eauto ])]]; (* transf *)
  inversion H1; subst;
  try solve [eapply stpd2_top; eauto using stp2_closed1];
  try solve [eapply stpd2_sel2; eauto];
  try solve [eapply stpd2_fun; eapply stpd2_trans; eauto];
  try solve [eapply stpd2_mem; eauto; eapply stpd2_trans; eauto];
  try solve [eapply stpd2_sela1; eauto; eapply stpd2_wrapf; eapply IHn; eauto; try omega];
  try solve [indexr_contra].
  - Case "sel2 - sel1".
    rewrite H6 in H2. inversion H2. subst.
    eapply IHn. eapply H4. omega. eauto.
  - Case "sel2 - selx".
    rewrite H6 in H2. inversion H2. subst.
    eapply stpd2_sel2; eauto.
  - Case "selx - sel1".
    rewrite H5 in H3. inversion H3. subst.
    eapply stpd2_sel1_down; eauto.
  - Case "selx - selx".
    rewrite H5 in H3. inversion H3. subst.
    eapply stpd2_selx; eauto.
  - Case "selax - selax".
    eapply stpd2_selax; eauto.
  - Case "all - all".
    eapply stpd2_all; eauto.
    eapply stpd2_trans; eauto.
    eapply stpd2_trans. eapply stpd2_narrow. eexists. eapply H8. eauto. eauto.
Grab Existential Variables. apply 0.
Qed.

Lemma stpd2_upgrade_general: forall G1 G2 T1 T2 GH,
  stpd2 false G1 T1 G2 T2 GH ->
  stpd2 true G1 T1 G2 T2 GH.
Proof.
  intros. destruct H as [n H].
  eapply stpd2_untrans_aux; eauto using stp2_reg2.
Qed.

(* We need to fix stpd2_sel1 to weaken the non-trans hypothesis,
   that allowed the more convenient one-pass pushback proof. *)
Lemma stpd2_sel1: forall G1 G2 GX TX x T2 GH,
    indexr x G1 = Some (vty GX TX) ->
    closed 0 0 (length GX) TX ->
    stpd2 false GX TX G2 T2 GH ->
    stpd2 true G1 (TVarF x) G2 T2 GH.
Proof.
  intros. eapply stpd2_sel1_down; eauto using stpd2_upgrade_general.
Qed.

(* Otherwise, we don't generally need to push back transitivity
   in non-empty abstract contexts. *)
Lemma stpd2_untrans: forall G1 G2 G3 T1 T2 T3,
  stpd2 true G1 T1 G2 T2 [] ->
  stpd2 true G2 T2 G3 T3 [] ->
  stpd2 true G1 T1 G3 T3 [].
Proof. intros. repeat eu. eapply stpd2_untrans_aux; eauto. Qed.

Lemma stpd2_upgrade: forall G1 G2 T1 T2,
  stpd2 false G1 T1 G2 T2 [] ->
  stpd2 true G1 T1 G2 T2 [].
Proof.
  intros. destruct H as [n H].
  eapply stpd2_untrans_aux; eauto using stp2_reg2.
Qed.

(* ### Substitution for relating static and dynamic semantics ### *)
Lemma indexr_hit2 {X}: forall x (B:X) A G,
  length G = x ->
  B = A ->
  indexr x (B::G) = Some A.
Proof.
  intros.
  unfold indexr.
  assert (beq_nat x (length G) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1. subst. reflexivity.
Qed.

Lemma indexr_miss {X}: forall x (B:X) A G,
  indexr x (B::G) = A ->
  x <> (length G)  ->
  indexr x G = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = false). eapply beq_nat_false_iff. eauto.
  rewrite H1 in H. eauto.
Qed.

Lemma indexr_hit {X}: forall x (B:X) A G,
  indexr x (B::G) = Some A ->
  x = length G ->
  B = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1 in H. inversion H. eauto.
Qed.

Lemma indexr_hit0: forall GH (GX0:venv) (TX0:ty),
      indexr 0 (GH ++ [(GX0, TX0)]) =
      Some (GX0, TX0).
Proof.
  intros GH. induction GH.
  - intros. simpl. eauto.
  - intros. simpl. destruct a. simpl. rewrite app_length. simpl.
    assert (length GH + 1 = S (length GH)). omega. rewrite H.
    eauto.
Qed.

Hint Resolve beq_nat_true_iff.
Hint Resolve beq_nat_false_iff.

Lemma closed_no_open: forall T x i j k,
  closed i j k T ->
  T = open_rec i x T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed; rewrite <-IHclosed; auto];
  try solve [compute; compute in IHclosed1; compute in IHclosed2;
             rewrite <-IHclosed1; rewrite <-IHclosed2; auto].

  Case "TVarB".
    unfold open_rec. assert (i <> x0). omega.
    apply beq_nat_false_iff in H0.
    rewrite H0. auto.
Qed.

Lemma open_subst_commute: forall T2 TX j k x i,
closed i j k TX ->
(open_rec i (TVarH x) (subst TX T2)) =
(subst TX (open_rec i (TVarH (x+1)) T2)).
Proof.
  intros T2 TX j k. induction T2; intros; eauto.
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eapply closed_upgrade. eauto. eauto. eauto.
  -  simpl. case_eq (beq_nat i 0); intros E. symmetry. eapply closed_no_open. eauto. simpl. eauto.
  - simpl. case_eq (beq_nat i0 i); intros E. simpl.
    assert (x+1<>0). omega. eapply beq_nat_false_iff in H0.
    assert (x=x+1-1). unfold id. omega.
    rewrite H0. eauto.
    simpl. eauto.
  -  simpl. rewrite IHT2. eauto. eauto.
Qed.

Lemma closed_no_subst: forall T i k TX,
   closed i 0 k T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
  try rewrite (IHT i k TX); eauto; try rewrite (IHT2 (S i) k TX); eauto;
  try rewrite (IHT1 i k TX); eauto.

  eapply closed_upgrade. eauto. eauto.

  subst. omega.
Qed.

Lemma closed_subst: forall i j k TX T, closed i (j+1) k T -> closed 0 j k TX -> closed i j k (subst TX T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - Case "TVarH". simpl.
    case_eq (beq_nat i 0); intros E.
    eapply closed_upgrade. eapply closed_upgrade_free.
    eauto. omega. eauto. omega.
    econstructor. assert (i > 0). eapply beq_nat_false_iff in E. omega. omega.
Qed.

Lemma subst_open_commute_m: forall i j k j' TX T2, closed (i+1) (j+1) k T2 -> closed 0 j' k TX ->
    subst TX (open_rec i (TVarH (j+1)) T2) = open_rec i (TVarH j) (subst TX T2).
Proof.
  intros. generalize dependent i. generalize dependent j.
  induction T2; intros; inversion H; simpl; eauto;
          try rewrite IHT2_1; try rewrite IHT2_2; try rewrite IHT2; eauto.

  - Case "TVarH". simpl. case_eq (beq_nat i 0); intros E.
    eapply closed_no_open. eapply closed_upgrade. eauto. omega.
    eauto.
  - Case "TVarB". simpl. case_eq (beq_nat i0 i); intros E.
    simpl. case_eq (beq_nat (j+1) 0); intros E2.
    eapply beq_nat_true_iff in E2. omega.
    assert (j+1-1 = j). omega. eauto.
    eauto.
Qed.

Lemma subst_open_commute: forall i j k TX T2, closed (i+1) (j+1) k T2 -> closed 0 0 k TX ->
    subst TX (open_rec i (TVarH (j+1)) T2) = open_rec i (TVarH j) (subst TX T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_zero: forall i i' k TX T2, closed i' 0 k T2 ->
    subst TX (open_rec i (TVarH 0) T2) = open_rec i TX T2.
Proof.
  intros. generalize dependent i'. generalize dependent i.
  induction T2; intros; inversion H; simpl; eauto;
  try rewrite (IHT2_1 _ i');
  try rewrite (IHT2_2 _ (S i'));
  try rewrite (IHT2_2 _ (S i'));
  try rewrite (IHT2 _ i'); eauto.
  eapply closed_upgrade; eauto.
  case_eq (beq_nat i 0); intros E. omega. omega.
  case_eq (beq_nat i0 i); intros E. eauto. eauto.
Qed.

Lemma Forall2_length: forall A B f (G1:list A) (G2:list B),
                        Forall2 f G1 G2 -> length G1 = length G2.
Proof.
  intros. induction H.
  eauto.
  simpl. eauto.
Qed.

Lemma nosubst_intro: forall i k T, closed i 0 k T -> nosubst T.
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H; simpl; eauto.
  omega.
Qed.

Lemma nosubst_open: forall i TX T2, nosubst TX -> nosubst T2 -> nosubst (open_rec i TX T2).
Proof.
  intros. generalize dependent i. induction T2; intros;
  try inversion H0; simpl; eauto.
  case_eq (beq_nat i0 i); intros E. eauto. eauto.
Qed.

Lemma indexr_subst: forall GH0 x TX T,
   indexr x (GH0 ++ [(TMem TX)]) = Some T ->
   x = 0 /\ TMem TX = T \/
   x > 0 /\ indexr (x-1) (map (subst TX) GH0) = Some (subst TX T).
Proof.
  intros GH0. induction GH0; intros.
  - simpl in H. case_eq (beq_nat x 0); intros E.
    + rewrite E in H. inversion H.
      left. split. eapply beq_nat_true_iff. eauto. eauto.
    + rewrite E in H. inversion H.
  -  unfold id in H. remember ((length (GH0 ++ [(TMem TX)]))) as L.
     case_eq (beq_nat x L); intros E.
     + assert (x = L). eapply beq_nat_true_iff. eauto.
       eapply indexr_hit in H.
       right. split. rewrite app_length in HeqL. simpl in HeqL. omega.
       assert ((x - 1) = (length (map (subst TX) GH0))).
       rewrite map_length. rewrite app_length in HeqL. simpl in HeqL. unfold id. omega.
       simpl.
       eapply beq_nat_true_iff in H1. unfold id in H1. unfold id. rewrite H1.
       subst. eauto. eauto. subst. eauto.
     + assert (x <> L). eapply beq_nat_false_iff. eauto.
       eapply indexr_miss in H. eapply IHGH0 in H.
       inversion H. left. eapply H1.
       right. inversion H1. split. eauto.
       simpl.
       assert ((x - 1) <> (length (map (subst TX) GH0))).
       rewrite app_length in HeqL. simpl in HeqL. rewrite map_length.
       unfold not. intros. subst L. unfold id in H0. unfold id in H2.
       unfold not in H0. eapply H0. unfold id in H4. rewrite <-H4. omega.
       eapply beq_nat_false_iff in H4. unfold id in H4. unfold id. rewrite H4.
       eauto. subst. eauto.
Qed.


Lemma stp_substitute: forall T1 T2 GX GH,
   stp GX GH T1 T2 ->
   forall GH0 TX,
     GH = (GH0 ++ [(TMem TX)]) ->
     closed 0 0 (length GX) TX ->
     stp GX (map (subst TX) GH0) TX TX ->
     stp GX (map (subst TX) GH0)
         (subst TX T1)
         (subst TX T2).
Proof.
  intros T1 T2 GX GH H.
  induction H.
  - Case "top".
    intros. subst. simpl. rewrite app_length in H. simpl in H.
    apply stp_top. rewrite map_length.
    apply closed_subst. assumption.
    eapply closed_upgrade_free. eassumption. omega.
  - Case "fun". intros. simpl. eapply stp_fun. eauto. eauto.
  - Case "mem". intros. simpl. eapply stp_mem. eauto.
  - Case "sel1". intros. simpl. eapply stp_sel1. apply H. assumption.
    assert (subst TX T = T) as A. {
      eapply closed_no_subst. eassumption.
    }
    rewrite <- A.
    apply IHstp; eauto.
  - Case "selx". intros. simpl. eapply stp_selx. apply H.
  - Case "sela1". intros GH0 TX ? ? ?. simpl.
    subst GH. specialize (indexr_subst _ x TX (TMem T) H). intros.
    destruct H2; destruct H2.
    + inversion H5. subst. simpl.
      specialize (IHstp GH0 T).
      assert (subst T T = T). eapply closed_no_subst; eauto.
      rewrite H2 in IHstp.
      eapply IHstp. eauto. eauto. eauto.
    + subst. simpl.
      assert (beq_nat x 0 = false). eapply beq_nat_false_iff; omega. rewrite H6. simpl.
      eapply stp_sela1. simpl in H5. eapply H5.
      eapply closed_subst.
      assert (x - 1 + 1 = x) as A by omega.  rewrite A. assumption.
      eapply closed_upgrade_free. eassumption. omega.
      eauto.
  - Case "selax". intros GH0 TX ? ? ?. simpl.
    subst GH. specialize (indexr_subst _ x TX v H). intros.
    destruct H0; destruct H0.
    + subst. simpl. eauto.
    + subst. simpl. assert (beq_nat x 0 = false). eapply beq_nat_false_iff. omega. rewrite H4. eapply stp_selax. eauto.
  - Case "all".
    intros GH0 TX ? ? ?.
    simpl. eapply stp_all.
    + eapply IHstp1; eauto.
    + rewrite map_length. eauto.
    + rewrite map_length. eapply closed_subst. subst GH.
      rewrite app_length in H1. simpl in H1. eauto.
      eapply closed_upgrade_free; eauto. omega.
    + rewrite map_length. eapply closed_subst. subst GH.
      rewrite app_length in H2. simpl in H2. eauto.
      eapply closed_upgrade_free; eauto. omega.
    + specialize IHstp2 with (GH0:=(TMem T3)::GH0) (TX:=TX).
      subst GH. simpl in IHstp2.
      unfold open. unfold open in IHstp2.
      subst x.
      rewrite open_subst_commute with (j:=0) (k:=(length G1)).
      rewrite open_subst_commute with (j:=0) (k:=(length G1)).
      rewrite app_length in IHstp2. simpl in IHstp2.
      eapply IHstp2; eauto. eapply stp_extend; eauto.
      eauto. eauto.
Qed.

(*
when and how we can replace with multiple environments:

stp2 G1 T1 G2 T2 (GH0 ++ [(vty GX TX)])

1) T1 closed

   stp2 G1 T1 G2' T2' (subst GH0)

2) G1 contains (GX TX) at some index x1

   index x1 G1 = (GX TX)
   stp2 G (subst (TVarF x1) T1) G2' T2'

3) G1 = GX

   stp2 G1 (subst TX T1) G2' T2'

4) G1 and GX unrelated

   stp2 ((GX,TX) :: G1) (subst (TVarF (length G1)) T1) G2' T2'

*)

(* ---- two-env substitution. first define what 'compatible' types mean. ---- *)

Definition compat (GX:venv) (TX: ty) (G1:venv) (T1:ty) (T1':ty) :=
  (exists x1, indexr x1 G1 = Some (vty GX TX) /\ T1' = (subst (TVarF x1) T1)) \/
  (G1 = GX /\ T1' = (subst TX T1)) \/
  (closed 0 0 (length G1) T1 /\ T1' = T1) \/ (* this one is for convenience: redundant with next *)
  (nosubst T1 /\ T1' = subst TTop T1).


Definition compat2 (GX:venv) (TX: ty) (p1:(venv*ty)) (p2:(venv*ty)) :=
  match p1, p2 with
      (G1,T1), (G2,T2) => G1 = G2 /\ compat GX TX G1 T1 T2
  end.

Lemma closed_compat: forall GX TX GXX TXX TXX' i j,
  compat GX TX GXX TXX TXX' ->
  closed 0 j (length GXX) TX ->
  closed i (j+1) (length GXX) TXX ->
  closed i j (length GXX) TXX'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2. destruct H2. rewrite H3.
    eapply closed_subst. eauto.
    eapply cl_sel. apply indexr_max in H2. omega.
  - destruct H2. destruct H2. rewrite H3.
    eapply closed_subst. eauto. eauto.
  - destruct H2. rewrite H3.
    eapply closed_upgrade. eapply closed_upgrade_free. eauto. omega. omega.
  - destruct H2. rewrite H3.
    eapply closed_subst. eauto. eauto.
Qed.

Lemma indexr_compat_miss0: forall GH GH' GX TX (GXX:venv) (TXX:ty) n,
      Forall2 (compat2 GX TX) GH GH' ->
      indexr (n+1) (GH ++ [(GX, TX)]) = Some (GXX,TXX) ->
      exists TXX', indexr n GH' = Some (GXX,TXX') /\ compat GX TX GXX TXX TXX'.
Proof.
  intros. revert n H0. induction H.
  - intros. simpl. eauto. simpl in H0. assert (n+1 <> 0). omega.
    eapply beq_nat_false_iff in H. rewrite H in H0. inversion H0.
  - intros. simpl. destruct y.
    case_eq (beq_nat n (length l')); intros E.
    + simpl in H1. rewrite app_length in H1. simpl in H1.
      assert (n = length l'). eapply beq_nat_true_iff. eauto.
      assert (beq_nat (n+1) (length l + 1) = true). eapply beq_nat_true_iff.
      rewrite (Forall2_length _ _ _ _ _ H0). omega.
      rewrite H3 in H1. destruct x. inversion H1. subst. simpl in H.
      destruct H. subst. eexists. eauto.
    + simpl in H1. destruct x.
      assert (n <> length l'). eapply beq_nat_false_iff. eauto.
      assert (beq_nat (n+1) (length l + 1) = false). eapply beq_nat_false_iff.
      rewrite (Forall2_length _ _ _ _ _ H0). omega.
      rewrite app_length in H1. simpl in H1.
      rewrite H3 in H1.
      eapply IHForall2. eapply H1.
Qed.

Lemma compat_top: forall GX TX G1 T1',
  compat GX TX G1 TTop T1' -> closed 0 0 (length GX) TX -> T1' = TTop.
Proof.
  intros ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.

Lemma compat_mem: forall GX TX G1 T1 T1',
    compat GX TX G1 (TMem T1) T1' ->
    closed 0 0 (length GX) TX ->
    exists TA, T1' = TMem TA /\
                  compat GX TX G1 T1 TA.
Proof.
  intros ? ? ? ? ? CC CLX. destruct CC.

  simpl in H. destruct H. destruct H. repeat eexists. eauto. unfold compat. eauto.

  simpl in H. destruct H. destruct H. repeat eexists. eauto. unfold compat. eauto.

  simpl in H. destruct H. destruct H. inversion H. repeat eexists. eauto. unfold compat. eauto.

  simpl in H. destruct H. repeat eexists. eauto. unfold compat. eauto.
Qed.

Lemma compat_fun: forall GX TX G1 T1 T2 T1',
    compat GX TX G1 (TFun T1 T2) T1' ->
    closed 0 0 (length GX) TX ->
    exists TA TB, T1' = TFun TA TB /\
                  compat GX TX G1 T1 TA /\
                  compat GX TX G1 T2 TB.
Proof.
  intros ? ? ? ? ? ? CC CLX. destruct CC.

  simpl in H. destruct H. destruct H. repeat eexists. eauto.
  unfold compat. eauto. unfold compat. eauto.

  simpl in H. destruct H. destruct H. repeat eexists. eauto.
  unfold compat. eauto. unfold compat. eauto.

  simpl in H. destruct H. destruct H. inversion H. repeat eexists. eauto.
  unfold compat. eauto. unfold compat. eauto.

  simpl in H. destruct H. destruct H. repeat eexists. eauto.
  unfold compat. eauto. unfold compat. eauto.
Qed.

Lemma compat_sel: forall GX TX G1 T1' (GXX:venv) (TXX:ty) x,
    compat GX TX G1 (TVarF x) T1' ->
    closed 0 0 (length GX) TX ->
    closed 0 0 (length GXX) TXX ->
    indexr x G1 = Some (vty GXX TXX) ->
    exists TXX', T1' = (TVarF x) /\ compat GX TX GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? CC CL CL1 IX.

  destruct CC.
  destruct H. destruct H. simpl in H0. eexists. split. eauto. right. right. left. eauto.
  destruct H. destruct H. simpl in H0. eexists. split. eauto. right. right. left. eauto.
  destruct H. destruct H. simpl in H0. eexists. split. eauto. right. right. left. eauto.
  destruct H. destruct H. simpl in H0. eexists. split. eauto. right. right. left. eauto.
Qed.

Lemma compat_selh: forall GX TX G1 T1' GH0 GH0' (GXX:venv) (TXX:ty) x,
    compat GX TX G1 (TVarH x) T1' ->
    closed 0 0 (length GX) TX ->
    indexr x (GH0 ++ [(GX, TX)]) = Some (GXX, TXX) ->
    Forall2 (compat2 GX TX) GH0 GH0' ->
    (x = 0 /\ GXX = GX /\ TXX = TX) \/
    exists TXX',
      x > 0 /\ T1' = TVarH (x-1) /\
      indexr (x-1) GH0' = Some (GXX, TXX') /\
      compat GX TX GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? CC CL IX FA.

  case_eq (beq_nat x 0); intros E.
  - left. assert (x = 0). eapply beq_nat_true_iff. eauto. subst x.
    rewrite indexr_hit0 in IX. inversion IX. eauto.
  - right. assert (x <> 0). eapply beq_nat_false_iff. eauto.
    assert (x > 0). unfold id. unfold id in H. omega.
    eapply (indexr_compat_miss0) in FA. destruct FA.
    destruct CC.
    + simpl in H2. rewrite E in H2.
      destruct H2. destruct H2. eexists. eauto.
    + destruct H2. destruct H2. eexists. eauto. simpl in H3. rewrite E in H3.
      eauto.
      destruct H2. destruct H2. inversion H2. subst. omega.
      destruct H2. simpl in H3. rewrite E in H3. eauto.
    + assert (x-1+1=x). omega. rewrite H1. eauto.
Qed.

Lemma compat_all: forall GX TX G1 T1 T2 T1' n,
    compat GX TX G1 (TAll T1 T2) T1' ->
    closed 0 0 (length GX) TX -> closed 1 (n+1) (length G1) T2 ->
    exists TA TB, T1' = TAll TA TB /\
                  closed 1 n (length G1) TB /\
                  compat GX TX G1 T1 TA /\
                  compat GX TX G1 (open_rec 0 (TVarH (n+1)) T2) (open_rec 0 (TVarH n) TB).
Proof.
  intros ? ? ? ? ? ? ? CC CLX CL2. destruct CC.

  simpl in H. destruct H. destruct H. repeat eexists. eauto. eapply closed_subst. eauto.
    apply indexr_max in H. apply cl_sel. omega.

  unfold compat. eauto. unfold compat. left. exists x. split; eauto.
  erewrite subst_open_commute. eauto. eauto. apply indexr_max in H. eauto.

  destruct H. destruct H. simpl in H0. subst G1.
  repeat eexists. eauto. eapply closed_subst. eauto.
  eapply closed_upgrade_free. eauto. omega. unfold compat. eauto. unfold compat.
  right. left. erewrite subst_open_commute. eauto. eauto. eauto.

  destruct H. destruct H. inversion H. repeat eexists. eauto. subst.
  eapply closed_upgrade_free. eauto. omega. unfold compat. eauto.
  unfold compat. eauto. right. right.

  right. split. eapply nosubst_open. simpl. omega. eapply nosubst_intro. eauto. symmetry.
  assert (T2 = subst TTop T2). symmetry. eapply closed_no_subst. eauto.
  remember (open_rec 0 (TVarH n) T2) as XX. rewrite H8 in HeqXX. subst XX.
  eapply subst_open_commute. eauto. eauto.

  simpl in H. destruct H. destruct H. repeat eexists. eauto. eapply closed_subst. eauto. eauto.
  unfold compat. right. right. right. eauto.
  unfold compat. right. right. right. split. eapply nosubst_open. simpl. omega. eauto.
  erewrite subst_open_commute. eauto. eauto. eauto.
Qed.

Lemma compat_closed: forall GX TX G T T' j,
  compat GX TX G T T' ->
  closed 0 (j + 1) (length G) T ->
  closed 0 0 (length GX) TX ->
  closed 0 j (length G) T'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2 as [x1 [Hindex Heq]]. subst.
    apply closed_subst. eassumption.
    apply indexr_max in Hindex. apply cl_sel. omega.
  - destruct H2. subst.
    apply closed_subst. eassumption.
    eapply closed_upgrade_free. eassumption. omega.
  - destruct H2. subst.
    eapply closed_upgrade_free. eapply H2. omega.
  - destruct H2. subst.
    apply closed_subst. assumption. eauto.
Qed.

Lemma stp2_substitute_aux: forall n, forall G1 G2 T1 T2 GH m n1,
   stp2 m G1 T1 G2 T2 GH n1 ->
   n1 <= n ->
   forall GH0 GH0' GX TX T1' T2',
     GH = (GH0 ++ [(GX, TX)]) ->
     closed 0 0 (length GX) TX ->
     compat GX TX G1 T1 T1' ->
     compat GX TX G2 T2 T2' ->
     Forall2 (compat2 GX TX) GH0 GH0' ->
     stpd2 false G1 T1' G2 T2' GH0'.
Proof.
  intros n. induction n.
  Case "z". intros. inversion H0. subst. inversion H; eauto.
  intros G1 G2 T1 T2 GH m n1 H NE.
  induction H.
  - Case "top".
    intros GH0 GH0' GXX TXX T1' T2' ? CX IX1 IX2 FA; eapply stpd2_wrapf.
    eapply compat_top in IX2.
    subst. eapply stpd2_top.
    eapply compat_closed. eassumption.
    rewrite app_length in H. simpl in H.
    erewrite <- Forall2_length. eapply H. eassumption.
    eassumption. assumption.

  - Case "fun".
    intros GH0 GH0' GXX TXX T1' T2' ? CX IX1 IX2 FA; eapply stpd2_wrapf.
    eapply compat_fun in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_fun in IX2. repeat destruct IX2 as [? IX2].
    subst. eapply stpd2_fun.
    eapply IHn; eauto; try omega. eapply IHn; eauto; try omega.
    eauto. eauto.

  - Case "mem".
    intros GH0 GH0' GXX TXX T1' T2' ? CX IX1 IX2 FA; eapply stpd2_wrapf.
    eapply compat_mem in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_mem in IX2. repeat destruct IX2 as [? IX2].
    subst. eapply stpd2_mem.
    eapply IHn; eauto; try omega.
    eauto. eauto.

  - Case "sel1".
    intros GH0 GH0' GXX TXX T1' T2' ? CX IX1 IX2 FA; eapply stpd2_wrapf.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX G1 T1' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    assert (compat GXX TXX GX TX TX) as CPX. right. right. left. eauto.

    subst.
    eapply stpd2_sel1; eauto.
    eapply IHn; eauto; try omega.
    eauto. eauto. eauto.

  - Case "sel2".
    intros GH0 GH0' GXX TXX T1' T2' ? CX IX1 IX2 FA; eapply stpd2_wrapf.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX G2 T2' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    assert (compat GXX TXX GX TX TX) as CPX. right. right. left. eauto.

    subst.
    eapply stpd2_sel2; eauto.
    eapply IHn; eauto; try omega.
    eauto. eauto. eauto.

  - Case "selx".
    intros GH0 GH0' GXX TXX T1' T2' ? CX IX1 IX2 FA; eapply stpd2_wrapf.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (T1' = TVarF x1). {
      destruct IX1. ev. eauto.
      destruct H3. ev. auto.
      destruct H3. ev. eauto.
      destruct H3. eauto.
    }
    assert (T2' = TVarF x2). {
      destruct IX2. ev. eauto.
      destruct H4. ev. auto.
      destruct H4. ev. eauto.
      destruct H4. ev. eauto.
    }
    subst.
    eapply stpd2_selx. eauto. eauto.

  - Case "sela1".
    intros GH0 GH0' GXX TXX T1' T2' ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX G1 (TVarH x) T1') as IXX. eauto.

    eapply (compat_selh GXX TXX G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    destruct IX1.
    + SCase "x = 0".
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl.
        eapply stpd2_wrapf. eapply stpd2_sel1. eauto. eauto.
        eapply IHn; eauto; try omega. right. right. left. auto.
      * subst. simpl.
        eapply IHn; eauto; try omega. right. right. left. auto.
      * subst. inversion H5. subst. omega.
      * subst. destruct H5. eauto.
    + SCase "x > 0".
      ev. subst.
      eapply stpd2_wrapf. eapply stpd2_sela1. eauto.

      assert (x-1+1=x) as A by omega.
      remember (x-1) as x1. rewrite <- A in H0.
      eapply compat_closed. eauto. eauto. eauto.
      eapply IHn; eauto; try omega.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.

  - Case "selax".
    intros GH0 GH0' GXX TXX T1' T2' ? CX IX1 IX2 FA; eapply stpd2_wrapf.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX G1 (TVarH x) T1') as IXX1. eauto.
    assert (compat GXX TXX G2 (TVarH x) T2') as IXX2. eauto.

    destruct v as [GX TX].
    eapply (compat_selh GXX TXX G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].
    eapply (compat_selh GXX TXX G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    destruct IX1; destruct IX2.
    + destruct H3. destruct H4. subst. (* x = 0 *)

      inversion IXX1; inversion IXX2.

      destruct H0. destruct H0. subst. simpl.
      destruct H3. destruct H3. subst. simpl.
      eapply stpd2_sel1. eauto. eauto.
      eapply stpd2_wrapf. eapply stpd2_sel2. eauto. eauto.
      eapply stpd2_wrapf.
      eapply stp2_refl. eapply closed_upgrade_free. eassumption. omega.

      destruct H0. destruct H0. subst. simpl.
      destruct H3. destruct H3. subst. simpl.
      eapply stpd2_sel1. eauto. eauto.
      eapply stpd2_wrapf.
      eapply stp2_refl. eapply closed_upgrade_free. eassumption. omega.

      destruct H3. destruct H3. subst. simpl.
      inversion H3. omega. (* contra *)

      destruct H3. destruct H3. eauto. (* contra *)

      (* --- *)

      destruct H0. destruct H0. subst. simpl.
      destruct H3. destruct H0. subst. simpl.
      eapply stpd2_sel2. eauto. eauto.
      eapply stpd2_wrapf.
      eapply stp2_refl. eapply closed_upgrade_free. eassumption. omega.

      destruct H0. destruct H0. inversion H0. omega. (* contra *)

      destruct H0. destruct H0. eauto. (* contra *)

      (* --- *)

      destruct H0. destruct H0. subst. simpl.
      destruct H3. destruct H0. subst. simpl.
      eapply stp2_refl. eapply closed_upgrade_free. eassumption. omega.

      destruct H0. destruct H0. inversion H0. omega.
      destruct H0. destruct H0. eauto.
      destruct H0. destruct H0. inversion H0. omega.
      destruct H0. destruct H0. eauto.

    + destruct H3. destruct H3. omega.
    + destruct H2. destruct H3. omega.
    + destruct H2. destruct H2. destruct H4. destruct H5.
      destruct H3. destruct H3. destruct H7. destruct H8.
      subst. eapply stpd2_selax. eauto.

    + eauto.
    + subst GH. eauto.
    + eauto.
    + eauto.
    + eauto. subst GH. eauto.
    + eauto.

  - Case "all".
    intros GH0 GH0' GX TX T1' T2' ? CX IX1 IX2 FA; eapply stpd2_wrapf.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply compat_all in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_all in IX2. repeat destruct IX2 as [? IX2].

    subst.

    eapply stpd2_all.
    + eapply IHn; eauto; try omega.
    + eauto.
    + eauto.
    + eauto.
    + subst.
      eapply IHn. eauto. omega. simpl.
      change ((G2, T3) :: GH0 ++ [(GX, TX)]) with (((G2, T3) :: GH0) ++ [(GX, TX)]).
      reflexivity.
      eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
  - Case "wrapf".
    intros. subst. eapply IHn; eauto; try omega.
  - Case "transf".
    intros. subst.
    apply stp2_extend2 with (v1:=(vty GX TX)) in H.
    apply stp2_extend1 with (v1:=(vty GX TX)) in H0.
    eapply stpd2_trans.

    eapply IHn; eauto; try omega.
    unfold compat. simpl. left. exists (length G2).
    rewrite <- beq_nat_refl. split; eauto.

    eapply IHn; eauto; try omega.
    unfold compat. simpl. left. exists (length G2).
    rewrite <- beq_nat_refl. split; eauto.
Qed.

Lemma stp2_substitute: forall G1 G2 T1 T2 GH m,
   stpd2 m G1 T1 G2 T2 GH ->
   forall GH0 GH0' GX TX T1' T2',
     GH = (GH0 ++ [(GX, TX)]) ->
     closed 0 0 (length GX) TX ->
     compat GX TX G1 T1 T1' ->
     compat GX TX G2 T2 T2' ->
     Forall2 (compat2 GX TX) GH0 GH0' ->
     stpd2 false G1 T1' G2 T2' GH0'.
Proof.
  intros. repeat eu. eapply stp2_substitute_aux; eauto.
Qed.

(* ### Relating Static and Dynamic Subtyping ### *)
Lemma stp_to_stp2: forall G1 GH T1 T2,
  stp G1 GH T1 T2 ->
  forall GX GY, wf_env GX G1 -> wf_envh GX GY GH ->
  stpd2 false GX T1 GX T2 GY.
Proof.
  intros G1 G2 T1 T2 ST. induction ST; intros GX GY WX WY; eapply stpd2_wrapf.
  - Case "top".
    eapply stpd2_top. erewrite wfh_length; eauto. erewrite wf_length; eauto.
  - Case "fun". eapply stpd2_fun; eauto.
  - Case "mem". eapply stpd2_mem; eauto.
  - Case "sel1".
    assert (exists v : vl, indexr x GX = Some v /\ val_type GX v (TMem T)) as A.
    eapply indexr_safe_ex. eauto. eauto.
    destruct A as [? [? VT]].
    inversion VT; subst.
    destruct H3 as [? H3]. inversion H3. subst.
    eapply stp2_extendH_mult with (H2:=GY) in H7. rewrite app_nil_r in H7.
    eapply stpd2_sel1; eauto. inversion H2. subst.
    eapply stp2_closed1 in H3. eauto. inversion H3. subst. simpl in H9. apply H9.
    eapply stp2_closed1 in H3. eauto. inversion H3. subst. simpl in H13. apply H13.
    eapply stpd2_trans. eexists. apply H7. eapply IHST; eauto.
    destruct H5 as [? H5]. inversion H5.
    destruct H5 as [? H5]. inversion H5.
  - Case "selx". eauto.
    assert (exists v0 : vl, indexr x GX = Some v0 /\ val_type GX v0 v) as A.
    eapply indexr_safe_ex. eauto. eauto. eauto.
    destruct A as [? [? ?]].
    eapply stpd2_selx; eauto.
  - Case "sela1". eauto.
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v (TMem T)) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    inversion VT. subst.
    eapply stpd2_sela1. eauto.
    erewrite wf_length; eauto.
    eapply IHST. eauto. eauto.
  - Case "selax". eauto.
    assert (exists v0, indexr x GY = Some v0 /\ valh_type GX GY v0 v) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    destruct VT. subst.
    eapply stpd2_selax. eauto.
  - Case "all".
    subst x.
    assert (length GY = length GH) as A. eapply wfh_length; eauto.
    assert (length GX = length G1) as B. eapply wf_length; eauto.
    eapply stpd2_all. eauto. eauto.
    rewrite A. rewrite B. eauto.
    rewrite A. rewrite B. eauto.
    rewrite A.
    eapply IHST2. eauto. eapply wfeh_cons. eauto.
Qed.

Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stpd2 true H1 T1 H2 T2 [] ->
  val_type H2 vf T2.
Proof.
  intros. inversion H; econstructor; eauto; eapply stpd2_untrans; eauto.
Qed.

Lemma restp_widen: forall vf H1 H2 T1 T2,
  res_type H1 vf T1 ->
  stpd2 true H1 T1 H2 T2 [] ->
  res_type H2 vf T2.
Proof.
  intros. inversion H. eapply not_stuck. eapply valtp_widen; eauto.
Qed.


(* ### Inversion Lemmas ### *)

Lemma invert_abs: forall venv vf T1 T2,
  val_type venv vf (TFun T1 T2) ->
  exists env tenv x y T3 T4,
    vf = (vabs env T3 y) /\
    length env = x /\
    wf_env env tenv /\
    has_type (T3::tenv) y T4 /\
    stpd2 true venv T1 env T3 [] /\
    stpd2 true env T4 venv T2 [].
Proof.
  intros. inversion H; repeat ev; try solve by inversion.
  inversion H3. subst.
  assert (stpd2 false venv0 T1 venv1 T0 []) as E1. eauto.
  assert (stpd2 false venv1 T3 venv0 T2 []) as E2. eauto.
  eapply stpd2_upgrade in E1. eapply stpd2_upgrade in E2.
  repeat eu. repeat eexists; eauto.
Qed.

Lemma invert_tabs: forall venv vf T1 T2,
  val_type venv vf (TAll T1 T2) ->
  exists env tenv x y T3 T4,
    vf = (vtabs env T3 y) /\
    length env = x /\
    wf_env env tenv /\
    has_type ((TMem T3)::tenv) y (open (TVarF x) T4) /\
    stpd2 true venv T1 env T3 [] /\
    stpd2 true ((vty venv T1)::env) (open (TVarF x) T4) venv (open T1 T2) [].
Proof.
  intros. inversion H; ev; try solve by inversion. inversion H3. subst.
  eexists. eexists. eexists. eexists. eexists. eexists.
  repeat split; eauto; remember (length venv1) as x.

  eapply stpd2_upgrade; eauto.
  (* inversion of TAll < TAll *)
  assert (stpd2 true venv0 T1 venv1 T0 []). eapply stpd2_upgrade; eauto.
  assert (stpd2 false venv1 (open (TVarH 0) T3) venv0 (open (TVarH 0) T2) [(venv0, T1)]). {
    eauto.
  }

  (* need reflexivity *)
  assert (stpd2 true venv0 T1 venv0 T1 []). eapply stp2_reg1. eauto.
  assert (closed 0 0 (length venv0) T1). eapply stpd2_closed1 in H5. simpl in H5. eauto.

  (* now rename *)

  assert (stpd2 false ((vty venv0 T1) :: venv1) (open_rec 0 (TVarF x) T3) venv0 (open T1 T2) []). {
    eapply stp2_substitute with (GH0:=nil).
    eapply stpd2_extend1. eapply H4. simpl. eauto.
    simpl. eauto.
    eauto.
    left. eexists. split. eapply indexr_hit2. eauto. eauto. eauto. unfold open.
    erewrite (subst_open_zero 0 1). subst x.
    assert ((length venv1) + 0=length venv1) as R by omega. rewrite R. eauto. eauto.
    right. left. split. eauto. unfold open. erewrite (subst_open_zero 0 1). eauto. eauto.
    eauto.
  }

  (* done *)
  subst.
  eapply stpd2_upgrade; eauto.
Qed.

(* ### Type Safety ### *)
(* If term type-checks and the term evaluates without timing-out,
   the result is not stuck, but a value.
*)
Theorem full_safety : forall n e tenv venv res T,
  teval n venv e = Some res -> has_type tenv e T -> wf_env venv tenv ->
  res_type venv res T.

Proof.
  intros n. induction n.
  (* 0 *)   intros. inversion H.
  (* S n *) intros. destruct e; inversion H.

  - Case "Var".
    remember (tvar i) as e. induction H0; inversion Heqe; subst.
    + destruct (indexr_safe_ex venv0 env T1 i) as [v [I V]]; eauto.
      rewrite I. eapply not_stuck. eapply V.

    + eapply restp_widen. eapply IHhas_type; eauto.
      eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.

  - Case "Abs".
    remember (tabs t e) as xe. induction H0; inversion Heqxe; subst.
    + eapply not_stuck. eapply v_abs; eauto.
      eauto. eapply stpd2_upgrade. eapply stp_to_stp2. eauto. eauto. econstructor.
    + eapply restp_widen. eapply IHhas_type; eauto.
      eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.

  - Case "App".
    remember (tapp e1 e2) as e. induction H0; inversion Heqe; subst.
    +
      remember (teval n venv0 e1) as tf.
      remember (teval n venv0 e2) as tx.


      destruct tx as [rx|]; try solve by inversion.
      assert (res_type venv0 rx T1) as HRX. SCase "HRX". subst. eapply IHn; eauto.
      inversion HRX as [? vx].

      destruct tf as [rf|]; subst rx; try solve by inversion.
      assert (res_type venv0 rf (TFun T1 T2)) as HRF. SCase "HRF". subst. eapply IHn; eauto.
      inversion HRF as [? vf].

      destruct (invert_abs venv0 vf T1 T2) as
          [env1 [tenv [x0 [y0 [T3 [T4 [EF [FRX [WF [HTY [STX STY]]]]]]]]]]]. eauto.
      (* now we know it's a closure, and we have has_type evidence *)

      assert (res_type (vx::env1) res T4) as HRY.
        SCase "HRY".
          subst. eapply IHn. eauto. eauto.
          (* wf_env x *) econstructor. eapply valtp_widen; eauto.
                         eapply stpd2_extend2. eauto. eauto. eauto.

      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto. eapply stpd2_extend1. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto.
      eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.

  - Case "TAbs".
    remember (ttabs t e) as xe. induction H0; inversion Heqxe; subst.
    + eapply not_stuck. eapply v_tabs; eauto.
      eauto. eapply stpd2_upgrade. eapply stp_to_stp2. eauto. eauto. econstructor.
    + eapply restp_widen. eapply IHhas_type; eauto.
      eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.

  - Case "TApp".
    remember (ttapp e t) as xe. induction H0; inversion Heqxe; subst.
    +
      remember t as T11.
      remember (teval n venv0 e) as tf.

      destruct tf as [rf|]; try solve by inversion.
      assert (res_type venv0 rf (TAll T11 T12)) as HRF. SCase "HRF". subst. eapply IHn; eauto.
      inversion HRF as [? vf].

      subst t.
      destruct (invert_tabs venv0 vf T11 T12) as
          [env1 [tenv [x0 [y0 [T3 [T4 [EF [FRX [WF [HTY [STX STY]]]]]]]]]]]. eauto.
      (* now we know it's a closure, and we have has_type evidence *)

      assert (res_type ((vty venv0 T11)::env1) res (open (TVarF x0) T4)) as HRY.
        SCase "HRY".
          subst. eapply IHn. eauto. eauto.
          (* wf_env x *) econstructor. eapply v_ty.
          (* wf_env   *) eauto.
          eapply stpd2_extend2. eapply stpd2_mem.
          eapply stpd2_wrapf. eauto. eauto.
      eauto.
      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto.

    + eapply restp_widen. eapply IHhas_type; eauto.
      eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.

Qed.
