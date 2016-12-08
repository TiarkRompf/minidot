(* Termination for D<> *)
(* this version includes a proof of totality (like in nano0-total.v *)

(* copied from nano4-total.v *)
(* add TMem and TSel, complicated val_type0 wf definition *)
(* copied from nano4-total1-wip.v / dsubsup.v *)
(* scale up to full D<> *)

(* some proofs are commented out with a label PERF:
   this is just to make Coq go faster through the file *)

(*
TODO: 
 - extend and subst lemmas
 - lower bounds (Sel2 rules)
 - allow arbitrary expressions in paths
*)


(*
 DSub (D<:) + Bot
 T ::= Top | Bot | x.Type | { Type: S..U } | (z: T) -> T^z
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
| TBot : ty
(* (z: T) -> T^z *)
| TAll : ty -> ty -> ty
(* x.Type *)
| TSel : var -> ty
(* { Type: S..U } *)
| TMem : ty(*S*) -> ty(*U*) -> ty
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
| cl_sel: forall i j k x,
    k > x ->
    closed i j k (TSel (varF x))
| cl_selh: forall i j k x,
    j > x ->
    closed i j k (TSel (varH x))
| cl_selb: forall i j k x,
    i > x ->
    closed i j k (TSel (varB x))
| cl_mem: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TMem T1 T2)
.

(* open define a locally-nameless encoding wrt to TVarB type variables. *)
(* substitute var u for all occurrences of (varB k) *)
Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TSel (varF x) => TSel (varF x)
    | TSel (varH i) => TSel (varH i)
    | TSel (varB i) => if beq_nat k i then TSel u else TSel (varB i)
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

(* Locally-nameless encoding with respect to varH variables. *)
Fixpoint subst (U : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TSel (varB i) => TSel (varB i)
    | TSel (varF i) => TSel (varF i)
    | TSel (varH i) => if beq_nat i 0 then TSel U else TSel (varH (i-1))
    | TMem T1 T2     => TMem (subst U T1) (subst U T2)
  end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TBot         => True
    | TAll T1 T2   => nosubst T1 /\ nosubst T2
    | TSel (varB i) => True
    | TSel (varF i) => True
    | TSel (varH i) => i <> 0
    | TMem T1 T2    => nosubst T1 /\ nosubst T2
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
| stp_bot: forall G1 GH T2,
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH TBot T2
| stp_mem: forall G1 GH S1 U1 S2 U2,
    stp G1 GH U1 U2 ->
    stp G1 GH S2 S1 ->
    stp G1 GH (TMem S1 U1) (TMem S2 U2)
| stp_sel1: forall G1 GH TX T2 x,
    indexr x G1 = Some TX ->
    closed 0 0 (length G1) TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH (TSel (varF x)) T2
| stp_sel2: forall G1 GH TX T1 x,
    indexr x G1 = Some TX ->
    closed 0 0 (length G1) TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 (TSel (varF x)) 
| stp_selx: forall G1 GH v x,
    indexr x G1 = Some v ->
    stp G1 GH (TSel (varF x)) (TSel (varF x))
| stp_sela1: forall G1 GH TX T2 x,
    indexr x GH = Some TX ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH (TSel (varH x)) T2
| stp_sela2: forall G1 GH TX T1 x,
    indexr x GH = Some TX ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 (TSel (varH x)) 
| stp_selax: forall G1 GH v x,
    indexr x GH = Some v  ->
    stp G1 GH (TSel (varH x)) (TSel (varH x))
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
.

(* ### Type Assignment ### *)
Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           stp env [] T1 T1 ->
           has_type env (tvar x) T1
| t_typ: forall env T1,
           closed 0 0 (length env) T1 ->
           has_type env (ttyp T1) (TMem T1 T1)
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
        | tvar x       => Some (indexr x env)
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
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* ------------------------- NOTES -------------------------
Define value typing (val_type)
val_type0 cannot straightforwardly be defined as inductive
family, because the (forall vx, val_type0 env vx T1 -> ... )
occurrence violates the positivity restriction.
--------------------------------------------------------- *)


Fixpoint tsize_flat(T: ty) :=
  match T with
    | TTop => 1
    | TBot => 1
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSel _ => 1
    | TMem T1 T2 => S (tsize_flat T1 + tsize_flat T2)
  end.

Lemma open_preserves_size: forall T x j,
  tsize_flat T = tsize_flat (open_rec j (varH x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  - destruct v; simpl; destruct (beq_nat j i); eauto.
Qed.


Inductive sel: Type :=
| tp : sel
| ub : sel -> sel
| lb : sel -> sel
.

Definition vset := vl -> sel -> Prop.

Fixpoint pos s := match s with
                    | tp => true
                    | ub i => pos i
                    | lb i => if (pos i) then false else true
                  end.

Fixpoint ub_ins s := match s with
                    | tp => ub tp
                    | ub i => ub (ub_ins i)
                    | lb i => lb (ub_ins i)
                  end.


Require Coq.Program.Wf.

Program Fixpoint val_type (env:list vset) (GH:list vset) (v:vl) (T:ty) (i:sel) {measure (tsize_flat T)}: Prop :=
  match v,T,i with
    | vabs env1 T0 y, TAll T1 T2, tp =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall vx (jj:vset),
        (* val_type env GH vx T1 tp -> *) jj vx tp ->
        (forall vy iy, if pos iy then jj vy iy -> val_type env GH vy T1 iy
                       else           val_type env GH vy T1 iy -> jj vy iy) ->
        (forall vy iy, if pos iy then jj vy (lb iy) -> jj vy (ub iy) 
                       else           jj vy (ub iy) -> jj vy (lb iy)) ->
        exists v, tevaln (vx::env1) y v /\ val_type env (jj::GH) v (open (varH (length GH)) T2) tp
    | vty env1 TX, TMem T1 T2, tp =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2
      /\ forall vy iy, if (pos iy)
                  then val_type env GH vy T1 iy -> val_type env GH vy T2 iy
                  else val_type env GH vy T2 iy -> val_type env GH vy T1 iy
    | _, TMem T1 T2, ub i =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2
      /\ val_type env GH v T2 i
    | _, TMem T1 T2, lb i =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2
      /\ val_type env GH v T1 i
    | _, TSel (varF x), _ =>
      match indexr x env with
        | Some jj => jj v (ub i)
        | _ => False
      end
    | _, TSel (varH x), _ =>
      match indexr x GH with
        | Some jj => jj v (ub i)
        | _ => False
      end
    | _, TTop, _ => True
(*      pos i = true
    | _, TAll _ _, _ =>
      pos i = true /\ i <> tp
    | _, TBot, _ =>
      pos i = false *)
    | _,_,_ =>
      False
  end.

Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed. 
Next Obligation. simpl. unfold open. rewrite <-open_preserves_size. omega. Qed. (* TApp case: open *)
Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed.

Next Obligation. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; destruct H0; inversion H0; inversion H1. Qed.

(* 
   The expansion of val_type, val_type_func is incomprehensible. 
   We cannot (easily) unfold and reason about it. Therefore, we prove unfolding of
   val_type to its body as a lemma.
   (Note that the unfold_sub tactic relies on 
   functional extensionality)
*)

Import Coq.Program.Wf.
Import WfExtensionality.

Lemma val_type_unfold: forall env GH v T i, val_type env GH v T i =
  match v,T,i with
    | vabs env1 T0 y, TAll T1 T2, tp =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall vx (jj:vset),
        (* val_type env GH vx T1 tp -> *) jj vx tp ->
        (forall vy iy, if pos iy then jj vy iy -> val_type env GH vy T1 iy
                       else           val_type env GH vy T1 iy -> jj vy iy) ->
        (forall vy iy, if pos iy then jj vy (lb iy) -> jj vy (ub iy) 
                       else           jj vy (ub iy) -> jj vy (lb iy)) ->
        exists v, tevaln (vx::env1) y v /\ val_type env (jj::GH) v (open (varH (length GH)) T2) tp
    | vty env1 TX, TMem T1 T2, tp =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2
      /\ forall vy iy, if (pos iy)
                  then val_type env GH vy T1 iy -> val_type env GH vy T2 iy
                  else val_type env GH vy T2 iy -> val_type env GH vy T1 iy
    | _, TMem T1 T2, ub i =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2
      /\ val_type env GH v T2 i
    | _, TMem T1 T2, lb i =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2
      /\ val_type env GH v T1 i
    | _, TSel (varF x), _ =>
      match indexr x env with
        | Some jj => jj v (ub i)
                    (* /\
                    (forall vy iy, if (pos iy) then jj vy (ub (lb iy)) -> jj vy (ub (ub iy))
                                                else jj vy (ub (ub iy)) -> jj vy (ub (lb iy)))*)
        | _ => False
      end
    | _, TSel (varH x), _ =>
      match indexr x GH with
        | Some jj => jj v (ub i)
        | _ => False
      end
    | _, TTop, _ => True
(*      pos i = true
    | _, TAll _ _, _ =>
      pos i = true /\ i <> tp
    | _, TBot, _ =>
      pos i = false *)
    | _,_,_ =>
      False
  end.
Proof. admit. (* need further check 
  intros. unfold val_type at 1. unfold val_type_func.
  unfold_sub val_type (val_type env GH v T i).
  simpl.
  destruct v; simpl; try reflexivity.
  destruct T.
  - destruct i; simpl; try reflexivity.
  - simpl; try reflexivity.
  - destruct i; destruct T1; simpl; reflexivity. 
  - destruct v; simpl; try reflexivity.

  (* TSel case has another match *)
  destruct (indexr i0 env); simpl; try reflexivity;
  destruct v; simpl; try reflexivity.
  (* TSelH *) 
  destruct (indexr i0 GH); simpl; try reflexivity.
  - destruct i; eauto.
  -  destruct T; simpl; try reflexivity;
     try destruct v; simpl; try reflexivity.
     destruct (indexr i0 env); simpl; try reflexivity;
       destruct v; simpl; try reflexivity.
     destruct (indexr i0 GH); simpl; try reflexivity.

     destruct i; simpl; try reflexivity.*)
Qed.


(* this is just to accelerate Coq -- val_type in the goal is slooow *)
Inductive vtp: list vset -> list vset -> vl -> ty -> sel -> Prop :=
| vv: forall G H v T i, val_type G H v T i -> vtp G H v T i.


Lemma unvv: forall G H v T i,
  vtp G H v T i -> val_type G H v T i.
Proof.
  intros. inversion H0. subst. apply H2.
Qed.


(* make logical relation explicit *)
Definition R H G t v T := tevaln H t v /\ val_type G [] v T tp.


(* consistent environment *)
Definition R_env venv genv tenv :=
  length venv = length tenv /\
  length genv = length tenv /\
  forall x TX, indexr x tenv = Some TX ->
    (exists v : vl, R venv genv (tvar x) v TX) /\
    (exists vx (jj:vset),
       indexr x venv = Some vx /\
       indexr x genv = Some jj /\
       jj vx tp /\ (* do we need both this and R above?, Note by Fei: R is not necessary *)
       (forall vy iy, if pos iy then jj vy iy -> vtp genv [] vy TX iy
                      else           vtp genv [] vy TX iy -> jj vy iy) /\
       (forall vy iy, if pos iy then jj vy (lb iy) -> jj vy (ub iy) 
                      else           jj vy (ub iy) -> jj vy (lb iy)))
.


(* automation *)
Hint Unfold venv.
Hint Unfold tenv.

Hint Unfold open.
Hint Unfold indexr.
Hint Unfold length.

Hint Unfold R.
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

(* ############################################################ *)
(* Examples *)
(* ############################################################ *)


Ltac crush :=
  try solve [eapply stp_selx; compute; eauto; crush];
  try solve [eapply stp_selax; compute; eauto; crush];
  try solve [econstructor; compute; eauto; crush];
  try solve [eapply t_sub; crush].

(* define polymorphic identity function *)

Definition polyId := TAll (TMem TBot TTop) (TAll (TSel (varB 0)) (TSel (varB 1))).

Example ex1: has_type [] (tabs (TMem TBot TTop) (tabs (TSel (varF 0)) (tvar 1))) polyId.
Proof.
  crush.
Qed.

(* instantiate it to TTop *)
Example ex2: has_type [polyId] (tapp (tvar 0) (ttyp TTop)) (TAll TTop TTop).
Proof.
  crush.
Qed.

(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)



(* ## Extension, Regularity ## *)

Lemma wf_length : forall vs gs ts,
                    R_env vs gs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
Qed.

Lemma wf_length2 : forall vs gs ts,
                    R_env vs gs ts ->
                    (length gs = length ts).
Proof.
  intros. destruct H. destruct H0. auto.
Qed.


Hint Immediate wf_length.

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
    | TBot         => TBot
    | TAll T1 T2   => TAll (splice n T1) (splice n T2)
    | TSel (varF i) => TSel (varF i)
    | TSel (varB i) => TSel (varB i)
    | TSel (varH i) => if le_lt_dec n i then TSel (varH (i+1)) else TSel (varH i)
    | TMem T1 T2   => TMem (splice n T1) (splice n T2)
  end.

Definition spliceat n (V: (venv*ty)) :=
  match V with
    | (G,T) => (G,splice n T)
  end.

Lemma splice_open_permute: forall {X} (G0:list X) T2 n j,
(open_rec j (varH (n + S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open_rec j (varH (n + length G0)) T2)).
Proof.
  intros X G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto;
  destruct v; eauto.

  case_eq (le_lt_dec (length G) i); intros E LE; simpl; eauto.
  rewrite LE. eauto.
  rewrite LE. eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  case_eq (le_lt_dec (length G) (n + length G)); intros EL LE.
  rewrite E.
  assert (n + S (length G) = n + length G + 1). omega.
  rewrite H. eauto.
  omega.
  rewrite E. eauto.
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
  - (* TAll *) simpl.
    rewrite IHclosed1. rewrite IHclosed2.
    reflexivity.
    assumption. assumption.
  - (* TVarH *) simpl.
    case_eq (le_lt_dec n x); intros E LE. omega. reflexivity.
  - (* TMem *) simpl.
    rewrite IHclosed1. rewrite IHclosed2.
    reflexivity.
    assumption. assumption.
Qed.

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.

Ltac inv_mem := match goal with
                  | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |-
                    closed 0 (length ?GH) (length ?G) ?T2 => inversion H; subst; eauto
                  | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |-
                    closed 0 (length ?GH) (length ?G) ?T1 => inversion H; subst; eauto
                end.

Lemma stp_closed : forall G GH T1 T2,
                     stp G GH T1 T2 ->
                     closed 0 (length GH) (length G) T1 /\ closed 0 (length GH) (length G) T2.
Proof.
  intros. induction H;
    try solve [repeat ev; split; try inv_mem; eauto using indexr_max].
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

Lemma closed_open: forall i j k V T, closed (i+1) j k T -> closed i j k (TSel V) ->
  closed i j k (open_rec i V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.
  eapply closed_upgrade. eauto. eauto.
  - Case "TVarB". simpl.
    case_eq (beq_nat i x); intros E. eauto.
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
  tsize_flat T < n ->
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
  intros. apply stp_refl_aux with (n:=S (tsize_flat T)); eauto.
Qed.


Lemma concat_same_length: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GU = length GH1 ->
  GU=GH1 /\ GL=GH0.
Proof.
  intros. generalize dependent GH1. induction GU; intros.
  - simpl in H0. induction GH1. rewrite app_nil_l in H. rewrite app_nil_l in H.
    split. reflexivity. apply H.
    simpl in H0. omega.
  - simpl in H0. induction GH1. simpl in H0. omega.
    simpl in H0. inversion H0. simpl in H. inversion H. specialize (IHGU GH1 H4 H2).
    destruct IHGU. subst. split; reflexivity.
Qed.

Lemma concat_same_length': forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GL = length GH0 ->
  GU=GH1 /\ GL=GH0.
Proof.
  intros.
  assert (length (GU ++ GL) = length (GH1 ++ GH0)) as A. {
    rewrite H. reflexivity.
  }
  rewrite app_length in A. rewrite app_length in A.
  rewrite H0 in A. apply NPeano.Nat.add_cancel_r in A.
  apply concat_same_length; assumption.
Qed.

Lemma exists_GH1L: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X) x0,
  length GL = x0 ->
  GU ++ GL = GH1 ++ GH0 ->
  length GH0 <= x0 ->
  exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ GH0.
Proof.
  intros X GU. induction GU; intros.
  - eexists. rewrite app_nil_l. split. reflexivity. simpl in H0. assumption.
  - induction GH1.

    simpl in H0.
    assert (length (a :: GU ++ GL) = length GH0) as Contra. {
      rewrite H0. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H0. inversion H0.
    specialize (IHGU GL GH1 GH0 x0 H H4 H1).
    destruct IHGU as [GH1L [IHA IHB]].
    exists GH1L. split. simpl. rewrite IHA. reflexivity. apply IHB.
Qed.

Lemma exists_GH0U: forall {X} (GH1: list X) (GH0: list X) (GU: list X) (GL: list X) x0,
  length GL = x0 ->
  GU ++ GL = GH1 ++ GH0 ->
  x0 < length GH0 ->
  exists GH0U, GH0 = GH0U ++ GL.
Proof.
  intros X GH1. induction GH1; intros.
  - simpl in H0. exists GU. symmetry. assumption.
  - induction GU.

    simpl in H0.
    assert (length GL = length (a :: GH1 ++ GH0)) as Contra. {
      rewrite H0. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H0. inversion H0.
    specialize (IHGH1 GH0 GU GL x0 H H4 H1).
    destruct IHGH1 as [GH0U IH].
    exists GH0U. apply IH.
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
  - Case "bot".
    eapply stp_bot.
    rewrite map_splice_length_inc.
    apply closed_splice.
    assumption.
  - Case "sel1".
    eapply stp_sel1. apply H. assumption.
    assert (splice (length G0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp. reflexivity.
  - Case "sel2".
    eapply stp_sel2. apply H. assumption.
    assert (splice (length G0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp. reflexivity.
  - Case "sela1".
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_sela1.
      apply indexr_splice_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x = x +1) as A by omega.
      rewrite <- A. eapply H0.
      eapply IHstp. eauto.
    + eapply stp_sela1. eapply indexr_splice_lo. eauto. eauto. eauto.
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp. eauto.
  - Case "sela2".
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_sela2.
      apply indexr_splice_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x = x +1) as A by omega.
      rewrite <- A. eapply H0.
      eapply IHstp. eauto.
    + eapply stp_sela2. eapply indexr_splice_lo. eauto. eauto. eauto.
      assert (splice (length G0) TX=TX) as A. {
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

    specialize IHstp2 with (G3:=G0) (G4:=T3 :: G2).
    simpl in IHstp2. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x.
    rewrite app_length in IHstp2. simpl in IHstp2.
    eapply IHstp2. eauto.
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
  assert (closed 0 (length GH) (length G1) T3). eapply stp_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (splice (length GH)) [T3] ++ v1::GH =
          (T3::v1::GH)) as HGX3. {
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
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
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

Lemma venv_ext__ge_length:
  forall G G',
    venv_ext G' G ->
    length G' >= length G.
Proof.
  intros. induction H; simpl; omega.
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



(* TODO: need more about about GH? *)
Lemma indexr_safe_ex: forall H1 GH G1 TF i,
             R_env H1 GH G1 ->
             indexr i G1 = Some TF ->
             exists v, indexr i H1 = Some v /\ val_type GH [] v TF tp.
Proof.
  intros. destruct H. destruct H2. destruct (H3 i TF H0) as [[v [E V]] G].
  exists v. split; eauto. destruct E as [n E].
  assert (S n > n) as N. omega. specialize (E (S n) N).
  simpl in E. inversion E. eauto.
Qed.




Inductive res_type: list vset -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv [] v T tp ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.



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

Lemma open_subst_commute: forall T2 V j k x i,
closed i j k (TSel V) ->
(open_rec i (varH x) (subst V T2)) =
(subst V (open_rec i (varH (x+1)) T2)).
Proof.
  intros T2 TX j k. induction T2; intros; eauto; try destruct v; eauto.
  - simpl. rewrite IHT2_1; eauto. rewrite IHT2_2; eauto.
    eapply closed_upgrade. eauto. eauto.
  - simpl.
    case_eq (beq_nat i 0); intros E.
    apply beq_nat_true in E. subst.
    case_eq (beq_nat i0 0); intros E0.
    apply beq_nat_true in E0. subst.
    destruct TX; eauto.
    simpl. destruct i; eauto.
    inversion H; subst. omega.
    simpl. reflexivity.
    case_eq (beq_nat i0 0); intros E0.
    apply beq_nat_true in E0. subst.
    simpl. destruct TX; eauto.
    case_eq (beq_nat i i0); intros E1.
    apply beq_nat_true in E1. subst.
    inversion H; subst. omega.
    reflexivity.
    simpl. reflexivity.
  - simpl.
    case_eq (beq_nat i i0); intros E.
    apply beq_nat_true in E; subst.
    simpl.
    assert (x+1 <> 0) as A by omega.
    eapply beq_nat_false_iff in A.
    rewrite A.
    assert (x = x + 1 - 1) as B. unfold id. omega.
    rewrite <- B. reflexivity.
    simpl. reflexivity.
  - simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
Qed.

Lemma closed_no_subst: forall T i k TX,
   closed i 0 k T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
  try solve [rewrite (IHT i k TX); eauto; try omega];
  try solve [rewrite (IHT1 i k TX); eauto; rewrite (IHT2 (S i) k TX); eauto; try omega];
  try solve [rewrite (IHT1 i k TX); eauto; rewrite (IHT2 i k TX); eauto; try omega];
  try omega.
Qed.

Lemma closed_subst: forall i j k V T, closed i (j+1) k T -> closed 0 j k (TSel V) -> closed i j k (subst V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - Case "TVarH". simpl.
    case_eq (beq_nat x 0); intros E.
    eapply closed_upgrade. eapply closed_upgrade_free.
    eauto. omega. eauto. omega.
    econstructor. assert (x > 0). eapply beq_nat_false_iff in E. omega. omega.
Qed.

Lemma closed_nosubst: forall i j k V T, closed i (j+1) k T -> nosubst T -> closed i j k (subst V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto; subst;
  try inversion H0; eauto.

  - Case "TVarH". simpl. simpl in H0. unfold id in H0.
    assert (beq_nat x 0 = false) as E. apply beq_nat_false_iff. assumption.
    rewrite E.
    eapply cl_selh. omega.
Qed.

Lemma subst_open_commute_m: forall i j k k' j' V T2, closed (i+1) (j+1) k T2 -> closed 0 j' k' (TSel V) ->
    subst V (open_rec i (varH (j+1)) T2) = open_rec i (varH j) (subst V T2).
Proof.
  intros.
  generalize dependent i. generalize dependent j.
  induction T2; intros; inversion H; simpl; eauto; subst;
  try rewrite IHT2_1;
  try rewrite IHT2_2;
  try rewrite IHT2; eauto.
  - Case "TVarH". simpl. case_eq (beq_nat x 0); intros E.
    eapply closed_no_open. eapply closed_upgrade. eauto. omega.
    eauto.
  - Case "TVarB". simpl. case_eq (beq_nat i x); intros E.
    simpl. case_eq (beq_nat (j+1) 0); intros E2.
    eapply beq_nat_true_iff in E2. omega.
    subst. assert (j+1-1 = j) as A. omega. rewrite A. eauto.
    eauto.
Qed.

Lemma subst_open_commute: forall i j k k' V T2, closed (i+1) (j+1) k T2 -> closed 0 0 k' (TSel V) ->
    subst V (open_rec i (varH (j+1)) T2) = open_rec i (varH j) (subst V T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_zero: forall i i' k TX T2, closed i' 0 k T2 ->
    subst TX (open_rec i (varH 0) T2) = open_rec i TX T2.
Proof.
  intros. generalize dependent i'. generalize dependent i.
  induction T2; intros; inversion H; simpl; eauto;
  try solve [rewrite (IHT2_1 _ i'); eauto;
             rewrite (IHT2_2 _ (S i')); eauto;
             rewrite (IHT2_2 _ (S i')); eauto];
  try solve [rewrite (IHT2_1 _ i'); eauto;
             rewrite (IHT2_2 _ i'); eauto].
  subst.
  case_eq (beq_nat x 0); intros E. omega. omega.
  case_eq (beq_nat i x); intros E. eauto. eauto.
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

Lemma nosubst_open: forall i V T2, nosubst (TSel V) -> nosubst T2 -> nosubst (open_rec i V T2).
Proof.
  intros. generalize dependent i. induction T2; intros;
  try inversion H0; simpl; eauto; destruct v; eauto.
  case_eq (beq_nat i i0); intros E. eauto. eauto.
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
(*
Definition compat (GX:venv) (TX: ty) (V: option vl) (G1:venv) (T1:ty) (T1':ty) :=
  (exists x1 v, indexr x1 G1 = Some v /\ V = Some v /\ GX = GX /\ val_type_stub GX v TX /\ T1' = (subst (varF x1) T1)) \/
  (closed 0 0 (length G1) T1 /\ T1' = T1) \/ (* this one is for convenience: redundant with next *)
  (nosubst T1 /\ T1' = subst (varF 0) T1).
Definition compat2 (GX:venv) (TX: ty) (V: option vl) (p1:(venv*ty)) (p2:(venv*ty)) :=
  match p1, p2 with
      (G1,T1), (G2,T2) => G1 = G2 /\ compat GX TX V G1 T1 T2
  end.
Lemma closed_compat: forall GX TX V GXX TXX TXX' i j,
  compat GX TX V GXX TXX TXX' ->
  closed 0 j (length GXX) TX ->
  closed i (j+1) (length GXX) TXX ->
  closed i j (length GXX) TXX'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2. destruct H2. destruct H2. destruct H3. destruct H4. destruct H4.
    destruct H5. rewrite H5.
    eapply closed_subst. eauto.
    eapply cl_sel. apply indexr_max in H2. omega.
  - destruct H2. rewrite H3.
    eapply closed_upgrade. eapply closed_upgrade_free. eauto. omega. omega.
  - subst. eapply closed_nosubst. eauto. eauto.
Qed.
Lemma indexr_compat_miss0: forall GH GH' GX TX V (GXX:venv) (TXX:ty) n,
      Forall2 (compat2 GX TX V) GH GH' ->
      indexr (n+1) (GH ++ [(GX, TX)]) = Some (GXX,TXX) ->
      exists TXX', indexr n GH' = Some (GXX,TXX') /\ compat GX TX V GXX TXX TXX'.
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
Lemma compat_top: forall GX TX V G1 T1',
  compat GX TX V G1 TTop T1' -> closed 0 0 (length GX) TX -> T1' = TTop.
Proof.
  intros ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.
Lemma compat_bot: forall GX TX V G1 T1',
  compat GX TX V G1 TBot T1' -> closed 0 0 (length GX) TX -> T1' = TBot.
Proof.
  intros ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.
Lemma compat_mem: forall GX TX V G1 S1 U1 T1',
    compat GX TX V G1 (TMem S1 U1) T1' ->
    closed 0 0 (length GX) TX ->
    exists SA UA, T1' = TMem SA UA /\
                  compat GX TX V G1 S1 SA /\
                  compat GX TX V G1 U1 UA.
Proof.
  intros ? ? ? ? ? ? ? CC CLX.
  destruct CC as [|CC]; ev; subst.
  repeat eexists; eauto; solve [unfold compat; left; repeat eexists; eassumption].
  destruct CC as [|CC]; ev; subst;
  inversion H; subst;
  repeat eexists; eauto; solve [unfold compat; eauto].
Qed.
Lemma compat_mem_fwd2: forall GX TX V G1 T2 T2',
    compat GX TX V G1 T2 T2' ->
    compat GX TX V G1 (TMem TBot T2) (TMem TBot T2').
Proof.
  intros. repeat destruct H as [|H]; ev; repeat eexists; eauto.
  - left. repeat eexists; eauto. rewrite H3. eauto.
  - right. left. subst. eauto.
  - right. right. subst. simpl. eauto.
Qed.
Lemma compat_mem_fwd1: forall GX TX V G1 T1 T1',
    compat GX TX V G1 T1 T1' ->
    compat GX TX V G1 (TMem T1 TTop) (TMem T1' TTop).
Proof.
  intros. repeat destruct H as [|H]; ev; repeat eexists; eauto.
  - left. repeat eexists; eauto. rewrite H3. eauto.
  - right. left. subst. eauto.
  - right. right. subst. simpl. eauto.
Qed.
Lemma compat_sel: forall GX TX V G1 T1' (GXX:venv) (TXX:ty) x v,
    compat GX TX V G1 (TSel (varF x)) T1' ->
    closed 0 0 (length GX) TX ->
    closed 0 0 (length GXX) TXX ->
    indexr x G1 = Some v ->
    val_type_stub GXX v TXX ->
    exists TXX', T1' = (TSel (varF x)) /\ compat GX TX V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? CC CL CL1 IX HV.
  destruct CC.
  destruct H. destruct H. destruct H. destruct H0. destruct H1. destruct H2.
  simpl in H3. eexists. split. eauto. right. left. eauto.
  destruct H. destruct H. simpl in H0. eexists. split. eauto. right. left. eauto.
  destruct H. destruct H. simpl in H0. eexists. split. eauto. right. left. eauto.
Qed.
Lemma compat_selh: forall GX TX V G1 T1' GH0 GH0' (GXX:venv) (TXX:ty) x,
    compat GX TX V G1 (TSel (varH x)) T1' ->
    closed 0 0 (length GX) TX ->
    indexr x (GH0 ++ [(GX, TX)]) = Some (GXX, TXX) ->
    Forall2 (compat2 GX TX V) GH0 GH0' ->
    (x = 0 /\ GXX = GX /\ TXX = TX) \/
    exists TXX',
      x > 0 /\ T1' = TSel (varH (x-1)) /\
      indexr (x-1) GH0' = Some (GXX, TXX') /\
      compat GX TX V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? CC CL IX FA.
  case_eq (beq_nat x 0); intros E.
  - left. assert (x = 0). eapply beq_nat_true_iff. eauto. subst x.
    rewrite indexr_hit0 in IX. inversion IX. eauto.
  - right. assert (x <> 0). eapply beq_nat_false_iff. eauto.
    assert (x > 0). unfold id. unfold id in H. omega.
    eapply (indexr_compat_miss0) in FA. destruct FA.
    destruct CC.
    destruct H2. destruct H2. destruct H2. destruct H3. destruct H4. destruct H5.
    simpl in H6.
    rewrite E in H6.
    eexists. split. omega. split; eauto.
    simpl in H2. destruct H2. destruct H2.
    inversion H2; subst. omega.
    destruct H2. rewrite E in H3.
    eexists. eauto.
    assert (x-1+1=x) as A. omega. rewrite A. eauto.
Qed.
Lemma compat_all: forall GX TX V G1 T1 T2 T1' n,
    compat GX TX V G1 (TAll T1 T2) T1' ->
    closed 0 0 (length GX) TX -> closed 1 (n+1) (length G1) T2 ->
    exists TA TB, T1' = TAll TA TB /\
                  closed 1 n (length G1) TB /\
                  compat GX TX V G1 T1 TA /\
                  compat GX TX V G1 (open_rec 0 (varH (n+1)) T2) (open_rec 0 (varH n) TB).
Proof.
  intros ? ? ? ? ? ? ? ? CC CLX CL2. destruct CC.
  ev. simpl in H0. repeat eexists; eauto. eapply closed_subst; eauto using indexr_max.
  unfold compat. left. repeat eexists; eauto.
  unfold compat. left. repeat eexists; eauto. erewrite subst_open_commute; eauto.
  destruct H. destruct H. inversion H. repeat eexists. eauto. subst.
  eapply closed_upgrade_free. eauto. omega. unfold compat. eauto.
  unfold compat. eauto. right. right. subst.
  split. eapply nosubst_open. simpl. omega. eapply nosubst_intro. eauto. symmetry.
  assert (T2 = subst (varF 0) T2) as A. symmetry. eapply closed_no_subst. eauto.
  remember (open_rec 0 (varH n) T2) as XX. rewrite A in HeqXX. subst XX.
  eapply subst_open_commute. eauto. eauto.
  simpl in H. destruct H. destruct H. repeat eexists. eauto. eapply closed_nosubst. eauto. eauto.
  unfold compat. right. right. eauto.
  unfold compat. right. right. split. eapply nosubst_open. simpl. omega. eauto.
  erewrite subst_open_commute. eauto. eauto. eauto.
Qed.
Lemma compat_closed: forall GX TX V G T T' j,
  compat GX TX V G T T' ->
  closed 0 (j + 1) (length G) T ->
  closed 0 0 (length GX) TX ->
  closed 0 j (length G) T'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2 as [x1 [v [Hindex [HeqV [HGX [Hv Heq]]]]]]. subst.
    apply closed_subst. eassumption.
    apply indexr_max in Hindex. apply cl_sel. omega.
  - destruct H2. subst.
    eapply closed_upgrade_free. eapply H2. omega.
  - subst.
    apply closed_nosubst. assumption. eauto.
Qed.
Lemma stp2_substitute_aux: forall n, forall G1 G2 T1 T2 GH m n1,
   stp2 false m G1 T1 G2 T2 GH n1 ->
   n1 <= n ->
   forall GH0 GH0' GX TX T1' T2' V,
     GX = GX ->
     GH = (GH0 ++ [(GX, TX)]) ->
     val_type_stub GX V TX ->
     closed 0 0 (length GX) TX ->
     compat GX TX (Some V) G1 T1 T1' ->
     compat GX TX (Some V) G2 T2 T2' ->
     Forall2 (compat2 GX TX (Some V)) GH0 GH0' ->
     stpd2 false m G1 T1' G2 T2' GH0'.
Proof. admit. (*PERF
  intros n. induction n.
  Case "z". intros. inversion H0. subst. inversion H; eauto.
  intros G1 G2 T1 T2 GH m n1 H NE. remember false as s.
  induction H; inversion Heqs.
   - Case "top".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    eapply compat_top in IX2.
    subst. eapply stpd2_top.
    eapply compat_closed. eassumption.
    rewrite app_length in H. simpl in H.
    erewrite <- Forall2_length. eapply H. eassumption.
    eassumption. assumption.
  - Case "bot".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    eapply compat_bot in IX1.
    subst. eapply stpd2_bot.
    eapply compat_closed. eassumption.
    rewrite app_length in H. simpl in H.
    erewrite <- Forall2_length. eapply H. eassumption.
    eassumption. assumption.
  - Case "mem".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    eapply compat_mem in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_mem in IX2. repeat destruct IX2 as [? IX2].
    subst. eapply stpd2_mem.
    eapply IHn; eauto; try omega.
    eapply IHn; eauto; try omega.
    eauto. eauto.
  - Case "sel1".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.
    eapply (compat_sel GXX TXX (Some V) G1 T1' GX TX) in IX1. repeat destruct IX1 as [? IX1].
    assert (compat GXX TXX (Some V) GX TX TX) as CPX. right. left. eauto.
    subst.
    eapply stpd2_sel1. eauto. eauto. eauto.
    eapply IHn; eauto; try omega.
    eapply compat_mem_fwd2. eauto.
    eauto. eauto. eauto. eauto.
  - Case "sel2".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.
    eapply (compat_sel GXX TXX (Some V) G2 T2' GX TX) in IX2. repeat destruct IX2 as [? IX2].
    assert (compat GXX TXX (Some V) GX TX TX) as CPX. right. left. eauto.
    subst.
    eapply stpd2_sel2. eauto. eauto. eauto.
    eapply IHn; eauto; try omega.
    eapply compat_mem_fwd1. eauto.
    eauto. eauto. eauto. eauto.
  - Case "selx".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.
    assert (T1' = TSel (varF x1)). {
      destruct IX1. ev. eauto.
      destruct H6. ev. auto.
      destruct H6. ev. eauto.
    }
    assert (T2' = TSel (varF x2)). {
      destruct IX2. ev. eauto.
      destruct H7. ev. auto.
      destruct H7. ev. eauto.
    }
    subst.
    eapply stpd2_selx. eauto. eauto.
  - Case "sela1".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.
    assert (compat GXX TXX (Some V) G1 (TSel (varH x)) T1') as IXX. eauto.
    eapply (compat_selh GXX TXX (Some V) G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].
    destruct IX1.
    + SCase "x = 0".
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H8; subst.
        eapply stpd2_sel1. eauto. eauto. eauto.
        eapply IHn; eauto; try omega. right. left. auto.
        eapply compat_mem_fwd2. eauto.
      * subst. inversion H7. subst. omega.
      * subst. destruct H7. eauto.
    + SCase "x > 0".
      ev. subst.
      eapply stpd2_sela1. eauto.
      assert (x-1+1=x) as A by omega.
      remember (x-1) as x1. rewrite <- A in H0.
      eapply compat_closed. eauto. eauto. eauto.
      eapply IHn; eauto; try omega.
      eapply compat_mem_fwd2. eauto.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.
(*  - Case "sela2".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.
    assert (compat GXX TXX (Some V) G2 (TSel (varH x)) T2') as IXX. eauto.
    eapply (compat_selh GXX TXX (Some V) G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].
    destruct IX2.
    + SCase "x = 0".
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H8; subst.
        eapply stpd2_sel2. eauto. eauto. eauto.
        eapply IHn; eauto; try omega. right. left. auto.
        eapply compat_mem_fwd1. eauto.
      * subst. inversion H7. subst. omega.
      * subst. destruct H7. eauto.
    + SCase "x > 0".
      ev. subst.
      eapply stpd2_sela2. eauto.
      assert (x-1+1=x) as A by omega.
      remember (x-1) as x1. rewrite <- A in H0.
      eapply compat_closed. eauto. eauto. eauto.
      eapply IHn; eauto; try omega.
      eapply compat_mem_fwd1. eauto.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.*)
  - Case "selax".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.
    assert (compat GXX TXX (Some V) G1 (TSel (varH x)) T1') as IXX1. eauto.
    assert (compat GXX TXX (Some V) G2 (TSel (varH x)) T2') as IXX2. eauto.
    destruct v as [GX TX].
    eapply (compat_selh GXX TXX (Some V) G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].
    eapply (compat_selh GXX TXX (Some V) G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].
    assert (not (nosubst (TSel (varH 0)))). unfold not. intros. simpl in H1. eauto.
    assert (not (closed 0 0 (length G1) (TSel (varH 0)))). unfold not. intros. inversion H6. omega.
    assert (not (closed 0 0 (length G2) (TSel (varH 0)))). unfold not. intros. inversion H7. omega.
    destruct x; destruct IX1; ev; try omega; destruct IX2; ev; try omega; subst.
    + SCase "x = 0".
      repeat destruct IXX1 as [IXX1|IXX1]; ev; try contradiction.
      repeat destruct IXX2 as [IXX2|IXX2]; ev; try contradiction.
      * SSCase "sel-sel".
        subst. simpl. inversion H17; subst. inversion H9; subst.
        eapply stpd2_selx. eauto. eauto.
    + SCase "x > 0".
      destruct IXX1; destruct IXX2; ev; subst; eapply stpd2_selax; eauto.
    (* leftovers *)
    + eauto. + subst. eauto. + eauto. + eauto. + subst. eauto. + eauto.
  - Case "all".
    intros GH0 GH0' GX TX T1' T2' V ? ? ? CX IX1 IX2 FA.
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
      eapply IHn. eauto. omega. simpl. eauto.
      change ((G2, T3) :: GH0 ++ [(GX, TX)]) with (((G2, T3) :: GH0) ++ [(GX, TX)]).
      reflexivity.
      eauto. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
  - Case "wrapf".
    intros. subst. eapply stpd2_wrapf. eapply IHn; eauto; try omega.
  - Case "transf".
    intros. subst.
    apply stp2_extend2 with (v1:=V) in H.
    apply stp2_extend1 with (v1:=V) in H0.
    eapply stpd2_transf.
    eapply IHn; eauto; try omega.
    unfold compat. simpl. left. exists (length G2). exists V.
    rewrite <- beq_nat_refl. split; eauto.
    eapply IHn; eauto; try omega.
    unfold compat. simpl. left. exists (length G2). exists V.
    rewrite <- beq_nat_refl. split; eauto. *)
Qed.
Lemma stp2_substitute: forall G1 G2 T1 T2 GH m,
   stpd2 false m G1 T1 G2 T2 GH ->
   forall GH0 GH0' GX TX T1' T2' V,
     GX = GX ->
     GH = (GH0 ++ [(GX, TX)]) ->
     val_type_stub GX V TX ->
     closed 0 0 (length GX) TX ->
     compat GX TX (Some V) G1 T1 T1' ->
     compat GX TX (Some V) G2 T2 T2' ->
     Forall2 (compat2 GX TX (Some V)) GH0 GH0' ->
     stpd2 false m G1 T1' G2 T2' GH0'.
Proof.
  intros. repeat eu. eapply stp2_substitute_aux; eauto.
Qed.
*)





(* ### Value Typing / Logical Relation for Values ### *)


(* ### TODO: Extend and Substitute  ### *)

(* NOTE: we need more generic internal lemmas, due to contravariance *)

(* used in valtp_widen *)
Lemma valtp_closed: forall vf GH H1 T1 i,
  val_type H1 GH vf T1 i ->
  closed 0 (length GH) (length H1) T1.
Proof.
  intros. destruct T1; destruct vf;
  rewrite val_type_unfold in H; try eauto; try contradiction.
  - (* fun *) destruct i; try solve by inversion.
    ev. econstructor; eauto.
  - (* sel *) destruct v.
              remember (indexr i0 H1) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto.
              remember (indexr i0 GH) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto. 
              inversion H. 
  - (* sel *) destruct v.
              remember (indexr i0 H1) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto.
              remember (indexr i0 GH) as L; try destruct L as [?|]; try contradiction.
              constructor. eapply indexr_max. eauto. 
              inversion H.
  - destruct i; try solve by inversion. ev. constructor; assumption.
    ev. constructor; assumption.
  - destruct i; try solve by inversion.
    ev. constructor; assumption.
    ev. constructor; assumption.
    ev. constructor; assumption.
Qed.

 
Lemma valtp_extend_aux: forall n T1 i vx vf H1 G1,
  tsize_flat T1 < n ->
  closed 0 (length G1) (length H1) T1 ->
  (vtp H1 G1 vf T1 i <-> vtp (vx :: H1) G1 vf T1 i).
Proof. 
  induction n; intros ? ? ? ? ? ? S C. inversion S.
  destruct T1; split; intros V; apply unvv in V; rewrite val_type_unfold in V.
  - apply vv. rewrite val_type_unfold. assumption.
  - apply vv. rewrite val_type_unfold. assumption.
  - apply vv. rewrite val_type_unfold. assumption.
  - apply vv. rewrite val_type_unfold. assumption.
  - destruct vf. destruct i. 
    + ev. apply vv. rewrite val_type_unfold. split.
    simpl. eapply closed_upgrade_freef. apply H. omega. split. simpl.
    eapply closed_upgrade_freef. apply H0. omega. intros.
    specialize (H2 _ _ H3).
    assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then jj vy iy -> val_type H1 G1 vy T1_1 iy
      else val_type H1 G1 vy T1_1 iy -> jj vy iy)).
    { intros. destruct (pos iy) eqn : A. intros. specialize (H4 vy iy). rewrite A in H4.
      specialize (H4 H6). apply unvv. apply vv in H4. simpl in *. eapply IHn; try omega; try eassumption.
      intros. specialize (H4 vy iy). rewrite A in H4. apply H4. apply unvv. simpl in *. 
      apply vv in H6. apply IHn; try omega; try eassumption. }
    specialize (H2 H6 H5). ev. exists x. split; try assumption.
    apply unvv. apply vv in H7. apply IHn; try eassumption. unfold open. erewrite <- open_preserves_size.
    simpl in *. omega. eapply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
    constructor. simpl. omega.
    + apply vv. rewrite val_type_unfold. assumption.
    + apply vv. rewrite val_type_unfold. assumption.
    + apply vv. rewrite val_type_unfold. assumption.
  - destruct vf. destruct i.
    + ev. apply vv. rewrite val_type_unfold. inversion C. subst.
    split; try assumption. split; try assumption. intros.
    specialize (H2 _ _ H3).
    assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then jj vy iy -> val_type (vx :: H1) G1 vy T1_1 iy
      else val_type (vx :: H1) G1 vy T1_1 iy -> jj vy iy)).
    { intros. destruct (pos iy) eqn : A. intros. specialize (H4 vy iy). rewrite A in H4. specialize (H4 H6).
      apply unvv. apply vv in H4. simpl in *. apply IHn; try eassumption; try omega.
      specialize (H4 vy iy). rewrite A in H4. intros. apply H4. apply unvv. apply vv in H6. 
      simpl in *. eapply IHn; try eassumption; try omega. }
    specialize (H2 H6 H5). ev. exists x. split; try assumption. apply unvv. apply vv in H7. eapply IHn; try eassumption.
    unfold open. erewrite <- open_preserves_size. simpl in *. omega. simpl. eapply closed_open.
    simpl. eapply closed_upgrade_free. eassumption. omega. constructor. omega.
    + apply vv. rewrite val_type_unfold. assumption.
    + apply vv. rewrite val_type_unfold. assumption.
    + apply vv. rewrite val_type_unfold. assumption.

  - apply vv. rewrite val_type_unfold. destruct vf.
    + destruct v.
    destruct (indexr i0 H1) eqn : A.
    assert (indexr i0 (vx :: H1) = Some v). apply indexr_extend. assumption. rewrite H. assumption.
    inversion V. assumption. inversion V. 
    + destruct v.
    destruct (indexr i0 H1) eqn : A. 
    assert (indexr i0 (vx :: H1) = Some v). apply indexr_extend. assumption. rewrite H. assumption.
    inversion V. assumption. inversion V.

  - apply vv. rewrite val_type_unfold. destruct vf.
    + destruct v. inversion C. subst. 
    eapply indexr_has in H4. ev. assert (indexr i0 (vx:: H1) = Some x). apply indexr_extend.
    assumption. rewrite H0 in V. rewrite H. assumption. assumption. inversion V.
    + destruct v. inversion C. subst. 
    eapply indexr_has in H4. ev. assert (indexr i0 (vx:: H1) = Some x). apply indexr_extend.
    assumption. rewrite H0 in V. rewrite H. assumption. assumption. inversion V.

  - inversion C. subst. apply vv. rewrite val_type_unfold. destruct vf. destruct i. inversion V. 
    ev. split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    apply unvv. eapply IHn with (H1 := H1). simpl in *. omega. apply H6. apply vv. assumption.
    ev. split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    apply unvv. eapply IHn with (H1 := H1). simpl in *. omega. assumption. apply vv. assumption.
    destruct i. simpl. ev. split. eapply closed_upgrade_freef; try eassumption; try omega.
    split. eapply closed_upgrade_freef; try eassumption; try omega.

    intros. destruct (pos iy) eqn : A. specialize (H2 vy iy). rewrite A in H2. intros.
    assert (val_type H1 G1 vy T1_1 iy). apply unvv. apply vv in H3. simpl in *. eapply IHn; try eassumption; try omega.
    specialize (H2 H4). apply unvv. apply vv in H2. simpl in *. eapply IHn with (H1 := H1); try eassumption; try omega.
            specialize (H2 vy iy). rewrite A in H2. intros. assert (val_type H1 G1 vy T1_2 iy).
    apply unvv. apply vv in H3. simpl in *. eapply IHn; try eassumption; try omega.
    specialize (H2 H4). simpl in *. apply unvv. apply vv in H2. eapply IHn with (H1 := H1); try eassumption; try omega.
    
    ev. split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    simpl in *. apply unvv. apply vv in H2. eapply IHn with (H1 := H1); try eassumption; try omega.

    ev. split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    split. simpl. eapply closed_upgrade_freef. eassumption. omega.
    simpl in *. apply unvv. apply vv in H2. eapply IHn with (H1 := H1); try eassumption; try omega.

  - inversion C. subst. apply vv. rewrite val_type_unfold. destruct vf. destruct i. inversion V. 
    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption;
    try omega. 

    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption;
    try omega. 

    destruct i. ev. split; try assumption. split; try assumption.
    intros. destruct (pos iy) eqn : A. specialize (H2 vy iy). rewrite A in H2. intros.
    assert (val_type (vx :: H1) G1 vy T1_1 iy ). apply unvv. apply vv in H3. simpl in *. eapply IHn with (H1 := H1); try eassumption; try omega.
    specialize (H2 H4). apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption; try omega.
            specialize (H2 vy iy). rewrite A in H2. intros. assert (val_type (vx :: H1) G1 vy T1_2 iy).
    simpl in *. apply unvv. apply vv in H3. eapply IHn with (H1 := H1); try eassumption; try omega.
    specialize (H2 H4). apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption; try omega.

    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption; try omega.
    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. simpl in *. eapply IHn; try eassumption; try omega.
Qed.



(* used in wf_env_extend and in main theorem *)
Lemma valtp_extend: forall i vx vf H1 T1,
  val_type H1 [] vf T1 i ->
  vtp (vx::H1) [] vf T1 i.
Proof.
  intros. eapply valtp_extend_aux with (H1 := H1). eauto. simpl.
  apply valtp_closed in H. simpl in *. assumption. apply vv in H. assumption.
Qed.

(* used in wf_env_extend *)
Lemma valtp_shrink: forall i vx vf H1 T1,
  val_type (vx::H1) [] vf T1 i ->
  closed 0 0 (length H1) T1 ->                     
  vtp H1 [] vf T1 i.
Proof.
  intros. apply vv in H. eapply valtp_extend_aux. eauto. simpl. assumption.
  eassumption.
Qed.

Lemma valtp_shrinkM: forall i vx vf H1 GH T1,
  val_type (vx::H1) GH vf T1 i ->
  closed 0 (length GH) (length H1) T1 ->                     
  vtp H1 GH vf T1 i.
Proof.
  intros. apply vv in H. eapply valtp_extend_aux. eauto. simpl. assumption.
  eassumption.
Qed.

Lemma indexr_hit_high: forall (X:Type) x (jj : X) l1 l2 vf,
  indexr x (l1 ++ l2) = Some vf -> (length l2) <= x ->
  indexr (x + 1) (l1 ++ jj :: l2) = Some vf.
Proof. intros. induction l1. simpl in *. apply indexr_max in H. omega.
  simpl in *. destruct (beq_nat x (length (l1 ++ l2))) eqn : A.
  rewrite beq_nat_true_iff in A. assert (x + 1 = length (l1 ++ l2) + 1).
  omega. rewrite app_length in *. assert(x + 1 = length (l1) + S (length l2)).
  omega. simpl in *. rewrite <- beq_nat_true_iff in H2. rewrite H2. assumption.
  rewrite beq_nat_false_iff in A. assert (x + 1 <> length (l1 ++ l2) + 1).
  omega. rewrite app_length in *. assert(x + 1 <> length (l1) + S (length l2)). omega.
  rewrite <- beq_nat_false_iff in H2. simpl. rewrite H2. apply IHl1. assumption.
Qed.

Lemma indexr_hit_low: forall (X:Type) x (jj : X) l1 l2 vf,
  indexr x (l1 ++ l2) = Some vf -> x < (length l2) ->
  indexr (x) (l1 ++ jj :: l2) = Some vf.
Proof. intros. apply indexr_has in H0. ev. assert (indexr x (l1 ++ l2) = Some x0).
  apply indexr_extend_mult. assumption. rewrite H1 in H. inversion H. subst.
  assert (indexr x (jj :: l2) = Some vf). apply indexr_extend. assumption.
  apply indexr_extend_mult. eassumption.
Qed.

Lemma splice_preserves_size: forall T j,
  tsize_flat T = tsize_flat (splice j T).
Proof.
  intros. induction T; simpl; try rewrite IHT1; try rewrite IHT2; try reflexivity.
  destruct v; simpl; try reflexivity. destruct (le_lt_dec j i); simpl; try reflexivity.
Qed.

Lemma open_permute : forall T V0 V1 i j a b c d,
  closed 0 a b (TSel V0) -> closed 0 c d (TSel V1) -> i <> j ->
  open_rec i V0 (open_rec j V1 T) = open_rec j V1 (open_rec i V0 T).
Proof. intros. generalize dependent i. generalize dependent j.
  induction T; intros.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. specialize (IHT1 _ _ H1). rewrite IHT1. assert ((S i) <> (S j)) by omega.
  specialize (IHT2 _ _ H2). rewrite IHT2. reflexivity.
  destruct v. simpl. reflexivity. simpl. reflexivity.
  (* varB *)
  destruct (beq_nat i i0) eqn : A. rewrite beq_nat_true_iff in A. subst.
  assert ((open_rec j V1 (TSel (varB i0)) = (TSel (varB i0)))). simpl. 
  assert (beq_nat j i0 = false). rewrite beq_nat_false_iff. omega. rewrite H2. reflexivity.
  rewrite H2. simpl. assert (beq_nat i0 i0 = true). erewrite beq_nat_refl. eauto. rewrite H3. 
  eapply closed_no_open. eapply closed_upgrade. eauto. omega.
  destruct (beq_nat j i0) eqn : B. rewrite beq_nat_true_iff in B. subst.
  simpl. assert (beq_nat i0 i0 = true). erewrite beq_nat_refl. eauto. rewrite H2.
  assert (beq_nat i i0 = false). rewrite beq_nat_false_iff. omega. rewrite H3.
  assert (TSel (V1) = open_rec i V0 (TSel V1)). eapply closed_no_open. eapply closed_upgrade.
  eapply H0. omega. rewrite <- H4. simpl. rewrite H2. reflexivity.
  assert ((open_rec j V1 (TSel (varB i0))) = TSel (varB i0)). simpl. rewrite B. reflexivity.
  rewrite H2. assert (open_rec i V0 (TSel (varB i0)) = (TSel (varB i0))). simpl.
  rewrite A. reflexivity. rewrite H3. simpl. rewrite B. reflexivity.

  simpl. specialize (IHT1 _ _ H1). rewrite IHT1.
  specialize (IHT2 _ _ H1). rewrite IHT2. reflexivity.
Qed.

Lemma closed_open2: forall i j k V T i1, closed i j k T -> closed i j k (TSel V) ->
  closed i j k (open_rec i1 V T).
Proof.
  intros. generalize dependent i. revert i1.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.
  eapply closed_upgrade. eauto. eauto.
  - Case "TVarB". simpl.
    case_eq (beq_nat i1 x); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
Qed.


Lemma splice_retreat4: forall T i j k m V' V ,
  closed i (j + 1) k (open_rec m V' (splice 0 T)) ->
  (closed i j k (TSel V) -> closed i (j) k (open_rec m V T)).
Proof. induction T; intros; try destruct v; simpl in *.
  constructor.
  constructor.
  inversion H; subst. 
  specialize (IHT1 _ _ _ _ _ _ H6 H0). assert (closed (S i) (j) k (TSel V)).
  eapply closed_upgrade. eapply H0. omega.
  specialize (IHT2 _ _ _ _ _ _ H7 H1). constructor. assumption. assumption. 
  inversion H. subst. constructor. omega.
  inversion H. subst. constructor. omega.
  destruct (beq_nat m i0) eqn : A. assumption. 
    inversion H. subst. constructor. omega.
  inversion H. subst. constructor. eapply IHT1. eassumption. assumption.
  eapply IHT2. eassumption. assumption.
Qed.

Lemma splice_retreat5: forall T i j k m V' V ,
  closed i (j + 1) k (TSel V') -> closed i (j) k (open_rec m V T) ->
  closed i (j + 1) k (open_rec m V' (splice 0 T)).
Proof. induction T; intros; try destruct v; simpl in *.
  constructor.
  constructor.
  inversion H0; subst.
  specialize (IHT1 _ _ _ _ _ _ H H6). assert (closed (S i) (j + 1) k (TSel V')).
  eapply closed_upgrade. eapply H. omega.
  specialize (IHT2 _ _ _ _ _ _ H1 H7). constructor. assumption. assumption. 
  inversion H0. subst. constructor. omega.
  inversion H0. subst. constructor. omega.
  destruct (beq_nat m i0) eqn : A. assumption. 
    inversion H0. subst. constructor. omega.
  inversion H0. subst. constructor. eapply IHT1. eassumption. eassumption.
  eapply IHT2. eassumption. eassumption.
Qed.


Lemma splice_open_permute0: forall x0 T2 n j,
(open_rec j (varH (n + x0 + 1 )) (splice (x0) T2)) =
(splice (x0) (open_rec j (varH (n + x0)) T2)).
Proof.
  intros x0 T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto;
  destruct v; eauto.

  case_eq (le_lt_dec (x0) i); intros E LE; simpl; eauto.
  rewrite LE. eauto.
  rewrite LE. eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  case_eq (le_lt_dec (x0) (n + x0)); intros EL LE.
  rewrite E. eauto. omega.
  rewrite E. eauto.
Qed.

Lemma indexr_extend_end: forall {X : Type} (jj : X) l x,
  indexr (x + 1) (l ++ [jj]) = indexr x l.
Proof. intros. induction l. simpl. assert (beq_nat (x + 1) 0 = false).
  rewrite beq_nat_false_iff. omega. rewrite H. reflexivity.
  simpl. destruct (beq_nat (x) (length (l))) eqn : A.
  rewrite beq_nat_true_iff in A. assert (x + 1 = length (l ++ [jj])). rewrite app_length. simpl. omega.
  rewrite <- beq_nat_true_iff in H. rewrite H. reflexivity.
  rewrite beq_nat_false_iff in A. assert (x +1 <> length (l ++ [jj])). rewrite app_length. simpl. omega.
  rewrite <- beq_nat_false_iff in H. rewrite H. assumption.
Qed.

Lemma indexr_hit01: forall {X : Type} GH (jj : X),
      indexr 0 (GH ++ [jj]) = Some (jj).
Proof.
  intros X GH. induction GH.
  - intros. simpl. eauto.
  - intros. simpl. destruct (length (GH ++ [jj])) eqn : A.
    rewrite app_length in *. simpl in *. omega.
    apply IHGH.
Qed.  


Lemma valtp_splice_aux: forall n T vf H GH1 GH0 jj i,
tsize_flat T < n -> closed 0 (length (GH1 ++ GH0)) (length H) T ->
(  
  vtp H (GH1 ++ GH0) vf T i <-> 
  vtp H (GH1 ++ jj :: GH0) vf (splice (length GH0) T) i
).
Proof.
  induction n; intros ? ? ? ? ? ? ? Sz C. inversion Sz.
  destruct T; split; intros V; apply unvv in V; rewrite val_type_unfold in V;
    assert (length GH1 + S (length GH0) = S(length (GH1 ++ GH0))) as E;
    try rewrite app_length; try omega.
  - apply vv. rewrite val_type_unfold. destruct vf; apply V.
  - apply vv. rewrite val_type_unfold. destruct vf; apply V.
  - apply vv. rewrite val_type_unfold. destruct vf; apply V.
  - apply vv. rewrite val_type_unfold. destruct vf; apply V.
  - destruct vf. destruct i.
    + ev. apply vv. rewrite val_type_unfold. split.
    rewrite app_length. simpl. rewrite E. apply closed_splice. apply H0.
    split. rewrite app_length. simpl. rewrite E. apply closed_splice. apply H1.
    intros. specialize (H2 _ _ H3). 
    assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then jj0 vy iy -> val_type H (GH1 ++ GH0) vy T1 iy
      else val_type H (GH1 ++ GH0) vy T1 iy -> jj0 vy iy)).
    { intros. destruct (pos iy) eqn : A. intros. specialize (H4 vy iy). rewrite A in H4. specialize (H4 H6).
      apply unvv. apply vv in H4. simpl in *. eapply IHn; try eassumption; try omega. 
      specialize (H4 vy iy).  rewrite A in H4. intros. apply H4. simpl in *. apply unvv. apply vv in H6.
      eapply IHn with (GH0 := GH0); try eassumption; try try omega. }
    specialize (H2 H6 H5). ev. exists x. split; try assumption. 
    assert (jj0 ::GH1 ++ jj :: GH0 = (jj0 :: GH1) ++ jj :: GH0) as Eq by apply app_comm_cons.
    unfold open in *. rewrite app_length in *. simpl. rewrite Eq. rewrite splice_open_permute. apply unvv. apply vv in H7. 
    eapply IHn with (GH0 := GH0); try eassumption. 
    simpl in Sz. rewrite <- open_preserves_size. omega.
    apply closed_open. simpl. eapply closed_upgrade_free.
    apply H1. rewrite app_length. omega.
    constructor. simpl. rewrite app_length. omega.
    + apply vv. rewrite val_type_unfold. simpl. ev. inversion V. 
    + apply vv. rewrite val_type_unfold. simpl. ev. inversion V.
    + apply vv. rewrite val_type_unfold. simpl. ev. inversion V.

  - destruct vf. simpl in V. destruct i.
    + ev. apply vv. rewrite val_type_unfold. inversion C. subst.
    split. assumption. split. assumption. intros.
    specialize (H2 _ _ H3).
    assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then
       jj0 vy iy ->
       val_type H (GH1 ++ jj :: GH0) vy (splice (length GH0) T1) iy
      else
       val_type H (GH1 ++ jj :: GH0) vy (splice (length GH0) T1) iy ->
       jj0 vy iy)).
    { intros. destruct (pos iy) eqn : A. intros. specialize (H4 vy iy). rewrite A in H4. specialize (H4 H6).
      apply unvv. apply vv in H4. simpl in *. eapply IHn with (GH0 := GH0); try eassumption; try omega.
      specialize (H4 vy iy). rewrite A in H4. intros. apply H4. apply unvv. apply vv in H6. simpl in *. eapply IHn;
      try eassumption; try omega. }
    specialize (H2 H6 H5). ev. exists x. split; try assumption. apply unvv. apply vv in H7.
    assert (jj0 ::GH1 ++ jj :: GH0 = (jj0 :: GH1) ++ jj :: GH0) as Eq by apply app_comm_cons.
    unfold open in *. rewrite app_length in *. simpl in *. rewrite splice_open_permute in H7. 
    rewrite app_comm_cons. eapply IHn with (GH0 := GH0); try eassumption. simpl in *. rewrite <- open_preserves_size. omega.
    apply closed_open. simpl. eapply closed_upgrade_free. eassumption. rewrite app_length. omega. constructor. simpl. rewrite app_length.
    omega.
    + apply vv. rewrite val_type_unfold. simpl. ev. inversion V.
    + apply vv. rewrite val_type_unfold. simpl. ev. inversion V.
    + simpl in *. apply vv. rewrite val_type_unfold. simpl. inversion V.

  - apply vv. rewrite val_type_unfold. destruct vf. simpl in *. destruct v.
    + assumption. 
    + destruct (indexr i0 (GH1 ++ GH0)) eqn : B; try solve by inversion. 
    destruct (le_lt_dec (length GH0) i0) eqn : A. 
    assert (indexr (i0 + 1) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_high. assumption. omega.
    rewrite H0. apply V. assert (indexr (i0) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_low. assumption. omega.
    rewrite H0. apply V.
    + inversion V.
    + simpl in *. destruct v; simpl; try apply V.
    destruct (indexr i0 (GH1 ++ GH0)) eqn : B; try solve by inversion. 
    destruct (le_lt_dec (length GH0) i0) eqn : A. 
    assert (indexr (i0 + 1) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_high. assumption. omega.
    rewrite H0. apply V. assert (indexr (i0) (GH1 ++ jj :: GH0) = Some v). apply indexr_hit_low. assumption. omega.
    rewrite H0. apply V.

  - apply vv. rewrite val_type_unfold. destruct vf; simpl in *. destruct v.
    + assumption.
    + destruct (le_lt_dec (length GH0) i0) eqn : A. inversion C. subst.  
    eapply indexr_has in H4. ev. assert (indexr (i0 + 1)(GH1 ++ jj:: GH0) = Some x). apply indexr_hit_high; assumption. 
    rewrite H0. rewrite H1 in V. assumption. 
    assert (i0 < length GH0) as H4 by omega. eapply indexr_has in H4. ev. assert (indexr (i0)(GH1 ++ GH0) = Some x).
    apply indexr_extend_mult. assumption. assert (indexr i0 (GH1 ++ jj :: GH0) = Some x). apply indexr_hit_low; assumption. 
    rewrite H1. rewrite H2 in V. assumption.
    + inversion V.
    + destruct v; try solve by inversion; try assumption.
    destruct (le_lt_dec (length GH0) i0) eqn : A. inversion C. subst. 
    eapply indexr_has in H4. ev. assert (indexr (i0 + 1)(GH1 ++ jj:: GH0) = Some x). apply indexr_hit_high; assumption. 
    rewrite H0. rewrite H1 in V. assumption. 
    assert (i0 < length GH0) as H4 by omega. eapply indexr_has in H4. ev. assert (indexr (i0)(GH1 ++ GH0) = Some x).
    apply indexr_extend_mult. assumption. assert (indexr i0 (GH1 ++ jj :: GH0) = Some x). apply indexr_hit_low; assumption. 
    rewrite H1. rewrite H2 in V. assumption.

  - inversion C. subst. apply vv. rewrite val_type_unfold. destruct vf. simpl in *. destruct i. inversion V. 
    ev. split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    apply unvv. eapply IHn with (GH0 := GH0). simpl in *. omega. apply H6. apply vv. assumption.

    ev. split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    apply unvv. eapply IHn with (GH0 := GH0). simpl in *. omega. assumption. apply vv. assumption.

    simpl in *. destruct i. ev.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    intros. specialize (H2 vy iy). destruct (pos iy) eqn : A. intros. assert (val_type H (GH1 ++ GH0) vy T1 iy).
    apply unvv. apply vv in H3. eapply IHn; try eassumption; try omega. specialize (H2 H4). apply vv in H2.
    apply unvv. apply vv in H4. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    intros. assert (val_type H (GH1 ++ GH0) vy T2 iy). apply unvv. apply vv in H3. eapply IHn; try eassumption; try omega. 
    specialize (H2 H4). apply vv in H2. apply unvv. apply vv in H4. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    ev. apply unvv. apply vv in H2. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    split. rewrite app_length. simpl. rewrite E. eapply closed_splice. assumption.
    ev. apply unvv. apply vv in H2. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    
  - inversion C. subst. apply vv. rewrite val_type_unfold. destruct vf. simpl in *. destruct i. inversion V. 
    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.
    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.
    simpl in *. destruct i. 
    split; try assumption. split; try assumption. ev. intros. specialize (H2 vy iy). destruct (pos iy) eqn : A.
    intros. assert (val_type H (GH1 ++ jj :: GH0) vy (splice (length GH0) T1) iy).
    apply unvv. apply vv in H3. eapply IHn with (GH0 := GH0); try eassumption; try omega. 
    specialize (H2 H4). apply vv in H2. apply unvv. eapply IHn; try eassumption; try omega.
    intros. assert (val_type H (GH1 ++ jj :: GH0) vy (splice (length GH0) T2) iy).
    apply unvv. apply vv in H3. eapply IHn with (GH0 := GH0); try eassumption; try omega.
    specialize (H2 H4). apply vv in H2. apply unvv. eapply IHn; try eassumption; try omega.

    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.
    split; try assumption. split; try assumption. ev. apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega.
Qed.



(* used in valtp_widen *)
Lemma valtp_extendH: forall vf H1 GH T1 jj i,
  val_type H1 GH vf T1 i -> 
  vtp H1 (jj::GH) vf T1 i.
Proof.
  intros. assert (jj::GH = ([] ++ jj :: GH)). simpl. reflexivity. rewrite H0.
  assert (splice (length GH) T1 = T1). apply valtp_closed in H. eapply closed_splice_idem. eassumption. omega.
  rewrite <- H2. 
  eapply valtp_splice_aux with (GH0 := GH). eauto. simpl. apply valtp_closed in H. eapply closed_upgrade_free. eassumption. omega.
  simpl. apply vv in H. assumption.
Qed.

Lemma valtp_shrinkH: forall vf H1 GH T1 jj i,
  val_type H1 (jj::GH) vf T1 i ->
  closed 0 (length GH) (length H1) T1 ->                     
  vtp H1 GH vf T1 i.
Proof.
  intros. 
  assert (vtp H1 ([] ++ GH) vf T1 i <-> 
  vtp H1 ([] ++ jj :: GH) vf (splice (length GH) T1) i).
  eapply valtp_splice_aux. eauto. simpl. assumption. 
  apply H2. simpl. assert (splice (length GH) T1 = T1).
  eapply closed_splice_idem. eassumption. omega. apply vv in H.
  rewrite H3. assumption.
Qed.




(* used in invert_abs *)
Lemma vtp_subst1: forall venv jj v T2,
  val_type venv [jj] v (open (varH 0) T2) tp ->
  closed 0 0 (length venv) T2 ->
  val_type venv [] v T2 tp.
Proof.
  intros. assert (open (varH 0) T2 = T2). symmetry. unfold open. 
  eapply closed_no_open. eapply H0. rewrite H1 in H. 
  apply unvv. eapply valtp_shrinkH. simpl. eassumption. assumption.
Qed.


Lemma vtp_subst2_aux: forall n T venv jj v x i GH j k,
  tsize_flat T < n ->
  closed j (length GH) (length venv) T -> k < j ->
  indexr x venv = Some jj ->
  (vtp venv (GH ++ [jj]) v (open_rec k (varH 0) (splice 0 T)) i <->
   vtp venv GH v (open_rec k (varF x) T) i).
Proof. induction n; intros ? ? ? ? ? ? ? ? ? Sz Cz Bd Id. inversion Sz.
  destruct T; split; intros V; apply unvv in V; rewrite val_type_unfold in V.
  - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V.
  - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V.
  - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V.
  - unfold open. simpl in *. apply vv. rewrite val_type_unfold. destruct v; apply V.
  - inversion Cz. subst. 
    unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct v.
    destruct i.
    + ev. split. {rewrite app_length in *.  simpl in *. eapply splice_retreat4. 
    eassumption. constructor. eapply indexr_max. eassumption. }
    split. { rewrite app_length in *. simpl in *. eapply splice_retreat4.
    eassumption. constructor. eapply indexr_max. eassumption. }
    
    intros. specialize (H1 _ _ H2). assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then
       jj0 vy iy ->
       val_type venv0 (GH ++ [jj]) vy (open_rec k (varH 0) (splice 0 T1)) iy
      else
       val_type venv0 (GH ++ [jj]) vy (open_rec k (varH 0) (splice 0 T1)) iy ->
       jj0 vy iy)).
    { intros. destruct (pos  iy) eqn : A. specialize (H3 vy iy). rewrite A in H3. intros. 
      specialize (H3 H7). apply unvv. apply vv in H3. eapply IHn; try eassumption; try omega.
      specialize (H3 vy iy). rewrite A in H3. intros. apply H3. apply unvv. apply vv in H7.
      eapply IHn; try eassumption; try omega. }
    specialize (H1 H7 H6). ev. exists x0. split. assumption. apply unvv. apply vv in H8.
    assert (jj0 :: GH ++ [jj] = (jj0 :: GH) ++ [jj]) as Eq.
    apply app_comm_cons. rewrite Eq in H8.
    unfold open. 
    erewrite open_permute in H8. erewrite open_permute.  
    assert ((open_rec 0 (varH (length (GH ++ [jj]))) (splice 0 T2)) =
             splice 0 (open_rec 0 (varH (length GH)) T2)). {
    rewrite app_length. simpl.
    assert ((length GH) = (length GH) + 0). omega. rewrite H9.
    apply (splice_open_permute0 0 T2 (length GH) 0).
    }
    rewrite H9 in H8.
    eapply IHn with (GH := (jj0::GH)). erewrite <- open_preserves_size. omega.
    assert (closed (S j) (S (length GH)) (length venv0) T2). eapply closed_upgrade_free.
    eassumption. omega. eapply closed_open2. eassumption. constructor. simpl. omega. omega. 
    eapply Id. apply H8. constructor. eauto. constructor. eauto. omega.
    constructor. eauto. constructor. eauto. omega. 
    + assumption.
    + assumption.
    + assumption.
  
  - inversion Cz. subst. 
    unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct v.
    destruct i.
    + ev. split. { rewrite app_length. simpl. eapply splice_retreat5. constructor. omega. 
    eassumption. }
    split. { rewrite app_length. simpl. eapply splice_retreat5. constructor.
    omega. eassumption. }
    intros. specialize (H1 _ _ H2). assert ((forall (vy : vl) (iy : sel),
      if pos iy
      then jj0 vy iy -> val_type venv0 GH vy (open_rec k (varF x) T1) iy
      else val_type venv0 GH vy (open_rec k (varF x) T1) iy -> jj0 vy iy)).
    { intros. destruct (pos  iy) eqn : A. specialize (H3 vy iy). rewrite A in H3. intros. 
      specialize (H3 H7). apply unvv. apply vv in H3. eapply IHn; try eassumption; try omega.
      specialize (H3 vy iy). rewrite A in H3. intros. apply H3. apply unvv. apply vv in H7.
      eapply IHn; try eassumption; try omega. }
    specialize (H1 H7 H6). ev. exists x0. split. assumption. apply unvv. apply vv in H8.
    assert (jj0 :: GH ++ [jj] = (jj0 :: GH) ++ [jj]) as Eq.
    apply app_comm_cons. rewrite Eq. unfold open in *. 
    erewrite open_permute in H8. erewrite open_permute.  
    assert ((open_rec 0 (varH (length (GH ++ [jj]))) (splice 0 T2)) =
             splice 0 (open_rec 0 (varH (length GH)) T2)). {
    rewrite app_length. simpl.
    assert ((length GH) = (length GH) + 0). omega. rewrite H9.
    apply (splice_open_permute0 0 T2 (length GH) 0).
    }
    rewrite H9.
    eapply IHn with (GH := (jj0::GH)). erewrite <- open_preserves_size. omega.
    assert (closed (S j) (S (length GH)) (length venv0) T2). eapply closed_upgrade_free.
    eassumption. omega. eapply closed_open2. eassumption. constructor. simpl. omega. omega. 
    eapply Id. apply H8. constructor. eauto. constructor. eauto. omega.
    constructor. eauto. constructor. eauto. omega. 
    + assumption.
    + assumption.
    + assumption.

  - unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. 
    destruct v; destruct v0; simpl in *; try apply V.
    + assert (indexr (i0 + 1) (GH ++ [jj]) = indexr i0 GH). {
    apply indexr_extend_end. }   
    rewrite H in V. apply V.
    + destruct (beq_nat k i0) eqn : A. 
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). 
    apply indexr_hit01.
    rewrite H in V. rewrite Id. apply V. inversion V.
    + assert (indexr (i0 + 1) (GH ++ [jj]) = indexr i0 GH). apply indexr_extend_end.
    rewrite H in V. apply V.
    + destruct (beq_nat k i0) eqn : A. 
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01.
    rewrite H in V. rewrite Id. apply V. inversion V.

  - unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. 
    destruct v; destruct v0; simpl in *; try apply V.
    assert (indexr (i0 + 1) (GH ++ [jj]) = indexr i0 GH). apply indexr_extend_end.
    rewrite H. apply V.
    destruct (beq_nat k i0) eqn : A. 
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01.
    rewrite H. rewrite Id in V. apply V. inversion V.
    assert (indexr (i0 + 1) (GH ++ [jj]) = indexr i0 GH). apply indexr_extend_end.
    rewrite H. apply V.
    destruct (beq_nat k i0) eqn : A. 
    simpl in *. assert (indexr 0 (GH ++ [jj]) = Some jj). apply indexr_hit01.
    rewrite H. rewrite Id in V. apply V. inversion V.

  - inversion Cz. subst. 
    unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct i. 
    + destruct v; try solve by inversion. ev. rewrite app_length in *. split. { eapply splice_retreat4.
      simpl in *. eassumption. constructor. apply indexr_max in Id. omega. } split. { eapply splice_retreat4.
      simpl in *. eassumption. constructor. apply indexr_max in Id. omega. } 
    intros. specialize (H1 vy iy). destruct (pos iy). intros. assert (
    val_type venv0 (GH ++ [jj]) vy (open_rec k (varH 0) (splice 0 T1)) iy).
    apply vv in H2. apply unvv. eapply IHn; try eassumption; try omega. specialize (H1 H3). apply vv in H1.
    apply unvv. eapply IHn; try eassumption; try omega.
    intros. assert (
    val_type venv0 (GH ++ [jj]) vy (open_rec k (varH 0) (splice 0 T2)) iy).
    apply vv in H2. apply unvv. eapply IHn; try eassumption; try omega. specialize (H1 H3). apply vv in H1.
    apply unvv. eapply IHn; try eassumption; try omega.

    + rewrite app_length in *. destruct v. ev. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. 
    apply vv in H1. apply unvv. eapply IHn; try eassumption; try omega.
    ev. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. 
    apply vv in H1. apply unvv. eapply IHn; try eassumption; try omega.

    + rewrite app_length in *. destruct v. ev. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. 
    apply vv in H1. apply unvv. eapply IHn; try eassumption; try omega.
    ev. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. split. eapply splice_retreat4. eassumption. constructor. eapply indexr_max.
    eassumption. 
    apply vv in H1. apply unvv. eapply IHn; try eassumption; try omega.

  - inversion Cz. subst. 
    unfold open in *. simpl in *. apply vv. rewrite val_type_unfold in *. destruct i. 
    + destruct v; try solve by inversion. ev. rewrite app_length in *. split. { eapply splice_retreat5.
      constructor. omega. eassumption. }
    split. eapply splice_retreat5. constructor. omega. eassumption.
    intros. specialize (H1 vy iy). destruct (pos iy). intros. assert (val_type venv0 GH vy (open_rec k (varF x) T1) iy).
    apply vv in H2. apply unvv. eapply IHn; try eassumption; try omega. specialize (H1 H3). apply vv in H1.
    apply unvv. eapply IHn; try eassumption; try omega.
    intros. assert (val_type venv0 GH vy (open_rec k (varF x) T2) iy).
    apply unvv. apply vv in H2. eapply IHn; try eassumption; try omega. specialize (H1 H3). apply vv in H1.
    apply unvv. eapply IHn; try eassumption; try omega.

    + rewrite app_length. simpl in *. destruct v. ev. split. eapply splice_retreat5. constructor. omega. eassumption.
    split. eapply splice_retreat5. constructor. omega. eassumption.
    apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.
    ev. split. eapply splice_retreat5. constructor. omega. eassumption.
    split. eapply splice_retreat5. constructor. omega. eassumption.
    apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.

    + rewrite app_length. simpl in *. destruct v. ev. split. eapply splice_retreat5. constructor. omega. eassumption.
    split. eapply splice_retreat5. constructor. omega. eassumption.
    apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.
    ev. split. eapply splice_retreat5. constructor. omega. eassumption.
    split. eapply splice_retreat5. constructor. omega. eassumption.
    apply unvv. apply vv in H1. eapply IHn; try eassumption; try omega.

   
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
Qed.  

Lemma vtp_subst: forall T venv jj v x i GH,
  closed 1 (length GH) (length venv) T -> 
  indexr x venv = Some jj ->
  (vtp venv (GH ++ [jj]) v (open (varH 0) (splice 0 T)) i <->
   vtp venv GH v (open (varF x) T) i).
Proof. intros. eapply vtp_subst2_aux. eauto. eassumption. omega. assumption. Qed.


(* used in invert_dabs *)
Lemma vtp_subst2: forall venv jj v x T2,
  closed 1 0 (length venv) T2 ->
  val_type venv [jj] v (open (varH 0) T2) tp ->
  indexr x venv = Some jj ->
  val_type venv [] v (open (varF x) T2) tp.
Proof.
  intros. apply vv in H0. assert ([jj] = ([] ++ [jj])). simpl. reflexivity.
  rewrite H2 in H0. assert (splice 0 T2 = T2). eapply closed_splice_idem.
  eassumption. omega. rewrite <- H3 in H0. eapply vtp_subst in H0. apply unvv. eassumption.
  simpl. assumption. assumption.
Qed.

(* used in vabs case of main theorem *)
Lemma vtp_subst3: forall venv jj v T2,
  closed 1 0 (length venv) T2 ->
  val_type (jj::venv) [] v (open (varF (length venv)) T2) tp ->
  val_type venv [jj] v (open (varH 0) T2) tp.
Proof.
  intros. apply unvv. assert (splice 0 T2 = T2) as EE. eapply closed_splice_idem. eassumption. omega.
  assert (vtp (jj::venv0) ([] ++ [jj]) v (open (varH 0) (splice 0 T2)) tp).
  assert (indexr (length venv0) (jj :: venv0) = Some jj). simpl. 
    replace (beq_nat (length venv0) (length venv0) ) with true. reflexivity. 
    apply beq_nat_refl. 
  eapply vtp_subst. simpl. eapply closed_upgrade_freef. eassumption. omega. eassumption.
  apply vv. assumption. 
  simpl in *. rewrite EE in H1. eapply valtp_shrinkM. apply unvv. eassumption.
  apply closed_open. simpl. eapply closed_upgrade_free. eassumption. omega.
  constructor. simpl. omega.
Qed.


(* ### Inhabited types have `Good Bounds` ### *)

(* used in invert_abs *)
Lemma valtp_bounds: forall G v T1,
  val_type G [] v T1 tp ->
  forall (vy : vl) (iy : sel),
    if pos iy
    then val_type G [] vy T1 (lb iy) -> val_type G [] vy T1 (ub iy)
    else val_type G [] vy T1 (ub iy) -> val_type G [] vy T1 (lb iy).
Proof. 
  intros. induction T1; rewrite val_type_unfold in H; try solve by inversion.

  - destruct (pos iy) eqn : A4. intros. rewrite val_type_unfold. destruct vy; assumption.
    intros. rewrite val_type_unfold in H0. rewrite val_type_unfold. destruct vy; assumption.

  - destruct (pos iy) eqn : A4. intros. rewrite val_type_unfold in H0. apply unvv. destruct vy; inversion H0.
    intros. rewrite val_type_unfold in H0. apply unvv. destruct vy; inversion H0.
    
  - destruct v; try solve by inversion. ev. destruct (pos iy). intros. rewrite val_type_unfold in H2.
    apply unvv. destruct vy; inversion H2. intros. apply unvv. rewrite val_type_unfold in H2.
    destruct vy ; inversion H2.

  - destruct v. 
    + destruct v0; try solve by inversion. 
      destruct (indexr i G) eqn: In; try solve by inversion.
      destruct (pos iy) eqn : A. intros. rewrite val_type_unfold in H0.
      rewrite val_type_unfold. rewrite In in *. admit.
      intros. rewrite val_type_unfold in H0. 
      rewrite val_type_unfold. rewrite In in *. admit.
    + destruct v0; try solve by inversion.
      destruct (indexr i G) eqn : In; try solve by inversion.
      destruct (pos iy) eqn : A. intros. rewrite val_type_unfold in H0.
      rewrite val_type_unfold. rewrite In in *. admit.
      intros. rewrite val_type_unfold in H0. 
      rewrite val_type_unfold. rewrite In in *. admit.
    

  - destruct v; try solve by inversion. ev. specialize (H1 vy iy).
    destruct (pos iy). intros. rewrite val_type_unfold in H2.
    apply unvv. destruct vy. ev. specialize (H1 H4). apply vv. rewrite val_type_unfold. split.
    simpl. assumption. split. assumption. assumption. 
    ev. specialize (H1 H4). apply vv. rewrite val_type_unfold. split; simpl. assumption. split; simpl.
    assumption. assumption.
    intros. rewrite val_type_unfold in H2. apply unvv. destruct vy. 
    ev. specialize (H1 H4). apply vv. rewrite val_type_unfold. split.
    simpl. assumption. split. assumption. assumption. 
    ev. specialize (H1 H4). apply vv. rewrite val_type_unfold. split; simpl. assumption. split; simpl.
    assumption. assumption.

Qed.



(* ### Relating Value Typing and Subtyping ### *)
  
Lemma valtp_widen_aux: forall G1 GH1 T1 T2,
  stp G1 GH1 T1 T2 ->
  forall (H: list vset) GH,
    length G1 = length H ->
    (forall x TX, indexr x G1 = Some TX ->
                   exists vx jj,
                     indexr x H = Some jj /\
                     jj vx tp /\
                     (forall vy iy, if pos iy then jj vy iy -> vtp H GH vy TX iy
                                    else           vtp H GH vy TX iy -> jj vy iy) /\
                     (forall vy iy, if pos iy then jj vy (lb iy) -> jj vy (ub iy) 
                                    else           jj vy (ub iy) -> jj vy (lb iy))) ->
    length GH1 = length GH ->
    (forall x TX, indexr x GH1 = Some TX ->
                   exists vx jj,
                     indexr x GH = Some jj /\
                     jj vx tp /\
                     (forall vy iy, if pos iy then jj vy iy -> vtp H GH vy TX iy
                                    else           vtp H GH vy TX iy -> jj vy iy) /\
                     (forall vy iy, if pos iy then jj vy (lb iy) -> jj vy (ub iy) 
                                    else           jj vy (ub iy) -> jj vy (lb iy))) ->
  (forall vf i, if (pos i) then
     val_type H GH vf T1 i -> vtp H GH vf T2 i
   else
     val_type H GH vf T2 i -> vtp H GH vf T1 i).
Proof.
  intros ? ? ? ? stp. 
  induction stp; intros G GHX LG RG LGHX RGHX vf i; 
  remember (pos i) as p; destruct p; intros V0.
  
  - Case "Top".
    eapply vv. rewrite val_type_unfold. destruct vf; rewrite Heqp; reflexivity.
  - rewrite val_type_unfold in V0. simpl in V0. rewrite <-Heqp in V0. destruct vf; inversion V0. 
  - Case "Bot".
    rewrite val_type_unfold in V0. destruct vf; rewrite <-Heqp in V0; inversion V0.
  - eapply vv. rewrite val_type_unfold. rewrite <-Heqp. destruct vf; reflexivity.
  - Case "mem".
    subst. 
    rewrite val_type_unfold in V0. 
    eapply vv. rewrite val_type_unfold. destruct i.
    + destruct vf. eapply V0. eapply stp_closed1 in stp2. eapply stp_closed2 in stp1.
      rewrite <-LG. rewrite <-LGHX. split; eassumption.
    + simpl in Heqp. specialize (IHstp1 _ _ LG RG LGHX RGHX vf i). rewrite <-Heqp in IHstp1.
      destruct vf; eapply unvv; eapply IHstp1; assumption.
    + simpl in Heqp. assert (false = pos i) as Heqp'. destruct (pos i). inversion Heqp. reflexivity.
    specialize (IHstp2 _ _ LG RG LGHX RGHX vf i). rewrite <-Heqp' in IHstp2.
    destruct vf; eapply unvv; eapply IHstp2; assumption.
  - subst. 
    rewrite val_type_unfold in V0. 
    eapply vv. rewrite val_type_unfold. destruct i.
    + destruct vf. eapply V0. eapply stp_closed2 in stp2. eapply stp_closed1 in stp1.
      rewrite <-LG. rewrite <-LGHX. split; eassumption.
    + simpl in Heqp. specialize (IHstp1 _ _ LG RG LGHX RGHX vf i). rewrite <-Heqp in IHstp1.
      destruct vf; eapply unvv; eapply IHstp1; assumption.
    + simpl in Heqp. assert (true = pos i) as Heqp'. destruct (pos i). reflexivity. inversion Heqp.
    specialize (IHstp2 _ _ LG RG LGHX RGHX vf i). rewrite <-Heqp' in IHstp2.
    destruct vf; eapply unvv; eapply IHstp2; assumption.
  - Case "Sel1".
    subst. 
    rewrite val_type_unfold in V0.
    remember RG as ENV. clear HeqENV.
    specialize (RG _ _ H).
    ev. rewrite H1 in V0.
    assert (x1 vf (ub i)). destruct vf; eauto. clear V0.
    assert (vtp G GHX vf TX (ub i)). specialize (H3 vf (ub i)). simpl in H3. rewrite <-Heqp in H3. eapply H3. assumption.
    assert (vtp G GHX vf (TMem TBot T2) (ub i)).
    specialize (IHstp _ _ LG ENV LGHX RGHX vf (ub i)). simpl in IHstp. rewrite <-Heqp in IHstp.
    eapply IHstp. eapply unvv. assumption.
    
    eapply unvv in H7. rewrite val_type_unfold in H7.
    destruct vf; eapply vv; apply H7.
  - eapply vv. rewrite val_type_unfold.
    remember RG as ENV. clear HeqENV.
    specialize (RG _ _ H).
    ev. rewrite H1.    
    assert (vtp G GHX vf (TMem TBot T2) (ub i)). eapply vv. rewrite val_type_unfold. destruct vf; assumption.
    assert (vtp G GHX vf TX (ub i)).
    specialize (IHstp _ _ LG ENV LGHX RGHX vf (ub i)). simpl in IHstp. rewrite <-Heqp in IHstp. eapply IHstp. eapply unvv. assumption.
    assert (x1 vf (ub i)).
    specialize (H3 vf (ub i)). simpl in H3. rewrite <-Heqp in H3. eapply H3. assumption.
    destruct vf; assumption.
  - Case "Sel2".
    eapply vv. rewrite val_type_unfold.
    remember RG as ENV. clear HeqENV.
    specialize (RG _ _ H).
    ev. rewrite H1.    
    assert (vtp G GHX vf (TMem T1 TTop) (lb i)). eapply vv. rewrite val_type_unfold. destruct vf; assumption.
    assert (vtp G GHX vf TX (lb i)).
    specialize (IHstp _ _ LG ENV LGHX RGHX vf (lb i)). simpl in IHstp. rewrite <-Heqp in IHstp. eapply IHstp. eapply unvv. assumption.
    assert (x1 vf (lb i)).
    specialize (H3 vf (lb i)). simpl in H3. rewrite <-Heqp in H3. eapply H3. assumption.
    assert (x1 vf (ub i)). specialize (H4 vf i). rewrite <-Heqp in H4. eapply H4. assumption.
    destruct vf; assumption.
   - subst. 
    rewrite val_type_unfold in V0.
    remember RG as ENV. clear HeqENV.
    specialize (RG _ _ H).
    ev. rewrite H1 in V0.
    assert (x1 vf (ub i)). destruct vf; eauto. clear V0.
    assert (x1 vf (lb i)). specialize (H4 vf i). rewrite <-Heqp in H4. eapply H4. assumption.
    assert (vtp G GHX vf TX (lb i)). specialize (H3 vf (lb i)). simpl in H3. rewrite <-Heqp in H3. eapply H3. assumption.
    assert (vtp G GHX vf (TMem T1 TTop) (lb i)).
    specialize (IHstp _ _ LG ENV LGHX RGHX vf (lb i)). simpl in IHstp. rewrite <-Heqp in IHstp.
    eapply IHstp. eapply unvv. assumption.
    
    eapply unvv in H8. rewrite val_type_unfold in H8.
    destruct vf; eapply vv; apply H8.
    
  - Case "selx".
    eapply vv. eapply V0.
  - eapply vv. eapply V0.

  (* exactly the same as sel1/sel2, modulo RG/RGHX *)
  - Case "Sel1".
    subst. 
    rewrite val_type_unfold in V0.
    remember RGHX as ENV. clear HeqENV.
    specialize (RGHX _ _ H).
    ev. rewrite H1 in V0.
    assert (x1 vf (ub i)). destruct vf; eauto. clear V0.
    assert (vtp G GHX vf TX (ub i)). specialize (H3 vf (ub i)). simpl in H3. rewrite <-Heqp in H3. eapply H3. assumption.
    assert (vtp G GHX vf (TMem TBot T2) (ub i)).
    specialize (IHstp _ _ LG RG LGHX ENV vf (ub i)). simpl in IHstp. rewrite <-Heqp in IHstp.
    eapply IHstp. eapply unvv. assumption.
    
    eapply unvv in H7. rewrite val_type_unfold in H7.
    destruct vf; eapply vv; apply H7.
  - eapply vv. rewrite val_type_unfold.
    remember RGHX as ENV. clear HeqENV.
    specialize (RGHX _ _ H).
    ev. rewrite H1.    
    assert (vtp G GHX vf (TMem TBot T2) (ub i)). eapply vv. rewrite val_type_unfold. destruct vf; assumption.
    assert (vtp G GHX vf TX (ub i)).
    specialize (IHstp _ _ LG RG LGHX ENV vf (ub i)). simpl in IHstp. rewrite <-Heqp in IHstp. eapply IHstp. eapply unvv. assumption.
    assert (x1 vf (ub i)).
    specialize (H3 vf (ub i)). simpl in H3. rewrite <-Heqp in H3. eapply H3. assumption.
    destruct vf; assumption.
  - Case "Sel2".
    eapply vv. rewrite val_type_unfold.
    remember RGHX as ENV. clear HeqENV.
    specialize (RGHX _ _ H).
    ev. rewrite H1.    
    assert (vtp G GHX vf (TMem T1 TTop) (lb i)). eapply vv. rewrite val_type_unfold. destruct vf; assumption.
    assert (vtp G GHX vf TX (lb i)).
    specialize (IHstp _ _ LG RG LGHX ENV vf (lb i)). simpl in IHstp. rewrite <-Heqp in IHstp. eapply IHstp. eapply unvv. assumption.
    assert (x1 vf (lb i)).
    specialize (H3 vf (lb i)). simpl in H3. rewrite <-Heqp in H3. eapply H3. assumption.
    assert (x1 vf (ub i)). specialize (H4 vf i). rewrite <-Heqp in H4. eapply H4. assumption.
    destruct vf; assumption.
   - subst. 
    rewrite val_type_unfold in V0.
    remember RGHX as ENV. clear HeqENV.
    specialize (RGHX _ _ H).
    ev. rewrite H1 in V0.
    assert (x1 vf (ub i)). destruct vf; eauto. clear V0.
    assert (x1 vf (lb i)). specialize (H4 vf i). rewrite <-Heqp in H4. eapply H4. assumption.
    assert (vtp G GHX vf TX (lb i)). specialize (H3 vf (lb i)). simpl in H3. rewrite <-Heqp in H3. eapply H3. assumption.
    assert (vtp G GHX vf (TMem T1 TTop) (lb i)).
    specialize (IHstp _ _ LG RG LGHX ENV vf (lb i)). simpl in IHstp. rewrite <-Heqp in IHstp.
    eapply IHstp. eapply unvv. assumption.
    
    eapply unvv in H8. rewrite val_type_unfold in H8.
    destruct vf; eapply vv; apply H8.


    
  - Case "selax".
    eapply vv. eapply V0.
  - eapply vv. eapply V0.

  - Case "Fun".
    subst. 
    rewrite val_type_unfold in V0.
    assert (val_type G GHX vf (TAll T3 T4) i). rewrite val_type_unfold.
    subst. destruct vf; destruct i; try solve [inversion V0].
    destruct V0 as [? [? LR]].
    assert (closed 0 (length GHX) (length G) T3). rewrite <-LG. rewrite <-LGHX. eapply stp_closed in stp1. eapply stp1.
    assert (closed 1 (length GHX) (length G) T4). rewrite <-LG. rewrite <-LGHX. eapply H1.
    split. eauto. split. eauto. 
    intros vx jj VST0 STJ STB. 

    specialize (IHstp1 _ _ LG RG LGHX RGHX).
    
    assert (val_type G GHX vx T3 tp) as VX0. {
      specialize (STJ vx tp). simpl in STJ. eapply STJ. eapply VST0. }
    assert (vtp G GHX vx T1 tp) as VX1. {
      specialize (IHstp1 vx tp). simpl in IHstp1. eapply IHstp1. eapply VX0. }

    assert (forall (vy : vl) iy, 
              if pos iy then jj vy iy -> val_type G GHX vy T1 iy
              else val_type G GHX vy T1 iy -> jj vy iy) as STJ1.
    { intros vy iy. specialize (STJ vy iy).
      remember (pos iy) as p. destruct p.
      specialize (IHstp1 vy iy). rewrite <-Heqp0 in IHstp1.
      intros. eapply unvv. eapply IHstp1. eapply STJ. assumption.
      specialize (IHstp1 vy iy). rewrite <-Heqp0 in IHstp1.
      intros. eapply STJ. eapply unvv. eapply IHstp1. assumption. }
    eapply unvv in VX1. 
    destruct (LR vx jj VST0 STJ1 STB) as [v [TE VT]]. 

    exists v. split. eapply TE. eapply unvv.

    (* now deal with function result! *)
    rewrite <-LGHX. rewrite <-LGHX in VT.

    (* broaden goal so that we can apply stp2 *)
    assert (if pos tp then
      val_type G (jj :: GHX) v (open (varH (length GH)) T2) tp ->
      vtp G (jj :: GHX) v (open (varH (length GH)) T4) tp
    else 
      val_type G (jj :: GHX) v (open (varH (length GH)) T4) tp ->
      vtp G (jj :: GHX) v (open (varH (length GH)) T2) tp) as ST2. {
    
    eapply IHstp2. eapply LG.

    (* extend RG *)
    intros ? ? IX. destruct (RG _ _ IX) as [vx0 [jj0 [IX1 [VJ0 [FA FAB]]]]].
    assert (vtp G GHX vx0 TX tp). specialize (FA vx0 tp). simpl in FA. eapply FA. assumption.
    assert (closed 0 (length GHX) (length G) TX). eapply valtp_closed. eapply unvv. eassumption.
    exists vx0. exists jj0. split. eapply IX1. split. assumption. split.
    (* jj -> val_type *) intros.
    remember FA as FA'. clear HeqFA'. specialize (FA' vy iy).
    remember (pos iy) as p. destruct p. 
    intros. eapply valtp_extendH. eapply unvv. eapply FA'. assumption.
    intros. eapply FA'. eapply valtp_shrinkH. eapply unvv. eassumption. assumption.
    (* jj lb -> jj ub *) apply FAB. 
    
    (* extend LGHX *)
    simpl. rewrite LGHX. reflexivity.

    (* extend RGHX *)
    intros ? ? IX.
    { case_eq (beq_nat x (length GHX)); intros E.
      + simpl in IX. rewrite LGHX in IX. rewrite E in IX. inversion IX. subst TX.
        exists vx. exists jj. split. simpl. rewrite E. reflexivity.
        split. assumption. split.
        intros. specialize (STJ vy iy). remember (pos iy) as p. destruct p; intros.  
        eapply valtp_extendH. eapply STJ. assumption.
        eapply STJ. eapply unvv. eapply valtp_shrinkH. eapply unvv. eassumption.
        assumption. assumption.
      + assert (indexr x GH = Some TX) as IX0.
        simpl in IX. rewrite LGHX in IX. rewrite E in IX. inversion IX. reflexivity.
        specialize (RGHX _ _ IX0). ev.
        assert (vtp G GHX x0 TX tp). specialize (H7 x0 tp). simpl in H7. eapply H7. assumption.
        exists x0. exists x1. split. simpl. rewrite E. eapply H5. split. assumption. split. 
        intros. specialize (H7 vy iy). remember (pos iy) as p. destruct p; intros.  
        eapply valtp_extendH. eapply unvv. eapply H7. assumption.
        eapply H7. eapply valtp_shrinkH. eapply unvv. eassumption.
        eapply valtp_closed. eapply unvv. eassumption.
        assumption.
    }

    }
    simpl in ST2. eapply ST2. eapply VT. 

    assumption.
    assumption.
    assumption.
    assumption.
    assumption.
    eapply vv. eapply H.

  - rewrite val_type_unfold in V0. rewrite <-Heqp in V0.
    destruct vf; destruct i; inversion V0; inversion H2;
    simpl in Heqp; inversion Heqp.
      
  - Case "trans".
    specialize (IHstp1 _ _ LG RG LGHX RGHX vf i).
    specialize (IHstp2 _ _ LG RG LGHX RGHX vf i).
    rewrite <-Heqp in *.
    eapply IHstp2. eapply unvv. eapply IHstp1. eapply V0.
  - specialize (IHstp1 _ _ LG RG LGHX RGHX vf i).
    specialize (IHstp2 _ _ LG RG LGHX RGHX vf i).
    rewrite <-Heqp in *.
    eapply IHstp1. eapply unvv. eapply IHstp2. eapply V0.
Qed.


Lemma valtp_widen: forall vf GH H G1 T1 T2,
  val_type GH [] vf T1 tp ->
  stp G1 [] T1 T2 ->
  R_env H GH G1 ->
  vtp GH [] vf T2 tp.
Proof.
  intros.
  assert (forall (vf0 : vl) (i : sel),
    if pos i
    then val_type GH [] vf0 T1 i -> vtp GH [] vf0 T2 i
    else val_type GH [] vf0 T2 i -> vtp GH [] vf0 T1 i).
  eapply valtp_widen_aux. eassumption. destruct H2 as [L1 [L2 ?]]. omega.
  { intros. destruct H2 as [L1 [L2 A]]. specialize (A _ _ H3). ev.
    eexists. eexists. repeat split; eassumption.  }
  reflexivity.
  { intros. simpl in H3. inversion H3. }
  specialize (H3 vf tp). simpl in H3. eapply H3. assumption.
Qed.

(* --- up to here --- *)

Lemma wf_env_extend: forall vx jj G1 R1 H1 T1,
  R_env H1 R1 G1 ->
  val_type (jj::R1) [] vx T1 tp ->
  jj vx tp -> (* redundant? *)
  (forall vy iy, if pos iy then jj vy iy -> vtp (jj::R1) [] vy T1 iy
                 else           vtp (jj::R1) [] vy T1 iy -> jj vy iy) ->
  (forall vy iy, if pos iy then jj vy (lb iy) -> jj vy (ub iy) 
                 else           jj vy (ub iy) -> jj vy (lb iy)) ->
  R_env (vx::H1) (jj::R1) (T1::G1).
Proof.
  intros. unfold R_env in *. destruct H as [L1 [L2 U]].
  split. simpl. rewrite L1. reflexivity.
  split. simpl. rewrite L2. reflexivity.
  intros. simpl in H. case_eq (beq_nat x (length G1)); intros E; rewrite E in H.
  - inversion H. subst T1. split. exists vx. unfold R. split.
    exists 0. intros. destruct n. omega. simpl. rewrite <-L1 in E. rewrite E. reflexivity.
    assumption. exists vx. exists jj.
    split. simpl. rewrite <-L1 in E. rewrite E. reflexivity.
    split. simpl. rewrite <-L2 in E. rewrite E. reflexivity.
    split. assumption. split. assumption. assumption.
  - destruct (U x TX H) as [[vy [EV VY]] IR]. split.
    exists vy. split.
    destruct EV as [n EV]. assert (S n > n) as N. omega. specialize (EV (S n) N). simpl in EV.
    exists n. intros. destruct n0. omega. simpl. rewrite <-L1 in E. rewrite E. assumption.
    eapply unvv. eapply valtp_extend. assumption.
    ev. exists x0. exists x1. 
    split. simpl. rewrite <-L1 in E. rewrite E. assumption.
    split. simpl. rewrite <-L2 in E. rewrite E. assumption.
    split. assumption. split.
    intros. specialize (H8 vy0 iy). remember (pos iy) as p. destruct p.
    intros. eapply valtp_extend. eapply unvv. eapply H8. assumption.
    intros. eapply H8. eapply valtp_shrink. eapply unvv. eassumption.
    eapply valtp_closed in VY. eapply VY.
    assumption.
Qed.

Lemma wf_env_extend0: forall vx (jj:vset) G1 R1 H1 T1,
  R_env H1 R1 G1 ->
  jj vx tp -> 
  (forall vy iy, if pos iy then jj vy iy -> vtp R1 [] vy T1 iy
                 else           vtp R1 [] vy T1 iy -> jj vy iy) ->
  (forall vy iy, if pos iy then jj vy (lb iy) -> jj vy (ub iy) 
                 else           jj vy (ub iy) -> jj vy (lb iy)) ->
  R_env (vx::H1) (jj::R1) (T1::G1).
Proof.
  intros.
  assert (val_type R1 [] vx T1 tp) as V0.
  specialize (H2 vx tp). simpl in H2. eapply unvv. eapply H2. assumption.
  eapply wf_env_extend. assumption. eapply unvv. eapply valtp_extend. eapply V0.
  assumption.
  intros. specialize (H2 vy iy). remember (pos iy) as p. destruct p.
  intros. eapply valtp_extend. eapply unvv. eapply H2. assumption.
  intros. eapply H2. eapply valtp_shrink. eapply unvv. eassumption.
  eapply unvv in H4. eapply valtp_closed in V0. apply V0.
  assumption.
Qed.

(*
Lemma restp_widen: forall vf H1 H2 T1 T2,
  res_type H1 vf T1 ->
  stpd2 true true H1 T1 H2 T2 [] ->
  res_type H2 vf T2.
Proof.
  intros. inversion H. eapply not_stuck. eapply unvv. eapply valtp_widen; eauto.
Qed.
*)



(* ### Inversion Lemmas ### *)

Lemma invert_abs: forall venv vf T1 T2,
  val_type venv [] vf (TAll T1 T2) tp ->
  exists env TX y,
    vf = (vabs env TX y) /\ 
    (closed 0 0 (length venv) T2 -> forall vx : vl,
       val_type venv [] vx T1 tp ->
       exists v : vl, tevaln (vx::env) y v /\ val_type venv [] v T2 tp).
Proof.
  intros. 
  rewrite val_type_unfold in H.   
  destruct vf; try solve [inversion H].
  ev. exists l. exists t. exists t0. split. eauto.
  intros C. simpl in H1.

  intros. 
  
  assert (exists (jj:vset),
            jj vx tp /\
            (forall vy iy, if pos iy then jj vy iy -> val_type venv0 [] vy T1 iy
                           else           val_type venv0 [] vy T1 iy -> jj vy iy) /\
            (forall vy iy, if pos iy then jj vy (lb iy) -> jj vy (ub iy)
                           else           jj vy (ub iy) -> jj vy (lb iy))) as A. {
    exists (fun vy iy => val_type venv0 [] vy T1 iy). split.
    assumption. split.
    intros. destruct (pos iy); intros; assumption.
    eapply valtp_bounds. eapply H2. }
                                                                                 
  ev.
  specialize (H1 vx x H3 H4 H5). 
  ev.
  exists x0.
  split. eapply H1.

  eapply vtp_subst1. eapply H6. eapply C.

  inversion H. destruct H1. reflexivity.
Qed.


Lemma invert_dabs: forall venv vf T1 T2 x jj,
  val_type venv [] vf (TAll T1 T2) tp ->
  indexr x venv = Some jj ->
  (forall vy iy, if pos iy then jj vy iy -> val_type venv [] vy T1 iy
                 else           val_type venv [] vy T1 iy -> jj vy iy) ->
  (forall vy iy, if pos iy then jj vy (lb iy) -> jj vy (ub iy)
                 else           jj vy (ub iy) -> jj vy (lb iy)) ->
  exists env TX y,
    vf = (vabs env TX y) /\
    forall vx : vl,
       jj vx tp ->
       exists v : vl, tevaln (vx::env) y v /\ val_type venv [] v (open (varF x) T2) tp.
Proof.
  intros. 
  rewrite val_type_unfold in H.   
  destruct vf; try solve [inversion H].
  ev. exists l. exists t. exists t0. split. eauto.
  simpl in H1.

  intros. 
  
  specialize (H4 vx jj H5 H1 H2). 
  ev.
  exists x0.
  split. eapply H4.

  eapply vtp_subst2. simpl in *. eassumption. eassumption. eapply H0.

  inversion H. destruct H4. reflexivity.
Qed.



(* final type safety + termination proof *)


Theorem full_total_safety : forall e tenv T,
  has_type tenv e T -> forall venv renv, R_env venv renv tenv ->
  exists v, tevaln venv e v /\ val_type renv [] v T tp.
Proof.
  intros ? ? ? W.
  induction W; intros ? ? WFE.

  - Case "Var". 
    destruct (indexr_safe_ex venv0 renv env T1 x) as [v IV]. eauto. eauto. 
    inversion IV as [I V]. 

    exists v. split. exists 0. intros. destruct n. omega. simpl. rewrite I. eauto. eapply V.

  - Case "Typ".
    repeat eexists. intros. destruct n. inversion H0. simpl. eauto.
    rewrite <-(wf_length2 venv0 renv) in H.
    rewrite val_type_unfold. simpl. split; eapply H.
    (* NOTE: may need to change vty/TMem case *)
    (* assert (stpd2 false false venv0 T1 venv0 T1 []). eapply stpd2_wrapf. eapply stp2_refl. eapply H. eu. exists x. exists x. split; eauto. *)
    eapply WFE.
    
  - Case "App".
    rewrite <-(wf_length2 _ _ _ WFE) in H. 
    destruct (IHW1 venv0 renv WFE) as [vf [IW1 HVF]].
    destruct (IHW2 venv0 renv WFE) as [vx [IW2 HVX]].
    
    eapply invert_abs in HVF.
    destruct HVF as [venv1 [TX [y [HF IHF]]]].

    destruct (IHF H vx HVX) as [vy [IW3 HVY]].

    exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWF. subst vf. rewrite IWX. rewrite IWY. eauto.
      omega. omega. omega.
    }
    eapply HVY.

  - Case "DApp".
    rewrite <-(wf_length2 _ _ _ WFE) in H0. 
    destruct (IHW1 venv0 renv WFE) as [vf [IW1 HVF]].
    destruct (IHW2 venv0 renv WFE) as [vx [IW2 HVX]].

    (* TODO: extract this into a lemma? *)
    assert (exists vx jj,
              indexr x venv0 = Some vx /\
              indexr x renv = Some jj /\
              jj vx tp /\
              (forall vy iy, if pos iy then jj vy iy -> vtp renv [] vy T1 iy
                             else           vtp renv [] vy T1 iy -> jj vy iy) /\
              (forall vy iy, if pos iy then jj vy (lb iy) -> jj vy (ub iy)
                             else           jj vy (ub iy) -> jj vy (lb iy))) as B.
    { unfold R_env in WFE. ev. remember (tvar x) as E. clear W1 IHW1 IHW2 HVF HVX IW1 IW2. induction W2; inversion HeqE; try subst x0.
    + destruct (H3 _ _ H4). assumption.
    + specialize (IHW2 H5 H1 H2 H3). ev.
      eexists. eexists. split. eassumption. split. eassumption. split. assumption. split.
      assert (forall vy iy, if pos iy then val_type renv [] vy T1 iy -> vtp renv [] vy T0 iy
                            else           val_type renv [] vy T0 iy -> vtp renv [] vy T1 iy) as A.
      eapply valtp_widen_aux. eassumption. omega.
      intros. specialize (H3 _ _ H11). destruct H3. ev. eexists. eexists. repeat split; eassumption. auto.
      intros. inversion H11.
      intros. specialize (A vy iy). specialize (H9 vy iy). destruct (pos iy).
      intros. eapply A. eapply unvv. eapply H9. assumption.
      intros. eapply H9. eapply A. eapply unvv. assumption.
      assumption. }

    ev. 
    eapply invert_dabs in HVF.
    destruct HVF as [venv1 [TX [y [HF IHF]]]].

    (* shouldn't be needed *)
    assert (x0 = vx). { destruct IW2. assert (S x2 > x2) as SS. omega. specialize (H6 (S x2) SS). simpl in H6. inversion H6. rewrite H8 in H1. inversion H1. reflexivity. }
    subst x0.                      
                      
    destruct (IHF vx H3) as [vy [IW3 HVY]].

    exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWF. subst vf. rewrite IWX. rewrite IWY. reflexivity.
      omega. omega. omega.
    }
    subst T. eapply HVY. eapply H2. intros. specialize (H4 vy iy). destruct (pos iy).
    intros. eapply unvv. eapply H4. assumption.
    intros. eapply H4. eapply vv. assumption.
    assumption.
    
  - Case "Abs".
    rewrite <-(wf_length2 _ _ _ WFE) in H.
    inversion H; subst. 
    eexists. split. exists 0. intros. destruct n. omega. simpl. eauto.
    rewrite val_type_unfold. repeat split; eauto.
    intros.
    assert (R_env (vx::venv0) (jj::renv) (T1::env)) as WFE1. {
      eapply wf_env_extend0. eapply WFE. eapply H0.
      intros. specialize (H1 vy iy). destruct (pos iy).
      intros. eapply vv. eapply H1. assumption.
      intros. eapply H1. eapply unvv. assumption.
      assumption. }
    specialize (IHW (vx::venv0) (jj::renv) WFE1).
    destruct IHW as [v [EV VT]]. rewrite <-(wf_length2 _ _ _ WFE) in VT. 
    exists v. split. eapply EV. 
    eapply vtp_subst3. assumption. eapply VT. 

  - Case "Sub".
    specialize (IHW venv0 renv WFE). ev. eexists. split. eassumption.
    eapply unvv. eapply valtp_widen. eapply H1. eapply H. eapply WFE. 

Grab Existential Variables.
  apply 0. 
Qed.