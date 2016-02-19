(*
FSub (F<:)
T ::= Top | X | T -> T | Forall Z <: T. T^Z
t ::= x | lambda x:T.t | Lambda X<:T.t | t t | t [T]
*)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

(* ### Syntax ### *)

Definition id := nat.

Inductive ty : Type :=
| TTop : ty
| TFun : ty -> ty -> ty
| TAll : ty -> ty -> ty
| TVarF : id -> ty (* free type variable, in concrete environment *)
| TVarH : id -> ty (* free type variable, in abstract environment  *)
| TVarB : id -> ty (* locally-bound type variable *)
(* For uniformity, we use TMem to mark type variables in the environment. *)
(* The advantage is that we don't need to represent two kinds of bindings
   x: T, X <: T
   in environments, but instead just
   x: T, X: TMem T
*)
| TMem : ty -> ty  (* Z <: T *)
.

Inductive tm : Type :=
| tvar : id -> tm
| tabs : id -> ty -> tm -> tm
| tapp : tm -> tm -> tm
| ttabs : id -> ty -> tm -> tm
| ttapp : tm -> ty -> tm
.

Inductive vl : Type :=
(* a closure for a term abstraction *)
| vabs : list (id*vl) (*H*) -> id -> ty -> tm -> vl
(* a closure for a type abstraction *)
| vtabs : list (id*vl) (*H*) -> id -> ty -> tm -> vl
(* For uniformity, we represent a type closing over H here as well,
   because such types can be bound in H during type application.
   They represent a type variable binding in the runtime environment,
   corresponding to TMem in the static environment.
*)
| vty : list (id*vl) (*H*) -> ty -> vl
.

Definition tenv := list (id*ty). (* Gamma environment: static *)
Definition venv := list (id*vl). (* H environment: run-time *)
Definition aenv := list (id*(venv*ty)). (* J environment: abstract at run-time *)

(* ### Representation of Bindings ### *)

(* An environment is a list of strictly decreasing ids. *)

Fixpoint fresh {X: Type} (l : list (id * X)): nat :=
  match l with
    | [] => 0
    | (n',a)::l' => 1 + n'
  end.

Fixpoint index {X : Type} (n : id) (l : list (id * X)) : option X :=
  match l with
    | [] => None
    | (n',a) :: l'  =>
      if le_lt_dec (fresh l') n' then
        if (beq_nat n n') then Some a else index n l'
      else None
  end.

(* An indexr'ed environment of size n is a list of strictly decrementing ids,
   from n-1 to 0.
   In this case, we don't even look at the id LHS in the environment,
   but just rely on the list structures.
   Such rigid environments are used for 'abstract' environments, which the
   meta-theory fully controls and where there is no need for user-visible
   flexibility in using ids.
*)
Fixpoint indexr {X : Type} (n : id) (l : list (id * X)) : option X :=
  match l with
    | [] => None
    | (n',a) :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.


(* closed and open define a locally-nameless encoding wrt to TVarB type variables. *)
Inductive closed_rec: nat -> nat -> ty -> Prop :=
| cl_top: forall k l,
    closed_rec k l TTop
| cl_fun: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TFun T1 T2)
| cl_all: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec (S k) l T2 ->
    closed_rec k l (TAll T1 T2)
| cl_sel: forall k l x,
    closed_rec k l (TVarF x)
| cl_selh: forall k l x,
    l > x ->
    closed_rec k l (TVarH x)
| cl_selb: forall k l i,
    k > i ->
    closed_rec k l (TVarB i)
| cl_mem: forall k l T,
    closed_rec k l T ->
    closed_rec k l (TMem T)
.

Definition closed j l T := closed_rec j l T.

(* substitute type u for all occurrences of (TVarB k) *)
Fixpoint open_rec (k: nat) (u: ty) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TFun T1 T2  => TFun (open_rec k u T1) (open_rec k u T2)
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TVarF x => TVarF x
    | TVarH i => TVarH i
    | TVarB i => if beq_nat k i then u else TVarB i
    | TMem T0  => TMem (open_rec k u T0)
  end.

Definition open u T := open_rec 0 u T.

Fixpoint open_tm_rec (k: nat) (u: ty) (t: tm) { struct t }: tm :=
  match t with
    | tvar x => tvar x
    | tabs x T t => tabs x (open_rec k u T) (open_tm_rec (S k) u t)
    | tapp t1 t2 => tapp (open_tm_rec k u t1) (open_tm_rec k u t2)
    | ttabs x T t => ttabs x (open_rec k u T) (open_tm_rec (S k) u t)
    | ttapp t1 T2 => ttapp (open_tm_rec k u t1) (open_rec k u T2)
  end.

Definition open_tm u t := open_tm_rec 0 u t.

(* Locally-nameless encoding with respect to varH variables. *)
Fixpoint subst (U : ty) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TFun T1 T2   => TFun (subst U T1) (subst U T2)
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TVarB i      => TVarB i
    | TVarF i      => TVarF i
    | TVarH i      => if beq_nat i 0 then U else TVarH (i-1)
    | TMem T0      => TMem (subst U T0)
  end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TFun T1 T2   => nosubst T1 /\ nosubst T2
    | TAll T1 T2   => nosubst T1 /\ nosubst T2
    | TVarB i      => True
    | TVarF i      => True
    | TVarH i      => i <> 0
    | TMem T0      => nosubst T0
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
| stp_topx: forall G1 GH,
    stp G1 GH TTop TTop
| stp_top: forall G1 GH T1,
    stp G1 GH T1 T1 -> (* regularity *)
    stp G1 GH T1 TTop
| stp_fun: forall G1 GH T1 T2 T3 T4,
    stp G1 GH T3 T1 ->
    stp G1 GH T2 T4 ->
    stp G1 GH (TFun T1 T2) (TFun T3 T4)
| stp_mem: forall G1 GH T1 T2,
    stp G1 GH T1 T2 ->
    stp G1 GH (TMem T1) (TMem T2)
| stp_sel1: forall G1 GH T T2 x,
    index x G1 = Some (TMem T) ->
    closed 0 0 T ->
    stp G1 GH T T2 ->
    stp G1 GH (TVarF x) T2
| stp_selx: forall G1 GH T x,
    index x G1 = Some (TMem T) ->
    stp G1 GH (TVarF x) (TVarF x)
| stp_sela1: forall G1 GH T T2 x,
    indexr x GH = Some (TMem T) ->
    closed 0 x T ->
    stp G1 GH T T2 ->
    stp G1 GH (TVarH x) T2
| stp_selax: forall G1 GH T x,
    indexr x GH = Some (TMem T)  ->
    stp G1 GH (TVarH x) (TVarH x)
| stp_all: forall G1 GH T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) T2 -> (* must not accidentally bind x *)
    closed 1 (length GH) T4 ->
    stp G1 ((0,TMem T1)::GH) (open (TVarH x) T2) (open (TVarH x) T2) -> (* regularity *)
    stp G1 ((0,TMem T3)::GH) (open (TVarH x) T2) (open (TVarH x) T4) ->
    stp G1 GH (TAll T1 T2) (TAll T3 T4)
.

(* ### Type Assignment ### *)
Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x env T1,
           index x env = Some T1 ->
           stp env [] T1 T1 ->
           has_type env (tvar x) T1
| t_app: forall env f x T1 T2,
           has_type env f (TFun T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
| t_abs: forall env x y T1 T2,
           has_type ((x,T1)::env) (open_tm (TVarF x) y) T2 ->
           stp env [] (TFun T1 T2) (TFun T1 T2) ->
           fresh env <= x ->
           has_type env (tabs x T1 y) (TFun T1 T2)
| t_tapp: forall env f T11 T12 T,
           has_type env f (TAll T11 T12) ->
           T = open T11 T12 ->
           has_type env (ttapp f T11) T
| t_tabs: forall env x y T1 T2,
           has_type ((x,TMem T1)::env) (open_tm (TVarF x) y) (open (TVarF x) T2) ->
           stp env [] (TAll T1 T2) (TAll T1 T2) ->
           fresh env <= x ->
           has_type env (ttabs x T1 y) (TAll T1 T2)
| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2
.

(* ### Runtime Subtyping ### *)
(* H1 T1 <: H2 T2 -| J *)
Inductive stp2: venv -> ty -> venv -> ty -> aenv  -> Prop :=
| stp2_topx: forall G1 G2 GH,
    stp2 G1 TTop G2 TTop GH
| stp2_top: forall G1 G2 GH T,
    stp2 G1 T G1 T GH -> (* regularity *)
    stp2 G1 T G2 TTop GH
| stp2_fun: forall G1 G2 T1 T2 T3 T4 GH,
    stp2 G2 T3 G1 T1 GH ->
    stp2 G1 T2 G2 T4 GH ->
    stp2 G1 (TFun T1 T2) G2 (TFun T3 T4) GH
| stp2_mem: forall G1 G2 T1 T2 GH,
    stp2 G1 T1 G2 T2 GH ->
    stp2 G1 (TMem T1) G2 (TMem T2) GH

(* concrete type variables *)
(* vty already marks binding as type binding, so need for additional TMem marker *)
| stp2_sel1: forall G1 G2 GX TX x T2 GH,
    index x G1 = Some (vty GX TX) ->
    closed 0 0 TX ->
    stp2 GX TX G2 T2 GH ->
    stp2 G1 (TVarF x) G2 T2 GH
| stp2_sel2: forall G1 G2 GX TX x T1 GH,
    index x G2 = Some (vty GX TX) ->
    closed 0 0 TX ->
    stp2 G1 T1 GX TX GH ->
    stp2 G1 T1 G2 (TVarF x) GH
| stp2_selx: forall G1 G2 v x1 x2 GH,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 G1 (TVarF x1) G2 (TVarF x2) GH

(* abstract type variables *)
(* X<:T, one sided *)
| stp2_sela1: forall G1 G2 GX TX x T2 GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 x TX ->
    stp2 GX TX G2 T2 GH ->
    stp2 G1 (TVarH x) G2 T2 GH
| stp2_selax: forall G1 G2 v x GH,
    indexr x GH = Some v ->
    stp2 G1 (TVarH x) G2 (TVarH x) GH

| stp2_all: forall G1 G2 T1 T2 T3 T4 x GH,
    stp2 G2 T3 G1 T1 GH ->
    x = length GH ->
    closed 1 (length GH) T2 -> (* must not accidentally bind x *)
    closed 1 (length GH) T4 ->
    stp2 G1 (open (TVarH x) T2) G1 (open (TVarH x) T2) ((0,(G1, T1))::GH) -> (* regularity *)
    stp2 G1 (open (TVarH x) T2) G2 (open (TVarH x) T4) ((0,(G2, T3))::GH) ->
    stp2 G1 (TAll T1 T2) G2 (TAll T3 T4) GH
.

(* consistent environment *)
Inductive wf_env : venv -> tenv -> Prop :=
| wfe_nil : wf_env nil nil
| wfe_cons : forall n v t vs ts,
    val_type ((n,v)::vs) v t ->
    wf_env vs ts ->
    wf_env (cons (n,v) vs) (cons (n,t) ts)

(* value type assignment *)
with val_type : venv -> vl -> ty -> Prop :=
| v_ty: forall env venv tenv T1 TE,
    wf_env venv tenv ->
    stp2 venv (TMem T1) env TE [] ->
    val_type env (vty venv T1) TE
| v_abs: forall env venv tenv x y T1 T2 TE,
    wf_env venv tenv ->
    has_type ((x,T1)::tenv) (open_tm (TVarF x) y) T2 ->
    fresh venv <= x ->
    stp2 venv (TFun T1 T2) env TE [] ->
    val_type env (vabs venv x T1 y) TE
| v_tabs: forall env venv tenv x y T1 T2 TE,
    wf_env venv tenv ->
    has_type ((x,TMem T1)::tenv) (open_tm (TVarF x) y) (open (TVarF x) T2) ->
    fresh venv <= x ->
    stp2 venv (TAll T1 T2) env TE [] ->
    val_type env (vtabs venv x T1 y) TE
.

Inductive wf_envh : venv -> aenv -> tenv -> Prop :=
| wfeh_nil : forall vvs, wf_envh vvs nil nil
| wfeh_cons : forall n t vs vvs ts,
    wf_envh vvs vs ts ->
    wf_envh vvs (cons (n,(vvs,t)) vs) (cons (n,TMem t) ts)
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
        | tvar x     => Some (index x env)
        | tabs x T y => Some (Some (vabs env x T y))
        | ttabs x T y  => Some (Some (vtabs env x T y))
        | tapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vtabs _ _ _ _)) => Some None
                | Some (Some (vabs env2 x _ ey)) =>
                  teval n ((x,vx)::env2) (open_tm (TVarF x) ey)
              end
          end
        | ttapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vty _ _)) => Some None
            | Some (Some (vabs _ _ _ _)) => Some None
            | Some (Some (vtabs env2 x T ey)) =>
              teval n ((x,vty env ex)::env2) (open_tm (TVarF x) ey)
          end
      end
  end.

(* automation *)
Hint Unfold venv.
Hint Unfold tenv.

Hint Unfold open.
Hint Unfold closed.
Hint Unfold index.
Hint Unfold length.

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Hint Constructors closed_rec.
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

Example ex1: has_type [] (ttabs 0 TTop (tabs 1 (TVarB 0) (tvar 1))) polyId.
Proof.
  crush_has_tp.
Qed.

(* instantiate it to TTop *)
Example ex2: has_type [(0,polyId)] (ttapp (tvar 0) TTop) (TFun TTop TTop).
Proof.
  crush2.
Qed.


(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)

(* ## Extension, Regularity ## *)

Lemma wf_fresh : forall vs ts,
                    wf_env vs ts ->
                    (fresh vs = fresh ts).
Proof.
  intros. induction H. auto.
  compute. eauto.
Qed.

Hint Immediate wf_fresh.


Lemma wfh_length : forall vvs vs ts,
                    wf_envh vvs vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  compute. eauto.
Qed.

Hint Immediate wf_fresh.

Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < fresh vs.
Proof.
  intros X vs. induction vs.
  - Case "nil". intros. inversion H.
  - Case "cons".
    intros. inversion H. destruct a.
    case_eq (le_lt_dec (fresh vs) i); intros ? E1.
    + SCase "ok".
      rewrite E1 in H1.
      case_eq (beq_nat n i); intros E2.
      * SSCase "hit".
        eapply beq_nat_true in E2. subst n. compute. eauto.
      * SSCase "miss".
        rewrite E2 in H1.
        assert (n < fresh vs). eapply IHvs. apply H1.
        compute. omega.
    + SCase "bad".
      rewrite E1 in H1. inversion H1.
Qed.

Lemma indexr_max : forall X vs n (T: X),
                       indexr n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  - Case "nil". intros. inversion H.
  - Case "cons".
    intros. inversion H. destruct a.
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

Lemma index_extend : forall X vs n n' x (T: X),
                       index n vs = Some T ->
                       fresh vs <= n' ->
                       index n ((n',x)::vs) = Some T.

Proof.
  intros.
  assert (n < fresh vs). eapply index_max. eauto.
  assert (n <> n'). omega.
  assert (beq_nat n n' = false) as E. eapply beq_nat_false_iff; eauto.
  assert (fresh vs <= n') as E2. omega.
  elim (le_xx (fresh vs) n' E2). intros ? EX.
  unfold index. unfold index in H. rewrite H. rewrite E. rewrite EX. reflexivity.
Qed.

Lemma indexr_extend : forall X vs n n' x (T: X),
                       indexr n vs = Some T ->
                       indexr n ((n',x)::vs) = Some T.

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

Definition splicett n (V: (id*ty)) :=
  match V with
    | (x,T) => (x,(splice n T))
  end.

Definition spliceat n (V: (id*(venv*ty))) :=
  match V with
    | (x,(G,T)) => (x,(G,splice n T))
  end.

Lemma splice_open_permute: forall {X} (G0:list (id*X)) T2 n j,
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

Lemma indexr_splice_hi: forall G0 G2 x0 x v1 T,
    indexr x0 (G2 ++ G0) = Some T ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (splicett (length G0)) G2 ++ (x, v1) :: G0) = Some (splice (length G0) T).
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

Lemma indexr_spliceat_hi: forall G0 G2 x0 x v1 G T,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (spliceat (length G0)) G2 ++ (x, v1) :: G0) =
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
    + rewrite E in H.  eapply IHG2 in H. destruct p. eapply indexr_extend. eapply H. eauto.
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
  - simpl in H. destruct a.
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
  - destruct a. simpl.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E.
      apply indexr_max in H. subst.
      rewrite app_length in H. apply plus_lt_contra in H. inversion H.
    + apply IHG2. assumption.
Qed.

Lemma indexr_splice_lo: forall G0 G2 x0 x v1 T f,
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 (map (splicett f) G2 ++ (x, v1) :: G0) = Some T.
Proof.
  intros.
  assert (indexr x0 G0 = Some T). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.

Lemma indexr_spliceat_lo: forall G0 G2 x0 x v1 G T f,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    x0 < length G0 ->
    indexr x0 (map (spliceat f) G2 ++ (x, v1) :: G0) = Some (G, T).
Proof.
  intros.
  assert (indexr x0 G0 = Some (G, T)). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.


Lemma fresh_splice_ctx: forall G n,
  fresh G = fresh (map (splicett n) G).
Proof.
  intros. induction G.
  - simpl. reflexivity.
  - destruct a. simpl. reflexivity.
Qed.

Lemma index_splice_ctx: forall G x T n,
  index x G = Some T ->
  index x (map (splicett n) G) = Some (splice n T).
Proof.
  intros. induction G.
  - simpl in H. inversion H.
  - destruct a. simpl in H.
    case_eq (le_lt_dec (fresh G) i); intros E LE; rewrite LE in H.
    case_eq (beq_nat x i); intros Eq; rewrite Eq in H.
    inversion H. simpl. erewrite <- (fresh_splice_ctx). rewrite LE.
    rewrite Eq. reflexivity.
    simpl. erewrite <- (fresh_splice_ctx). rewrite LE.
    rewrite Eq. apply IHG. apply H.
    inversion H.
Qed.

Lemma closed_splice: forall j l T n,
  closed j l T ->
  closed j (S l) (splice n T).
Proof.
  intros. induction H; simpl; eauto.
  case_eq (le_lt_dec n x); intros E LE.
  unfold closed. apply cl_selh. omega.
  unfold closed. apply cl_selh. omega.
Qed.

Lemma map_splice_length_inc: forall G0 G2 x v1,
   (length (map (splicett (length G0)) G2 ++ (x, v1) :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma map_spliceat_length_inc: forall G0 G2 x v1,
   (length (map (spliceat (length G0)) G2 ++ (x, v1) :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.


Lemma closed_inc: forall j l T,
  closed j l T ->
  closed j (S l) T.
Proof.
  intros. induction H; simpl; eauto.
  unfold closed. apply cl_selh. omega.
Qed.

Lemma closed_inc_mult: forall j l l' T,
  closed j l T ->
  l' >= l ->
  closed j l' T.
Proof.
  intros j l l' T H LE. induction LE.
  - assumption.
  - apply closed_inc. assumption.
Qed.

Lemma closed_splice_idem: forall k l T n,
                            closed k l T ->
                            n >= l ->
                            splice n T = T.
Proof.
  intros. induction H; eauto.
  - (* TFun *) simpl.
    rewrite IHclosed_rec1. rewrite IHclosed_rec2.
    reflexivity.
    assumption. assumption.
  - (* TAll *) simpl.
    rewrite IHclosed_rec1. rewrite IHclosed_rec2.
    reflexivity.
    assumption. assumption.
  - (* TVarH *) simpl.
    case_eq (le_lt_dec n x); intros E LE. omega. reflexivity.
  - (* TMem *) simpl.
    rewrite IHclosed_rec.
    reflexivity. assumption.
Qed.

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.

Lemma stp_closed : forall G GH T1 T2,
                     stp G GH T1 T2 ->
                     closed 0 (length GH) T1 /\ closed 0 (length GH) T2.
Proof.
  intros. induction H;
    try solve [repeat ev; split; eauto];
    try solve [try inversion IHstp; split; eauto; apply cl_selh; eapply indexr_max; eassumption];
    try solve [inversion IHstp1 as [IH1 IH2]; inversion IH2; split; eauto;
               apply cl_selh; eapply indexr_max; eassumption].
Qed.

Lemma stp_closed2 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) T2.
Proof.
  intros. apply (proj2 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp_closed1 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) T1.
Proof.
  intros. apply (proj1 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp2_closed: forall G1 G2 T1 T2 GH,
                     stp2 G1 T1 G2 T2 GH ->
                     closed 0 (length GH) T1 /\ closed 0 (length GH) T2.
  intros. induction H;
    try solve [repeat ev; split; eauto];
    try solve [try inversion IHstp2_1; try inversion IHstp2_2; split; eauto;
               apply cl_selh; eapply indexr_max; eassumption];
    try solve [inversion IHstp2 as [IH1 IH2]; inversion IH2; split; eauto;
               apply cl_selh; eapply indexr_max; eassumption].
Qed.

Lemma stp2_closed2 : forall G1 G2 T1 T2 GH,
                       stp2 G1 T1 G2 T2 GH ->
                       closed 0 (length GH) T2.
Proof.
  intros. apply (proj2 (stp2_closed G1 G2 T1 T2 GH H)).
Qed.

Lemma stp2_closed1 : forall G1 G2 T1 T2 GH,
                       stp2 G1 T1 G2 T2 GH ->
                       closed 0 (length GH) T1.
Proof.
  intros. apply (proj1 (stp2_closed G1 G2 T1 T2 GH H)).
Qed.

Lemma stp_splice : forall GX G0 G1 T1 T2 x v1,
   stp GX (G1++G0) T1 T2 ->
   stp GX ((map (splicett (length G0)) G1) ++ (x,v1)::G0)
       (splice (length G0) T1) (splice (length G0) T2).
Proof.
  intros GX G0 G1 T1 T2 x v1 H. remember (G1++G0) as G.
  revert G0 G1 HeqG.
  induction H; intros; subst GH; simpl; eauto.
  - Case "sel1".
    eapply stp_sel1. apply H. assumption.
    assert (splice (length G0) T=T) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp. reflexivity.
  - Case "sela1".
    case_eq (le_lt_dec (length G0) x0); intros E LE.
    + apply stp_sela1 with (T:=(splice (length G0) T)).
      assert (TMem (splice (length G0) T)=(splice (length G0) (TMem T))) as B by auto.
      rewrite B. apply indexr_splice_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x0 = x0 +1) as A by omega.
      rewrite <- A. eapply H0.
      eapply IHstp. eauto.
    + eapply stp_sela1. eapply indexr_splice_lo. eauto. eauto. eauto. eauto.
      assert (splice (length G0) T=T) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp. eauto.
  - Case "selax".
    case_eq (le_lt_dec (length G0) x0); intros E LE.
    + eapply stp_selax with (T:=splice (length G0) T).
      assert (TMem (splice (length G0) T)=(splice (length G0) (TMem T))) as B by auto.
      rewrite B. eapply indexr_splice_hi. eauto. eauto.
    + eapply stp_selax. eapply indexr_splice_lo. eauto. eauto.
  - Case "all".
    eapply stp_all.
    eapply IHstp1. eauto. eauto. eauto.

    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.

    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.

    specialize IHstp2 with (G3:=G0) (G4:=(0, TMem T1) :: G2).
    simpl in IHstp2. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x0.
    rewrite app_length in IHstp2. simpl in IHstp2.
    eapply IHstp2. eauto.

    specialize IHstp3 with (G3:=G0) (G4:=(0, TMem T3) :: G2).
    simpl in IHstp2. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x0.
    rewrite app_length in IHstp3. simpl in IHstp3.
    eapply IHstp3. eauto.
Qed.

Lemma stp2_splice : forall G1 T1 G2 T2 GH1 GH0 x v1,
   stp2 G1 T1 G2 T2 (GH1++GH0) ->
   stp2 G1 (splice (length GH0) T1) G2 (splice (length GH0) T2)
        ((map (spliceat (length GH0)) GH1) ++ (x,v1)::GH0).
Proof.
  intros G1 T1 G2 T2 GH1 GH0 x v1 H. remember (GH1++GH0) as GH.
  revert GH0 GH1 HeqGH.
  induction H; intros; subst GH; simpl; eauto.
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
    case_eq (le_lt_dec (length GH0) x0); intros E LE.
    + eapply stp2_sela1. eapply indexr_spliceat_hi. apply H. eauto.
      eapply closed_splice in H0. assert (S x0 = x0 +1) by omega. rewrite <- H2.
      eapply H0.
      eapply IHstp2. eauto.
    + eapply stp2_sela1. eapply indexr_spliceat_lo. apply H. eauto. eauto.
      assert (splice (length GH0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp2. eauto.
  - Case "selax".
    case_eq (le_lt_dec (length GH0) x0); intros E LE.
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

    subst x0.
    specialize IHstp2_2 with (GH2:=GH0) (GH3:=(0, (G1, T1)) :: GH1).
    simpl in IHstp2_2.
    repeat rewrite splice_open_permute with (j:=0).
    rewrite app_length in IHstp2_2.
    eapply IHstp2_2. reflexivity.

    subst x0.
    specialize IHstp2_3 with (GH2:=GH0) (GH3:=(0, (G2, T3)) :: GH1).
    simpl in IHstp2_3.
    repeat rewrite splice_open_permute with (j:=0).
    rewrite app_length in IHstp2_3.
    eapply IHstp2_3. reflexivity.
Qed.

Lemma stp_extend : forall G1 GH T1 T2 x v1,
                       stp G1 GH T1 T2 ->
                       stp G1 ((x,v1)::GH) T1 T2.
Proof.
  intros. induction H; eauto using indexr_extend.
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
  assert (closed 0 (length GH) T1).  eapply stp_closed2. eauto.
  assert (splice (length GH) T1 = T1) as A1. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (closed 0 (length GH) T3). eapply stp_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (splicett (length GH)) [(0,TMem T1)] ++(x,v1)::GH =
          ((0,TMem T1)::(x,v1)::GH)) as HGX1. {
    simpl. rewrite A1. eauto.
  }
  assert (map (splicett (length GH)) [(0,TMem T3)] ++(x,v1)::GH =
          ((0,TMem T3)::(x,v1)::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  apply stp_all with (x:=length ((x,v1) :: GH)).
  apply IHstp1.
  reflexivity.
  apply closed_inc. apply H1.
  apply closed_inc. apply H2.
  simpl.
  rewrite <- A2. rewrite <- A2.
  unfold open.
  change (TVarH (S (length GH))) with (TVarH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite <- HGX1.
  apply stp_splice.
  rewrite A2. simpl. unfold open in H3. rewrite <- H0. apply H3.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (TVarH (S (length GH))) with (TVarH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  rewrite <- HGX3.
  apply stp_splice.
  simpl. unfold open in H4. rewrite <- H0. apply H4.
Qed.

Lemma indexr_at_index: forall {A} x0 GH0 GH1 x (v:A),
  beq_nat x0 (length GH1) = true ->
  indexr x0 (GH0 ++ (x, v) :: GH1) = Some v.
Proof.
  intros. apply beq_nat_true in H. subst.
  induction GH0.
  - simpl. rewrite <- beq_nat_refl. reflexivity.
  - destruct a. simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    rewrite false_beq_nat. assumption. omega.
Qed.

Lemma indexr_same: forall {A} x0 (v0:A) GH0 GH1 x (v:A) (v':A),
  beq_nat x0 (length GH1) = false ->
  indexr x0 (GH0 ++ (x, v) :: GH1) = Some v0 ->
  indexr x0 (GH0 ++ (x, v') :: GH1) = Some v0.
Proof.
  intros ? ? ? ? ? ? ? ? E H.
  induction GH0.
  - simpl. rewrite E. simpl in H. rewrite E in H. apply H.
  - destruct a. simpl.
    rewrite app_length. simpl.
    case_eq (beq_nat x0 (length GH0 + S (length GH1))); intros E'.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite H. reflexivity.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite IHGH0. reflexivity. assumption.
Qed.

Inductive venv_ext : venv -> venv -> Prop :=
| venv_ext_refl : forall G, venv_ext G G
| venv_ext_cons : forall x T G1 G2, fresh G1 <= x -> venv_ext G1 G2 -> venv_ext ((x,T)::G1) G2.

Inductive aenv_ext : aenv -> aenv -> Prop :=
| aenv_ext_nil : aenv_ext nil nil
| aenv_ext_cons :
    forall x T G' G A A',
      aenv_ext A' A -> venv_ext G' G ->
      aenv_ext ((x,(G',T))::A') ((x,(G,T))::A).

Lemma aenv_ext_refl: forall GH, aenv_ext GH GH.
Proof.
  intros. induction GH.
  - apply aenv_ext_nil.
  - destruct a. destruct p. apply aenv_ext_cons.
    assumption.
    apply venv_ext_refl.
Qed.

Lemma index_extend_mult : forall G G' x T,
                       index x G = Some T ->
                       venv_ext G' G ->
                       index x G' = Some T.
Proof.
  intros G G' x T H HV.
  induction HV.
  - assumption.
  - apply index_extend. apply IHHV. apply H. assumption.
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


Lemma stp2_closure_extend_rec :
  forall G1 G2 T1 T2 GH,
    stp2 G1 T1 G2 T2 GH ->
    (forall G1' G2' GH',
       aenv_ext GH' GH ->
       venv_ext G1' G1 ->
       venv_ext G2' G2 ->
       stp2 G1' T1 G2' T2 GH').
Proof.
  intros G1 G2 T1 T2 GH H.
  induction H; intros; eauto;
  try solve [inversion IHstp2_1; inversion IHstp2_2; eauto];
  try solve [inversion IHstp2; eauto].
  - Case "sel1".
    eapply stp2_sel1. eapply index_extend_mult. apply H.
    assumption. assumption.
    apply IHstp2. assumption. apply venv_ext_refl. assumption.
  - Case "sel2".
    eapply stp2_sel2. eapply index_extend_mult. apply H.
    assumption. assumption.
    apply IHstp2. assumption. assumption. apply venv_ext_refl.
  - Case "selx".
    eapply stp2_selx.
    eapply index_extend_mult. apply H. assumption.
    eapply index_extend_mult. apply H0. assumption.
  - Case "sela1".
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_sela1 with (GX:=GX') (TX:=TX).
    assumption. assumption.
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
    assert (length GH = length GH') as A. {
      apply aenv_ext__same_length. assumption.
    }
    eapply stp2_all with (x:=length GH').
    apply IHstp2_1; assumption.
    reflexivity.
    subst. rewrite <- A. assumption.
    subst. rewrite <- A. assumption.
    subst. rewrite <- A.
    apply IHstp2_2. apply aenv_ext_cons. assumption. assumption. assumption. assumption.
    subst. rewrite <- A.
    apply IHstp2_3. apply aenv_ext_cons. assumption. assumption. assumption. assumption.
Qed.

Lemma stp2_closure_extend : forall G1 T1 G2 T2 GH GX T x v,
                              stp2 G1 T1 G2 T2 ((0,(GX,T))::GH) ->
                              fresh GX <= x ->
                              stp2 G1 T1 G2 T2 ((0,((x,v)::GX,T))::GH).
Proof.
  intros. eapply stp2_closure_extend_rec. apply H.
  apply aenv_ext_cons. apply aenv_ext_refl. apply venv_ext_cons.
  assumption. apply venv_ext_refl. apply venv_ext_refl. apply venv_ext_refl.
Qed.

Lemma stp2_extend : forall x v1 G1 G2 T1 T2 H,
                      stp2 G1 T1 G2 T2 H ->
                      (fresh G1 <= x ->
                       stp2 ((x,v1)::G1) T1 G2 T2 H) /\
                      (fresh G2 <= x ->
                       stp2 G1 T1 ((x,v1)::G2) T2 H) /\
                      (fresh G1 <= x -> fresh G2 <= x ->
                       stp2 ((x,v1)::G1) T1 ((x,v1)::G2) T2 H).
Proof.
  intros. induction H0;
    try solve [split; try split; intros; eauto using index_extend];
    try solve [split; try split; intros;
               inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]]; eauto];
    try solve [split; try split; intros; inversion IHstp2 as [? [? ?]]; eauto];
    try solve [split; try split; intros; inversion IHstp2 as [? [? ?]]; eauto using index_extend];
    try solve [split; try split; intros; inversion IHstp2_1 as [? [? ?]];
               inversion IHstp2_2 as [? [? ?]]; inversion IHstp2_3 as [? [? ?]];
               eauto; eapply stp2_all; eauto using stp2_closure_extend].
Qed.

Lemma stp2_extend2 : forall x v1 G1 G2 T1 T2 H,
                       stp2 G1 T1 G2 T2 H ->
                       fresh G2 <= x ->
                       stp2 G1 T1 ((x,v1)::G2) T2 H.
Proof.
  intros. apply (proj2 (stp2_extend x v1 G1 G2 T1 T2 H H0)). assumption.
Qed.

Lemma stp2_extend1 : forall x v1 G1 G2 T1 T2 H,
                       stp2 G1 T1 G2 T2 H ->
                       fresh G1 <= x ->
                       stp2 ((x,v1)::G1) T1 G2 T2 H.
Proof.
  intros. apply (proj1 (stp2_extend x v1 G1 G2 T1 T2 H H0)). assumption.
Qed.

Lemma stp2_extendH : forall x v1 G1 G2 T1 T2 GH,
                       stp2 G1 T1 G2 T2 GH ->
                       stp2 G1 T1 G2 T2 ((x,v1)::GH).
Proof.
  intros. induction H; eauto using indexr_extend.
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
  assert (closed 0 (length GH) T1). eapply stp2_closed2. eauto.
  assert (splice (length GH) T1 = T1) as A1. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (spliceat (length GH)) [(0,(G1, T1))] ++(x,v1)::GH =
          ((0, (G1, T1))::(x,v1)::GH)) as HGX1. {
    simpl. rewrite A1. eauto.
  }
  assert (closed 0 (length GH) T3). eapply stp2_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (spliceat (length GH)) [(0,(G2, T3))] ++(x,v1)::GH =
          ((0, (G2, T3))::(x,v1)::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  eapply stp2_all.
  apply IHstp2_1.
  reflexivity.
  apply closed_inc. apply H1.
  apply closed_inc. apply H2.
  simpl.
  unfold open.
  rewrite <- A2.
  unfold open.
  change (TVarH (S (length GH))) with (TVarH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite <- HGX1.
  apply stp2_splice.
  subst x0. simpl. unfold open in H3. apply H3.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (TVarH (S (length GH))) with (TVarH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite -> splice_open_permute.
  rewrite <- HGX3.
  apply stp2_splice.
  subst x0. simpl. unfold open in H4. apply H4.
Qed.

Lemma stp2_extendH_mult : forall G1 G2 T1 T2 H H2,
                       stp2 G1 T1 G2 T2 H ->
                       stp2 G1 T1 G2 T2 (H2++H).
Proof.
  intros. induction H2.
  - simpl. assumption.
  - simpl. destruct a as [x v1].
    apply stp2_extendH. assumption.
Qed.

Lemma stp2_extendH_mult0 : forall G1 G2 T1 T2 H2,
                       stp2 G1 T1 G2 T2 [] ->
                       stp2 G1 T1 G2 T2 H2.
Proof.
  intros. rewrite app_nil_end.
  apply stp2_extendH_mult. assumption.
Qed.

Lemma stp2_reg  : forall G1 G2 T1 T2 GH,
                    stp2 G1 T1 G2 T2 GH ->
                    stp2 G1 T1 G1 T1 GH /\ stp2 G2 T2 G2 T2 GH.
Proof.
  intros. induction H;
    try solve [split; eauto];
    try solve [inversion IHstp2; split; eauto];
    try solve [inversion IHstp2_1; inversion IHstp2_2; split; eauto];
    try solve [inversion IHstp2_1; inversion IHstp2_2; inversion IHstp2_3; split; eauto].
Qed.

Lemma stp2_reg2 : forall G1 G2 T1 T2 GH ,
                       stp2 G1 T1 G2 T2 GH ->
                       stp2 G2 T2 G2 T2 GH.
Proof.
  intros. apply (proj2 (stp2_reg G1 G2 T1 T2 GH H)).
Qed.

Lemma stp2_reg1 : forall G1 G2 T1 T2 GH,
                       stp2 G1 T1 G2 T2 GH ->
                       stp2 G1 T1 G1 T1 GH.
Proof.
  intros. apply (proj1 (stp2_reg G1 G2 T1 T2 GH H)).
Qed.

(* not used, but for good measure *)
Lemma stp_reg  : forall G GH T1 T2,
                    stp G GH T1 T2 ->
                    stp G GH T1 T1 /\ stp G GH T2 T2.
Proof.
  intros. induction H;
    try solve [split; eauto];
    try solve [inversion IHstp; split; eauto];
    try solve [inversion IHstp1; inversion IHstp2; split; eauto];
    try solve [inversion IHstp1; inversion IHstp2; inversion IHstp3; split; eauto].
Qed.

Lemma valtp_extend : forall vs v x v1 T,
                       val_type vs v T ->
                       fresh vs <= x ->
                       val_type ((x,v1)::vs) v T.
Proof.
  intros. induction H; eauto; econstructor; eauto; eapply stp2_extend2; eauto.
Qed.


Lemma index_safe_ex: forall H1 G1 TF i,
             wf_env H1 G1 ->
             index i G1 = Some TF ->
             exists v, index i H1 = Some v /\ val_type H1 v TF.
Proof. intros. induction H.
   - Case "nil". inversion H0.
   - Case "cons". inversion H0.
     case_eq (le_lt_dec (fresh ts) n); intros ? E1.
     + SCase "ok".
       rewrite E1 in H3.
       assert ((fresh ts) <= n) as QF. eauto. rewrite <-(wf_fresh vs ts H1) in QF.
       elim (le_xx (fresh vs) n QF). intros ? EX.

       case_eq (beq_nat i n); intros E2.
       * SSCase "hit".
         assert (index i ((n, v) :: vs) = Some v). {
           eauto. unfold index. rewrite EX. rewrite E2. eauto.
         }
         assert (t = TF).
         unfold index in H0. rewrite E1 in H0. rewrite E2 in H0. inversion H0. eauto.
         subst t. eauto.
       * SSCase "miss".
         rewrite E2 in H3.
         assert (exists v0, index i vs = Some v0 /\ val_type vs v0 TF) as HI. {
           eapply IHwf_env. eauto.
         }
         inversion HI as [v0 HI1]. inversion HI1.
         eexists. econstructor. eapply index_extend; eauto. eapply valtp_extend; eauto.
     + SSCase "bad".
       rewrite E1 in H3. inversion H3.
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
Lemma stp2_trans: forall G1 G2 G3 T1 T2 T3 H,
  stp2 G1 T1 G2 T2 H ->
  stp2 G2 T2 G3 T3 H ->
  stp2 G1 T1 G3 T3 H.
Proof. admit. Qed.


(* ### Substitution for relating static and dynamic semantics ### *)

Lemma index_miss {X}: forall x x1 (B:X) A G,
  index x ((x1,B)::G) = A ->
  fresh G <= x1 ->
  x <> x1 ->
  index x G = A.
Proof.
  intros.
  unfold index in H.
  elim (le_xx (fresh G) x1 H0). intros.
  rewrite H2 in H.
  assert (beq_nat x x1 = false). eapply beq_nat_false_iff. eauto.
  rewrite H3 in H. eapply H.
Qed.

Lemma index_hit {X}: forall x x1 (B:X) A G,
  index x ((x1,B)::G) = Some A ->
  fresh G <= x1 ->
  x = x1 ->
  B = A.
Proof.
  intros.
  unfold index in H.
  elim (le_xx (fresh G) x1 H0). intros.
  rewrite H2 in H.
  assert (beq_nat x x1 = true). eapply beq_nat_true_iff. eauto.
  rewrite H3 in H. inversion H. eauto.
Qed.

Lemma index_hit2 {X}: forall x x1 (B:X) A G,
  fresh G <= x1 ->
  x = x1 ->
  B = A ->
  index x ((x1,B)::G) = Some A.
Proof.
  intros.
  unfold index.
  elim (le_xx (fresh G) x1 H). intros.
  rewrite H2.
  assert (beq_nat x x1 = true). eapply beq_nat_true_iff. eauto.
  rewrite H3. rewrite H1. eauto.
Qed.


Lemma indexr_miss {X}: forall x x1 (B:X) A G,
  indexr x ((x1,B)::G) = A ->
  x <> (length G)  ->
  indexr x G = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = false). eapply beq_nat_false_iff. eauto.
  rewrite H1 in H. eauto.
Qed.

Lemma indexr_hit {X}: forall x x1 (B:X) A G,
  indexr x ((x1,B)::G) = Some A ->
  x = length G ->
  B = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1 in H. inversion H. eauto.
Qed.


Lemma indexr_hit0: forall GH (GX0:venv) (TX0:ty),
      indexr 0 (GH ++ [(0,(GX0, TX0))]) =
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

Lemma closed_no_open: forall T x l j,
  closed_rec j l T ->
  T = open_rec j x T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed_rec; rewrite <-IHclosed_rec; auto];
  try solve [compute; compute in IHclosed_rec1; compute in IHclosed_rec2;
             rewrite <-IHclosed_rec1; rewrite <-IHclosed_rec2; auto].

  Case "TVarB".
    unfold open_rec. assert (k <> i). omega.
    apply beq_nat_false_iff in H0.
    rewrite H0. auto.
Qed.

Lemma closed_upgrade: forall i j l T,
 closed_rec i l T ->
 j >= i ->
 closed_rec j l T.
Proof.
 intros. generalize dependent j. induction H; intros; eauto.
 Case "TBind". econstructor. eapply IHclosed_rec1. omega. eapply IHclosed_rec2. omega.
 Case "TVarB". econstructor. omega.
Qed.

Lemma closed_upgrade_free: forall i l k T,
 closed_rec i l T ->
 k >= l ->
 closed_rec i k T.
Proof.
 intros. generalize dependent k. induction H; intros; eauto.
 Case "TVarH". econstructor. omega.
Qed.

Lemma open_subst_commute: forall T2 TX (n:nat) x j,
closed j n TX ->
(open_rec j (TVarH x) (subst TX T2)) =
(subst TX (open_rec j (TVarH (x+1)) T2)).
Proof.
  intros T2 TX n. induction T2; intros; eauto.
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eapply closed_upgrade. eauto. eauto. eauto.
  -  simpl. case_eq (beq_nat i 0); intros E. symmetry. eapply closed_no_open. eauto. simpl. eauto.
  - simpl. case_eq (beq_nat j i); intros E. simpl.
    assert (x+1<>0). omega. eapply beq_nat_false_iff in H0.
    assert (x=x+1-1). unfold id. omega.
    rewrite H0. eauto.
    simpl. eauto.
  -  simpl. rewrite IHT2. eauto. eauto.
Qed.

Lemma closed_no_subst: forall T j TX,
   closed_rec j 0 T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
  try rewrite (IHT j TX); eauto; try rewrite (IHT2 (S j) TX); eauto;
  try rewrite (IHT1 j TX); eauto.

  eapply closed_upgrade. eauto. eauto.

  subst. omega.
Qed.

Lemma closed_open: forall j n TX T, closed (j+1) n T -> closed j n TX ->
  closed j n (open_rec j TX T).
Proof.
  intros. generalize dependent j.
  induction T; intros; inversion H; unfold closed;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.
  eapply closed_upgrade. eauto. eauto.
  - Case "TVarB". simpl.
    case_eq (beq_nat j i); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
Qed.

Lemma closed_subst: forall j n TX T, closed j (n+1) T -> closed 0 n TX -> closed j (n) (subst TX T).
Proof.
  intros. generalize dependent j.
  induction T; intros; inversion H; unfold closed;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - Case "TVarH". simpl.
    case_eq (beq_nat i 0); intros E.
    eapply closed_upgrade. eapply closed_upgrade_free.
    eauto. omega. eauto. omega.
    econstructor. assert (i > 0). eapply beq_nat_false_iff in E. omega. omega.
Qed.


Lemma subst_open_commute_m: forall j n m TX T2, closed (j+1) (n+1) T2 -> closed 0 m TX ->
    subst TX (open_rec j (TVarH (n+1)) T2) = open_rec j (TVarH n) (subst TX T2).
Proof.
  intros. generalize dependent j. generalize dependent n.
  induction T2; intros; inversion H; simpl; eauto;
          try rewrite IHT2_1; try rewrite IHT2_2; try rewrite IHT2; eauto.

  - Case "TVarH". simpl. case_eq (beq_nat i 0); intros E.
    eapply closed_no_open. eapply closed_upgrade. eauto. omega.
    eauto.
  - Case "TVarB". simpl. case_eq (beq_nat j i); intros E.
    simpl. case_eq (beq_nat (n+1) 0); intros E2.
    eapply beq_nat_true_iff in E2. omega.
    assert (n+1-1 = n). omega. eauto.
    eauto.
Qed.

Lemma subst_open_commute: forall j n TX T2, closed (j+1) (n+1) T2 -> closed 0 0 TX ->
    subst TX (open_rec j (TVarH (n+1)) T2) = open_rec j (TVarH n) (subst TX T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_zero: forall j k TX T2, closed k 0 T2 ->
    subst TX (open_rec j (TVarH 0) T2) = open_rec j TX T2.
Proof.
  intros. generalize dependent k. generalize dependent j.
  induction T2; intros; inversion H; simpl; eauto;
  try rewrite (IHT2_1 _ k);
  try rewrite (IHT2_2 _ (S k));
  try rewrite (IHT2_2 _ (S k));
  try rewrite (IHT2 _ k); eauto.
  eapply closed_upgrade; eauto.
  case_eq (beq_nat i 0); intros E. omega. omega.
  case_eq (beq_nat j i); intros E. eauto. eauto.
Qed.

Lemma Forall2_length: forall A B f (G1:list A) (G2:list B),
                        Forall2 f G1 G2 -> length G1 = length G2.
Proof.
  intros. induction H.
  eauto.
  simpl. eauto.
Qed.


Lemma nosubst_intro: forall j T, closed j 0 T -> nosubst T.
Proof.
  intros. generalize dependent j.
  induction T; intros; inversion H; simpl; eauto.
  omega.
Qed.

Lemma nosubst_open: forall j TX T2, nosubst TX -> nosubst T2 -> nosubst (open_rec j TX T2).
Proof.
  intros. generalize dependent j. induction T2; intros;
  try inversion H0; simpl; eauto.
  case_eq (beq_nat j i); intros E. eauto. eauto.
Qed.

(* substitution for one-env stp. not necessary, but good sanity check *)
Definition substt (UX: ty) (V: (id*ty)) :=
  match V with
    | (x,T) => (x-1,(subst UX T))
  end.

Lemma indexr_subst: forall GH0 x TX T,
   indexr x (GH0 ++ [(0, TMem TX)]) = Some T ->
   x = 0 /\ TMem TX = T \/
   x > 0 /\ indexr (x-1) (map (substt TX) GH0) = Some (subst TX T).
Proof.
  intros GH0. induction GH0; intros.
  - simpl in H. case_eq (beq_nat x 0); intros E.
    + rewrite E in H. inversion H.
      left. split. eapply beq_nat_true_iff. eauto. eauto.
    + rewrite E in H. inversion H.
  -  destruct a. unfold id in H. remember ((length (GH0 ++ [(0, TMem TX)]))) as L.
     case_eq (beq_nat x L); intros E.
     + assert (x = L). eapply beq_nat_true_iff. eauto.
       eapply indexr_hit in H.
       right. split. rewrite app_length in HeqL. simpl in HeqL. omega.
       assert ((x - 1) = (length (map (substt TX) GH0))).
       rewrite map_length. rewrite app_length in HeqL. simpl in HeqL. unfold id. omega.
       simpl.
       eapply beq_nat_true_iff in H1. unfold id in H1. unfold id. rewrite H1.
       subst. eauto. eauto. subst. eauto.
     + assert (x <> L). eapply beq_nat_false_iff. eauto.
       eapply indexr_miss in H. eapply IHGH0 in H.
       inversion H. left. eapply H1.
       right. inversion H1. split. eauto.
       simpl.
       assert ((x - 1) <> (length (map (substt TX) GH0))).
       rewrite app_length in HeqL. simpl in HeqL. rewrite map_length.
       unfold not. intros. subst L. unfold id in H0. unfold id in H2.
       unfold not in H0. eapply H0. unfold id in H4. rewrite <-H4. omega.
       eapply beq_nat_false_iff in H4. unfold id in H4. unfold id. rewrite H4.
       eauto. subst. eauto.
Qed.


Lemma stp_substitute: forall T1 T2 GX GH,
   stp GX GH T1 T2 ->
   forall GH0 TX,
     GH = (GH0 ++ [(0,TMem TX)]) ->
     closed 0 0 TX ->
     stp GX (map (substt TX) GH0) TX TX ->
     stp GX (map (substt TX) GH0)
         (subst TX T1)
         (subst TX T2).
Proof.
  intros T1 T2 GX GH H.
  induction H.
  - Case "topx". eauto.
  - Case "top". eauto.
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
      eapply closed_inc_mult. eassumption. omega.
      eauto.
  - Case "selax". intros GH0 TX ? ? ?. simpl.
    subst GH. specialize (indexr_subst _ x TX (TMem T) H). intros.
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
    + specialize IHstp2 with (GH0:=(0, TMem T1)::GH0) (TX:=TX).
      subst GH. simpl in IHstp2.
      unfold open. unfold open in IHstp2.
      subst x.
      rewrite open_subst_commute with (n:=0).
      rewrite app_length in IHstp2. simpl in IHstp2.
      eapply IHstp2; eauto. eapply stp_extend; eauto.
      eauto.
    + specialize IHstp3 with (GH0:=(0, TMem T3)::GH0) (TX:=TX).
      subst GH. simpl in IHstp3.
      unfold open. unfold open in IHstp3.
      subst x.
      rewrite open_subst_commute with (n:=0).
      rewrite open_subst_commute with (n:=0).
      rewrite app_length in IHstp3. simpl in IHstp3.
      eapply IHstp3; eauto. eapply stp_extend; eauto.
      eauto. eauto.
Qed.

(*
when and how we can replace with multiple environments:

stp2 G1 T1 G2 T2 (GH0 ++ [(0,vtya GX TX)])

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
  (exists x1, index x1 G1 = Some (vty GX TX) /\ T1' = (subst (TVarF x1) T1)) \/
  (G1 = GX /\ T1' = (subst TX T1)) \/
  (closed 0 0 T1 /\ T1' = T1) \/ (* this one is for convenience: redundant with next *)
  (nosubst T1 /\ T1' = subst TTop T1).


Definition compat2 (GX:venv) (TX: ty) (p1:id*(venv*ty)) (p2:id*(venv*ty)) :=
  match p1, p2 with
      (n1,(G1,T1)), (n2,(G2,T2)) => n1=n2(*+1 disregarded*) /\ G1 = G2 /\ compat GX TX G1 T1 T2
  end.


Lemma closed_compat: forall GX TX GXX TXX TXX' j k,
  compat GX TX GXX TXX TXX' ->
  closed 0 k TX ->
  closed j (k+1) TXX ->
  closed j k TXX'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2. destruct H2. rewrite H3.
    eapply closed_subst. eauto. eauto.
  - destruct H2. destruct H2. rewrite H3.
    eapply closed_subst. eauto. eauto.
  - destruct H2. rewrite H3.
    eapply closed_upgrade. eapply closed_upgrade_free. eauto. omega. omega.
  - destruct H2. rewrite H3.
    eapply closed_subst. eauto. eauto.
Qed.

Lemma indexr_compat_miss0: forall GH GH' GX TX (GXX:venv) (TXX:ty) n,
      Forall2 (compat2 GX TX) GH GH' ->
      indexr (n+1) (GH ++ [(0,(GX, TX))]) = Some (GXX,TXX) ->
      exists TXX', indexr n GH' = Some (GXX,TXX') /\ compat GX TX GXX TXX TXX'.
Proof.
  intros. revert n H0. induction H.
  - intros. simpl. eauto. simpl in H0. assert (n+1 <> 0). omega.
    eapply beq_nat_false_iff in H. rewrite H in H0. inversion H0.
  - intros. simpl. destruct y.
    case_eq (beq_nat n (length l')); intros E.
    + simpl in H1. destruct x. rewrite app_length in H1. simpl in H1.
      assert (n = length l'). eapply beq_nat_true_iff. eauto.
      assert (beq_nat (n+1) (length l + 1) = true). eapply beq_nat_true_iff.
      rewrite (Forall2_length _ _ _ _ _ H0). omega.
      rewrite H3 in H1. destruct p. destruct p0. inversion H1. subst. simpl in H.
      destruct H. destruct H2. subst. inversion H1. subst.
      eexists. eauto.
    + simpl in H1. destruct x.
      assert (n <> length l'). eapply beq_nat_false_iff. eauto.
      assert (beq_nat (n+1) (length l + 1) = false). eapply beq_nat_false_iff.
      rewrite (Forall2_length _ _ _ _ _ H0). omega.
      rewrite app_length in H1. simpl in H1.
      rewrite H3 in H1.
      eapply IHForall2. eapply H1.
Qed.

Ltac eu := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.

Lemma compat_top: forall GX TX G1 T1',
  compat GX TX G1 TTop T1' -> closed 0 0 TX -> T1' = TTop.
Proof.
  intros ? ? ? ? CC CLX. repeat destruct CC as [|CC]; eu; eauto.
Qed.

Lemma compat_mem: forall GX TX G1 T1 T1',
    compat GX TX G1 (TMem T1) T1' ->
    closed 0 0 TX ->
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
    closed 0 0 TX ->
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
    closed 0 0 TX ->
    closed 0 0 TXX ->
    index x G1 = Some (vty GXX TXX) ->
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
    closed 0 0 TX ->
    indexr x (GH0 ++ [(0, (GX, TX))]) = Some (GXX, TXX) ->
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
    closed 0 0 TX -> closed 1 (n+1) T2 ->
    exists TA TB, T1' = TAll TA TB /\
                  closed 1 n TB /\
                  compat GX TX G1 T1 TA /\
                  compat GX TX G1 (open_rec 0 (TVarH (n+1)) T2) (open_rec 0 (TVarH n) TB).
Proof.
  intros ? ? ? ? ? ? ? CC CLX CL2. destruct CC.

  simpl in H. destruct H. destruct H. repeat eexists. eauto. eapply closed_subst. eauto. eauto.
  unfold compat. eauto. unfold compat. left. exists x. eauto.
  rewrite subst_open_commute. eauto. eauto. eauto.

  destruct H. destruct H. simpl in H0. repeat eexists. eauto. eapply closed_subst. eauto.
  eapply closed_upgrade_free. eauto. omega. unfold compat. eauto. unfold compat.
  right. left. rewrite subst_open_commute. eauto. eauto. eauto.

  destruct H. destruct H. inversion H. repeat eexists. eauto. subst.
  eapply closed_upgrade_free. eauto. omega. unfold compat. eauto.
  unfold compat. eauto. right. right.

  right. split. eapply nosubst_open. simpl. omega. eapply nosubst_intro. eauto. symmetry.
  assert (T2 = subst TTop T2). symmetry. eapply closed_no_subst. eauto.
  remember (open_rec 0 (TVarH n) T2) as XX. rewrite H7 in HeqXX. subst XX.
  eapply subst_open_commute. eauto. eauto.

  simpl in H. destruct H. destruct H. repeat eexists. eauto. eapply closed_subst. eauto. eauto.
  unfold compat. right. right. right. eauto.
  unfold compat. right. right. right. split. eapply nosubst_open. simpl. omega. eauto.
  rewrite subst_open_commute. eauto. eauto. eauto.
Qed.

Lemma stp2_substitute: forall G1 G2 T1 T2 GH,
   stp2 G1 T1 G2 T2 GH ->
   forall GH0 GH0' GX TX T1' T2',
     GH = (GH0 ++ [(0,(GX, TX))]) ->
     stp2 GX TX GX TX GH0' ->
     closed 0 0 TX ->
     compat GX TX G1 T1 T1' ->
     compat GX TX G2 T2 T2' ->
     Forall2 (compat2 GX TX) GH0 GH0' ->
     stp2 G1 T1' G2 T2' GH0'.
Proof.
  intros G1 G2 T1 T2 GH H.
  induction H.
  - Case "topx".
    intros GH0 GH0' GXX TXX T1' T2' ? RF CX IX1 IX2 FA.
    eapply compat_top in IX1.
    eapply compat_top in IX2.
    subst. eauto. eauto. eauto.

  - Case "top".
    intros GH0 GH0' GXX TXX T1' T2' ? RF CX IX1 IX2 FA.
    eapply compat_top in IX2.
    subst. eauto. eauto.

  - Case "fun".
    intros GH0 GH0' GXX TXX T1' T2' ? RF CX IX1 IX2 FA.
    eapply compat_fun in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_fun in IX2. repeat destruct IX2 as [? IX2].
    subst. eauto. eauto. eauto.

  - Case "mem".
    intros GH0 GH0' GXX TXX T1' T2' ? RF CX IX1 IX2 FA.
    eapply compat_mem in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_mem in IX2. repeat destruct IX2 as [? IX2].
    subst. eauto. eauto. eauto.

  - Case "sel1".
    intros GH0 GH0' GXX TXX T1' T2' ? RF CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX G1 T1' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    assert (compat GXX TXX GX TX TX) as CPX. right. right. left. eauto.

    subst.
    eapply stp2_sel1. eauto. eauto.
    eapply IHstp2. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto. eauto. eauto.

  - Case "sel2".
    intros GH0 GH0' GXX TXX T1' T2' ? RF CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX G2 T2' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    assert (compat GXX TXX GX TX TX) as CPX. right. right. left. eauto.

    subst.
    eapply stp2_sel2. eauto. eauto.
    eapply IHstp2. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto. eauto. eauto.

  - Case "selx".
    intros GH0 GH0' GXX TXX T1' T2' ? RF CX IX1 IX2 FA.

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
    eapply stp2_selx. eauto. eauto.

  - Case "sela1".
    intros GH0 GH0' GXX TXX T1' T2' ? RF CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX G1 (TVarH x) T1') as IXX. eauto.

    eapply (compat_selh GXX TXX G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    destruct IX1.
    + destruct H4. destruct H5. subst.

      assert (compat GXX TXX GXX TXX TXX) as CPX. {
        right. left. split. eauto. symmetry. eapply closed_no_subst. eauto.
      }

      inversion IXX.

      destruct H2. destruct H2. subst. simpl.
      eapply stp2_sel1. eauto. eauto.
      eapply IHstp2. eauto. eauto. eauto. eauto. eauto. eauto.

      inversion H2.

      destruct H4. subst. simpl.
      eapply IHstp2. eauto. eauto. eauto. eauto. eauto. eauto.

      inversion H4.

      destruct H5. inversion H5. omega. (* contra *)

      destruct H5. simpl in H5. destruct H5. eauto. (* contra *)

    + destruct H4 as [TXX' ?]. destruct H4. destruct H5. destruct H6.
      subst T1'. eapply stp2_sela1. eauto.
      assert (x-1+1=x) as A by omega.
      remember (x-1) as x0. rewrite <- A in H0.
      eapply closed_compat. eauto. eapply closed_upgrade_free. eauto. omega. eauto.
      eapply IHstp2. eauto. eauto. eauto. eauto. eauto. eauto.

    + eauto.
    + subst GH. eauto.
    + eauto.


  - Case "selax".

    intros GH0 GH0' GXX TXX T1' T2' ? RFL CX IX1 IX2 FA.

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
      eapply stp2_sel1. eauto. eauto.
      eapply stp2_sel2. eauto. eauto. eauto.

      destruct H0. destruct H0. subst. simpl.
      destruct H3. destruct H3. subst. simpl.
      eapply stp2_sel1. eauto. eauto. eauto.

      destruct H3. destruct H3. subst. simpl.
      inversion H3. omega. (* contra *)

      destruct H3. destruct H3. eauto. (* contra *)

      (* --- *)

      destruct H0. destruct H0. subst. simpl.
      destruct H3. destruct H0. subst. simpl.
      eapply stp2_sel2. eauto. eauto. eauto.

      destruct H0. destruct H0. inversion H0. omega. (* contra *)

      destruct H0. destruct H0. eauto. (* contra *)

      (* --- *)

      destruct H0. destruct H0. subst. simpl.
      destruct H3. destruct H0. subst. simpl.
      eauto.

      destruct H0. destruct H0. inversion H0. omega.
      destruct H0. destruct H0. eauto.
      destruct H0. destruct H0. inversion H0. omega.
      destruct H0. destruct H0. eauto.

    + destruct H3. destruct H3. omega.
    + destruct H2. destruct H3. omega.
    + destruct H2. destruct H2. destruct H4. destruct H5.
      destruct H3. destruct H3. destruct H7. destruct H8.
      subst. eapply stp2_selax. eauto.

    + eauto.
    + subst GH. eauto.
    + eauto.
    + eauto.
    + eauto. subst GH. eauto.
    + eauto.

  - Case "all".
    intros GH0 GH0' GX TX T1' T2' ? RFL CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply compat_all in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_all in IX2. repeat destruct IX2 as [? IX2].

    subst.

    eapply stp2_all.
    + eapply IHstp2_1. eauto. eauto. eauto. eauto. eauto. eauto.
    + eauto.
    + eauto.
    + eauto.
    + subst. specialize IHstp2_2 with (GH1 := (0, (G1, T1))::GH0).
      eapply IHstp2_2.
      reflexivity.
      eapply stp2_extendH. eauto. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto.
    + subst. specialize IHstp2_3 with (GH1 := (0, (G2, T3))::GH0).
      eapply IHstp2_3.
      reflexivity.
      eapply stp2_extendH. eauto. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
Qed.

(* ### Relating Static and Dynamic Subtyping ### *)
Lemma stp_to_stp2: forall G1 GH T1 T2,
  stp G1 GH T1 T2 ->
  forall GX GY, wf_env GX G1 -> wf_envh GX GY GH ->
  stp2 GX T1 GX T2 GY.
Proof.
  intros G1 G2 T1 T2 ST. induction ST; intros GX GY WX WY.
  - Case "topx". eauto.
  - Case "top". eauto.
  - Case "fun". eauto.
  - Case "mem". eauto.
  - Case "sel1".
    assert (exists v : vl, index x GX = Some v /\ val_type GX v (TMem T)) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? VT]].
    inversion VT; try solve by inversion; subst.
    eapply stp2_sel1; eauto. inversion H2. subst.
    eapply stp2_closed1 in H3. eauto. inversion H3. subst. simpl in H7. apply H7.
    eapply stp2_closed1 in H3. eauto. inversion H3. subst. simpl in H11. apply H11.
    inversion H3. subst.
    eapply stp2_extendH_mult with (H2:=GY) in H8. rewrite app_nil_r in H8.
    eapply stp2_trans. eapply H8. eapply IHST; eauto.
  - Case "selx". eauto.
    assert (exists v : vl, index x GX = Some v /\ val_type GX v (TMem T)) as A.
    eapply index_safe_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]].
    inversion VT; try solve by inversion; subst.
    inversion H2. subst.
    eapply stp2_sel2. eauto. eapply stp2_closed1 in H2. simpl in H2. inversion H2. subst. apply H6.
    eapply stp2_sel1. eauto. eapply stp2_closed1 in H2. simpl in H2. inversion H2. subst. apply H6.
    eapply stp2_extendH_mult with (H2:=GY) in H2. rewrite app_nil_r in H2. inversion H2. subst.
    eapply stp2_reg1. eapply H8.
  - Case "sela1". eauto.
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v (TMem T)) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    inversion VT. subst.
    eapply stp2_sela1. eauto. assumption. eapply IHST. eauto. eauto.
  - Case "selax". eauto.
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v (TMem T)) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    destruct VT. subst.
    eapply stp2_selax. eauto.
  - Case "all".
    subst x. assert (length GY = length GH). eapply wfh_length; eauto.
    eapply stp2_all. eauto. eauto. rewrite H. eauto. rewrite H.  eauto.
    rewrite H.
    eapply IHST2. eauto. eapply wfeh_cons. eauto.
    rewrite H.
    eapply IHST3. eauto. eapply wfeh_cons. eauto.
Qed.

Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stp2 H1 T1 H2 T2 [] ->
  val_type H2 vf T2.
Proof.
  intros. inversion H; econstructor; eauto; eapply stp2_trans; eauto.
Qed.

Lemma restp_widen: forall vf H1 H2 T1 T2,
  res_type H1 vf T1 ->
  stp2 H1 T1 H2 T2 [] ->
  res_type H2 vf T2.
Proof.
  intros. inversion H. eapply not_stuck. eapply valtp_widen; eauto.
Qed.


(* ### Inversion Lemmas ### *)

Lemma invert_abs: forall venv vf T1 T2,
  val_type venv vf (TFun T1 T2) ->
  exists env tenv x y T3 T4,
    vf = (vabs env x T3 y) /\
    fresh env <= x /\
    wf_env env tenv /\
    has_type ((x,T3)::tenv) (open_tm (TVarF x) y) T4 /\
    stp2 venv T1 env T3 [] /\
    stp2 env T4 venv T2 [].
Proof.
  intros. inversion H; try solve by inversion. inversion H3. subst. repeat eexists; repeat eauto.
Qed.

Lemma invert_tabs: forall venv vf T1 T2,
  val_type venv vf (TAll T1 T2) ->
  exists env tenv x y T3 T4,
    vf = (vtabs env x T3 y) /\
    fresh env <= x /\
    wf_env env tenv /\
    has_type ((x,TMem T3)::tenv) (open_tm (TVarF x) y) (open (TVarF x) T4) /\
    stp2 venv T1 env T3 [] /\
    stp2 ((x,vty venv T1)::env) (open (TVarF x) T4) venv (open T1 T2) [].
Proof.
  intros. inversion H; try solve by inversion. inversion H3. subst. repeat eexists; repeat eauto.
  (*
  remember (fresh venv1) as x.
  remember (x + fresh venv0) as xx.
  *)

  (* inversion of TAll < TAll *)
  assert (stp2 venv0 T1 venv1 T0 []). eauto.
  assert (stp2 venv1 (open (TVarH 0) T3) venv0 (open (TVarH 0) T2) [(0,(venv0, T1))]). {
    eapply H19.
  }

  (* need reflexivity *)
  assert (stp2 venv0 T1 venv0 T1 []). eapply stp2_reg1. eauto.
  assert (closed 0 0 T1). eapply stp2_closed1 in H6. simpl in H6. eauto.

  (* now rename *)

  assert (stp2 ((x,vty venv0 T1) :: venv1) (open_rec 0 (TVarF x) T3) venv0 (open T1 T2) []). {
    eapply stp2_substitute with (GH0:=nil).
    eapply stp2_extend1. eapply H5. eauto.
    simpl. eauto.
    eauto.
    eauto.
    left. eexists. split. eapply index_hit2. eauto. eauto. eauto. unfold open.
      rewrite (subst_open_zero 0 1). eauto. eauto.
    right. left. split. eauto. unfold open. rewrite (subst_open_zero 0 1). eauto. eauto.
    eauto.
  }

  (* done *)
  subst. eauto.
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
    + destruct (index_safe_ex venv0 env T1 i) as [v [I V]]; eauto.
      rewrite I. eapply not_stuck. eapply V.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stp_to_stp2; eauto. econstructor.

  - Case "Abs".
    remember (tabs i t e) as xe. induction H0; inversion Heqxe; subst.
    + eapply not_stuck. eapply v_abs; eauto. rewrite (wf_fresh venv0 env H1).
      eauto. eapply stp_to_stp2. eauto. eauto. econstructor.
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stp_to_stp2; eauto. econstructor.

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

      assert (res_type ((x0,vx)::env1) res T4) as HRY.
        SCase "HRY".
          subst. eapply IHn. eauto. eauto.
          (* wf_env x *) econstructor. eapply valtp_widen; eauto.
                         eapply stp2_extend2. eauto. eauto. eauto.

      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto. eapply stp2_extend1. eauto. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stp_to_stp2; eauto. econstructor.

  - Case "TAbs".
    remember (ttabs i t e) as xe. induction H0; inversion Heqxe; subst.
    + eapply not_stuck. eapply v_tabs; eauto. rewrite (wf_fresh venv0 env H1).
      eauto. eapply stp_to_stp2. eauto. eauto. econstructor.
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stp_to_stp2; eauto. econstructor.

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

      assert (res_type ((x0,vty venv0 T11)::env1) res (open (TVarF x0) T4)) as HRY.
        SCase "HRY".
          subst. eapply IHn. eauto. eauto.
          (* wf_env x *) econstructor. eapply v_ty.
          (* wf_env   *) eauto.
      eapply stp2_extend2. eapply stp2_mem. eauto. eauto.
      eauto.
      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stp_to_stp2; eauto. econstructor.

Qed.
