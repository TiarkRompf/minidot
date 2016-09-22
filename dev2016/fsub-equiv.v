(*
FSub (F<:)
T ::= Top | X | T -> T | Forall Z <: T. T^Z
t ::= x | lambda x:T.t | Lambda X<:T.t | t t | t [T]
*)

(* semantic equality big-step / small-step *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.

(* ### Syntax ### *)

Definition id := nat.

Inductive ty : Type :=
| TTop : ty
| TFun : ty -> ty -> ty
| TAll : ty -> ty -> ty
| TVarF : id -> ty (* free type variable, in concrete environment *)
| TVarH : id -> ty (* free type variable, in abstract environment  *)
| TVarB : id -> ty (* locally-bound type variable *)
.

Inductive tm : Type :=
| tvar : id -> tm
| tabs : ty -> tm -> tm
| tapp : tm -> tm -> tm
| ttabs : ty -> tm -> tm
| ttapp : tm -> ty -> tm
| tty: ty -> tm
.

Inductive binding {X: Type} :=
| bind_tm : X -> binding
| bind_ty : X -> binding
.

Inductive vl : Type :=
(* a closure for a term abstraction *)
| vabs : venv (*H*) -> ty -> tm -> vl
(* a closure for a type abstraction *)
| vtabs : venv (*H*) -> ty -> tm -> vl
(* a closure over a type *)
| vty : venv (*H*) -> ty -> vl
with venv : Type := (* need to recurse structurally, hence don't use built-in list *)
| vnil: venv
| vcons: vl -> venv -> venv
.

Definition tenv := list (@binding ty). (* Gamma environment: static *)
(*Definition venv := list vl. (* H environment: run-time *) *)
Definition aenv := list (venv*ty). (* J environment: abstract at run-time *)

(* ### Representation of Bindings ### *)

(* An environment is a list of values, indexed by decrementing ids. *)

Fixpoint lengthr (l : venv) : nat :=
  match l with
    | vnil => 0
    | vcons a  l' =>
      S (lengthr l')
  end.


Fixpoint indexr (n : id) (l : venv) : option vl :=
  match l with
    | vnil => None
    | vcons a  l' =>
      if (beq_nat n (lengthr l')) then Some a else indexr n l'
  end.


Inductive closed: nat(*B*) -> nat(*H*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall i j k,
    closed i j k TTop
| cl_fun: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TFun T1 T2)
| cl_all: forall i j k T1 T2,
    closed i j k T1 ->
    closed (S i) j k T2 ->
    closed i j k (TAll T1 T2)
| cl_sel: forall i j k x,
    k > x ->
    closed i j k (TVarF x)
| cl_selh: forall i j k x,
    j > x ->
    closed i j k (TVarH x)
| cl_selb: forall i j k x,
    i > x ->
    closed i j k (TVarB x)
.

(* open define a locally-nameless encoding wrt to TVarB type variables. *)
(* substitute type u for all occurrences of (TVarB k) *)
Fixpoint open_rec (k: nat) (u: ty) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TFun T1 T2  => TFun (open_rec k u T1) (open_rec k u T2)
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TVarF x => TVarF x
    | TVarH i => TVarH i
    | TVarB i => if beq_nat k i then u else TVarB i
  end.

Definition open u T := open_rec 0 u T.

(* Locally-nameless encoding with respect to varH variables. *)
Fixpoint subst (U : ty) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TFun T1 T2   => TFun (subst U T1) (subst U T2)
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TVarB i      => TVarB i
    | TVarF i      => TVarF i
    | TVarH i      => if beq_nat i 0 then U else TVarH (i-1)
  end.

Definition liftb (f: ty -> ty) b :=
  match b with
    | bind_tm T => bind_tm (f T)
    | bind_ty T => bind_ty (f T)
  end.

Definition substb (U: ty) := liftb (subst U).

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TFun T1 T2   => nosubst T1 /\ nosubst T2
    | TAll T1 T2   => nosubst T1 /\ nosubst T2
    | TVarB i      => True
    | TVarF i      => True
    | TVarH i      => i <> 0
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
(*
Inductive stp: tenv -> tenv -> ty -> ty -> Prop :=
| stp_top: forall G1 GH T1,
    closed 0 (length GH) (length G1) T1 ->
    stp G1 GH T1 TTop
| stp_fun: forall G1 GH T1 T2 T3 T4,
    stp G1 GH T3 T1 ->
    stp G1 GH T2 T4 ->
    stp G1 GH (TFun T1 T2) (TFun T3 T4)
| stp_sel1: forall G1 GH T T2 x,
    indexr x G1 = Some (bind_ty T) ->
    closed 0 0 (length G1) T ->
    stp G1 GH T T2 ->
    stp G1 GH (TVarF x) T2
| stp_selx: forall G1 GH v x,
    (* This is a bit looser than just being able to select on TMem vars. *)
    indexr x G1 = Some v ->
    stp G1 GH (TVarF x) (TVarF x)
| stp_sela1: forall G1 GH T T2 x,
    indexr x GH = Some (bind_ty T) ->
    closed 0 x (length G1) T ->
    stp G1 GH T T2 ->
    stp G1 GH (TVarH x) T2
| stp_selax: forall G1 GH v x,
    (* This is a bit looser than just being able to select on TMem vars. *)
    indexr x GH = Some v  ->
    stp G1 GH (TVarH x) (TVarH x)
| stp_all: forall G1 GH T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G1) T4 ->
    stp G1 ((bind_ty T3)::GH) (open (TVarH x) T2) (open (TVarH x) T4) ->
    stp G1 GH (TAll T1 T2) (TAll T3 T4)
.

(* ### Type Assignment ### *)
Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x env T1,
           indexr x env = Some (bind_tm T1) ->
           stp env [] T1 T1 ->
           has_type env (tvar x) T1
| t_app: forall env f x T1 T2,
           has_type env f (TFun T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
| t_abs: forall env y T1 T2,
           has_type (bind_tm T1::env) y T2 ->
           stp env [] (TFun T1 T2) (TFun T1 T2) ->
           has_type env (tabs T1 y) (TFun T1 T2)
| t_tapp: forall env f T11 T12 T,
           has_type env f (TAll T11 T12) ->
           T = open T11 T12 ->
           has_type env (ttapp f T11) T
| t_tabs: forall env y T1 T2,
           has_type (bind_ty T1::env) y (open (TVarF (length env)) T2) ->
           stp env [] (TAll T1 T2) (TAll T1 T2) ->
           has_type env (ttabs T1 y) (TAll T1 T2)
| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2
.
 *)

(* ### Runtime Subtyping ### *)
(* H1 T1 <: H2 T2 -| J *)
(*
Inductive stp2: bool (* whether the last rule may not be transitivity *) ->
                venv -> ty -> venv -> ty -> aenv  ->
                nat (* derivation size *) ->
                Prop :=
| stp2_top: forall G1 G2 GH T n,
    closed 0 (length GH) (length G1) T ->
    stp2 true G1 T G2 TTop GH (S n)
| stp2_fun: forall G1 G2 T1 T2 T3 T4 GH n1 n2,
    stp2 false G2 T3 G1 T1 GH n1 ->
    stp2 false G1 T2 G2 T4 GH n2 ->
    stp2 true G1 (TFun T1 T2) G2 (TFun T3 T4) GH (S (n1 + n2))

(* concrete type variables *)
| stp2_sel1: forall G1 G2 GX TX x T2 GH n1,
    indexr x G1 = Some (vty GX TX) ->
    closed 0 0 (length GX) TX ->
    stp2 true GX TX G2 T2 GH n1 ->
    stp2 true G1 (TVarF x) G2 T2 GH (S n1)
| stp2_sel2: forall G1 G2 GX TX x T1 GH n1,
    indexr x G2 = Some (vty GX TX) ->
    closed 0 0 (length GX) TX ->
    stp2 false G1 T1 GX TX GH n1 ->
    stp2 true G1 T1 G2 (TVarF x) GH (S n1)
| stp2_selx: forall G1 G2 v x1 x2 GH n,
    indexr x1 G1 = Some v ->
    indexr x2 G2 = Some v ->
    stp2 true G1 (TVarF x1) G2 (TVarF x2) GH (S n)

(* abstract type variables *)
(* X<:T, one sided *)
| stp2_sela1: forall G1 G2 GX TX x T2 GH n1,
    indexr x GH = Some (GX, TX) ->
    closed 0 x (length GX) TX ->
    stp2 false GX TX G2 T2 GH n1 ->
    stp2 true G1 (TVarH x) G2 T2 GH (S n1)
| stp2_selax: forall G1 G2 v x GH n,
    indexr x GH = Some v ->
    stp2 true G1 (TVarH x) G2 (TVarH x) GH (S n)

| stp2_all: forall G1 G2 T1 T2 T3 T4 x GH n1 n2,
    stp2 false G2 T3 G1 T1 GH n1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G2) T4 ->
    stp2 false G1 (open (TVarH x) T2) G2 (open (TVarH x) T4) ((G2, T3)::GH) n2 ->
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
with val_type : venv -> vl -> @binding ty -> Prop :=
| v_ty: forall env venv tenv T1 TE,
    wf_env venv tenv ->
    (exists n, stp2 true venv T1 env TE [] n) ->
    val_type env (vty venv T1) (bind_ty TE)
| v_abs: forall env venv tenv x y T1 T2 TE,
    wf_env venv tenv ->
    has_type (bind_tm T1::tenv) y T2 ->
    length venv = x ->
    (exists n, stp2 true venv (TFun T1 T2) env TE [] n) ->
    val_type env (vabs venv T1 y) (bind_tm TE)
| v_tabs: forall env venv tenv x y T1 T2 TE,
    wf_env venv tenv ->
    has_type (bind_ty T1::tenv) y (open (TVarF x) T2) ->
    length venv = x ->
    (exists n, stp2 true venv (TAll T1 T2) env TE [] n) ->
    val_type env (vtabs venv T1 y) (bind_tm TE)
.

Inductive wf_envh : venv -> aenv -> tenv -> Prop :=
| wfeh_nil : forall vvs, wf_envh vvs nil nil
| wfeh_cons : forall t vs vvs ts,
    wf_envh vvs vs ts ->
    wf_envh vvs (cons (vvs,t) vs) (cons (bind_ty t) ts)
.

Inductive valh_type : venv -> aenv -> (venv*ty) -> (@binding ty) -> Prop :=
| v_tya: forall aenv venv T1,
    valh_type venv aenv (venv, T1) (bind_ty T1)
.
*)

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
        | tty T        => Some (Some (vty env T))
        | tvar x       => Some (indexr x env)
        | tabs T y     => Some (Some (vabs env T y))
        | ttabs T y    => Some (Some (vtabs env T y))
        | tapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vtabs _ _ _)) => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vabs env2 _ ey)) =>
                  teval n (vcons vx env2) ey
              end
          end
        | ttapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vabs _ _ _)) => Some None
            | Some (Some (vty _ _)) => Some None
            | Some (Some (vtabs env2 T ey)) =>
              teval n (vcons (vty env ex) env2) ey
          end
      end
  end.

(* Substitution-based evaluator *)


Fixpoint shift_ty (u:nat) (T : ty) {struct T} : ty :=
  match T with
    | TTop        => TTop
    | TFun T1 T2  => TFun (shift_ty u T1) (shift_ty u T2)
    | TAll T1 T2  => TAll (shift_ty u T1) (shift_ty u T2)
    | TVarF i     => TVarF i
    | TVarH i     => TVarH (i+u)
    | TVarB i     => TVarB i
  end.


Fixpoint shift_tm (u:nat) (T : tm) {struct T} : tm :=
  match T with
    | tvar i      => tvar (i + u)
    | tabs T1 t   => tabs (shift_ty u T1) (shift_tm u t)
    | tapp t1 t2  => tapp (shift_tm u t1) (shift_tm u t2)
    | ttabs T1 t  => ttabs (shift_ty u T1) (shift_tm u t) 
    | ttapp t1 T2 => ttapp (shift_tm u t1) (shift_ty u T2)
    | tty T       => tty (shift_ty u T)
  end.

Definition et t := match t with
                     | tty T => T
                     | _ => TTop
                   end.

Fixpoint subst_tm (u:tm) (T : tm) {struct T} : tm :=
  match T with
    | tvar i      => if beq_nat i 0 then u else tvar (i-1)
    | tabs T1 t   => tabs (subst (et u) T1) (subst_tm (shift_tm 1 u) t)
    | tapp t1 t2  => tapp (subst_tm u t1) (subst_tm u t2)
    | ttabs T1 t  => ttabs (subst (et u) T1) (subst_tm (shift_tm 1 u) t)
    | ttapp t1 T2 => ttapp (subst_tm u t1) (subst (et u) T2)
    | tty T       => tty (subst (et u) T)
  end.

Fixpoint subst_ty (u:ty) (T : tm) {struct T} : tm :=
  match T with
    | tvar i      => if beq_nat i 0 then (tty u) else tvar (i-1)
    | tabs T1 t   => tabs (subst u T1) (subst_ty (shift_ty 1 u) t)
    | tapp t1 t2  => tapp (subst_ty u t1) (subst_ty u t2)
    | ttabs T1 t  => ttabs (subst u T1) (subst_ty (shift_ty 1 u) t)
    | ttapp t1 T2 => ttapp (subst_ty u t1) (subst u T2)
    | tty T       => tty (subst u T)
  end.

Fixpoint tevals(n: nat)(t: tm){struct n}: option (option tm) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | tty T        => Some (Some (tty T))
        | tvar x       => Some None
        | tabs T y     => Some (Some (tabs T y))
        | ttabs T y    => Some (Some (ttabs T y))
        | tapp ef ex   =>
          match tevals n ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match tevals n ef with
                | None => None
                | Some None => Some None
                | Some (Some (tty T)) => Some None
                | Some (Some (tvar _)) => Some None
                | Some (Some (tapp _ _)) => Some None
                | Some (Some (ttapp _ _)) => Some None
                | Some (Some (ttabs _ _)) => Some None
                | Some (Some (tabs _ ey)) =>
                  tevals n (subst_tm vx ey)
              end
          end
        | ttapp ef ex   =>
          match tevals n ef with
            | None => None
            | Some None => Some None
            | Some (Some (tty T)) => Some None
            | Some (Some (tvar _)) => Some None
            | Some (Some (tapp _ _)) => Some None
            | Some (Some (ttapp _ _)) => Some None
            | Some (Some (tabs _ _)) => Some None
            | Some (Some (ttabs T ey)) =>
              tevals n (subst_ty ex ey)
          end
      end
  end.








(* ### Evaluation (Small-Step Semantics) ### *)

Inductive value : tm -> Prop :=
| V_Abs : forall T t,
    value (tabs T t)
| V_TAbs : forall T t,
    value (ttabs T t)
| V_Ty : forall T,
    value (tty T)
.


Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall v T1 t12,
    value v ->
    step (tapp (tabs T1 t12) v) (subst_tm v t12)
| ST_App1 : forall t1 t1' t2,
    step t1 t1' ->
    step (tapp t1 t2) (tapp t1' t2)
| ST_App2 : forall f t2 t2',
    value f ->
    step t2 t2' ->
    step (tapp f t2) (tapp f t2')
.
(* TODO: ttapp *)

Inductive mstep : nat -> tm -> tm -> Prop :=
| MST_Z : forall t,
    mstep 0 t t
| MST_S: forall n t1 t2 t3,
    step t1 t2 ->
    mstep n t2 t3 ->
    mstep (S n) t1 t3
.



(* automation *)
(*Hint Unfold venv.*)
Hint Constructors venv.
Hint Unfold tenv.

Hint Unfold open.
Hint Unfold indexr.
Hint Unfold length.

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Hint Constructors closed.
(* Hint Constructors has_type.
Hint Constructors val_type.
Hint Constructors wf_env.
Hint Constructors stp.
Hint Constructors stp2. *)

Hint Constructors option.
Hint Constructors list.

Hint Resolve ex_intro.



(* ### Euivalence big-step env <-> big-step subst ### *)

Fixpoint subst_ty_all n venv t {struct venv} :=
  match venv with
    | vnil                       => t
    | vcons (vabs venv0 T y) tl  => subst TTop (subst_ty_all (S n) tl t) (* bogus *) 
    | vcons (vtabs venv0 T y) tl => subst TTop (subst_ty_all (S n) tl t) (* bogus *)
    | vcons (vty venv0 T) tl     =>
      subst (shift_ty n (subst_ty_all 0 venv0 T)) (subst_ty_all (S n) tl t)
  end.


Fixpoint subst_tm_all n venv t {struct venv} :=
  match venv with
    | vnil => t
    | vcons (vabs venv0 T y) tl =>
      subst_tm (shift_tm n (tabs (subst_ty_all 0 venv0 T) (subst_tm_all 1 venv0 y))) (subst_tm_all (S n) tl t)
    | vcons (vtabs venv0 T y) tl =>
      subst_tm (shift_tm n (ttabs (subst_ty_all 0 venv0 T) (subst_tm_all 1 venv0 y))) (subst_tm_all (S n) tl t)
    | vcons (vty venv0 T) tl =>
      subst_ty (shift_ty n (subst_ty_all 0 venv0 T)) (subst_tm_all (S n) tl t) (* bogus *)
    (* last case: need to subst on term level, so that variable names remain correct ??? *)
    (* but is inserting tvar 0 ok for subsequent substitutions ??? *)
  end.


Definition subst_tm_res t :=
  match t with
    | None => None
    | Some None => Some None
    | Some (Some (vabs venv0 T y)) => Some (Some ((tabs (subst_ty_all 0 venv0 T) (subst_tm_all 1 venv0 y))))
    | Some (Some (vtabs venv0 T y)) => Some (Some ((ttabs (subst_ty_all 0 venv0 T) (subst_tm_all 1 venv0 y))))
    | Some (Some (vty venv0 T)) => Some (Some (tty (subst_ty_all 0 venv0 T)))
  end.



Lemma idx_miss: forall env i l,
  i >= lengthr env ->
  indexr i env = None /\ subst_tm_all l env (tvar i) = (tvar (i-(lengthr env))).
Proof.
  intros env. induction env.
  - intros. simpl in H. simpl. 
    assert (i-0=i). omega. rewrite H0. eauto.
  - intros. simpl in H. simpl.
    destruct (IHenv i (S l)) as [A B]. omega. 
    rewrite B. simpl. 
    assert (beq_nat (i - lengthr env) 0 = false). eapply beq_nat_false_iff. omega.
    assert (beq_nat i (lengthr env) = false). eapply beq_nat_false_iff. omega.
    rewrite H0. rewrite H1. 
    assert (i - lengthr env - 1 = i - S (lengthr env)). omega.
    rewrite H2. 

    destruct v; try destruct v; eauto.
Qed. 

Lemma idx_miss1: forall env i l,
  i >= lengthr env ->
  subst_tm_all l env (tvar i) = (tvar (i-(lengthr env))).
Proof.
  intros env. eapply idx_miss; eauto. 
Qed. 

Lemma shiftz_id_ty: forall t,
  shift_ty 0 t = t.
Proof.
  intros. induction t; simpl; eauto; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; eauto.
Qed.

Lemma shiftz_id: forall t,
  shift_tm 0 t = t.
Proof.
  intros. induction t; simpl; eauto; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; eauto; try rewrite shiftz_id_ty; eauto.
Qed.


Lemma shift_add_ty: forall t l1 l2,
  shift_ty l1 (shift_ty l2 t) = shift_ty (l2+l1) t.
Proof.
  intros. induction t; simpl; eauto; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; eauto.
  rewrite plus_assoc. eauto.
Qed.

Lemma shift_add: forall t l1 l2,
  shift_tm l1 (shift_tm l2 t) = shift_tm (l2+l1) t.
Proof.
  intros. induction t; simpl; eauto; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; eauto; try rewrite shift_add_ty; eauto.
  rewrite plus_assoc. eauto.
Qed.

Lemma subst_shift_id_ty: forall t u l,
  subst u (shift_ty (S l) t) = shift_ty l t.
Proof.
  intros t. induction t; intros; simpl; eauto.
  - rewrite IHt1. rewrite IHt2. eauto.
  - rewrite IHt1. rewrite IHt2. eauto. 
  - assert (beq_nat (i + S l) 0 = false). eapply beq_nat_false_iff. omega. rewrite H.
    assert (i+(S l)-1=i+l). omega. rewrite H0; eauto.
Qed.

Lemma subst_shift_id_ty1: forall t u l,
  subst_ty u (shift_tm (S l) t) = shift_tm l t.
Proof.
  intros t. induction t; intros; simpl; eauto.
  - assert (beq_nat (i + S l) 0 = false). eapply beq_nat_false_iff. omega. rewrite H.
    assert (i+(S l)-1=i+l). omega. rewrite H0; eauto.
  - rewrite IHt. rewrite subst_shift_id_ty. eauto. 
  - rewrite IHt1. rewrite IHt2. eauto. 
  - rewrite IHt. rewrite subst_shift_id_ty. eauto. 
  - rewrite IHt. rewrite subst_shift_id_ty. eauto.
  - rewrite subst_shift_id_ty. eauto. 
Qed.

Lemma subst_shift_id: forall t u l,
  subst_tm u (shift_tm (S l) t) = shift_tm l t.
Proof.
  intros t. induction t; intros; simpl; eauto.
  - assert (beq_nat (i + S l) 0 = false). eapply beq_nat_false_iff. omega. rewrite H.
    assert (i+(S l)-1=i+l). omega. rewrite H0; eauto.
  - rewrite IHt. rewrite subst_shift_id_ty. eauto. 
  - rewrite IHt1. rewrite IHt2. eauto. 
  - rewrite IHt. rewrite subst_shift_id_ty. eauto. 
  - rewrite IHt. rewrite subst_shift_id_ty. eauto.
  - rewrite subst_shift_id_ty. eauto. 
Qed.

Lemma subst_ty_tm: forall t u,
  subst_tm (tty u) t = subst_ty u t.
Proof.
  intros t. induction t; intros; simpl; eauto.
  - rewrite IHt. eauto. 
  - rewrite IHt1. rewrite IHt2. eauto.
  - rewrite IHt. eauto.
  - rewrite IHt. eauto.
Qed. 



Lemma idx_miss2: forall env i v l,
  i < lengthr env ->
  subst_tm_all l (vcons v env) (tvar i) = subst_tm_all l env (tvar i).
Proof.
  intros env. induction env.
  - intros. inversion H.
  - intros. simpl in H.
    case_eq (beq_nat i (lengthr env)); intros E.
    + 
      assert (beq_nat (i - lengthr env) 0 = true) as E1.
      eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.

      simpl. rewrite idx_miss1. rewrite idx_miss1. simpl. rewrite E1.

      destruct v0; destruct v; eauto.

      simpl. rewrite subst_shift_id. eauto. rewrite subst_shift_id_ty. eauto.
      simpl. rewrite subst_shift_id. eauto. rewrite subst_shift_id_ty. eauto.
      simpl. rewrite subst_shift_id_ty. eauto.
      simpl. rewrite subst_shift_id. eauto. rewrite subst_shift_id_ty. eauto.
      simpl. rewrite subst_shift_id. eauto. rewrite subst_shift_id_ty. eauto.
      simpl. rewrite subst_shift_id_ty. eauto. 

      simpl. rewrite subst_shift_id_ty. eauto. rewrite shift_add_ty. rewrite plus_comm.
      rewrite subst_shift_id_ty1. eauto. 
      simpl. rewrite subst_shift_id_ty. eauto. rewrite shift_add_ty. rewrite plus_comm. 
      rewrite subst_shift_id_ty1. eauto. 
      simpl. rewrite subst_shift_id_ty. eauto. 
      
      eapply beq_nat_true_iff in E. omega.
      eapply beq_nat_true_iff in E. omega.

    + assert (i < lengthr env). rewrite beq_nat_false_iff in E. omega.
      remember (vcons v env) as env1. simpl.
      subst env1. rewrite IHenv. rewrite IHenv.

      destruct v0.
      eapply (IHenv i (vabs v0 t t0)). eauto.
      eapply (IHenv i (vtabs v0 t t0)). eauto.
      eapply (IHenv i (vty v0 t)). eauto.
      eauto.
      eauto. 
Qed. 


Lemma idx_hit: forall env i,
  i < lengthr env ->
  subst_tm_res (Some (indexr i env)) = Some (Some (subst_tm_all 0 env (tvar i))).
Proof.
  intros env. induction env.
  - intros. inversion H.
  - intros.
    simpl in H. simpl.
    case_eq (beq_nat i (lengthr env)); intros E.
    + eapply beq_nat_true_iff in E.
      rewrite idx_miss1. subst i. simpl.      
      assert (beq_nat (lengthr env - lengthr env) 0 = true). eapply beq_nat_true_iff. omega.
      rewrite H0.
      assert (beq_nat (lengthr env) (lengthr env) = true). eapply beq_nat_true_iff. omega.
      destruct v.  
      rewrite shiftz_id. rewrite shiftz_id_ty. eauto.
      rewrite shiftz_id. rewrite shiftz_id_ty. eauto.
      rewrite shiftz_id_ty. eauto.
      omega.
    + assert (i <> lengthr env). eapply beq_nat_false_iff. eauto.
      assert (i < lengthr env). omega.

      specialize (IHenv _ H1). 
      rewrite <-(idx_miss2 env _ v) in IHenv . simpl in IHenv. eauto. eauto.
Qed.

(* proof of equivalence *)

Theorem big_env_subst: forall n env e1 e2,
  subst_tm_all 0 env e1 = e2 ->
  subst_tm_res (teval n env e1) = (tevals n e2).
Proof.   
  intros n. induction n.
  (* z *) intros. simpl. eauto.
  (* S n *) intros.
  destruct e1; simpl; eauto.
  - (* var *)
    assert (i < lengthr env \/ i >= lengthr env) as L. omega. 
    destruct L as [L|L].
    + (* hit *) 
      simpl in H.
      specialize (idx_hit env i L). intros IX. rewrite H in IX.
      remember (indexr i env). destruct o. 
      * simpl in IX. rewrite IX. destruct v; inversion IX; eauto.
      * inversion IX. 
    +
      specialize (idx_miss env i 0 L). intros IX. rewrite H in IX.
      destruct IX as [A B]. rewrite A. rewrite B. eauto. 

  - (* tabs *)
    assert (forall env l,
              subst_tm_all l env (tabs t e1) = 
              (tabs (subst_ty_all l env t) (subst_tm_all (S l) env e1))) as REC. {
    intros env0. induction env0; intros.
    simpl. eauto.
    simpl. destruct v; rewrite IHenv0; simpl; eauto;
    try rewrite shift_add; rewrite shift_add_ty; rewrite plus_comm; eauto. }

    rewrite REC in H. subst e2. eauto. 
  - (* tapp *)
    assert (forall env l,
              subst_tm_all l env (tapp e1_1 e1_2) = 
              (tapp (subst_tm_all l env e1_1) (subst_tm_all l env e1_2))) as REC. {
    intros env0. induction env0; intros.
    simpl. eauto.
    simpl. destruct v; rewrite IHenv0; simpl; eauto. }

    rewrite REC in H. subst e2.
    
    assert (subst_tm_res (teval n env e1_2) = tevals n (subst_tm_all 0 env e1_2)) as HF. eapply IHn; eauto. 
    assert (subst_tm_res (teval n env e1_1) = tevals n (subst_tm_all 0 env e1_1)) as HX. eapply IHn; eauto.
    rewrite <-HF. rewrite <-HX. simpl. 

    remember ((teval n env e1_2)) as A.
    destruct A as [[|]|]; simpl.
    * remember ((teval n env e1_1)) as B.
      destruct B as [[|]|]; simpl. 
      { destruct v0; destruct v; simpl; eauto.
        eapply IHn. simpl. rewrite shiftz_id. rewrite shiftz_id_ty. eauto.
        eapply IHn. simpl. rewrite shiftz_id. rewrite shiftz_id_ty. eauto.
        eapply IHn. simpl. rewrite subst_ty_tm. rewrite shiftz_id_ty. eauto. 
      }
      destruct v; eauto.
      destruct v; eauto.  
    * eauto.
    * eauto.
  - (* ttabs *)
    assert (forall env l,
              subst_tm_all l env (ttabs t e1) = 
              (ttabs (subst_ty_all l env t) (subst_tm_all (S l) env e1))) as REC. {
    intros env0. induction env0; intros.
    simpl. eauto.
    simpl. destruct v; rewrite IHenv0; simpl; eauto;
    try rewrite shift_add; rewrite shift_add_ty; rewrite plus_comm; eauto. }

    rewrite REC in H. subst e2. eauto.
  - (* ttapp *)
    assert (forall env l,
              subst_tm_all l env (ttapp e1 t) = 
              (ttapp (subst_tm_all l env e1) (subst_ty_all l env t))) as REC. {
    intros env0. induction env0; intros.
    simpl. eauto.
    simpl. destruct v; rewrite IHenv0; simpl; eauto. }

    rewrite REC in H. subst e2.
    
    assert (subst_tm_res (teval n env e1) = tevals n (subst_tm_all 0 env e1)) as HX. eapply IHn; eauto.
    rewrite <-HX. simpl. 

    remember ((teval n env e1)) as B.
    destruct B as [[?|]|]; simpl. 
    { destruct v; simpl; eauto.
      eapply IHn. simpl. rewrite shiftz_id_ty. eauto. }
    eauto. eauto. 
  - (* dummy *)
    assert (forall env l T,
              subst_tm_all l env (tty T) = 
              (tty (subst_ty_all l env T))) as REC. {
      intros env0. induction env0; intros.
      simpl. eauto.
      simpl. destruct v; rewrite IHenv0; simpl; eauto;
             try rewrite shift_add; rewrite shift_add_ty; rewrite plus_comm; eauto. }

    rewrite REC in H. subst e2. eauto. 
Qed.


(* ### Equivalence big-step subst <-> small-step subst ### *)


Lemma app_inv: forall nu t1 t2 t3,
  tevals nu (tapp t1 t2) = Some (Some t3) ->
  exists T ty v2 nv, nu = S nv /\
                     tevals nv t1 = Some (Some (tabs T ty)) /\
                     tevals nv t2 = Some (Some v2) /\
                     tevals nv (subst_tm v2 ty) = Some (Some t3).
Proof.
  intros. destruct nu. inversion H. 
  simpl in H.
  remember (tevals nu t2) as rx.
  destruct rx. destruct o.
  remember (tevals nu t1) as rf.
  destruct rf. destruct o.

  destruct t0; inversion H; repeat eexists; eauto.
  inversion H. inversion H. inversion H. inversion H.
Qed.

Lemma tapp_inv: forall nu t1 t2 t3,
  tevals nu (ttapp t1 t2) = Some (Some t3) ->
  exists T ty nv, nu = S nv /\
                     tevals nv t1 = Some (Some (ttabs T ty)) /\
                     tevals nv (subst_ty t2 ty) = Some (Some t3).
Proof.
  intros. destruct nu. inversion H. 
  simpl in H.
  remember (tevals nu t1) as rf.
  destruct rf. destruct o.

  destruct t; inversion H; repeat eexists; eauto.
  inversion H. inversion H. 
Qed.


Lemma eval_stable: forall n t1 v j,
  tevals n t1 = Some v ->
  j >= n ->
  tevals j t1 = Some v.
Proof.
  intros n. induction n; intros. inversion H.
  destruct j. inversion H0.
  destruct t1; eauto.
  - simpl in H. simpl. 
    remember (tevals n t1_2) as rx.
      destruct rx. destruct o.
      rewrite (IHn _ (Some t)). 
      remember (tevals n t1_1) as rf.
      destruct rf. destruct o.
      rewrite (IHn _ (Some t0)).
      destruct t0; eauto; eapply IHn; eauto; omega.
      destruct t0; eauto; eapply IHn; eauto; omega.
      omega.
      rewrite (IHn _ None). eauto. eauto. omega.
      inversion H. 
      
      eauto. omega.
      inversion H. rewrite (IHn _ None). eauto. eauto. omega.
      inversion H.
 - simpl in H. simpl. 
    remember (tevals n t1) as rf.
      destruct rf. destruct o.
      rewrite (IHn _ (Some t0)). 
      destruct t0; eauto; eapply IHn; eauto; omega.
      destruct t0; eauto; eapply IHn; eauto; omega.
      omega.
      rewrite (IHn _ None). eauto. eauto. omega.
      inversion H. 
Qed.



Lemma value_eval: forall t1,
   value t1 ->
   forall nu, nu >= 1 -> tevals nu t1 = Some (Some t1).
Proof.
  intros. destruct nu. inversion H0. inversion H; eauto.
Qed.


Lemma step_eval: forall t1 t2,
  step t1 t2 ->
  forall t3 nu, tevals nu t2 = Some (Some t3) ->
  tevals (S nu) t1 = Some (Some t3).
Proof.
  intros ? ? ?. induction H; intros.
  - (* AppAbs *)
    simpl.
    assert (nu >= 1). destruct nu. inversion H0. omega. 
    rewrite (value_eval v).
    rewrite (value_eval (tabs T1 t12)).
    eapply H0; omega. constructor.
    eauto. eauto. eauto. 
  - (* App1 *)
    simpl. eapply app_inv in H0.
    repeat destruct H0 as [? H0].
    destruct H0 as [N [E1 [E2 E3]]].
    subst nu. eapply IHstep in E1.
    eapply eval_stable in E2.
    rewrite E1. rewrite E2. eapply eval_stable. eapply E3. eauto. eauto. 
  - (* App2 *)
    simpl. eapply app_inv in H1.
    repeat destruct H1 as [? H1].
    destruct H1 as [N [E1 [E2 E3]]].
    subst nu. eapply IHstep in E2.
    eapply eval_stable in E1.
    rewrite E1. rewrite E2. eapply eval_stable. eapply E3. eauto. eauto.
Qed.
    
  
(* proof of equivalence: small-step implies big-step *)

Theorem small_to_big: forall n t1 t2,
   mstep n t1 t2 -> value t2 ->
   exists ns, tevals ns t1 = Some (Some t2).
Proof.
  intros n. induction n.
  (* z *)
  intros. inversion H; subst. 
  exists 1. eapply value_eval; eauto. 
  (* S n *) 
  intros. inversion H; subst.
  eapply IHn in H3. destruct H3.
  exists (S x). eapply step_eval; eauto.
  eauto. 
Qed.


(* proof of equivalence: big-step implies small-step *)

Lemma ms_app1 : forall n t1 t1' t2,
     mstep n t1 t1' ->
     mstep n (tapp t1 t2) (tapp t1' t2).
Proof.
  intros. induction H. constructor.
  econstructor. eapply ST_App1; eauto. eauto.
Qed.

Lemma ms_app2 : forall n t1 t2 t2',
     value t1 ->
     mstep n t2 t2' ->
     mstep n (tapp t1 t2) (tapp t1 t2').
Proof.
  intros. induction H0. constructor.
  econstructor. apply ST_App2; eauto. eauto.
Qed.

Lemma ms_trans : forall n1 n2 t1 t2 t3,
     mstep n1 t1 t2 ->
     mstep n2 t2 t3 ->
     mstep (n1+n2) t1 t3.
Proof.
  intros. induction H. eauto. 
  econstructor. eauto. eauto. 
Qed.


Theorem big_to_small: forall n t1 t2,
   tevals n t1 = Some (Some t2) ->
   exists ns, value t2 /\ mstep ns t1 t2.
Proof.
  intros n. induction n; intros. inversion H. destruct t1.
  - simpl in H. inversion H.
  - simpl in H. inversion H. eexists. split; constructor.
  - eapply app_inv in H. repeat destruct H as [? H].
    destruct H as [N [E1 [E2 E3]]]. inversion N. subst x2. 
    eapply IHn in E1. eapply IHn in E2. eapply IHn in E3.
    destruct E1 as [? [? E1]]. destruct E2 as [? [? E2]]. destruct E3 as [? [? E3]].
    eexists. split. eauto. 
    eapply ms_app1 in E1. eapply ms_app2 in E2. 
    eapply ms_trans. eapply E1.
    eapply ms_trans. eapply E2. econstructor. econstructor.
    eauto. eauto. eauto.
  - simpl in H. inversion H. eexists. split; constructor.
  - admit. (* TTAPP case *)
  - simpl in H. inversion H. eexists. split; constructor.        
Qed.
