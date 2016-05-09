(* Full safety for STLC *)
(* values well-typed with respect to runtime environment *)
(* inversion lemma structure *)
(* subtyping (in addition to nano2.v) *)
(* this version includes a proof of totality (like in nano0-total.v *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Module STLC.

Definition id := nat.

Inductive ty : Type :=
  | TBot   : ty
  | TTop   : ty
  | TBool  : ty           
  | TFun   : ty -> ty -> ty
  | TMem   : ty -> ty
  | TSel   : nat -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
  | vbool : bool -> vl
  | vabs  : list vl -> tm -> vl
  | vty   : list vl -> ty -> vl
.

Definition venv := list vl.
Definition tenv := list ty.

Hint Unfold venv.
Hint Unfold tenv.

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.


Inductive closed: nat -> ty -> Prop :=
| cl_bot: forall k,
    closed k TBot
| cl_top: forall k,
    closed k TTop
| cl_bool: forall k,
    closed k TBool
| cl_fun: forall k T1 T2,
    closed k T1 ->
    closed k T2 ->
    closed k (TFun T1 T2)
.

Inductive stp: tenv -> ty -> ty -> Prop :=
| stp_bot: forall G1 T1,
    closed (length G1) T1 ->
    stp G1 TBot T1
| stp_top: forall G1 T1,
    closed (length G1) T1 ->
    stp G1 T1 TTop
| stp_bool: forall G1,
    stp G1 TBool TBool
| stp_fun: forall G1 T1 T2 T3 T4,
    stp G1 T3 T1 ->
    stp G1 T2 T4 ->
    stp G1 (TFun T1 T2) (TFun T3 T4)
.


Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_var: forall x env T1,
    index x env = Some T1 ->
    has_type env (tvar x) T1
| t_app: forall env f x T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env x T1 ->
    has_type env (tapp f x) T2
| t_abs: forall env y T1 T2,
    has_type (T1::env) y T2 ->
    closed (length env) (TFun T1 T2) ->       
    has_type env (tabs y) (TFun T1 T2)
| t_sub: forall env x T1 T2,
    has_type env x T1 ->
    stp env T1 T2 ->
    has_type env x T2
.





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
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (index x env)
        | tabs y     => Some (Some (vabs env y))
        | tapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vbool _)) => Some None
                | Some (Some (vty env2 T)) => Some None
                | Some (Some (vabs env2 ey)) =>
                  teval n (vx::env2) ey
              end
          end
      end
  end.



Inductive stp2: bool -> venv -> ty -> venv -> ty -> nat -> Prop :=
| stp2_bot: forall G1 G2 T n1,
    closed (length G2) T ->
    stp2 true G1 TBot G2 T (S n1)
| stp2_top: forall G1 G2 T n1,
    closed (length G1) T ->
    stp2 true G1 T G2 TTop (S n1)
| stp2_bool: forall G1 G2 n1,
    stp2 true G1 TBool G2 TBool (S n1)
| stp2_fun: forall G1 G2 T1 T2 T3 T4 n1 n2,
    stp2 false G2 T3 G1 T1 n1 ->
    stp2 false G1 T2 G2 T4 n2 ->
    stp2 true G1 (TFun T1 T2) G2 (TFun T3 T4) (S (n1+n2))
| stp2_wrapf: forall G1 G2 T1 T2 n1,
    stp2 true G1 T1 G2 T2 n1 ->
    stp2 false G1 T1 G2 T2 (S n1)
| stp2_transf: forall G1 G2 G3 T1 T2 T3 n1 n2,
    stp2 true G1 T1 G2 T2 n1 ->
    stp2 false G2 T2 G3 T3 n2 ->
    stp2 false G1 T1 G3 T3 (S (n1+n2))
.         



Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* some messy experiments ...

Inductive cls: venv -> ty -> nat -> Prop :=
| cls_bot: forall G,
    cls G TBot 1
| cls_top: forall G,
    cls G TTop 1
| cls_bool: forall G,
    cls G TBool 1
| cls_fun: forall G T1 T2 n1 n2,
    cls G T1 n1 ->
    cls G T2 n2 ->
    cls G (TFun T1 T2) (S (n1+n2))
| cls_mem: forall G T1 n1,
    cls G T1 n1 ->
    cls G (TMem T1) (S n1)
| cls_sel: forall G GX TX x n1,
    index x G = Some (vty GX TX) ->
    cls GX TX n1 ->
    cls G (TSel x) (S n1)
| cls_sel0: forall G GX TX x,
    index x G <> Some (vty GX TX) ->
    cls G (TSel x) 0
.

Inductive tree (A:Type) :=
 | Node : A -> list (tree A) -> tree A.

Lemma my_tree_ind : forall (A : Type) 
  (P : tree A -> Prop) (Pl : list (tree A) -> Prop),
  (forall a l, Pl l -> P (Node _ a l)) ->
  Pl nil ->
  (forall t l, P t -> Pl l -> Pl (t :: l)) ->
  forall t, P t.
Proof.
 intros A P Pl Hnode Hnil Hcons.
 fix my_tree_ind 1. 
 destruct t as [a l].
 apply Hnode.
 induction l as [ | t l IHl].
 apply Hnil.
 apply Hcons.
 apply my_tree_ind.
 apply IHl.
Qed.

Print my_tree_ind.


Lemma clsf: forall G T, exists k, cls G T k.
Proof.
  intros.
  induction T.
  eexists; econstructor.
  eexists; econstructor.
  eexists; econstructor.
  destruct IHT1. destruct IHT2.
  eexists. econstructor; eauto.
  destruct IHT.
  eexists. econstructor; eauto.
  remember (index n G) as r. symmetry in Heqr.
  destruct r. destruct v.
  eexists. eapply cls_sel0. eauto. rewrite Heqr. compute. intros. inversion H.
  eexists. eapply cls_sel0. eauto. rewrite Heqr. compute. intros. inversion H.
  eexists. eapply cls_sel. eauto. instantiate (1:=0). admit. (* where from ? *)
  eexists. eapply cls_sel0. eauto. rewrite Heqr. compute. intros. inversion H. 
Grab Existential Variables.
  apply TBot. apply nil. apply TBot. apply nil. apply TBot. apply nil.
 Qed.

Require Coq.Program.Wf.
Require Recdef.

(*
Function val_type0 (env:venv) (v:vl) (T:ty) {wf (clsf) T}: Prop := match v, T with
| vbool b, TBool => True
| vabs env1 y, TFun T1 T2 =>
  closed (length env) T1 /\ closed (length env) T2 /\
  (forall vx, val_type0 env vx T1 ->
              exists v, tevaln (vx::env1) y v /\ val_type0 env v T2)
| _, TTop => True (* can NOT check v with other type *)
| _,_ => False
end.
*)

(* n < S n *) 

Variable A : Type.

Variable f : A -> nat.

Print lt. 
Check lt.

Definition ltof (a b:A) := f a < f b.
Definition gtof (a b:A) := f b > f a.

Theorem well_founded_ltof : well_founded ltof.
Proof.
  red in |- *.
  cut (forall n (a:A), f a < n -> Acc ltof a).
  intros H a. apply (H (S (f a))). auto with arith.
  induction n.
  intros; absurd (f a < 0); auto with arith.
  intros a ltSma.
  apply Acc_intro.
  unfold ltof in |- *; intros b ltfafb.
  apply IHn.
  apply lt_le_trans with (f a); auto with arith.
Defined.

Inductive gl: venv -> venv -> Prop :=
| gl_tl: forall x G1,
    gl G1 (x::G1)
| gl_vty: forall GX TX G1,
    gl GX ((vty GX TX)::G1)
| gl_tl2: forall x G0 G1,
    gl G0 G1 ->
    gl G0 (x::G1)
| gl_vty2: forall GX TX G1 G0,
    gl G0 GX -> 
    gl G0 ((vty GX TX)::G1)
.

Lemma gl_trans: forall G1 G2 G3,
                  gl G1 G2 -> gl G2 G3 -> gl G1 G3.
Proof.
  intros. induction G3.
  inversion H0.
  inversion H0.
  subst.
  admit. admit. admit. admit. 
Qed.
  

Hint Constructors gl.

Function gsz (G:venv) {wf gl G} :=
       match G with
         | [] => 0
         | (vty GX TX)::tl => 1 + (gsz GX) + (gsz tl)
         | _::tl => gsz tl
       end.

intros. eapply gl_tl. 
intros. eapply gl_tl. 
intros. eapply gl_tl. 
intros. eapply gl_vty. 
(* well-founded *)
compute.
(* cut (forall n a, gl a n-> Acc gl a).
intros. eapply H. eapply gl_tl.  *)
assert (forall a n, gl a n-> Acc gl a).
intros a. induction a. intros.
constructor. intros. inversion H0.
admit.
admit.
Qed.

*)

(* rough and preliminary size measure  *)
Fixpoint size (t : vl) : nat :=
  match t with
    | vbool _ => 0
    | vabs _ _ => 0
    | vty l _ =>
      1 + (fix size_l (l : venv) : nat :=
             match l with
               | nil => 0
               | h::r => size h + size_l r
             end) l
  end.

Fixpoint tsz (G:venv) (T:ty) {struct T} :=
  match T with
    | TBot => 1
    | TTop => 1
    | TBool => 1
    | TFun T1 T2 => S (tsz G T1 + tsz G T2)
    | TMem T1 => S (tsz G T1)
    | TSel x => match index x G with
                  | Some v => size v
                  | None => 0
                end
  end.

(* this does not hold currently!! *)
Lemma tsz_indir: forall GX TX,
  tsz GX TX < size (vty GX TX).
Proof. admit. Qed. 
  



Require Coq.Program.Wf.

Program Fixpoint val_type0 (env:venv) (v:vl) (T:ty) {measure (tsz env T)}: Prop :=
  match v,T with
    | vbool b, TBool =>
      True
    | vabs env1 y, TFun T1 T2 =>
      closed (length env) T1 /\ closed (length env) T2 /\
      (forall vx, val_type0 env vx T1 ->
                  exists v, tevaln (vx::env1) y v /\ val_type0 env v T2)
    | vty env1 TX, TMem T1 =>
      exists n1 n2, stp2 false env1 TX env T1 n1 /\ stp2 false env T1 env1 TX n2
    | _, TSel x =>
      match index x env with
        | Some (vty GX TX) => val_type0 GX v TX
        | _ => False
      end
    | _, TTop => True (* can NOT check v with other type *)
    | _,_ => False
  end.

Check val_type0_func_obligation_16.

Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed.
Next Obligation. (* TSel case *)
  simpl. rewrite <-Heq_anonymous. eapply tsz_indir. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.

Print val_type0_func.

(* 
   PROBLEM: 
   val_type0_func is incomprehensible, we cannot (easily) unfold 
   and reason about it ...

   Can we even prove inversion lemmas?
*)




(* ------------------------- NOTES -------------------------

val_type0 cannot straightforwardly be defined as inductive
family, because the (forall vx, val_type0 env vx T1 -> ... )
occurrence violates the positivity restriction.

The current definition as Fixpoint has some problems, too.
Since it recurses structurally on T, it is unclear how to
add the following desirable rules:

- v: x.T

    index y G1 = Some (vty TX) ->
    vtp G1 v TX ->
    vtp G1 v (TSel y)

- v: { z => T }

    vtp G1 v (open 0 (TVar true x) T2) ->
    closed 0 (length G1) T2 ->
    vtp G1 v (TBind T2)

- v: (x:T1) -> T2^x

    subst x in T2

Another concern is what to do if stp2 needs to use 
val_type0 internally (for T < x.L < U).

Ideas:

1) can we define a more complex size measure on types?
   (to exclude recursion through x.T)
2) can stp2 get away with a restricted version of vtp?
   (stp2 only needs type members, not functions)

--------------------------------------------------------- *)


Inductive val_type : venv -> vl -> ty -> Prop :=
| v_sub: forall G1 T1 G2 T2 v,
    val_type0 G1 v T1 ->
    (exists n, stp2 true G1 T1 G2 T2 n) ->
    val_type G2 v T2
.

Inductive wf_env : venv -> tenv -> Prop := 
| wfe_nil : wf_env nil nil
| wfe_cons : forall v t vs ts,
    val_type vs v t ->
    wf_env vs ts ->
    wf_env (cons v vs) (cons t ts)
.

Definition stpd2 m G1 T1 G2 T2 := exists n, stp2 m G1 T1 G2 T2 n.

Hint Constructors stp2.

Ltac ep := match goal with
             | [ |- stp2 ?M ?G1 ?T1 ?G2 ?T2 ?N ] => assert (exists (n:nat), stp2 M G1 T1 G2 T2 n) as EEX
           end.

Ltac eu := match goal with
             | H: stpd2 _ _ _ _ _ |- _ => destruct H as [? H]
           end.

Lemma stpd2_bot: forall G1 G2 T,
    closed (length G2) T ->
    stpd2 true G1 TBot G2 T.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_top: forall G1 G2 T,
    closed (length G1) T ->
    stpd2 true G1 T G2 TTop.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_bool: forall G1 G2,
    stpd2 true G1 TBool G2 TBool.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_fun: forall G1 G2 T1 T2 T3 T4,
    stpd2 false G2 T3 G1 T1 ->
    stpd2 false G1 T2 G2 T4 ->
    stpd2 true  G1 (TFun T1 T2) G2 (TFun T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.

Lemma stpd2_wrapf: forall G1 G2 T1 T2,
    stpd2 true G1 T1 G2 T2 ->
    stpd2 false G1 T1 G2 T2.
Proof. intros. repeat eu. eexists. eauto. Qed.
Lemma stpd2_transf: forall G1 G2 G3 T1 T2 T3,
    stpd2 true G1 T1 G2 T2 ->
    stpd2 false G2 T2 G3 T3 ->
    stpd2 false G1 T1 G3 T3.
Proof. intros. repeat eu. eexists. eauto. Qed.



Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
Hint Constructors stp2.
Hint Constructors val_type.
Hint Constructors wf_env.

Hint Unfold stpd2.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.


Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.





Lemma wf_length : forall vs ts,
                    wf_env vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  assert ((length (v::vs)) = 1 + length vs). constructor.
  assert ((length (t::ts)) = 1 + length ts). constructor.
  rewrite IHwf_env in H1. auto.
Qed.

Hint Immediate wf_length.

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

Lemma index_exists : forall X vs n,
                       n < length vs ->
                       exists (T:X), index n vs = Some T.
Proof.
  intros X vs. induction vs.
  Case "nil". intros. inversion H.
  Case "cons".
  intros. inversion H.
  SCase "hit".
  assert (beq_nat n (length vs) = true) as E. eapply beq_nat_true_iff. eauto.
  simpl. subst n. rewrite E. eauto.
  SCase "miss".
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff. omega.
  simpl. rewrite E. eapply IHvs. eauto.
Qed.


Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply index_max. eauto.
  assert (n <> length vs). omega.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff; eauto.
  unfold index. unfold index in H. rewrite H. rewrite E. reflexivity.
Qed.


Lemma closed_extend : forall X (a:X) G T,
                       closed (length G) T ->
                       closed (length (a::G)) T.
Proof.
  intros. induction T; inversion H;  econstructor; eauto.
Qed.


Lemma stp2_extend : forall m v1 G1 G2 T1 T2 n,
                      stp2 m G1 T1 G2 T2 n ->
                      stp2 m (v1::G1) T1 G2 T2 n /\
                      stp2 m G1 T1 (v1::G2) T2 n /\
                      stp2 m (v1::G1) T1 (v1::G2) T2 n.
Proof.
  intros. induction H; try solve [repeat split; econstructor; try eauto;
          try eapply IHstp2; eauto;
          try eapply index_extend; eauto; try eapply closed_extend; eauto;
          try eapply IHstp2_1; try eapply IHstp2_2;
            try eapply IHstp2_3; try eapply IHstp2_4].

  (* trans case left *)
  
  repeat split; eapply stp2_transf; try eapply IHstp2_1; eauto; try eapply IHstp2_2; eauto.
Qed.

Lemma stpd2_extend : forall m v1 G1 G2 T1 T2,
                      stpd2 m G1 T1 G2 T2 ->
                      stpd2 m (v1::G1) T1 G2 T2 /\
                      stpd2 m G1 T1 (v1::G2) T2 /\
                      stpd2 m (v1::G1) T1 (v1::G2) T2.
Proof.
  intros. repeat eu. repeat split; eexists; eapply stp2_extend; eauto.
Qed.


Lemma stp2_extend1 : forall m v1 G1 G2 T1 T2 n, stp2 m G1 T1 G2 T2 n -> stp2 m (v1::G1) T1 G2 T2 n.
Proof. intros. eapply stp2_extend. eauto. Qed.

Lemma stp2_extend2 : forall m v1 G1 G2 T1 T2 n, stp2 m G1 T1 G2 T2 n -> stp2 m G1 T1 (v1::G2) T2 n.
Proof. intros. eapply stp2_extend. eauto. Qed.

Lemma stpd2_extend1 : forall m v1 G1 G2 T1 T2, stpd2 m G1 T1 G2 T2 -> stpd2 m (v1::G1) T1 G2 T2.
Proof. intros. eapply stpd2_extend. eauto. Qed.

Lemma stpd2_extend2 : forall m v1 G1 G2 T1 T2, stpd2 m G1 T1 G2 T2 -> stpd2 m G1 T1 (v1::G2) T2.
Proof. intros. eapply stpd2_extend. eauto. Qed.



Lemma stp_closed : forall G1 T1 T2,
                      stp G1 T1 T2 ->
                      closed (length G1) T1 /\
                      closed (length G1) T2.
Proof.
  intros. induction H; repeat split; try  econstructor; try eapply IHstp1; try eapply IHstp2; eauto; try eapply IHstp; eauto; try eapply index_max; eauto.
  (* destruct IHstp. inversion H1. eauto.
  destruct IHstp2. inversion H3. eauto. *)
Qed.



Lemma stpd2_closed : forall m G1 G2 T1 T2,
                      stpd2 m G1 T1 G2 T2 ->
                      closed (length G1) T1 /\
                      closed (length G2) T2.
Proof.
  intros. eu. induction H; repeat split; try  econstructor; try eapply IHstp2_1; try eapply IHstp2_2; eauto; try eapply IHstp2; eauto; try eapply index_max; eauto.
  (* destruct IHstp2. inversion H1. eauto.
  eapply IHstp2_4. *)
Qed.

Lemma stpd2_closed1 : forall m G1 G2 T1 T2,
                      stpd2 m G1 T1 G2 T2 ->
                      closed (length G1) T1.
Proof. intros. eapply (stpd2_closed m G1 G2); eauto. Qed.

Lemma stpd2_closed2 : forall m G1 G2 T1 T2,
                      stpd2 m G1 T1 G2 T2 ->
                      closed (length G2) T2.
Proof. intros. eapply (stpd2_closed m G1 G2); eauto. Qed.



Lemma valtp0_closed : forall G1 v T,
                       val_type0 G1 v T ->
                       closed (length G1) T.
Proof.
  intros.
  induction T; simpl in H; destruct v; try (solve by inversion); ev; econstructor; eauto.
  unfold val_type0 in H. unfold val_type0_func in H.
  compute in H.
  simpl in H. 
Qed.

Lemma valtp_extend : forall vs v v1 T,
                       val_type vs v T ->
                       val_type (v1::vs) v T.
Proof.
  intros. induction H; econstructor; eauto; try eapply stpd2_extend; eauto; try eapply index_extend; eauto. 
Qed.



Lemma index_safe_ex: forall H1 G1 TF i,
             wf_env H1 G1 ->
             index i G1 = Some TF ->
             exists v, index i H1 = Some v /\ val_type H1 v TF.
Proof. intros. induction H.
       Case "nil". inversion H0.
       Case "cons". inversion H0.
         case_eq (beq_nat i (length ts)).
           SCase "hit".
             intros E.
             rewrite E in H3. inversion H3. subst t.
             assert (beq_nat i (length vs) = true). eauto.
             assert (index i (v :: vs) = Some v). eauto.  unfold index. rewrite H2. eauto.
             eauto using valtp_extend.
           SCase "miss".
             intros E.
             assert (beq_nat i (length vs) = false). eauto.
             rewrite E in H3.
             assert (exists v0, index i vs = Some v0 /\ val_type vs v0 TF) as HI. eapply IHwf_env. eauto.
           inversion HI as [v0 HI1]. inversion HI1. 
           eexists. econstructor. eapply index_extend; eauto. eapply valtp_extend; eauto.
Qed.

  
Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.


Lemma stpd2_refl: forall G1 T1,
  closed (length G1) T1 ->
  stpd2 true G1 T1 G1 T1.
Proof.
  intros. induction T1; inversion H.
  - Case "bool". eapply stpd2_bool; eauto.
  - Case "fun". eapply stpd2_fun; try eapply stpd2_wrapf; eauto.
  - Case "bot". exists 1. eauto.
  - Case "top". exists 1. eauto.
Qed.


Lemma stpd2_reg1 : forall m G1 G2 T1 T2,
                      stpd2 m G1 T1 G2 T2 ->
                      stpd2 true G1 T1 G1 T1.
Proof.
  intros. eapply stpd2_refl. eapply (stpd2_closed m G1 G2). eauto.
Qed.

Lemma stpd2_reg2 : forall m G1 G2 T1 T2,
                      stpd2 m G1 T1 G2 T2 ->
                      stpd2 true G2 T2 G2 T2.
Proof.
  intros. eapply stpd2_refl. eapply (stpd2_closed m G1 G2). eauto.
Qed.

Lemma valtp0_reg : forall G2 T2 v,
                      val_type0 G2 v T2 ->
                      stpd2 true G2 T2 G2 T2.
Proof.
  intros. eapply stpd2_refl. eapply valtp0_closed. eauto.
Qed.



Lemma stpd2_trans_axiom_aux: forall n, forall G1 G2 G3 T1 T2 T3 n1,
  stp2 false G1 T1 G2 T2 n1 -> n1 < n ->
  stpd2 false G2 T2 G3 T3 ->
  stpd2 false G1 T1 G3 T3.
Proof.
  intros n. induction n; intros; try omega; repeat eu; subst; inversion H; subst.
  - Case "wrapf". eapply stpd2_transf. eexists. eauto. eexists. eauto. 
  - Case "transf". eapply stpd2_transf. eexists. eauto. eapply IHn. eauto. omega. eexists. eauto.
Qed.



Lemma stp2_trans_axiom: forall m G1 G2 G3 T1 T2 T3,
  stpd2 m G1 T1 G2 T2 -> 
  stpd2 false G2 T2 G3 T3 ->
  stpd2 false G1 T1 G3 T3.
Proof.
  intros. destruct m; eu; eu; eapply stpd2_trans_axiom_aux; eauto.
Qed.


Lemma stp2_trans: forall n, forall m G1 G2 G3 T1 T2 T3 n1 n2,
  stp2 m G1 T1 G2 T2 n1 -> 
  stp2 true G2 T2 G3 T3 n2 ->
  n1 < n ->
  stpd2 true G1 T1 G3 T3.
Proof.
  intros n. induction n; intros. solve by inversion.
  inversion H.
  - Case "bot". eapply stpd2_bot; eauto. eapply stpd2_closed2; eauto.
  - Case "top". inversion H0; subst; try solve by inversion.
    + SCase "top". eapply stpd2_top; eauto.
  - Case "bool". inversion H0; subst; try solve by inversion.
    + SCase "top". eapply stpd2_top; eauto. econstructor.
    + SCase "bool". eapply stpd2_bool; eauto.
  - Case "fun". inversion H0; subst; try solve by inversion.
    + SCase "top". eapply stpd2_top; eauto. eapply stpd2_closed1; eauto.
    + SCase "fun". inversion H14. subst. eapply stpd2_fun; eapply stp2_trans_axiom; eauto.
  - Case "wrapf".
    subst. eapply IHn. eapply H2. eapply H0. omega.
  - Case "transf".
    assert (stpd2 true G4 T4 G3 T3). eapply IHn. eapply H3. eapply H0. omega.
    eu. subst. eapply IHn. eapply H2. eauto. omega.
Qed.

Lemma stpd2_trans: forall m G1 G2 G3 T1 T2 T3,
  stpd2 m G1 T1 G2 T2 ->
  stpd2 true G2 T2 G3 T3 ->
  stpd2 true G1 T1 G3 T3.
Proof.
  intros. repeat eu. eapply stp2_trans; eauto.
Qed.

Lemma stp_to_stpd2: forall G1 T1 T2,
  stp G1 T1 T2 ->
  forall GX, wf_env GX G1 -> 
  stpd2 true GX T1 GX T2.
Proof.
  intros G1 T1 T2 H. induction H; intros.
  - Case "bot". eapply stpd2_bot; eauto. rewrite (wf_length GX G1); eauto.
  - Case "top". eapply stpd2_top; eauto. rewrite (wf_length GX G1); eauto.
  - Case "bool". eapply stpd2_bool; eauto.
  - Case "fun".  eapply stpd2_fun; eapply stpd2_wrapf; eauto.
Qed.

Lemma valtp0_widen: forall n, forall m n1 vf H1 H2 T1 T2,
  val_type0 H1 vf T1 ->
  stp2 m H1 T1 H2 T2 n1 -> n1 < n ->
  val_type0 H2 vf T2.
Proof.
  intros n. induction n; intros. omega. 
  inversion H0; subst.
  - Case "Bot". compute in H. destruct vf; inversion H.
  - Case "Top". destruct vf; compute; eauto.
  - Case "Bool". destruct vf; compute; eauto.
  - Case "Fun". destruct vf. simpl in H. inversion H.
    simpl in H. ev. simpl.
    split. eapply stpd2_closed1. eauto.
    split. eapply stpd2_closed2. eauto. 
    intros.
    specialize (H7 vx).
    eapply IHn in H8.
    specialize (H7 H8).
    ev.
    exists x. split. eauto.
    eapply IHn. eauto. eauto. omega.
    eauto.
    omega.
  - Case "wrapf".
    eapply IHn. eauto. eapply H4. omega.
  - Case "transf".
    assert (val_type0 G2 vf T3). eapply IHn; eauto. omega.
    eapply IHn; eauto. omega. 
Qed.


Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stpd2 true H1 T1 H2 T2 ->
  val_type H2 vf T2.
Proof.
  intros.  inversion H.
  - econstructor; eauto. eapply stpd2_trans; eauto.
Qed.

Lemma restp_widen: forall vf H1 H2 T1 T2,
  res_type H1 vf T1 ->
  stpd2 true H1 T1 H2 T2 ->
  res_type H2 vf T2.
Proof.
  intros. inversion H. eapply not_stuck. eapply valtp_widen; eauto.
Qed.


Lemma cvaltp: forall venv vf T1,
  val_type0 venv vf T1 ->
  val_type venv vf T1.
Proof.
  intros. econstructor. eauto. eapply valtp0_reg. eauto. 
Qed.

Lemma invert_abs: forall venv vf T1 T2,
  val_type venv vf (TFun T1 T2) ->
  exists env y,
    vf = (vabs env y) /\ 
    (forall vx : vl,
       val_type venv vx T1 ->
       exists v : vl, tevaln (vx::env) y v /\ val_type venv v T2).
Proof.
  intros. inversion H. ev. subst.
  assert (val_type0 venv0 vf (TFun T1 T2)). eapply valtp0_widen;eauto. 
  destruct vf. inversion H2.
  exists l. exists t. split. eauto.
  intros. simpl in H2. ev. 
  inversion H3. subst.
  assert (val_type0 venv0 vx T1). ev. eapply valtp0_widen; eauto.
  specialize (H5 vx H8).
  ev. eexists. split. eauto. eapply cvaltp; eauto. 
Qed.


(* if not a timeout, then result not stuck and well-typed *)

Theorem full_total_safety : forall e tenv T,
  has_type tenv e T -> forall venv, wf_env venv tenv ->
  exists v, tevaln venv e v /\ val_type venv v T.
Proof.
  intros ? ? ? W.
  induction W; intros ? WFE.

  - Case "True". eexists. split.
    exists 0. intros. destruct n. omega. simpl. eauto. eapply cvaltp. simpl. eauto. 
  - Case "False". eexists. split.
    exists 0. intros. destruct n. omega. simpl. eauto. eapply cvaltp. simpl. eauto. 

  - Case "Var". 
    destruct (index_safe_ex venv0 env T1 x) as [v IV]. eauto. eauto. 
    inversion IV as [I V]. 

    exists v. split. exists 0. intros. destruct n. omega. simpl. rewrite I. eauto. eapply V.

  - Case "App".
    destruct (IHW1 venv0 WFE) as [vf [IW1 HVF]].
    destruct (IHW2 venv0 WFE) as [vx [IW2 HVX]].
    
    eapply invert_abs in HVF.
    destruct HVF as [venv1 [y [HF IHF]]].

    destruct (IHF vx HVX) as [vy [IW3 HVY]].

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

  - Case "Abs".
    erewrite <-(wf_length venv0 env WFE) in H. inversion H; subst. 
    eexists. split. exists 0. intros. destruct n. omega. simpl. eauto.
    eapply cvaltp. simpl. repeat split; eauto.  intros. 
    assert (stpd2 true venv0 T1 (vx::venv0) T1). eapply stpd2_extend2. eapply stpd2_refl; eauto. eu.
    assert (stpd2 true (vx::venv0) T2 venv0 T2). eapply stpd2_extend1. eapply stpd2_refl; eauto. eu.
    assert (val_type0 (vx::venv0) vx T1). eapply valtp0_widen; eauto. 
    assert (wf_env (vx::venv0) (T1::env)). eapply wfe_cons; eauto. eapply cvaltp; eauto.
    specialize (IHW (vx::venv0) H6). ev.
    assert (val_type0 venv0 x1 T2). inversion H8. subst. ev. eapply valtp0_widen. eauto. eapply stp2_transf. eauto. eauto. eauto.
    (* we have all pieces ... *)
    eexists. split; eauto.
  - Case "Sub".
    specialize (IHW venv0 WFE). ev. eexists. split. eauto.
    eapply valtp_widen. eauto. eapply stp_to_stpd2; eauto.
Qed.

End STLC.