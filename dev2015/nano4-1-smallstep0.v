(* Full safety for STLC *)
(* values well-typed with respect to runtime environment *)
(* inversion lemma structure *)
(* subtyping (in addition to nano2.v) *)

(* copied from nano4-1, making the step to small-step *)

(* first step: substitution *)


Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Module STLC.

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tloc : id -> tm
  | tabs : tm -> tm (* \f x.y *)
  | tapp : tm -> tm -> tm (* f(x) *)
.

Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : (*list vl -> *) tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.

Hint Unfold venv.
Hint Unfold tenv.

(*
Fixpoint length {X: Type} (l : list X): nat :=
  match l with
    | [] => 0
    | _::l' => 1 + length l'
  end.
*)
Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.


Definition vl2tm (v:vl): tm :=
  match v with
    | vbool true => ttrue
    | vbool false => tfalse
    | vabs ey => tabs ey
  end.
    
Inductive has_type : venv -> tenv -> tm -> ty -> Prop :=
| t_true: forall sto env,
           has_type sto env ttrue TBool
| t_false: forall sto env,
           has_type sto env tfalse TBool
| t_var: forall x sto env T1,
           index x env = Some T1 ->
           has_type sto env (tvar x) T1
| t_loc: forall x v sto env T1,
           index x sto = Some v ->
           has_type sto [] (vl2tm v) T1 ->
           has_type sto env (tloc x) T1
| t_abs: forall sto env y T1 T2,
           has_type sto (T1::(TFun T1 T2)::env) y T2 -> 
           has_type sto env (tabs y) (TFun T1 T2)
| t_app: forall sto env f x T1 T2,
           has_type sto env f (TFun T1 T2) ->
           has_type sto env x T1 ->
           has_type sto env (tapp f x) T2
.

Definition val_type S v T := has_type S [] (vl2tm v) T.

Inductive wf_sto : venv -> tenv -> Prop := 
| wfe_nil : wf_sto nil nil
| wfe_cons : forall v t vs ts,
    val_type (v::vs) v t ->
    wf_sto vs ts ->
    wf_sto (cons v vs) (cons t ts)
.

Inductive stp: venv -> tenv -> ty -> ty -> Prop :=
| stp_bool: forall S G,
    stp S G TBool TBool
| stp_fun: forall S G T1 T2 T3 T4,
    stp S G T3 T1 ->
    stp S G T2 T4 ->
    stp S G (TFun T1 T2) (TFun T3 T4)
.
    


Fixpoint subst (a:tm) (t:tm) {struct t}: tm :=
  match t with
    | ttrue => ttrue
    | tfalse => tfalse
    | tvar i => if beq_nat i 0 then a else tvar (i-1)
    | tapp t1 t2 => tapp (subst a t1) (subst a t2)
    | tabs t1 => tabs (subst a t1)
    | tloc i => tloc i
  end.


(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v

Could use do-notation to clean up syntax.
 *)

(* TODO: store + substitution *)

Definition push sto (v:vl) := (v::sto, length sto).

Fixpoint teval(n: nat)(sto: venv)(t: tm){struct n}: option (option (venv * nat)) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (push sto (vbool true)))
        | tfalse     => Some (Some (push sto (vbool false)))
        | tvar x     => Some None
        | tloc x     => Some (Some (sto,x))
        | tabs y     => Some (Some (push sto (vabs y)))
        | tapp ef ex   =>
          match teval n sto ef with
            | None => None
            | Some None => Some None
            | Some (Some (sto1,lvf)) =>
              match teval n sto1 ex with
                | None => None
                | Some None => Some None
                | Some (Some (sto2, lvx)) =>
                  match index lvx sto2, index lvf sto1 with
                    | Some vx, Some (vabs ey) =>
                      teval n sto2 (subst (tloc lvx) (subst (tloc lvf) ey))
                    | _,_ => Some None
                  end
              end
          end
      end
  end.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
Hint Constructors wf_sto.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.
Hint Unfold val_type.

Hint Resolve ex_intro.

Lemma wf_length : forall vs ts,
                    wf_sto vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  assert ((length (v::vs)) = 1 + length vs). constructor.
  assert ((length (t::ts)) = 1 + length ts). constructor.
  rewrite IHwf_sto in H1. auto.
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

(*
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
*)

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

Lemma hastp_extend : forall vs ts v1 t T,
                       has_type vs ts t T ->
                       has_type (v1::vs) ts t T.
Proof. intros. induction H; eauto.
econstructor. eapply index_extend; eauto. eauto. 
Qed.

Lemma valtp_extend : forall vs v v1 T,
                       val_type vs v T ->
                       val_type (v1::vs) v T.
Proof. intros. eapply hastp_extend. eauto. Qed.

Lemma index_extend_mult : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a++vs) = Some T.

Proof. intros. induction a. eauto. eapply index_extend. eauto. Qed.

Lemma hastp_extend_mult : forall vs ts v1 t T,
                       has_type vs ts t T ->
                       has_type (v1++vs) ts t T.
Proof. intros. induction v1. eauto. eapply hastp_extend. eauto. Qed.

Lemma valtp_extend_mult : forall vs v v1 T,
                       val_type vs v T ->
                       val_type (v1++vs) v T.
Proof. intros. induction v1. eauto. eapply hastp_extend. eauto. Qed.


(*
Lemma index_safe_ex: forall H1 G1 TF i,
             wf_sto H1 G1 ->
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
             eauto.
           SCase "miss".
             intros E.
             assert (beq_nat i (length vs) = false). eauto.
             rewrite E in H3.
             assert (exists v0, index i vs = Some v0 /\ val_type vs v0 TF) as HI. eapply IHwf_env. eauto.
           inversion HI as [v0 HI1]. inversion HI1. 
           eexists. econstructor. eapply index_extend; eauto. eapply valtp_extend; eauto.
Qed.
*)
  
Inductive res_type: venv -> option (venv * nat) -> ty -> Prop :=
| not_stuck: forall sto sto0 sto1 tenv x v T,
      index x sto = Some v ->
      val_type sto v T ->
      sto = sto1++sto0 ->
      wf_sto sto tenv ->
      res_type sto0 (Some (sto,x)) T.

Hint Constructors res_type.
Hint Resolve not_stuck.

(*
Lemma restp_extend_mult : forall vs v v1 T,
                       res_type vs v T ->
                       res_type (v1++vs) v T.
Proof.
  intros. inversion H. subst sto. 
  eapply not_stuck. eauto. eauto.rewrite index_extend_mult. eapply index_extend_mult; eauto.  eauto. instantiate (1:= nil). simpl. eauto. 
*)


(*
Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stp H1 T1 H2 T2 ->
  val_type H2 vf T2.
Proof.
  intros. inversion H; inversion H0; subst T2; subst; eauto. inversion H9. inversion H9.
  admit.
Qed.


Lemma invert_abs: forall venv vf vx T1 T2,
  val_type venv vf (TFun T1 T2) ->
  exists env tenv y T3 T4,
    vf = (vabs env y) /\ 
    wf_env env tenv /\
    has_type (T3::(TFun T3 T4)::tenv) y T4 /\
    stp venv T1 (vx::vf::env) T3 /\
    stp (vx::vf::env) T4 venv T2.
Proof.
  intros. inversion H. repeat eexists; repeat eauto. admit. admit.
Qed.
*)

(* if not a timeout, then result not stuck and well-typed *)

Lemma index_hit: forall {X: Type} vs (v:X),
  index (length vs) (v :: vs) = Some v.
Proof. 
  intros. simpl.
  assert (beq_nat (length vs) (length vs) = true).
  eapply beq_nat_true_iff. eauto.
  rewrite H. eauto.
Qed.

Lemma index_hit0: forall {X: Type} vs (v:X),
  index 0 (vs++[v]) = Some v.
Proof. 
  intros. induction vs. eauto.
  rewrite <-app_comm_cons. eapply index_extend. eauto.
Qed.

Lemma index_hit1: forall {X: Type} vs (v:X) x,
  index (S x) (vs++[v]) = index x vs.
Proof.
  intros. induction vs. eauto. 
  rewrite <-app_comm_cons.
  remember (index x vs). destruct o.
  symmetry in Heqo. eapply index_extend in Heqo. eapply index_extend in IHvs.
  rewrite Heqo. rewrite IHvs. eauto.
  simpl. rewrite <-Heqo. rewrite IHvs.
  simpl. rewrite app_length. simpl.
  assert (length vs + 1 = S (length vs)). omega. rewrite H. eauto.
Qed.



Lemma hastp_subst: forall sto x T0, 
  has_type sto [] (tloc x) T0 ->
  forall t env T,
  has_type sto (env++[T0]) t T ->
  has_type sto env (subst (tloc x) t) T.
Proof.
  intros sto x T0 H. inversion H. subst. induction t; intros; inversion H0; subst T.
  - eauto. 
  - eauto.
  - (* var *) simpl. destruct i.
    + (* hit *) simpl. subst env0. rewrite index_hit0 in H6. inversion H6. subst. eauto.
    + (* miss *) simpl. subst env0. rewrite index_hit1 in H6.
         assert (i - 0 = i) as E. omega. rewrite E. eauto.
  - (* loc *)
    simpl. eauto. 
  - (* abs *)
    simpl. eauto.
  - (* app *)
    simpl. eauto. 
Qed.



Lemma push_safe: forall sto tenv v T,
  wf_sto sto tenv ->
  val_type (v::sto) v T ->
  res_type sto (Some (push sto v)) T.
Proof.
  intros. eapply not_stuck. eapply index_hit. eauto. eauto.
  instantiate (1:= [v]). eauto. econstructor; eauto.
Qed.

Theorem full_safety : forall n e sto sto2 tenv2 res T,
  teval n (sto2++sto) e = Some res -> has_type sto [] e T -> wf_sto (sto2++sto) tenv2 ->
  res_type (sto2++sto) res T.

Proof.
  intros n. induction n.
  (* 0 *)   intros. inversion H.
  (* S n *) intros. destruct e; inversion H; inversion H0.
  
  - Case "True".  eapply push_safe; eauto.
  - Case "False". eapply push_safe; eauto.
  - Case "Var".
    inversion H6.
  - Case "Loc". 
    subst. 

    eapply not_stuck. eauto. eauto. eapply index_extend_mult; eauto.
    eapply valtp_extend_mult; eauto.
    rewrite app_nil_l. eauto. eauto.

  - Case "Abs".

    eapply push_safe; eauto. unfold val_type. unfold vl2tm. subst.
    eapply hastp_extend. eapply hastp_extend_mult. eauto.

  - Case "App".
    subst T.

    remember (teval n (sto2++sto) e1) as tf.
    destruct tf as [rf|]; try solve by inversion. 
    assert (res_type (sto2++sto) rf (TFun T1 T2)) as HRF. SCase "HRF". subst. eapply IHn; eauto.
    inversion HRF as [? ? ? ? ? vf].

    subst.

    remember (teval n (sto4 ++ sto2 ++ sto) e2) as tx.
    destruct tx as [rx|]; try solve by inversion. 
    assert (res_type (sto4 ++ sto2 ++ sto) rx T1) as HRX. SCase "HRX". subst. eapply IHn; eauto. eapply hastp_extend_mult; eauto.
    inversion HRX as [? ? ? ? ? vx].

    subst.

    rewrite H2 in H3.
    rewrite H8 in H3.

    (* inversion lemma for vf ? *)
    destruct vf. inversion H10; inversion H14; destruct b; inversion H5.
    (* now we know it's a closure, and we have has_type evidence *)

    inversion H10.
    
    assert (res_type ([] ++ sto3 ++ sto4 ++ sto2 ++ sto) res T2) as HRR.
    eapply IHn. eauto. eauto.
    eapply hastp_subst. eauto. eapply hastp_subst. eapply hastp_extend_mult. eauto.
    simpl. eauto. eapply hastp_extend_mult. eauto. eauto.

    inversion HRR as [? ? ? ? ? vr].

    eapply not_stuck. eauto. eauto. eauto. instantiate (1:= sto6 ++ [] ++ sto3 ++ sto4).
    simpl. rewrite H19. simpl. rewrite <- app_assoc. rewrite <- app_assoc. eauto.
    eauto.

Qed.

End STLC.