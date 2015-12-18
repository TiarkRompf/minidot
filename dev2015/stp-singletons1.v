(* Clean-slate look at subtyping relation based on *)
(* singleton types (single env) *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Lt.

Module STLC.

Definition id := nat.

Inductive ty : Type :=
  | TBot   : ty
  | TTop   : ty
  | TBool  : ty           
  | TFun   : ty -> ty -> ty
  | TVar   : bool -> id -> ty
  | TVarB  : id -> ty                   
  | TMem   : ty -> ty -> ty (* intro *)
  | TSel   : ty -> ty (* elim *)
  | TBind  : ty -> ty                   
.

Inductive vl : Type :=
  | vbool : bool -> vl
  | vabs  : ty -> ty -> vl
  | vty   : ty -> vl
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


(* closed j k means normal variables < i and < j, bound variables < k *)
Inductive closed: nat -> nat -> nat -> ty -> Prop :=
| cl_bot: forall i j k,
    closed i j k TBot
| cl_top: forall i j k,
    closed i j k TTop
| cl_bool: forall i j k,
    closed i j k TBool
| cl_fun: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TFun T1 T2)
| cl_var0: forall i j k x,
    i > x ->
    closed i j k (TVar false x)
| cl_var1: forall i j k x,
    j > x ->
    closed i j k (TVar true x)
| cl_varB: forall i j k x,
    k > x ->
    closed i j k (TVarB x)
| cl_mem: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->        
    closed i j k (TMem T1 T2)
| cl_sel: forall i j k T1,
    closed i j k T1 ->
    closed i j k (TSel T1)
| cl_bind: forall i j k T1,
    closed i j (S k) T1 ->
    closed i j k (TBind T1)
.


Fixpoint open (k: nat) (u: ty) (T: ty) { struct T }: ty :=
  match T with
    | TVar b x => TVar b x (* free var remains free. functional, so we can't check for conflict *)
    | TVarB x => if beq_nat k x then u else TVarB x
    | TTop        => TTop
    | TBot        => TBot
    | TBool       => TBool
    | TSel T1     => TSel (open k u T1)                  
    | TFun T1 T2  => TFun (open k u T1) (open k u T2)
    | TMem T1 T2  => TMem (open k u T1) (open k u T2)
    | TBind T1    => TBind (open (S k) u T1)                          
  end.

Fixpoint subst (k: nat) (U : ty) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TBool        => TBool
    | TMem T1 T2   => TMem (subst k U T1) (subst k U T2)
    | TSel T1      => TSel (subst k U T1)
    | TVarB i      => TVarB i
    | TVar true i  => TVar true i
    | TVar false i =>
      match nat_compare i k with
        | Lt => TVar false i
        | Eq => U
        | Gt => TVar false (i-1)
      end
    | TFun T1 T2   => TFun (subst k U T1) (subst k U T2)
    | TBind T2     => TBind (subst k U T2)
  end.

(*
Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TBot         => True
    | TBool        => True
    | TMem m T1 T2   => nosubst T1 /\ nosubst T2
    | TSel (varB i) m => True
    | TSel (varF i) m => True
    | TSel (varH i) m => i <> 0
    | TAll m T1 T2   => nosubst T1 /\ nosubst T2
    | TBind T2     => nosubst T2
    | TAnd T1 T2   => nosubst T1 /\ nosubst T2
    | TOr  T1 T2   => nosubst T1 /\ nosubst T2
  end.
*)



Inductive stp: tenv -> ty -> ty -> Prop :=
| stp_bot: forall G1 T,
    closed (length G1) 0 0  T ->
    stp G1 TBot T
| stp_top: forall G1 T,
    closed (length G1) 0 0 T ->
    stp G1 T TTop
| stp_bool: forall G1,
    stp G1 TBool TBool
| stp_fun: forall G1 T1 T2 T3 T4,
    stp G1 T3 T1 ->
    stp G1 T2 T4 ->
    stp G1 (TFun T1 T2) (TFun T3 T4)
| stp_mem: forall G1 T1 T2 T3 T4,
    stp G1 T3 T1 ->
    stp G1 T2 T4 ->
    stp G1 (TMem T1 T2) (TMem T3 T4)
| stp_varx: forall G1 x,
    x < length G1 ->
    stp G1 (TVar false x) (TVar false x)
(* | stp_vary: forall G1 x y,
    index x G1 = Some (TVar false y) ->
    y < length G1 ->
    stp G1 (TVar false y) (TVar false x) *)
| stp_var1: forall G1 x T1,
    index x G1 = Some T1 ->
    closed (length G1) 0 0 T1 ->
    stp G1 (TVar false x) T1
| stp_sel1: forall G1 T2 b x,
    stp G1 (TVar b x) (TMem TBot T2) ->
    stp G1 (TSel (TVar b x)) T2
| stp_sel2: forall G1 T1 b x,
    stp G1 (TVar b x) (TMem T1 TTop) ->
    stp G1 T1 (TSel (TVar b x))

.


Inductive stp2: nat -> bool -> tenv -> venv -> ty -> ty -> nat -> Prop :=
| stp2_bot: forall m GH G1 T n1,
    closed (length GH) (length G1) 0  T ->
    stp2 m true GH G1 TBot T (S n1)
| stp2_top: forall m GH G1 T n1,
    closed (length GH) (length G1) 0 T ->
    stp2 m true GH G1 T  TTop (S n1)
| stp2_bool: forall m GH G1 n1,
    stp2 m true GH G1 TBool TBool (S n1)
| stp2_fun: forall m GH G1 T1 T2 T3 T4 n1 n2,
    stp2 m false GH G1 T3 T1 n1 ->
    stp2 m false GH G1 T2 T4 n2 ->
    stp2 m true GH G1 (TFun T1 T2) (TFun T3 T4) (S (n1+n2))
| stp2_mem: forall m GH G1 T1 T2 T3 T4 n1 n2,
    stp2 m false GH G1 T3 T1 n2 ->
    stp2 m true GH G1 T2 T4 n1 ->
    stp2 m true GH G1 (TMem T1 T2) (TMem T3 T4) (S (n1+n2))


| stp2_varx: forall m GH G1 x n1,
    x < length G1 ->
    stp2 m true GH G1 (TVar true x) (TVar true x) (S n1)
| stp2_var1: forall m GH G1 TX x T2 v n1,
    index x G1 = Some v ->
    val_type0 G1 v TX -> (* slack for: val_type G2 v T2 *)
    stp2 m true GH G1 TX T2 n1 ->
    stp2 m true GH G1 (TVar true x) T2 (S n1)
         
| stp2_var_bind2: forall m GH G1 x T2 n1 ,
    stp2 m true [] G1 (TVar true x) (open 0 (TVar true x) T2) n1 ->
    stp2 (S m) true GH G1 (TVar true x) (TBind T2) (S (n1))

(*| stp2_bind1: forall m GH G1 x T2 n1,
    stp2 m true GH G1 (TVar true x) (TBind T2) n1 ->
    stp2 m true GH G1 (TVar true x) (open 0 (TVar true x) T2) (S (n1)) *)

    
(*| stp2_varax: forall m GH G1 x n1,
    x < length GH ->
    stp2 m true GH G1 (TVar false x) (TVar false x) (S n1) *)
(* | stp2_varay: forall m GH G1 TX x1 x2 n1,
    index x1 GH = Some TX ->
    stp2 m false GH G1 TX (TVar false x2) n1 ->
    stp2 m true GH G1 (TVar false x2) (TVar false x1) (S n1) *)
(* | stp2_vary: forall m GH G1 x1 x2 n1,
    index x1 GH = Some (TVar true x2) ->
    x2 < length G1 ->
    stp2 m true GH G1 (TVar true x2) (TVar false x1) (S n1) *)
| stp2_vara1: forall m GH GU G1 TX T2 x n1,
    index x GH = Some TX ->
    GH = GU ++ [TX] ->
    x = 0 -> 
    stp2 m true [TX] G1 TX T2 n1 -> (* TEMP -- SHOULD ALLOW UP TO x *)
    stp2 m true GH G1 (TVar false x) T2 (S n1)


| stp2_strong_sel1: forall m GH G1 T2 TX b x n1,
    index x G1 = Some (vty TX) ->
    stp2 m true GH G1 TX T2 n1 ->
    stp2 m true GH G1 (TSel (TVar b x)) T2 (S n1)
| stp2_strong_sel2: forall m GH G1 T1 TX b x n1,
    index x G1 = Some (vty TX) ->
    stp2 m true GH G1 T1 TX n1 ->
    stp2 m true GH G1 T1 (TSel (TVar b x)) (S n1)

(*         
| stp2_sel1: forall m GH G1 T2 b x n1,
    stp2 (S m) false GH G1 (TVar b x) (TMem TBot T2) n1 ->
    stp2 (S m) true GH G1 (TSel (TVar b x)) T2 (S n1)
| stp2_sel2: forall m GH G1 T1 b x n1,
    stp2 (S m) true GH G1 (TVar b x) (TMem T1 TTop) n1 ->
    stp2 (S m) true GH G1 T1 (TSel (TVar b x)) (S n1)
 *)

| stp2_bindx: forall m GH G1 T1 T1' T2 T2' n1,
    stp2 m false (T1'::GH) G1 T1' T2' n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    T2' = (open 0 (TVar false (length GH)) T2) -> 
    stp2 (S m) true GH G1 (TBind T1) (TBind T2) (S n1)
         
         
| stp2_wrapf: forall m GH G1 T1 T2 n1,
    stp2 m true GH G1 T1 T2 n1 ->
    stp2 m false GH G1 T1 T2 (S n1)
| stp2_transf: forall m GH G1 T1 T2 T3 n1 n2 m2,
    stp2 m false GH G1 T1 T2 n1 ->
    stp2 m2 true GH G1 T2 T3 n2 -> m2 <= m ->
    stp2 m false GH G1 T1 T3 (S (n1+n2))
         

with wf_env : venv -> tenv -> Prop := 
| wfe_nil : wf_env nil nil
| wfe_cons : forall v t vs ts,
    val_type (v::vs) v t ->
    wf_env vs ts ->
    wf_env (cons v vs) (cons t ts)

with val_type0 : venv -> vl -> ty -> Prop :=
| v_bool: forall venv b,
    val_type0 venv (vbool b) TBool
| v_abs: forall venv T1 T2,
    val_type0 venv (vabs T1 T2) (TFun T1 T2)
| v_ty: forall venv T1,
    val_type0 venv (vty T1) (TMem T1 T1)
              
with val_type : venv -> vl -> ty -> Prop :=
| v_sub: forall G1 T1 T2 v,
    val_type0 G1 v T1 ->
    (exists n, stp2 0 true [] G1 T1 T2 n) ->
    val_type G1 v T2
.
              


Definition stpd2 m b GH G1 T1 T2 := exists n, stp2 m b GH G1 T1 T2 n.

Hint Constructors stp2.

Ltac ep := match goal with
             | [ |- stp2 ?M ?B ?GH ?G1 ?T1 ?T2 ?N ] => assert (exists (n:nat), stp2 M B GH G1 T1 T2 n) as EEX
           end.

Ltac eu := match goal with
             | H: stpd2 _ _ _ _ _ _ |- _ => destruct H as [? H]
           end.

Lemma stpd2_bot: forall m GH G1 T,
    closed (length GH) (length G1) 0 T ->
    stpd2 m true GH G1 TBot T.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_top: forall m GH G1 T,
    closed (length GH) (length G1) 0 T ->
    stpd2 m true GH G1 T TTop.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_bool: forall m GH G1,
    stpd2 m true GH G1 TBool TBool.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_fun: forall m GH G1 T1 T2 T3 T4,
    stpd2 m false GH G1 T3 T1 ->
    stpd2 m false GH G1 T2 T4 ->
    stpd2 m true  GH G1 (TFun T1 T2) (TFun T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.
Lemma stpd2_mem: forall m GH G1 T1 T2 T3 T4,
    stpd2 m false GH G1 T3 T1 ->
    stpd2 m true  GH G1 T2 T4 ->
    stpd2 m true  GH G1 (TMem T1 T2) (TMem T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.

(*
Lemma stpd2_varx: forall m GH G1 x,
    x < length G1 ->                    
    stpd2 m true GH G1 (TVar true x) (TVar true x).
Proof. intros. repeat eu. exists 1. eauto. Qed.
Lemma stpd2_var1: forall m GH G1 TX x T2 v,
    index x G1 = Some v ->
    val_type0 G1 v TX -> (* slack for: val_type G2 v T2 *)
    stpd2 m true GH G1 TX T2 ->
    stpd2 m true GH G1 (TVar true x) T2.
Proof. intros. repeat eu. eexists. eauto. Qed.
(*Lemma stpd2_var1b: forall m GH G1 GX TX G2 x x2 T2 v,
    index x G1 = Some v ->
    index x2 G2 = Some v ->
    val_type0 GX v TX -> (* slack for: val_type G2 v T2 *)
    stpd2 m true GH GX TX G2 (open 0 (TVar true x2) T2) ->
    stpd2 m true GH G1 (TVar true x) G2 (TBind T2).
Proof. intros. repeat eu. eexists. eauto. Qed.*)
Lemma stpd2_sel: forall m GH G1 T1 T2,
    stpd2 m false GH G1 T2 T1 ->
    stpd2 m true  GH G1 T1 T2 ->
    stpd2 m true  GH G1 (TSel T1) (TSel T2).
Proof. intros. repeat eu. eexists. eauto. Qed.
Lemma stpd2_red: forall m GH G1 T1 T2,
    stpd2 m true GH G1 T1 (TMem TBot T2) ->
    stpd2 m true GH G1 (TSel T1) T2.
Proof. intros. repeat eu. eexists. eauto. Qed.
Lemma stpd2_red2: forall m GH G1 TX T1 T2 T0,
    real T0 ->
    stpd2 m true GH G1 T0 T2 ->
    stpd2 m false GH G1 T2 (TMem TX TTop) ->
    stpd2 m true GH G1 T0 (TMem TX TTop) ->
    stpd2 m false GH G1 T1 TX ->
    stpd2 m true GH G1 T1 (TSel T2).
Proof. intros. repeat eu. eexists. eauto. Qed.

(*
Lemma stpd2_bindI: forall G1 G2 T2 x,
    stpd2 true G1 (TVar x) G2 (open 0 (TVar x) T2) ->
    stpd2 true G1 (TVar x) G2 (TBind T2).
Proof. intros. repeat eu. eexists. eauto. Qed. *

Lemma stpd2_bindE: forall G1 G2 T2 x,
    stpd2 true G1 (TVar x) G2 (TBind T2) ->
    stpd2 true G1 (TVar x) G2 (open 0 (TVar x) T2).
Proof. intros. repeat eu. eexists. eauto. Qed.
*)

(*Lemma stpd2_bind1: forall m GH G1 T1 T2,
    closed (length GH) (length G2) 0 T2 ->
    stpd2 m true ((G1,(open 0 (TVar false (length GH)) T1))::GH)
          G1 (TVar false (length GH)) G2 T2 ->
    stpd2 m true GH G1 (TBind T1) G2 T2.
Proof. intros. repeat eu. eexists. eauto. Qed.
*)

*)

Lemma stpd2_wrapf: forall m GH G1 T1 T2,
    stpd2 m true GH G1 T1 T2 ->
    stpd2 m false GH G1 T1 T2.
Proof. intros. repeat eu. eexists. eauto. Qed.
Lemma stpd2_transf: forall m GH G1 T1 T2 T3,
    stpd2 m false GH G1 T1 T2 ->
    stpd2 m true GH G1 T2 T3 ->
    stpd2 m false GH G1 T1 T3.
Proof. intros. repeat eu. eexists. eauto. Qed.



Hint Constructors ty.
Hint Constructors vl.


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


Lemma closed_extend : forall T X (a:X) i k G,
                       closed i (length G) k T ->
                       closed i (length (a::G)) k T.
Proof.
  intros T. induction T; intros; inversion H;  econstructor; eauto.
  simpl. omega.
Qed.

(*
Lemma stp2_extend : forall m b GH  v1 G1 G2 T1 T2 n,
                      stp2 m b GH G1 T1 G2 T2 n ->
                      stp2 m b GH (v1::G1) T1 G2 T2 n /\
                      stp2 m b GH G1 T1 (v1::G2) T2 n /\
                      stp2 m b GH (v1::G1) T1 (v1::G2) T2 n.
Proof.
  intros. induction H; try solve [repeat split; econstructor; try eauto;
          try eapply index_extend; eauto; try eapply closed_extend; eauto;
          try eapply IHstp2; eauto;
          try eapply IHstp2_1; try eapply IHstp2_2;
            try eapply IHstp2_3; try eapply IHstp2_4].
(*
  repeat split; eapply stp2_var1b. eapply index_extend; eauto. eauto. eauto.
  eauto. eauto. eapply index_extend; eauto. eauto. eapply IHstp2. eapply index_extend; eauto.
  eapply index_extend; eauto. eauto.
  eapply IHstp2.
*)
  admit. (* bind1 *)
  admit.
  admit.
  
  repeat split; eapply stp2_transf; try eapply IHstp2_1; eauto; try eapply IHstp2_2; eauto.
Qed.

Lemma stpd2_extend : forall m b GH v1 G1 G2 T1 T2,
                      stpd2 m b GH G1 T1 G2 T2 ->
                      stpd2 m b GH (v1::G1) T1 G2 T2 /\
                      stpd2 m b GH G1 T1 (v1::G2) T2 /\
                      stpd2 m b GH (v1::G1) T1 (v1::G2) T2.
Proof.
  intros. repeat eu. repeat split; eexists; eapply stp2_extend; eauto.
Qed.


Lemma stp2_extend1 : forall m b GH v1 G1 G2 T1 T2 n, stp2 m b GH G1 T1 G2 T2 n -> stp2 m b GH (v1::G1) T1 G2 T2 n.
Proof. intros. eapply stp2_extend. eauto. Qed.

Lemma stp2_extend2 : forall m b GH v1 G1 G2 T1 T2 n, stp2 m b GH G1 T1 G2 T2 n -> stp2 m b GH G1 T1 (v1::G2) T2 n.
Proof. intros. eapply stp2_extend. eauto. Qed.

Lemma stpd2_extend1 : forall m b GH v1 G1 G2 T1 T2, stpd2 m b GH G1 T1 G2 T2 -> stpd2 m b GH (v1::G1) T1 G2 T2.
Proof. intros. eapply stpd2_extend. eauto. Qed.

Lemma stpd2_extend2 : forall m b GH v1 G1 G2 T1 T2, stpd2 m b GH G1 T1 G2 T2 -> stpd2 m b GH G1 T1 (v1::G2) T2.
Proof. intros. eapply stpd2_extend. eauto. Qed.
*)


Lemma stp_closed : forall G1 T1 T2,
                      stp G1 T1 T2 ->
                      closed (length G1) 0 0 T1 /\
                      closed (length G1) 0 0 T2.
Proof.
 admit. (*   intros. induction H; repeat split; try  econstructor; try eapply IHstp1; try eapply IHstp2; eauto; try eapply IHstp; eauto; try eapply index_max; eauto.
  destruct IHstp. inversion H1. eauto.
    destruct IHstp. inversion H1. eauto. *)

Qed.



Lemma stpd2_closed : forall m b GH G1 T1 T2,
                      stpd2 m b GH G1 T1 T2 ->
                      closed (length GH) (length G1) 0 T1 /\
                      closed (length GH) (length G1) 0 T2.
Proof.
  admit. (*
  intros. eu. induction H; repeat split; try  econstructor; try eapply IHstp2_1; try eapply IHstp2_2; eauto; try eapply IHstp2; eauto; try eapply index_max; eauto.
  destruct IHstp2. inversion H1. eauto.
  eapply IHstp2_4. *)
  
Qed.

Lemma stpd2_closed1 : forall m b GH G1 T1 T2,
                      stpd2 m b GH G1 T1 T2 ->
                      closed (length GH) (length G1) 0 T1.
Proof. intros. eapply (stpd2_closed m b GH G1 T1 T2); eauto. Qed.

Lemma stpd2_closed2 : forall m b GH G1 T1 T2,
                      stpd2 m b GH G1 T1 T2 ->
                      closed (length GH) (length G1) 0 T2.
Proof. intros. eapply (stpd2_closed m b GH G1); eauto. Qed.


Lemma valtp_extend : forall vs v v1 T,
                       val_type vs v T ->
                       val_type (v1::vs) v T.
Proof.
  admit.
  (*intros. induction H; econstructor; eauto; try eapply stpd2_extend; eauto; try eapply index_extend; eauto. 
   *)
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
             eauto.
           SCase "miss".
             intros E.
             assert (beq_nat i (length vs) = false). eauto.
             rewrite E in H3.
             assert (exists v0, index i vs = Some v0 /\ val_type vs v0 TF) as HI. eapply IHwf_env. eauto.
           inversion HI as [v0 HI1]. inversion HI1. 
           eexists. econstructor. eapply index_extend; eauto. eapply valtp_extend; eauto.
Qed.

  

Lemma stpd2_refl: forall m GH G1 T1,
  closed (length GH) (length G1) 0 T1 ->
  stpd2 m true GH G1 T1 T1.
Proof.
admit. (*  intros. induction T1; inversion H.
  - Case "bot". exists 1. eauto.
  - Case "top". exists 1. eauto.
  - Case "bool". eapply stpd2_bool; eauto.
  - Case "fun". eapply stpd2_fun; try eapply stpd2_wrapf; eauto.
  - Case "var0". exists 1. eauto. 
  - Case "var1".
    assert (exists v, index i G1 = Some v) as E. eapply index_exists; eauto.
    destruct E.
    eapply stpd2_varx; eauto.
  - Case "varb". inversion H4. 
  - Case "mem". eapply stpd2_mem; try eapply stpd2_wrapf; eauto.
  - Case "sel". eapply stpd2_sel; try eapply stpd2_wrapf; eauto.
  - Case "bind".
    admit.
    
    (* don't have index & val_type0 evidence *)
    
    (*exists 3. eapply stp2_bind1. eauto. 
    eapply stp2_bind2.
    simpl. eauto.

    eapply stp2_vara1. simpl. rewrite <-beq_nat_refl. eauto. *)
    
    (* TODO: 
       stp2 m true ((G1, open 0 (TVar false (length GH)) T1) :: GH) G1
     (open 0 (TVar false (length GH)) T1) G1
     (open 0 (TVar false (length GH)) T1) 0
     *)*)
Qed.

Lemma stpd2_reg1 : forall m b GH G1 T1 T2,
                      stpd2 m b GH G1 T1 T2 ->
                      stpd2 m true GH G1 T1 T1.
Proof.
  intros. eapply stpd2_refl. eapply (stpd2_closed m b GH G1 T1 T2). eauto.
Qed.

Lemma stpd2_reg2 : forall m b GH G1 T1 T2,
                      stpd2 m b GH G1 T1 T2 ->
                      stpd2 m true GH G1 T2 T2.
Proof.
  intros. eapply stpd2_refl. eapply (stpd2_closed m b GH G1). eauto.
Qed.

(*

Lemma invert_bind1: forall n, forall venv vf T1 GX TX n1,
  val_type0 GX vf TX -> stp2 true GX TX venv (TBind T1) n1 -> n1 < n ->
  exists x n2,
    index x venv = Some vf ->
    n2 < n1 ->
    stp2 true GX TX venv (open 0 (TVar x) T1) n2.
Proof.
  intros n. induction n; intros. solve by inversion.
  inversion H; subst. 
  - Case "bool". solve by inversion.
  - Case "fun". solve by inversion.
(*   - Case "var". subst. inversion H0; subst.
    + SCase "normal".
    assert (vf = v) as A. rewrite H2 in H4. inversion H4. eauto.
    rewrite A. assert (n0 < n) as B. omega. 
    specialize (IHn venv0 v T1 GX0 TX n0 H5 H6 B).
    ev. repeat eexists; eauto. 
  (* repeat eapply IHn; eauto. omega. *)
    + SCase "bindE". eauto.
    + eauto.      *)
  - Case "mem". solve by inversion.
Qed.
*)


Lemma stp2_downgrade: forall m m2 b GH G1 T1 T2 n1,
  stp2 m b GH G1 T1 T2 n1 -> m <= m2 ->
  stp2 m2 b GH G1 T1 T2 n1.
Proof.
  admit.
Qed.

(*
Lemma stpd2_trans_axiom_aux: forall n, forall m m2 GH G1 T1 T2 T3 n1,
  stpd2 m false GH G1 T1 T2 -> 
  stp2 m2 false GH G1 T2 T3 n1 -> n1 < n -> m2 <= m ->
  stpd2 m2 false GH G1 T1 T3.
Proof.
  intros n. induction n; intros; try omega; repeat eu; subst; inversion H0; clear H0; subst.
  - Case "wrapf". eexists. eapply stp2_transf. eauto. eauto. eauto. 
  - Case "transf".
    assert (m = m2 + (m - m2)). omega.
    assert (stpd2 m false GH G1 T1 T4). eapply IHn. eauto. rewrite H0. eapply stp2_downgrade. eauto. eapply stp2_downgrade. eauto. omega. eauto. 
    eu. eexists. eapply stp2_transf. eauto. eauto. omega. 
Qed.



Lemma stp2_trans_axiom: forall m b GH G1 T1 T2 T3,
  stpd2 m false GH G1 T1 T2 -> 
  stpd2 m b GH G1 T2 T3 ->
  stpd2 m false GH G1 T1 T3.
Proof.
  intros. destruct b; eu; eu; eapply stpd2_trans_axiom_aux; eauto.
Qed.
*)


Ltac index_subst := match goal with
                      | H1: index ?x ?G = ?V1 , H2: index ?x ?G = ?V2 |- _ => rewrite H1 in H2; inversion H2; subst
                      | _ => idtac
                    end.

Ltac invty := match goal with
                | H1: TBot     = _ |- _ => inversion H1
                | H1: TBool    = _ |- _ => inversion H1
                | H1: TSel _   = _ |- _ => inversion H1
                | H1: TMem _ _ = _ |- _ => inversion H1
                | H1: TVar _ _ = _ |- _ => inversion H1
                | H1: TFun _ _ = _ |- _ => inversion H1
                | H1: TBind  _ = _ |- _ => inversion H1
                | _ => idtac
              end.

Ltac invstp_var := match goal with
  | H1: stp2 _ true _ _ TBot        (TVar _ _) _ |- _ => inversion H1
  | H1: stp2 _ true _ _ TTop        (TVar _ _) _ |- _ => inversion H1
  | H1: stp2 _ true _ _ TBool       (TVar _ _) _ |- _ => inversion H1
  | H1: stp2 _ true _ _ (TFun _ _)  (TVar _ _) _ |- _ => inversion H1
  | H1: stp2 _ true _ _ (TMem _ _)  (TVar _ _) _ |- _ => inversion H1
  | H1: val_type0 _ _ _ |- _ => inversion H1
  | _ => idtac
end.



Lemma closed_no_subst: forall T i j k TX,
   closed i j k T ->
   subst i TX T = T.
Proof.
  admit.
(*  intros T. induction T; intros; inversion H; simpl; eauto;
    try rewrite (IHT (S j) TX); eauto;
    try rewrite (IHT2 (S j) TX); eauto;
    try rewrite (IHT j TX); eauto;
    try rewrite (IHT1 j TX); eauto;
    try rewrite (IHT2 j TX); eauto.

  eapply closed_upgrade. eauto. eauto.
  subst. omega.
  subst. eapply closed_upgrade. eassumption. omega.
  subst. eapply closed_upgrade. eassumption. omega. *)
Qed.

(*
Lemma subst_open_commute: forall i j n V l T2, closed i (n+1) (j+1) (n+1) T2 -> closed 0 0 (TSel V l) ->
    subst V (open_rec j (varH (n+1)) T2) = open_rec j (varH n) (subst V T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.
*)

(* FIXME: need some closed evidence, but don't worry about it for now *)

Lemma subst_open_commute: forall T0 TX n,
  (subst n TX (open 0 (TVar false n) T0)) = open 0 TX T0.
Proof. admit. Qed.


Lemma subst_open_commute1: forall T0 x x0,
 (open 0 (TVar true x0) (subst 0 (TVar true x) T0)) 
 = (subst 0 (TVar true x) (open 0 (TVar true x0) T0)).
Proof. admit. Qed.


(*
Lemma stp2_subst: forall m b GH G1 T1 T2 TX n1,
   stp2 m b (TX::GH) G1 T1 T2 n1 ->
   stpd2 m b GH G1 (subst (length GH) TX T1) (subst (length GH) TX T2).
Proof.
  admit.
Qed.
*)


(* THIS WILL NOT WORK !!! *)
(* using stp2_transf, we increase the size to m recursively *)

(* IDEA: do not support trans for bindx, by making stp2_trans
   work only for T1 = mem, fun, var.
   Is that sufficient for induction? ---> probably yes
*)

Lemma stp2_narrow: forall m m2 b GH TX1 TX2 G1 T1 T2 n1 n2,
  stp2 m false (TX1::GH) G1 TX1 TX2 n1 ->
  stp2 m2 b (TX2::GH) G1 T1 T2 n2 -> m2 <= m ->
  stpd2 m2 b (TX1::GH) G1 T1 T2.
Proof.
  admit.
Qed.

Definition substt x T := (subst 0 (TVar true x) T).


Lemma closed_subst: forall i j k x T2,
  closed (i + 1) j k T2 ->
  closed i j k (substt x T2).
Proof. admit. Qed.



(* TODO: need to be careful will m1 and m2 !!! *)
Lemma stp2_subst_narrow: forall ml, forall nl, forall m m2 b GH G1 T1 T2 TX x n1 n2,
   stp2 m true [] G1 (TVar true x) (substt x TX) n1 ->
   stp2 m2 b (GH++[TX]) G1 T1 T2 n2 -> m < ml -> n2 < nl -> m2 <= m ->
   (forall (m1 : nat) (b : bool) (G1 : venv) (T1 T2 T3 : ty) (n1 n2 : nat),
        stp2 m true [] G1 T1 T2 n1 ->
        stp2 m1 b [] G1 T2 T3 n2 ->
        m1 <= m -> stpd2 m1 true [] G1 T1 T3) ->
   stpd2 m2 b (map (substt x) GH) G1 (substt x T1) (substt x T2).
Proof.
  (*
  intros ml. (* induction ml. intros. omega. *)
  intros nl. induction nl. intros. omega.
  intros. inversion H0.
  - Case "bot". subst.
    eapply stpd2_bot; eauto. rewrite map_length. simpl. eapply closed_subst. rewrite app_length in H4. simpl in H4. eapply H4.
  - Case "top". subst.
    eapply stpd2_top; eauto. rewrite map_length. simpl. eapply closed_subst. rewrite app_length in H4. simpl in H4. eapply H4.
  - Case "bool". subst.
    eapply stpd2_bool; eauto.
  - Case "fun". subst.
    eapply stpd2_fun. eapply IHnl; eauto. omega. eapply IHnl; eauto. omega.
  - Case "mem". subst.
    eapply stpd2_mem. eapply IHnl; eauto. omega. eapply IHnl; eauto. omega.

  - Case "varx". subst.
    eexists. eapply stp2_varx. eauto.
  - Case "var1". subst.
    assert (TX0 = substt x TX0) as C. simpl. admit. (* closed! NOTE: need to add to stp2_var1 *)
    eapply IHnl in H6.
    eu. eexists. eapply stp2_var1. eauto. eauto. rewrite C. eauto.
    eauto. eauto. omega. eauto.
  - Case "var-bind". subst.
(*    assert (stpd2 m0 true (map (substt x) GH) G1 (substt x (TVar true x0)) (substt x (open 0 (TVar true x0) T0))).
     assert (S m0 + d = m0 + S d) as R. omega. 
     eapply IHnl. instantiate (3:= S d). rewrite <-R. eapply H. (* requires that m of LHS can be larger than RHS *)
     eapply H4. omega. omega. eauto. 
    eu. eexists. eapply stp2_var_bind2. fold subst. erewrite subst_open_commute1. eapply H5. *)
    admit.
    (* GH = [], so no need to recurse. just need to show types are closed! *)
  - Case "vara1". 
    case_eq (beq_nat x0 0); intros E.
    + SCase "hit". 
      eapply beq_nat_true_iff in E. subst x0.
      assert (TX = TX0). admit.
      subst TX0.
      (* downgrade LHS from (S ml) to m *)
      assert (stp2 (m+(length GH)) true [] G1 (TVar true x) (substt x TX) n1) as LHS.
      assumption.
      (* admit. *) (* PROBABLY THE KEY CHALLENGE !! *)
      (* RHS via induction *)
      assert (stpd2 (m + length GH) true (map (substt x) []) G1 (substt x TX) (substt x T2)) as RHS.
      assert (GH = GU). admit. subst GU. 
      assert (m + length GH + 0 = m + length GH) as R. eauto.
      eapply IHnl. simpl. rewrite R. eauto. simpl. eauto. simpl. omega. omega. eauto.
      destruct RHS as [nr RHS].
      (* transitivity *)
      assert (stpd2 (m + length GH) true [] G1 (substt x (TVar false 0)) (substt x T2)).
      unfold substt. simpl. eapply H3. (* trans *) eapply LHS. eapply RHS. omega.
      (* extendH *)
      assert (stpd2 (m + length GH) true (map (substt x) GH) G1 (substt x (TVar false 0)) (substt x T2)).
      admit.

      eauto. admit.  (* TODO: now m is too high!!!!! *)
    + SCase "miss". admit.
      
  - Case "ssel1". admit.
  - Case "ssel2". admit.

  - Case "bindx". admit.

  - Case "wrapf". admit.
  - Case "transf". admit.
    
    Grab Existential Variables.
    apply 0. *)
admit.
Qed.






Lemma stp2_trans: forall l, forall n, forall k, forall m1 m2 b G1 T1 T2 T3 n1 n2,
  stp2 m1 true [] G1 T1 T2 n1 -> 
  stp2 m2 b [] G1 T2 T3 n2 ->
  n2 < n -> m1 < l -> n1 < k -> m2 <= m1 -> 
  stpd2 m2 true [] G1 T1 T3.
Proof.
  intros l. induction l. intros. solve by inversion.
  intros n. induction n. intros. solve by inversion.
  intros k. induction k; intros. solve by inversion.
  destruct b.
  (* b = true *) {
  inversion H.
  - Case "bot". eapply stpd2_bot; eauto. subst. eapply stpd2_closed2; eauto. 
  - Case "top". inversion H0; subst; invty.
    + SCase "top". eapply stpd2_top; eauto.
    + SCase "sel2". admit.
  - Case "bool". inversion H0; subst; invty.
    + SCase "top". eapply stpd2_top; eauto. 
    + SCase "bool". eapply stpd2_bool; eauto.
    + SCase "sel2". admit.
  - Case "fun". inversion H0; subst; invty.
    + SCase "top". eapply stpd2_top; eauto. eapply stpd2_closed1; eauto.
    + SCase "fun". admit. (*invty. subst. eapply stpd2_fun; eapply stp2_trans_axiom; eauto.*)
    + SCase "sel2". admit.
  - Case "mem". inversion H0; subst; invty.
    + SCase "top". eapply stpd2_top; eauto. eapply stpd2_closed1; eauto.
    + SCase "mem". admit. (*invty. subst. eapply stpd2_mem. eapply stp2_trans_axiom; eauto. eapply IHn; eauto. omega. *)
    + SCase "sel2". admit.

  - Case "varx". inversion H0; subst; invty.
    + SCase "top". eapply stpd2_top; eauto. 
    + SCase "varx". eauto. 
    + SCase "var1". eauto. 
    + SCase "var1b". eauto. 
    + SCase "sel2". eauto.

  - Case "var1".
    (* left gets smaller, right stays same *)
    subst. assert (stpd2 m2 true [] G1 TX T3). eapply IHk. apply H7. eauto. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp2_var1; eauto. 
  - Case "varbind2".
    (* left and right decrease level, right size increases *)
    inversion H0; subst; invty.
    + SCase "top". eapply stpd2_top; eauto. eapply stpd2_closed1; eauto.
    + SCase "sel2". admit. 
    + SCase "bind1".
      invty. subst.
      remember (TVar false (length [])) as VZ.
      remember (TVar true x) as VX.

      (* left *)
      assert (stpd2 m true [] G1 VX (open 0 VX T0)) as LHS. admit.
      eu.
      (* right *)
      assert (stpd2 m0 false (open 0 VZ T0 :: []) G1 (open 0 VZ T0) (open 0 VZ T5)) as RHS1.
      eexists. eassumption.
      eu.
      
      (* narrow and subst! *)
      
      assert (stpd2 m0 false [] G1 (open 0 VX T0) (open 0 VX T5)) as RHS2. {
        subst VX. erewrite <-subst_open_commute in LHS. eapply stp2_subst_narrow in LHS.
        unfold substt in LHS. 
        erewrite subst_open_commute in LHS.
        erewrite subst_open_commute in LHS. 
        unfold substt. instantiate (3:=[]) in LHS. simpl in LHS. eapply LHS.
        simpl. subst. simpl in RHS1. eapply RHS1.
        eauto. eauto. omega.
        intros. eapply IHl; eauto. omega. (* omega. *)
      }
      
      (* now trans *)
      assert (stpd2 m0 true [] G1 VX (open 0 VX T5)) as BB. {
        assert (stpd2 m true [] G1 (open 0 VX T0) (open 0 VX T0)) as R.
        eapply stpd2_reg2; eauto.
        eu. eu. subst. eapply IHl. eapply LHS. eapply RHS2. eauto. omega. eauto. omega. 
      }
      
      eu. eexists. subst. eapply stp2_var_bind2. eapply BB.
      
  - Case "vara1". subst.
    (* contradiction: GH <> [] *)
    assert (length (GU ++ [TX]) > 0). rewrite app_length. simpl. omega.
    rewrite <- H6 in H7. simpl in H7. inversion H7.

  - Case "ssel1". subst.
    assert (stpd2 m2 true [] G1 TX T3). eapply IHk. eauto. eauto. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp2_strong_sel1. eauto. eauto.
  - Case "ssel2". subst. inversion H0; subst; invty.
    + SCase "top". eapply stpd2_top. eapply stpd2_closed1; eauto.
    + SCase "ssel1". (* cross case *)index_subst. eapply IHn. eapply H6. eauto. omega. eauto. eauto. eauto. 
    + SCase "ssel2".
      assert (stpd2 m2 true [] G1 T1 TX0). eapply IHn. eapply H. eauto. omega. eauto. eauto. eauto. 
      eu. eexists. eapply stp2_strong_sel2. eauto. eauto. 
      
  - Case "bindx". subst. inversion H0; subst; invty.
    + SCase "top". eapply stpd2_top. eapply stpd2_closed1; eauto.
    + SCase "ssel2". 
      assert (stpd2 m2 true [] G1 (TBind T0) TX). eapply IHn. eapply H. eauto. omega. eauto. eauto. eauto. 
      eu. eexists. eapply stp2_strong_sel2. eauto. eauto.
    + SCase "bindx".
      remember (TVar false (length [])) as V.
      (* narrow! still needed *)
      assert (stpd2 m0 false (open 0 V T0 :: []) G1 (open 0 V T4) (open 0 V T2)).
      eapply stp2_narrow. eapply H5. eauto. omega. 
      (* trans axiom *)
      assert (stpd2 m0 false (open 0 V T0 :: []) G1 (open 0 V T0) (open 0 V T2)).
      admit. (* eapply stp2_trans_axiom. eauto. eauto. *)
      (* result *)
      eu. eexists. subst V. eapply stp2_bindx. eauto. eauto. eauto. 
    
  }  (* b = false *) {
    inversion H0.

  - Case "wrapf". eapply IHn. eapply H. eauto. omega. eauto. eauto. eauto.
  - Case "transf". subst.
    assert (stpd2 m2 true [] G1 T1 T4) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eauto. eauto. 
    eu. eapply IHn. eapply LHS. eapply stp2_downgrade. eauto. eauto. omega. omega. eauto. eauto. 
  }

Grab Existential Variables.
apply 0.  
Qed.


Lemma stpd2_trans: forall m b G1 T1 T2 T3,
  stpd2 m true [] G1 T1 T2 ->
  stpd2 m b    [] G1 T2 T3 ->
  stpd2 m true [] G1 T1 T3.
Proof.
  intros. repeat eu. eapply stp2_trans; eauto.
Qed.

(* TODO: stp_to_stp2 *)

(* TODO: specific inversion lemmas *)

(* TODO: evaluation semantics / soundness *)


End STLC.