(* Clean-slate look at subtyping relation based on *)
(* singleton types (single env) *)

(* TODO: 
   get rid of all admits
   + Rewriting semantics
   + Soundness proof
   Type checker / examples
------
   - multiple members
   - intersection types
   - app var / proper TAll comparison
   - examples / type checking

   - remove unnecessary size variables
   - closedness question: expansion cannot use id beyond self
*)

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
  | TMem   : ty -> ty -> ty (* intro *)
  | TVar   : bool -> id -> ty
  | TVarB  : id -> ty                   
  | TSel   : ty -> ty (* elim *)
  | TBind  : ty -> ty                   
.

Inductive tm : Type :=
  | tvar  : bool -> id -> tm
  | tbool : bool -> tm
  | tmem  : ty -> tm
  | tapp  : tm -> tm -> tm
  | tabs  : ty -> ty -> tm -> tm
.

Inductive vl : Type :=
  | vbool : bool -> vl
  | vabs  : ty -> ty -> tm -> vl
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


(* closed i j k means normal variables < i and < j, bound variables < k *)
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
| cl_mem: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->        
    closed i j k (TMem T1 T2)
| cl_var0: forall i j k x,
    i > x ->
    closed i j k (TVar false x)
| cl_var1: forall i j k x,
    j > x ->
    closed i j k (TVar true x)
| cl_varB: forall i j k x,
    k > x ->
    closed i j k (TVarB x)
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

Fixpoint subst (U : ty) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TBool        => TBool
    | TMem T1 T2   => TMem (subst U T1) (subst U T2)
    | TSel T1      => TSel (subst U T1)
    | TVarB i      => TVarB i
    | TVar true i  => TVar true i
    | TVar false i => if beq_nat i 0 then U else TVar false (i-1)
    | TFun T1 T2   => TFun (subst U T1) (subst U T2)
    | TBind T2     => TBind (subst U T2)
  end.



Inductive has_type : tenv -> venv -> tm -> ty -> nat -> Prop :=
  | T_Varx : forall m GH G1 x T n1,
      vtp m G1 x T n1 ->
      has_type GH G1 (tvar true x) T (S n1)
  | T_Vary : forall G1 GH x T n1,
      index x GH = Some T ->
      closed (length GH) (length G1) 0 T -> 
      has_type GH G1 (tvar false x) T (S n1)
  | T_Mem : forall GH G1 T11 n1,
      closed (length GH) (length G1) 0 T11 -> 
      has_type GH G1 (tmem T11) (TMem T11 T11) (S n1)
  | T_Abs : forall GH G1 T11 T12 t12 n1,
      has_type (T11::GH) G1 t12 T12 n1 ->
      closed (length GH) (length G1) 0 T11 ->
      closed (length GH) (length G1) 0 T12 -> 
      has_type GH G1 (tabs T11 T12 t12) (TFun T11 T12) (S n1)
  | T_App : forall T1 T2 GH G1 t1 t2 n1 n2,
      has_type GH G1 t1 (TFun T1 T2) n1 ->
      has_type GH G1 t2 T1 n2 ->
      has_type GH G1 (tapp t1 t2) T2 (S (n1+n2))
  | T_Sub : forall m GH G1 t T1 T2 n1 n2,
      has_type GH G1 t T1 n1 ->
      stp2 m false GH G1 T1 T2 n2 ->
      has_type GH G1 t T2 (S (n1 + n2))


with stp2: nat -> bool -> tenv -> venv -> ty -> ty -> nat -> Prop :=
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
    stp2 m false GH G1 T2 T4 n1 ->
    stp2 m true GH G1 (TMem T1 T2) (TMem T3 T4) (S (n1+n2))

| stp2_varx: forall m GH G1 x n1,
    x < length G1 ->
    stp2 m true GH G1 (TVar true x) (TVar true x) (S n1)
| stp2_var1: forall m m2 GH G1 x T2 n1,
    vtp m2 G1 x T2 n1 -> (* slack for: val_type G2 v T2 *)
    stp2 m true GH G1 (TVar true x) T2 (S n1)

(* not sure if we should have these 2 or not ... ? *)
(*
| stp2_varb1: forall m GH G1 T2 x n1,
    stp2 m true GH G1 (TVar true x) (TBind T2) n1 -> 
    stp2 m true GH G1 (TVar true x) (open 0 (TVar false x) T2) (S n1) 

| stp2_varb2: forall m GH G1 T2 x n1,
    stp2 m true GH G1 (TVar true x) (open 0 (TVar false x) T2) n1 -> 
    stp2 m true GH G1 (TVar true x) (TBind T2) (S n1)
*)
    
| stp2_varax: forall m GH G1 x n1,
    x < length GH ->
    stp2 m true GH G1 (TVar false x) (TVar false x) (S n1)
(*
| stp2_varay: forall m GH G1 TX x1 x2 n1,
    index x1 GH = Some TX ->
    stp2 m false GH G1 TX (TVar false x2) n1 ->
    stp2 m true GH G1 (TVar false x2) (TVar false x1) (S n1)
| stp2_vary: forall m GH G1 x1 x2 n1,
    index x1 GH = Some (TVar true x2) ->
    x2 < length G1 ->
    stp2 m true GH G1 (TVar true x2) (TVar false x1) (S n1)
*)
| stp2_vara1: forall m GH G1 T2 x n1,
    htp  m false GH G1 x T2 n1 -> (* TEMP -- SHOULD ALLOW UP TO x *)
    stp2 m true GH G1 (TVar false x) T2 (S n1)
(*
| stp2_varab1: forall m GH G1 T2 x n1,
    stp2 m true GH G1 (TVar false x) (TBind T2) n1 -> 
    stp2 m true GH G1 (TVar false x) (open 0 (TVar false x) T2) (S n1) 

| stp2_varab2: forall m GH G1 T2 x n1,
    stp2 m true GH G1 (TVar false x) (open 0 (TVar false x) T2) n1 -> 
    stp2 (S m) true GH G1 (TVar false x) (TBind T2) (S n1)
*)
         
(* NOTE: Currently we require *all* store references (TVar true x)
   to expand (strong_sel), even in nested contexts (GH <> nil).
   This is directly related to the htp GL restriction: when
   substituting, we must derive the precise expansion, and cannot
   tolerate potentially unsafe bindings in GH.
   Is this an issue? If yes, we can keep sel1/sel2 and htp
   for store references, and only invert once we know GH=[].
   We need to be careful, though: it is not clear that we can
   use stp2_trans on the embedded vtp. We may need to specially
   mark self variables (again), since they are the only ones 
   that occur recursively. *)

| stp2_strong_sel1: forall m GH G1 T2 TX x n1,
    index x G1 = Some (vty TX) ->
    stp2 m false [] G1 TX T2 n1 ->
    stp2 m true GH G1 (TSel (TVar true x)) T2 (S n1)
| stp2_strong_sel2: forall m GH G1 T1 TX x n1,
    index x G1 = Some (vty TX) ->
    stp2 m false [] G1 T1 TX n1 ->
    stp2 m true GH G1 T1 (TSel (TVar true x)) (S n1)

(*
| stp2_xsel1: forall m GH G1 T2 TX x n1,
    index x G1 = Some (vty TX) ->
    stp2 m false [] G1 TX T2 n1 ->
    stp2 m true GH G1 (TSel (TVar true x)) T2 (S n1)
| stp2_xsel2: forall m GH G1 T1 TX x n1,
    index x G1 = Some (vty TX) ->
    stp2 m false [] G1 T1 TX n1 ->
    stp2 m true GH G1 T1 (TSel (TVar true x)) (S n1)         
*)

| stp2_sel1: forall m GH G1 T2 n1,
    htp  m false GH G1 0 (TMem TBot T2) n1 ->
    stp2 m true GH G1 (TSel (TVar false 0)) T2 (S n1)

| stp2_sel2: forall m GH G1 T1 n1,
    htp  m false GH G1 0 (TMem T1 TTop) n1 ->
    stp2 m true GH G1 T1 (TSel (TVar false 0)) (S n1)


| stp2_bind1: forall m GH G1 T1 T1' T2 n1,
    htp m false (T1'::GH) G1 (length GH) T2 n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp2 m true GH G1 (TBind T1) T2 (S n1)

| stp2_bindx: forall m GH G1 T1 T1' T2 T2' n1,
    htp m false (T1'::GH) G1 (length GH) T2' n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    T2' = (open 0 (TVar false (length GH)) T2) -> 
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 1 T2 ->
    stp2 m true GH G1 (TBind T1) (TBind T2) (S n1)
         
         
| stp2_wrapf: forall m GH G1 T1 T2 n1,
    stp2 m true GH G1 T1 T2 n1 ->
    stp2 m false GH G1 T1 T2 (S n1)
| stp2_transf: forall m GH G1 T1 T2 T3 n1 n2 m2 m3,
    stp2 m false GH G1 T1 T2 n1 ->
    stp2 m2 false GH G1 T2 T3 n2 -> 
    stp2 m3 false GH G1 T1 T3 (S (n1+n2))
         

with htp: nat -> bool -> tenv -> venv -> nat -> ty -> nat -> Prop :=
| htp_var: forall m b GH G1 x TX n1,
    (* can we assign (TVar false x) ? probably not ... *)
    index x GH = Some TX ->
    closed (length GH) (length G1) 0 TX ->         
    htp m b GH G1 x TX (S n1)
| htp_bind: forall m b GH G1 x TX n1,
    (* is it needed given stp2_bind1? for the moment, yes ...*)
    htp m b GH G1 x (TBind TX) n1 ->
    closed x (length G1) 1 TX ->
    htp m b GH G1 x (open 0 (TVar false x) TX) (S n1)
| htp_sub: forall m b GH GU GL G1 x T1 T2 n1 n2,
    htp m b GH G1 x T1 n1 ->
    stp2 m b GL G1 T1 T2 n2 ->
    length GL = S x ->
    GH = GU ++ GL -> (* NOTE: restriction to GL means we need trans in sel rules *)
    htp m b GH G1 x T2 (S (n1+n2))
             
with vtp : nat -> venv -> nat -> ty -> nat -> Prop :=
| vtp_top: forall m G1 x n1,
    x < length G1 ->
    vtp m G1 x TTop (S n1)
| vtp_bool: forall m G1 x b n1,
    index x G1 = Some (vbool b) ->
    vtp m G1 x (TBool) (S (n1))
| vtp_mem: forall m G1 x TX T1 T2 ms n1 n2,
    index x G1 = Some (vty TX) ->
    stp2 ms false [] G1 T1 TX n1 ->
    stp2 ms false [] G1 TX T2 n2 ->
    vtp m G1 x (TMem T1 T2) (S (n1+n2))
| vtp_fun: forall m G1 x T1 T2 T3 T4 t ms n1 n2 n3,
    index x G1 = Some (vabs T1 T2 t) ->
    has_type [T1] G1 t T2 n3 ->
    stp2 ms false [] G1 T3 T1 n1 ->
    stp2 ms false [] G1 T2 T4 n2 ->             
    vtp m G1 x (TFun T3 T4) (S (n1+n2+n3))
| vtp_bind: forall m G1 x T2 n1,
    vtp m G1 x (open 0 (TVar true x) T2) n1 ->
    closed 0 (length G1) 1 T2 ->
    vtp (S m) G1 x (TBind T2) (S (n1))
| vtp_sel: forall m G1 x y TX n1,
    index y G1 = Some (vty TX) ->
    vtp m G1 x TX n1 ->
    vtp m G1 x (TSel (TVar true y)) (S (n1))


with vtp2 : venv -> nat -> ty -> nat -> Prop :=
| vtp2_refl: forall G1 x n1,
    x < length G1 -> 
    vtp2 G1 x (TVar true x) (S n1)
| vtp2_down: forall m G1 x T n1,
    vtp m G1 x T n1 ->
    vtp2 G1 x T (S n1) 
| vtp2_sel: forall G1 x y TX n1,
    index y G1 = Some (vty TX) ->
    vtp2 G1 x TX n1 ->
    vtp2 G1 x (TSel (TVar true y)) (S (n1)).
              

Definition has_typed GH G1 x T1 := exists n, has_type GH G1 x T1 n.

Definition stpd2 m b GH G1 T1 T2 := exists n, stp2 m b GH G1 T1 T2 n.

Definition htpd m b GH G1 x T1 := exists n, htp m b GH G1 x T1 n.

Definition vtpd m G1 x T1 := exists n, vtp m G1 x T1 n.
Definition vtpd2 G1 x T1 := exists n, vtp2 G1 x T1 n.

Definition vtpdd m G1 x T1 := exists m1 n, vtp m1 G1 x T1 n /\ m1 <= m.

Hint Constructors stp2.
Hint Constructors vtp.

Ltac ep := match goal with
             | [ |- stp2 ?M ?B ?GH ?G1 ?T1 ?T2 ?N ] => assert (exists (n:nat), stp2 M B GH G1 T1 T2 n) as EEX
           end.

Ltac eu := match goal with
             | H: has_typed _ _ _ _ |- _ => destruct H as [? H]
             | H: stpd2 _ _ _ _ _ _ |- _ => destruct H as [? H]
             | H: htpd _ _ _ _ _ _ |- _ => destruct H as [? H]
             | H: vtpd _ _ _ _ |- _ => destruct H as [? H]
             | H: vtpd2 _ _ _ |- _ => destruct H as [? H]
             | H: vtpdd _ _ _ _ |- _ => destruct H as [? [? [H ?]]]
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
    stpd2 m false GH G1 T2 T4 ->
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
Hint Constructors vtp.
Hint Constructors htp.
Hint Constructors has_type.

Hint Unfold has_typed.
Hint Unfold stpd2.
Hint Unfold vtpd.
Hint Unfold vtpdd.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.


Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.





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


Lemma all_extend: forall ni,
  (forall m b GH  v1 G1 T1 T2 n,
     stp2 m b GH G1 T1 T2 n -> n < ni ->
     stp2 m b GH (v1::G1) T1 T2 n) /\
  (forall m v1 x G1 T2 n,
     vtp m G1 x T2 n -> n < ni ->
     vtp m (v1::G1) x T2 n) /\
  (forall m b v1 x GH G1 T2 n,
     htp m b GH G1 x T2 n -> n < ni ->
     htp m b GH (v1::G1) x T2 n) /\
  (forall GH G1 t T v n,
     has_type GH G1 t T n -> n < ni ->
     has_type GH (v::G1) t T n).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H.
  (* stp *)
  - econstructor. eapply closed_extend. eauto.
  - econstructor. eapply closed_extend. eauto.
  - econstructor. 
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega. 
  - econstructor. simpl. eauto.
  - econstructor. eapply IHn. eauto. omega. 
  - econstructor. eauto.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply index_extend. eauto. eapply IHn. eauto. omega.
  - econstructor. eapply index_extend. eauto. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto. eapply closed_extend. eauto. 
  - eapply stp2_bindx. eapply IHn. eauto. omega. eauto. eauto. eapply closed_extend. eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega.
  - eapply stp2_transf. eapply IHn. eauto. omega. eapply IHn. eauto. omega. 
  (* vtp *)    
  - econstructor. simpl. eauto.
  - econstructor. eapply index_extend. eauto.
  - econstructor. eapply index_extend. eauto. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eapply index_extend. eauto. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply closed_extend. eauto. 
  - econstructor. eapply index_extend. eauto. eapply IHn. eauto. omega.
  (* htp *)
  - econstructor. eauto. eapply closed_extend. eauto. 
  - eapply htp_bind. eapply IHn. eauto. omega. eapply closed_extend. eauto. 
  - eapply htp_sub. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eauto. eauto.
  (* has_type *)
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eauto. eapply closed_extend. eauto.
  - econstructor. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply closed_extend. eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega. 
Qed.


Lemma closed_upgrade_gh: forall i i1 j k T1,
  closed i j k T1 -> i <= i1 -> closed i1 j k T1.
Proof. admit. Qed.

Lemma all_closed: forall ni,
  (forall m b GH G1 T1 T2 n,
     stp2 m b GH G1 T1 T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T1) /\
  (forall m b GH G1 T1 T2 n,
     stp2 m b GH G1 T1 T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T2) /\
  (forall m x G1 T2 n,
     vtp m G1 x T2 n -> n < ni ->
     x < length G1) /\
  (forall m x G1 T2 n,
     vtp m G1 x T2 n -> n < ni ->
     closed 0 (length G1) 0 T2) /\
  (forall m b x GH G1 T2 n,
     htp m b GH G1 x T2 n -> n < ni ->
     x < length GH) /\
  (forall m b x GH G1 T2 n,
     htp m b GH G1 x T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T2) /\
  (forall GH G1 t T n,
     has_type GH G1 t T n -> n < ni ->
     closed (length GH) (length G1) 0 T).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H; destruct IHn as [IHS1 [IHS2 [IHV1 [IHV2 [IHH1 [IHH2 IHT]]]]]].
  (* stp left *)
  - econstructor. 
  - eauto. 
  - econstructor. 
  - econstructor. eapply IHS2. eauto. omega. eapply IHS1. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS1. eauto. omega. 
  - econstructor. simpl. eauto.
  - econstructor. eauto. eapply IHV1. eauto. omega. 
  - econstructor. eauto.
  - econstructor. eapply IHH1. eauto. omega.
  - econstructor. econstructor. eapply index_max. eauto. 
  - eapply closed_upgrade_gh. eapply IHS1. eapply H2. omega. simpl. omega.  
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. eauto.
  - econstructor. eauto.
  - eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  (* stp right *)
  - eauto. 
  - econstructor. 
  - econstructor. 
  - econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega. 
  - econstructor. simpl. eauto.
  - eapply closed_upgrade_gh. eapply IHV2. eauto. omega. omega. 
  - econstructor. eauto.
  - eapply IHH2. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHS2. eapply H2. omega. simpl. omega.  
  - econstructor. econstructor. eapply index_max. eauto.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply IHH1. eauto. omega. 
  - eauto. 
  - econstructor. eauto.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  (* vtp left *)
  - eauto.
  - eapply index_max. eauto.
  - eapply index_max. eauto.
  - eapply index_max. eauto.
  - eapply IHV1. eauto. omega.
  - eapply IHV1. eauto. omega.
  (* vtp right *)
  - econstructor.
  - econstructor.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - econstructor. eauto. (* eapply IHV2 in H1. eauto. omega. *)
  - econstructor. econstructor. eapply index_max. eauto.
  (* htp left *)
  - eapply index_max. eauto.
  - eapply IHH1. eauto. omega.
  - eapply IHH1. eauto. omega.
  (* htp right *)
  - eauto. 
  - admit. (* closed-open *) 
  - eapply closed_upgrade_gh. eapply IHS2. eauto. omega. admit. (* length ++ *)
  (* has_type *)
  - eapply closed_upgrade_gh. eapply IHV2. eauto. omega. omega.
  - eauto.
  - econstructor. eauto. eauto.
  - econstructor. eauto. eauto. 
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHS2. eauto. omega. 
Qed.



Lemma vtp_extend : forall m v1 x G1 T2 n,
                      vtp m G1 x T2 n ->
                      vtp m (v1::G1) x T2 n.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma htp_extend : forall m b v1 x GH G1 T2 n,
                      htp m b GH G1 x T2 n ->
                      htp m b GH (v1::G1) x T2 n.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma stp2_extend : forall m b GH  v1 G1 T1 T2 n,
                      stp2 m b GH G1 T1 T2 n ->
                      stp2 m b GH (v1::G1) T1 T2 n.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma stp2_extend_mult : forall m b GH G1 G' T1 T2 n,
                      stp2 m b GH G1 T1 T2 n ->
                      stp2 m b GH (G'++G1) T1 T2 n.
Proof. intros. induction G'. simpl. eauto. simpl. eapply stp2_extend. eauto. Qed. 

Lemma has_type_extend: forall GH G1 t T v n1,
  has_type GH G1 t T n1 ->
  has_type GH (v::G1) t T n1.
Proof. intros. eapply all_extend. eauto. eauto. Qed. 

Lemma has_type_extend_mult: forall GH G1 t T G' n1,
  has_type GH G1 t T n1 ->
  has_type GH (G'++G1) t T n1.
Proof. intros. induction G'. simpl. eauto. simpl. eapply has_type_extend. eauto. Qed. 




Lemma vtp_closed: forall m G1 x T2 n1,
  vtp m G1 x T2 n1 -> 
  closed 0 (length G1) 0 T2.
Proof. intros. eapply all_closed. eauto. eauto. Qed.

Lemma vtp_closed1: forall m G1 x T2 n1,
  vtp m G1 x T2 n1 -> 
  x < length G1.
Proof. intros. eapply all_closed. eauto. eauto. Qed.

Lemma vtp2_closed1: forall G1 x T2 n1,
  vtp2 G1 x T2 n1 -> 
  x < length G1.
Proof. intros. induction H; eauto. eapply vtp_closed1. eauto. Qed.

Lemma has_type_closed: forall GH G1 t T n1,
  has_type GH G1 t T n1 ->
  closed (length GH) (length G1) 0 T.
Proof. intros. eapply all_closed. eauto. eauto. Qed.



Lemma stp2_closed1 : forall m b GH G1 T1 T2 n1,
                      stp2 m b GH G1 T1 T2 n1 ->
                      closed (length GH) (length G1) 0 T1.
Proof. intros. edestruct all_closed. eapply H0. eauto. eauto. Qed.

Lemma stp2_closed2 : forall m b GH G1 T1 T2 n1,
                      stp2 m b GH G1 T1 T2 n1 ->
                      closed (length GH) (length G1) 0 T2.
Proof. intros. edestruct all_closed. destruct H1. eapply H1. eauto. eauto. Qed.

Lemma stpd2_closed1 : forall m b GH G1 T1 T2,
                      stpd2 m b GH G1 T1 T2 ->
                      closed (length GH) (length G1) 0 T1.
Proof. intros. eu. eapply stp2_closed1. eauto. Qed. 


Lemma stpd2_closed2 : forall m b GH G1 T1 T2,
                      stpd2 m b GH G1 T1 T2 ->
                      closed (length GH) (length G1) 0 T2.
Proof. intros. eu. eapply stp2_closed2. eauto. Qed. 


Lemma beq_nat_true_eq: forall A, beq_nat A A = true.
Proof. intros. eapply beq_nat_true_iff. eauto. Qed.


Lemma stpd2_refl: forall m GH G1 T1,
  closed (length GH) (length G1) 0 T1 ->
  stpd2 m true GH G1 T1 T1.
Proof.
  intros. induction T1; inversion H.
  - Case "bot". exists 1. eauto.
  - Case "top". exists 1. eauto.
  - Case "bool". eapply stpd2_bool; eauto.
  - Case "fun". eapply stpd2_fun; try eapply stpd2_wrapf; eauto.
  - Case "mem". eapply stpd2_mem; try eapply stpd2_wrapf; eauto.
  - Case "var0". exists 1. eauto. 
  - Case "var1".
    assert (exists v, index i G1 = Some v) as E. eapply index_exists; eauto.
    destruct E.
    eexists. eapply stp2_varx; eauto.
  - Case "varb". inversion H4. 
  - Case "sel". admit. (* sel-sel ? *)
  - Case "bind".
    eexists. eapply stp2_bindx. eapply htp_var. simpl. rewrite beq_nat_true_eq. eauto.
    instantiate (1:=open 0 (TVar false (length GH)) T1).
    admit. (* closed-open *)
    eauto. eauto. eauto. eauto. 
Grab Existential Variables.
apply 0. apply 0.    
Qed.

Lemma stpd2_reg1 : forall m b GH G1 T1 T2,
                      stpd2 m b GH G1 T1 T2 ->
                      stpd2 m true GH G1 T1 T1.
Proof. intros. eapply stpd2_refl. eapply stpd2_closed1. eauto. Qed.

Lemma stpd2_reg2 : forall m b GH G1 T1 T2,
                      stpd2 m b GH G1 T1 T2 ->
                      stpd2 m true GH G1 T2 T2.
Proof. intros. eapply stpd2_refl. eapply stpd2_closed2. eauto. Qed.



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
  | _ => idtac
end.

Definition substt x T := (subst (TVar true x) T).

Hint Immediate substt.


Lemma closed_no_subst: forall T i j k TX,
   closed i j k T ->
   subst TX T = T.
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

Lemma subst_open_commute: forall T0 TX,
  (subst TX (open 0 (TVar false 0) T0)) = open 0 TX T0.
Proof. admit. Qed.


Lemma subst_open_commute1: forall T0 x x0,
 (open 0 (TVar true x0) (subst (TVar true x) T0)) 
 = (subst (TVar true x) (open 0 (TVar true x0) T0)).
Proof. admit. Qed.


Lemma subst_closed_id: forall x j k T2,
  closed 0 j k T2 ->
  substt x T2 = T2.
Proof. admit. Qed. 


Lemma closed_subst: forall i j k x T2,
  closed (i + 1) j k T2 ->
  closed i j k (substt x T2).
Proof. admit. Qed.

Lemma closed_subst1: forall i j k x T2,
  closed i j k T2 -> i <> 0 ->
  closed (i-1) j k (substt x T2).
Proof. admit. Qed.

Lemma index_subst: forall GH TX T0 T3 x,
  index (length (GH ++ [TX])) (T0 :: GH ++ [TX]) = Some T3 ->
  index (length GH) (map (substt x) (T0 :: GH)) = Some (substt x T3).
Proof. admit. Qed.

Lemma index_subst1: forall GH TX T3 x x0,
  index x0 (GH ++ [TX]) = Some T3 -> x0 <> 0 ->
  index (x0-1) (map (substt x) GH) = Some (substt x T3).
Proof. admit. Qed.

Lemma index_hit0: forall (GH:tenv) TX T2,
 index 0 (GH ++ [TX]) = Some T2 -> T2 = TX.
Proof. admit. Qed. 


Lemma subst_open3: forall (GH:tenv) TX TX0 x,
  (substt x (open 0 (TVar false (length (GH ++ [TX]))) TX0)) =
  (open 0 (TVar false (length GH)) (substt x TX0)).
Proof. admit. Qed. 

Lemma subst_open4: forall (GH:tenv) TX T0 x, 
  substt x (open 0 (TVar false (length (GH ++ [TX]))) T0) =
  open 0 (TVar false (length (map (substt x) GH))) (substt x T0).
Proof. admit. Qed.

Lemma subst_open5: forall (GH:tenv) T0 x xi, 
  xi <> 0 -> substt x (open 0 (TVar false xi) T0) =
  open 0 (TVar false (xi-1)) (substt x T0).
Proof. admit. Qed.

Lemma gh_match: forall (GH:tenv) GU GL TX T0,
  T0 :: GH ++ [TX] = GU ++ GL ->
  length GL = S (length (GH ++ [TX])) ->
  GU = [] /\ GL = T0 :: GH ++ [TX].
Proof. admit. Qed. 

Lemma gh_match1: forall (GH:tenv) GU GL TX,
  GH ++ [TX] = GU ++ GL ->
  length GL > 0 ->
  exists GL1, GL = GL1 ++ [TX] /\ GH = GU ++ GL1.
Proof. admit. Qed. 



Lemma sub_env1: forall (GL:tenv) GU GH TX,
  GH ++ [TX] = GU ++ GL ->
  length GL = 1 ->
  GL = [TX].
Proof. admit. Qed. 

Lemma app_cons1: forall (G1:venv) v,
  v::G1 = [v]++G1.
Proof. admit. Qed.




(* NOT SO EASY ... *) (*
It seems like we'd need to have z:z.type, which is problematic
Lemma htp_bind_admissible: forall m GH G1 x TX n1, (* is it needed given stp2_bind1? *)
    htp m true GH G1 x (TBind TX) n1 ->
    htpd m true GH G1 x (open 0 (TVar false x) TX).
Proof.
  intros.
  assert (closed x (length G1) 1 TX). admit. 
  assert (GL: tenv). admit.
  assert (length GL = S x). admit. 
  
  eexists. eapply htp_sub. eapply H. eapply stp2_bind1.
  eapply htp_sub. eapply htp_var. simpl. rewrite beq_nat_true_eq. eauto.
  
Qed.
*)


Lemma stp2_subst_narrow0: forall n, forall m2 b GH G1 T1 T2 TX x n2,
   stp2 m2 b (GH++[TX]) G1 T1 T2 n2 -> x < length G1 -> n2 < n -> 
   (forall (m1 : nat) GH (T3 : ty) (n1 : nat),
      htp m1 false (GH++[TX]) G1 0 T3 n1 -> n1 < n ->
      exists m2, vtpd m2 G1 x (substt x T3)) ->
   stpd2 m2 b (map (substt x) GH) G1 (substt x T1) (substt x T2).
Proof.
  intros n. induction n. intros. omega.
  intros ? ? ? ? ? ? ? ? ? ? ? ? narrowX.

  (* helper lemma for htp *)
  assert (forall ni n2, forall m GH T2 xi,
    htp m false (GH ++ [TX]) G1 xi T2 n2 -> xi <> 0 -> n2 < ni -> ni < S n ->
    htpd m false (map (substt x) GH) G1 (xi-1) (substt x T2)) as htp_subst_narrow02. {
      induction ni. intros. omega. 
      intros. inversion H2.
      + (* var *) subst.
        repeat eexists. eapply htp_var. eapply index_subst1. eauto. eauto.
        rewrite map_length. eauto. eapply closed_subst. rewrite app_length in H7. eapply H7.
      + (* bind *) subst.
        assert (htpd m false
         (map (substt x) (GH0)) G1
         (xi-1) (substt x (TBind TX0))) as BB.
        eapply IHni. eapply H6. eauto. omega. omega.
        rewrite subst_open5. 
        eu. repeat eexists. eapply htp_bind. eauto. eapply closed_subst1. eauto. eauto. apply []. eauto.
      + (* sub *) subst.
        assert (exists GL0, GL = GL0 ++ [TX] /\ GH0 = GU ++ GL0) as A. eapply gh_match1. eauto. omega.
        destruct A as [GL0 [? ?]]. subst GL.
        
        assert (htpd m false
                     (map (substt x) GH0) G1
                     (xi-1) (substt x T3)) as AA.
        eapply IHni. eauto. eauto. omega. omega. 
        assert (stpd2 m false (map (substt x) GL0) G1 (substt x T3) (substt x T0)) as BB.
        eapply IHn. eauto. eauto. omega. { intros. eapply narrowX. eauto. eauto. }
        eu. eu. repeat eexists. eapply htp_sub. eauto. eauto.
        (* - *)
        rewrite map_length. rewrite app_length in H8. simpl in H8. omega.
        subst GH0. rewrite map_app. eauto. 
  }
  (* special case *)                                                                                   
  assert (forall ni n2, forall m T0 T2,
    htp m false (T0 :: GH ++ [TX]) G1 (length (GH ++ [TX])) T2 n2 -> n2 < ni -> ni < S n ->
    htpd m false (map (substt x) (T0::GH)) G1 (length GH) (substt x T2)) as htp_subst_narrow0. {
      intros.
      rewrite app_comm_cons in H2. 
      remember (T0::GH) as GH1. remember (length (GH ++ [TX])) as xi.
      rewrite app_length in Heqxi. simpl in Heqxi.
      assert (length GH = xi-1) as R. omega.
      rewrite R. eapply htp_subst_narrow02. eauto. omega. eauto. eauto. 
  }

                                                                                               
  (* main logic *)  
  inversion H.
  - Case "bot". subst.
    eapply stpd2_bot; eauto. rewrite map_length. simpl. eapply closed_subst. rewrite app_length in H2. simpl in H2. eapply H2.
  - Case "top". subst.
    eapply stpd2_top; eauto. rewrite map_length. simpl. eapply closed_subst. rewrite app_length in H2. simpl in H2. eapply H2.
  - Case "bool". subst.
    eapply stpd2_bool; eauto.
  - Case "fun". subst.
    eapply stpd2_fun. eapply IHn; eauto. omega. eapply IHn; eauto. omega.
  - Case "mem". subst.
    eapply stpd2_mem. eapply IHn; eauto. omega. eapply IHn; eauto. omega.


  - Case "varx". subst.
    eexists. eapply stp2_varx. eauto.
  - Case "var1". subst.
    assert (substt x T2 = T2) as R. eapply subst_closed_id. eapply vtp_closed. eauto. 
    eexists. eapply stp2_var1. rewrite R. eauto.
  - Case "varax". subst.
    case_eq (beq_nat x0 0); intros E.
    + (* hit *)
      assert (x0 = 0). eapply beq_nat_true_iff. eauto. 
      repeat eexists. unfold substt. subst x0. simpl. eapply stp2_varx. eauto. 
    + (* miss *)
      assert (x0 <> 0). eapply beq_nat_false_iff. eauto. 
      repeat eexists. unfold substt. simpl. rewrite E. eapply stp2_varax. rewrite map_length. rewrite app_length in H2. simpl in H2. omega. 
  - Case "vara1". 
    case_eq (beq_nat x0 0); intros E.
    + (* hit *)
      assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0. 
      assert (exists m0, vtpd m0 G1 x (substt x T2)). subst. eapply narrowX; eauto. omega. 
      ev. eu. subst. repeat eexists. simpl. eapply stp2_var1. eauto. 
    + (* miss *)
      assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      subst. 
      assert (htpd m2 false (map (substt x) GH) G1 (x0-1) (substt x T2)). eapply htp_subst_narrow02. eauto. eauto. eauto. eauto.
      eu. repeat eexists. unfold substt at 2. simpl. rewrite E. eapply stp2_vara1. eauto. 
(*
  - Case "varab1".
    case_eq (beq_nat x0 0); intros E.
    + (* hit *)
      assert (x0 = 0). eapply beq_nat_true_iff; eauto. 
      assert (exists m0, vtpd m0 G1 x (substt x (TBind T0))). subst. eapply H1; eauto. omega. 
      assert ((subst 0 (TVar true x) T0) = T0) as R. admit. (* closed! *)
      ev. eu. inversion H11. rewrite R in H16. clear R. subst.
      repeat eexists. eapply stp2_var1. unfold substt. rewrite subst_open_commute. eauto. 
    + (* miss *)
      assert (stpd2 m2 true (map (substt x) GH) G1 (substt x (TVar false x0))
         (substt x (TBind T0))). eapply IHn; eauto. omega. 
      assert (substt x (TBind T0) = TBind (substt x T0)) as R1. admit.
      assert (substt x (open 0 (TVar false x0) T0) = open 0 (TVar false x0) (substt x T0)) as R2. admit.
      assert (substt x (TVar false x0) = (TVar false x0)) as R3. admit. 
      rewrite R2. rewrite R3. eu. repeat eexists. eapply stp2_varab1. rewrite <-R3. rewrite <-R1. eauto.
  - Case "varab2".
    case_eq (beq_nat x0 0); intros E.
    + (* hit *)
      assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0. 
      assert (exists m0, vtpd m0 G1 x (substt x (open 0 (TVar false 0) T0))). subst. eapply H1; eauto. omega. 
      assert ((subst 0 (TVar true x) T0) = T0) as R. admit. (* closed! *)
      ev. eu. unfold substt in H10. rewrite subst_open_commute in H10. 
      repeat eexists. unfold substt. simpl. eapply stp2_var1. eapply vtp_bind. eauto.
      rewrite R. eauto. 
    + (* miss *)
      assert (stpd2 m true (map (substt x) GH) G1 (substt x (TVar false x0))
         (substt x (open 0 (TVar false x0) T0))). eapply IHn; eauto. omega. 
      assert (substt x (TBind T0) = TBind (substt x T0)) as R1. admit.
      assert (substt x (open 0 (TVar false x0) T0) = open 0 (TVar false x0) (substt x T0)) as R2. admit.
      assert (substt x (TVar false x0) = (TVar false x0)) as R3. admit. 
      rewrite R3. rewrite R1. eu. repeat eexists. eapply stp2_varab2.
      rewrite R3 in H10. rewrite R2 in H10. eauto.
*)

  - Case "ssel1". subst. 
    assert (substt x T2 = T2) as R. eapply subst_closed_id. eapply stpd2_closed2 with (GH:=[]). eauto. 
    eexists. eapply stp2_strong_sel1. eauto. rewrite R. eauto. 
    
  - Case "ssel2". subst. 
    assert (substt x T1 = T1) as R. eapply subst_closed_id. eapply stpd2_closed1 with (GH:=[]). eauto. 
    eexists. eapply stp2_strong_sel2. eauto. rewrite R. eauto. 

  - Case "sel1". subst. (* invert htp to vtp and create strong_sel node *)
    assert (exists m0, vtpd m0 G1 x (substt x (TMem TBot T2))) as A. eapply narrowX. eauto. omega.
    destruct A as [? A]. eu. inversion A. subst.
    repeat eexists. eapply stp2_strong_sel1. eauto. unfold substt. 
    instantiate (1:=n2). admit. (* FIXME: m2 vs ms *)

  - Case "sel2". subst. (* invert htp to vtp and create strong_sel node *)
    assert (exists m0, vtpd m0 G1 x (substt x (TMem T1 TTop))) as A. eapply narrowX. eauto. omega.
    destruct A as [? A]. eu. inversion A. subst. 
    repeat eexists. eapply stp2_strong_sel2. eauto. unfold substt. 
    instantiate (1:=n2). admit. (* FIXME: m2 vs ms *)

   - Case "bind1". 
    assert (htpd m2 false (map (substt x) (T1'::GH)) G1 (length GH) (substt x T2)). 
    eapply htp_subst_narrow0. eauto. eauto. omega. 
    eu. repeat eexists. eapply stp2_bind1. rewrite map_length. eapply H13.
    simpl. subst T1'. fold subst. eapply subst_open4.
    fold subst. eapply closed_subst. rewrite app_length in H4. simpl in H4. rewrite map_length. eauto. 
    eapply closed_subst. rewrite map_length. rewrite app_length in H5. simpl in H5. eauto. 
   
  - Case "bindx". 
    assert (htpd m2 false (map (substt x) (T1'::GH)) G1 (length GH) (substt x T2')). 
    eapply htp_subst_narrow0. eauto. eauto. omega. 
    eu. repeat eexists. eapply stp2_bindx. rewrite map_length. eapply H14. 
    subst T1'. fold subst. eapply subst_open4. 
    subst T2'. fold subst. eapply subst_open4.
    rewrite app_length in H5. simpl in H5. eapply closed_subst. rewrite map_length. eauto.
    rewrite app_length in H6. simpl in H6. eapply closed_subst. rewrite map_length. eauto. 

  - Case "wrapf".
    assert (stpd2 m2 true (map (substt x) GH) G1 (substt x T1) (substt x T2)).
    eapply IHn; eauto. omega.
    eu. repeat eexists. eapply stp2_wrapf. eauto. 
  - Case "transf". 
    assert (stpd2 m false (map (substt x) GH) G1 (substt x T1) (substt x T3)).
    eapply IHn; eauto. omega.
    assert (stpd2 m0 false (map (substt x) GH) G1 (substt x T3) (substt x T2)).
    eapply IHn; eauto. omega.
    eu. eu. repeat eexists. eapply stp2_transf. eauto. eauto. 
    
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. 
Qed. 


Lemma stp2_subst_narrowX: forall ml, forall nl, forall m b m2 GH G1 T2 TX x n1 n2,
   vtp m G1 x (substt x TX) n1 ->
   htp m2 b (GH++[TX]) G1 0 T2 n2 -> x < length G1 -> m < ml -> n2 < nl ->
   (forall (m0 m1 : nat) (b : bool) (G1 : venv) x (T2 T3 : ty) (n1 n2 : nat),
        vtp m0 G1 x T2 n1 ->
        stp2 m1 b [] G1 T2 T3 n2 -> m0 <= m ->
        vtpdd m0 G1 x T3) ->
   vtpdd m G1 x (substt x T2). (* decrease b/c transitivity *)
Proof. 
  intros ml. (* induction ml. intros. omega. *)
  intros nl. induction nl. intros. omega.
  intros.
  inversion H0.
  - Case "var". subst.
    assert (T2 = TX). eapply index_hit0. eauto. 
    subst T2.
    repeat eexists. eauto. eauto. 
  - Case "bind". subst.
    assert (vtpdd m G1 x (substt x (TBind TX0))) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    destruct A as [? [? [A ?]]]. inversion A. subst.
    repeat eexists. unfold substt. rewrite subst_open_commute.
    assert (closed 0 (length G1) 0 (TBind (substt x TX0))). eapply vtp_closed. unfold substt in A. simpl in A. eapply A.
    assert ((substt x (TX0)) = TX0) as R. eapply subst_closed_id. eauto.
    unfold substt in R. rewrite R in H9. eapply H9. omega.
  - Case "sub". subst. 
    assert (GL = [TX]). eapply sub_env1; eauto. subst GL.
    assert (vtpdd m G1 x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto. 
    eu.
    assert (stpd2 m2 b (map (substt x) []) G1 (substt x T1) (substt x T2)) as B.
    eapply stp2_subst_narrow0. eauto. eauto. eauto. {
      intros. eapply IHnl in H. eu. repeat eexists. eauto. eauto. eauto. eauto. omega. eauto. 
    }
    simpl in B. eu. 
    assert (vtpdd x0 G1 x (substt x T2)).
    eapply H4. eauto. eauto. eauto.
    eu. repeat eexists. eauto. omega. 
Qed.



Lemma stp2_trans: forall l, forall n, forall k, forall m1 m2 b G1 x T2 T3 n1 n2,
  vtp m1 G1 x T2 n1 -> 
  stp2 m2 b [] G1 T2 T3 n2 ->
  m1 < l -> n2 < n -> n1 < k -> 
  vtpdd m1 G1 x T3.
Proof.
  intros l. induction l. intros. solve by inversion.
  intros n. induction n. intros. solve by inversion.
  intros k. induction k; intros. solve by inversion.
  destruct b.
  (* b = true *) {
  inversion H.
  - Case "top". inversion H0; subst; invty.
    + SCase "top". repeat eexists; eauto.
    + SCase "ssel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega. 
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp2_closed2 in H0. simpl in H0. inversion H0. inversion H9. omega.  
  - Case "bool". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply index_max. eauto. eauto. 
    + SCase "bool". repeat eexists; eauto. 
    + SCase "ssel2". 
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega. 
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto.
    + SCase "sel2". 
      eapply stp2_closed2 in H0. simpl in H0. inversion H0. inversion H9. omega.  
  - Case "mem". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply index_max. eauto. eauto. 
    + SCase "mem". invty. subst.
      repeat eexists. eapply vtp_mem. eauto.
      eapply stp2_transf. eauto. eapply H5.
      eapply stp2_transf. eauto. eapply H13.
      eauto. 
    + SCase "sel2". 
      assert (vtpdd m1 G1 x TX0). eapply IHn; eauto. omega. 
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. 
    + SCase "sel2". 
      eapply stp2_closed2 in H0. simpl in H0. inversion H0. inversion H11. omega.
  - Case "fun". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply index_max. eauto. eauto. 
    + SCase "fun". invty. subst.
      repeat eexists. eapply vtp_fun. eauto. eauto. 
      eapply stp2_transf. eauto. eapply H6.
      eapply stp2_transf. eauto. eapply H14.
      eauto. 
    + SCase "sel2". 
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega. 
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. 
    + SCase "sel2". 
      eapply stp2_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
  - Case "bind". 
    inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto. 
    + SCase "sel2". 
      assert (vtpdd (S m) G1 x TX). eapply IHn; eauto. omega. 
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. 
    + SCase "sel2". 
      eapply stp2_closed2 in H0. simpl in H0. inversion H0. inversion H10. omega.  
    + SCase "bind1".
      invty. subst.
      remember (TVar false (length [])) as VZ.
      remember (TVar true x) as VX.

      (* left *)
      assert (vtpd m G1 x (open 0 VX T0)) as LHS. eexists. eassumption.
      eu.
      (* right *)
      assert (substt x (open 0 VZ T0) = (open 0 VX T0)) as R. unfold substt. subst. eapply subst_open_commute.  
      assert (substt x T3 = T3) as R1. eapply subst_closed_id. eauto. 

      assert (vtpdd m G1 x (substt x T3)) as BB. {
        eapply stp2_subst_narrowX. rewrite <-R in LHS. eapply LHS.
        instantiate (2:=nil). simpl. eapply H11. eapply vtp_closed1. eauto. eauto. eauto. 
        { intros. eapply IHl. eauto. eauto. omega. eauto. eauto. }
      }
      rewrite R1 in BB. 
      eu. repeat eexists. eauto. omega. 
    + SCase "bindx".
      invty. subst.
      remember (TVar false (length [])) as VZ.
      remember (TVar true x) as VX.

      (* left *)
      assert (vtpd m G1 x (open 0 VX T0)) as LHS. eexists. eassumption.
      eu.
      (* right *)
      assert (substt x (open 0 VZ T0) = (open 0 VX T0)) as R. unfold substt. subst. eapply subst_open_commute.  

      assert (vtpdd m G1 x (substt x (open 0 VZ T4))) as BB. {
        eapply stp2_subst_narrowX. rewrite <-R in LHS. eapply LHS.
        instantiate (2:=nil). simpl. eapply H11. eapply vtp_closed1. eauto. eauto. eauto. 
        { intros. eapply IHl. eauto. eauto. omega. eauto. eauto. }
      }
      unfold substt in BB. subst. rewrite subst_open_commute in BB. 
      clear R.
      eu. repeat eexists. eapply vtp_bind. eauto. eauto. omega. (* enough slack to add bind back *)
  - Case "ssel2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto. 
    + SCase "ssel1". index_subst. eapply IHn. eauto. eauto. eauto. omega. eauto.
    + SCase "ssel2". 
      assert (vtpdd m1 G1 x TX0). eapply IHn; eauto. omega. 
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto.
    + SCase "sel1".
      assert (closed (length ([]:tenv)) (length G1) 0 (TSel (TVar false 0))).
      eapply stpd2_closed2. eauto.
      simpl in H7. inversion H7. inversion H12. omega. 
      
  }  (* b = false *) {
    inversion H0.

  - Case "wrapf". eapply IHn. eapply H. eauto. eauto. omega. eauto.
  - Case "transf". subst.
    assert (vtpdd m1 G1 x T0) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto.
    eu.
    assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. 
    eu. repeat eexists. eauto. omega. 
  }

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


Lemma stp2_trans2: forall n, forall m b G1 T2 T3 x n1 n2,
  vtp2 G1 x T2 n1 ->
  stp2 m b [] G1 T2 T3 n2 -> n2 < n ->
  vtpd2 G1 x T3.
Proof.
  intros n. induction n. intros. omega.
  intros.
  inversion H.
  - Case "self". subst.
    inversion H0.
    + SCase "top". subst.
      eexists. eapply vtp2_down. eapply vtp_top. eauto.
    + SCase "varx". subst.
      eexists. eapply vtp2_refl. eauto.
    + SCase "var1". subst.
      eexists. eapply vtp2_down. eauto.
    + SCase "ssel2". subst.
      assert (vtpd2 G1 x TX). eapply IHn; eauto. omega. 
      eu. eexists. eapply vtp2_sel. eauto. eauto. 
    + SCase "sel2". subst.
      assert (closed (length ([]:tenv)) (length G1) 0 (TVar false 0)) as CL.
      eapply stpd2_closed1. eauto.
      simpl in CL. inversion CL. omega.
    + SCase "wrapf". subst.
      clear H0. eapply IHn; eauto. omega.
    + SCase "transf". subst.
      assert (vtpd2 G1 x T2). eapply IHn; eauto. omega.
      eu. eapply IHn; eauto. omega. 
  - Case "down". subst.
    assert (vtpdd m0 G1 x T3). eapply stp2_trans; eauto.
    eu. eexists. eapply vtp2_down. eauto.
  - Case "sel". subst.
    inversion H0.
    + SCase "top". subst.
      eexists. eapply vtp2_down. eapply vtp_top. eapply vtp2_closed1. eauto. 
    + SCase "varx". subst.
      index_subst.
      eapply IHn. eauto. eauto. omega. 
    + SCase "ssel1". subst.
      assert (vtpd2 G1 x TX0). eapply IHn. eapply H. eauto. omega.
      eu. eexists. eapply vtp2_sel. eauto. eauto. 
    + SCase "sel1". subst.
      assert (closed (length ([]:tenv)) (length G1) 0 (TVar false 0)) as CL.
      eapply stpd2_closed1. eauto.
      simpl in CL. inversion CL. omega.
    + SCase "wrapf". subst.
      clear H0. eapply IHn; eauto. omega. 
    + SCase "transf". subst.
      assert (vtpd2 G1 x T2). eapply IHn; eauto. omega.
      eu. eapply IHn; eauto. omega. 

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. 
Qed.



(* TODO: stp_to_stp2 *)

(* TODO: specific inversion lemmas *)

(* TODO: evaluation semantics / soundness *)


(* Reduction semantics  *)


Fixpoint subst_tm (u:nat) (T : tm) {struct T} : tm :=
  match T with
    | tvar true i  => tvar true i
    | tvar false i => if beq_nat i 0 then (tvar true u) else tvar false (i-1)
    | tbool b      => tbool b                           
    | tmem T       => tmem (subst (TVar true u) T)
    | tabs T1 T2 t => tabs (subst (TVar true u) T1) (subst (TVar true u) T2) (subst_tm u t)
(*    | TVarB i      => TVarB i *)
    | tapp t1 t2   => tapp (subst_tm u t1) (subst_tm u t2)
  end.

Inductive step : venv -> tm -> venv -> tm -> Prop :=
| ST_Mem : forall G1 T1,
    step G1 (tmem T1) (vty T1::G1) (tvar true (length G1))
| ST_Abs : forall G1 T1 T2 t,
    step G1 (tabs T1 T2 t) (vabs T1 T2 t::G1) (tvar true (length G1))
| ST_AppAbs : forall G1 f x T1 T2 t12,
    index f G1 = Some (vabs T1 T2 t12) ->
    step G1 (tapp (tvar true f) (tvar true x)) G1 (subst_tm x t12)
| ST_App1 : forall G1 G1' t1 t1' t2,
    step G1 t1 G1' t1' ->
    step G1 (tapp t1 t2) G1' (tapp t1' t2)
| ST_App2 : forall G1 G1' f t2 t2',
    step G1 t2 G1' t2' ->
    step G1 (tapp (tvar true f) t2) G1' (tapp (tvar true f) t2')
.






Lemma hastp_inv: forall G1 x T n1,
  has_type [] G1 (tvar true x) T n1 ->
  exists m n1, vtp m G1 x T n1.
Proof.
  intros. remember [] as GH. remember (tvar true x) as t.
  induction H; subst; try inversion Heqt.
  - Case "varx". subst. repeat eexists. eauto.
  - Case "sub".
    destruct IHhas_type. eauto. eauto. ev.
    assert (exists m0, vtpdd m0 G1 x T2). eexists. eapply stp2_trans; eauto. 
    ev. eu. repeat eexists. eauto. 
Qed.

Lemma hastp_subst: forall m G1 GH TX T x t n1 n2,
  has_type (GH++[TX]) G1 t T n2 ->
  vtp m G1 x TX n1 ->
  exists n3, has_type (map (substt x) GH) G1 (subst_tm x t) (substt x T) n3.
Proof.
  intros. remember (GH++[TX]) as GH0. revert GH HeqGH0. induction H; intros.
  - Case "varx". simpl. eexists. eapply T_Varx. erewrite subst_closed_id. eauto. eapply vtp_closed. eauto.
  - Case "vary". subst. simpl.
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0.
      eexists. eapply T_Varx. eapply index_hit0 in H. subst. erewrite subst_closed_id. eauto. eapply vtp_closed. eauto. 
    + assert (x0 <> 0). eapply beq_nat_false_iff; eauto.
      eexists. eapply T_Vary. eapply index_subst1. eauto. eauto. rewrite map_length. eapply closed_subst. rewrite app_length in H1. simpl in H1. eapply H1.
  - Case "mem". subst. simpl.
    eexists. eapply T_Mem. eapply closed_subst. rewrite app_length in H. rewrite map_length. eauto.
  - Case "abs". subst. simpl.
    assert (has_typed (map (substt x) (T11::GH0)) G1 (subst_tm x t12) (substt x T12)) as HI.
    eapply IHhas_type. eauto. eauto.
    eu. simpl in HI. 
    eexists. eapply T_Abs. eapply HI. eapply closed_subst. rewrite map_length. rewrite app_length in H1. simpl in H1. eauto. eauto.
    eapply closed_subst. rewrite map_length. rewrite app_length in H2. simpl in H2. eauto. 
  - Case "app".
    edestruct IHhas_type1. eauto. eauto.
    edestruct IHhas_type2. eauto. eauto. 
    eexists. eapply T_App. eapply H2. eapply H3. 
  - Case "sub". subst. 
    edestruct stp2_subst_narrow0. eapply H1. eapply vtp_closed1. eauto. eauto. 
    { intros. edestruct stp2_subst_narrowX. erewrite subst_closed_id.
      eapply H0. eapply vtp_closed. eauto. eauto. eapply vtp_closed1. eauto. eauto. eauto.
      { intros. eapply stp2_trans; eauto. }
      ev. repeat eexists. eauto.
    }
    edestruct IHhas_type. eauto. eauto.
    eexists. eapply T_Sub. eauto. eauto.
Grab Existential Variables.
  apply 0. apply 0.
Qed.

Theorem type_safety : forall G t T n1,
  has_type [] G t T n1 ->
  (exists x, t = tvar true x) \/
  (exists G' t' n2, step G t (G'++G) t' /\ has_type [] (G'++G) t' T n2).
Proof. 
  intros.
  assert (closed (length ([]:tenv)) (length G) 0 T) as CL. eapply has_type_closed. eauto. 
  remember [] as GH. remember t as tt. remember T as TT.
  revert T t HeqTT HeqGH Heqtt CL. 
  induction H; intros. 
  - Case "varx". eauto. 
  - Case "vary". subst GH. inversion H. 
  - Case "mem". right.
    assert (stpd2 0 true [] (vty T11::G1) T11 T11).
    eapply stpd2_refl. subst. eapply closed_extend. eauto. 
    eu. repeat eexists. rewrite <-app_cons1. eapply ST_Mem. eapply T_Varx. eapply vtp_mem.
    simpl. rewrite beq_nat_true_eq. eauto. eauto. eauto. 
  - Case "abs". right.
    inversion CL.
    assert (stpd2 0 true [] (vabs T11 T12 t12::G1) T11 T11).
    eapply stpd2_refl. subst. eapply closed_extend. eauto. 
    assert (stpd2 0 true [] (vabs T11 T12 t12::G1) T12 T12).
    eapply stpd2_refl. subst. eapply closed_extend. eauto. 
    eu. eu. repeat eexists. rewrite <-app_cons1. eapply ST_Abs. eapply T_Varx. eapply vtp_fun.
    simpl. rewrite beq_nat_true_eq. eauto. subst.
    eapply has_type_extend. eauto. eauto. eauto. 
  - Case "app". subst.
    assert (closed (length ([]:tenv)) (length G1) 0 (TFun T1 T)) as TF. eapply has_type_closed. eauto. 
    assert ((exists x : id, t2 = tvar true x) \/
                (exists (G' : venv) (t' : tm) n2,
                   step G1 t2 (G'++G1) t' /\ has_type [] (G'++G1) t' T1 n2)) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto. 
    assert ((exists x : id, t1 = tvar true x) \/
                (exists (G' : venv) (t' : tm) n2,
                   step G1 t1 (G'++G1) t' /\ has_type [] (G'++G1) t' (TFun T1 T) n2)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      destruct HX.
      * SSCase "arg-val".
        ev. ev. subst. 
        assert (exists m n1, vtp m G1 x (TFun T1 T) n1). eapply hastp_inv. eauto.
        assert (exists m n1, vtp m G1 x0 T1 n1). eapply hastp_inv. eauto.
        ev. inversion H1. subst.
        assert (vtpdd x1 G1 x0 T0). eapply stp2_trans. eauto. eauto. eauto. eauto. eauto.
        eu.
        assert (has_typed (map (substt x0) []) G1 (subst_tm x0 t) (substt x0 T2)) as HI.
        eapply hastp_subst; eauto.
        eu. simpl in HI. erewrite subst_closed_id in HI. 
        right. repeat eexists. rewrite app_nil_l. eapply ST_AppAbs. eauto.
        eapply T_Sub. eauto. eauto.
        change 0 with (length ([]:tenv)). eapply stpd2_closed1. eauto. 
      * SSCase "arg_step".
        ev. subst. 
        right. repeat eexists. eapply ST_App2. eauto. eapply T_App.
        eapply has_type_extend_mult. eauto. eauto. 
    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply ST_App1. eauto. eapply T_App.
      eauto. eapply has_type_extend_mult. eauto. 
  - Case "sub". subst.
    assert ((exists x : id, t0 = tvar true x) \/
               (exists (G' : venv) (t' : tm) n2,
                  step G1 t0 (G'++G1) t' /\ has_type [] (G'++G1) t' T1 n2)) as HH.
    eapply IHhas_type; eauto. change 0 with (length ([]:tenv)) at 1. eapply stpd2_closed1; eauto.
    destruct HH.
    + SCase "val".
      ev. subst. left. eexists. eauto.
    + SCase "step".
      ev. subst. 
      right. repeat eexists. eauto. eapply T_Sub. eauto. eapply stp2_extend_mult. eauto. 
      
Grab Existential Variables.
apply 0. apply 0.
Qed. 


End STLC.