Require Export SfLib.

Require Export Arith.EqNat.

Require Export Arith.Le.

(* 
subtyping: 
  - looking at single-environment case again.
  - new pushback proof structure: transitivity axiom only 
    needed in contravariant positions

 DOING:
  - add bindx (and/or bind2/bind1) rules

 TODO:
  - transitivity will only hold in realizable context

 QUESTIONS: 
  - exact statement of transitivity? 
  - what's the right notion of realizable types/contexts?
  - how can we do induction across realizability evidence?
*)


(* ############################################################ *)
(* Syntax *)
(* ############################################################ *)

Module DOT.

Definition id := nat.

Inductive ty : Type :=
  | TNoF   : ty (* marker for empty method list *)

  | TBot   : ty
  | TTop   : ty
  | TBool  : ty
  | TAnd   : ty -> ty -> ty
  | TFun   : id -> ty -> ty -> ty
  | TMem   : ty -> ty -> ty
  | TSel   : id -> ty

  | TSelB  : id -> ty
  | TBind  : ty -> ty
.
  
Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : id -> id -> tm -> tm (* a.f(x) *)
  | tabs : id -> ty -> list (id * dc) -> tm -> tm (* let f:T = x => y in z *)
  | tlet : id -> ty -> tm -> tm -> tm (* let x:T = y *)                                         
with dc: Type :=
  | dfun : ty -> ty -> id -> tm -> dc (* def m:T = x => y *)
.

Fixpoint dc_type_and (dcs: list(nat*dc)) :=
  match dcs with
    | nil => TNoF
    | (n, dfun T1 T2 _ _)::dcs =>
      TAnd (TFun (length dcs) T1 T2)  (dc_type_and dcs)
  end.


Definition TObj p dcs := TAnd (TMem p p) (dc_type_and dcs).
Definition TArrow p x y := TAnd (TMem p p) (TAnd (TFun 0 x y) TNoF).


Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : list (id*vl) -> id -> ty -> list (id * dc) -> vl (* clos env f:T = x => y *)
| vmock : list (id*vl) -> ty -> id -> id -> vl
.

Definition env := list (nat*vl).
Definition tenv := list (nat*ty).

Fixpoint index {X : Type} (n : nat)
               (l : list (nat * X)) : option X :=
  match l with
    | [] => None
    (* for now, ignore binding value n' !!! *)
    | (n',a) :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

Fixpoint update {X : Type} (n : nat) (x: X)
               (l : list (nat * X)) { struct l }: list (nat * X) :=
  match l with
    | [] => []
    (* for now, ignore binding value n' !!! *)
    | (n',a) :: l'  => if beq_nat n (length l') then (n',x)::l' else (n',a) :: update n x l'
  end.



(* LOCALLY NAMELESS *)

Inductive closed_rec: nat -> ty -> Prop :=
| cl_nof: forall k,
    closed_rec k TNoF
| cl_top: forall k,
    closed_rec k TTop
| cl_bot: forall k,
    closed_rec k TBot
| cl_bool: forall k,
    closed_rec k TBool
| cl_fun: forall k m T1 T2,
    closed_rec k T1 ->
    closed_rec k T2 ->
    closed_rec k (TFun m T1 T2)
| cl_mem: forall k T1 T2,
    closed_rec k T1 ->
    closed_rec k T2 ->
    closed_rec k (TMem T1 T2)
| cl_and: forall k T1 T2,
    closed_rec k T1 ->
    closed_rec k T2 ->
    closed_rec k (TAnd T1 T2)
| cl_bind: forall k T1,
    closed_rec (S k) T1 ->
    closed_rec k (TBind T1)
| cl_sel: forall k x,
    closed_rec k (TSel x)
| cl_selb: forall k i,
    k > i ->
    closed_rec k (TSelB i)
.

Hint Constructors closed_rec.

Definition closed T := closed_rec 0 T.

Inductive bound_fv: id -> ty -> Prop :=
| bfv_nof: forall u,
    bound_fv u TNoF
| bfv_top: forall u,
    bound_fv u TTop
| bfv_bot: forall u,
    bound_fv u TBot
| bfv_bool: forall u,
    bound_fv u TBool
| bfv_fun: forall u m T1 T2,
    bound_fv u T1 ->
    bound_fv u T2 ->
    bound_fv u (TFun m T1 T2)
| bfv_mem: forall u T1 T2,
    bound_fv u T1 ->
    bound_fv u T2 ->
    bound_fv u (TMem T1 T2)
| bfv_and: forall u T1 T2,
    bound_fv u T1 ->
    bound_fv u T2 ->
    bound_fv u (TAnd T1 T2)
| bfv_bind: forall u T1,
    bound_fv u T1 ->
    bound_fv u (TBind T1)
| bfv_selb: forall u i,
    bound_fv u (TSelB i)
| bfv_sel: forall u x,
    u > x ->
    bound_fv u (TSel x)
.

Hint Constructors bound_fv.

Inductive bound_fvs: id -> tenv -> Prop :=
| bound_fvs_nil : forall u,
    bound_fvs u []
| bound_fvs_cons: forall u x T G,
    bound_fv u T ->
    bound_fvs u ((x,T)::G)
.

Fixpoint open_rec (k: nat) (u: id) (T: ty) { struct T }: ty :=
  match T with
    | TSel x      => TSel x (* free var remains free. functional, so we can't check for conflict *)
    | TSelB i     => if beq_nat k i then TSel u else TSelB i
    | TBind T1    => TBind (open_rec (S k) u T1)
    | TNoF        => TNoF
    | TBot => TBot
    | TTop => TTop
    | TBool       => TBool
    | TAnd T1 T2  => TAnd (open_rec k u T1) (open_rec k u T2)
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
    | TFun m T1 T2  => TFun m (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

(* sanity check *)
Example open_ex1: open 9 (TBind (TAnd (TMem TBot TTop) (TFun 0 (TSelB 1) (TSelB 0)))) =
                      (TBind (TAnd (TMem TBot TTop) (TFun 0 (TSel  9) (TSelB 0)))).
Proof. compute. eauto. Qed.


Lemma closed_no_open: forall T x j,
  closed_rec j T ->
  T = open_rec j x T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed_rec; rewrite <-IHclosed_rec; auto];
  try solve [compute; compute in IHclosed_rec1; compute in IHclosed_rec2; rewrite <-IHclosed_rec1; rewrite <-IHclosed_rec2; auto].

  Case "TSelB".
    unfold open_rec. assert (k <> i). omega. 
    apply beq_nat_false_iff in H0.
    rewrite H0. auto.
Qed.

Lemma closed_upgrade: forall i j T,
 closed_rec i T ->
 j >= i ->
 closed_rec j T.
Proof.
 intros. generalize dependent j. induction H; intros; eauto.
 Case "TBind". econstructor. eapply IHclosed_rec. omega.
 Case "TSelB". econstructor. omega.
Qed.


Hint Unfold open.
Hint Unfold closed.


(* ############################################################ *)
(* Static properties: type assignment, subtyping, ... *)
(* ############################################################ *)

(* static type expansion.
   needs to imply dynamic subtyping / value typing. *)
Inductive tresolve: id -> ty -> ty -> Prop :=
  | tr_self: forall x T,
             tresolve x T T
  | tr_and1: forall x T1 T2 T,
             tresolve x T1 T ->
             tresolve x (TAnd T1 T2) T
  | tr_and2: forall x T1 T2 T,
             tresolve x T2 T ->
             tresolve x (TAnd T1 T2) T
  | tr_unpack: forall x T2 T3 T,
             open x T2 = T3 ->
             tresolve x T3 T ->
             tresolve x (TBind T2) T
.

Tactic Notation "tresolve_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Self" |
    Case_aux c "And1" |
    Case_aux c "And2" |
    Case_aux c "Bind" ].


(* static type well-formedness.
   needs to imply dynamic subtyping. *)
Inductive wf_type : tenv -> ty -> Prop :=
| wf_top: forall env,
    wf_type env TNoF
| wf_bool: forall env,
    wf_type env TBool
| wf_and: forall env T1 T2,
    wf_type env T1 ->
    wf_type env T2 ->
    wf_type env (TAnd T1 T2)
| wf_mem: forall env TL TU,
    wf_type env TL ->
    wf_type env TU ->
    wf_type env (TMem TL TU)
| wf_fun: forall env f T1 T2,
    wf_type env T1 ->
    wf_type env T2 ->
    wf_type env (TFun f T1 T2)
| wf_sel: forall env x TE TL TU,
    index x env = Some (TE) ->
    tresolve x TE (TMem TL TU) ->
    wf_type env (TSel x)
| wf_bind: forall f env T TA,
    bound_fvs (length env) env ->
    bound_fv (length env) TA ->
    open (length env) TA = T ->
    wf_type ((f,T)::env) T ->
    wf_type env (TBind TA)
.

Tactic Notation "wf_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Top" |
    Case_aux c "Bool" |
    Case_aux c "And" |
    Case_aux c "Mem" |
    Case_aux c "Fun" |
    Case_aux c "Sel" |
    Case_aux c "Bind" ].



(* TODO: need to see what to do for expansion / 'has' *)
(*
  x: { z => Tz }
  x: Tx

  x: y.A(L..U)
  x: U
 *)


Inductive stp : bool -> tenv -> ty -> ty -> nat -> Prop := 
  
| stp_bool: forall G1 n1,
    stp true G1 TBool TBool n1

| stp_fun: forall m G1 T11 T12 T21 T22 n1 n2,
    stp false G1 T21 T11 n1 ->
    stp true G1 T12 T22 n2 ->
    stp true G1 (TFun m T11 T12) (TFun m T21 T22) (S (n1+n2))

| stp_mem: forall G1 T11 T12 T21 T22 n1 n2,
    stp false G1 T21 T11 n1 ->
    stp true G1 T12 T22 n2 ->
    stp true G1 (TMem T11 T12) (TMem T21 T22) (S (n1+n2))
        
| stp_sel2: forall x T1 TX G1 n1,
    index x G1 = Some TX ->
    stp true G1 TX (TMem T1 TTop) n1 ->
    stp true G1 T1 (TSel x) (S n1)
| stp_sel1: forall x T2 TX G1 n1,
    index x G1 = Some TX ->
    stp true G1 TX (TMem TBot T2) n1->
    stp true G1 (TSel x) T2 (S n1)
| stp_selx: forall x TX TL TU G1 n1,
    index x G1 = Some TX ->
    tresolve x TX (TMem TL TU) ->
    stp true G1 (TSel x) (TSel x) n1
(* TODO!
| stp_bind2: forall f G1 T1 T2 TA2 n1,
    stp true ((f,T1)::G1) T1 T2 n1 ->
    open (length G1) TA2 = T2 ->                
    stp true G1 T1 (TBind TA2) (S n1)
| stp_bind1: forall f G1 T1 T2 TA1 n1,
    stp true ((f,T1)::G1) T1 T2 n1 ->
    open (length G1) TA1 = T1 ->                
    stp true G1 (TBind TA1) T2 (S n1)
... or at least...
*)
| stp_bindx: forall f G1 T1 T2 TA1 TA2 n1,
    bound_fvs (length G1) G1 ->
    bound_fv (length G1) TA1 ->
    bound_fv (length G1) TA2 ->
    stp true ((f,T1)::G1) T1 T2 n1 ->
    open (length G1) TA1 = T1 ->
    open (length G1) TA2 = T2 ->
    stp true G1 (TBind TA1) (TBind TA2) (S n1)
| stp_transf: forall G1 T1 T2 T3 n1 n2,
    stp true G1 T1 T2 n1 ->
    stp false G1 T2 T3 n2 ->           
    stp false G1 T1 T3 (S (n1+n2))

| stp_wrapf: forall G1 T1 T2 n1,
    stp true G1 T1 T2 n1 ->
    stp false G1 T1 T2 (S n1)       
.


Tactic Notation "stp_cases" tactic(first) ident(c) :=
  first;
  [ 
    Case_aux c "Bool < Bool" |
    Case_aux c "Fun < Fun" |
    Case_aux c "Mem < Mem" |
(*
    Case_aux c "Bind < Bind" |
    Case_aux c "T & ? < T" |
    Case_aux c "? & T < T" |
    Case_aux c "? < ? & ?" |
*)
    Case_aux c "? < Sel" |
    Case_aux c "Sel < ?" |
    Case_aux c "Sel < Sel" |
    Case_aux c "Bind < Bind" |
    Case_aux c "Trans" |
    Case_aux c "Wrap"
  ].


Hint Resolve ex_intro.

Hint Constructors stp.

Definition stpd b G1 T1 T2 := exists n, stp b G1 T1 T2 n.

Hint Unfold stpd.

Ltac ep := match goal with
             | [ |- stp ?M ?G1 ?T1 ?T2 ?N ] => assert (exists (x:nat), stp M G1 T1 T2 x) as EEX
           end.

Ltac eu := match goal with
             | H: stpd _ _ _ _ |- _ => destruct H
(*             | H: exists n: nat ,  _ |- _  =>
               destruct H as [e P] *)
           end.

Lemma stpd_bool: forall G1,
    stpd true G1 TBool TBool.
Proof. intros. exists 0. eauto. Qed.
Lemma stpd_fun: forall m G1 T11 T12 T21 T22,
    stpd false G1 T21 T11 ->
    stpd true G1 T12 T22 ->
    stpd true G1 (TFun m T11 T12) (TFun m T21 T22).
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_mem: forall G1 T11 T12 T21 T22,
    stpd false G1 T21 T11 ->
    stpd true G1 T12 T22 ->
    stpd true G1 (TMem T11 T12) (TMem T21 T22).
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_sel2: forall x T1 TX G1,
    index x G1 = Some TX ->
    stpd true G1 TX (TMem T1 TTop) ->
    stpd true G1 T1 (TSel x).
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_sel1:  forall x T2 TX G1,
    index x G1 = Some TX ->
    stpd true G1 TX (TMem TBot T2) ->
    stpd true G1 (TSel x) T2.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_selx: forall x TX TL TU G1,
    index x G1 = Some TX ->
    tresolve x TX (TMem TL TU) ->
    stpd true G1 (TSel x) (TSel x).
Proof. intros. repeat eu. exists 0. eauto. Qed.
Lemma stpd_bindx: forall f G1 T1 T2 TA1 TA2,
    bound_fvs (length G1) G1 ->
    bound_fv (length G1) TA1 ->
    bound_fv (length G1) TA2 ->
    stpd true ((f,T1)::G1) T1 T2 ->
    open (length G1) TA1 = T1 ->
    open (length G1) TA2 = T2 ->
    stpd true G1 (TBind TA1) (TBind TA2).
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_transf: forall G1 T1 T2 T3,
    stpd true G1 T1 T2 ->
    stpd false G1 T2 T3 ->           
    stpd false G1 T1 T3.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_wrapf: forall G1 T1 T2,
    stpd true G1 T1 T2 ->
    stpd false G1 T1 T2. 
Proof. intros. repeat eu. eauto. Qed.





Ltac index_subst := match goal with
                 | H1: index ?x ?G = ?V1 , H2: index ?x ?G = ?V2 |- _ => rewrite H1 in H2; inversion H2; subst
                 | _ => idtac
               end.

Lemma stp0f_trans: forall n n1 n2 G1 T1 T2 T3,
    stp false G1 T1 T2 n1 ->
    stp false G1 T2 T3 n2 ->
    n1 <= n ->
    stpd false G1 T1 T3.
Proof.
  intros n. induction n.
  - Case "z".
    intros. assert (n1 = 0). omega. subst. inversion H.
  - Case "S n".
    intros. inversion H.
    + eapply stpd_transf. eexists. eapply H2. eapply IHn. eapply H3. eapply H0. omega.
    + eapply stpd_transf. eexists. eapply H2. eexists. eapply H0.
Qed.  

Definition trans_on n1 := 
                      forall  m T1 T2 T3 G1, 
                      stp m G1 T1 T2 n1 ->
                      stpd true G1 T2 T3 ->
                      stpd true G1 T1 T3.
Hint Unfold trans_on.

Definition trans_up n := forall n1, n1 <= n ->
                      trans_on n1.
Hint Unfold trans_up.

Lemma trans_le: forall n n1,
                      trans_up n ->
                      n1 <= n ->
                      trans_on n1
.
Proof. intros. unfold trans_up in H. eapply H. eauto. Qed.

Lemma closed_open_up_rec: forall k j x T,
  k >= j ->
  closed_rec j (open_rec k x T) ->
  closed_rec (S k) T.
Proof.
  intros k j x T Hcmp H.
  generalize dependent j. generalize dependent k.
  induction T;
    intros k j Hcmp H;
    eauto; try solve [inversion H; subst; eauto].
  - Case "SelB".
    unfold open_rec in H.
    remember (beq_nat k i). destruct b.
    + apply cl_selb. apply beq_nat_eq in Heqb. subst. omega.
    + inversion H. subst. apply cl_selb. omega.
  - Case "Bind".
    apply cl_bind. apply IHT with (j:=(S k)). omega. inversion H. subst.
    apply closed_upgrade with (i:=(S j)). assumption. omega.
Qed.

Lemma closed_open_up: forall x T,
  closed (open x T) ->
  closed_rec 1 T.
Proof.
  intros x T H. unfold closed in H. unfold open in H.
  apply closed_open_up_rec with (x:=x) (j:=0).
  - omega.
  - assumption.
Qed.

Lemma stp_closed: forall m G T1 T2 n,
  stp m G T1 T2 n ->
  closed T1 /\ closed T2.
Proof.
  intros. stp_cases (induction H) Case; eauto;
   try solve [inversion IHstp; split; eauto];
   try solve [inversion IHstp1; inversion IHstp2; split; eauto];
   try solve [inversion IHstp as [IHX IHMem]; inversion IHMem; subst; split; eauto].
  - Case "Bind < Bind".
    inversion IHstp as [IHstp1 IHstp2]. subst. unfold closed.
    split; solve [apply cl_bind; apply closed_open_up with (x:=length G1); assumption].
Qed.

Lemma index_range: forall {X} i G (T:X),
  index i G = Some T ->
  i < length G.
Proof.
  intros X i G T H. induction G.
  - inversion H.
  - simpl. simpl in H.
    remember (beq_nat i (length G)).
    destruct b.
    + apply beq_nat_eq in Heqb. omega.
    + apply lt_S. apply IHG. destruct a as [j G']. assumption.
Qed.

Lemma index_neq: forall {X} i j G (T:X),
  index i G = Some T ->
  j >= length G ->
  i <> j.
Proof.
  intros. apply index_range in H. omega.
Qed.

Lemma stp_bound_fv: forall m G T1 T2 n,
  stp m G T1 T2 n ->
  bound_fv (length G) T1 /\ bound_fv (length G) T2.
Proof.
  intros m G T1 T2 n H. stp_cases (induction H) Case; eauto;
  try solve [
    inversion IHstp1; inversion IHstp2;
    split; try constructor; assumption].
  - Case "? < Sel".
    inversion IHstp as [IHX IHMem]. inversion IHMem; subst.
    split; eauto. constructor. unfold ">".
    eapply index_range. apply H.
  - Case "Sel < ?".
    inversion IHstp as [IHX IHMem]. inversion IHMem; subst.
    split; eauto. constructor. unfold ">".
    eapply index_range. apply H.
  - Case "Sel < Sel".
    split; constructor; eapply index_range; eauto.
Qed.

Lemma bound_fv_inc: forall u T,
  bound_fv u T ->
  bound_fv (S u) T.
Proof.
  intros u T H. induction H; eauto.
Qed.

Lemma stp1_bound_fv: forall m G T1 T2 n,
  stp m G T1 T2 n ->
  bound_fv (length G) T1.
Proof.
  intros m G T1 T2 n H.
  apply (proj1 (stp_bound_fv m G T1 T2 n H)).
Qed.

Lemma stp2_bound_fv: forall m G T1 T2 n,
  stp m G T1 T2 n ->
  bound_fv (length G) T2.
Proof.
  intros m G T1 T2 n H.
  apply (proj2 (stp_bound_fv m G T1 T2 n H)).
Qed.

Lemma index_shrink: forall {X} i x (Tx:X) G (T:X),
  index i ((x,Tx)::G) = Some T ->
  i < length G ->
  index i G = Some T.
Proof.
  intros. inversion H.
  remember (beq_nat i (length G)).
  induction b.
  + apply beq_nat_eq in Heqb. omega.
  + reflexivity.
Qed.

Lemma index_ext_same: forall {X} G x x' (T:X) (T':X),
              index x G = Some T ->
              index x ((x',T')::G) = Some T.
Proof.
  intros X G x x' T T' H.
  assert (x < length G) as A by solve [eapply index_range; apply H].
  generalize dependent T'. generalize dependent x'.
  destruct G.
  - inversion H.
  - assert (beq_nat x (S (length G)) = false) as A'.
      apply false_beq_nat. simpl in A. omega.
    intros x' T'. destruct p as [x1 T1].
    simpl. rewrite A'.
    remember (beq_nat x (length G)).
    destruct b.
    + inversion H. rewrite <- Heqb. reflexivity.
    + inversion H. rewrite <- Heqb. reflexivity.
Qed.

Lemma update_ext_same: forall {X} G x x' (T:X) (T':X) Gu (Tu:X),
              index x G = Some T ->
              update x Tu G = Gu ->
              update x Tu ((x',T')::G) = (x',T')::Gu.
Proof.
  intros X G x x' T T' Gu Tu H Hu.
  assert (x < length G) as A by solve [eapply index_range; apply H].
  generalize dependent T'. generalize dependent x'.
  destruct G.
  - inversion H.
  - assert (beq_nat x (S (length G)) = false) as A'.
      apply false_beq_nat. simpl in A. omega.
    intros x' T'. destruct p as [x1 T1].
    simpl. rewrite A'.
    remember (beq_nat x (length G)).
    destruct b.
    + inversion Hu. unfold update. rewrite <- Heqb. reflexivity.
    + inversion Hu. unfold update. rewrite <- Heqb. reflexivity.
Qed.

Lemma stp_ext_open: forall n x Tx y G T1 T2,
  bound_fvs (length G) G ->
  bound_fv (S (length G)) Tx ->
  bound_fv (length G) T1 ->
  bound_fv (length G) T2 ->
  stp true ((x,Tx)::(y,(open (length G) T1))::G) (open (length G) T1) (open (length G) T2) n ->
  stp true ((y,(open (length ((x,Tx)::G)) T1))::(x,Tx)::G) (open (length ((x,Tx)::G)) T1) (open (length ((x,Tx)::G)) T2) n.
Proof.
 admit.
(*
  intros n x Tx y G T1 T2 Henv HTx HT1 HT2 H.
  simpl.
  induction T1; induction T2; try solve [compute in H; inversion H].

  compute in H. inversion H. subst. inversion HT2. subst.
  compute. apply stp_sel2 with (TX:=TX).
  apply index_shrink in H1. apply index_shrink in H1.
  apply index_ext_same. apply index_ext_same.
  assumption.
  omega. simpl. omega.
  assumption.

  simpl.
  remember (open (length G) T1) as TO1.
  remember (open (length G) T2) as TO2.
  remember (open (S (length G)) T1) as TS1.
  remember (open (S (length G)) T2) as TS2.
  induction T1. subst. inversion H. subst. inversion H2.
  symmetry in HeqTO1. symmetry in HeqTO2.
  generalize dependent TS2. generalize dependent TS1.
  stp_cases (induction H) Case; intros TS1 TS2.
  - Case "Bool < Bool".
    apply open_TBool in HeqTO1. apply open_TBool in HeqTO2. subst.
    simpl. compute. apply stp_bool.
  - Case "Fun < Fun".
    apply open_TFun in HeqTO1. apply open_TFun in HeqTO2.
    inversion HeqTO1 as [TO11 [TO12 [HO1 [HO11 HO12]]]].
    inversion HeqTO2 as [TO21 [TO22 [HO2 [HO21 HO22]]]].
    subst. simpl. apply stp_fun.
    + fold open_rec. apply IHstp1.
*)
Qed.

Lemma stp_ext: forall m G T1 T2 n x Tx,
  stp m G T1 T2 n ->
  bound_fv (S (length G)) Tx ->
  stp m ((x,Tx)::G) T1 T2 n.
Proof.
  intros m G T1 T2 n x Tx H Hmax.
  stp_cases (induction H) Case; eauto.
  - Case "? < Sel". eapply stp_sel2.
      eapply index_ext_same. apply H. apply IHstp.
      assumption.
  - Case "Sel < ?". eapply stp_sel1.
      eapply index_ext_same. apply H. apply IHstp.
      assumption.
  - Case "Sel < Sel". eapply stp_selx.
      eapply index_ext_same. apply H. apply H0.
  - Case "Bind < Bind". eapply stp_bindx.
    + subst. apply bound_fvs_cons. simpl. assumption.
    + subst. simpl. apply bound_fv_inc. assumption.
    + subst. simpl. apply bound_fv_inc. assumption.
    + subst. eapply stp_ext_open.
        assumption.
        assumption.
        apply H0.
        apply H1.
        apply IHstp.
        simpl. apply bound_fv_inc. assumption.
    + reflexivity.
    + reflexivity.
Qed.

Lemma upd_hit: forall {X} G G' x x' (T:X) T',
              index x G = Some T ->
              update x' T' G = G' ->
              beq_nat x x' = true ->
              index x G' = Some T'.
Proof. admit. Qed.
Lemma upd_miss: forall {X} G G' x x' (T:X) T',
              index x G = Some T ->
              update x' T' G = G' ->
              beq_nat x x' = false ->
              index x G' = Some T.
Proof. admit. Qed.

Lemma stp_narrow: forall m G1 T1 T2 n1,
  stpd m G1 T1 T2 ->
                    
  forall x TX1 TX2 G1',

    index x G1 = Some TX2 ->
    update x TX1 G1 = G1' ->
    stp true G1' TX1 TX2 n1 ->
    trans_on n1 ->

    stpd m G1' T1 T2.  
Proof.
  intros m G1 T1 T2 n1 H. destruct H as [n2 H].
  induction H; intros.
  - Case "Bool". 
    intros. eapply stpd_bool.
  - Case "Fun". 
    intros. eapply stpd_fun. eapply IHstp1; eauto. eapply IHstp2; eauto.
  - Case "Mem". 
    intros. eapply stpd_mem. eapply IHstp1; eauto. eapply IHstp2; eauto.
  - Case "Sel2". intros.
    { case_eq (beq_nat x x0); intros E.
      (* hit updated binding *)
      + assert (x = x0) as EX. eapply beq_nat_true_iff; eauto. subst. index_subst. index_subst. 
        eapply stpd_sel2. eapply upd_hit; eauto. eapply H4. eapply H3. eapply IHstp; eauto.
      (* other binding *)
      + assert (x <> x0) as EX. eapply beq_nat_false_iff; eauto.
        eapply stpd_sel2. eapply upd_miss; eauto. eapply IHstp. eapply H1. eauto. eauto. eauto.
    }
  - Case "Sel1". intros.
    { case_eq (beq_nat x x0); intros E.
      (* hit updated binding *)
      + assert (x = x0) as EX. eapply beq_nat_true_iff; eauto. subst. index_subst. index_subst. 
        eapply stpd_sel1. eapply upd_hit; eauto. eapply H4. eapply H3. eapply IHstp; eauto.
      (* other binding *)
      + assert (x <> x0) as EX. eapply beq_nat_false_iff; eauto.
        eapply stpd_sel1. eapply upd_miss; eauto. eapply IHstp. eapply H1. eauto. eauto. eauto.
    }
  - Case "Selx". eapply stpd_selx.
  - Case "Bindx". eapply stpd_bindx. eapply IHstp.
      eapply index_ext_same. eapply H2.
      eapply update_ext_same. eapply H2. eapply H3.
  - Case "Trans". eapply stpd_transf. eapply IHstp1; eauto. eapply IHstp2; eauto.
  - Case "Wrap". eapply stpd_wrapf. eapply IHstp; eauto.
Qed.


Inductive simple_type: ty -> Prop :=
| simple_mem: forall T1,
  simple_type (TMem T1 T1)  (* otherwise, would need trans_on T1 T2 *)
.                           

(* no induction, no trans (?) *)
(* proper realizability evidence? *)
Lemma stpd_trans_lo: forall G1 T1 T2 TX,
  stpd true G1 T1 T2 ->                     
  stpd true G1 TX (TMem T2 TTop) ->
  simple_type TX ->
  stpd true G1 TX (TMem T1 TTop).
Proof.
  intros. repeat eu. inversion H0; inversion H1.
  - eapply stpd_mem. eapply stpd_transf. eexists. eapply H. eexists. subst. eauto. eauto. 
  - subst. inversion H4. (* NEED TO HANDLE THIS CASE? PROBABLY YES .... *)
Qed.


(* proper realizability evidence? *)
Lemma stpd_trans_hi: forall G1 T1 T2 TX n1,
                       (* trans_on *)
  stpd true G1 T1 T2 ->                     
  stp true G1 TX (TMem TBot T1) n1 ->
  simple_type TX ->
  trans_up n1 ->
  stpd true G1 TX (TMem TBot T2).
Proof.
  intros.
  inversion H1. subst TX.
  inversion H0. subst.
  assert (trans_on n2) as IH. { eapply trans_le; eauto. omega. }
  eapply stpd_mem. eauto. eapply IH; eauto.
Qed.

(* need to invert mem. will require proper realizability
   evidence *)
Lemma stpd_trans_cross: forall G1 TX T1 T2 n1,
                          (* trans_on *)
  stp true G1 TX (TMem T1 TTop) n1 ->
  stpd true G1 TX (TMem TBot T2) ->
  simple_type TX ->
  trans_up n1 ->
  stpd true G1 T1 T2.
Proof.
  intros.
  inversion H1. subst TX.
  inversion H. destruct H0. inversion H0. subst.
  assert (trans_on n0) as IH. { eapply trans_le. eauto. omega. }
  eapply IH. eauto. eexists. eauto.
Qed.


Lemma stp1_trans: forall n, trans_up n.
Proof.
  intros n. induction n.
  Case "z". admit.
  Case "S n".
  unfold trans_up. intros n1 NE  b T1 T2 T3 G1 S12 S23.
  destruct S23 as [n2 S23].

  (* SHOTGUN: construct `simple` evidence out of thin air.
     This needs to become a parameter, but need to figure out
     how to integrate it exactly. *)
  assert (forall x T, index x G1 = Some T -> simple_type T) as IMP. admit.
  
  stp_cases(inversion S12) SCase.  (* stp_cases(inversion S23) SSCase;  subst; *)
  
  - SCase "Bool < Bool". inversion S23; subst; try solve by inversion.
    + SSCase "Bool". eapply stpd_bool; eauto.
    + SSCase "Sel2". eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto.
  - SCase "Fun < Fun". inversion S23; subst; try solve by inversion.
    + SSCase "Fun". inversion H10. subst.
      eapply stpd_fun.
      * eapply stp0f_trans; eauto.
      * assert (trans_on n3) as IH.
        { eapply trans_le; eauto. omega. }
        eapply IH; eauto.
    + SSCase "Sel2". eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto.
  - SCase "Mem < Mem". inversion S23; subst; try solve by inversion.
    + SSCase "Mem". inversion H10. subst.
      eapply stpd_mem.
      * eapply stp0f_trans; eauto.
      * assert (trans_on n3) as IH.
        { eapply trans_le; eauto. omega. }
        eapply IH; eauto.
    + SSCase "Sel2". eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto.
  - SCase "? < Sel". inversion S23; subst; try solve by inversion.
    + SSCase "Sel2". eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto.
    + SSCase "Sel1". (* interesting case *)
      index_subst.
      assert (trans_up n0) as IH.
      { unfold trans_up. intros. apply IHn. omega. }
      inversion H10. subst. index_subst. eapply stpd_trans_cross; eauto.
    + SSCase "Selx". inversion H8. index_subst. subst. index_subst. subst.
      eapply stpd_sel2. eauto. eauto.
  - SCase "Sel < ?".
      (* TODO: use stpd_trans_hi? *)
      assert (trans_up n0) as IH.
      { unfold trans_up. intros. eapply IHn. omega. }
      eapply stpd_sel1. eauto. eapply stpd_trans_hi; eauto.
  - SCase "Sel < Sel". inversion S23; subst; try solve by inversion.
     + SSCase "Sel2". eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto.
     + SSCase "Sel1". inversion H8. index_subst. subst. index_subst. subst.
       eapply stpd_sel1. eauto. eauto.
     + SSCase "Selx". inversion H6. subst. repeat index_subst.
       eapply stpd_selx; eauto.
  - SCase "Trans". subst.
    assert (trans_on n3) as IH2.
    { eapply trans_le; eauto. omega. }
    assert (trans_on n0) as IH1.
    { eapply trans_le; eauto. omega. }
    assert (stpd true G1 T4 T3) as S123.
    { eapply IH2; eauto. }
    destruct S123.
    eapply IH1; eauto.
  - SCase "Wrap". subst.
    assert (trans_on n0) as IH.
    { eapply trans_le; eauto. omega. }
    eapply IH; eauto.
Qed.


End DOT.

