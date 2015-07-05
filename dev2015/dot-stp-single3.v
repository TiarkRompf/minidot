Require Export SfLib.

Require Export Arith.EqNat.

Require Export Arith.Le.

(* 
subtyping: 
  - looking at single-environment case again.

  - WIP: trying to figure out pushback story for binds.

    this version explores an stp metric based on n levels
    of trans-freedom, with n incremented when going into
    bounds.

    the trans pushback statement holds for n levels if
    there is realizability evidence for n levels of bounds
    and if the environment is concrete at level 0.

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

Definition closed j T := closed_rec j T.


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

(* this is the version we can narrow *)

Fixpoint plus (a: list nat) (b: list nat) :=
  match a,b with
    | x::xs, y::ys => (x+y)::(plus xs ys)
    | nil, ys => ys
    | xs, nil => xs
  end.

Fixpoint less (a: list nat) (b: list nat): Prop :=
  match a,b with
    | x::xs, y::ys => x < y \/ (x = y /\ less xs ys)
    | xs, ys => xs = nil
end.

Inductive itp: nat -> ty -> Prop :=
| itp_refl: forall T,
    itp 0 T
| itp_mem: forall T n,
    itp n T ->
    itp (S n) (TMem T T).


Inductive stp : nat -> tenv -> ty -> ty -> nat -> Prop := 

| stp_bot: forall G1 T n1 d1,
    stp (S d1) G1 TBot T (S n1)
             
| stp_top: forall G1 T n1 d1,
    stp (S d1) G1 T TTop (S n1)
             
| stp_bool: forall G1 n1 d1,
    stp (S d1) G1 TBool TBool (S n1)

| stp_fun: forall m G1 T11 T12 T21 T22 n1 n2 d3,
    stp 0 G1 T21 T11 n1 ->
    stp 0 G1 T12 T22 n2 ->
    stp (S d3) G1 (TFun m T11 T12) (TFun m T21 T22) (S (n1+n2))

| stp_mem: forall G1 T11 T12 T21 T22 n1 n2 d2,
    stp 0 G1 T21 T11 n1 ->
    stp d2 G1 T12 T22 n2 ->
    stp (S d2) G1 (TMem T11 T12) (TMem T21 T22) (S (n1+n2))

(*
| stp_sel2: forall x T1 TX G1 n1 d1,
    index x G1 = Some (TMem TX) ->
    stp d1 G1 T1 TX n1 ->
    stp d1 G1 T1 (TSel x) (S n1)
| stp_sel1: forall x T2 TX G1 n1 d1,
    index x G1 = Some (TMem TX) ->
    stp d1 G1 TX T2 n1 ->
    stp d1 G1 (TSel x) T2 (S n1)
*)
        
| stp_sel2: forall x T1 TX G1 n1 d1,
    index x G1 = Some TX ->
    itp d1 TX ->          
    stp d1 G1 TX (TMem T1 TTop) n1 ->
    stp d1 G1 T1 (TSel x) (S n1)
| stp_sel1: forall x T2 TX G1 n1 d1,
    index x G1 = Some TX ->
    itp d1 TX ->          
    stp d1 G1 TX (TMem TBot T2) n1 ->
    stp d1 G1 (TSel x) T2 (S n1)


| stp_selx: forall x G1 n1 d1,
    stp (S d1) G1 (TSel x) (TSel x) (S n1)
                  
| stp_bindx: forall G1 T1 T2 TA1 TA2 n1 d1,
    stp (S d1) ((length G1,T1)::G1) T1 T2 n1 ->
    open (length G1) TA1 = T1 ->                
    open (length G1) TA2 = T2 ->
    stp (S d1) G1 (TBind TA1) (TBind TA2) (S n1)

| stp_wrapf: forall G1 T1 T2 n1 d,
    stp d G1 T1 T2 n1 ->
    stp 0 G1 T1 T2 (S n1)

| stp_transf: forall G1 T1 T2 T3 n1 n2 d,
    stp d G1 T1 T2 n1 ->
    stp 0 G1 T2 T3 n2 ->
    stp 0 G1 T1 T3 (S (n1+n2)) 
.

Hint Resolve ex_intro.

Hint Constructors stp.


(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)



Definition stpd b G1 T1 T2 := exists n, stp b G1 T1 T2 n.

Hint Unfold stpd.

Ltac ep := match goal with
             | [ |- stp ?M ?G1 ?T1 ?T2 ?N ] => assert (exists (x:nat), stp M G1 T1 T2 x) as EEX
           end.

Ltac eu := match goal with
             | H: stpd _ _ _ _ |- _ => destruct H
             | H: exists n: nat ,  _ |- _  => destruct H
           end.



Ltac index_subst := match goal with
                 | H1: index ?x ?G = ?V1 , H2: index ?x ?G = ?V2 |- _ => rewrite H1 in H2; inversion H2; subst
                 | _ => idtac
               end.


Lemma upd_length_same: forall {X} G x (T:X),
              length G = length (update x T G).
Proof.
  intros X G x T. induction G.
  - simpl. reflexivity.
  - destruct a as [n' Ta]. simpl.
    remember (beq_nat x (length G)).
    destruct b.
    + simpl. reflexivity.
    + simpl. f_equal. apply IHG.
Qed.

Lemma upd_hit: forall {X} G G' x x' (T:X) T',
              index x G = Some T ->
              update x' T' G = G' ->
              beq_nat x x' = true ->
              index x G' = Some T'.
Proof.
  intros X G G' x x' T T' Hi Hu Heq.
  subst. induction G.
  - simpl in Hi. inversion Hi.
  - destruct a as [n' Ta]. simpl in Hi.
    remember (beq_nat x (length G)).
    apply beq_nat_true in Heq.
    destruct b.
    + simpl.
      apply beq_nat_eq in Heqb.
      subst. subst.
      rewrite <- beq_nat_refl.
      simpl.
      rewrite <- beq_nat_refl.
      reflexivity.
    + simpl.
      subst.
      rewrite <- Heqb.
      simpl.
      assert ((length G) = (length (update x' T' G))) as HnG. {
        apply upd_length_same.
      }
      rewrite <- HnG.
      rewrite <- Heqb.
      apply IHG.
      apply Hi.
Qed.

Lemma upd_miss: forall {X} G G' x x' (T:X) T',
              index x G = Some T ->
              update x' T' G = G' ->
              beq_nat x x' = false ->
              index x G' = Some T.
Proof.
  intros X G G' x x' T T' Hi Hu Heq.
  subst. induction G.
  - simpl in Hi. inversion Hi.
  - destruct a as [n' Ta]. simpl in Hi. simpl.
    remember (beq_nat x (length G)).
    destruct b.
    + apply beq_nat_eq in Heqb.
      subst.
      rewrite beq_nat_sym. rewrite Heq.
      simpl.
      assert ((length G) = (length (update x' T' G))) as HnG. {
        apply upd_length_same.
      }
      rewrite <- HnG.
      rewrite <- beq_nat_refl.
      apply Hi.
    + remember (beq_nat x' (length G)) as b'.
      destruct b'.
      * simpl.
        rewrite <- Heqb.
        apply Hi.
      * simpl.
        assert ((length G) = (length (update x' T' G))) as HnG. {
          apply upd_length_same.
        }
        rewrite <- HnG.
        rewrite <- Heqb.
        apply IHG.
        apply Hi.
Qed.


Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  Case "nil". intros. inversion H.
  Case "cons".
  intros. inversion H. destruct a.
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

  
Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply index_max. eauto.
  assert (n <> length vs). omega.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff; eauto.
  unfold index. unfold index in H. rewrite H. rewrite E. destruct a. reflexivity.
Qed.

Lemma update_extend: forall X (T1: X) (TX1: X) G1 G1' x a,
  index x G1 = Some T1 ->
  update x TX1 G1 = G1' ->
  update x TX1 (a::G1) = (a::G1').
Proof.
  intros X T1 TX1 G1 G1' x a Hi Hu.
  assert (x < length G1) as Hlt. {
    eapply index_max.
    eauto.
  }
  assert (x <> length G1) as Hneq by omega.
  assert (beq_nat x (length G1) = false) as E. {
    eapply beq_nat_false_iff; eauto.
  }
  destruct a as [n' Ta].
  simpl. rewrite E. rewrite Hu. reflexivity.
Qed.

Lemma update_pres_len: forall X (TX1: X) G1 G1' x, 
  update x TX1 G1 = G1' ->
  length G1 = length G1'.
Proof.
  intros X TX1 G1 G1' x H. subst. apply upd_length_same.
Qed.

Lemma stp_extend : forall m G1 T1 T2 x v n,
                       stp m G1 T1 T2 n ->
                       stp m ((x,v)::G1) T1 T2 n.
Proof. admit. (*intros. destruct H. eexists. eapply stp_extend1. apply H.*) Qed.





Fixpoint zeros d :=
  match d with
    | 0 => nil
    | S n => 0::(zeros n)
  end.


Ltac mzero := match goal with
             | H: _ :: _ = zeros ?d |- _ => destruct d; inversion H; simpl in H; inversion H
           end.


Lemma stp_trans0: forall n, forall n1 G1 T1 T2 T3 n2,
      stp 0 G1 T1 T2 n1 -> n1 < n ->
      stp 0 G1 T2 T3 n2 -> 
      exists n3, stp 0 G1 T1 T3 n3. (* d2 <= d1 ? *)
Proof.
  intros n. induction n; intros; inversion H; subst.
  inversion H0. inversion H0. inversion H0. inversion H0.
  - admit.
  - admit.
  - Case "wrapf". eexists. eapply stp_transf. eauto. eauto.
  - Case "transf". admit.
Qed.




Lemma stp_trans1: forall n, forall n1 G1 T1 T2 T3 n2 d1 d2,
      itp d2 T1 ->
      stp d1 G1 T1 T2 n1 -> n1 < n ->
      stp d2 G1 T2 T3 n2 -> d2 <= d1 ->
      exists n3, stp d2 G1 T1 T3 n3. (* 0 < d1 ? *)
Proof.
  intros n1. induction n1.
  admit.
  intros.
  destruct d2.
  (* zero: rhs may use trans *)
  assert (stp 1 G1 T1 T2 n0). admit.  (* TODO: we have d1, but we need 1 !*)
  eexists. eapply stp_transf. eauto. eauto.
  (* > 0 no immediate trans in rhs *)
  
  inversion H0; subst.
  - Case "bot". admit.
  - Case "top". admit.
  - Case "bool". admit.
  - Case "fun". admit.
  - Case "mem". inversion H2; subst.
    + SCase "top". eauto.
    + SCase "mem".
      (* regular induction on upper bound *)
      assert (exists n3, stp d2 G1 T12 T4 n3).
      eapply IHn1. inversion H. eauto. eauto. omega. eauto. omega.
      (* call zero case on lower bound (can't induct because taking from right) *)
      assert (exists n3, stp 0 G1 T2 T11 n3).
      eapply stp_trans0. eauto. eauto. eauto.
      eu. eu.
      eexists. eapply stp_mem; eauto.
    + SCase "sel2".
      inversion H7. subst. inversion H8. subst.
      (* already need to invert TX < (TMem (TMem T4)) *)
      assert (exists n3, stp 0 G1 (TMem T11 T12) T n3).
      eapply stp_trans0. eauto. eauto. eauto.
      eu.
      (* now main rule *)
      eexists. eapply stp_sel2. eauto. eauto. eapply stp_mem; eauto.
  - Case "sel2". inversion H1; subst.
    + SCase "top". admit.
    + SCase "sel2". admit.
    + SCase "sel1". admit. (**)
    + SCase "selx". admit.
    + SCase "wrap". admit.
    + SCase "trans". admit.
  - Case "sel1". admit.
  - Case "selx". admit.
  - Case "bindx". admit. (**)
  - Case "wrapf". admit. (**)
  - Case "trans". admit.
Qed.


Lemma stp_narrow: forall n, forall m G1 T1 T2 n1 n0,
  stp m G1 T1 T2 n0 -> n0 < n ->                  
  forall x TX1 TX2 G1' d2,
    index x G1 = Some TX2 ->
    update x TX1 G1 = G1' ->
    stp d2 G1' TX1 TX2 n1 -> m <= d2 ->
    exists n3, stp m G1' T1 T2 n3.
Proof.
  intros n. induction n.
  (* z *) intros. admit. 
  (* s n *)
  intros m G1 T1 T2 n1 nz H NE.
  inversion H; intros.
  - Case "Top". admit. 
  - Case "Bool". admit. 
  - Case "Fun". admit.
  - Case "Mem". subst.
    assert (exists n3 : nat, stp 0 (update x TX1 G1) T3 T0 n3).
    eapply IHn; eauto. omega. omega.
    assert (exists n3 : nat, stp d2 (update x TX1 G1) T0 T3 n3).
    eapply IHn; eauto. omega. omega.
    eu. eu.
    eexists. eapply stp_mem; eauto.
  - Case "Sel2". intros.
    { case_eq (beq_nat x x0); intros E.
      (* hit updated binding *)
      + assert (x = x0) as EX. eapply beq_nat_true_iff; eauto. subst. index_subst. index_subst.

        (* narrow ind *)
        assert (exists n3, stp m (update x0 TX1 G1) TX (TMem T1) n3).
        eapply IHn. eauto. omega. eauto. eauto. eauto. omega.
        eu.
        
        (* trans with delta *)
        assert (exists n3, stp m (update x0 TX1 G1) TX1 (TMem T1) n3).
        eapply stp_trans1. eauto. eauto. eauto. omega.
        eu.
        
        eexists. eapply stp_sel2. eapply upd_hit; eauto. eauto.

      + assert (x <> x0) as EX. eapply beq_nat_false_iff; eauto.
        assert (exists n3, stp m G1' TX (TMem T1) n3).
        eapply IHn; eauto. omega.
        eu.

        eexists. eapply stp_sel2. eapply upd_miss; eauto. eauto.
    }
  - Case "Sel1". admit.
  - Case "Selx". admit.
  - Case "Bindx".
    assert (length G1 = length G1'). { eapply update_pres_len; eauto. }
    remember (length G1) as L. clear HeqL. subst L.

    admit.
    (*
    eapply stpd_bindx. {
      eapply IHn. eapply H0. omega.
      eapply index_extend; eauto.
      eapply update_extend; eauto.
      eapply stp_extend; eauto.
    }
    eauto.
    eauto. *)

  - Case "Wrap". admit. (* eapply stpd_wrapf. eapply IHn; eauto. omega. *)
  - Case "Trans". admit. (*eapply stpd_transf. eapply IHn; eauto. omega. eapply IHn; eauto. omega. *)

Qed.




(* ---------- EXPANSION / MEMBERSHIP ---------- *)
(* In the current version, expansion is an implementation
   detail. We just use it to derive some helper lemmas
   to show that implementable types have good bounds.
*)


(* expansion / membership *)
(* this is the precise version! no slack in lookup *)
(* TODO: need the name for bind? *)
Inductive exp : tenv -> ty -> ty -> Prop :=
(*
| exp_bot: forall G1,
    exp G1 TBot (TMem TTop TBot)  (* causes trouble in inv_mem: need to build stp deriv with smaller n *)
*)
| exp_mem: forall G1 T1 T2,
    exp G1 (TMem T1 T2) (TMem T1 T2)
| exp_sel: forall G1 x T T2 T3 T4 T5,
    index x G1 = Some T ->
    exp G1 T (TMem T2 T3) ->
    exp G1 T3 (TMem T4 T5) ->
    exp G1 (TSel x) (TMem T4 T5) 
.

(*
NOT NEEDED (apparently)
Lemma exp_unique: forall G1 T1 TA1 TA2 TA1L TA2L, 
  exp G1 T1 (TMem TA1L TA1) ->
  exp G1 T1 (TMem TA2L TA2) ->
  TA1 = TA2.
Proof.  Qed.
*)


(* key lemma that relates exp and stp. result has bounded size. *)
Lemma stpd_inv_mem: forall n n1 G1, 

  forall TA1 TA2 TA1L TA2L T1,
  exp G1 T1 (TMem TA1L TA1) ->
  stp2 true G1 T1 (TMem TA2L TA2) n1 ->
  n1 <= n ->
  exists n3, stp2 true G1 (TMem TA1L TA1) (TMem TA2L TA2) n3 /\ n3 <= n1. (* should be semantic eq! *)
Proof.
  intros n1. induction n1.
  (*z*) intros. inversion H0; subst; inversion H1; subst; try omega. try inversion H.
  (* s n *)
  intros. inversion H.
(*  - Case "bot". subst. exists 0. split. eapply stp_mem. eauto. eauto. inversion H0.  subst. omega. *)
  - Case "mem". subst. exists n0. auto. (*inversion H0. subst. exists n3. split. eauto. omega. *)
  - Case "sel".
    subst.
    inversion H0.
    repeat index_subst. clear H4.
    
    assert (exists n0 : nat, stp2 true G1 (TMem T2 T3) (TMem TBot (TMem TA2L TA2)) n0 /\ n0 <= n2) as S1.
    eapply (IHn1 n2). apply H7. apply H6. omega.

    destruct S1 as [? [S1 ?]]. inversion S1. subst.

    assert (exists n0 : nat, stp2 true G1 (TMem TA1L TA1) (TMem TA2L TA2) n0 /\ n0 <= n5) as S2.
    eapply (IHn1 n5). apply H8. apply H16. omega.

    destruct S2 as [? [S2 ?]].
    
    eexists. split. apply S2. omega.
Qed.


Definition env_good_bounds G1 :=
  forall TX T2 T3 x,
    index x G1 = Some TX ->
    exp G1 TX (TMem T2 T3) ->
    exists n2, stp2 true G1 T2 T3 n2.

(*
could go this route, if itp contains L<U evidence,
but currently not needed.

Lemma env_itp_gb: forall G1 n1,
  env_itp G1 n1 ->
  env_good_bounds G1.                  
Proof. Qed.
*)


(* dual case *)
Lemma stpd_build_mem: forall n1 G1, 
  forall TA1 TA2 TA1L TA2L T1,
    exp G1 T1 (TMem TA1L TA1) ->
    env_good_bounds G1 ->
    env_itp G1 -> (* to obtain itp evidence for sel1 result *)
  stp2 true G1 (TMem TA1L TA1) (TMem TA2L TA2) n1 ->
  exists n3, stp2 true G1 T1 (TMem TA2L TA2) n3.
Proof.
  (* now taking 'good bounds' evidence as input *)

  intros.
  generalize dependent n1.
  generalize dependent TA2.
  generalize dependent TA2L.
  induction H.
  - Case "mem".
    subst. eexists. eauto.
  - Case "sel".
    intros. subst.
    (* inversion H2. subst. index_subst. subst. *)
    assert (exists n3, stp2 true G1 T3 (TMem TA2L TA2) n3) as IX2. {
      eapply IHexp2. eauto. eauto. eauto.
    }
    destruct IX2 as [n4 IX2].
    (* here we need T2 < T3 to construct stp_mem *)
    (* current stragety is to get it from env_good_bounds *)
    assert (exists n2, stp2 true G1 T2 T3 n2) as IY. eauto.
    destruct IY as [? IY].
    assert (exists n3, stp2 true G1 T (TMem TBot (TMem TA2L TA2)) n3) as IX. {
      eapply IHexp1. eauto. eauto. eapply stp2_mem. eapply stp2_wrapf. eapply stp2_bot.
      apply IY. apply IX2. 
    }
    destruct IX.
    assert (itpd2 G1 T) as IZ. { eapply H1; eauto. (* from env_itp *) }
    destruct IZ.                          
    subst. eexists. eapply stp2_sel1. eauto. eauto. eauto.
    Grab Existential Variables. apply 0.
Qed.



(* trans helpers -- these are based on exp only and currently not used *)

Lemma stpde_trans_lo: forall G1 T1 T2 TX TXL TXU,
  stpd2 true G1 T1 T2 ->                     
  stpd2 true G1 TX (TMem T2 TTop) ->
  exp G1 TX (TMem TXL TXU) ->
  env_itp G1 ->
  env_good_bounds G1 ->
  stpd2 true G1 TX (TMem T1 TTop).
Proof.
  intros. repeat eu.
  assert (exists nx, stp2 true G1 (TMem TXL TXU) (TMem T2 TTop) nx /\ nx <= x) as E. eapply (stpd_inv_mem x). eauto. eauto. omega.
  destruct E as [nx [ST X]].
  inversion ST. subst.

  eapply stpd_build_mem. eauto. eauto. eauto. eapply stp2_mem. eapply stp2_transf. eauto. eauto. eauto. eauto.
Qed.

Lemma stpde_trans_hi: forall G1 T1 T2 TX n1 TXL TXU,
  stpd2 true G1 T1 T2 ->                     
  stp2 true G1 TX (TMem TBot T1) n1 ->
  exp G1 TX (TMem TXL TXU) ->
  env_itp G1 ->
  env_good_bounds G1 ->
  trans_up n1 ->
  stpd2 true G1 TX (TMem TBot T2).
Proof.
  intros. repeat eu.
  assert (exists nx, stp2 true G1 (TMem TXL TXU) (TMem TBot T1) nx /\ nx <= n1) as E. eapply (stpd_inv_mem n1). eauto. eauto. omega.
  destruct E as [nx [ST X]].
  inversion ST. subst.

  assert (trans_on n3) as IH. { eapply trans_le; eauto. omega. }
  assert (stpd2 true G1 TXU T2) as ST1. { eapply IH. eauto. eauto. }
  destruct ST1.
  eapply stpd_build_mem. eauto. eauto. eauto. eapply stp2_mem. eauto. eauto. eauto.
Qed.

(* need to invert mem. requires proper realizability evidence *)
Lemma stpde_trans_cross: forall G1 TX T1 T2 TXL TXU n1 n2 n,
                          (* trans_on *)
  stp2 true G1 TX (TMem T1 TTop) n1 ->
  stpd2 true G1 TX (TMem TBot T2) ->
  exp G1 TX (TMem TXL TXU) ->
  stp2 true G1 TXL TXU n2 ->
  trans_up n ->
  n2 <= n ->
  n1 <= n ->
  stpd2 true G1 T1 T2.
Proof.
  intros. eu.
  assert (exists n3, stp2 true G1 (TMem TXL TXU) (TMem T1 TTop) n3 /\ n3 <= n1) as SM1. eapply (stpd_inv_mem n1). eauto. eauto. omega.
  assert (exists n3, stp2 true G1 (TMem TXL TXU) (TMem TBot T2) n3 /\ n3 <= x) as SM2. eapply (stpd_inv_mem x). eauto. eauto. omega.
  destruct SM1 as [n3 [SM1 E3]].
  destruct SM2 as [n4 [SM2 E4]].
  inversion SM1. inversion SM2.
  subst. clear SM1 SM2.
  
  assert (trans_on n0) as IH0. { eapply trans_le; eauto. omega. }
  assert (trans_on n2) as IH1. { eapply trans_le; eauto. }
  eapply IH0. eauto. eapply IH1. eauto. eauto. 
Qed.

(* ----- end expansion  ----- *)



(* -- trans helpers: based on imp *)


(* if a type is realizable, it expands *)
Lemma itp_exp_internal: forall n G1, forall T1 TL TU n1 n3,
  n1 <= n ->
  itp2 G1 T1 n1 ->
  stp2 true G1 T1 (TMem TL TU) n3 ->
  exists TL1 TU1 n4 n5 n6,
    exp G1 T1 (TMem TL1 TU1) /\
    stp2 true G1 TL1 TU1 n5 /\
    stp2 true G1 (TMem TL1 TU1) (TMem TL TU) n6 /\
    itp2 G1 TU1 n4 /\
    n4 <= n /\
    n5 <= n3 /\
    n6 <= n3.
Proof.
  intros n1 G1.
  induction n1.
  Case "z". intros. inversion H; subst. inversion H0; subst; inversion H1. subst.
  Case "S n". intros. inversion H0; subst; inversion H1. subst.
  - SCase "mem".
    repeat eexists. eapply exp_mem. eauto. eauto. eauto. omega. omega. omega.
  - SCase "sel".
    index_subst.

    (* first half *)
    assert (n2 <= n1) as E. omega.
    assert (exists TL1 TU1 n4 n5 n6,
              exp G1 TX0 (TMem TL1 TU1) /\
              stp2 true G1 TL1 TU1 n5 /\
              stp2 true G1 (TMem TL1 TU1) (TMem TBot (TMem TL TU)) n6 /\
              itp2 G1 TU1 n4 /\
              n4 <= n1 /\
              n5 <= n0 /\
              n6 <= n0
           ) as IH. { eapply IHn1. apply E. eauto. eauto. }
    repeat destruct IH as [? IH].

    (* obtain stp for second half input *)
    assert (exists n, stp2 true G1 (TMem x0 x1) (TMem TBot (TMem TL TU)) n /\ n <= n0) as IX.
    { eauto. }
    repeat destruct IX as [? IX]. inversion H13. subst.

    
    assert (exists TL1 TU1 n4' n5' n6',
              exp G1 x1 (TMem TL1 TU1) /\
              stp2 true G1 TL1 TU1 n5' /\
              stp2 true G1 (TMem TL1 TU1) (TMem TL TU) n6' /\
              itp2 G1 TU1 n4' /\
              n4' <= n1 /\
              n5' <= n6 /\
              n6' <= n6
           ) as IH2. { eapply IHn1. apply H11. eauto. eauto. } 
    repeat destruct IH2 as [? IH2].
    repeat eexists. index_subst.
    eapply exp_sel. eauto. eauto. eauto. eauto. eauto. eauto. omega. omega. omega.
Qed.


Lemma itp_exp: forall G1 T1 TL TU n1 n2,
  itp2 G1 T1 n1 ->
  stp2 true G1 T1 (TMem TL TU) n2 ->
  exists TL1 TU1, exp G1 T1 (TMem TL1 TU1).
Proof.
  intros.
  assert (exists TL1 TU1 n4 n5 n6,
            exp G1 T1 (TMem TL1 TU1) /\
            stp2 true G1 TL1 TU1 n5 /\
            stp2 true G1 (TMem TL1 TU1) (TMem TL TU) n6 /\
            itp2 G1 TU1 n4 /\
            n4 <= n1 /\
            n5 <= n2 /\
            n6 <= n2
         ) as HH. eapply itp_exp_internal; eauto.
  repeat destruct HH as [? HH].
  repeat eexists. eauto.
Qed.

(* need to invert mem. requires proper realizability evidence *)
Lemma stpd_trans_cross: forall G1 TX T1 T2 n1 n2 n,
  stp2 true G1 TX (TMem T1 TTop) n1 ->
  stpd2 true G1 TX (TMem TBot T2) ->
  itp2 G1 TX n2 ->
  n1 <= n ->
  trans_up n ->
  stpd2 true G1 T1 T2.
Proof.
  intros. eu.
  assert (exists TL1 TU1, exists TL TU n4 n5 n6,
            exp G1 TX (TMem TL TU) /\
            stp2 true G1 TL TU n5 /\
            stp2 true G1 (TMem TL TU) (TMem TL1 TU1) n6 /\
            itp2 G1 TU n4 /\
            n4 <= n2 /\
            n5 <= n1 /\
            n6 <= n1
         ) as HH. { eexists. eexists. eapply itp_exp_internal; eauto. }
  repeat destruct HH as [? HH].

  eapply stpde_trans_cross; eauto. omega.
Qed.







Lemma stpd_trans_hi: forall G1 T1 T2 TX n1 n2,
  stpd2 true G1 T1 T2 ->                     
  stp2 true G1 TX (TMem TBot T1) n1 ->
  itp2 G1 TX n2 ->
  trans_up n1 ->
  stpd2 true G1 TX (TMem TBot T2).
Proof.
  intros. eu.
  generalize dependent T1.
  generalize dependent T2.
  generalize dependent x.
  generalize dependent n1.
  induction H1; intros.
  - inversion H0.
  - inversion H0.
  - Case "mem".
    inversion H0. subst.
    assert (trans_on n5) as IH. { eapply trans_le; eauto. omega. }

    eapply stpd2_mem. eauto. eauto. eapply IH. eauto. eauto.
  - Case "sel".
    inversion H3. subst. index_subst.
    assert (trans_up n2) as IH. { unfold trans_up. intros. eapply trans_le; eauto. omega. }
    eapply stpd2_sel1. eauto. eauto.
    + eapply IHitp. eauto. 
      (* arg: (TMem TBot T1) <: (TMem TBot T2) *)
      eapply stp2_mem. eapply stp2_wrapf. eapply stp2_bot. eapply stp2_bot. eapply H0. eapply H7.
Grab Existential Variables. apply 0. apply 0.
Qed.


Inductive trivial_stp: ty -> ty -> Prop :=
| trivial_mem: forall T1 T2,
    trivial_stp (TMem T1 TTop) (TMem T2 TTop)
| trivial_nest: forall T1 T2,
    trivial_stp T1 T2 ->
    trivial_stp (TMem TBot T1) (TMem TBot T2).

(* TODO: should be able to do this without itp *)
(* by induction on TX < T1 *)
Lemma stpd_trans_triv: forall G1 T1 T2 TX n2,
  trivial_stp T1 T2 ->
  stpd2 true G1 T1 T2 ->                     
  stpd2 true G1 TX T1 ->
  itp2 G1 TX n2 ->
  stpd2 true G1 TX T2.
Proof.
  intros. eu.
  generalize dependent T1.
  generalize dependent T2.
  generalize dependent x.
  induction H2; intros.
  - inversion H; subst; inversion H1.
  - inversion H; subst; inversion H1.
  - Case "mem".
    (* remember (TMem TL TU) as TX.
    generalize dependent TX. *)
    induction H.
    + SCase "trivial mem".
      inversion H0. inversion H1. subst. inversion H. subst.
      eapply stpd2_mem. eapply stp0f2_trans. eauto. eauto. eauto. eauto. eauto.
    + SCase "trivial nest".
      inversion H0. inversion H1. subst. inversion H3. subst.
      eapply stpd2_mem. eauto. eauto. eapply IHitp. eauto. eauto. eauto.
  - Case "sel".
    inversion H0.
    + SCase "trivial mem". subst.
      inversion H3. subst. index_subst.
      eapply stpd2_sel1. eauto. eauto. eapply IHitp. eauto. eapply trivial_nest. eauto.
      eapply stpd2_mem. eauto. eauto. eauto. eauto.
    + SCase "trivial nest". subst.
      inversion H3. subst. index_subst.
      eapply stpd2_sel1. eauto. eauto. eapply IHitp. eauto. eapply trivial_nest. eauto.
      eapply stpd2_mem. eauto. eauto. eauto. eauto.
Grab Existential Variables. apply 0. apply 0. apply 0. apply 0.
Qed.



Lemma stpd_trans_lo: forall G1 T1 T2 TX n2,
  stpd2 true G1 T1 T2 ->                     
  stpd2 true G1 TX (TMem T2 TTop) ->
  itp2 G1 TX n2 ->
  stpd2 true G1 TX (TMem T1 TTop).
Proof.
  intros. eapply stpd_trans_triv. eapply trivial_mem.
  eapply stpd2_mem. eapply stpd2_wrapf. eauto. eauto. eauto. eauto. eauto.
  Grab Existential Variables. apply 0. apply 0.
Qed.


(* proper trans lemma *)
Lemma stp2_trans: forall n, trans_up n.
Proof.
  intros n. induction n. {
    Case "z".
    unfold trans_up. intros n1 NE1 b G1 T1 T2 T3 S12 S23.
    destruct S23 as [? S23].
    inversion NE1. subst n1.
    inversion S12; subst.
    - SCase "Bot < ?". eapply stpd2_bot.
    - SCase "? < Top". inversion S23; subst.
      + SSCase "Top". eauto.
      + SSCase "Sel2".
        assert (index x0 G1 = Some TX). eauto.
        (* eapply IMP in H. destruct H. subst. *)
        eapply stpd2_sel2. eauto. eauto. eapply stpd_trans_lo; eauto.
    - SCase "Bool < Bool". eauto.
  }
  
  Case "S n".
  unfold trans_up. intros n1 NE1 b G1 T1 T2 T3 S12 S23.
  destruct S23 as [n2 S23].

  stp_cases(inversion S12) SCase. 
  - SCase "Bot < ?". eapply stpd2_bot.
  - SCase "? < Top". subst. inversion S23; subst.
    + SSCase "Top". eapply stpd2_top.
    + SSCase "Sel2".
      assert (itpd G1 TX) as E. eauto. destruct E as [? E].
      eapply itp_exp in E; eauto.
      eapply stpd2_sel2; eauto. eauto. eapply stpd_trans_lo; eauto.
  - SCase "Bool < Bool". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eauto.
    + SSCase "Bool". eapply stpd2_bool; eauto.
    + SSCase "Sel2". eapply stpd2_sel2. eauto. eauto. eexists. eapply H6. 
  - SCase "Fun < Fun". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eapply stpd2_top.
    + SSCase "Fun". inversion H10. subst.
      eapply stpd2_fun.
      * eapply stp0f2_trans; eauto.
      * assert (trans_on n3) as IH.
        { eapply trans_le; eauto. omega. }
        eapply IH; eauto.
    + SSCase "Sel2".
      assert (itpd G1 TX) as E. eauto. destruct E as [? E].
      eapply itp_exp in E; eauto.
      eapply stpd2_sel2. eauto. eauto. eapply stpd_trans_lo; eauto.
  - SCase "Mem < Mem". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eapply stpd2_top.
    + SSCase "Mem". inversion H12. subst.
      eapply stpd2_mem.
      * eapply stp0f2_trans; eauto.
      * eauto. 
      * assert (trans_on n4) as IH.
        { eapply trans_le; eauto. omega. }
        eapply IH; eauto.
    + SSCase "Sel2". 
      assert (itpd G1 TX) as E. eauto. destruct E as [? E].
      eapply itp_exp in E; eauto.
      eapply stpd2_sel2. eauto. eauto. eapply stpd_trans_lo; eauto.
  - SCase "? < Sel". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eapply stpd2_top.
    + SSCase "Sel2". 
      assert (itpd G1 TX) as E. eauto. destruct E as [? E].
      eapply itp_exp in E; eauto.
      eapply stpd2_sel2. eauto. eauto. eapply stpd_trans_lo; eauto.
    + SSCase "Sel1". (* interesting case *)
      index_subst.
      assert (itpd G1 TX) as E. eauto. destruct E as [? E].
      eapply itp_exp in E; eauto.
      inversion H12. subst. index_subst. eauto. eapply stpd_trans_cross; eauto. 
      assert (trans_up n0) as IH. 
      { unfold trans_up. intros. apply IHn. omega. }
      apply IH.
    + SSCase "Selx". inversion H9. index_subst. subst. index_subst. subst.
      eapply stpd2_sel2. eauto. eauto. eauto.
  - SCase "Sel < ?".
      assert (trans_up n0) as IH.
      { unfold trans_up. intros. eapply IHn. omega. }
      assert (itpd G1 TX) as E. eauto. destruct E as [? E].
      eapply itp_exp in E; eauto.
      eapply stpd2_sel1. eauto. eauto. eapply stpd_trans_hi; eauto. 
  - SCase "Sel < Sel". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eapply stpd2_top.
    + SSCase "Sel2". 
      assert (itpd G1 TX) as E. eauto. destruct E as [? E].
      eapply itp_exp in E; eauto.
      (* eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto. *)
    + SSCase "Sel1". inversion H9. index_subst. subst. index_subst. subst.
      eapply stpd2_sel1. eauto. eauto. eauto.
    + SSCase "Selx". inversion H6. subst. repeat index_subst.
      eapply stpd2_selx; eauto.
  - SCase "Bind < Bind". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eapply stpd2_top.
    + SSCase "Sel2". 
      assert (itpd G1 TX) as E. eauto. destruct E as [? E].
      eapply itp_exp in E; eauto.
      eapply stpd2_sel2. eauto. eauto. eapply stpd_trans_lo; eauto.
    + SSCase "Bind".
      inversion H12. subst.
      assert (stpd false ((length G1, open (length G1) TA1) :: G1)
                   (open (length G1) TA2) (open (length G1) TA3)) as NRW.
      { 
        assert (beq_nat (length G1) (length G1) = true) as E.
        { eapply beq_nat_true_iff. eauto. }
        inversion H12. subst.
        eapply stp_narrow. eauto. eauto.
        instantiate (2 := length G1). unfold index. rewrite E. eauto.
        instantiate (1 := open (length G1) TA1). unfold update. rewrite E. eauto.
        eauto.
      }
      eapply stpd2_bindx. eapply stp0f_trans. eapply H. eapply NRW. eauto.
      eauto. eauto.
  - SCase "Trans". subst.
    assert (trans_on n3) as IH2.
    { eapply trans_le; eauto. omega. }
    assert (trans_on n0) as IH1.
    { eapply trans_le; eauto. omega. }
    assert (stpd2 true G1 T4 T3) as S123.
    { eapply IH2; eauto. }
    destruct S123.
    eapply IH1; eauto.
  - SCase "Wrap". subst.
    assert (trans_on n0) as IH.
    { eapply trans_le; eauto. omega. }
    eapply IH; eauto.
Qed.


(* convert stp false to stp2 false, and then to stp2 true *)

Lemma stp2_untrans: forall n, forall G1 T1 T2 n0,
  stp2 false G1 T1 T2 n0 ->
  n0 <= n ->
  stpd2 true G1 T1 T2.
Proof.
  intros n. induction n.
  - Case "z".
    intros. inversion H; inversion H0; subst; eauto; try solve by inversion.
  - Case "s n".
    intros. inversion H; subst.
    + SCase "transf". eapply stp2_trans.
      instantiate (2 := n1).
      instantiate (1 := n1).
      eauto. eapply H1. eapply IHn. eauto. omega. 
    + SCase "wrapf". eauto.
Qed.

Lemma stp_convert: forall n, forall m G1 T1 T2 n0,
  stp m G1 T1 T2 n0 ->
  n0 <= n ->
  env_itp G1 ->
  stpd2 m G1 T1 T2.
Proof.
  intros n.
  induction n.
  - Case "z".
    intros. inversion H; inversion H0; subst; eauto; try solve by inversion.
  - Case "s n".
    intros.
    inversion H.
    + SCase "bot". eauto.
    + SCase "top". eauto.
    + SCase "bool". eauto.
    + SCase "fun". eapply stpd2_fun. eapply IHn; eauto. omega. eapply IHn; eauto. omega.
    + SCase "mem". eapply stpd2_mem. eapply IHn; eauto. omega. eapply IHn; eauto. omega. eapply IHn; eauto. omega.
    + SCase "sel2".
      assert (stpd2 false G1 TX (TMem T1 TTop)) as ST. { eapply IHn; eauto. omega. }
      assert (stpd2 true G1 TX (TMem T1 TTop)). { destruct ST. eapply stp2_untrans; eauto. } 
      assert (itpd2 G1 TX). { eapply H1; eauto. } (* from env_itp *)
      eapply stpd2_sel2; eauto.
    + SCase "sel1".
      assert (stpd2 false G1 TX (TMem TBot T2)) as ST. { eapply IHn; eauto. omega. }
      assert (stpd2 true G1 TX (TMem TBot T2)). { destruct ST. eapply stp2_untrans; eauto. } (* un-trans *)
      assert (itpd2 G1 TX). { eapply H1; eauto. } (* from env_itp *)
      eapply stpd2_sel1; eauto.
    + SCase "selx".
      eapply stpd2_selx; eauto.
    + SCase "bindx".
      eapply stpd2_bindx; eauto.
    + SCase "transf".
      eapply stpd2_transf. eapply IHn; eauto. omega. eapply IHn; eauto. omega.
    + SCase "wrapf".
      eapply stpd2_wrapf. eapply IHn; eauto. omega.
Grab Existential Variables. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

End DOT.

