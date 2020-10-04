Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

(* Shallow embedding using built-in sigma *)

Module one.

  (* Types *)

  Polymorphic Definition TNat : Type :=
    nat.

  Polymorphic Definition TTop : Type :=
    True.

  Polymorphic Definition TBot : Type :=
    False.

  Polymorphic Definition TMem L U : Type :=
    sigT (fun a : Type => prod (L -> a) (a -> U)).

  Polymorphic Definition TSel {L U} (t: TMem L U): Type :=
    projT1 t.

  Polymorphic Definition TAny : Type := TMem TBot TTop.

  (* Terms *)

  Polymorphic Definition tzro: TNat :=
    0.

  Polymorphic Definition ttyp T: TMem T T :=
    existT (fun a => prod (T -> a) (a -> T)) T (pair (fun (a:T) => a) (fun (a:T) => a)).

  (* Intro & elim forms *)

  Lemma intro: forall L U (x: TMem L U) (y: L), (TSel x).
  Proof.
    intros. destruct x. destruct p. simpl. apply x0. apply y. 
  Qed.

  Lemma elim: forall L U (x: TMem L U) (y: TSel x), U.
  Proof.
    intros. destruct x. destruct p. simpl. apply u. apply y. 
  Qed.

  Lemma elim_for_realz: forall L U (x: TMem L U), (TSel x -> U).
  Proof.
    intros. destruct x. destruct p. simpl. eauto.
  Qed.

  (* Subtyping *)

  Polymorphic Definition subtype L U : Type := L -> U.

  Notation "L '<:' U" := (subtype L U) (at level 90).

  Polymorphic Definition widenBounds L1 L2 U1 U2 (t: TMem L1 U1) (wl: L2->L1) (wu:U1->U2): (TMem L2 U2) :=
    match t with
    | existT _ T (a,b) => existT _ T (fun x => a (wl x), fun x => wu (b x))
    end.

  Polymorphic Definition widenLower L1 L2 U (t: TMem L1 U) (wl: L2 -> L1): (TMem L2 U) :=
    match t with
    | existT _ T (a, b) => existT _ T (fun x => a (wl x), fun x => b x)
    end.

  Polymorphic Definition widenUpper L U1 U2 (t: TMem L U1) (wu: U1 -> U2): (TMem L U2) :=
    match t with
    | existT _ T (a, b) => existT _ T (fun x => a x, fun x => wu (b x))
    end.
  
  Polymorphic Definition widenBoundsFull T (t: TMem T T): (TMem TBot TTop) :=
    widenBounds T TBot T TTop t (fun x => match x with end) (fun x => I).

  Lemma subTMemTMem: forall S1 S2 U1 U2 (s1 : S2 <: S1) (s2 : U1 <: U2), (TMem S1 U1) <: (TMem S2 U2).
  Proof.
    intros. unfold subtype. intros. eapply widenBounds; eauto.
  Qed.

  Lemma subTSelRight: forall U (x : (TMem TBot U)), (TSel x) <: U.
  Proof.
    intros. unfold subtype. intros. eapply elim; eauto.
  Qed.

  Lemma subTSelLeft: forall S (x: (TMem S TTop)), S <: (TSel x).
  Proof.
    intros. unfold subtype. intros. eapply intro; eauto.
  Qed.

  Lemma subAllAll: forall S1 S2 U1 U2 (sub1 : S2 <: S1) (f: S2 -> (U1 <: U2)), (S1 -> U1) <: (S2 -> U2).
  Proof.
    intros. unfold subtype. intros.
    apply f. apply X0. apply X. apply sub1. apply X0.
  Qed.

  Lemma subTrans: forall S T U (s1: S <: T) (s2: T <: U), (S <: U).
  Proof.
    intros. unfold subtype. intros. auto.
  Qed.

  Lemma subTop: forall T, (T <: TTop).
  Proof.
    intros. unfold subtype. intros. constructor.
  Qed.

  Lemma subBot: forall T, (TBot <: T).
  Proof.
    intros. unfold subtype. intros. inversion X.
  Qed.

  Lemma subRefl: forall T, (T <: T).
  Proof.
    intros. unfold subtype. intros. auto.
  Qed.
  
  (* Verify impredicativity via universe polymorphism *)

  Definition nest T: TMem (TMem T T) (TMem T T) :=
    ttyp (TMem T T). 

  Definition unnest T: TSel (nest T) :=
    ttyp T.

  (* Test polymorphic identity *)

  Polymorphic Definition polyId (t: TMem False True) (x: TSel t): (TSel t) := x.

  Definition applyPolyId: TNat := polyId (widenBoundsFull _ (ttyp TNat)) 7.

End one.
