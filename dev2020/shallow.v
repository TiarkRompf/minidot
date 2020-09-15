
Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.




(* Shallow embedding using built-in sigma *)

Module one.

  (* Types *)
  Polymorphic Definition TNat: Type :=
    nat.

  Polymorphic Definition TMem L U: Type :=
    sigT (fun a:Type => prod (L -> a) (a -> U)).

  Polymorphic Definition TSel {L U} (t: TMem L U): Type :=
    projT1 t.

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
  Polymorphic Definition widenBounds L1 L2 U1 U2 (t: TMem L1 U1) (wl: L2->L1) (wu:U1->U2): (TMem L2 U2) :=
    match t with
    | existT _ T (a,b) => existT _ T (fun x => a (wl x), fun x => wu (b x))
    end.
  
  Polymorphic Definition widenBoundsFull T (t: TMem T T): (TMem False True) :=
    widenBounds T False T True t (fun x => match x with end) (fun x => I).


  
  (* Verify impredicativity via universe polymorphism *)
  Definition nest T: TMem (TMem T T) (TMem T T) :=
    ttyp (TMem T T). 

  Definition unnest T: TSel (nest T) :=
    ttyp T.



  (* Test polymorphic identity *)
  Polymorphic Definition polyId (t: TMem False True) (x: TSel t): (TSel t) := x.

  Definition applyPolyId: TNat := polyId (widenBoundsFull _ (ttyp TNat)) 7.



End one.



