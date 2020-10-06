Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

(* Shallow embedding using built-in sigma *)

Module one.
  Set Printing Universes.

  (* T ∈ Types ::= ℕ
   *             | ⊤
   *             | ⊥
   *             | x.Type
   *             | {Type = T..T}
   *             | ∀x:T.T^ˣ
   *)

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

  Polymorphic Definition TAll (A : Type) (B: A -> Type): Type := forall x:A, (B x).

  Polymorphic Definition TAny : Type := TMem TBot TTop.

  (* t ∈ Terms ::= n
   *             | x
   *             | {Type = T}
   *             | λx:T.t
   *             | t t
   *)

  Polymorphic Definition tzro: TNat :=
    0.

  Polymorphic Definition ttyp T: TMem T T :=
    existT (fun a => prod (T -> a) (a -> T)) T (pair (fun (a:T) => a) (fun (a:T) => a)).

  Polymorphic Definition tabs {A: Type} {B: A -> Type} (f: forall x:A, B x): TAll A B :=
    f.

  Polymorphic Definition tapp {A: Type} {B: A -> Type} (f: TAll A B) (x: A): (B x) :=
    f x.

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

  (* Test subtyping *)

  Lemma TSubAny: forall T, T <: TMem TBot TTop.
  Proof.
    unfold subtype. intros.
    unfold TMem. exists TTop. split.
    - intros. inversion X0.
    - intros. apply X0.
  Qed.

  Lemma AnySubAny: TMem TBot TTop <: TMem TBot TTop.
  Proof. apply TSubAny. Qed.

  (* {Type = {Type = ⊥..⊤}} *)
  Check ttyp (TMem TBot TTop).

  (* Bad bounds *)

  Definition bad T := T -> False.

  Lemma badBound: bad (TMem TTop TBot).
  Proof.
    unfold bad. intros. unfold TMem in X.
    inversion X. destruct X0. apply t. apply x0. constructor.
  Qed.

  Lemma nonsenseSubtype: (TMem TTop TBot) <: (TMem TBot TTop).
  Proof.
    unfold subtype. intros. apply badBound in X. inversion X.
  Qed.

  Lemma badBoundExists: forall (T: TAny) (v: TSel T), exists (S: TAny), bad (TMem (TSel T) (TSel S)).
  Proof.
    intros. unfold TAny in *. unfold TSel in *. unfold TMem in *.
    exists (existT (fun a => prod (TBot -> a) (a -> TTop)) TBot (pair (fun (a:TBot) => a) (fun (a:TBot) => I))).
    unfold bad. intros. simpl in X. destruct X. destruct p.
    destruct T. simpl in x0. destruct p. simpl in v.
    apply t. apply x0. apply v.
  Qed.
  
  (* Verify impredicativity via universe polymorphism *)

  Definition nest T: TMem (TMem T T) (TMem T T) :=
    ttyp (TMem T T). 

  Definition unnest T: TSel (nest T) :=
    ttyp T.

  (* Test polymorphic identity *)

  Polymorphic Definition polyId (t: TMem TBot TTop) (x: TSel t): (TSel t) := x.

  Polymorphic Definition polyIdType: Type := forall (t : TAny), (TSel t) -> (TSel t).

  (* id(7) = 7 *)
  Definition polyNat : TNat := polyId (widenBoundsFull TNat (ttyp TNat)) 7.

  Example polyNatEq: polyNat = 7.
  Proof. cbv. reflexivity. Qed.

  (* id(id) = id *)
  Definition polyPoly : polyIdType := polyId (widenBoundsFull polyIdType (ttyp polyIdType)) polyId.

  Example polyPolyEq: polyPoly = polyId.
  Proof. cbv. reflexivity. Qed.

  (* id({Type = Nat}) = {Type = Nat} *)
  Definition polyNatType : (TMem TNat TNat) := polyId (widenBoundsFull _ (nest TNat)) (ttyp TNat).

  Example polyNatTypeEq: polyNatType = (ttyp TNat).
  Proof. cbv. reflexivity. Qed.

  (* id({Type = ∀ (t: {Type:⊥..⊤}) → ∀ t.Type → t.Type}) =
       {Type = ∀ (t: {Type:⊥..⊤}) → ∀ t.Type → t.Type} *)
  Definition polyPolyType : (TMem polyIdType polyIdType) :=
    polyId (widenBoundsFull _ (nest polyIdType)) (ttyp polyIdType).

  Example polyPolyTypeEq: polyPolyType = (ttyp polyIdType).
  Proof. cbv. reflexivity. Qed.

  (* id({Type = {Type=⊥..⊤}}) = {Type = {Type=⊥..⊤}} *)
  Definition polyAnyType: (TMem TAny TAny) := polyId (widenBoundsFull _ (nest TAny)) (ttyp TAny).

  Lemma polyAnyTypeEq: polyId (widenBoundsFull _ (nest TAny)) (ttyp TAny) = (ttyp TAny).
  Proof. cbv. reflexivity. Qed.

  (* Church encoding of Booleans *)

  Polymorphic Definition TBool: Type := forall (a: TAny), (TSel a) -> (TSel a) -> (TSel a).

  Polymorphic Definition DTrue: TBool :=
    tabs (fun (a: TAny) =>
            tabs (fun (x: TSel a) =>
                    tabs (fun (y: TSel a) =>
                            x))).

  Polymorphic Definition DFalse: TBool :=
    tabs (fun (a: TAny) =>
            tabs (fun (x: TSel a) =>
                    tabs (fun (y: TSel a) =>
                            y))).

  Polymorphic Definition ite (a: TAny) (cnd: TBool) (thn: TSel a) (els: TSel a): TSel a :=
    cnd a thn els.
    (* (tapp (tapp (tapp cnd a) thn) els). *)

  Example ite_true: ite (widenBoundsFull _ (ttyp TNat)) DTrue 1 2 = 1.
  Proof. cbv. reflexivity. Qed.

  Example ite_false: ite (widenBoundsFull _ (ttyp TNat)) DFalse 1 2 = 2.
  Proof. cbv. reflexivity. Qed.

  (* Church encoding of products *)

  Polymorphic Definition TProd (X: TAny) (Y: TAny) := forall (a: TAny), (TSel X -> TSel Y -> TSel a) -> (TSel a).

  Polymorphic Definition DPair (X: TAny) (Y: TAny) (x: TSel X) (y: TSel Y): TProd X Y :=
    tabs (fun (a: TAny) =>
            tabs (fun (k: TSel X -> TSel Y -> TSel a) =>
                    k x y)).

  Check DPair (widenBoundsFull _ (ttyp TNat)) (widenBoundsFull _ (ttyp TNat)) 1 2.

  Polymorphic Definition DFst {X : TAny} {Y: TAny} (p: TProd X Y): TSel X :=
    tapp p X (tabs (fun (x: TSel X) => tabs (fun (y: TSel Y) => x))).

  Polymorphic Definition DSnd {X : TAny} {Y: TAny} (p: TProd X Y): TSel Y :=
    tapp p Y (tabs (fun (x: TSel X) => tabs (fun (y: TSel Y) => y))).

  Example pair123: DSnd (DSnd (DPair (widenBoundsFull _ (ttyp TNat))
                                     (widenBoundsFull _ (ttyp (TProd (widenBoundsFull _ (ttyp TNat)) (widenBoundsFull _ (ttyp TNat)))))
                                     1
                                     (DPair (widenBoundsFull _ (ttyp TNat)) (widenBoundsFull _ (ttyp TNat)) 2 3))) = 3.
  Proof. cbv. reflexivity. Qed.

  (* Church encoding of sums *)

  Polymorphic Definition TSum (X: TAny) (Y: TAny): Type :=
    forall (a: TAny), (TSel X -> TSel a) -> (TSel Y -> TSel a) -> (TSel a).

  Polymorphic Definition DInL {X: TAny} {Y: TAny} (e: TSel X): TSum X Y :=
    tabs (fun (a: TAny) =>
            tabs (fun (f: TSel X -> TSel a) =>
                    tabs (fun (g: TSel Y -> TSel a) =>
                            tapp f e))).

  Polymorphic Definition DInR {X: TAny} {Y: TAny} (e: TSel Y): TSum X Y :=
    tabs (fun (a: TAny) =>
            tabs (fun (f: TSel X -> TSel a) =>
                    tabs (fun (g: TSel Y -> TSel a) =>
                            tapp g e))).

  Polymorphic Definition DCase {X: TAny} {Y: TAny} (Z: TAny) (e: TSum X Y)
              (f: TSel X -> TSel Z) (g: TSel Y -> TSel Z): TSel Z :=
    e Z f g.

  (* Church encoding of lists *)

  Polymorphic Definition TList (X: TAny): Type :=
    forall (a: TAny), TSel a -> (TSel X -> TSel a -> TSel a) -> TSel a.

  Polymorphic Definition DNil {X: TAny}: TList X :=
    tabs (fun (a: TAny) =>
            tabs (fun (n: TSel a) =>
                    tabs (fun (f: TSel X -> TSel a -> TSel a) =>
                            n))).

  Polymorphic Definition DCons {X: TAny} (hd: TSel X) (tl: TList X): TList X :=
    tabs (fun (a: TAny) =>
            tabs (fun (n: TSel a) =>
                    tabs (fun (f: TSel X -> TSel a -> TSel a) =>
                            f hd (tl a n f)))).

  Polymorphic Definition DFold {X: TAny} {Z: TAny} (e: TList X)
              (zero: TSel Z) (f: TSel X -> TSel Z -> TSel Z): TSel Z :=
    e Z zero f.

  Definition list123: TList (widenBoundsFull TNat (ttyp TNat)) := DCons (X := widenBoundsFull _ (ttyp TNat)) 1 (DCons (X := widenBoundsFull _ (ttyp TNat)) 2 (DCons (X := widenBoundsFull _ (ttyp TNat)) 3 DNil)).

  Example fold_list123 :
    DFold (Z := widenBoundsFull _ (ttyp TNat)) list123 0 (tabs (fun x => tabs (fun z => x + z))) = 6.
  Proof. cbv. reflexivity. Qed.
  
End one.
