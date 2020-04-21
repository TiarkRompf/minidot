Set Printing Universes.

(* Types *)
Polymorphic Definition TNat: Type := nat.

Polymorphic Definition TMem L U: Type :=
  sigT (fun a:Type => prod (L -> a) (a -> U)).

Polymorphic Definition TSel {L U} (t: TMem L U): Type :=
  projT1 t.

Polymorphic Definition TTop: Type := sigT (fun a: Type => a).

Polymorphic Definition TBot: Type := forall x: Type, x.

Polymorphic Definition TAll (A : Type) (B: A -> Type): Type := forall x:A, (B x).

Polymorphic Definition TAnd (A: Type) (B: Type): Type := A * B. (* TODO: not sure *)

(* TODO: TBind, use coinduction? *)

Check (TAll (TMem TBot TTop) (fun x => TAll (TSel x) (fun _ => (TSel x)))).

(* Terms *)
Polymorphic Definition tzro: TNat :=
0.

Polymorphic Definition ttyp T: TMem T T :=
existT (fun a => prod (T -> a) (a -> T)) T (pair (fun (a:T) => a) (fun (a:T) => a)).

Polymorphic Definition tabs {A: Type} {B: A -> Type} (f: forall x:A, B x): TAll A B := f.

Polymorphic Definition tapp {A: Type} {B: A -> Type} (f: TAll A B) (x: A): (B x) := f x.

Check tabs.

(* TODO: unpack *)

(* Intro & elim forms *)
Lemma intro: forall L U (x: TMem L U) (y: L), (TSel x).
Proof.
intros. destruct x. destruct p. simpl. apply x0. apply y.
Qed.

Lemma elim: forall L U (x: TMem L U) (y: TSel x), U.
Proof.
intros. destruct x. destruct p. simpl. apply u. apply y.
Qed.


(* Verify impredicativity via universe polymorphism *)
Definition nest T: TMem (TMem T T) (TMem T T) :=
  ttyp (TMem T T).

Check nest.

Definition unnest T: TSel (nest T) :=
ttyp T.

Check unnest.

(* Subtyping could be translated as coercions *)

Polymorphic Definition sub_any {A: Type} (t: A): TTop := existT (fun a: Type => a) A t.
Polymorphic Definition sub_bot {A: Type} (t: TBot): A := t A.

Polymorphic Definition tmem_any {L U: Type} (t: TMem L U): TTop := sub_any t.
Polymorphic Definition bot_tmem {L U: Type} (t: TBot): (TMem L U) := sub_bot t.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import languages_o2.

Section D_meta.
Import D.

Lemma ty_wf_weaken: forall Gamma T U, ty_wf Gamma T -> ctx_wf (U :: Gamma) -> ty_wf (U :: Gamma) T.
Proof.
  Admitted.

Lemma wf_lookup: forall Gamma x T, ctx_wf Gamma -> indexr x Gamma = Some T -> ty_wf Gamma T.
Proof.
  intros.
  induction H; inversion H0.
  inversion H0.
  destruct (beq_nat x (length Gamma)).
  - injection H2. intros. subst.
    apply ty_wf_weaken. assumption. constructor. assumption. assumption.
  - apply IHctx_wf in H2. apply ty_wf_weaken. assumption. constructor. assumption. assumption.
Qed.

Lemma hcwf: forall {Gamma e T}, has_type Gamma e T -> ctx_wf Gamma
    with
    tcwf: forall {Gamma T}, ty_wf Gamma T -> ctx_wf Gamma.
Proof.
  - intros. induction H; eauto.
  - intros. induction H; eauto.
Qed.

Lemma extract1: forall Gamma T1 T2, ty_wf Gamma (TMem T1 T2) -> ty_wf Gamma T2.
Proof.
  intros. inversion H. eauto.
Qed.

Lemma extract2: forall Gamma T1 T2, ty_wf Gamma (TMem T1 T2) -> ty_wf Gamma T1.
Proof.
  intros. inversion H. eauto.
Qed.

Lemma ty_wf_open: forall Gamma e T1 T2,
    ty_wf (T1 :: Gamma) (open (varF (length Gamma)) T2) ->
    has_type Gamma e T1 ->
    ty_wf Gamma (open' e T2)
  with
    has_type_open: forall Gamma e1 e2 T1 T2,
      has_type (T1 :: Gamma) e2 T2 ->
      has_type Gamma e1 T1 ->
      has_type Gamma (open_tm' e1 e2) (open' e1 T2).
Proof.
  -  (* ty_wf_open *)
    intros.  unfold open in *. unfold open' in *. unfold open_tm' in *.
    generalize dependent Gamma. generalize dependent e. generalize dependent T1.
    induction T2; intros.
    (* TTop *)
    -- simpl. constructor. eapply hcwf. eauto.
    (* TBot *)
    -- simpl. constructor. eapply hcwf. eauto.
    (* TAll *)
    -- simpl in H. inversion H. subst. simpl. constructor.
       --- eapply IHT2_1; eauto.
       --- unfold open in *.
         admit. (* TODO messy *)
    (* TSel *)
    -- inversion H0; subst; eauto.
    (* TMem *)
    -- inversion H. subst. simpl. constructor.
       eapply IHT2_1. eauto. auto.
       eapply IHT2_2. eauto. auto.
    (* TBind *)
    -- inversion H.
    (* TAnd *)
    -- inversion H.

  (* has_type_open *)
  - intros. unfold open in *. unfold open' in *. unfold open_tm' in *.
    generalize dependent Gamma. generalize dependent e1. generalize dependent e2.
    generalize dependent T1.
    induction T2; intros; eauto.
Admitted. (*TODO: most of the cases are wrong, try avoiding eauto *)

Lemma htwf: forall Gamma e T, has_type Gamma e T -> ty_wf Gamma T.
Proof.
  intros. induction H; auto.
  - eapply wf_lookup; eauto.
  - apply wf_sel with (T1 := T1) (T2 := TTop); auto. constructor. eapply tcwf. eauto.
  - apply (extract1 _ _ _ IHhas_type2).
  - constructor; auto.
  - inversion IHhas_type1. subst. eapply ty_wf_open; eauto.
  - constructor; auto.
Qed.

End D_meta.

Polymorphic Inductive term: Type -> Type :=
| Duh: term nat (* TODO remove *)
| term_tmem: forall T, TMem T T -> term (TMem T T)
.

Polymorphic Definition TERM: Type := sigT (fun T: Type => term T).

Polymorphic Definition TERM_of {T} (t: term T): TERM :=
  existT term T t.

Polymorphic Fixpoint tctx {Gamma} (reify: forall U, term U -> U) (wf: D.ctx_wf Gamma): list Type  :=
  match wf with
  | D.wf_empty => []
  | D.wf_cons Gamma T wf_Gamma_T wf_Gamma => (ttp reify wf_Gamma_T) :: (tctx reify wf_Gamma)
  end
with ttp {Gamma} {T} (reify: forall U, term U -> U) (ty_wf: D.ty_wf Gamma T): Type := (* TODO make reify part of this mutually-recursive group of definitions *)
  match ty_wf with
  | D.wf_top _ _ =>
    TTop
  | D.wf_bot _ _ =>
    TBot
  | D.wf_all _ _ _ ty_wf_T1 ty_wf_T2 =>
    TBot (*TODO*)
  | D.wf_mem _ _ _ ty_wf_T1 ty_wf_T2 =>
    TBot (*TODO*)
  | D.wf_sel _ _ _ _ _ _ has_type_e =>
    match ttm has_type_e with
    | existT _ _ (term_tmem _ t) => TSel (reify t) (* TODO this will get rejected *)
    | _ => False
    end
  end
(*
  Problem: we cannot mention ttp in the return type of ttm! The idea is to
  construct a TERM = term U for some U s.t. U = ttp (htwf typing).
  reify is supposed to turn this intermediate term representation into a proper
  coq term having the type U.
 *)
with ttm {Gamma} {t} {T} (typing: D.has_type Gamma t T): TERM :=
  match typing with
  | D.t_var v _ _ _ _ =>
    TERM_of Duh
  | D.t_typ _ _ ty_wf_T1 =>
    TERM_of Duh
  | D.t_seli _ _ _ _ has_type_a_T1 has_type_e_TM_T1_Top =>
    TERM_of Duh
  | D.t_sele _ _ _ _ has_type_a_TSel_e has_type_e_TM_Bot_T1 =>
    TERM_of Duh
  | D.t_app _ _ _ _ _ has_type_f_TAll_T1_T2 has_type_x_T1 =>
    TERM_of Duh
  | D.t_abs _ _ _ _ ty_wf_T1 has_type_y_T2 =>
    TERM_of Duh
  end.

(* TODO: how to relate evaluation in D and in Coq?

   - State as axiom that "Coq terms normalize" (does Coq coq correct paper help here?)
   - Seems reasonable to prove: If a well-typed source term never yields a result for any
     amount of fuel, then the coq translation does not normalize => contradiction of axiom

*)
