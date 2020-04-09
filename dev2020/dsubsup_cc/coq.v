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

Polymorphic Definition TAnd (A: Type) (B: Type): Type := A * B.

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

Require Import languages.

(* By construction, this asserts type-preservation *)
Polymorphic Fixpoint tctx Gamma (wf: D.ctx_wf Gamma): list Type  :=
  match wf with
  | wf_empty => []
  | wf_cons Gamma T wf_Gamma_T wf_Gamma => (ttp Gamma T wf_Gamma_T) :: (tctx wf_Gamma)
  end
with ttp Gamma T (wf: D.ty_wf Gamma T): Type := (* either return type or function from type list to type. *)
  match wf with
  | D.wf_top _ => TTop

  | D.wf_bot _ => TBot

  | D.wf_all _ _ _ ty_wf_T1 ty_wf_T2 =>

  | D.wf_mem _ _ _ ty_wf_T1 ty_wf_T2 =>

  | D.wf_sel _ _ _ _ _ _ has_type_e =>

  end
with ttm Gamma t T (typing: D.has_type Gamma t T):  :=
  match typing with
  | t_var v _ _ _ _ =>

  | t_typ _ _ ty_wf_T1 =>

  | t_seli _ _ _ _ has_type_a_T1 has_type_e_TM_T1_Top =>

  | t_sele _ _ _ _ has_type_a_TSel_e has_type_e_TM_Bot_T1 =>

  | t_app _ _ _ _ _ has_type_f_TAll_T1_T2 has_type_x_T1 =>

  | t_abs _ _ _ _ ty_wf_T1 has_type_y_T2 =>

  end.

(* TODO: how to relate evaluation in D and in Coq?

   - State as axiom that "Coq terms normalize" (does Coq coq correct paper help here?)
   - Seems reasonable to prove: If a well-typed source term never yields a result for any
     amount of fuel, then the coq translation does not normalize => contradiction of axiom

*)
