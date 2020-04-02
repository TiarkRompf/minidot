Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import languages.
Import CC.Notations.
Open Scope cc_scope.

Import CC.

Lemma open_identity: forall b b' f u t,
    closed b f t ->
    b' >= b ->
    (open_rec b' u t) = t.
Proof.
Admitted.

Lemma subst_identity: forall b f f' u t,
    closed b f t ->
    f' >= f ->
    (subst f u t) = t.
Proof.
Admitted.

(* TODO: prove that (T^e) = (T^x){e/x} *)
Lemma open_subst: forall b b' f u t,
    closed b f t ->
    (open_rec b' u t) = (subst f u (open_rec b' (tvar (varF f)) t)).
Proof.
Admitted.

(* TODO prove strong normalization *)
Theorem full_total_safety : strong_normalization.
Proof.
  unfold strong_normalization.
Admitted.
