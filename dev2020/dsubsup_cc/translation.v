(* Elaboration from D<:> with full terms as paths into a simpler CC-style
   dependently typed system without type bounds.

   The current version does not have an explicit subtyping judgement but
   includes intro and elim forms for e.T types as part of the type
   assignment for terms (has_type).
*)


(*
  Source language (currently missing: T ::=  T1 /\ T2 | { z => T^z }):

  DSubSup (D<:>)
  T ::= Top | Bot | t.Type | { Type: S..U } | (z: T) -> T^z
  t ::= x | { Type = T } | lambda x:T.t | t t

  Target language (inspired by https://docs.racket-lang.org/pie/index.html):

  t ::= x | Unit | Type
      | (z: T) -> T^z  | lambda x:T.t | t t
      | Sigma z:T. T^z | (t, t)  | fst t | snd t

  Translation (with syntactic sugar ->/* for non-dependent fun/pair):

  [[ t.Type ]]         = fst [[ t ]]
  [[ { Type: S..U } ]] = Sigma T:Type. ([[ S ]] -> T) * (T -> [[ U ]])

  [[ { Type = T } ]]   = (T, ((lambda x:T. x), (lambda x:T. x)))

*)

(*
  Roadmap:

  Frontend:
    - finish proof of type-preserving translation (esp. binding/subst for dep elim)
    - add intersection and recursive types to source (term-based elim/intro)
    - add subtyping relation
    - introduce rec capabilities and translate to term/nonterm based on context

  Backend (mainly follow Zombie paper POPL14):
    - prove termination of target
    - distinguish terminating/non-terminating fragment

*)


Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import languages.
(* make ⋆ and ◻ available *)
Import CC.Notations.
Open Scope cc_scope.

Import D. (* Dsubsup language *)

Fixpoint ttp G T (ty: is_type G T): CC.tm :=
  match ty with
  | t_top _ => CC.TTop
  | t_bot _ => CC.TBot
  | t_all _ _ _ T1 T2 => CC.TAll (ttp _ _ T1) (ttp _ _ T2)
  | t_mem _ _ _ T1 T2 =>
    let f1 := CC.TAll (ttp _ _ T1) (CC.tvar (varB 1)) in
    let f2 := CC.TAll (CC.tvar (varB 2)) (ttp _ _ T2) in
    CC.TSig ⋆ (CC.TSig f1 f2) (* XXX check *)
  | t_sel _ _ _ _ _ _ e => CC.tfst (ttm _ _ _ e)
  end
with ttm G e T (tm: has_type G e T): CC.tm :=
  match tm with
  | t_var v _ _ _ _ => CC.tvar (varF v)
  | t_typ _ _ T1 =>
    let T1' := (ttp _ _ T1) in
    let idfun := (CC.tabs T1' (CC.tvar (varF (length G)))) in
    CC.tsig T1' (CC.tsig idfun idfun)
  | t_sel2 _ _ _ _ T1 TM  => CC.tapp (CC.tfst (CC.tsnd (ttm _ _ _ TM))) (ttm _ _ _ T1)
  | t_sel1 _ _ _ _ T1 TM  => CC.tapp (CC.tsnd (CC.tsnd (ttm _ _ _ TM))) (ttm _ _ _ T1)
  | t_app _ _ _ _ _ T1 T2 _ => CC.tapp (ttm _ _ _ T1) (ttm _ _ _ T2)
  | t_abs _ _ _ _ T1 T2 => CC.tapp (ttp _ _ T1) (ttm _ _ _ T2)
  end.


(* TODO: dependent app isn't correctly defined right now, so we need this crutch *)
Lemma shotgun1: forall env T1 T2,
    is_type (T1 :: env) (open (varF (length env)) T2) ->
    is_type env T2.
Admitted.

Lemma shotgun2: forall env e T1 T2,
    CC.has_type env e T2 ->
    CC.has_type ((T1, CC.Star) :: env) (CC.open_rec 0 (varF (length env)) e) T2.
Admitted.


Lemma extract1: forall G T1 T2, is_type G (TMem T1 T2) -> is_type G T2.
Proof.
  intros. inversion H. eauto.
Qed.
Lemma extract2: forall G T1 T2, is_type G (TAll T1 T2) -> is_type (T1::G) (open (varF (length G)) T2).
Proof.
  intros. inversion H. eauto.
Qed.

(* if term has a type, the type is well-formed *)
Fixpoint htwf G e T (tm: has_type G e T): is_type G T :=
  match tm with
  | t_var _ _ _ _ i => i
  | t_sel2 _ _ _ _ h1 h2 => t_sel _ _ _ _ (htwf _ _ _ h1) (t_top _) h2
  | t_sel1 _ _ _ _ h1 h2 => extract1 _ _ _ (htwf _ _ _ h2)
  | t_typ _ _ i => t_mem _ _ _ i i
  | t_app _ _ _ _ _ h1 _ _ => shotgun1 _ _ _ (extract2 _ _ _ ((htwf _ _ _ h1)))
  | t_abs _ _ _ _ i h => t_all _ _ _ i (htwf _ _ _ h)
  end.



Lemma indexr_lookup_max: forall T (G1:list T) a,
    indexr (length G1) (a :: G1) = Some a.
Proof.
Admitted.

(* todo: is_type has a canonical form *)
Lemma foobar: forall G T1 T2 i1 i2 e h, htwf G e (TMem T1 T2) h = t_mem G _ _ i1 i2.
Proof.
Admitted.


(* Theorem: translation is well-typed *)
(* todo: need an env predicate to relate G and G1 *)
Theorem ttpok:
  forall G T (IT: is_type G T), forall G1, CC.has_type G1 (ttp _ _ IT) CC.Star.
Proof.
  apply (is_type_ind_mut (* TODO this is not defined yet *)
           (fun G T IT => forall G1, CC.has_type G1 (ttp _ _ IT) CC.Star)
           (fun G e T HT => forall G1, CC.has_type G1 (ttm _ _ _ HT) (ttp _ _ (htwf _ _ _ HT)))).

  - (* TTop *) econstructor.

  - (* TBot *) econstructor.

  - (* TMem T1 T2  ->  \Sigma TX: Type. (T1' -> TX) * (TX -> T2') *)
    intros. simpl. eapply CC.t_sigt. econstructor.
    unfold CC.open. simpl. eapply CC.t_sigt. econstructor. eapply shotgun2. eauto.
    eapply shotgun2. eapply CC.t_var. eapply indexr_lookup_max. econstructor.
    unfold CC.open. simpl. eapply CC.t_all.
    admit. admit. (* boring but tedious, need to get all open/subst right *)

  - (* TAll *) intros. simpl. econstructor. eauto. unfold CC.open. simpl. admit. (* open mismatch *)

  - (* TSel e  ->  fst e' *)
    (* we know e: *)
    (* e: TMem T1 T2  ->  e': \Sigma ... *)
    intros. simpl.

    rewrite (foobar _ _ _ i i0) in H1. simpl in H1.
    eapply CC.t_fst. eapply H1.

  - (* t_var *) intros. econstructor.
    admit. (* indexr *)
    eapply H.

  - (* t_sel2 *)
    (* apply first conversion function *)
    intros. simpl.

    rewrite (foobar _ _ _ (htwf _ _ _ h) (t_top _)) in H0. simpl in H0.

    eapply CC.t_app. eapply CC.t_fst. eapply CC.t_snd. eapply H0. eapply H.

  - (* t_sel1 *)
    (* apply second conversion function *)
    intros. simpl.

    assert (is_type env T1) as i0. admit. (* from htwf *)

    rewrite (foobar _ _ _ (t_bot _) i0) in H0. simpl in H0.

    eapply CC.t_app. eapply CC.t_snd. eapply CC.t_snd. eapply H0.

    (* FIXME: function arg -- need correct type: fst of triple *)
    admit.

  - (* t_typ *)
    admit.

  - (* t_app *)
    admit.

  - (* t_abs *)
    admit.

Admitted.
