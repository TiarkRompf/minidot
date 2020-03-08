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

(* type-directed translation of D into CC

   TODO: we should have marker syntax in CC for translation artifacts.
   these should not consume fuel in evaluation. we could then show that
   source exps and translation require the exact same amount of fuel.
*)
Fixpoint ttp Gamma T (wf: ty_wf Gamma T): CC.tm :=
  match wf with
  | wf_top _ =>
    CC.TTop
  | wf_bot _ =>
    CC.TBot
  | wf_all _ _ _ ty_wf_T1 ty_wf_T2 =>
    CC.TAll (ttp _ _ ty_wf_T1) (ttp _ _ ty_wf_T2)
  | wf_mem _ _ _ ty_wf_T1 ty_wf_T2 =>   (* Type L..U ~>  (Σα:⋆.(L → α × α → U)) : ◻ *)
    let f1 := CC.TAll (ttp _ _ ty_wf_T1) (CC.tvar (varB 1)) in
    let f2 := CC.TAll (CC.tvar (varB 2)) (ttp _ _ ty_wf_T2) in
    CC.TSig ⋆ (CC.TSig f1 f2)
  | wf_sel _ _ _ _ _ _ has_type_e =>
    CC.tfst (ttm _ _ _ has_type_e)
  end
with ttm Gamma t T (typing: has_type Gamma t T): CC.tm :=
  match typing with
  | t_var v _ _ _ _ =>
    CC.tvar (varF v)
  | t_typ _ _ ty_wf_T1 =>
    let T1' := (ttp _ _ ty_wf_T1) in
    (* let idfun := (CC.tabs T1' (CC.tvar (varF (length Gamma)))) in *)
    let idfun := (CC.tabs T1' (CC.tvar (varB 0))) in (* TODO: confirm w. Tiark *)
    (* TODO: it seems we need type annotations in tsig, since the result may
       also be typed as Σα:⋆.(α→α×α→α), while we would like the type
       Σα:⋆.(T1'→α×α→T1'). *)
    CC.tsig T1' (CC.tsig idfun idfun)
  | t_seli _ _ _ _ has_type_a_T1 has_type_e_TM_T1_Top =>
    let a' := (ttm _ _ _ has_type_a_T1) in
    let e' := (ttm _ _ _ has_type_e_TM_T1_Top) in
    CC.tapp (CC.tfst (CC.tsnd e')) a'
  | t_sele _ _ _ _ has_type_a_TSel_e has_type_e_TM_Bot_T1 =>
    let a' := (ttm _ _ _ has_type_a_TSel_e) in
    let e' := (ttm _ _ _ has_type_e_TM_Bot_T1) in
    CC.tapp (CC.tsnd (CC.tsnd e')) a'
  | t_app _ _ _ _ _ has_type_f_TAll_T1_T2 has_type_x_T1 =>
    (* TODO this'll need a lemma stating that subst/open and translation commute  *)
    CC.tapp (ttm _ _ _ has_type_f_TAll_T1_T2) (ttm _ _ _ has_type_x_T1)
  | t_abs _ _ _ _ ty_wf_T1 has_type_y_T2 =>
    CC.tabs (ttp _ _ ty_wf_T1) (ttm _ _ _ has_type_y_T2)
  end.

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
    -- simpl. constructor.
    (* TBot *)
    -- simpl. constructor.
    (* TAll *)
    -- simpl in H. inversion H. subst. simpl. constructor.
       --- eapply IHT2_1; eauto.
       --- unfold open in *.
         admit. (* TODO messy *)
    (* TSel *)
    -- eapply ty_wf_open. (* TODO this can't be right *)
       eauto.
       auto.
    (* TMem *)
    -- inversion H. subst. simpl. constructor.
       eapply IHT2_1. eauto. auto.
       eapply IHT2_2. eauto. auto.
    (* TBind *)
    -- inversion H.
    (* TAnd *)
    -- inversion H.
  (* has_type_open *)
  - apply has_type_open. (* TODO this can't be right *)
Admitted.

(* if term has a type, the type is well-formed *)
Lemma htwf: forall Gamma e T, has_type Gamma e T -> ty_wf Gamma T.
Proof.
  intros. induction H; auto.
  - apply wf_sel with (T1 := T1) (T2 := TTop); auto. constructor.
  - apply (extract1 _ _ _ IHhas_type2).
  - constructor; auto.
  - inversion IHhas_type1. subst. eapply ty_wf_open; eauto.
  - constructor; auto.
Qed.

(* Fixpoint htwf G e T (tm: has_type G e T): ty_wf G T := *)
(*   match tm with *)
(*   | t_var _ _ _ _ ty_wf_T1 => *)
(*     ty_wf_T1 *)
(*   | t_seli _ _ _ _ has_type_a_T1 has_type_e_TM_T1_Top => *)
(*     wf_sel _ _ _ _ (htwf _ _ _ has_type_a_T1) (wf_top _) has_type_e_TM_T1_Top *)
(*   | t_sele _ _ _ _ _ has_type_e_TM_Bot_T1 => *)
(*     extract1 _ _ _ (htwf _ _ _ has_type_e_TM_Bot_T1) *)
(*   | t_typ _ _ ty_wf_T1 => *)
(*     wf_mem _ _ _ ty_wf_T1 ty_wf_T1 *)
(*   | t_app Gamma f x T1 T2 has_type_f_TAll_T1_T2 has_type_x_T1 => *)
(*     match (htwf Gamma f (TAll T1 T2) has_type_f_TAll_T1_T2) as p in (ty_wf _ (TAll _ _)) return (ty_wf Gamma (open' x T2)) with *)
(*     | wf_all _ _ _ _ ty_wf_T2x => *)
(*       (ty_wf_open _ _ _ _ ty_wf_T2x has_type_x_T1) *)
(*     end *)
(*   | t_abs _ _ _ _ i h => *)
(*     wf_all _ _ _ i (htwf _ _ _ h) *)
(*   end. *)

Lemma indexr_lookup_max: forall T (G1:list T) a,
    indexr (length G1) (a :: G1) = Some a.
Proof.
Admitted.

(* todo: ty_wf has a canonical form *)
(* Lemma foobar: forall G T1 T2 i1 i2 e h, htwf G e (TMem T1 T2) h = t_mem G _ _ i1 i2. *)
(* Proof. *)
(* Admitted. *)


(* Theorem: translation is well-typed *)
(* todo: need an env predicate to relate G and G1 *)
Theorem ttpok:
  forall Gamma T (IT: ty_wf Gamma T), forall Gamma1, CC.has_type Gamma1 (ttp _ _ IT) ⋆
  with
    ttmok:
      forall Gamma t T (typing: has_type Gamma t T), forall Gamma1, CC.has_type Gamma1 (ttm _ _ _ typing) (ttp _ _ (htwf _ _ _ typing)).
Proof.
  apply (ty_wf_ind_mut (* TODO this is not defined yet *)
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

    assert (ty_wf env T1) as i0. admit. (* from htwf *)

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
