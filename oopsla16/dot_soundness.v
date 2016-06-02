Require Import dot.

(*
precise subtyping:
- no built-in transitivity axiom
- delegate to usual stp in most cases, except for leverage in pushback
- we actually only need to define precise subtyping on empty abstract context
  so no need for rules on abstract variables
*)
Inductive stpp: venv -> ty -> ty -> Prop :=
| stpp_bot: forall G1 T,
    closed 0 (length G1) 0  T ->
    stpp G1 TBot T
| stpp_top: forall G1 T,
    closed 0 (length G1) 0 T ->
    stpp G1 T  TTop
| stpp_fun: forall G1 l T1 T2 T3 T4 T2' T4',
    T2' = (open 0 (TVar false 0) T2) ->
    T4' = (open 0 (TVar false 0) T4) ->
    closed 0 (length G1) 1 T2 ->
    closed 0 (length G1) 1 T4 ->
    stpd [] G1 T3 T1 ->
    stpd [T3] G1 T2' T4' ->
    stpp G1 (TFun l T1 T2) (TFun l T3 T4)
| stpp_mem: forall G1 l T1 T2 T3 T4,
    stpd [] G1 T3 T1 ->
    stpd [] G1 T2 T4 ->
    stpp G1 (TMem l T1 T2) (TMem l T3 T4)

| stpp_varx: forall G1 x,
    x < length G1 ->
    stpp G1 (TVar true x) (TVar true x)

| stpp_strong_sel1: forall G1 l T2 ds TX x,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stpp G1 TX T2 -> (* not stp! for leverage in pushback *)
    stpp G1 (TSel (TVar true x) l) T2
| stpp_strong_sel2: forall G1 l T1 ds TX x,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stpd [] G1 T1 TX ->
    stpp G1 T1 (TSel (TVar true x) l)

| stpp_selx: forall G1 l T1,
    closed 0 (length G1) 0 T1 ->
    stpp G1 (TSel T1 l) (TSel T1 l)

| stpp_bind1: forall G1 T1 T1' T2,
    stpd [T1'] G1 T1' T2 ->
    T1' = (open 0 (TVar false 0) T1) ->
    closed 0 (length G1) 1 T1 ->
    closed 0 (length G1) 0 T2 ->
    stpp G1 (TBind T1) T2

| stpp_bindx: forall G1 T1 T1' T2 T2',
    stpd [T1'] G1 T1' T2' ->
    T1' = (open 0 (TVar false 0) T1) ->
    T2' = (open 0 (TVar false 0) T2) ->
    closed 0 (length G1) 1 T1 ->
    closed 0 (length G1) 1 T2 ->
    stpp G1 (TBind T1) (TBind T2)

| stpp_and11: forall G1 T1 T2 T,
    stpp G1 T1 T -> (* not stp! for leverage in pushback *)
    closed 0 (length G1) 0 T2 ->
    stpp G1 (TAnd T1 T2) T
| stpp_and12: forall G1 T1 T2 T,
    stpp G1 T2 T -> (* not stp! for leverage in pushback *)
    closed 0 (length G1) 0 T1 ->
    stpp G1 (TAnd T1 T2) T
| stpp_and2: forall G1 T1 T2 T,
    stpd [] G1 T T1 ->
    stpd [] G1 T T2 ->
    stpp G1 T (TAnd T1 T2)

| stpp_or21: forall G1 T1 T2 T,
    stpd [] G1 T T1 ->
    closed 0 (length G1) 0 T2 ->
    stpp G1 T (TOr T1 T2)
| stpp_or22: forall G1 T1 T2 T,
    stpd [] G1 T T2 ->
    closed 0 (length G1) 0 T1 ->
    stpp G1 T (TOr T1 T2)
| stpp_or1: forall G1 T1 T2 T,
    stpp G1 T1 T -> (* not stp! for leverage in pushback *)
    stpp G1 T2 T -> (* not stp! for leverage in pushback *)
    stpp G1 (TOr T1 T2) T
.

Lemma stpp_to_stp: forall G T1 T2,
  stpp G T1 T2 ->
  stpd [] G T1 T2.
Proof.
  intros. induction H; repeat eu; eexists; eauto 2.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0.
Qed.

Hint Constructors stpp.

Lemma stpp_closed: forall G T1 T2,
  stpp G T1 T2 ->
  closed 0 (length G) 0 T1 /\ closed 0 (length G) 0 T2.
Proof.
  intros. eapply stpp_to_stp in H. eu. split.
  - eapply stp_closed1 in H. simpl in H. apply H.
  - eapply stp_closed2 in H. simpl in H. apply H.
Qed.

Lemma stpp_refl: forall G1 T1,
  closed 0 (length G1) 0 T1 ->
  stpp G1 T1 T1.
Proof.
  intros. inversion H; subst;
  try solve [eauto 2];
  try solve [inversion H; subst; omega];
  try (eapply (stpd_refl []) in H0; edestruct H0);
  try (eapply (stpd_refl []) in H1; edestruct H1).
  - Case "fun".
    assert (stpd [T0] G1 (open 0 (TVar false 0) T2) (open 0 (TVar false 0) T2)) as A. {
      eapply stpd_refl.  eapply closed_open. simpl. eapply closed_upgrade_gh. eauto.
      omega. econstructor. simpl. omega.
    }
    edestruct A.
    econstructor; eauto 2.
  - Case "mem".
    econstructor; eauto 2.
  - Case "bind".
    remember (open 0 (TVar false 0) T0) as T0'.
    assert (stpd [T0'] G1 T0' T0') as A. {
      subst. eapply stpd_refl. eapply closed_open. eapply closed_upgrade_gh. eauto.
      simpl. omega. simpl. econstructor. omega.
    }
    eu. eapply stpp_bindx; eauto.
  - eapply stpp_and2.
    eexists. eapply stp_and11. eassumption. inversion H; subst; eauto.
    eexists. eapply stp_and12. eassumption. inversion H; subst; eauto.
  - eapply stpp_or1.
    eapply stpp_or21. eassumption. inversion H; subst; eauto.
    eapply stpp_or22. eassumption. inversion H; subst; eauto.
Qed.

Lemma stp_trans_pushback_aux: forall n, forall G T1 T2 T3 n12,
  stp [] G T1 T2 n12 -> n12 < n ->
  stpp G T2 T3 ->
  stpp G T1 T3.
Proof.
  intros n. induction n. intros; try omega.
  intros G T1 T2 T3 n12 H12 LE H23.
  inversion H12; intros; subst; simpl in *;
  try solve [eapply stpp_bot; eauto 2; eapply stpp_closed; eauto];
  try solve [eapply stpp_strong_sel1; eauto 2; eapply IHn; eauto; omega];
  try solve [eapply htp_closed1 in H; simpl in H; omega];
  try solve [eapply stpp_to_stp in H23; destruct H23 as [? H23];
    eapply stpp_bind1; eauto 2; [
      eexists; eapply stp_trans; eauto 2;
      eapply stp_upgrade_gh; eauto 2 |
      eapply stp_closed2 in H23; simpl in H23; eapply H23]];
  try solve [eapply stpp_and11; eauto 2; eapply IHn; eauto 2; omega];
  try solve [eapply stpp_and12; eauto 2; eapply IHn; eauto 2; omega];
  try solve [eapply stpp_or1; eapply IHn; eauto 2; omega];
  try solve [eapply IHn; [eapply H | omega | eapply IHn; [eapply H0 | omega | eauto ]]];
  inversion H23; subst; repeat eu;
  try solve [eauto 2];
  try solve [econstructor; eexists; eapply stp_trans; eauto 2];
  try solve [eapply stpp_top; eauto 2;
             try econstructor; eauto 2;
             try solve [eapply (stp_closed2 []); eassumption];
             try solve [eapply (stp_closed1 []); eassumption]];
  try solve [eapply stpp_strong_sel2; eauto 2; eexists; eauto 3];
  try solve [eapply stpp_and2; eauto 2; eexists; eapply stp_trans; eauto 2];
  try solve [eapply stpp_or21; eauto 2; eexists; eapply stp_trans; eauto 2];
  try solve [eapply stpp_or22; eauto 2; eexists; eapply stp_trans; eauto 2];
  try solve [eapply IHn with (n12:=n1); eauto 2; omega];
  try solve [eapply IHn with (n12:=n2); eauto 2; omega].
  - Case "fun-fun".
    assert (stpd [T7] G (open 0 (TVar false 0) T4) (open 0 (TVar false 0) T6)) as A. {
      change [T7] with ([T7]++[]). eapply stp_narrow_norec.
      eassumption. eassumption.
    }
    destruct A as [? A].
    eapply stpp_fun. reflexivity. reflexivity. eauto. eauto.
    eexists. eapply stp_trans; eauto.
    eexists. eapply stp_trans. eapply A. eauto.
  - Case "sel2-sel1".
    rewrite H in H4. inversion H4. subst.
    rewrite H0 in H6. inversion H6. subst.
    eapply IHn; eauto 2. omega.
  - Case "bindx-bind1".
    assert (stpd [open 0 (TVar false 0) T0] G (open 0 (TVar false 0) T4) T3) as A. {
      change ([open 0 (TVar false 0) T0]) with ([open 0 (TVar false 0) T0]++[]).
      eapply stp_narrow0; eauto.
    }
    eu. eapply stpp_bind1.
    eexists. eapply stp_trans. eapply H. eapply A. reflexivity. eauto. eauto.
  - Case "bindx-bindx".
    assert (stpd [open 0 (TVar false 0) T0] G (open 0 (TVar false 0) T4) (open 0 (TVar false 0) T2)) as A. {
      eapply stp_narrow0; eauto.
    }
    eu. eapply stpp_bindx.
    eexists. eapply stp_trans. eapply H. eapply A. reflexivity. eauto. eauto. eauto.
Qed.

Lemma stp_trans_pushback: forall G T1 T2 n,
  stp [] G T1 T2 n ->
  stpp G T1 T2.
Proof.
  intros.
  eapply stp_trans_pushback_aux; eauto.
  eapply stpp_refl.
  eapply stp_closed2 in H. simpl in H. eauto.
Qed.

(*
We need to count the number of packing when typing a concrete variable.
Like for precise subtyping, we really only need this in an emptry abstract context.
*)
Inductive htpy : nat(*pack count*) -> venv -> id(*concrete var*) -> ty -> Prop :=
  | TY_Vary : forall m G1 x ds ds' T T' n1,
      index x G1 = Some (vobj ds) ->
      dms_has_type [T'] G1 ds' T' n1 ->
      subst_dms x ds' = ds ->
      substt x T' = T ->
      closed 0 (length G1) 0 T ->
      htpy m G1 x T
  | TY_VarPack : forall m G1 x T1 T1',
      htpy m G1 x T1' ->
      T1' = (open 0 (TVar true x) T1) ->
      closed 0 (length G1) 1 T1 ->
      htpy (S m) G1 x (TBind T1)
  | TY_VarUnpack : forall m G1 x T1 T1',
      htpy m G1 x (TBind T1) ->
      T1' = (open 0 (TVar true x) T1) ->
      closed 0 (length G1) 0 T1' ->
      htpy m G1 x T1'
  | TY_Sub : forall m G1 t T1 T2 n2,
      htpy m G1 t T1 ->
      stp [] G1 T1 T2 n2 ->
      htpy m G1 t T2.

Lemma htpy_to_hastp: forall m G y T,
  htpy m G y T ->
  exists n, has_type [] G (tvar true y) T n.
Proof.
  intros. induction H;
  try destruct IHhtpy as [n IH];
  try solve [eexists; eauto 3].
Qed.

Hint Constructors htpy.

Lemma hastp_to_htpy: forall G y T n,
  has_type [] G (tvar true y) T n ->
  exists m, htpy m G y T.
Proof.
  intros.
  remember [] as GH. generalize dependent HeqGH.
  remember (tvar true y) as t. generalize dependent Heqt.
  induction H; intros; inversion Heqt; subst;
  try (specialize (IHhas_type eq_refl eq_refl); destruct IHhas_type as [m IH]);
  try solve [eexists; eauto 3].
Grab Existential Variables.
apply 0.
Qed.

Definition Subst (m: nat) := forall GH G x TX T1 T2 m1 n2, m1 <= m ->
  htpy m1 G x (substt x TX) ->
  stp (GH++[TX]) G T1 T2 n2 ->
  stpd (map (substt x) GH) G (substt x T1) (substt x T2).

Lemma pre_canon_bind_aux: forall m1, Subst m1 -> forall G y T T0,
  htpy (S m1) G y T0 -> stpd [] G T0 (TBind T) ->
  htpy m1 G y (open 0 (TVar true y) T).
Proof.
  intros m1 HS G y T T0 H Hsub.
  remember (S m1) as m. generalize dependent m1. generalize dependent T.
  induction H; intros; subst.
  - eu. eapply stp_trans_pushback in Hsub.
    assert False as Contra. {
      clear H. clear H3. clear HS. clear x0. clear m1.
      induction H0; subst; unfold substt in Hsub; simpl in Hsub.
      - inversion Hsub.
      - inversion Hsub; subst. inversion H4. eapply IHdms_has_type. eapply H4.
      - inversion Hsub; subst. inversion H6. eapply IHdms_has_type. eapply H6.
    }
    inversion Contra.
  - inversion Heqm; subst. clear Heqm.
    eu. eapply stp_trans_pushback in Hsub. inversion Hsub; subst.
    + assert (substt x T1=T1) as EqT1. {
        eapply subst_closed_id. eassumption.
      }
      assert (substt x (open 0 (TVar false 0) T1) = (open 0 (TVar true x) T1)) as A. {
        rewrite subst_open_commute0b. rewrite EqT1. reflexivity.
      }
      assert (substt x (TBind T)=(TBind T)) as EqT. {
        eapply subst_closed_id. eassumption.
      }
      eu. edestruct HS as [? IHS]. eauto. rewrite <- A in H. eapply H.
      instantiate (4:=nil). simpl. eapply H2.
      rewrite A in IHS. rewrite EqT in IHS. simpl in IHS.
      eapply TY_VarUnpack. eapply TY_Sub. eapply H. eapply IHS.
      reflexivity. eapply closed_open. simpl. inversion H6. eassumption.
      econstructor. eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed1 in H. omega.
    + assert (substt x T1=T1) as EqT1. {
        eapply subst_closed_id. eassumption.
      }
      assert (substt x (open 0 (TVar false 0) T1) = (open 0 (TVar true x) T1)) as A1. {
        rewrite subst_open_commute0b. rewrite EqT1. reflexivity.
      }
      assert (substt x T=T) as EqT. {
        eapply subst_closed_id. eassumption.
      }
      assert (substt x (open 0 (TVar false 0) T) = (open 0 (TVar true x) T)) as A. {
        rewrite subst_open_commute0b. rewrite EqT. reflexivity.
      }
      eu. edestruct HS as [? IHS]. eauto. rewrite <- A1 in H. eapply H.
      instantiate (4:=nil). simpl. eapply H3.
      rewrite A1 in IHS. rewrite A in IHS. simpl in IHS.
      eapply TY_Sub. eapply H. eapply IHS.
  - eu. eapply TY_VarUnpack. eapply TY_Sub. eapply IHhtpy.
    eapply stpd_refl.
    eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed in H. simpl in H. eapply H.
    eauto. eauto.
    eapply Hsub. reflexivity.
    eapply stp_closed2 in Hsub. simpl in Hsub. inversion Hsub; subst.
    eapply closed_open. simpl. eassumption.
    econstructor.
    eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed1 in H. omega.
  - eu. eapply IHhtpy. eexists. eapply stp_trans. eassumption. eapply Hsub.
    eauto. eauto.
Qed.

Lemma pre_canon_bind: forall m1, Subst m1 -> forall G y T,
  htpy (S m1) G y (TBind T) ->
  htpy m1 G y (open 0 (TVar true y) T).
Proof.
  intros. eapply pre_canon_bind_aux; eauto 2.
  eapply stpd_refl.
  simpl.
  eapply htpy_to_hastp in H0. destruct H0 as [? H0]. eapply has_type_closed in H0. simpl in H0. eapply H0.
Qed.

(*
Lemma pre_canon_bind_aux: forall m1, Subst m1 -> forall G y T T0,
  htpy (S m1) G y T0 -> stpd [] G T0 (TBind T) ->
  exists T1,
    htpy m1 G y (open 0 (TVar true y) T1) /\
    stpd [(open 0 (TVar true y) T1)] G (open 0 (TVar false 0) T1) (open 0 (TVar false 0) T) /\
    closed 0 (length G) 1 T1.
Proof.
  intros m1 HS G y T T0 H Hsub.
  remember (S m1) as m. generalize dependent m1. generalize dependent T.
  induction H; intros; subst.
  - admit.
  - inversion Heqm; subst.
    eu. eapply stp_trans_pushback in Hsub. inversion Hsub; subst.
    specialize (IHhtpy T1 H2 m1).
    eexists. split; try split; try eassumption.
    eapply stpd_refl. simpl. eapply closed_open. simpl.
    eapply closed_upgrade_gh. eauto. omega. econstructor. omega.
  - destruct T1; simpl in HeqT0; inversion HeqT0.
    destruct i; simpl in HeqT0; inversion HeqT0.
    specialize (IHhtpy (TBind T1) eq_refl m1 HS eq_refl).
    destruct IHhtpy as [? [IH1 [IH2 IH3]]]. repeat eu.
    assert (closed 0 (length G1) 2 T1) as C1. {
      eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed in H. simpl in H. inversion H; subst. inversion H6; subst. eassumption.
    }
    assert (closed 0 (length G1) 0 (TVar true x)) as Cx. {
      eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed1 in H.
      econstructor. omega.
    }
    assert (substt x x0 = x0) as A. {
      eapply subst_closed_id. eapply IH3.
    }
    assert (substt x (open 0 (TVar true x) x0) = (open 0 (TVar true x) x0)) as A'. {
      unfold substt. rewrite <- subst_open_commute1.
      unfold substt in A. rewrite A. reflexivity.
    }
    edestruct HS as [? IHS]. eauto. rewrite <- A' in IH1. eapply IH1.
    instantiate (4:=nil). simpl. eapply IH2.
    repeat rewrite subst_open_commute0b in IHS.
    assert (map (substt x) [] = []) as B by eauto. rewrite B in IHS.
    unfold substt in *. rewrite subst_open_commute1 in IHS.
    rewrite A' in IHS. clear B.
    eexists. split. eapply TY_VarUnpack. eapply TY_Sub. eapply IH1.
    simpl in IHS. eapply IHS. reflexivity.
    eapply closed_open. eapply closed_open. eapply closed_subst. simpl.
    eapply closed_upgrade_gh. eassumption. omega. eassumption.
    eapply closed_upgrade. eassumption. omega.
    eassumption. split.
    assert ((open 1 (TVar true x) T1)=(substt x (open 1 (TVar true x) T1))) as B. {
      erewrite subst_closed_id. reflexivity.
      eapply closed_open. simpl. eapply C1.
      eapply closed_upgrade. eapply Cx. omega.
    }
    unfold substt in B.
    rewrite subst_open_commute1. rewrite <- B.
    eapply stpd_refl. simpl.
    eapply closed_open. eapply closed_open. simpl.
    eapply closed_upgrade_gh. eapply C1. omega.
    econstructor. inversion Cx. omega.
    econstructor. omega.
    eapply closed_open. eapply closed_subst. simpl.
    eapply closed_upgrade_gh. eapply C1. omega.
    eauto. econstructor. inversion Cx. omega.
  - Case "sub".
    admit.
Qed.

Lemma pre_canon_bind: forall m1, Subst m1 -> forall G y T,
  htpy (S m1) G y (TBind T) ->
  htpy m1 G y (open 0 (TVar true y) T).
Proof.
  intros m1 HS G y T H.
  edestruct pre_canon_bind_aux as [? A]; eauto.
  destruct A as [A1 [A2 A3]].
  assert (substt y (open 0 (TVar true y) x) = (open 0 (TVar true y) x)) as Eq. {
    eapply subst_closed_id.
    eapply htpy_to_hastp in A1. destruct A1 as [? A1]. eapply has_type_closed in A1. simpl in A1. eapply A1.
  }
  eu.
  edestruct HS as [? IHS]. eauto. rewrite <- Eq in A1. eapply A1.
  instantiate (4:=nil). simpl. eapply A2.
  simpl in IHS.
  eapply TY_Sub. eapply A1.
  repeat rewrite subst_open_commute0b in IHS.
  erewrite subst_closed_id in IHS. erewrite subst_closed_id in IHS.
  eapply IHS.
  eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed in H. simpl in H. simpl in H. inversion H; subst. eassumption.
  eapply A3.
Qed.
*)