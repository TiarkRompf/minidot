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

Definition Subst (m: nat) := forall GH G x TX T1 T2 m1 n2, m1 < m ->
  htpy m1 G x (substt x TX) ->
  stp (GH++[TX]) G T1 T2 n2 ->
  stpd (map (substt x) GH) G (substt x T1) (substt x T2).

Lemma pre_canon_bind_aux: forall m1, Subst m1 -> forall G y T T0,
  htpy m1 G y T0 -> stpd [] G T0 (TBind T) ->
  htpy (m1-1) G y (open 0 (TVar true y) T).
Proof.
  intros m1 HS G y T T0 H Hsub.
  generalize dependent T.
  induction H; intros; subst.
  - eu. eapply stp_trans_pushback in Hsub.
    assert False as Contra. {
      clear H. clear H3. clear HS. clear x0.
      induction H0; subst; unfold substt in Hsub; simpl in Hsub.
      - inversion Hsub.
      - inversion Hsub; subst. inversion H4. eapply IHdms_has_type. eapply H4.
      - inversion Hsub; subst. inversion H6. eapply IHdms_has_type. eapply H6.
    }
    inversion Contra.
  - remember H as Hm'. clear HeqHm'.
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
      eu. edestruct HS as [? IHS]. eauto. rewrite <- A in Hm'. eapply Hm'.
      instantiate (4:=nil). simpl. eapply H2.
      rewrite A in IHS. rewrite EqT in IHS. simpl in IHS.
      eapply TY_VarUnpack. eapply TY_Sub.
      assert (S m - 1 = m) as Eqm by omega. rewrite Eqm. clear Eqm.
      eapply H. eapply IHS.
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
      eu. edestruct HS as [? IHS]. eauto. rewrite <- A1 in Hm'. eapply Hm'.
      instantiate (4:=nil). simpl. eapply H3.
      rewrite A1 in IHS. rewrite A in IHS. simpl in IHS.
      eapply TY_Sub.
      assert (S m - 1 = m) as Eqm by omega. rewrite Eqm. clear Eqm.
      eapply H. eapply IHS.
  - eu. eapply TY_VarUnpack. eapply TY_Sub. eapply IHhtpy. eapply HS.
    eapply stpd_refl.
    eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed in H. simpl in H. eapply H. eapply Hsub. reflexivity.
    eapply stp_closed2 in Hsub. simpl in Hsub. eapply closed_open. simpl.
    inversion Hsub; subst. eassumption.
    eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed1 in H.
    econstructor. omega.
  - eu. eapply IHhtpy. eapply HS. eexists. eapply stp_trans. eassumption. eapply Hsub.
Qed.

Lemma pre_canon_bind: forall m1, Subst m1 -> forall G y T,
  htpy m1 G y (TBind T) ->
  htpy (m1-1) G y (open 0 (TVar true y) T).
Proof.
  intros. eapply pre_canon_bind_aux; eauto 2.
  eapply stpd_refl.
  simpl.
  eapply htpy_to_hastp in H0. destruct H0 as [? H0]. eapply has_type_closed in H0. simpl in H0. eapply H0.
Qed.

Lemma Subst_mono: forall m1,
  Subst (S m1) ->
  Subst m1.
Proof.
  intros m1. unfold Subst. intros.
  eapply H; try eassumption. omega.
Qed.

Lemma dms_hastp_inv_mem: forall G1 x ds' T' l TS TU n,
  dms_has_type [T'] G1 ds' T' n ->
  closed 0 (length G1) 0 (substt x T') ->
  index x G1 = Some (vobj (subst_dms x ds')) ->
  stpp G1 (substt x T') (TMem l TS TU) ->
  exists T, index l (dms_to_list (subst_dms x ds')) = Some (dty T) /\
  stpd [] G1 TS T /\ stpd [] G1 T TU.
Proof.
  intros G1 x ds' T' l TS TU n H HC HI Hsub.
  remember T' as T0. remember H as HT0. clear HeqHT0.
  rewrite HeqT0 in H at 2. rewrite HeqT0 in Hsub. rewrite HeqT0 in HC. clear HeqT0.
  remember ds' as ds0. rewrite Heqds0 in H.
  assert (exists dsa, dms_to_list ds0 = dsa ++ dms_to_list ds') as Hds. {
    exists []. rewrite app_nil_l. subst. reflexivity.
  }
  clear Heqds0.
  remember n as n0. rewrite Heqn0 in *. rewrite <- Heqn0 in HT0. clear Heqn0.
  remember [T0] as GH. generalize dependent T0.
  generalize dependent TU. generalize dependent TS. generalize dependent l.
  induction H; intros; unfold substt in Hsub; simpl in Hsub.
  - inversion Hsub.
  - subst. simpl in Hsub.
    destruct Hds as [dsa Hdsa]. simpl in Hdsa.
    inversion Hsub; subst.
    + inversion H4; subst.
      exists (subst (TVar true x) T11). split.
      erewrite index_subst_dms with (D:=dty T11). simpl. reflexivity. eauto.
      split; eassumption.
    + assert (closed 0 (length G1) 0 (substt x TS)) as HCS. {
       unfold substt in *. simpl in HC. inversion HC; subst.
       eauto.
      }
      edestruct IHdms_has_type as [T IH]. eauto. eauto.
      exists (dsa ++ [dty T11]). rewrite <- app_assoc. simpl. eauto. eauto. eauto. eauto.
      exists T. eapply IH.
  - subst. simpl in Hsub.
    destruct Hds as [dsa Hdsa]. simpl in Hdsa.
    inversion Hsub; subst.
    + inversion H6.
    + assert (closed 0 (length G1) 0 (substt x TS)) as HCS. {
       unfold substt in *. simpl in HC. inversion HC; subst.
       eauto.
      }
      edestruct IHdms_has_type as [T IH]. eauto. eauto.
      exists (dsa ++ [dfun T11 T12 t12]). rewrite <- app_assoc. simpl. eauto. eauto. eauto. eauto.
      exists T. eapply IH.
Qed.

Lemma htpy_bind0_contra_aux: forall G x T0 T,
  htpy 0 G x T0 -> stpd [] G T0 (TBind T) ->
  False.
Proof.
  intros G x T0 T H Hsub. generalize dependent T.
  remember 0 as m. generalize dependent Heqm.
  induction H; intros; subst.
  - clear H. clear H3.
    eu. eapply stp_trans_pushback in Hsub.
    induction H0; subst; unfold substt in Hsub; simpl in Hsub.
    + inversion Hsub.
    + inversion Hsub; subst. inversion H4. eapply IHdms_has_type. eapply H4.
    + inversion Hsub; subst. inversion H6. eapply IHdms_has_type. eapply H6.
  - inversion Heqm.
  - eapply IHhtpy. eauto. eapply stpd_refl.
    eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed in H. simpl in H. eapply H.
  - eu. eapply IHhtpy. eauto. eexists. eapply stp_trans. eapply H0. eapply Hsub.
Qed.

Lemma htpy_bind0_contra: forall G x T,
  htpy 0 G x (TBind T) ->
  False.
Proof.
  intros. eapply htpy_bind0_contra_aux; eauto 2.
  eapply stpd_refl.
  eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed in H. simpl in H. eapply H.
Qed.

Lemma pre_canon_mem_aux: forall m1, Subst m1 -> forall G y T0,
  htpy m1 G y T0 -> forall l TS TU, stpd [] G T0 (TMem l TS TU) ->
  exists ds T, index y G = Some (vobj ds) /\
               index l (dms_to_list ds) = Some (dty T) /\
               stpd [] G TS T /\ stpd [] G T TU.
Proof.
  intros m1. induction m1; intros HS G y T0 H l TS TU Hsub;
  generalize dependent TU; generalize dependent TS; generalize dependent l;
  simpl in HS.
  {remember 0 as m. rewrite Heqm in *. rewrite <- Heqm in H.
  induction H; intros; subst.
  - eu. eapply stp_trans_pushback in Hsub.
    edestruct dms_hastp_inv_mem as [T IH]; eauto.
  - inversion Heqm.
  - eapply htpy_bind0_contra in H. inversion H.
  - eu. eapply IHhtpy. eauto. eexists. eapply stp_trans. eapply H0. eapply Hsub.
  }
  remember (S m1) as m. induction H; intros; subst.
  - eu. eapply stp_trans_pushback in Hsub.
    edestruct dms_hastp_inv_mem as [T IH]; eauto.
  - inversion Heqm; subst.
    eu. eapply stp_trans_pushback in Hsub. inversion Hsub; subst; eu.
    + assert (substt x T1=T1) as EqT1. {
        eapply subst_closed_id. eassumption.
      }
      assert (substt x (open 0 (TVar false 0) T1) = (open 0 (TVar true x) T1)) as A. {
        rewrite subst_open_commute0b. rewrite EqT1. reflexivity.
      }
      assert (substt x (TMem l TS TU)=(TMem l TS TU)) as EqT. {
        eapply subst_closed_id. eassumption.
      }
      assert (open 0 (TVar false 0) (TMem l TS TU)=(TMem l TS TU)) as EqT'. {
        erewrite <- closed_no_open. reflexivity. eassumption.
      }
      assert (open 0 (TVar true x) (TMem l TS TU)=(TMem l TS TU)) as EqT''. {
        erewrite <- closed_no_open. reflexivity. eassumption.
      }
      assert (htpy (S m1) G1 x (TBind (TMem l TS TU))) as H'. {
        eapply TY_Sub. eapply TY_VarPack; eauto.
        eapply stp_bindx. eapply H2. simpl. reflexivity.
        simpl. simpl in EqT'. rewrite EqT'. reflexivity.
        simpl. eauto. simpl. eapply closed_upgrade. eauto. omega.
      }
      eapply pre_canon_bind in H'. rewrite EqT'' in H'.
      assert (S m1 - 1 = m1) as Eqm1 by omega. rewrite Eqm1 in H'.
      edestruct IHm1 as [ds [T IH]].
      eapply Subst_mono. eassumption. eapply H'.
      eapply stpd_refl. eauto.
      eexists ds. eexists T. eapply IH.
      eassumption.
  - assert (S m1 - 1 = m1) as Eqm1 by omega.
    eu. eapply pre_canon_bind in H. rewrite Eqm1 in H.
    edestruct IHm1 as [ds [T IH]].
    eapply Subst_mono. eassumption. eapply H.
    eexists. eauto.
    eexists ds. eexists T. eapply IH. eassumption.
  - eu. eapply IHhtpy; eauto 2. eexists. eapply stp_trans. eassumption. eapply Hsub.
Qed.

Lemma pre_canon_mem: forall m1, Subst m1 -> forall G y l TS TU,
  htpy m1 G y (TMem l TS TU) ->
  exists ds T, index y G = Some (vobj ds) /\
               index l (dms_to_list ds) = Some (dty T) /\
               stpd [] G TS T /\ stpd [] G T TU.
Proof.
  intros. eapply pre_canon_mem_aux; eauto 2.
  eapply stpd_refl.
  simpl.
  eapply htpy_to_hastp in H0. destruct H0 as [? H0]. eapply has_type_closed in H0. simpl in H0. eapply H0.
Qed.

Lemma unsimpl_substt: forall x T, subst (TVar true x) T=substt x T.
Proof. intros. unfold substt. reflexivity. Qed.

Lemma subst_aux: forall m0 m, m < m0 -> forall n0 n, n < n0 ->
  (forall G x TX GH T1 T2,
    htpy m G x (substt x TX) ->
    stp (GH++[TX]) G T1 T2 n ->
    stpd (map (substt x) GH) G (substt x T1) (substt x T2)) /\
  (forall G x TX GH z T,
    htpy m G x (substt x TX) ->
    z <> 0 ->
    htp (GH++[TX]) G z T n ->
    htpd (map (substt x) GH) G (z-1) (substt x T)) /\
  (forall G x TX GH T,
    htpy m G x (substt x TX) ->
    htp (GH++[TX]) G 0 T n ->
    htpy m G x (substt x T)).
Proof.
  induction m0; intros m LEm. inversion LEm.
  induction n0; intros n LEn. inversion LEn.
  split; try split.
  - intros  G x TX GH T1 T2 HX Hsub.
    assert (x < length G) as CX. {
      eapply htpy_to_hastp in HX. destruct HX as [? HX]. eapply has_type_closed1 in HX.
      eauto.
    }
    inversion Hsub; subst.
    + unfold substt at 2. simpl.
      eexists. eapply stp_bot.
      rewrite map_length. eapply closed_subst.
      rewrite app_length in H. simpl in H. eapply H. econstructor. omega.
    + unfold substt at 3. simpl.
      eexists. eapply stp_top.
      rewrite map_length. eapply closed_subst.
      rewrite app_length in H. simpl in H. eapply H. econstructor. omega.
    + unfold substt at 2. unfold substt at 2. simpl.
      rewrite app_length in *. simpl in *.
      eapply stpd_fun. reflexivity. reflexivity.
      rewrite map_length. eapply closed_subst. eassumption. econstructor. omega.
      rewrite map_length. eapply closed_subst. eassumption. econstructor. omega.
      eapply IHn0. instantiate (1:=n1). omega. eapply HX. eassumption.
      edestruct IHn0 as [IH ?]. instantiate (1:=n2). omega.
      specialize (IH G x TX).
      specialize (IH (T4::GH) (open 0 (TVar false (length GH + 1)) T3) (open 0 (TVar false (length GH + 1)) T5)).
      specialize (IH HX H4).
      simpl in IH. repeat unfold substt in IH at 3.
      erewrite subst_open_commute in IH. erewrite subst_open_commute in IH.
      rewrite map_length. unfold substt in IH at 1. eapply IH.
      eauto. eauto. eauto. eauto.
    + repeat unfold substt at 2. simpl.
      eapply stpd_mem.
      eapply IHn0. instantiate (1:=n2). omega. eapply HX. eassumption.
      eapply IHn0. instantiate (1:=n1). omega. eapply HX. eassumption.
    + repeat unfold substt at 2. simpl.
      eexists. eapply stp_varx. assumption.
    + repeat unfold substt at 2. simpl.
      case_eq (beq_nat x0 0); intros E.
      * eexists. eapply stp_varx. assumption.
      * eexists. eapply stp_varax.
        rewrite map_length. rewrite app_length in *. simpl in *.
        eapply beq_nat_false in E. omega.
    + unfold substt at 2. simpl. erewrite subst_closed_id.
      eexists. eapply stp_strong_sel1; eauto 2.
      eapply stp_closed2 in H1. simpl in H1. eapply H1.
    + unfold substt at 3. simpl. erewrite subst_closed_id.
      eexists. eapply stp_strong_sel2; eauto 2.
      eapply stp_closed1 in H1. simpl in H1. eapply H1.
    + Case "sel1".
      unfold substt at 2. simpl.
      case_eq (beq_nat x0 0); intros E.
      * (* interesting case: converting from abstract to concrete sel1 *)
        apply beq_nat_true in E. subst.
        assert (htpy m G x (substt x (TMem l TBot T2))) as IH. {
          eapply IHn0. instantiate (1:=n1). omega. eapply HX. eassumption.
        }
        edestruct pre_canon_mem as [ds [T IH']].
        unfold substt in IH. simpl in IH.
        instantiate (1:=m). unfold Subst. intros.
        eapply IHm0. instantiate (1:=m1). omega.
        instantiate (1:=S n2). instantiate (1:=n2). omega. eauto. eassumption.
        eapply IH. rewrite unsimpl_substt in IH'.
        destruct IH' as [IH1 [IH2 [IH3 IH4]]]. repeat eu.
        eexists. eapply stp_strong_sel1; eauto 2.
      * apply beq_nat_false in E.
        assert (htpd (map (substt x) GH) G (x0-1) (substt x (TMem l TBot T2))) as IH. {
          eapply IHn0. instantiate (1:=n1). omega. eapply HX. apply E.
          eassumption.
        }
        eu.
        eexists. eapply stp_sel1; eauto 2.
    + Case "sel2".
      unfold substt at 3. simpl.
      case_eq (beq_nat x0 0); intros E.
      * (* interesting case: converting from abstract to concrete sel2 *)
        apply beq_nat_true in E. subst.
        assert (htpy m G x (substt x (TMem l T1 TTop))) as IH. {
          eapply IHn0. instantiate (1:=n1). omega. eapply HX. eassumption.
        }
        edestruct pre_canon_mem as [ds [T IH']].
        unfold substt in IH. simpl in IH.
        instantiate (1:=m). unfold Subst. intros.
        eapply IHm0. instantiate (1:=m1). omega.
        instantiate (1:=S n2). instantiate (1:=n2). omega. eauto. eassumption.
        eapply IH. rewrite unsimpl_substt in IH'.
        destruct IH' as [IH1 [IH2 [IH3 IH4]]]. repeat eu.
        eexists. eapply stp_strong_sel2; eauto 2.
      * apply beq_nat_false in E.
        assert (htpd (map (substt x) GH) G (x0-1) (substt x (TMem l T1 TTop))) as IH. {
          eapply IHn0. instantiate (1:=n1). omega. eapply HX. apply E.
          eassumption.
        }
        eu.
        eexists. eapply stp_sel2; eauto 2.
    + repeat unfold substt at 2. simpl.
      eexists. eapply stp_selx.
      rewrite app_length in *. simpl in *.
      rewrite map_length. eapply closed_subst. eassumption.
      econstructor. omega.
    + unfold substt at 2. simpl.
      specialize (IHn0 n1).
      assert (n1 < n0) as LEn1 by omega. specialize (IHn0 LEn1).
      destruct IHn0 as [IH ?]. specialize (IH G x TX).
      specialize (IH (open 0 (TVar false (length (GH ++ [TX]))) T0 :: GH)).
      specialize (IH (open 0 (TVar false (length (GH ++ [TX]))) T0)).
      specialize (IH T2 HX). specialize (IH H). eu.
      rewrite app_length in *. simpl in *.
      eexists. eapply stp_bind1. eapply IH.
      rewrite map_length. simpl. unfold substt.
      erewrite subst_open_commute. reflexivity. simpl. eassumption.
      econstructor. omega.
      rewrite map_length. eapply closed_subst. eassumption.
      econstructor. omega.
      rewrite map_length. eapply closed_subst. eassumption.
      econstructor. omega.
    +