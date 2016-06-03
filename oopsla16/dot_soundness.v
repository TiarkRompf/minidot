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
    + repeat unfold substt at 2. simpl.
      specialize (IHn0 n1).
      assert (n1 < n0) as LEn1 by omega. specialize (IHn0 LEn1).
      destruct IHn0 as [IH ?]. specialize (IH G x TX).
      specialize (IH (open 0 (TVar false (length (GH ++ [TX]))) T0 :: GH)).
      specialize (IH (open 0 (TVar false (length (GH ++ [TX]))) T0)).
      specialize (IH (open 0 (TVar false (length (GH ++ [TX]))) T3)).
      specialize (IH HX). specialize (IH H). eu.
      rewrite app_length in *. simpl in *.
      eexists. eapply stp_bindx. eapply IH.
      rewrite map_length. simpl. unfold substt.
      erewrite subst_open_commute. reflexivity. simpl. eassumption.
      econstructor. omega.
      rewrite map_length. simpl. unfold substt.
      erewrite subst_open_commute. reflexivity. simpl. eassumption.
      econstructor. omega.
      rewrite map_length. eapply closed_subst. eassumption.
      econstructor. omega.
      rewrite map_length. eapply closed_subst. eassumption.
      econstructor. omega.
    + unfold substt at 2. simpl.
      specialize (IHn0 n1).
      assert (n1 < n0) as LEn1 by omega. specialize (IHn0 LEn1).
      destruct IHn0 as [IH ?]. specialize (IH G x TX).
      specialize (IH GH T0 T2).
      specialize (IH HX). specialize (IH H). eu.
      rewrite app_length in *. simpl in *.
      eexists. eapply stp_and11. eapply IH.
      rewrite map_length. eapply closed_subst. eassumption. econstructor. omega.
    + unfold substt at 2. simpl.
      specialize (IHn0 n1).
      assert (n1 < n0) as LEn1 by omega. specialize (IHn0 LEn1).
      destruct IHn0 as [IH ?]. specialize (IH G x TX).
      specialize (IH GH T3 T2).
      specialize (IH HX). specialize (IH H). eu.
      rewrite app_length in *. simpl in *.
      eexists. eapply stp_and12. eapply IH.
      rewrite map_length. eapply closed_subst. eassumption. econstructor. omega.
    + unfold substt at 3. simpl.
      remember IHn0 as IH1. clear HeqIH1.
      specialize (IH1 n1).
      assert (n1 < n0) as LEn1 by omega. specialize (IH1 LEn1).
      destruct IH1 as [IH1 ?]. specialize (IH1 G x TX).
      specialize (IH1 GH T1 T0).
      specialize (IH1 HX). specialize (IH1 H). eu.
      remember IHn0 as IH2. clear HeqIH2.
      specialize (IH2 n2).
      assert (n2 < n0) as LEn2 by omega. specialize (IH2 LEn2).
      destruct IH2 as [IH2 ?]. specialize (IH2 G x TX).
      specialize (IH2 GH T1 T3).
      specialize (IH2 HX). specialize (IH2 H0). eu.
      eexists. eapply stp_and2. eapply IH1. eapply IH2.
    + unfold substt at 1. simpl.
      specialize (IHn0 n1).
      assert (n1 < n0) as LEn1 by omega. specialize (IHn0 LEn1).
      destruct IHn0 as [IH ?]. specialize (IH G x TX).
      specialize (IH GH T1 T0).
      specialize (IH HX). specialize (IH H). eu.
      rewrite app_length in *. simpl in *.
      eexists. eapply stp_or21. eapply IH.
      rewrite map_length. eapply closed_subst. eassumption. econstructor. omega.
    + unfold substt at 1. simpl.
      specialize (IHn0 n1).
      assert (n1 < n0) as LEn1 by omega. specialize (IHn0 LEn1).
      destruct IHn0 as [IH ?]. specialize (IH G x TX).
      specialize (IH GH T1 T3).
      specialize (IH HX). specialize (IH H). eu.
      rewrite app_length in *. simpl in *.
      eexists. eapply stp_or22. eapply IH.
      rewrite map_length. eapply closed_subst. eassumption. econstructor. omega.
    + unfold substt at 3. simpl.
      remember IHn0 as IH1. clear HeqIH1.
      specialize (IH1 n1).
      assert (n1 < n0) as LEn1 by omega. specialize (IH1 LEn1).
      destruct IH1 as [IH1 ?]. specialize (IH1 G x TX).
      specialize (IH1 GH T0 T2).
      specialize (IH1 HX). specialize (IH1 H). eu.
      remember IHn0 as IH2. clear HeqIH2.
      specialize (IH2 n2).
      assert (n2 < n0) as LEn2 by omega. specialize (IH2 LEn2).
      destruct IH2 as [IH2 ?]. specialize (IH2 G x TX).
      specialize (IH2 GH T3 T2).
      specialize (IH2 HX). specialize (IH2 H0). eu.
      eexists. eapply stp_or1. eapply IH1. eapply IH2.
    + eapply stpd_trans.
      eapply IHn0. instantiate (1:=n1). omega. eapply HX. eassumption.
      eapply IHn0. instantiate (1:=n2). omega. eapply HX. eassumption.

  - intros G x TX GH z T HX NE HZ.
    assert (x < length G) as CX. {
      eapply htpy_to_hastp in HX. destruct HX as [? HX]. eapply has_type_closed1 in HX.
      eauto.
    }
    inversion HZ; subst.
    + eexists. eapply htp_var. eapply index_subst1. eapply H. eapply NE.
      eapply closed_subst. eapply closed_upgrade_gh. eassumption.
      omega. econstructor. omega.
    + assert (htpd (map (substt x) GH) G (z - 1) (substt x (TBind TX0))) as IH. {
        eapply IHn0. instantiate (1:=n1). omega. eapply HX. eassumption.
        eassumption.
      }
      eu. rewrite subst_open5. eexists. eapply htp_unpack. eapply IH.
      eapply closed_subst. eapply closed_upgrade_gh. eassumption. omega.
      econstructor. omega. apply nil. eassumption.
    + assert (htpd (map (substt x) GH) G (z - 1) (substt x T1)) as IH1. {
        eapply IHn0. instantiate (1:=n1). omega. eapply HX. eassumption.
        eassumption.
      }
      edestruct gh_match1 as [GL1 [EqGL EqGH]]. eassumption. omega.
      assert (stpd (map (substt x) GL1) G (substt x T1) (substt x T)) as IH2. {
        eapply IHn0. instantiate (1:=n2). omega. eapply HX.
        rewrite <- EqGL. eassumption.
      }
      repeat eu.
      eexists. eapply htp_sub. eapply IH1. eapply IH2.
      rewrite map_length. subst. rewrite app_length in *. simpl in *. omega.
      instantiate (1:=(map (substt x) GU)). subst. rewrite map_app. reflexivity.

  - intros G x TX GH T HX HZ.
    assert (x < length G) as CX. {
      eapply htpy_to_hastp in HX. destruct HX as [? HX]. eapply has_type_closed1 in HX.
      eauto.
    }
    inversion HZ; subst.
    + Case "var".
      eapply index_hit0 in H. subst. eapply HX.
    + Case "unpack".
      eapply TY_VarUnpack.
      instantiate (1:=substt x TX0).
      assert (TBind (substt x TX0)=substt x (TBind TX0)) as A by
            solve [unfold substt; simpl; reflexivity].
      rewrite A.
      eapply IHn0. instantiate (1:=n1). omega. eapply HX. eassumption.
      rewrite subst_open_commute0b. reflexivity.
      eapply closed_subst. eapply closed_open. simpl. eapply closed_upgrade_gh.
      eassumption. omega. simpl. econstructor. omega. econstructor. omega.
      (* TODO(draft): I didn't need Lemma 6 here -- it's an unpack, not a pack :) ... *)
    + Case "sub".
      edestruct gh_match1 as [GL1 [EqGL EqGH]]. eassumption. omega.
      assert (length GL1=0) as EGL1. {
        subst. rewrite app_length in *. simpl in *. omega.
      }
      assert (GL1=[]) as EqGL1. {
        destruct GL1. reflexivity. simpl in EGL1. omega.
      }
      rewrite EqGL1 in EqGL. simpl in EqGL.
      assert (stpd (map (substt x) []) G (substt x T1) (substt x T)) as IH2. {
        eapply IHn0. instantiate (1:=n2). omega. eapply HX. simpl.
        rewrite <- EqGL. eassumption.
      }
      eu.
      eapply TY_Sub.
      eapply IHn0. instantiate (1:=n1). omega. eapply HX. eassumption. eapply IH2.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stp_subst: forall G x TX GH T1 T2 nx n,
  has_type [] G (tvar true x) (substt x TX) nx ->
  stp (GH++[TX]) G T1 T2 n ->
  stpd (map (substt x) GH) G (substt x T1) (substt x T2).
Proof.
  intros. edestruct hastp_to_htpy as [m HX]. eassumption.
  eapply subst_aux; eauto 2.
Qed.

Lemma all_Subst: forall m, Subst m.
Proof.
  intros. unfold Subst. intros. eapply htpy_to_hastp in H0. destruct H0.
  eapply stp_subst; eauto 2.
Qed.

Lemma htp_to_hastp: forall GH G z T n,
  htp GH G z T n ->
  has_typed GH G (tvar false z) T.
Proof.
  intros. induction H;
  try destruct IHhtp as [n IH].
  - eexists. eapply T_Varz. assumption.
    eapply closed_upgrade_gh. eassumption. eapply index_max in H. omega.
  - eexists. eapply T_VarUnpack; eauto 2.
    eapply has_type_closed_z in IH.
    eapply closed_open. simpl. eapply closed_upgrade_gh. eassumption. omega.
    econstructor. omega.
  - eexists. eapply T_Sub. eassumption. subst.
    eapply stp_upgrade_gh_mult. eassumption.
Grab Existential Variables. apply 0.
Qed.

Lemma htp_subst: forall G x TX GH z T nx n,
  has_type [] G (tvar true x) (substt x TX) nx ->
  htp (GH++[TX]) G z T n ->
  has_typed (map (substt x) GH) G (subst_tm x (tvar false z)) (substt x T).
Proof.
  intros. edestruct hastp_to_htpy as [m HX]. eassumption.
  simpl. case_eq (beq_nat z 0); intros E.
  - apply beq_nat_true in E. subst.
    assert (htpy m G x (substt x T)) as IH. {
      eapply subst_aux. instantiate (1:=S m). omega. eauto. eapply HX. eassumption.
    }
    eapply htpy_to_hastp in IH. destruct IH as [n' IH].
    eapply hastp_upgrade_gh. eapply IH.
  - apply beq_nat_false in E.
    assert (htpd (map (substt x) GH) G (z - 1) (substt x T)) as IH. {
      eapply subst_aux. eauto. eauto. eapply HX. assumption. eassumption.
    }
    destruct IH as [n' IH]. eapply htp_to_hastp. eapply IH.
Qed.

Lemma canon_bind: forall G y T n,
  has_type [] G (tvar true y) (TBind T) n ->
  has_typed [] G (tvar true y) (open 0 (TVar true y) T).
Proof.
  intros.
  eapply hastp_to_htpy in H. destruct H as [m H].
  assert (htpy (m-1) G y (open 0 (TVar true y) T)) as A. {
    eapply pre_canon_bind. eapply all_Subst. eapply H.
  }
  eapply htpy_to_hastp. eapply A.
Qed.

Lemma canon_mem: forall G y l TS TU n,
  has_type [] G (tvar true y) (TMem l TS TU) n ->
  exists ds T, index y G = Some (vobj ds) /\
               index l (dms_to_list ds) = Some (dty T) /\
               stpd [] G TS T /\ stpd [] G T TU.
Proof.
  intros.
  eapply hastp_to_htpy in H. destruct H as [m H].
  eapply pre_canon_mem; eauto 2. eapply all_Subst.
Qed.

(* TODO(draft):
hastp_subst is needed for canonical forms on functions (to substitute self).
The paper delays this lemma until main soundness proof, while it would fit nicely
at the end of the section on substitution. *)
Lemma hastp_subst_aux: forall n0 n, n < n0 -> forall G1 GH TX T x t nx,
  has_type (GH++[TX]) G1 t T n ->
  has_type [] G1 (tvar true x) (substt x TX) nx ->
  has_typed (map (substt x) GH) G1 (subst_tm x t) (substt x T).
Proof.
  intros n0. induction n0; intros n LE. inversion LE.
  intros G1 GH TX T x t nx H HX.
  inversion H; subst.
  - eexists. simpl.
    erewrite subst_closed_id. eapply T_Vary; eauto 2. eassumption.
  - simpl. case_eq (beq_nat x0 0); intros E.
    + apply beq_nat_true in E. subst. apply index_hit0 in H0. subst.
      eapply hastp_upgrade_gh. eassumption.
    + apply beq_nat_false in E.
      eexists. eapply T_Varz. eapply index_subst1. eassumption. apply E.
      rewrite app_length in *. simpl in *. rewrite map_length.
      eapply closed_subst. eassumption. econstructor.
      eapply has_type_closed1 in HX. omega.
  - simpl. edestruct IHn0 as [? IH]; eauto. omega. destruct b.
    + eexists. simpl in IH. eapply T_VarPack. eapply IH.
      rewrite subst_open_commute1. eauto.
      rewrite map_length. eapply closed_subst. rewrite app_length in *. simpl in *.
      eassumption. econstructor. eapply has_type_closed1 in HX. omega.
    + case_eq (beq_nat x0 0); intros E.
      * apply beq_nat_true in E. subst. unfold substt at 2. simpl. simpl in IH.
        eexists. eapply T_VarPack. eapply IH.
        rewrite subst_open_commute0b. eauto.
        rewrite map_length. eapply closed_subst. rewrite app_length in *. simpl in *.
        eassumption. econstructor. eapply has_type_closed1 in HX. omega.
      * simpl in IH. rewrite E in IH. unfold substt at 2. simpl.
        eexists. eapply T_VarPack. eapply IH.
        rewrite subst_open5. eauto. apply nil. apply beq_nat_false; eauto.
        rewrite map_length. eapply closed_subst. rewrite app_length in *. simpl in *.
        eassumption. econstructor. eapply has_type_closed1 in HX. omega.
  - simpl. edestruct IHn0 as [? IH]. instantiate (1:=n1). omega. eauto. eauto.
    destruct b.
    + eexists. simpl in IH. eapply T_VarUnpack. eapply IH.
      rewrite subst_open_commute1. eauto.
      rewrite map_length. eapply closed_subst. rewrite app_length in *. simpl in *.
      eassumption. econstructor. eapply has_type_closed1 in HX. omega.
    + case_eq (beq_nat x0 0); intros E.
      * apply beq_nat_true in E. subst. unfold substt at 2. simpl. simpl in IH.
        eexists. eapply T_VarUnpack. eapply IH.
        eapply subst_open_commute0b.
        rewrite map_length. eapply closed_subst. rewrite app_length in *. simpl in *.
        eassumption. econstructor. eapply has_type_closed1 in HX. omega.
      * simpl in IH. rewrite E in IH. unfold substt at 2. simpl.
        eexists. eapply T_VarUnpack. eapply IH.
        eapply subst_open5. apply nil. apply beq_nat_false; eauto.
        rewrite map_length. eapply closed_subst. rewrite app_length in *. simpl in *.
        eassumption. econstructor. eapply has_type_closed1 in HX. omega.
  - simpl. unfold substt at 2. simpl. rewrite unsimpl_substt. admit.
  - simpl.
    edestruct IHn0 as [? IH1]. instantiate (1:=n1). omega. eauto. eauto.
    edestruct IHn0 as [? IH2]. instantiate (1:=n2). omega. eauto. eauto.
    eexists. eapply T_App. eapply IH1. eapply IH2.
    rewrite map_length. eapply closed_subst. rewrite app_length in *. simpl in *.
    eassumption. econstructor. eapply has_type_closed1 in HX. omega.
  - edestruct IHn0 as [? IH1]. instantiate (1:=n1). omega. eauto. eauto.
    edestruct IHn0 as [? IH2]. instantiate (1:=n2). omega. eauto. eauto.
    simpl. destruct b2.
    + eexists. eapply T_AppVar. eapply IH1. eapply IH2.
      rewrite subst_open_commute1. eauto.
      rewrite map_length. eapply closed_subst. rewrite app_length in *. simpl in *.
      eassumption. econstructor. eapply has_type_closed1 in HX. omega.
    + case_eq (beq_nat x2 0); intros E.
      * apply beq_nat_true in E. subst.
        eexists. eapply T_AppVar. eapply IH1. eapply IH2.
        eapply subst_open_commute0b.
        rewrite map_length. eapply closed_subst. rewrite app_length in *. simpl in *.
        eassumption. econstructor. eapply has_type_closed1 in HX. omega.
      * simpl in IH2. rewrite E in IH2.
        eexists. eapply T_AppVar. eapply IH1. eapply IH2.
        eapply subst_open5. apply nil. apply beq_nat_false; eauto.
        rewrite map_length. eapply closed_subst. rewrite app_length in *. simpl in *.
        eassumption. econstructor. eapply has_type_closed1 in HX. omega.
  - edestruct IHn0 as [? IH1]. instantiate (1:=n1). omega. eauto. eauto.
    edestruct stp_subst as [? IH2]. eauto. eauto.
    eexists. eapply T_Sub. eapply IH1. eapply IH2.
Grab Existential Variables.
apply 0.
Qed.

Lemma hastp_subst: forall n G1 GH TX T x t nx,
  has_type (GH++[TX]) G1 t T n ->
  has_type [] G1 (tvar true x) (substt x TX) nx ->
  has_typed (map (substt x) GH) G1 (subst_tm x t) (substt x T).
Proof.
  intros. eapply hastp_subst_aux; eauto 2.
Qed.

Lemma dms_hastp_inv_fun: forall G1 x ds' T' l TS TU n nx,
  has_type [] G1 (tvar true x) (substt x T') nx ->
  dms_has_type [T'] G1 ds' T' n ->
  closed 0 (length G1) 0 (substt x T') ->
  index x G1 = Some (vobj (subst_dms x ds')) ->
  stpp G1 (substt x T') (TFun l TS TU) ->
  exists TS' TU' t', index l (dms_to_list (subst_dms x ds')) = Some (dfun TS' TU' t') /\
  has_typed [TS'] G1 t' (open 0 (TVar false 0) TU') /\
  stpd [] G1 (TFun l TS' TU') (TFun l TS TU).
Proof.
  intros G1 x ds' T' l TS TU n nx HX H HC HI Hsub.
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
    + inversion H4.
    + assert (closed 0 (length G1) 0 (substt x TS)) as HCS. {
       unfold substt in *. simpl in HC. inversion HC; subst.
       eauto.
      }
      edestruct IHdms_has_type as [T IH]. eauto. eauto.
      exists (dsa ++ [dty T11]). rewrite <- app_assoc. simpl. eauto. eauto. eauto. eauto. eauto.
      exists T. eapply IH.
  - subst. simpl in Hsub.
    destruct Hds as [dsa Hdsa]. simpl in Hdsa.
    inversion Hsub; subst.
    + inversion H6; subst.
      exists (subst (TVar true x) T11). exists (subst (TVar true x) T12).
      eexists (subst_tm x t12).
      split.
      erewrite index_subst_dms with (D:=dfun T11 T12 t12). simpl. reflexivity. eauto.
      split.
      * edestruct hastp_subst with (GH:=[T11]) (TX:=T0) as [? A]; eauto. simpl in A.
        erewrite <- subst_open_commute. simpl. unfold substt in A. eexists. eapply A.
        eauto. econstructor. eapply has_type_closed1 in HX. omega.
      * eapply stpp_to_stp. eassumption.
    + assert (closed 0 (length G1) 0 (substt x TS)) as HCS. {
       unfold substt in *. simpl in HC. inversion HC; subst.
       eauto.
      }
      edestruct IHdms_has_type as [T IH]. eauto. eauto.
      exists (dsa ++ [dfun T11 T12 t12]). rewrite <- app_assoc. simpl. eauto. eauto. eauto. eauto. eauto.
      exists T. eapply IH.
Qed.

Lemma canon_fun_aux: forall m1, forall G y T0,
  htpy m1 G y T0 -> forall l TS TU, stpd [] G T0 (TFun l TS TU) ->
  exists ds TS' TU' t',
    index y G = Some (vobj ds) /\
    index l (dms_to_list ds) = Some (dfun TS' TU' t') /\
    has_typed [TS'] G t' (open 0 (TVar false 0) TU') /\
    stpd [] G (TFun l TS' TU') (TFun l TS TU).
Proof.
  intros m1. induction m1; intros G y T0 H l TS TU Hsub;
  generalize dependent TU; generalize dependent TS; generalize dependent l.
  {remember 0 as m. rewrite Heqm in *. rewrite <- Heqm in H.
  induction H; intros; subst.
  - eu. eapply stp_trans_pushback in Hsub.
    edestruct dms_hastp_inv_fun as [TS' [TU' [t' [IH1 [IH2 [IH3 IH4]]]]]]; eauto 2. eu.
    repeat eexists; eauto.
  - inversion Heqm.
  - eapply htpy_bind0_contra in H. inversion H.
  - eu. eapply IHhtpy. eauto. eexists. eapply stp_trans. eapply H0. eapply Hsub.
  }
  remember (S m1) as m. induction H; intros; subst.
  - eu. eapply stp_trans_pushback in Hsub.
    edestruct dms_hastp_inv_fun as [ds [TS' [TU' [t' [IH1 [IH2 IH3]]]]]]; eauto 2. eu.
    repeat eexists; eauto.
  - inversion Heqm; subst.
    eu. eapply stp_trans_pushback in Hsub. inversion Hsub; subst; eu.
    + assert (substt x T1=T1) as EqT1. {
        eapply subst_closed_id. eassumption.
      }
      assert (substt x (open 0 (TVar false 0) T1) = (open 0 (TVar true x) T1)) as A. {
        rewrite subst_open_commute0b. rewrite EqT1. reflexivity.
      }
      assert (substt x (TFun l TS TU)=(TFun l TS TU)) as EqT. {
        eapply subst_closed_id. eassumption.
      }
      assert (open 0 (TVar false 0) (TFun l TS TU)=(TFun l TS TU)) as EqT'. {
        erewrite <- closed_no_open. reflexivity. eassumption.
      }
      assert (open 0 (TVar true x) (TFun l TS TU)=(TFun l TS TU)) as EqT''. {
        erewrite <- closed_no_open. reflexivity. eassumption.
      }
      assert (htpy (S m1) G1 x (TBind (TFun l TS TU))) as H'. {
        eapply TY_Sub. eapply TY_VarPack; eauto.
        eapply stp_bindx. eapply H2. simpl. reflexivity.
        simpl. simpl in EqT'. rewrite EqT'. reflexivity.
        simpl. eauto. simpl. eapply closed_upgrade. eauto. omega.
      }
      eapply pre_canon_bind in H'. rewrite EqT'' in H'.
      assert (S m1 - 1 = m1) as Eqm1 by omega. rewrite Eqm1 in H'.
      edestruct IHm1 as [? IH]. eapply H'.
      eapply stpd_refl. eauto.
      eexists. eapply IH.
      eapply all_Subst.
  - assert (S m1 - 1 = m1) as Eqm1 by omega.
    eu. eapply pre_canon_bind in H. rewrite Eqm1 in H.
    edestruct IHm1 as [? IH]. eapply H. eexists. eauto.
    eexists. eapply IH. eapply all_Subst.
  - eu. eapply IHhtpy; eauto 2. eexists. eapply stp_trans. eassumption. eapply Hsub.
Qed.

Lemma canon_fun: forall G1 x l TS TU nx,
  has_type [] G1 (tvar true x) (TFun l TS TU) nx ->
  exists ds TS' TU' t',
    index x G1 = Some (vobj ds) /\
    index l (dms_to_list ds) = Some (dfun TS' TU' t') /\
    has_typed [TS'] G1 t' (open 0 (TVar false 0) TU') /\
    stpd [] G1 (TFun l TS' TU') (TFun l TS TU).
Proof.
  intros.
  eapply hastp_to_htpy in H. destruct H as [m H].
  eapply canon_fun_aux; eauto 2.
  eapply stpd_refl.
  eapply htpy_to_hastp in H. destruct H as [? H]. eapply has_type_closed in H. eapply H.
Qed.

Theorem type_safety : forall G t T n1,
  has_type [] G t T n1 ->
  (exists x, t = tvar true x) \/
  (exists G' t' n2, step G t (G'++G) t' /\ has_type [] (G'++G) t' T n2).
Proof.
  intros.
  assert (closed (length ([]:tenv)) (length G) 0 T) as CL. eapply has_type_closed. eauto.
  remember [] as GH. remember t as tt. remember T as TT.
  revert T t HeqTT HeqGH Heqtt CL.
  induction H; intros.
  - Case "vary". eauto.
  - Case "varz". subst GH. inversion H.
  - Case "pack". subst GH.
    eapply has_type_closed_b in H. destruct H. subst.
    left. eexists. reflexivity.
  - Case "unpack". subst GH.
    eapply has_type_closed_b in H. destruct H. subst.
    left. eexists. reflexivity.
  - Case "obj". subst. right.
    repeat eexists. rewrite <- app_cons1. eapply ST_Obj.
    eapply T_VarPack. eapply T_Vary.
    simpl. rewrite beq_nat_true_eq. eauto. eapply dms_has_type_extend. eauto. eauto. eauto.
    eapply closed_subst. eapply closed_open. eapply closed_extend. eapply closed_upgrade_gh. eauto.
    simpl. omega. simpl. econstructor. omega. simpl. econstructor. omega.
    simpl. rewrite subst_open_commute0b. erewrite subst_closed_id. reflexivity. eauto.
    eapply closed_extend. eauto.
  - Case "app". subst.
    assert (closed (length ([]:tenv)) (length G1) 0 (TFun l T1 T)) as TF. eapply has_type_closed. eauto.
    assert ((exists x : id, t2 = tvar true x) \/
                (exists (G' : venv) (t' : tm) n2,
                   step G1 t2 (G'++G1) t' /\ has_type [] (G'++G1) t' T1 n2)) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto.
    assert ((exists x : id, t1 = tvar true x) \/
                (exists (G' : venv) (t' : tm) n2,
                   step G1 t1 (G'++G1) t' /\ has_type [] (G'++G1) t' (TFun l T1 T) n2)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      destruct HX.
      * SSCase "arg-val".
        ev. ev. subst.

      edestruct canon_fun as [ds' [TS' [TU' [t' IH]]]]. eassumption.
      destruct IH as [IHx [IHl [IHt IHs]]]. repeat eu.
      eapply stp_trans_pushback in IHs. inversion IHs; subst. repeat eu.
      edestruct stp_subst as [? Bs]. erewrite subst_closed_id.
      eapply H0. eapply has_type_closed in H0. simpl. eapply H0.
      instantiate (4:=nil). simpl. eassumption.
      edestruct hastp_subst as [? Bt].
      instantiate (6:=nil). simpl. eapply IHt. erewrite subst_closed_id.
      eapply T_Sub. eapply H0. eassumption.
      change 0 with (length (@nil ty)). eapply stp_closed2. eassumption.
      simpl in *.

      right. repeat eexists. rewrite app_nil_l. eapply ST_AppAbs. eauto. eauto.
      simpl. eapply T_Sub. eapply Bt.
      assert (substt x0 (open 0 (TVar false 0) T)=T) as EqT2. {
        rewrite subst_open_commute0b. erewrite subst_closed_id.
        erewrite <- closed_no_open. reflexivity.
        eassumption. eassumption.
      }
      rewrite <- EqT2. eapply Bs.

      * SSCase "arg_step".
        ev. subst.
        right. repeat eexists. eapply ST_App2. eauto. eapply T_App.
        eapply has_type_extend_mult. eauto. eauto.
        simpl in *. rewrite app_length. eapply closed_extend_mult. eassumption. omega.
    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply ST_App1. eauto. eapply T_App.
      eauto. eapply has_type_extend_mult. eauto.
      simpl in *. rewrite app_length. eapply closed_extend_mult. eassumption. omega.

  - Case "appvar". subst.
    assert (closed (length ([]:tenv)) (length G1) 0 (TFun l T1 T2)) as TF. eapply has_type_closed. eauto.
    assert ((exists x : id, tvar b2 x2 = tvar true x) \/
                (exists (G' : venv) (t' : tm) n2,
                   step G1 (tvar b2 x2) (G'++G1) t' /\ has_type [] (G'++G1) t' T1 n2)) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto.
    assert (b2 = true) as HXeq. {
      destruct HX as [[? HX] | Contra]. inversion HX. reflexivity.
      destruct Contra as [G' [t' [n' [Hstep Htyp]]]].
      inversion Hstep.
    }
    clear HX. subst b2.
    assert ((exists x : id, t1 = tvar true x) \/
                (exists (G' : venv) (t' : tm) n2,
                   step G1 t1 (G'++G1) t' /\ has_type [] (G'++G1) t' (TFun l T1 T2) n2)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      ev. ev. subst.

      edestruct canon_fun as [ds' [TS' [TU' [t' IH]]]]. eassumption.
      destruct IH as [IHx [IHl [IHt IHs]]]. repeat eu.
      eapply stp_trans_pushback in IHs. inversion IHs; subst. repeat eu.
      edestruct stp_subst as [? Bs]. erewrite subst_closed_id.
      eapply H0. eapply has_type_closed in H0. simpl. eapply H0.
      instantiate (4:=nil). simpl. eassumption.
      edestruct hastp_subst as [? Bt].
      instantiate (6:=nil). simpl. eapply IHt. erewrite subst_closed_id.
      eapply T_Sub. eapply H0. eassumption.
      change 0 with (length (@nil ty)). eapply stp_closed2. eassumption.
      simpl in *.

      right. repeat eexists. rewrite app_nil_l. eapply ST_AppAbs. eauto. eauto.
      simpl. eapply T_Sub. eapply Bt.
      assert (substt x2 (open 0 (TVar false 0) T2)=open 0 (TVar true x2) T2) as EqT2. {
        rewrite subst_open_commute0b. erewrite subst_closed_id. reflexivity.
        eassumption.
      }
      rewrite <- EqT2. eapply Bs.

    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply ST_App1. eauto. eapply T_AppVar.
      eauto. eapply has_type_extend_mult. eauto. reflexivity.
      simpl in *. rewrite app_length. eapply closed_extend_mult. eassumption. omega.

  - Case "sub". subst.
    assert ((exists x : id, t0 = tvar true x) \/
               (exists (G' : venv) (t' : tm) n2,
                  step G1 t0 (G'++G1) t' /\ has_type [] (G'++G1) t' T1 n2)) as HH.
    eapply IHhas_type; eauto. change 0 with (length ([]:tenv)) at 1. eapply stpd_closed1; eauto.
    destruct HH.
    + SCase "val".
      ev. subst. left. eexists. eauto.
    + SCase "step".
      ev. subst.
      right. repeat eexists. eauto. eapply T_Sub. eauto. eapply stp_extend_mult. eauto.
Qed.
