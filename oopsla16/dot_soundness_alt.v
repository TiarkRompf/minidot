Require Import dot.

(* :! -- directly invertible value typing *)
Inductive vtp(*possible types*) : nat(*pack count*) -> venv -> id -> ty -> nat(*size*) -> Prop :=
| vtp_top: forall m G1 x n1,
    x < length G1 ->
    vtp m G1 x TTop (S n1)
| vtp_mem: forall m G1 x l ds TX T1 T2 n1 n2,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] G1 T1 TX n1 ->
    stp [] G1 TX T2 n2 ->
    vtp m G1 x (TMem l T1 T2) (S (n1+n2))
| vtp_fun: forall m G1 x l ds dsx OT1 OT2 OT1x OT2x T1 T2 T3 T4 T2' T4' t T1x T2x tx T' T2x' n1 n2 n3 n4,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dfun OT1 OT2 t) ->
    eq_some OT1 T1 ->
    eq_some OT2 T2 ->
    subst_dms x dsx = ds ->
    dms_has_type [T'] G1 dsx T' n4 ->
    subst_dm x (dfun OT1x OT2x tx) = (dfun OT1 OT2 t) ->
    eq_some OT1x T1x ->
    eq_some OT2x T2x ->
    substt x T1x = T1 ->
    substt x T2x = T2 ->
    T2x' = (open 0 (TVar false 1) T2x) ->
    has_type [T1x;T'] G1 tx T2x' n3 ->
    stp [] G1 T3 T1 n1 ->
    T2' = (open 0 (TVar false 0) T2) ->
    T4' = (open 0 (TVar false 0) T4) ->
    closed 0 (length G1) 1 T2 ->
    closed 0 (length G1) 1 T4 ->
    stp [T3] G1 T2' T4' n2 ->
    vtp m G1 x (TFun l T3 T4) (S (n1+n2+n3+n4))
| vtp_bind: forall m G1 x T2 n1,
    vtp m G1 x (open 0 (TVar true x) T2) n1 ->
    closed 0 (length G1) 1 T2 ->
    vtp (S m) G1 x (TBind T2) (S (n1))
| vtp_sel: forall m G1 x y l ds TX n1,
    index y G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    vtp m G1 x TX n1 ->
    vtp m G1 x (TSel (TVar true y) l) (S (n1))
| vtp_and: forall m m1 m2 G1 x T1 T2 n1 n2,
    vtp m1 G1 x T1 n1 ->
    vtp m2 G1 x T2 n2 ->
    m1 <= m -> m2 <= m ->
    vtp m G1 x (TAnd T1 T2) (S (n1+n2))
| vtp_or1: forall m m1 m2 G1 x T1 T2 n1,
    vtp m1 G1 x T1 n1 ->
    closed 0 (length G1) 0 T2 ->
    m1 <= m -> m2 <= m ->
    vtp m G1 x (TOr T1 T2) (S (n1))
| vtp_or2: forall m m1 m2 G1 x T1 T2 n1,
    vtp m1 G1 x T2 n1 ->
    closed 0 (length G1) 0 T1 ->
    m1 <= m -> m2 <= m ->
    vtp m G1 x (TOr T1 T2) (S (n1))
.

Definition vtpd m G1 x T1 := exists n, vtp m G1 x T1 n.

Definition vtpdd m G1 x T1 := exists m1 n, vtp m1 G1 x T1 n /\ m1 <= m.

Hint Constructors vtp.

Ltac euv := match goal with
             | H: vtpd _ _ _ _ |- _ => destruct H as [? H]
             | H: vtpdd _ _ _ _ |- _ => destruct H as [? [? [H ?]]]
            end.

Hint Unfold vtpd.
Hint Unfold vtpdd.

Lemma vtp_all_extend: forall ni,
  (forall m v1 x G1 T2 n,
     vtp m G1 x T2 n -> n < ni ->
     vtp m (v1::G1) x T2 n).
Proof.
  intros n. induction n. repeat split; intros; omega.
  intros; inversion H.
  (* vtp *)
  - econstructor. simpl. eauto.
  - econstructor. eapply index_extend. eauto. eauto. eapply stp_extend. eauto. eapply stp_extend. eauto.
  - econstructor. eapply index_extend. eauto. eauto. eauto. eauto. eauto.
    eapply dms_has_type_extend. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eapply has_type_extend. eauto. eapply stp_extend. eauto. eauto. eauto.
    eapply closed_extend. eauto. eapply closed_extend. eauto. eapply stp_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - econstructor. eapply index_extend. eauto. eauto. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eauto. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply closed_extend. eauto. omega. eauto.
  - eapply vtp_or2. eapply IHn. eauto. omega. eapply closed_extend. eauto. omega. eauto.
Qed.

Lemma vtp_all_closed: forall ni,
  (forall m x G1 T2 n,
     vtp m G1 x T2 n -> n < ni ->
     x < length G1) /\
  (forall m x G1 T2 n,
     vtp m G1 x T2 n -> n < ni ->
     closed 0 (length G1) 0 T2).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H; destruct IHn as [IHV1 IHV2].
  (* vtp left *)
  - eauto.
  - eapply index_max. eauto.
  - eapply index_max. eauto.
  - eapply IHV1. eauto. omega.
  - eapply IHV1. eauto. omega.
  - eapply IHV1. eauto. omega.
  - eapply IHV1. eauto. omega.
  - eapply IHV1. eauto. omega.
  (* vtp right *)
  - econstructor.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply stp_closed1. eauto. eapply stp_closed2. eauto.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply stp_closed1. eauto. eauto.
  - econstructor. eauto.
  - econstructor. econstructor. eapply index_max. eauto.
  - econstructor. eapply IHV2. eauto. omega. eapply IHV2. eauto. omega.
  - econstructor. eapply IHV2. eauto. omega. eauto.
  - econstructor. eauto. eapply IHV2. eauto. omega.
Qed.

Lemma vtp_extend : forall m v1 x G1 T2 n,
                      vtp m G1 x T2 n ->
                      vtp m (v1::G1) x T2 n.
Proof. intros. eapply vtp_all_extend. eauto. eauto. Qed.

Lemma vtp_closed: forall m G1 x T2 n1,
  vtp m G1 x T2 n1 ->
  closed 0 (length G1) 0 T2.
Proof. intros. eapply vtp_all_closed. eauto. eauto. Qed.

Lemma vtp_closed1: forall m G1 x T2 n1,
  vtp m G1 x T2 n1 ->
  x < length G1.
Proof. intros. eapply vtp_all_closed. eauto. eauto. Qed.

Lemma stp_subst_narrow0: forall n, forall GH G1 T1 T2 TX x n2,
   stp (GH++[TX]) G1 T1 T2 n2 -> x < length G1 -> n2 < n ->
   (forall GH (T3 : ty) (n1 : nat),
      htp (GH++[TX]) G1 0 T3 n1 -> n1 < n ->
      exists m2, vtpd m2 G1 x (substt x T3)) ->
   stpd (map (substt x) GH) G1 (substt x T1) (substt x T2).
Proof.
  intros n. induction n. intros. omega.
  intros ? ? ? ? ? ? ? ? ? ? narrowX.

  (* helper lemma for htp *)
  assert (forall ni n2, forall GH T2 xi,
    htp (GH ++ [TX]) G1 xi T2 n2 -> xi <> 0 -> n2 < ni -> ni < S n ->
    htpd (map (substt x) GH) G1 (xi-1) (substt x T2)) as htp_subst_narrow02. {
      induction ni. intros. omega.
      intros. inversion H2.
      + (* var *) subst.
        repeat eexists. eapply htp_var. eapply index_subst1. eauto. eauto.
        eapply closed_subst0. eapply closed_upgrade_gh. eauto. omega. eauto.
      + (* bind *) subst.
        assert (htpd (map (substt x) (GH0)) G1 (xi-1) (substt x (TBind TX0))) as BB.
        eapply IHni. eapply H6. eauto. omega. omega.
        rewrite subst_open5.
        eu. repeat eexists. eapply htp_unpack. eauto.
        eapply closed_upgrade_gh. eapply closed_subst1. eauto. eauto. eauto. omega.
        apply []. eauto.
      + (* sub *) subst.
        assert (exists GL0, GL = GL0 ++ [TX] /\ GH0 = GU ++ GL0) as A. eapply gh_match1. eauto. omega.
        destruct A as [GL0 [? ?]]. subst GL.
        assert (htpd (map (substt x) GH0) G1 (xi-1) (substt x T3)) as AA.
        eapply IHni. eauto. eauto. omega. omega.
        assert (stpd (map (substt x) GL0) G1 (substt x T3) (substt x T0)) as BB.
        eapply IHn. eauto. eauto. omega. { intros. eapply narrowX. eauto. eauto. }
        eu. eu. repeat eexists. eapply htp_sub. eauto. eauto.
        (* - *)
        rewrite map_length. rewrite app_length in H8. simpl in H8. unfold id in *. omega.
        subst GH0. rewrite map_app. eauto.
  }
  (* special case *)
  assert (forall ni n2, forall T0 T2,
    htp (T0 :: GH ++ [TX]) G1 (length (GH ++ [TX])) T2 n2 -> n2 < ni -> ni < S n ->
    htpd (map (substt x) (T0::GH)) G1 (length GH) (substt x T2)) as htp_subst_narrow0. {
      intros.
      rewrite app_comm_cons in H2.
      remember (T0::GH) as GH1. remember (length (GH ++ [TX])) as xi.
      rewrite app_length in Heqxi. simpl in Heqxi.
      assert (length GH = xi-1) as R. omega.
      rewrite R. eapply htp_subst_narrow02. eauto. omega. eauto. eauto.
  }


  (* main logic *)
  inversion H.
  - Case "bot". subst.
    eapply stpd_bot; eauto. rewrite map_length. simpl. eapply closed_subst0.
    rewrite app_length in H2. simpl in H2. eapply H2. eauto.
  - Case "top". subst.
    eapply stpd_top; eauto. rewrite map_length. simpl. eapply closed_subst0.
    rewrite app_length in H2. simpl in H2. eapply H2. eauto.
  - Case "fun". subst.
    eapply stpd_fun. eauto. eauto.
    rewrite map_length. eapply closed_subst0. rewrite app_length in *. simpl in *. eauto. omega.
    rewrite map_length. eapply closed_subst0. rewrite app_length in *. simpl in *. eauto. omega.
    eapply IHn; eauto. omega.
    rewrite <- subst_open_commute_z. rewrite <- subst_open_commute_z.
    specialize (IHn (T4::GH)). simpl in IHn.
    unfold substt in IHn at 2.  unfold substt in IHn at 3. unfold substt in IHn at 3.
    simpl in IHn. eapply IHn.
    rewrite map_length. rewrite app_length in *. eassumption.
    omega. omega. eauto.
  - Case "mem". subst.
    eapply stpd_mem. eapply IHn; eauto. omega. eapply IHn; eauto. omega.


  - Case "varx". subst.
    eexists. eapply stp_varx. eauto.
  - Case "varax". subst.
    case_eq (beq_nat x0 0); intros E.
    + (* hit *)
      assert (x0 = 0). eapply beq_nat_true_iff. eauto.
      repeat eexists. unfold substt. subst x0. simpl. eapply stp_varx. eauto.
    + (* miss *)
      assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      repeat eexists. unfold substt. simpl. rewrite E.
      eapply stp_varax. rewrite map_length. rewrite app_length in H2. simpl in H2. omega.
  - Case "ssel1". subst.
    assert (substt x T2 = T2) as R. eapply subst_closed_id. eapply stpd_closed2 with (GH:=[]). eauto.
    eexists. eapply stp_strong_sel1. eauto. eauto. rewrite R. eauto.

  - Case "ssel2". subst.
    assert (substt x T1 = T1) as R. eapply subst_closed_id. eapply stpd_closed1 with (GH:=[]). eauto.
    eexists. eapply stp_strong_sel2. eauto. eauto. rewrite R. eauto.

  - Case "sel1". subst. (* invert htp to vtp and create strong_sel node *)
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0.
      assert (exists m0, vtpd m0 G1 x (substt x (TMem l TBot T2))) as A. eapply narrowX. eauto. omega.
      destruct A as [? A]. euv. inversion A. subst.
      repeat eexists. eapply stp_strong_sel1. eauto. eauto. unfold substt.
      eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      eapply htp_subst_narrow02 in H2.
      eu. repeat eexists. unfold substt. simpl. rewrite E. eapply stp_sel1. eapply H2. eauto. eauto. eauto.

  - Case "sel2". subst. (* invert htp to vtp and create strong_sel node *)
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0.
      assert (exists m0, vtpd m0 G1 x (substt x (TMem l T1 TTop))) as A. eapply narrowX. eauto. omega.
      destruct A as [? A]. euv. inversion A. subst.
      repeat eexists. eapply stp_strong_sel2. eauto. eauto. unfold substt.
      eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      eapply htp_subst_narrow02 in H2.
      eu. repeat eexists. unfold substt. simpl. rewrite E. eapply stp_sel2. eapply H2. eauto. eauto. eauto.
  - Case "selx".
    eexists. eapply stp_selx. eapply closed_subst0. rewrite app_length in H2. simpl in H2. rewrite map_length. eauto. eauto.

  - Case "bind1".
    assert (stpd (map (substt x) (T1'::GH)) G1 (substt x T1') (substt x T2)) as A.
    eapply IHn; eauto. omega.
    eu. repeat eexists. eapply stp_bind1. eapply A.
    simpl. subst T1'. fold subst. eapply subst_open4.
    fold subst. eapply closed_subst0. rewrite app_length in H4. simpl in H4. rewrite map_length. eauto. eauto.
    eapply closed_subst0. rewrite map_length. rewrite app_length in H5. simpl in H5. eauto. eauto.

  - Case "bindx".
    assert (stpd (map (substt x) (T1'::GH)) G1 (substt x T1') (substt x T2')) as A.
    eapply IHn; eauto. omega.
    eu. repeat eexists. eapply stp_bindx. eapply A.
    subst T1'. fold subst. eapply subst_open4.
    subst T2'. fold subst. eapply subst_open4.
    rewrite app_length in H5. simpl in H5. eauto. eapply closed_subst0. rewrite map_length. eauto. eauto.
    rewrite app_length in H6. simpl in H6. eauto. eapply closed_subst0. rewrite map_length. eauto. eauto.

  - Case "and11".
    assert (stpd (map (substt x) GH) G1 (substt x T0) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_and11. eauto. eapply closed_subst0. rewrite app_length in H3. rewrite map_length. eauto. eauto.
  - Case "and12".
    assert (stpd (map (substt x) GH) G1 (substt x T3) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_and12. eauto. eapply closed_subst0. rewrite app_length in H3. rewrite map_length. eauto. eauto.
  - Case "and2".
    assert (stpd (map (substt x) GH) G1 (substt x T1) (substt x T0)). eapply IHn. eauto. eauto. omega. eauto.
    assert (stpd (map (substt x) GH) G1 (substt x T1) (substt x T3)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eu. eexists. eapply stp_and2. eauto. eauto.

  - Case "or21".
    assert (stpd (map (substt x) GH) G1 (substt x T1) (substt x T0)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_or21. eauto. eapply closed_subst0. rewrite app_length in H3. rewrite map_length. eauto. eauto.
  - Case "or22".
    assert (stpd (map (substt x) GH) G1 (substt x T1) (substt x T3)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_or22. eauto. eapply closed_subst0. rewrite app_length in H3. rewrite map_length. eauto. eauto.
  - Case "or1".
    assert (stpd (map (substt x) GH) G1 (substt x T0) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    assert (stpd (map (substt x) GH) G1 (substt x T3) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eu. eexists. eapply stp_or1. eauto. eauto.

  - Case "trans".
    assert (stpd (map (substt x) GH) G1 (substt x T1) (substt x T3)).
    eapply IHn; eauto. omega.
    assert (stpd (map (substt x) GH) G1 (substt x T3) (substt x T2)).
    eapply IHn; eauto. omega.
    eu. eu. repeat eexists. eapply stp_trans. eauto. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


Lemma stp_subst_narrowX: forall ml, forall nl, forall m GH G1 T2 TX x n1 n2,
   vtp m G1 x (substt x TX) n1 ->
   htp (GH++[TX]) G1 0 T2 n2 -> x < length G1 -> m < ml -> n2 < nl ->
   (forall (m0 : nat) (G1 : venv) x (T2 T3 : ty) (n1 n2 : nat),
        vtp m0 G1 x (substt x T2) n1 ->
        stp [] G1 (substt x T2) (substt x T3) n2 -> m0 <= m ->
        vtpdd m0 G1 x (substt x T3)) ->
   vtpdd m G1 x (substt x T2). (* decrease b/c transitivity *)
Proof.
  intros ml. (* induction ml. intros. omega. *)
  intros nl. induction nl. intros. omega.
  intros.
  inversion H0.
  - Case "var". subst.
    assert (T2 = TX). eapply index_hit0. eauto.
    subst T2.
    repeat eexists. eauto. eauto.
  - Case "unpack". subst.
    assert (vtpdd m G1 x (substt x (TBind TX0))) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    destruct A as [? [? [A ?]]]. inversion A. subst.
    rewrite subst_open_commute0b. repeat eexists. eauto. omega.
  - Case "sub". subst.
    destruct GL.

    assert (vtpdd m G1 x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    euv.
    assert (stpd [] G1 (substt x T1) (substt x T2)) as B.
    erewrite subst_closed_id. erewrite subst_closed_id. eexists. eassumption.
    eapply stp_closed2 in H6. simpl in H6. eapply H6.
    eapply stp_closed1 in H6. simpl in H6. eapply H6.
    simpl in B. eu.
    assert (vtpdd x0 G1 x (substt x T2)).
    eapply H4. eauto. eauto. eauto.
    euv. repeat eexists. eauto. omega.

    assert (length GL = 0) as LenGL. simpl in *. omega.
    assert (GL = []). destruct GL. reflexivity. simpl in LenGL. inversion LenGL.
    subst GL.
    assert (TX = t). eapply proj2. apply app_inj_tail. eassumption.
    subst t.
    assert (vtpdd m G1 x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    euv.
    assert (stpd (map (substt x) []) G1 (substt x T1) (substt x T2)) as B.
    eapply stp_subst_narrow0. eauto. eauto. eauto. {
      intros. eapply IHnl in H. euv. repeat eexists. eauto. eauto. eauto. eauto. omega. eauto.
    }
    simpl in B. eu.
    assert (vtpdd x0 G1 x (substt x T2)).
    eapply H4. eauto. eauto. eauto.
    euv. repeat eexists. eauto. omega.
Qed.

(* possible types closure *)
Lemma vtp_widen: forall l, forall n, forall k, forall m1 G1 x T2 T3 n1 n2,
  vtp m1 G1 x T2 n1 ->
  stp [] G1 T2 T3 n2 ->
  m1 < l -> n2 < n -> n1 < k ->
  vtpdd m1 G1 x T3.
Proof.
  intros l. induction l. intros. solve by inversion.
  intros n. induction n. intros. solve by inversion.
  intros k. induction k; intros. solve by inversion.
  inversion H.
  - Case "top". inversion H0; subst; invty.
    + SCase "top". repeat eexists; eauto.
    + SCase "ssel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      euv. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H9. omega.
    + SCase "and".
      assert (vtpdd m1 G1 x T1). eapply IHn; eauto. omega. euv.
      assert (vtpdd m1 G1 x T0). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T1). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T0). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T0) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. euv.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. euv.
      repeat eexists. eauto. omega.
  - Case "mem". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply index_max. eauto. eauto.
    + SCase "mem". invty. subst.
      repeat eexists. eapply vtp_mem. eauto. eauto.
      eapply stp_trans. eauto. eauto.
      eapply stp_trans. eauto. eauto.
      eauto.
    + SCase "sel2".
      assert (vtpdd m1 G1 x TX0). eapply IHn; eauto. omega.
      euv. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and".
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. euv.
      assert (vtpdd m1 G1 x T5). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T5). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T5) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. euv.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. euv.
      repeat eexists. eauto. omega.
  - Case "fun". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply index_max. eauto. eauto.
    + SCase "fun". invty. subst.
      remember (substt x T2x) as T0.
      assert (stpd [T8] G1 (open 0 (TVar false 0) T0) (open 0 (TVar false 0) T5)) as A. {
        eapply stp_narrow_norec. simpl. eassumption. simpl. eassumption.
      }
      destruct A as [na A].
      repeat eexists. eapply vtp_fun. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      eauto. eauto. eauto. eauto. eauto. eauto.
      eapply stp_trans. eauto. eauto. eauto. eauto. eauto. eauto. eauto. reflexivity.
    + SCase "sel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      euv. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. subst. inversion H18. omega.
    + SCase "and".
      assert (vtpdd m1 G1 x T6). eapply IHn; eauto. omega. euv.
      assert (vtpdd m1 G1 x T7). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T6). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T7). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T7) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. euv.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. euv.
      repeat eexists. eauto. omega.
  - Case "bind".
    inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto.
    + SCase "sel2".
      assert (vtpdd (S m) G1 x TX). eapply IHn; eauto. omega.
      euv. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H10. omega.
    + SCase "bind1".
      invty. subst.
      remember (TVar false (length [])) as VZ.
      remember (TVar true x) as VX.

      (* left *)
      assert (vtpd m G1 x (open 0 VX T0)) as LHS. eexists. eassumption.
      euv.
      (* right *)
      assert (substt x (open 0 VZ T0) = (open 0 VX T0)) as R. unfold substt. subst. eapply subst_open_commute0. eauto.
      assert (substt x T3 = T3) as R1. eapply subst_closed_id. eauto.

      assert (vtpdd m G1 x (substt x T3)) as BB. {
        eapply stp_subst_narrowX. rewrite <-R in LHS. eapply LHS.
        instantiate (2:=nil). simpl.
        eapply htp_sub. eapply htp_var. simpl. reflexivity.
        eapply stp_closed1 in H11. simpl in H11. eapply H11. eapply H11. eauto.
        instantiate (1:=nil). simpl. reflexivity. eapply vtp_closed1. eauto. eauto. eauto.
        { intros. eapply IHl. eauto. eauto. omega. eauto. eauto. }
      }
      rewrite R1 in BB.
      euv. repeat eexists. eauto. omega.
    + SCase "bindx".
      invty. subst.
      remember (TVar false (length [])) as VZ.
      remember (TVar true x) as VX.

      (* left *)
      assert (vtpd m G1 x (open 0 VX T0)) as LHS. eexists. eassumption.
      euv.
      (* right *)
      assert (substt x (open 0 VZ T0) = (open 0 VX T0)) as R. unfold substt. subst. eapply subst_open_commute0. eauto.

      assert (vtpdd m G1 x (substt x (open 0 VZ T4))) as BB. {
        eapply stp_subst_narrowX. rewrite <-R in LHS. eapply LHS.
        instantiate (2:=nil). simpl.
        eapply htp_sub. eapply htp_var. simpl. reflexivity.
        eapply stp_closed1 in H11. simpl in H11. eapply H11. eapply H11. eauto.
        instantiate (1:=nil). simpl. reflexivity. eapply vtp_closed1. eauto. eauto. eauto.
        { intros. eapply IHl. eauto. eauto. omega. eauto. eauto. }
      }
      unfold substt in BB. subst. erewrite subst_open_commute0 in BB.
      clear R.
      euv. repeat eexists. eapply vtp_bind. eauto. eauto. omega. eauto. (* enough slack to add bind back *)
    + SCase "and".
      assert (vtpdd (S m) G1 x T1). eapply IHn; eauto. omega. euv.
      assert (vtpdd (S m) G1 x T4). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd (S m) G1 x T1). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd (S m) G1 x T4). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd (S m) G1 x T4) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. euv.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. euv.
      repeat eexists. eauto. omega.
  - Case "ssel2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto.
    + SCase "ssel1". index_subst. index_subst. eapply IHn. eapply H6. eauto. eauto. omega. eauto.
    + SCase "ssel2".
      assert (vtpdd m1 G1 x TX0). eapply IHn; eauto. omega.
      euv. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel1".
      assert (closed (length ([]:tenv)) (length G1) 0 (TSel (TVar false x0) l1)) as A.
      eapply stpd_closed2. eauto.
      simpl in A. inversion A. inversion H12. omega.
    + SCase "selx".
      eauto.
    + SCase "and".
      assert (vtpdd m1 G1 x T1). eapply IHn; eauto. omega. euv.
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T1). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T2) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. euv.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. euv.
      repeat eexists. eauto. omega.
  - Case "and". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto.
    + SCase "sel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      euv. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H13. omega.
    + SCase "and11". eapply IHn in H4. euv. repeat eexists. eauto. omega. eauto. omega. omega. eauto.
    + SCase "and12". eapply IHn in H5. euv. repeat eexists. eauto. omega. eauto. omega. omega. eauto.
    + SCase "and".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. euv.
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T4) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. euv.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. euv.
      repeat eexists. eauto. omega.

  - Case "or1". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto.
    + SCase "sel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      euv. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H13. omega.
    + SCase "and".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. euv.
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "or...".
      eapply IHn in H4. euv.
      repeat eexists. eapply H4. omega. eauto. omega. omega. eauto.
    + SCase "or...".
      assert (vtpdd m1 G1 x T4) as A. eapply IHn. eapply H. eauto. omega. omega. eauto. euv.
      eapply IHn in A. euv.
      repeat eexists. eauto. omega. eauto. omega. omega. eauto.

  - Case "or2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto.
    + SCase "sel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      euv. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H13. omega.
    + SCase "and".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. euv.
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. euv.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "or...".
      eapply IHn in H4. euv.
      repeat eexists. eapply H4. omega. eauto. omega. omega. eauto.
    + SCase "or...".
      assert (vtpdd m1 G1 x T4) as A. eapply IHn. eapply H. eauto. omega. omega. eauto. euv.
      eapply IHn in A. euv.
      repeat eexists. eauto. omega. eauto. omega. omega. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stp_subst_narrow_z: forall GH0 TX G1 T1 T2 x m n1 n2,
  stp (GH0 ++ [TX]) G1 T1 T2 n2 ->
  vtp m G1 x (substt x TX) n1 ->
  stpd (map (substt x) GH0) G1 (substt x T1) (substt x T2).
Proof.
  intros.
  edestruct stp_subst_narrow0. eauto. eapply vtp_closed1. eauto. eauto.
  { intros. edestruct stp_subst_narrowX. eauto. eauto.
    eapply vtp_closed1. eauto. eauto. eauto.
    { intros. eapply vtp_widen; eauto. }
    ev. repeat eexists. eauto.
  }
  eexists. eassumption.
Qed.

Lemma dms_hastp_inv: forall G1 x ds' T' n,
  dms_has_type [T'] G1 ds' T' n ->
  closed 0 (length G1) 0 (substt x T') ->
  index x G1 = Some (vobj (subst_dms x ds')) ->
  exists m n, vtp m G1 x (substt x T') n.
Proof.
  intros G1 x ds' T' n H HC HI.
  remember T' as T0. remember H as HT0. clear HeqHT0.
  rewrite HeqT0 in H at 2. rewrite HeqT0. rewrite HeqT0 in HC. clear HeqT0.
  remember ds' as ds0. rewrite Heqds0 in H.
  assert (exists dsa, dms_to_list ds0 = dsa ++ dms_to_list ds') as Hds. {
    exists []. rewrite app_nil_l. subst. reflexivity.
  }
  clear Heqds0.
  remember n as n0. rewrite Heqn0 in *. rewrite <- Heqn0 in HT0. clear Heqn0.
  remember [T0] as GH. generalize dependent T0.
  induction H; intros.
  - repeat eexists. eapply vtp_top. eapply index_max. eauto.
  - subst.
    assert (closed 0 (length G1) 0 (substt x TS)) as HCS. {
      unfold substt in *. simpl in HC. inversion HC; subst.
      eauto.
    }
    assert (closed 0 (length G1) 0 (substt x T11)) as HC11. {
      unfold substt in *. simpl in HC. inversion HC; subst.
      inversion H6; subst. eauto.
    }
    assert (stpd [] G1 (substt x T11) (substt x T11)) as A. {
      eapply stpd_refl. eauto.
    }
    eu.
    destruct Hds as [dsa Hdsa]. simpl in Hdsa.
    edestruct IHdms_has_type as [? [? AS]]. eauto. eauto. eauto.
    exists (dsa ++ [dty T11]). rewrite <- app_assoc. simpl. eauto. eauto. eauto.
    unfold substt in *. simpl.
    repeat eexists. eapply vtp_and. eapply vtp_mem. eauto.
    erewrite index_subst_dms with (D:=dty T11). simpl. reflexivity. eauto.
    eauto. eauto. eauto. eauto. eauto.
  - subst.
    assert (closed 0 (length G1) 0 (substt x TS)) as HCS. {
      unfold substt in *. simpl in HC. inversion HC; subst.
      eauto.
    }
    assert (closed 0 (length G1) 0 (substt x T11)) as HC11. {
      unfold substt in *. simpl in HC. inversion HC; subst.
      inversion H10; subst. eauto.
    }
    assert (closed 1 (length G1) 0 (open 0 (TVar false 0) (substt x T12))) as HC12. {
      unfold substt in *. simpl in HC. inversion HC; subst. inversion H10; subst.
      eapply closed_open. eapply closed_upgrade_gh. eauto. omega.
      econstructor. omega.
    }
    assert (stpd [] G1 (substt x T11) (substt x T11)) as A. {
      eapply stpd_refl. eauto.
    }
    eu.
    assert (stpd [(substt x T11)] G1 (open 0 (TVar false 0) (substt x T12)) (open 0 (TVar false 0) (substt x T12))) as B. {
      eapply stpd_refl. eauto.
    }
    eu.
    destruct Hds as [dsa Hdsa]. simpl in Hdsa.
    edestruct IHdms_has_type as [? [? AS]]. eauto. eauto. eauto.
    exists (dsa ++ [dfun OT11 OT12 t12]). rewrite <- app_assoc. simpl. eauto. eauto. eauto.
    unfold substt in *. simpl.
    repeat eexists. eapply vtp_and. eapply vtp_fun. eauto.
    erewrite index_subst_dms with (D:=dfun OT11 OT12 t12). simpl. reflexivity. eauto.
    eapply subst_eq_some; eauto. eapply subst_eq_some; eauto.
    eauto. eapply HT0. simpl. reflexivity. eauto. eauto. eauto. eauto. eauto.
    eauto. eauto. eauto. eauto.
    eapply closed_subst. eauto. econstructor. eapply index_max. eauto.
    eapply closed_subst. eauto. econstructor. eapply index_max. eauto.
    eauto. eauto. eauto. eauto.
Grab Existential Variables.
apply 0. apply 0.
Qed.

Lemma hastp_inv: forall G1 x T n1,
  has_type [] G1 (tvar true x) T n1 ->
  exists m n1, vtp m G1 x T n1.
Proof.
  intros. remember [] as GH. remember (tvar true x) as t.
  induction H; subst; try inversion Heqt.
  - Case "var". subst. eapply dms_hastp_inv; eauto.
  - Case "pack". subst.
    destruct IHhas_type. eauto. eauto. ev.
    repeat eexists. eapply vtp_bind. eauto. eauto.
  - Case "unpack". subst.
    destruct IHhas_type. eauto. eauto. ev. inversion H0.
    repeat eexists. eauto.
  - Case "sub".
    destruct IHhas_type. eauto. eauto. ev.
    assert (exists m0, vtpdd m0 G1 x T2). eexists. eapply vtp_widen; eauto.
    ev. euv. repeat eexists. eauto.
Qed.

Lemma stp_subst_narrow: forall GH0 TX G1 T1 T2 x m n1 n2,
  stp (GH0 ++ [TX]) G1 T1 T2 n2 ->
  vtp m G1 x TX n1 ->
  stpd (map (substt x) GH0) G1 (substt x T1) (substt x T2).
Proof.
  intros. eapply stp_subst_narrow_z. eauto.
  erewrite subst_closed_id. eauto. eapply vtp_closed in H0. eauto.
Qed.


Lemma hastp_subst_aux_z: forall ni, (forall G1 GH TX T x t n1 n2,
  has_type (GH++[TX]) G1 t T n2 -> n2 < ni ->
  has_type [] G1 (tvar true x) (substt x TX) n1 ->
  exists n3, has_type (map (substt x) GH) G1 (subst_tm x t) (substt x T) n3) /\
  (forall G1 GH TX T x ds n1 n2,
  dms_has_type (GH++[TX]) G1 ds T n2 -> n2 < ni ->
  has_type [] G1 (tvar true x) (substt x TX) n1 ->
  exists n3, dms_has_type (map (substt x) GH) G1 (subst_dms x ds) (substt x T) n3).
Proof.
  intro ni. induction ni. split; intros; omega. destruct IHni as [IHniT IHniD].
  split;
  intros; remember (GH++[TX]) as GH0; revert GH HeqGH0; inversion H; intros.
  - Case "vary".
    assert (substt x T = T) as EqT. {
      erewrite subst_closed_id. reflexivity. eauto.
    }
    subst. simpl. eexists. eapply T_Vary. eauto. eauto. eauto.
    rewrite EqT. reflexivity. rewrite EqT. eauto.
  - Case "varz". subst. simpl.
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0.
      eapply index_hit0 in H2. subst.
      eapply hastp_upgrade_gh. eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff; eauto.
      eexists. eapply T_Varz. eapply index_subst1. eauto. eauto.
      rewrite map_length. eapply closed_subst0.
      rewrite app_length in H3. simpl in H3. eapply H3. eapply has_type_closed1. eauto.
  - Case "pack". subst. simpl.
    edestruct IHniT as [? IH]. eauto. omega. eauto.
    assert (substt x (TBind T1) = (TBind (substt x T1))) as A. {
      eauto.
    }
    rewrite A.
    destruct b.
    + eexists. eapply T_VarPack. eapply IH.
      unfold substt. rewrite subst_open_commute1. reflexivity.
      rewrite map_length. eapply closed_subst0. rewrite app_length in H4. simpl in H4.
      apply H4. eapply has_type_closed1. eauto.
    + case_eq (beq_nat x0 0); intros E.
      * assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0.
        simpl in IH.
        eexists. eapply T_VarPack. eapply IH. rewrite subst_open_commute0b. eauto.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4. simpl in H4.
        eapply H4. econstructor. eapply has_type_closed1. eauto.
      * assert (x0 <> 0). eapply beq_nat_false_iff; eauto.
        simpl in IH. rewrite E in IH.
        eexists. eapply T_VarPack. eapply IH.
        remember (x0 - 1) as z.
        assert (x0 = z + 1) as B. {
          intuition. destruct x0. specialize (H3 eq_refl). inversion H3.
          subst. simpl. rewrite <- minus_n_O. rewrite NPeano.Nat.add_1_r.
          reflexivity.
        }
        rewrite B. unfold substt.
        rewrite subst_open_commute_z. reflexivity.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4.
        simpl in H4. eapply H4.
        econstructor. eapply has_type_closed1. eauto.
  - Case "unpack". subst. simpl.
    edestruct IHniT as [? IH]. eapply H2. omega. eauto.
    assert (substt x (TBind T1) = (TBind (substt x T1))) as A. {
      eauto.
    }
    rewrite A in IH.
    destruct b.
    + eexists. eapply T_VarUnpack. eapply IH.
      unfold substt. rewrite subst_open_commute1. reflexivity.
      rewrite map_length. eapply closed_subst0. rewrite app_length in H4. simpl in H4.
      apply H4. eapply has_type_closed1. eauto.
    + case_eq (beq_nat x0 0); intros E.
      * assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0.
        simpl in IH.
        eexists. eapply T_VarUnpack. eapply IH. rewrite subst_open_commute0b. eauto.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4. simpl in H4.
        eapply H4. econstructor. eapply has_type_closed1. eauto.
      * assert (x0 <> 0). eapply beq_nat_false_iff; eauto.
        simpl in IH. rewrite E in IH.
        eexists. eapply T_VarUnpack. eapply IH.
        remember (x0 - 1) as z.
        assert (x0 = z + 1) as B. {
          intuition. destruct x0. specialize (H3 eq_refl). inversion H3.
          subst. simpl. rewrite <- minus_n_O. rewrite NPeano.Nat.add_1_r.
          reflexivity.
        }
        rewrite B. unfold substt.
        rewrite subst_open_commute_z. reflexivity.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4.
        simpl in H4. eapply H4.
        econstructor. eapply has_type_closed1. eauto.
  - Case "obj".
    edestruct IHniD with (GH:=T'::GH1) as [? IH]. subst. eauto. omega. subst. eauto.
    subst. simpl.
    eexists. eapply T_Obj. eauto.
    rewrite app_length. simpl. unfold substt. rewrite subst_open_commute_z.
    rewrite map_length. eauto.
    eapply closed_subst. rewrite app_length in *. simpl in *. rewrite map_length. eauto.
    econstructor. eapply has_type_closed1. eauto.
  - Case "app". subst. simpl.
    edestruct IHniT as [? IH1]. eapply H2. omega. eauto.
    edestruct IHniT as [? IH2]. eapply H3. omega. eauto.
    eexists. eapply T_App. eauto. eauto. eapply closed_subst.
    subst. rewrite map_length. rewrite app_length in *. simpl in *. eauto.
    subst. rewrite map_length. econstructor. eapply has_type_closed1. eauto.
  - Case "appvar". subst. simpl.
    edestruct IHniT as [? IH1]. eapply H2. omega. eauto.
    edestruct IHniT as [? IH2]. eapply H3. omega. eauto.
    destruct b2.

    eexists. eapply T_AppVar. eauto. eauto.
    rewrite subst_open_commute1. eauto.
    eapply closed_subst. subst. rewrite map_length. rewrite app_length in *. simpl in *.
    eapply closed_upgrade_gh. eassumption. omega.
    subst. rewrite map_length. econstructor. eapply has_type_closed1. eauto.

    case_eq (beq_nat x2 0); intros E.

    eapply beq_nat_true in E. subst.
    rewrite subst_open_commute0b.
    eexists. eapply T_AppVar. eauto. eauto. eauto.
    rewrite map_length. rewrite <- subst_open_commute0b.
    eapply closed_subst. eapply closed_upgrade_gh. eassumption.
    rewrite app_length. simpl. omega.
    econstructor. eapply has_type_closed1. eauto.

    rewrite subst_open5.
    simpl in *. rewrite E in *.
    eexists. eapply T_AppVar. eauto. eauto. eauto.
    rewrite <- subst_open5. eapply closed_subst.
    subst. rewrite map_length. rewrite app_length in *. simpl in *. eassumption.
    subst. rewrite map_length. econstructor. eapply has_type_closed1. eauto.
    apply []. apply beq_nat_false. apply E. apply []. apply beq_nat_false. apply E.
  - Case "sub". subst.
    edestruct hastp_inv as [? [? HV]]; eauto.
    edestruct stp_subst_narrow_z. eapply H3. eapply HV.
    edestruct IHniT as [? IH]. eapply H2. omega. eauto.
    eexists. eapply T_Sub. eauto. eauto.
  - Case "dnil". subst. simpl.
    eexists. eapply D_Nil.
  - Case "mem". subst. simpl.
    edestruct IHniD as [? IH]. eapply H2. omega. eauto.
    eexists. eapply D_Mem. eauto. eapply closed_subst0.
    rewrite app_length in H3. rewrite map_length. eauto.
    eapply has_type_closed1. eauto. eauto.
    unfold substt. simpl. rewrite <- length_subst_dms. reflexivity.
  - Case "abs". subst. simpl.
    edestruct IHniD as [? IHD]. eapply H2. omega. eauto.
    edestruct IHniT with (GH:=T11::GH1) as [? HI] . eauto. omega. eauto.
    simpl in HI.
    eexists. eapply D_Fun. eapply IHD. eapply HI.
    rewrite map_length. rewrite app_length. simpl.
    rewrite subst_open. unfold substt. reflexivity.
    eapply closed_subst0. rewrite map_length.
    rewrite app_length in H5. simpl in H5. eauto. eauto.
    eapply has_type_closed1. eauto.
    eapply closed_subst0. rewrite map_length.
    rewrite app_length in H6. simpl in H6. eauto.
    eapply has_type_closed1. eauto. eauto.
    unfold substt. simpl. rewrite <- length_subst_dms. reflexivity.
    eapply subst_eq_some; eauto. eapply subst_eq_some; eauto.
Grab Existential Variables.
apply 0. apply 0.
Qed.

Lemma hastp_subst_z: forall G1 GH TX T x t n1 n2,
  has_type (GH++[TX]) G1 t T n2 ->
  has_type [] G1 (tvar true x) (substt x TX) n1 ->
  exists n3, has_type (map (substt x) GH) G1 (subst_tm x t) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_aux_z with (t:=t). eauto. eauto. eauto.
Qed.

Lemma hastp_subst: forall G1 GH TX T x t n1 n2,
  has_type (GH++[TX]) G1 t T n2 ->
  has_type [] G1 (tvar true x) TX n1 ->
  exists n3, has_type (map (substt x) GH) G1 (subst_tm x t) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_z with (t:=t). eauto.
  erewrite subst_closed_id. eauto. eapply has_type_closed in H0. eauto.
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
        assert (exists m n1, vtp m G1 x (TFun l T1 T) n1). eapply hastp_inv. eauto.
        assert (exists m n1, vtp m G1 x0 T1 n1). eapply hastp_inv. eauto.
        ev. inversion H2. subst.
        remember (substt x T1x) as T0. remember (substt x T2x) as T2.
        assert (vtpdd x1 G1 x0 T0). eapply vtp_widen. eauto. eauto. eauto. eauto. eauto.
        euv.
        assert (exists T, (exists n1, has_type [] G1 (tvar true x) T n1) /\ substt x T' = T) as A. {
          eexists. split. eexists. eapply T_Vary. eauto. eauto. eauto. eauto.
          eapply closed_subst. eapply dms_has_type_closed in H12. eauto. econstructor.
          eapply index_max in H7. omega. reflexivity.
        }
        destruct A as [Tx [[na A] EqTx]].
        assert (has_typed (map (substt x) [T1x]) G1 (subst_tm x tx) (substt x (open 0 (TVar false 1) T2x))) as HIx.
        eapply hastp_subst_z. eapply H19. rewrite EqTx. eapply A.
        eu. simpl in HIx.
        assert (has_typed (map (substt x0) []) G1
                          (subst_tm x0 (subst_tm x tx))
                          (substt x0 (substt x (open 0 (TVar false 1) T2x)))) as HIx0. {
          eapply hastp_subst. rewrite app_nil_l. eapply HIx.
          rewrite <- HeqT0. eauto.
        }
        eu. simpl in HIx0.
        assert ((substt x (open 0 (TVar false 1) T2x))=(open 0 (TVar false 0) (substt x T2x))) as EqT2x. {
          change 1 with (0+1). rewrite subst_open. reflexivity.
        }
        assert (has_typed [] G1 (subst_tm x0 t) (substt x0 (open 0 (TVar false 0) T2))) as HI. {
          inversion H13; subst. rewrite <- EqT2x. eexists. eapply HIx0.
        }
        eu. simpl in HI.
        edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H29. eauto.
        simpl in HI2.
        assert (substt x0 (open 0 (TVar false 0) T) = T) as EqT. {
          erewrite <- closed_no_open. erewrite subst_closed_id. reflexivity.
          eassumption. eassumption.
        }
        rewrite EqT in HI2.
        right. repeat eexists. rewrite app_nil_l. eapply ST_AppAbs. eauto. eauto.
        eapply T_Sub. eauto. eauto.
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
      assert (exists m n1, vtp m G1 x (TFun l T1 T2) n1). eapply hastp_inv. eauto.
      assert (exists m n1, vtp m G1 x2 T1 n1). eapply hastp_inv. eauto.
      ev. inversion H1. subst.
      remember (substt x T1x) as T0. remember (substt x T2x) as T3.
      assert (vtpdd x0 G1 x2 T0). eapply vtp_widen. eauto. eauto. eauto. eauto. eauto.
      euv.
      assert (exists T, (exists n1, has_type [] G1 (tvar true x) T n1) /\ substt x T' = T) as A. {
        eexists. split. eexists. eapply T_Vary. eauto. eauto. eauto. eauto.
        eapply closed_subst. eapply dms_has_type_closed in H12. eauto. econstructor.
        eapply index_max in H7. omega. reflexivity.
      }
      destruct A as [Tx [[na A] EqTx]].
      assert (has_typed (map (substt x) [T1x]) G1 (subst_tm x tx) (substt x (open 0 (TVar false 1) T2x))) as HIx.
      eapply hastp_subst_z. eapply H19. rewrite EqTx. eapply A.
      eu. simpl in HIx.
      assert (has_typed (map (substt x2) []) G1
                        (subst_tm x2 (subst_tm x tx))
                        (substt x2 (substt x (open 0 (TVar false 1) T2x)))) as HIx0. {
        eapply hastp_subst. rewrite app_nil_l. eapply HIx.
        rewrite <- HeqT0. eauto.
      }
      eu. simpl in HIx0.
      assert ((substt x (open 0 (TVar false 1) T2x))=(open 0 (TVar false 0) (substt x T2x))) as EqT2x. {
        change 1 with (0+1). rewrite subst_open. reflexivity.
      }
      assert (has_typed [] G1 (subst_tm x2 t) (substt x2 (open 0 (TVar false 0) T3))) as HI. {
        inversion H13; subst. rewrite <- EqT2x. eauto.
      }
      eu. simpl in HI.
      edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H29. eauto.
      simpl in HI2.
      assert ((substt x2 (open 0 (TVar false 0) T2))=(open 0 (TVar true x2) T2)) as EqT2. {
        rewrite subst_open_commute0b. erewrite subst_closed_id. reflexivity.
        eassumption.
      }
      rewrite EqT2 in HI2.
      right. repeat eexists. rewrite app_nil_l. eapply ST_AppAbs. eauto. eauto.
      eapply T_Sub. eauto. eauto.
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
