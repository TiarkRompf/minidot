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
