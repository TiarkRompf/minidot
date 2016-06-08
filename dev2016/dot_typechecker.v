Require Import LibTactics. (* from Chargueraud's TLC, everyone should use these tactics ;-) *)
Require Import dot_storeless_tidy.

(* ###################################################################### *)
(** ** Examples *)

(*
val glob = new {
  E: Top..Top,
  Stream: Bot..{head: Top -> glob.E} /\ {tail: Top -> glob.Stream}
};
val unit = new {};
val stream = new { head(x: Top): glob.E = unit, tail(x: Top): glob.Stream = stream };
stream.tail(unit).tail(unit).head(unit)
*)
Definition _E := 0.
Definition _Stream := 1.
Definition _head := 2.
Definition _tail := 3.

Definition ex1: tm :=
tvar (VObj
  (dcons (*E*) (dty TTop)
  (dcons (*Stream*) (dty
      (TAnd (TFun _head TTop (TSel (VarB 1) _E))
      (TAnd (TFun _tail TTop (TSel (VarB 1) _Stream)) TTop))) dnil))).

Inductive tc_error: Type :=
| err_tenv_hasnt: tenv -> id -> tc_error
| err_ty_hasnt: ty -> lb -> tc_error
| err_unbound_VarB: nat -> tc_error
| err_timeout: tc_error
| err_not_supported_yet: tc_error
| err_vobjs_are_not_in_tenv: dms -> tc_error
| err_type_mismatch: tenv -> tm -> ty -> ty -> tc_error.

Inductive tc_result(A: Set): Type :=
| tc_success: forall (a: A), tc_result A
| tc_fail: tc_error -> tc_result A.

Notation SUCCESS x := (tc_success _ x).
Notation FAIL err := (tc_fail _ err).

Notation "'LET' x 'BE' t1 'IN' t2" :=
  (match t1 with
   | tc_success _ x => t2
   | tc_fail _ err => tc_fail _ err
   end)   (right associativity, at level 60).

Eval cbv in (LET tp1 BE (SUCCESS TTop) IN (SUCCESS (TMem 3 tp1 tp1))).

Eval cbv in (LET tp1 BE (FAIL err_timeout) IN (SUCCESS (TMem 3 tp1 tp1))).

Definition lookup_in_tenv(G: tenv)(a: vr): tc_result ty :=
  match a with
  | VarF x => match index x G with
    | Some X => SUCCESS X
    | None => FAIL (err_tenv_hasnt G x)
    end
  | VarB n => FAIL (err_unbound_VarB n)
  | VObj ds => FAIL (err_vobjs_are_not_in_tenv ds)
  end.

Lemma lookup_in_tenv_correct: forall G i T,
  lookup_in_tenv G (VarF i) = SUCCESS T -> index i G = Some T.
Proof.
  intros. simpl in *. destruct (index i G); inversions H. reflexivity.
Qed.

(* tc_result is for timeout or non-wf types, option is for has/hasnt. *)
Fixpoint lookup_fun_or_mem(bot_default: ty)(fuel0: nat)(G: tenv)(T: ty)(l: lb): tc_result (option ty) :=
match fuel0 with
| 0 => FAIL err_timeout
| S fuel => match T with
  | TTop => SUCCESS None
  | TBot => SUCCESS (Some bot_default)
  | TMem l0 _ _ => if l =? l0 then SUCCESS (Some T) else SUCCESS None
  | TFun l0 _ _ => if l =? l0 then SUCCESS (Some T) else SUCCESS None
  | TSel a L =>
      LET X BE (lookup_in_tenv G a) IN
      LET opD BE (lookup_fun_or_mem bot_default fuel G X L) IN
      match opD with
      | Some (TMem _ Lo Hi) => lookup_fun_or_mem bot_default fuel G Hi l
      | _ => FAIL (err_ty_hasnt X L)
      end
  | TAnd T1 T2 => 
      LET oD1 BE (lookup_fun_or_mem bot_default fuel G T1 l) IN
      LET oD2 BE (lookup_fun_or_mem bot_default fuel G T2 l) IN
      match oD1, oD2 with
      | Some D1, Some D2 => FAIL err_not_supported_yet
      | Some D1, None    => SUCCESS (Some D1)
      | None   , Some D2 => SUCCESS (Some D2)
      | None   , None    => SUCCESS None
      end
  | TOr T1 T2 =>
      LET oD1 BE (lookup_fun_or_mem bot_default fuel G T1 l) IN
      LET oD2 BE (lookup_fun_or_mem bot_default fuel G T2 l) IN
      match oD1, oD2 with
      | Some D1, Some D2 => FAIL err_not_supported_yet
      | _, _ => SUCCESS None
      end
  | TBind ds => FAIL err_not_supported_yet
  end
end.

Definition lookup_fun(fuel: nat)(G: tenv)(T: ty)(l: lb)
  := lookup_fun_or_mem (TFun l TTop TBot) fuel G T l.
Definition lookup_mem(fuel: nat)(G: tenv)(T: ty)(l: lb)
  := lookup_fun_or_mem (TMem l TTop TBot) fuel G T l.

Lemma ifb_hoist: forall (A B: Type) (C: bool) (f: A -> B) (e1 e2: A),
  (if C then f e1 else f e2) = f (if C then e1 else e2).
Proof.
  intros. destruct C; auto.
Qed.

Ltac case_ifb :=
  match goal with
  | _ : context[if ?c then _ else _] |- _ => let Eq := fresh "Eq" in destruct c eqn: Eq
  end.

(*
Lemma lookup_correct: forall fuel,
   (forall G T l D, lookup_impl fuel G T l = SUCCESS (Some D) ->
    ty_has G T D /\ label_of_dec D = l)
/\ (forall G T l, lookup_impl fuel G T l = SUCCESS None     -> ty_hasnt G T l).
Proof.
  intro fuel. induction fuel; try solve [split; intros; simpl in *; discriminate].
  destruct IHfuel as [IH1 IH2]. split; introv Eq; simpl in Eq.
  + destruct T; inversions Eq.
    - destruct l; auto.
    - rewrite ifb_hoist in H0. inversions H0. case_ifb; try discriminate.
      inversions H1. apply beq_label_to_eq in Eq. subst. auto.
    - destruct a; try solve [inversions H0].
      destruct (EnvOps.get v G) eqn: Eq1; try solve [inversions H0].
      destruct (lookup_impl fuel G t0 (label_ty t)) eqn: Eq2; try solve [inversions H0].
      destruct o as [tD | ].
      * destruct (IH1 _ _ _ _ Eq2) as [Has1 Eq3].
        destruct tD as [L Lo Hi | m T1 T2]; simpl in Eq3; inversions Eq3.
        destruct (IH1 _ _ _ _ H0) as [Has2 Eq3]. eauto.
      * inversions H0.
    - repeat match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => let Eq := fresh "Eq" in destruct t eqn: Eq; inversions H
      end.
      * destruct (IH1 _ _ _ _ Eq) as [Has1 E1].
        destruct (IH1 _ _ _ _ Eq0) as [Has2 E2].
        rename d into D1, d0 into D2. split; eauto. 
        subst. destruct D1; destruct D2; unfold intersect_dec in H0; simpl; case_if;
        inversions E2; inversions H0; auto.
      * destruct (IH1 _ _ _ _ Eq) as [Has1 E1].
        lets Hasnt2: (IH2 _ _ _ Eq0). subst. eauto.
      * destruct (IH1 _ _ _ _ Eq0) as [Has1 E1].
        lets Hasnt2: (IH2 _ _ _ Eq). subst. eauto.
    - repeat match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => let Eq := fresh "Eq" in destruct t eqn: Eq; inversions H
      end.
      destruct (IH1 _ _ _ _ Eq) as [Has1 E1].
      destruct (IH1 _ _ _ _ Eq0) as [Has2 E2].
      rename d into D1, d0 into D2. split; eauto. 
      subst. destruct D1; destruct D2; unfold union_dec in H0; simpl; case_if;
      inversions E2; inversions H0; auto.
  + destruct T; inversions Eq.
    - destruct l; auto.
    - rewrite ifb_hoist in H0. inversions H0. case_ifb; try discriminate.
      inversions H1. apply beq_label_to_neq in Eq. auto.
    - destruct a; try solve [inversions H0].
      destruct (EnvOps.get v G) eqn: Eq1; try solve [inversions H0].
      destruct (lookup_impl fuel G t0 (label_ty t)) eqn: Eq2; try solve [inversions H0].
      destruct o as [tD | ].
      * destruct (IH1 _ _ _ _ Eq2) as [Has1 Eq3].
        destruct tD as [L Lo Hi | m T1 T2]; simpl in Eq3; inversions Eq3.
        lets Hasnt2: (IH2 _ _ _ H0). eauto.
      * inversions H0.
    - repeat match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => let Eq := fresh "Eq" in destruct t eqn: Eq; inversions H
      end.
      * destruct (IH1 _ _ _ _ Eq) as [Has1 E1].
        destruct (IH1 _ _ _ _ Eq0) as [Has2 E2].
        rename d into D1, d0 into D2.
        subst. destruct D1; destruct D2; unfold intersect_dec in H0; simpl; case_if;
        inversions E2; inversions H0; simpl in *.
        { destruct (Peano_dec.eq_nat_dec t t); try discriminate. exfalso. auto. }
        { destruct (Peano_dec.eq_nat_dec m m); try discriminate. exfalso. auto. }
      * lets Hasnt1: (IH2 _ _ _ Eq).
        lets Hasnt2: (IH2 _ _ _ Eq0). eauto.
    - repeat match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => let Eq := fresh "Eq" in destruct t eqn: Eq; inversions H
      end.
      * destruct (IH1 _ _ _ _ Eq) as [Has1 E1].
        destruct (IH1 _ _ _ _ Eq0) as [Has2 E2].
        unfold union_dec in H0. rewrite E1 in H0. rewrite E2 in H0.
        case_ifb. {
          rename d into D1, d0 into D2.
          subst. destruct D1; destruct D2; simpl; discriminate.
        } {
          exfalso. destruct l; unfold beq_label in Eq1.
          - destruct (Peano_dec.eq_nat_dec t t); [discriminate | auto].
          - destruct (Peano_dec.eq_nat_dec m m); [discriminate | auto].
        }
      * destruct (IH1 _ _ _ _ Eq) as [Has1 E1].
        lets Hasnt2: (IH2 _ _ _ Eq0). subst. eauto.
      * destruct o0 as [D |].
        { destruct (IH1 _ _ _ _ Eq0) as [Has1 E1].
          lets Hasnt2: (IH2 _ _ _ Eq). subst. eauto. }
        { lets Hasnt1: (IH2 _ _ _ Eq).
          lets Hasnt2: (IH2 _ _ _ Eq0). eauto. }
Qed.
*)



Fixpoint eq_vr_dec(v1 v2: vr): {v1 = v2} + {v1 <> v2}
with eq_ty_dec(T1 T2: ty): {T1 = T2} + {T1 <> T2}
with eq_tm_dec(t1 t2: tm): {t1 = t2} + {t1 <> t2}
with eq_dm_dec(d1 d2: dm): {d1 = d2} + {d1 <> d2}
with eq_dms_dec(ds1 ds2: dms): {ds1 = ds2} + {ds1 <> ds2}.
* decide equality; apply eq_nat_dec.
* decide equality; apply eq_nat_dec.
* decide equality; apply eq_nat_dec.
* decide equality.
* decide equality.
Defined.

Eval cbv in (if eq_dms_dec dnil dnil then "same" else "different").

Definition in_ty_list(T: ty)(l: list ty): bool :=
  if List.in_dec eq_ty_dec T l then true else false.

(* Some true: wf
   Some false: not wf
   None: timeout, either because of lack of fuel, or because not wf.
   A: assumptions (types which are assumed to be wf).
 *)
(*
Fixpoint check_wf_ty(fuel0: nat)(G: tenv)(A: list ty)(T: ty): tc_result unit :=
match fuel0 with
| 0 => FAIL err_timeout
| S fuel => if (in_ty_list T A) then SUCCESS tt else (match T with
  | TTop => SUCCESS tt
  | TBot => SUCCESS tt
  | ty_rcd (TMem L Lo Hi) => let A2 := cons T A in
      LET _ BE (check_wf_ty fuel G A2 Lo) IN (check_wf_ty fuel G A2 Hi)
  | ty_rcd (dec_mtd m T1 T2) => let A2 := cons T A in
      LET _ BE (check_wf_ty fuel G A2 T1) IN (check_wf_ty fuel G A2 T2)
  | TSel a L => 
      LET X BE (lookup_in_tenv G a) IN
      LET oD BE (lookup_impl fuel G X (label_ty L)) IN
      match oD with
      | Some (TMem _ Lo Hi) => if is_stable_ty X
          then LET _ BE check_wf_ty fuel G A X  IN
               LET _ BE check_wf_ty fuel G A Lo IN
                        check_wf_ty fuel G A Hi
          else FAIL (err_TSel_on_unstable a X L)
      | _ => FAIL (err_ty_hasnt X (label_ty L))
      end
  | TAnd T1 T2 => LET _ BE (check_wf_ty fuel G A T1) IN (check_wf_ty fuel G A T2)
  | TOr  T1 T2 => LET _ BE (check_wf_ty fuel G A T1) IN (check_wf_ty fuel G A T2)
  end)
end.
*)
(*
Lemma is_wf_ty_correct: forall fuel G A T,
  is_wf_ty fuel G A T = true -> wf_ty_impl G (from_list A) T.
Proof.
  intro. induction fuel; try solve [intros; simpl in *; discriminate].
  rename IHfuel into IH. introv Eq. simpl in Eq.
  destruct (in_ty_list T A) eqn: EqI.
  - clear Eq. assert (In: T \in (from_list A)) by admit. (* from EqI *)
    apply (wf_hyp _ In).
  - simpl in Eq. destruct T.
    + apply wf_top.
    + apply wf_bot.
    + apply wf_rcd. rewrite union_comm. rewrite <- from_list_cons.
      destruct d as [L Lo Hi | m Ta Tr];
      apply andb_prop in Eq; destruct Eq as [Eq1 Eq2];
      eauto.
    + destruct a; try discriminate.
      repeat match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => let Eq := fresh "Eq" in destruct t eqn: Eq; inversions H
      end.
      destruct d; try discriminate.
      apply andb_prop in H0. destruct H0 as [H0 Eq4].
      apply andb_prop in H0. destruct H0 as [H0 Eq3].
      apply andb_prop in H0. destruct H0 as [Eq1 Eq2].
      lets W1: (IH _ _ _ Eq2).
      lets W2: (IH _ _ _ Eq3).
      lets W3: (IH _ _ _ Eq4).
      refine (wf_sel Eq0 _ _ W1 W2 W3).
      * apply (is_stable_ty_correct _ Eq1).
      * destruct ((proj1 (lookup_correct fuel)) _ _ _ _ Eq) as [Has E].
        simpl in E. inversions E. exact Has.
    + apply andb_prop in Eq. destruct Eq as [Eq1 Eq2]. eauto.
    + apply andb_prop in Eq. destruct Eq as [Eq1 Eq2]. eauto.
Qed.
*)

Definition check_closed(G: tenv)(tp: ty): tc_result unit := SUCCESS tt. (* TODO *)

Fixpoint isSubType(fuel0: nat)(G: tenv)(tp1 tp2: ty): tc_result bool := match fuel0 with
| 0 => FAIL err_timeout
| S fuel => if eq_ty_dec tp1 tp2
            then LET _ BE (check_closed G tp1) IN SUCCESS true
            else firstTry fuel G tp1 tp2
end
with firstTry(fuel0: nat)(G: tenv)(tp1 tp2: ty): tc_result bool := match fuel0 with
| 0 => FAIL err_timeout
| S fuel => match tp2 with
  | TTop => LET _ BE check_closed G tp1 IN SUCCESS true
  | TBot => secondTry fuel G tp1 tp2
  | TMem L2 tpLo2 tpHi2 => match tp1 with
    | (TMem L1 tpLo1 tpHi1) =>
        if (L1 =? L2)
        then LET b1 BE (isSubType fuel G tpLo2 tpLo1) IN
             LET b2 BE (isSubType fuel G tpHi1 tpHi2) IN
             SUCCESS (b1 && b2)
        else SUCCESS false
    | _ => (secondTry fuel G tp1 tp2)
    end
  | TFun m2 tpArg2 tpRet2 => match tp1 with
    | (TFun m1 tpArg1 tpRet1) =>
        if (m1 =? m2)
        then LET b1 BE (isSubType fuel G tpArg2 tpArg1) IN
             LET b2 BE (isSubType fuel G tpRet1 tpRet2) IN
             SUCCESS (b1 && b2)
        else SUCCESS false
    | _ => (secondTry fuel G tp1 tp2)
    end
  | TSel a L => 
      LET X BE (lookup_in_tenv G a) IN
      LET oD BE (lookup_mem fuel G X L) IN
      match oD with
      | Some (TMem _ Lo Hi) =>
          LET b1 BE (isSubType fuel G tp1 Lo) IN
          LET b2 BE (isSubType fuel G Lo Hi) IN
          if (b1 && b2) then (SUCCESS true) else (secondTry fuel G tp1 tp2)
        | _ => FAIL (err_ty_hasnt X L)
      end
  | TAnd tp21 tp22 => 
      LET b1 BE (isSubType fuel G tp1 tp21) IN
      LET b2 BE (isSubType fuel G tp1 tp22) IN
      SUCCESS (b1 && b2)
  | TOr tp21 tp22 =>
      LET _ BE (check_closed G tp21) IN
      LET _ BE (check_closed G tp22) IN
      LET b1 BE (isSubType fuel G tp1 tp21) IN
      if b1 then (SUCCESS true) else
      LET b2 BE (isSubType fuel G tp1 tp22) IN
      if b2 then (SUCCESS true) else
      (secondTry fuel G tp1 tp2)
  | TBind ds => FAIL err_not_supported_yet
  end
end
with secondTry(fuel0: nat)(G: tenv)(tp1 tp2: ty): tc_result bool := match fuel0 with
| 0 => FAIL err_timeout
| S fuel => match tp1 with
  | TBot => LET _ BE (check_closed G tp2) IN (SUCCESS true)
  | TSel a L => 
      LET X BE (lookup_in_tenv G a) IN
      LET oD BE (lookup_mem fuel G X L) IN
      match oD with
      | Some (TMem _ Lo Hi) =>
          LET b1 BE (isSubType fuel G Hi tp2) IN
          LET b2 BE (isSubType fuel G Lo Hi) IN
          SUCCESS (b1 && b2)
        | _ => FAIL (err_ty_hasnt X L)
      end
  | TAnd tp11 tp12 =>
      LET _ BE (check_closed G tp11) IN
      LET _ BE (check_closed G tp12) IN
      LET b1 BE (isSubType fuel G tp11 tp2) IN
      if b1 then (SUCCESS true) else
      LET b2 BE (isSubType fuel G tp12 tp2) IN
      (SUCCESS b2)
  | TOr tp11 tp12 =>
      LET b1 BE (isSubType fuel G tp11 tp2) IN
      LET b2 BE (isSubType fuel G tp12 tp2) IN
      (SUCCESS (b1 && b2))
  | _ => SUCCESS false
  end
end.

(*
Lemma isSubType_correct: forall fuel,
   (forall G tp1 tp2, isSubType fuel G tp1 tp2 = true -> subty nohyp G tp1 tp2)
/\ (forall G tp1 tp2, firstTry  fuel G tp1 tp2 = true -> subty nohyp G tp1 tp2)
/\ (forall G tp1 tp2, secondTry fuel G tp1 tp2 = true -> subty nohyp G tp1 tp2).
Proof.
  intro. induction fuel. try solve [repeat split; intros; simpl in *; discriminate].
  destruct IHfuel as [IH0 [IH1 IH2]]. repeat split; introv Eq.
  + unfold isSubType in Eq. fold isSubType in Eq. fold firstTry in Eq. case_ifb.
    - subst. apply subty_refl. rewrite <- from_list_nil.
      apply (is_wf_ty_correct fuel). exact Eq.
    - apply (IH1 _ _ _ Eq).
  + destruct tp2.
    - apply subTTop. rewrite <- from_list_nil.
      apply (is_wf_ty_correct fuel). exact Eq.
    - apply (IH2 _ _ _ Eq).
    - unfold isSubType in Eq. fold isSubType in Eq.
      destruct d as [L2 Lo2 Hi2 | m2 A2 R2]; destruct tp1; try discriminate;
      destruct d as [L1 Lo1 Hi1 | m1 A1 R1]; try discriminate;
      apply andb_prop in Eq; destruct Eq as [Eq Eq3];
      apply andb_prop in Eq; destruct Eq as [Eq1 Eq2].
      * destruct (Peano_dec.eq_nat_dec L1 L2) as [Eq | Ne]; try discriminate; subst.
        apply subty_rcd. apply* subTMem.
      * destruct (Peano_dec.eq_nat_dec m1 m2) as [Eq | Ne]; try discriminate; subst.
        apply subty_rcd. apply* subdec_mtd.
    - unfold firstTry in Eq. fold secondTry in Eq. fold isSubType in Eq.
      destruct a; try discriminate.
      repeat match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => let Eq := fresh "Eq" in destruct t eqn: Eq; inversions H
      end.
      destruct d; try discriminate.
      apply Bool.orb_true_elim in H0. destruct H0 as [H0 | H0].
      * apply andb_prop in H0. destruct H0 as [H0 Eq4].
        apply andb_prop in H0. destruct H0 as [H0 Eq3].
        apply andb_prop in H0. destruct H0 as [Eq1 Eq2].
        apply (subty_trans (IH0 _ _ _ Eq1)).
        refine (subTSel_r Eq0 _ _ _ _).
        { rewrite <- from_list_nil. apply* is_wf_ty_correct. }
        { apply* is_stable_ty_correct. }
        { destruct ((proj1 (lookup_correct fuel)) _ _ _ _ Eq) as [Has E].
          simpl in E. inversions E. exact Has. }
        { apply* IH0. }
      * fold secondTry in H0. apply* IH2.
    - unfold isSubType in Eq. fold isSubType in Eq.
      apply andb_prop in Eq. destruct Eq as [Eq1 Eq2]. apply* subTAnd.
    - unfold isSubType in Eq. fold secondTry in Eq.
      apply Bool.orb_true_elim in Eq. destruct Eq as [Eq | Eq].
      * fold isSubType in Eq.
        apply Bool.orb_true_elim in Eq. destruct Eq as [Eq | Eq];
        apply andb_prop in Eq; destruct Eq as [Eq1 Eq2].
        { specialize (IH0 _ _ _ Eq1).
          refine (subty_trans IH0 (subTOr_l _ _ _)).
          + admit. (* subty_regular *)
          + rewrite <- from_list_nil. apply* is_wf_ty_correct. }
        { specialize (IH0 _ _ _ Eq1).
          refine (subty_trans IH0 (subTOr_r _ _ _)).
          + rewrite <- from_list_nil. apply* is_wf_ty_correct.
          + admit. (* subty_regular *) }
      * apply* IH2.
  + destruct tp1; unfold secondTry in Eq.
    - discriminate.
    - apply subTBot.
      rewrite <- from_list_nil. apply* is_wf_ty_correct.
    - discriminate.
    - fold isSubType in Eq.
      destruct a; try discriminate.
      repeat match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => let Eq := fresh "Eq" in destruct t eqn: Eq; inversions H
      end.
      destruct d; try discriminate.
      apply andb_prop in H0. destruct H0 as [H0 Eq4].
      apply andb_prop in H0. destruct H0 as [H0 Eq3].
      apply andb_prop in H0. destruct H0 as [Eq1 Eq2].
      refine (subty_trans _ (IH0 _ _ _ Eq1)).
      refine (subTSel_l Eq0 _ _ _ _).
      { rewrite <- from_list_nil. apply* is_wf_ty_correct. }
      { apply* is_stable_ty_correct. }
      { destruct ((proj1 (lookup_correct fuel)) _ _ _ _ Eq) as [Has E].
        simpl in E. inversions E. exact Has. }
      { apply* IH0. }
    - fold isSubType in Eq.
      apply Bool.orb_true_elim in Eq.
      destruct Eq as [Eq | Eq]; apply andb_prop in Eq; destruct Eq as [Eq1 Eq2].
      * specialize (IH0 _ _ _ Eq1).
        refine (subty_trans (subTAnd_l _ _ _) IH0).
        { admit. (* subty_regular *) }
        { rewrite <- from_list_nil. apply* is_wf_ty_correct. }
      * specialize (IH0 _ _ _ Eq1).
        refine (subty_trans (subTAnd_r _ _ _) IH0).
        { rewrite <- from_list_nil. apply* is_wf_ty_correct. }
        { admit. (* subty_regular *) }
    - fold isSubType in Eq. apply andb_prop in Eq; destruct Eq as [Eq1 Eq2].
      apply* subTOr.
Qed.
*)

Definition predictDefType(l: lb)(d: dm): ty := match d with
| dty U => TMem l U U
| dfun T1 T2 body => TFun l T1 T2
end.

Fixpoint predictDefsType(ds: dms): ty := match ds with
| dnil => TTop
| dcons d rest => TAnd (predictDefType (length (dms_to_list rest)) d) (predictDefsType rest)
end.

Definition adapt(fuel: nat)(G: tenv)(t: tm)(tpFound: ty)(tpExpected: option ty)
  : tc_result ty :=
  match tpExpected with
  | Some tpEx => LET b1 BE (isSubType fuel G tpFound tpEx) IN
                 if b1 then SUCCESS tpEx
                 else FAIL (err_type_mismatch G t tpFound tpEx)
  | None => SUCCESS tpFound
  end.

(* pt: expected type *)
Fixpoint typeCheckTrm(fuel0: nat)(G: tenv)(t: tm)(pt: option ty): tc_result ty :=
match fuel0 with
| 0 => FAIL err_timeout
| S fuel => LET tpFound BE (match t with
  | tvar (VObj ds) =>
      let T := predictDefsType ds in
      let T' := open 0 (VarF (length G)) T in
      let ds' := dms_open 0 (VarF (length G)) ds in
      LET _ BE (typeCheckDefs fuel (T' :: G) ds') IN SUCCESS (TBind T)
  | tvar v => lookup_in_tenv G v
  | tapp t m u =>
      LET T BE (typeCheckTrm fuel G t None) IN
      LET oD BE (lookup_fun fuel G T m) IN
      match oD with
      | Some (TFun _ tpArg tpRet) =>
          LET _ BE (typeCheckTrm fuel G u (Some tpArg)) IN
        (*TODO check whether return type contains self ref or arg name*)
          SUCCESS tpRet
      | _ => FAIL (err_ty_hasnt T m)
      end
  end) IN (adapt fuel G t tpFound pt)
end
with typeCheckDef(fuel0: nat)(G: tenv)(d: dm): tc_result unit := match fuel0 with
| 0 => FAIL err_timeout
| S fuel => match d with
  | dty U => check_closed G U
  | dfun T1 T2 body =>
      LET _ BE (typeCheckTrm fuel (T1 :: G) (tm_open 0 (VarF (length G)) body) (Some T2)) IN
      LET _ BE (check_closed G T1) IN (check_closed G T2)
  end
end
with typeCheckDefs(fuel0: nat)(G: tenv)(ds: dms): tc_result unit := match fuel0 with
| 0 => FAIL err_timeout
| S fuel => match ds with
  | dnil => SUCCESS tt
  | dcons d rest => LET _ BE (typeCheckDef fuel G d) IN (typeCheckDefs fuel G rest)
  end
end.

Lemma simpl_success: forall {A: Set} (e: tc_result A),
  LET a BE e IN SUCCESS a = e.
Proof.
  intros. destruct e; reflexivity.
Qed.

Lemma simpl_success_eq: forall {A B: Set} (e: tc_result B) (a2 a3: A),
  LET _ BE e IN SUCCESS a2 = SUCCESS a3 ->
  exists a1, e = SUCCESS a1 /\ a2 = a3.
Proof.
  intros. destruct e; inversions H. eauto.
Qed.

Lemma simpl_success_chain: forall {A1 A2: Set} (e1: tc_result A1) (e2: tc_result A2) (a: A2),
  LET x BE e1 IN e2 = SUCCESS a ->
  (exists a1, e1 = SUCCESS a1).
Proof.
  intros. destruct e1; inversions H. eauto.
Qed.

(*
Lemma simpl_success_eq: forall {A: Set} (e: tc_result A) (a2 a3: A),
  LET _ BE e IN SUCCESS a2 = SUCCESS a3 ->
  exists a1, e = SUCCESS a1 /\ a2 = a3.
Proof.
  intros. destruct e; inversions H. eauto.
Qed.

Lemma eq_success_inv: forall {A: Set} (e: tc_result A) (a: A),
  LET _ BE e = SUCCESS a -> 

Lemma success_eq_inv: forall {A B: Set} (e1: tc_result A) (a: A) (b1 b2: B),
  match e1 with
  | tc_success _ y => tc_success B b1
  | tc_fail _ err => tc_fail B err
  end = (tc_success B b2) ->
  b1 = b2 /\ exists a, e1 = tc_success A a.
Proof.
  intros. destruct e1.
  - inversion H. eauto.
  - inversion H.
Qed.
*)

Axiom admit_closed: forall i j T, closed i j T.
Axiom admit_dms_closed: forall i j ds, dms_closed i j ds.

Lemma open_and_predictDefsType_commute: forall i v ds,
  open i v (predictDefsType ds) = predictDefsType (dms_open i v ds).
Admitted.

Definition satisfies_pt(G: tenv)(T: ty)(pt: option ty)(n: nat) := match pt with
  | Some T' => stp G T T' n
  | None => True
  end.

Lemma adapt_correct: forall fuel G t T1 pt T2,
  adapt fuel G t T1 pt = SUCCESS T2 ->
  pt = None \/ (pt = Some T2 /\ exists n, stp G T1 T2 n).
Proof.
  intros. destruct pt.
  - right. unfold adapt in H. destruct (isSubType fuel G T1 t0) eqn: E; inversions H.
    destruct a eqn: E2; inversions H1.
    split; try reflexivity. admit. (* is_subtyp_correct *)
  - auto.
Qed.

(*
Definition has_expected_type(G: tenv)(t: tm)(pt: option ty)(T: ty)(n: nat) := match pt with
  | Some T' => T = T' /\ has_type G t T n
  | None => has_type G t T n
  end.
*)

Lemma typeChecking_correct: forall fuel,
   (forall G t pt T, typeCheckTrm  fuel G t pt = SUCCESS T  -> exists n, has_type G t T n)
/\ (forall G d l   , typeCheckDef  fuel G d    = SUCCESS tt -> exists n, dm_has_type G l d (predictDefType l d) n)
/\ (forall G ds    , typeCheckDefs fuel G ds   = SUCCESS tt -> exists n, dms_has_type G ds (predictDefsType ds) n).
Proof.
  intro fuel. induction fuel; try solve [repeat split; intros; inversions H].
  destruct IHfuel as [IH1 [IH2 IH3]]. split; [idtac | split]; introv Eq.
  + destruct t.
    - destruct v.
      * simpl in Eq. destruct (index i G) eqn: Eq2; inversions Eq.
        eexists. econstructor. assumption. apply admit_closed.
      * simpl in Eq. inversions Eq.
      * simpl in Eq. rewrite simpl_success in Eq. apply simpl_success_eq in Eq.
        destruct Eq as [unit [Eq2 Eq3]]. subst T. destruct unit.
        apply IH3 in Eq2. destruct Eq2 as [n D].
        rewrite <- open_and_predictDefsType_commute in D.
        eexists. eapply T_VarPack.
        { eapply T_VObj.
          + eapply D.
          + reflexivity.
          + reflexivity.
          + apply admit_closed.
          + apply admit_dms_closed.
          + reflexivity. }
        { reflexivity. }
        { apply admit_closed. }
    - inversions Eq. rewrite simpl_success in H0.
      destruct (typeCheckTrm fuel G t1) eqn: Eq; inversions H0.
      destruct (lookup_fun fuel G a l) eqn: Eq2; inversions H1.
      destruct a0 eqn: Eq3; inversions H0.
      destruct t eqn: Eq4; inversions H1.
      destruct (typeCheckTrm fuel G t2 (Some t0_1)) eqn: Eq5; inversions H0.
      edestruct (IH1 _ _ _ Eq). edestruct (IH1 _ _ _ Eq5).
      eexists. eapply T_App.
      - eapply IH1

      destruct (simpl_success_chain _ _ _ H0) as [a1 Eq].
 apply simpl_success_eq in H0.


    - fold typeCheckDefs in Eq. fold typeAssign in Eq. case_ifb; try discriminate.
      match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => destruct t eqn: Eq1
      end; try discriminate.
      case_ifb; try discriminate. inversions Eq.
      specialize (IH1 _ _ _ Eq1).
      specialize (IH3 _ _ Eq0).
      apply_fresh ty_new as x;
      try assert (Eqx: gen_fresh_var_from_env G = x) by admit; subst.
      * rewrite <- open_and_predictDefsType_commute in IH3. apply IH3.
      * rewrite <- open_and_predictDefsType_commute in IH1. apply IH1.
      * rewrite <- from_list_nil. apply* is_wf_ty_correct.
    - fold typeAssign in Eq.
      repeat match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => let Eq := fresh "Eq" in destruct t eqn: Eq; inversions H
      end.
      destruct d; try discriminate.
      match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => let Eq := fresh "Eq" in destruct t eqn: Eq; inversions H
      end.
      case_ifb; try discriminate. inversions H1.
      apply andb_prop in Eq2. destruct Eq2 as [Eq2 Eq3].
      refine (ty_call _ _ _ _).
      * apply (IH1 _ _ _ Eq0).
      * destruct ((proj1 (lookup_correct fuel)) _ _ _ _ Eq) as [Has E].
        simpl in E. inversions E. apply Has.
      * apply ty_sbsm with t4. 
        { apply (IH1 _ _ _ Eq1). }
        { assert (Imp: subty nohyp G t4 t0 -> subty okhyp G t4 t0) by admit. apply Imp.
          apply ((proj1 (isSubType_correct fuel)) _ _ _ Eq2). }
      * rewrite <- from_list_nil. apply* is_wf_ty_correct.
  + destruct d; unfold typeCheckDef in Eq.
    - apply ty_tdef. rewrite <- from_list_nil. apply* is_wf_ty_correct.
    - fold typeAssign in Eq.
      match goal with
      | H: match ?t with
           | Some _ => _
           | None => _
           end = _ |- _ => let Eq := fresh "Eq" in destruct t eqn: Eq
      end; try discriminate.
      apply andb_prop in Eq. destruct Eq as [Eq Eq3].
      apply andb_prop in Eq. destruct Eq as [Eq1 Eq2].
      apply_fresh ty_mdef as x;
      try assert (Eqx: gen_fresh_var_from_env G = x) by admit; subst.
      * rewrite <- from_list_nil. apply* is_wf_ty_correct.
      * rewrite <- from_list_nil. apply* is_wf_ty_correct.
      * apply ty_sbsm with t2.
        { apply (IH1 _ _ _ Eq0). }
        { assert (Imp: subty nohyp G t2 t0
                    -> subty okhyp (G & gen_fresh_var_from_env G ~ t) t2 t0) by admit.
          apply Imp.
           (* TODO weakening & nohyp_to_okhyp *)
          apply ((proj1 (isSubType_correct fuel)) _ _ _ Eq3). }
  + destruct ds; unfold typeCheckDefs in Eq.
    - simpl. apply ty_defs_nil.
    - fold typeCheckDef in Eq. fold typeCheckDefs in Eq.
      destruct (get_def (label_of_def d) ds) eqn: Eq0; try discriminate.
      apply andb_prop in Eq. destruct Eq as [Eq1 Eq2].
      apply ty_defs_cons.
      * fold predictDefsType. apply* IH3.
      * apply* IH2.
      * apply Eq0.
Qed.

Definition typeAssign_correct(fuel: nat) := (proj1 (typeChecking_correct fuel)).
*)

Definition TStream :=
      (TAnd (TFun _head TTop (TSel (VarB 1) _E))
      (TAnd (TFun _tail TTop (TSel (VarB 1) _Stream)) TTop)).

(*
Fact tc1: ty_tm empty ex1 TTop.
Proof.
  apply (typeAssign_correct 20). reflexivity.
Qed.

val glob = new {
  E: Top..Top,
  Stream: Bot..{head: Top -> glob.E} /\ {tail: Top -> glob.Stream}
};
val unit = new {};
val stream = new { head(x: Top): glob.E = unit, tail(x: Top): glob.Stream = stream };
stream.tail(unit).tail(unit).head(unit)
*)

Definition ex2: tm :=
tm_new (defs_cons (defs_cons defs_nil
  (def_ty E (ty_rcd (dec_mtd msg TTop TTop))))
  (def_ty Stream (TAnd
       (ty_rcd (dec_mtd head TTop (TSel (avar_b 0) E)))
       (ty_rcd (dec_mtd tail TTop (TSel (avar_b 0) Stream)))))
)
(tm_new defs_nil
(tm_new (defs_cons defs_nil 
  (def_mtd msg TTop TTop (tm_var (avar_b 1))))
(tm_new (defs_cons (defs_cons defs_nil
   (def_mtd head TTop (TSel (avar_b 3) E) (tm_var (avar_b 2))))
   (def_mtd tail TTop (TSel (avar_b 3) Stream) (tm_var (avar_b 1))))
(tm_call (tm_var (avar_b 0)) head (tm_var (avar_b 2)))))).

Eval vm_compute in
  (typeCheckTrm 34 empty ex2 (Some (ty_rcd (dec_mtd msg TTop TTop)))).

Definition ex2: tm :=
tm_new (defs_cons (defs_cons defs_nil
  (def_ty E TTop))
  (def_ty Stream (TAnd
       (ty_rcd (dec_mtd head TTop (TSel (avar_b 0) E)))
       (ty_rcd (dec_mtd tail TTop (TSel (avar_b 0) Stream)))))
)
(tm_new defs_nil
(tm_new (defs_cons (defs_cons defs_nil
   (def_mtd head TTop (TSel (avar_b 2) E) (tm_var (avar_b 2))))
   (def_mtd tail TTop (TSel (avar_b 2) Stream) (tm_var (avar_b 1))))
(tm_var (avar_b 1)))).

Eval vm_compute in (typeAssign 34 empty ex2).

Fact tc2: ty_tm empty ex2 TTop.
Proof.
  apply (typeAssign_correct 30). reflexivity.
Qed.


