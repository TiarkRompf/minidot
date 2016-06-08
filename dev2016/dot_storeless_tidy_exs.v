(*
coqc -I ../../sf/ dot_storeless_tidy.v
*)

(* Beware: This only works with Coq 8.4pl6, whereas Coq 8.5 seems to loop infinitely on the crush tactic *)

Require Import dot_storeless_tidy.

(* ############################################################ *)
(* Examples *)
(* ############################################################ *)

Hint Constructors dms_has_type.

Definition dm_compute (d: dm) (l: lb) :=
  match d with
    | dty T11 => TMem l T11 T11
    | dfun T11 T12 t12 => TFun l T11 T12
  end.
Fixpoint dms_compute (ds: dms) :=
  match ds with
    | dnil => TTop
    | dcons d ds => TAnd (dm_compute d (length (dms_to_list ds))) (dms_compute ds)
  end.

Ltac apply_dfun := match goal with
  | [ |- dm_has_type ?GH ?l (dfun ?T11 ?T12 ?t12) ?T ?n ] =>
    eapply (D_Fun GH l T11 T12 (open 0 (VarF (length GH)) T12) t12 (tm_open 0 (VarF (length GH)) t12))
  end.

Ltac apply_tobj := match goal with
  | [ |- has_type ?GH (tvar (VObj ?ds)) ?T ?n ] =>
    eapply (T_VObj GH ds (dms_open 0 (VarF (length GH)) ds) (dms_compute ds) (open 0 (VarF (length GH)) (dms_compute ds)) (open 0 (VObj ds) (dms_compute ds)))
end.

Ltac apply_stp_bind1 := match goal with
  | [ |- stp ?GH (TBind (TAnd ?T1 ?T2)) ?T1 ?n ] =>
    eapply (stp_trans GH (TBind (TAnd T1 T2)) (TAnd T1 T2) T1)
end.

Ltac crush := simpl;
  try solve [apply_stp_bind1; [(eapply stp_bind1; crush) | (eapply stp_and11; crush)]];
  try solve [eapply T_Sub; [(apply_tobj; crush) | (crush)]];
  try solve [apply_dfun; crush];
  try solve [eapply stp_selx; crush];
  try solve [simpl; erewrite <- closed_no_open; try reflexivity; crush];
  try solve [econstructor; crush];
  try solve [eapply T_Sub; crush].

Example ex0: has_typed [] (tvar (VObj dnil)) TTop.
  eexists. crush.
Grab Existential Variables.
apply 0. apply 0.
Qed.

Example ex_loop: has_typed [] (tvar (VObj (dcons (dfun TTop TBot (tapp (tvar (VarB 1)) 0 (tvar (VarB 0)))) dnil))) (TFun 0 TTop TBot).
  eexists.
  eapply T_Sub.
  apply_tobj.
  simpl. eapply D_Cons. reflexivity. simpl. apply_dfun.
  simpl. eapply T_App. instantiate (2:=TTop). crush.
  eapply T_VarF. simpl. reflexivity. crush. econstructor.
  reflexivity. reflexivity. crush. crush. crush. crush. reflexivity. reflexivity.
  crush. crush. reflexivity. crush.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

(* define polymorphic identity function *)

Definition polyId := TFun 0 (TMem 0 TBot TTop) (TFun 0 (TSel (VarB 0) 0) (TSel (VarB 1) 0)).

Example ex1: has_typed
               []
               (tvar (VObj (dcons (dfun (TMem 0 TBot TTop) (TFun 0 (TSel (VarB 0) 0) (TSel (VarB 1) 0))
               (tvar (VObj (dcons (dfun (TSel (VarB 1) 0) (TSel (VarB 2) 0) (tvar (VarB 0))) dnil)))) dnil))) polyId.
Proof.
  unfold polyId.
  eexists. crush.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

(* instantiate it to TTop *)
Example ex2: has_typed [polyId] (tapp (tvar (VarF 0)) 0 (tvar (VObj (dcons (dty TTop) dnil)))) (TFun 0 TTop TTop).
Proof.
  unfold polyId.
  eexists.
  eapply T_App.
  eapply T_Sub.
  eapply T_VarF. compute. reflexivity.
  crush.
  instantiate (2:=TMem 0 TTop TTop). crush.
  crush.
  crush.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.
