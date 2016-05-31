(*
coqc -I ../../sf/ dot.v
*)

Require Import dot.

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
  | [ |- dms_has_type ?GH ?G1 (dcons (dfun ?T11 ?T12 ?t12) ?ds) ?T ?n ] =>
    eapply (D_Fun GH G1 (length (dms_to_list ds)) T11 T12 (open 0 (TVar false (length GH)) T12) t12 ds (dms_compute ds) (TAnd (TFun (length (dms_to_list ds)) T11 T12) (dms_compute ds)))
  end.

Ltac apply_tobj := match goal with
  | [ |- has_type ?GH ?G1 (tobj ?ds) ?T ?n ] =>
    eapply (T_Obj GH G1 ds) with (T':=(dms_compute ds))
end.

Ltac apply_stp_bind1 := match goal with
  | [ |- stp ?GH ?G1 (TBind (TAnd ?T1 ?T2)) ?T1 ?n ] =>
    eapply (stp_trans GH G1 (TBind (TAnd T1 T2)) (TAnd T1 T2) T1)
end.

Ltac crush := simpl;
  try solve [apply_stp_bind1; [(eapply stp_bind1; crush) | (eapply stp_and11; crush)]];
  try solve [eapply T_Sub; [(apply_tobj; crush) | (crush)]];
  try solve [apply_dfun; crush];
  try solve [eapply stp_selx; crush];
  try solve [simpl; erewrite <- closed_no_open; try reflexivity; crush];
  try solve [econstructor; crush];
  try solve [eapply T_Sub; crush].

Example ex0: has_typed [] [] (tobj dnil) TTop.
  eexists. crush.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0.
Qed.

(* define polymorphic identity function *)

Definition polyId := TFun 0 (TMem 0 TBot TTop) (TFun 0 (TSel (TVarB 0) 0) (TSel (TVarB 1) 0)).

Example ex1: has_typed
               [] []
               (tobj (dcons (dfun (TMem 0 TBot TTop) (TFun 0 (TSel (TVarB 0) 0) (TSel (TVarB 1) 0))
               (tobj (dcons (dfun (TSel (TVar false 1) 0) (TSel (TVar false 1) 0) (tvar false 3)) dnil))) dnil)) polyId.
Proof.
  unfold polyId.
  eexists. crush.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

(* instantiate it to TTop *)
Example ex2: has_typed [polyId] [] (tapp (tvar false 0) 0 (tobj (dcons (dty TTop) dnil))) (TFun 0 TTop TTop).
Proof.
  unfold polyId.
  eexists.
  eapply T_App.
  eapply T_Sub.
  eapply T_Varz. compute. reflexivity.
  crush.
  instantiate (2:=TMem 0 TTop TTop). crush.
  crush.
  crush.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0.
Qed.
