(*
coqc -I ../../sf/ dot.v
*)

Require Import dot.

(* ############################################################ *)
(* Examples *)
(* ############################################################ *)

(* todo: automate! -- see crush in dsub.v *)

Example ex0: has_typed [] [] (tobj dnil) TTop.
  eexists. eapply T_Sub. eapply T_Obj. eapply D_Nil. eauto. eauto. eauto.
Grab Existential Variables.
apply 0. apply 0.
Qed.

(* define polymorphic identity function *)

Definition polyId := TFun 0 (TMem 0 TBot TTop) (TFun 0 (TSel (TVarB 0) 0) (TSel (TVarB 1) 0)).

Example ex1: has_typed
               [] []
               (tobj (dcons (dfun (TMem 0 TBot TTop) (TFun 0 (TSel (TVarB 0) 0) (TSel (TVarB 1) 0))
               (tobj (dcons (dfun (TSel (TVar false 1) 0) (TSel (TVar false 1) 0) (tvar false 3)) dnil))) dnil)) polyId.
Proof.
  eexists. eapply T_Sub. eapply T_Obj.
  eapply D_Abs. eapply D_Nil. eapply T_Sub. eapply T_Obj.
  eapply D_Abs. eapply D_Nil. eapply T_Varz. compute. eauto.
  compute. econstructor. econstructor. omega.
  compute. reflexivity.
  compute. econstructor. econstructor. omega.
  compute. econstructor. econstructor. omega.
  compute. reflexivity. reflexivity.
  compute. instantiate (1:=TAnd (TFun 0 (TSel (TVar false 1) 0) (TSel (TVar false 1) 0)) TTop). econstructor; eauto. econstructor; eauto.
  compute. reflexivity.
  eapply stp_trans. eapply stp_bind1.
  compute. instantiate (2:=TAnd (TFun 0 (TSel (TVar false 1) 0) (TSel (TVar false 1) 0)) TTop). eapply htp_var. compute. reflexivity.
  compute. econstructor; eauto. econstructor; eauto.
  econstructor. econstructor. omega.
  econstructor. econstructor. omega.
  compute. reflexivity.
  compute. econstructor; eauto. econstructor; eauto.
  compute. econstructor; eauto. econstructor; eauto.
  eapply stp_and11. eapply stp_fun with (T3:=(TSel (TVar false 1) 0)) (T4:=(TSel (TVar false 1) 0)) (T4':=(TSel (TVar false 1) 0)).
  compute. reflexivity.
  compute. reflexivity.
  compute. econstructor. econstructor. omega.
  compute. econstructor. econstructor. omega.
  eapply stp_selx. compute. econstructor. omega.
  eapply stp_selx. compute. econstructor. omega.
  compute. eauto.
  compute. reflexivity.
  compute. eauto.
  compute. econstructor; eauto.
  simpl. reflexivity.
  simpl. reflexivity.
  compute. instantiate (1:=TAnd (TFun 0 (TMem 0 TBot TTop) (TFun 0 (TSel (TVarB 0) 0) (TSel (TVarB 1) 0))) TTop). econstructor; eauto. econstructor; eauto. econstructor; eauto.
  econstructor. econstructor. omega.
  econstructor. econstructor. omega.
  simpl. reflexivity.
  unfold polyId.
  eapply stp_trans. eapply stp_bind1.
  eapply htp_var. compute. reflexivity.
  compute. instantiate (1:=(TAnd (TFun 0 (TMem 0 TBot TTop) (TFun 0 (TSel (TVarB 0) 0) (TSel (TVarB 1) 0))) TTop)). econstructor; eauto. econstructor; eauto. econstructor; eauto.
  simpl. reflexivity.
  compute. econstructor; eauto. econstructor; eauto. econstructor; eauto.
  econstructor. econstructor. omega.
  econstructor. econstructor. omega.
  compute. econstructor; eauto. econstructor; eauto. econstructor; eauto.
  eapply stp_and11. eapply stp_fun.
  simpl. reflexivity.
  simpl. reflexivity.
  compute. econstructor; eauto.
  compute. econstructor; eauto.
  eauto.
  eapply stp_fun. simpl. reflexivity. simpl. reflexivity. compute. econstructor. econstructor. omega. compute. econstructor. econstructor. omega.
  eapply stp_selx. compute. econstructor. omega.
  eapply stp_selx. compute. econstructor. omega.
  compute. eauto.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0.
Qed.

(* instantiate it to TTop *)
Example ex2: has_typed [polyId] [] (tapp (tvar false 0) 0 (tobj (dcons (dty TTop) dnil))) (TFun 0 TTop TTop).
Proof.
  eexists.
  eapply T_App.
  eapply T_Sub.
  eapply T_Varz. compute. reflexivity.
  compute. econstructor; eauto. econstructor; eauto.
  instantiate (2:=TMem 0 TTop TTop). eapply stp_fun.
  simpl. reflexivity.
  simpl. reflexivity.
  compute. econstructor; eauto. econstructor; eauto.
  eapply stp_mem. eauto. eauto.
  eapply stp_fun. simpl. reflexivity. simpl. reflexivity.
  compute. econstructor. econstructor. omega.
  compute. eauto.
  eapply stp_sel2. eapply htp_var. compute. eauto. compute. eauto.
  eapply stp_top. compute. econstructor. econstructor. omega.
  eapply T_Sub.
  eapply T_Obj. eapply D_Mem. eapply D_Nil. compute. eauto. simpl. reflexivity. reflexivity.
  compute. instantiate (1:=TAnd (TMem 0 TTop TTop) TTop). eauto.
  simpl. eauto.
  eapply stp_trans. eapply stp_bind1.
  eapply htp_var. compute. reflexivity.
  compute. instantiate (1:=TAnd (TMem 0 TTop TTop) TTop). eauto.
  simpl. reflexivity.
  compute. eauto.
  compute. eauto.
  eapply stp_and11. eapply stp_mem. eauto. eauto. compute. eauto. compute. eauto.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.
