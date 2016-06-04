Require Import dot.

(* ############################################################ *)
(* Examples *)
(* ############################################################ *)

Hint Constructors dms_has_type.

Definition dm_compute (d: dm) (l: lb) :=
  match d with
    | dty T11 => TMem l T11 T11
    | dfun (Some T11) (Some T12) t12 => TFun l T11 T12
    | dfun _ _ t12 => TFun l TBot TTop (* tactic not supported *)
  end.
Fixpoint dms_compute (ds: dms) :=
  match ds with
    | dnil => TTop
    | dcons d ds => TAnd (dm_compute d (length (dms_to_list ds))) (dms_compute ds)
  end.

Ltac apply_dfun := match goal with
  | [ |- dms_has_type ?GH ?G1 (dcons (dfun (Some ?T11) (Some ?T12) ?t12) ?ds) ?T ?n ] =>
    eapply (D_Fun GH G1 (length (dms_to_list ds)) (Some T11) T11 (Some T12) T12 (open 0 (TVar false (length GH)) T12) t12 ds (dms_compute ds) (TAnd (TFun (length (dms_to_list ds)) T11 T12) (dms_compute ds)))
  end.

Ltac apply_tobj := match goal with
  | [ |- has_type ?GH ?G1 (tobj ?ds) ?T ?n ] =>
    eapply (T_Obj GH G1 ds) with (T':=(dms_compute ds))
end.

Ltac apply_stp_bind1 := match goal with
  | [ |- stp ?GH ?G1 (TBind (TAnd ?T1 ?T2)) ?T1 ?n ] =>
    eapply stp_bind1 with (T1':=(TAnd T1 T2))
end.

Ltac crush := simpl;
  try solve [apply_stp_bind1; crush];
  try solve [eapply T_Sub; [(apply_tobj; crush) | (crush)]];
  try solve [apply_dfun; crush];
  try solve [eapply stp_selx; crush];
  try solve [simpl; erewrite <- closed_no_open; try reflexivity; crush];
  try solve [econstructor; crush];
  try solve [eapply T_Sub; crush];
  try solve [unfold eq_some; eauto 3].

Definition tfun TS TU t := dfun (Some TS) (Some TU) t.
Definition nfun t := dfun None None t.
Fixpoint list_to_dms (xs: list dm) : dms :=
  match xs with
    | nil => dnil
    | cons d xs => dcons d (list_to_dms xs)
  end.
Definition lobj ds := tobj (list_to_dms ds).

Example ex0: has_typed [] [] (tobj dnil) TTop.
  eexists. crush.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0.
Qed.

(* define polymorphic identity function *)
Definition polyId := TFun 0 (TMem 0 TBot TTop) (TFun 0 (TSel (TVarB 0) 0) (TSel (TVarB 1) 0)).

Example ex1: has_typed
               [] []
               (tobj (dcons (tfun (TMem 0 TBot TTop) (TFun 0 (TSel (TVarB 0) 0) (TSel (TVarB 1) 0))
               (tobj (dcons (tfun (TSel (TVar false 1) 0) (TSel (TVar false 1) 0) (tvar false 3)) dnil))) dnil)) polyId.
Proof.
  unfold polyId. unfold tfun.
  eexists. crush.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0.
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
apply 0.
Qed.

(*# Example from Paper #*)

(*
val listModule = new { m =>
  type List = { this =>
    type Elem
    def head(): this.Elem
    def tail(): m.List & { type Elem <: this.Elem }
  }
  def nil() = new { this =>
    type Elem = Bot
    def head() = bot()
    def tail() = bot()
  }
  def cons[T](hd: T)(tl: m.List & { type Elem <: T }) = new { this =>
    type Elem = T
    def head() = hd
    def tail() = tl
  }
}

type ListAPI = { m =>
  type List <: { this =>
    type Elem
    def head(): this.Elem
    def tail(): m.List & { type Elem <: this.Elem }
  }
  def nil(): List & { type Elem = Bot }
  def cons[T]: T =>
    m.List & { type Elem <: T } =>
      m.List & { type Elem <: T }
}

def cons(t: { type T }) = new {
  def apply(hd: t.T) = new {
    def apply(m.List & { type Elem <: t.T }) = new { this =>
      type Elem = t.T
      def head() = hd
      def tail() = tl
    }}}

*)

(*
new { m =>
  type List = { this => type Elem; def head(): this.Elem }
  def nil() = new { this => type Elem = Bot def head() = bot() }
} : { m =>
  type List <: { this => type Elem; def head(): this.Elem }
  def nil(): List & { type Elem = Bot }
}
*)
Definition TLstHd EL EU :=
  (TBind (TAnd
    (TFun 1 TTop (TSel (TVarB 1) 0)) (*def head(_:Top):this.Elem*)
    (TMem 0 EL EU) (*type Elem*)
  )).
Example paper_lsthd_nil:
  has_typed [] []
    (lobj
       [(tfun
           TTop (TLstHd TBot TBot)
           (lobj [(tfun TTop TBot (tapp (tvar false 2) 1 (tvar false 3)));
                  (dty TBot)]));
         (dty (TLstHd TBot TTop))])
    (TBind (TAnd
              (TFun 1 TTop (TAnd (TSel (TVarB 1) 0) (TMem 0 TBot TBot)))
              (TMem 0 TBot (TLstHd TBot TTop)))).
Proof.
  compute.
  eexists.
  eapply T_Sub.
  apply_tobj; simpl.
  apply_dfun; simpl. crush.
  eapply T_Sub. apply_tobj; simpl.
  apply_dfun; simpl. crush.
  eapply T_App; try solve [simpl; reflexivity]. instantiate (2:=TTop).
  eapply T_Sub. eapply T_Varz; crush. crush. crush. crush. crush. crush. crush. crush.
  crush. crush. crush. crush. crush. eapply stp_bindx; try solve [simpl; reflexivity].
  eapply stp_and2. crush. eapply stp_and12. eapply stp_and11. crush. crush. crush.
  crush. crush. crush. crush. crush. crush. crush. crush. crush. crush. crush.
  eapply stp_bindx; try solve [simpl; reflexivity].
  eapply stp_and2. eapply stp_and11. eapply stp_fun; try solve [simpl; reflexivity].
  crush. crush. crush. eapply stp_and2. eapply stp_sel2; try solve [simpl; reflexivity].
  eapply htp_sub. eapply htp_var. simpl. reflexivity. crush.
  eapply stp_and12. eapply stp_and11. eapply stp_mem.
  eapply stp_bindx; try solve [simpl; reflexivity].
  eapply stp_and2. eapply stp_and11. crush. crush. eapply stp_and12. crush. crush.
  crush. crush. crush. crush. crush.
  instantiate (1:=[TAnd
   (TFun 1 TTop
      (TBind (TAnd (TFun 1 TTop (TSel (TVarB 1) 0)) (TMem 0 TBot TBot))))
   (TAnd
      (TMem 0
         (TBind (TAnd (TFun 1 TTop (TSel (TVarB 1) 0)) (TMem 0 TBot TTop)))
         (TBind (TAnd (TFun 1 TTop (TSel (TVarB 1) 0)) (TMem 0 TBot TTop))))
      TTop)]). simpl. reflexivity. instantiate (1:=[TTop]). simpl. reflexivity.
  eapply stp_bind1; try solve [simpl; reflexivity]. eapply stp_and12. crush.
  crush. crush. crush. crush. eapply stp_and12. eapply stp_and11.
  eapply stp_mem. crush.
  eapply stp_bindx; try solve [simpl; reflexivity].
  eapply stp_and2. eapply stp_and11. crush. crush.  eapply stp_and12. crush. crush.
  crush. crush. crush. crush. crush. crush.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0.
Qed.
