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
    eapply (T_Obj GH G1 ds) with (T':=(dms_compute ds)); try solve [simpl; reflexivity]
end.

Ltac pick_stp_and c :=
  match goal with
    | [ |- stp ?GH ?G1 (TAnd ?T _) ?T ?n ] =>
      eapply stp_and11; c
    | [ |- stp ?GH ?G1 (TAnd _ ?T) ?T ?n ] =>
      eapply stp_and12; c
    | [ |- stp ?GH ?G1 (TAnd _ _) (TAnd _ _) ?n ] =>
      idtac
    | [ |- stp ?GH ?G1 (TAnd (TFun ?l _ _) _) (TFun ?l _ _) ?n ] =>
      eapply stp_and11; c
    | [ |- stp ?GH ?G1 (TAnd (TFun ?l _ _) _) _ ?n ] =>
      eapply stp_and12; c
    | [ |- stp ?GH ?G1 (TAnd (TMem ?l _ _) _) (TMem ?l _ _) ?n ] =>
      eapply stp_and11; c
    | [ |- stp ?GH ?G1 (TAnd (TMem ?l _ _) _) _ ?n ] =>
      eapply stp_and12; c
    | _ => idtac
  end.

Fixpoint compute_split_aux {X} (G: list X) (r: nat) :=
  match G with
    | [] => ([],[])
    | x::G => match r with
                | 0 => ([],x::G)
                | S r => match compute_split_aux G r with
                           | (GU,GL) => (x::GU,GL)
                         end
              end
  end.
Definition compute_split {X} (G: list X) (n: nat) :=
  compute_split_aux G ((length G)-(S n)).
Definition compute_GU {X} (G: list X) (n: nat) :=
  match (compute_split G n) with
    | (GU,GL) => GU
  end.
Definition compute_GL {X} (G: list X) (n: nat) :=
  match (compute_split G n) with
    | (GU,GL) => GL
  end.

Fixpoint rev_open (k: nat) (u: id) (T: ty) { struct T }: ty :=
  match T with
    | TVar false x => if beq_nat x u then TVarB k else TVar false x
    | TVar true x => TVar true x
    | TVarB i => TVarB i
    | TTop        => TTop
    | TBot        => TBot
    | TSel T1 l     => TSel (rev_open k u T1) l
    | TFun l T1 T2  => TFun l (rev_open k u T1) (rev_open (S k) u T2)
    | TMem l T1 T2  => TMem l (rev_open k u T1) (rev_open k u T2)
    | TBind T1    => TBind (rev_open (S k) u T1)
    | TAnd T1 T2  => TAnd (rev_open k u T1) (rev_open k u T2)
    | TOr T1 T2   => TOr (rev_open k u T1) (rev_open k u T2)
  end.

Ltac apply_htp_sub :=
  match goal with
    | [ |- htp ?GH ?G1 ?x ?T ?n ] =>
      eapply (htp_sub GH (compute_GU GH x) (compute_GL GH x))
  end.

Ltac apply_rev_open :=
  match goal with
    | [ |- ?T1 = open ?k (TVar false ?u) ?T2 ] =>
      try instantiate (1:=rev_open k u T1); simpl; reflexivity
  end.
  
Ltac crush := simpl;
  try solve [eapply T_Sub; [(apply_tobj; crush) | (crush)]];
  try solve [apply_dfun; crush];
  try solve [eapply stp_bot; crush];
  try solve [eapply stp_selx; crush];
  try solve [eapply stp_and2; crush];
  try solve [pick_stp_and crush];
  try solve [eapply stp_sel2; try solve [simpl; reflexivity]; crush];
  try solve [eapply stp_sel1; try solve [simpl; reflexivity]; crush];
  try solve [eapply stp_bindx; try solve [simpl; reflexivity]; crush];
  try solve [eapply stp_bind1; try solve [simpl; reflexivity]; crush];
  try solve [apply_rev_open];
  try solve [simpl; erewrite <- closed_no_open; try reflexivity; crush];
  try solve [apply_htp_sub; try solve [simpl; reflexivity];
             [eapply htp_var; crush | compute; repeat pick_stp_and; crush]];
  try solve [eapply T_App; try solve [simpl; reflexivity]; [idtac | crush | crush]; crush];
  try solve [econstructor; try solve [simpl; reflexivity]; crush];
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
apply 0. apply 0.
Qed.

(* define polymorphic identity function *)
Definition polyId := TFun 0 (TMem 0 TBot TTop) (TFun 0 (TSel (TVarB 0) 0) (TSel (TVarB 1) 0)).

Example ex1: has_typed
               [] []
               (tobj (dcons (tfun (TMem 0 TBot TTop) (TFun 0 (TSel (TVarB 0) 0) (TSel (TVarB 1) 0))
               (tobj (dcons (tfun (TSel (TVar false 1) 0) (TSel (TVar false 1) 0) (tvar false 3)) dnil))) dnil)) polyId.
Proof.
  compute. eexists. crush.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
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
apply 0. apply 0. apply 0.
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
  def nil() = new { this => type Elem = Bot; def head() = bot() }
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
Example paper_lst_hd_nil:
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
  compute. eexists. crush.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

Definition shift o v :=
  match v with
    | TVarB i => TVarB (o+i)
    | _ => v
  end.
(*
new { m =>
  type List = { this => type Elem; def tail(): m.List & { type Elem <: this.Elem } }
  def nil() = new { this => type Elem = Bot; def tail() = bot() }
} : { m =>
  type List <: { this => type Elem; def tail(): m.List & { type Elem <: this.Elem } }
  def nil(): List & { type Elem = Bot }
}
*)
Definition TLstTl o m EL EU :=
  (TBind (TAnd
    (*def tail(_:Top): m.List & { type Elem <: this.Elem } *)
    (TFun 1 TTop (TAnd (TSel (shift (o+2) m) 0) (TMem 0 TBot (TSel (TVarB 1) 0))))
    (*type Elem*) (TMem 0 EL EU)
  )).
Example paper_lst_tl_nil:
  has_typed [] []
    (lobj
       [(tfun
           TTop (TLstTl 1 (TVar false 0) TBot TBot)
           (lobj [(tfun TTop TBot (tapp (tvar false 2) 1 (tvar false 3)));
                   (dty TBot)]));
         (dty (TLstTl 0 (TVar false 0) TBot TTop))])
    (TBind (TAnd
              (TFun 1 TTop (TAnd (TSel (TVarB 1) 0) (TMem 0 TBot TBot)))
              (TMem 0 TBot (TLstTl 0 (TVarB 0) TBot TTop)))).
Proof.
  compute. eexists. crush.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0.
Qed.
