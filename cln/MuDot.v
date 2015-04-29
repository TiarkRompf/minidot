Set Implicit Arguments.

Require Import LibLN.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Definitions *)

(* ###################################################################### *)
(** ** Syntax *)

Parameter typ_label: Set.
Parameter mtd_label: Set.

Inductive label: Set :=
| label_typ: typ_label -> label
| label_mtd: mtd_label -> label.

Module labels.
  Parameter M: typ_label.
  Parameter m: mtd_label.
End labels.

Inductive avar: Set :=
  | avar_b: nat -> avar  (* bound var (de Bruijn index) *)
  | avar_f: var -> avar. (* free var ("name"), refers to tenv or venv *)

Inductive pth: Set :=
  | pth_var: avar -> pth.

Inductive typ: Set :=
  | typ_bind: decs -> typ
  | typ_sel: pth -> typ_label -> typ
with dec: Set :=
  | dec_typ : typ_label -> typ -> typ -> dec
  | dec_tyu : typ_label -> typ -> dec
  | dec_mtd : mtd_label -> typ -> typ -> dec
with decs: Set :=
  | decs_nil : decs
  | decs_cons: dec -> decs -> decs.

Inductive trm: Set :=
  | trm_var : avar -> trm
  | trm_new : defs -> trm
  | trm_call: trm -> mtd_label -> trm -> trm
with def: Set :=
  | def_typ: typ_label -> typ -> typ -> def
  | def_tyu: typ_label -> typ -> def
  | def_mtd: mtd_label -> typ -> typ -> trm -> def
with defs: Set :=
  | defs_nil : defs
  | defs_cons: def -> defs -> defs.

Inductive ctyp: Type :=
  | typ_clo: env ctyp -> typ -> ctyp.

Definition ctx := env ctyp.

(* ###################################################################### *)
(** ** Definition list membership *)

Definition label_of_def(d: def): label := match d with
| def_typ M _ _ => label_typ M
| def_tyu M _ => label_typ M
| def_mtd m _ _ _ => label_mtd m
end.

Definition label_of_dec(D: dec): label := match D with
| dec_typ M _ _ => label_typ M
| dec_tyu M _ => label_typ M
| dec_mtd m _ _ => label_mtd m
end.

Inductive defs_hasnt: defs -> label -> Prop :=
| defs_hasnt_nil: forall l,
    defs_hasnt defs_nil l
| defs_hasnt_cons: forall d ds l,
    defs_hasnt ds l ->
    label_of_def d <> l ->
    defs_hasnt (defs_cons d ds) l.

Inductive defs_has: defs -> def -> Prop :=
| defs_has_hit: forall d ds,
    defs_hasnt ds (label_of_def d) ->
    defs_has (defs_cons d ds) d
| defs_has_skip: forall d1 d2 ds,
    defs_has ds d1 ->
    label_of_def d2 <> label_of_def d1 ->
    defs_has (defs_cons d2 ds) d1.

Inductive decs_hasnt: decs -> label -> Prop :=
| decs_hasnt_nil: forall l,
    decs_hasnt decs_nil l
| decs_hasnt_cons: forall D Ds l,
    decs_hasnt Ds l ->
    label_of_dec D <> l ->
    decs_hasnt (decs_cons D Ds) l.

Inductive decs_has: decs -> dec -> Prop :=
| decs_has_hit: forall D Ds,
    decs_hasnt Ds (label_of_dec D) ->
    decs_has (decs_cons D Ds) D
| decs_has_skip: forall D1 D2 Ds,
    decs_has Ds D1 ->
    label_of_dec D2 <> label_of_dec D1 ->
    decs_has (decs_cons D2 Ds) D1.


(* ###################################################################### *)
(** ** Opening *)

(** Opening replaces in some syntax a bound variable with dangling index (k)
   by a free variable x. *)

Definition open_rec_avar (k: nat) (u: var) (a: avar): avar :=
  match a with
  | avar_b i => If k = i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Definition open_rec_pth (k: nat) (u: var) (p: pth): pth :=
  match p with
  | pth_var a => pth_var (open_rec_avar k u a)
  end.

Fixpoint open_rec_typ (k: nat) (u: var) (T: typ) { struct T }: typ :=
  match T with
  | typ_bind Ds => typ_bind (open_rec_decs (S k) u Ds)
  | typ_sel p M => typ_sel (open_rec_pth k u p) M
  end
with open_rec_dec (k: nat) (u: var) (D: dec) { struct D }: dec :=
  match D with
  | dec_typ M T U => dec_typ M (open_rec_typ k u T) (open_rec_typ k u U)
  | dec_tyu M U => dec_tyu M (open_rec_typ k u U)
  | dec_mtd m T U => dec_mtd m (open_rec_typ k u T) (open_rec_typ k u U)
  end
with open_rec_decs (k: nat) (u: var) (Ds: decs) { struct Ds }: decs :=
  match Ds with
  | decs_nil        => decs_nil
  | decs_cons D Ds' => decs_cons (open_rec_dec k u D) (open_rec_decs k u Ds')
  end.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm) { struct t }: trm :=
  match t with
  | trm_var a      => trm_var (open_rec_avar k u a)
  | trm_new ds     => trm_new (open_rec_defs (S k) u ds)
  | trm_call o m a => trm_call (open_rec_trm k u o) m (open_rec_trm k u a)
  end
with open_rec_def (k: nat) (u: var) (d: def) { struct d }: def :=
  match d with
  | def_typ M T U => def_typ M (open_rec_typ k u T) (open_rec_typ k u U)
  | def_tyu M U => def_tyu M (open_rec_typ k u U)
  | def_mtd m T U e => def_mtd m (open_rec_typ k u T) (open_rec_typ k u U) (open_rec_trm (S k) u e)
  end
with open_rec_defs (k: nat) (u: var) (ds: defs) { struct ds }: defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons d tl => defs_cons (open_rec_def k u d) (open_rec_defs k u tl)
  end.

Definition open_avar u a := open_rec_avar  0 u a.
Definition open_pth  u p := open_rec_pth   0 u p.
Definition open_typ  u t := open_rec_typ   0 u t.
Definition open_dec  u d := open_rec_dec   0 u d.
Definition open_decs u l := open_rec_decs  0 u l.
Definition open_trm  u e := open_rec_trm   0 u e.
Definition open_def  u d := open_rec_def   0 u d.
Definition open_defs u l := open_rec_defs  0 u l.


(* ###################################################################### *)
(** ** Free variables *)

Definition fv_avar (a: avar): vars :=
  match a with
  | avar_b i => \{}
  | avar_f x => \{x}
  end.

Definition fv_pth (p: pth): vars :=
  match p with
  | pth_var a => fv_avar a
  end.

Fixpoint fv_typ (T: typ) { struct T }: vars :=
  match T with
  | typ_bind Ds => fv_decs Ds
  | typ_sel p M => fv_pth p
  end
with fv_dec (D: dec) { struct D }: vars :=
  match D with
  | dec_typ _ T U => (fv_typ T) \u (fv_typ U)
  | dec_tyu _ T   => (fv_typ T)
  | dec_mtd _ T U => (fv_typ T) \u (fv_typ U)
  end
with fv_decs (Ds: decs) { struct Ds }: vars :=
  match Ds with
  | decs_nil          => \{}
  | decs_cons D Ds' => (fv_dec D) \u (fv_decs Ds')
  end.

Fixpoint fv_trm (t: trm): vars :=
  match t with
  | trm_var x        => (fv_avar x)
  | trm_new ds       => (fv_defs ds)
  | trm_call t1 m t2 => (fv_trm t1) \u (fv_trm t2)
  end
with fv_def (d: def): vars :=
  match d with
  | def_typ _ T U => (fv_typ T) \u (fv_typ U)
  | def_tyu _ U => (fv_typ U)
  | def_mtd _ T U u => (fv_typ T) \u (fv_typ U) \u (fv_trm u)
  end
with fv_defs(ds: defs): vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons d tl   => (fv_defs tl) \u (fv_def d)
  end.

Definition fv_ctx_types(G: ctx): vars := (fv_in_values (fun ct => match ct with typ_clo _ T => fv_typ T end) G).

(* ###################################################################### *)
(** ** Evaluation *)

Inductive val: Type :=
  | val_clo: env val -> defs -> val.

Definition vctx := env val.

Definition fv_ctx_values(H: vctx): vars := (fv_in_values (fun v => match v with val_clo _ ds => fv_defs ds end) H).

Inductive ev: vctx -> trm -> val -> Prop :=
| ev_var: forall H x v,
  binds x v H ->
  ev H (trm_var (avar_f x)) v
| ev_new: forall H ds,
  ev H (trm_new ds) (val_clo H ds)
| ev_call: forall H e1 m e2 H1 x1 ds1 body v2 x2 T1 T2 v,
  ev H e1 (val_clo H1 ds1) ->
  ev H e2 v2 ->
  x1 # H1 ->
  defs_has (open_defs x1 ds1) (def_mtd m T1 T2 body) ->
  x2 # H1 ->
  x2 <> x1 ->
  ev (H1 & (x1 ~ (val_clo H1 ds1)) & (x2 ~ v2)) (open_trm x2 body) v ->
  ev H (trm_call e1 m e2) v
.

(* ###################################################################### *)
(** ** Tactics *)

Ltac auto_specialize :=
  repeat match goal with
  | Impl: ?Cond ->            _ |- _ => let HC := fresh in
      assert (HC: Cond) by auto; specialize (Impl HC); clear HC
  | Impl: forall (_: ?Cond), _ |- _ => match goal with
      | p: Cond |- _ => specialize (Impl p)
      end
  end.

Ltac gather_vars :=
  let A := gather_vars_with (fun x: vars      => x         ) in
  let B := gather_vars_with (fun x: var       => \{ x }    ) in
  let C := gather_vars_with (fun x: ctx       => (dom x) \u (fv_ctx_types x)) in
  let D := gather_vars_with (fun x: vctx      => (dom x) \u (fv_ctx_values x)) in
  let E := gather_vars_with (fun x: avar      => fv_avar  x) in
  let F := gather_vars_with (fun x: trm       => fv_trm   x) in
  let G := gather_vars_with (fun x: def       => fv_def   x) in
  let H := gather_vars_with (fun x: defs      => fv_defs  x) in
  let I := gather_vars_with (fun x: typ       => fv_typ   x) in
  let J := gather_vars_with (fun x: dec       => fv_dec   x) in
  let K := gather_vars_with (fun x: decs      => fv_decs  x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

(* ###################################################################### *)
(** ** Examples of Evaluation *)

Module EvExamples.

Definition typ_top := typ_bind decs_nil.
Definition m := labels.m.
Definition t0 := (trm_new defs_nil).
Definition v0 := (val_clo empty defs_nil).
Definition fm t := (trm_new (defs_cons (def_mtd m typ_top typ_top t) defs_nil)).
Definition vm t := (val_clo empty (defs_cons (def_mtd m typ_top typ_top t) defs_nil)).
Definition fi i := fm (trm_var (avar_b i)).
Definition vi i := vm (trm_var (avar_b i)).

Example ev1:
  ev empty t0 v0.
Proof.
  apply ev_new.
Qed.

Example ev2:
  ev empty (trm_call (fi 0) m t0) v0.
Proof.
  pick_fresh x1. pick_fresh x2.
  eapply ev_call with (x1:=x1) (x2:=x2) (H1:=empty); auto.
  apply ev_new.
  apply ev_new.
  unfold open_defs. simpl. apply defs_has_hit. apply defs_hasnt_nil.
  erewrite If_r; auto. compute. erewrite If_l; auto.
  apply ev_var; auto.
Qed.

Example ev3:
  ev empty (trm_call (fi 1) m t0) (vi 1).
Proof.
  pick_fresh x1. pick_fresh x2.
  eapply ev_call with (x1:=x1) (x2:=x2) (H1:=empty); auto.
  apply ev_new.
  apply ev_new.
  unfold open_defs. simpl. apply defs_has_hit. apply defs_hasnt_nil.
  erewrite If_l; auto. compute.
  apply ev_var; auto.
Qed.

Example ev4:
  exists x1 x2,
  ev empty (trm_call (fm t0) m t0)
     (val_clo (empty & (x1 ~ (vm t0)) & (x2 ~ v0)) defs_nil)
  .
Proof.
  pick_fresh x1. pick_fresh x2. exists x1 x2.
  eapply ev_call with (x1:=x1) (x2:=x2) (H1:=empty); auto.
  apply ev_new.
  apply ev_new.
  unfold open_defs. simpl. apply defs_has_hit. apply defs_hasnt_nil.
  compute. apply ev_new.
Qed.

End EvExamples.

(* ###################################################################### *)
(** ** Typing *)

Fixpoint def_to_dec (d: def): dec :=
  match d with
  | def_typ M TL TU => dec_typ M TL TU
  | def_tyu M TU => dec_tyu M TU
  | def_mtd m T1 T2 t => dec_mtd m T1 T2
  end
.
Fixpoint defs_to_decs (ds: defs): decs :=
  match ds with
  | defs_nil => decs_nil
  | defs_cons d ds => decs_cons (def_to_dec d) (defs_to_decs ds)
  end
.

Inductive same_typ: ctx -> typ -> typ -> ctx -> Prop :=
| same_rfl: forall G T,
  same_typ G T T G
| same_sel: forall G1 G2 x1 x2 M Gx1 Tx1 Gx2 Tx2,
  binds x1 (typ_clo Gx1 Tx1) G1 ->
  binds x2 (typ_clo Gx2 Tx2) G2 ->
  same_typ Gx1 Tx1 Tx2 Gx2 ->
  same_typ G1
           (typ_sel (pth_var (avar_f x1)) M)
           (typ_sel (pth_var (avar_f x2)) M)
           G2
| same_bind: forall G Ds,
  (* TODO: do we need to go in there? *)
  same_typ G (typ_bind Ds) (typ_bind Ds) G
.

Inductive stp: bool -> ctx -> typ -> typ -> ctx -> Prop :=
| stp_sel2: forall G1 T1 G2 p M TL TU Gp,
  pth_has G2 p (dec_typ M TL TU) Gp ->
  stp true Gp TL TU Gp ->
  stp true G1 T1 TL Gp ->
  stp true G1 T1 (typ_sel p M) G2
| stp_sel1: forall G1 G2 T2 p M TL TU Gp,
  pth_has G1 p (dec_typ M TL TU) Gp ->
  stp true Gp TL TU Gp ->
  stp true Gp TU T2 G2 ->
  stp true G1 (typ_sel p M) T2 G2
| stp_sel1u: forall G1 G2 T2 p M TU Gp,
  pth_has G1 p (dec_tyu M TU) Gp ->
  stp true Gp TU T2 G2 ->
  stp true G1 (typ_sel p M) T2 G2
| stp_selx: forall G1 G2 p1 p2 M TL1 TU1 TL2 TU2 Gp1 Gp2,
  pth_has G1 p1 (dec_typ M TL1 TU1) Gp1 ->
  pth_has G2 p2 (dec_typ M TL2 TU2) Gp2 ->
  stp true Gp1 TL1 TU1 Gp1 ->
  stp true Gp2 TL2 TU2 Gp2 ->
  same_typ Gp2 TL2 TL1 Gp1 ->
  same_typ Gp1 TU1 TU2 Gp2 ->
  stp true G1 (typ_sel p1 M) (typ_sel p2 M) G2
| stp_selxu: forall G1 G2 p1 p2 M TU1 TU2 Gp1 Gp2,
  pth_has G1 p1 (dec_tyu M TU1) Gp1 ->
  pth_has G2 p2 (dec_tyu M TU2) Gp2 ->
  wf_typ Gp1 TU1 ->
  wf_typ Gp2 TU2 ->
  same_typ Gp1 TU1 TU2 Gp2 ->
  stp true G1 (typ_sel p1 M) (typ_sel p2 M) G2
| stp_bind: forall L G1 Ds1 G2 Ds2,
  wf_typ G2 (typ_bind Ds2) ->
  (forall x, x \notin L ->
   sdcs (G1 & (x ~ typ_clo G1 (typ_bind Ds1)))
        (open_decs x Ds1)
        (open_decs x Ds2)
        (G2 & (x ~ typ_clo G1 (typ_bind Ds1)))
  ) ->
  stp true G1 (typ_bind Ds1) (typ_bind Ds2) G2
| stp_transf: forall G1 G2 G3 T1 T2 T3,
  stp true G1 T1 T2 G2 ->
  stp false G2 T2 T3 G3 ->
  stp false G1 T1 T3 G3
| stp_wrapf: forall G1 G2 T1 T2,
  stp true G1 T1 T2 G2 ->
  stp false G1 T1 T2 G2

with sdc: ctx -> dec -> dec -> ctx -> Prop :=
| sdc_typ: forall G1 G2 M TL1 TL2 TU1 TU2,
  stp true G1 TL1 TU1 G1 ->
  stp true G2 TL2 TU2 G2 ->
  stp false G2 TL2 TL1 G1 ->
  stp true G1 TU1 TU2 G2 ->
  sdc G1 (dec_typ M TL1 TU1) (dec_typ M TL2 TU2) G2
| sdc_tyu: forall G1 G2 M TU1 TU2,
  stp true G1 TU1 TU2 G2 ->
  sdc G1 (dec_tyu M TU1) (dec_tyu M TU2) G2
| sdc_typu: forall G1 G2 M TL1 TU1 TU2,
  stp true G1 TL1 TU1 G1 ->
  stp true G1 TU1 TU2 G2 ->
  sdc G1 (dec_typ M TL1 TU1) (dec_tyu M TU2) G2
| sdc_mtd: forall G1 G2 m TL1 TL2 TU1 TU2,
  stp false G2 TL2 TL1 G1 ->
  stp true G1 TU1 TU2 G2 ->
  sdc G1 (dec_mtd m TL1 TU1) (dec_mtd m TL2 TU2) G2

with sdcs: ctx -> decs -> decs -> ctx -> Prop :=
| sdcs_nil: forall G1 Ds1 G2,
  wf_decs G1 Ds1 ->
  sdcs G1 Ds1 decs_nil G2
| sdcs_cons: forall G1 Ds1 G2 Ds2 D1 D2,
  decs_has Ds1 D1 ->
  sdc G1 D1 D2 G2 ->
  sdcs G1 Ds1 Ds2 G2 ->
  decs_hasnt Ds2 (label_of_dec D2) ->
  sdcs G1 Ds1 (decs_cons D2 Ds2) G2

with wf_typ: ctx -> typ -> Prop :=
| wf_sel: forall G p M TL TU Gp,
  pth_has G p (dec_typ M TL TU) Gp ->
  stp true Gp TL TU Gp ->
  wf_typ G (typ_sel p M)
| wf_selu: forall G p M TU Gp,
  pth_has G p (dec_tyu M TU) Gp ->
  wf_typ Gp TU ->
  wf_typ G (typ_sel p M)
| wf_bind: forall L G Ds,
  (forall x, x \notin L ->
   wf_decs (G & (x ~ typ_clo G (typ_bind Ds)))
           (open_decs x Ds)
  ) ->
  wf_typ G (typ_bind Ds)

with wf_dec: ctx -> dec -> Prop :=
| wf_dec_typ: forall G M TL TU,
  stp true G TL TU G ->
  wf_dec G (dec_typ M TL TU)
| wf_dec_tyu: forall G M TU,
  wf_typ G TU ->
  wf_dec G (dec_tyu M TU)
| wf_dec_mtd: forall G m TL TU,
  wf_typ G TL ->
  wf_typ G TU ->
  wf_dec G (dec_mtd m TL TU)

with wf_decs: ctx -> decs -> Prop :=
| wf_decs_nil: forall G,
  wf_decs G decs_nil
| wf_decs_cons: forall G Ds D,
  wf_dec G D ->
  wf_decs G Ds ->
  decs_hasnt Ds (label_of_dec D) ->
  wf_decs G (decs_cons D Ds)

with exp: ctx -> typ -> decs -> ctx -> Prop :=
| exp_bind: forall G Ds,
  exp G (typ_bind Ds) Ds G
| exp_sel: forall G G' G'' p M TL TU Ds,
  pth_has G p (dec_typ M TL TU) G' ->
  exp G' TU Ds G'' ->
  exp G (typ_sel p M) Ds G''
with pth_has: ctx -> pth -> dec -> ctx -> Prop :=
| pth_has_any: forall G x Gx Tx Ds D G' x',
  binds x (typ_clo Gx Tx) G ->
  exp Gx Tx Ds G' ->
  decs_has Ds D ->
  x' # G' ->
  pth_has G (pth_var (avar_f x)) (open_dec x' D) (G' & (x' ~ (typ_clo Gx Tx)))
.

Inductive tc_trm: ctx -> trm -> typ -> Prop :=
| tc_var: forall G T x Gx Tx,
  binds x (typ_clo Gx Tx) G ->
  stp true Gx Tx T G ->
  tc_trm G (trm_var (avar_f x)) T
| tc_new: forall L G ds Ds,
  defs_to_decs ds = Ds ->
  (forall z, z \notin L ->
   tc_defs (G & (z ~ (typ_clo G (typ_bind Ds))))
           (open_defs z ds) (open_decs z Ds)
  ) ->
  tc_trm G (trm_new ds) (typ_bind Ds)
| tc_call: forall G t1 m t2 T2 T,
  trm_has G t1 (dec_mtd m T2 T) ->
  tc_trm G t2 T2 ->
  tc_trm G (trm_call t1 m t2) T
| tc_sub: forall G t T TU,
  tc_trm G t T ->
  stp true G T TU G ->
  tc_trm G t TU
with tc_def: ctx -> def -> dec -> Prop :=
| tc_def_typ: forall G M TL TU,
  stp true G TL TU G ->
  tc_def G (def_typ M TL TU) (dec_typ M TL TU)
| tc_def_tyu: forall G M TU,
  wf_typ G TU ->
  tc_def G (def_tyu M TU) (dec_tyu M TU)
| tc_def_mtd: forall L G m T1 T2 t,
  wf_typ G T1 ->
  (forall x, x \notin L ->
   tc_trm (G & (x ~ (typ_clo G T1)))
          (open_trm x t) T2
  ) ->
  tc_def G (def_mtd m T1 T2 t) (dec_mtd m T1 T2)
with trm_has: ctx -> trm -> dec -> Prop :=
| trm_has_var: forall G x D Gp Dp,
  pth_has G (pth_var (avar_f x)) Dp Gp ->
  sdc Gp Dp D G ->
  trm_has G (trm_var (avar_f x)) D
| trm_has_trm: forall L G G' t T Ds D,
  tc_trm G t T ->
  exp G T Ds G' ->
  decs_has Ds D ->
  (forall x, x \notin L ->
   x \notin fv_dec (open_dec x D)
  ) ->
  sdc G' D D G ->
  trm_has G t D
with tc_defs: ctx -> defs -> decs -> Prop :=
| tc_defs_nil: forall G,
  tc_defs G defs_nil decs_nil
| tc_defs_cons: forall G d ds D Ds,
  tc_def G d D ->
  tc_defs G ds Ds ->
  tc_defs G (defs_cons d ds) (decs_cons D Ds)
.

Inductive tc_val: val -> ctyp -> Prop :=
| tc_val_clo: forall L H ds G Ds,
  tc_ctx H G ->
  Ds = defs_to_decs ds ->
  (forall z, z \notin L ->
   tc_defs (G & (z ~ (typ_clo G (typ_bind Ds))))
           (open_defs z ds) (open_decs z Ds)
  ) ->
  tc_val (val_clo H ds) (typ_clo G (typ_bind Ds))
with tc_ctx: vctx -> ctx -> Prop :=
| tc_ctx_empty:
  tc_ctx empty empty
| tc_ctx_rec: forall H G x v CT,
  tc_val v CT ->
  tc_ctx H G ->
  tc_ctx (H & (x ~ v)) (G & (x ~ CT))
.

Inductive wf_val: ctx -> val -> typ -> Prop :=
| wf_val_any: forall G v T Gv Tv,
  tc_val v (typ_clo Gv Tv) ->
  stp true Gv Tv T G ->
  wf_val G v T
.

(* ###################################################################### *)
(** ** Induction principles *)

Scheme stp_mut_sub  := Induction for stp  Sort Prop
with   sdc_mut_sub  := Induction for sdc  Sort Prop
with   sdcs_mut_sub := Induction for sdcs Sort Prop.
Combined Scheme sub_mutind from stp_mut_sub, sdc_mut_sub, sdcs_mut_sub.

Scheme wf_typ_mut_wf  := Induction for wf_typ  Sort Prop
with   wf_dec_mut_wf  := Induction for wf_dec  Sort Prop
with   wf_decs_mut_wf := Induction for wf_decs Sort Prop.
Combined Scheme wf_mutind from wf_typ_mut_wf, wf_dec_mut_wf, wf_decs_mut_wf.

Scheme stp_mut_sw  := Induction for stp  Sort Prop
with   sdc_mut_sw  := Induction for sdc  Sort Prop
with   sdcs_mut_sw := Induction for sdcs Sort Prop
with   wf_typ_mut_sw  := Induction for wf_typ  Sort Prop
with   wf_dec_mut_sw  := Induction for wf_dec  Sort Prop
with   wf_decs_mut_sw := Induction for wf_decs Sort Prop.
Combined Scheme sw_mutind from stp_mut_sw, sdc_mut_sw, sdcs_mut_sw, wf_typ_mut_sw, wf_dec_mut_sw, wf_decs_mut_sw.

Scheme stp_mut_sa  := Induction for stp  Sort Prop
with   sdc_mut_sa  := Induction for sdc  Sort Prop
with   sdcs_mut_sa := Induction for sdcs Sort Prop
with   wf_typ_mut_sa  := Induction for wf_typ  Sort Prop
with   wf_dec_mut_sa  := Induction for wf_dec  Sort Prop
with   wf_decs_mut_sa := Induction for wf_decs Sort Prop
with   exp_mut_sa     := Induction for exp Sort Prop
with   pth_has_mut_sa := Induction for pth_has Sort Prop.
Combined Scheme sa_mutind from stp_mut_sa, sdc_mut_sa, sdcs_mut_sa, wf_typ_mut_sa, wf_dec_mut_sa, wf_decs_mut_sa, exp_mut_sa, pth_has_mut_sa.

(* ###################################################################### *)
(** ** Properties *)

Theorem sub_reg:
  (forall b G1 T1 T2 G2, stp b G1 T1 T2 G2 -> wf_typ G1 T1 /\ wf_typ G2 T2) /\
  (forall G1 D1 D2 G2, sdc G1 D1 D2 G2 -> wf_dec G1 D1 /\ wf_dec G2 D2) /\
  (forall G1 Ds1 Ds2 G2, sdcs G1 Ds1 Ds2 G2 -> wf_decs G1 Ds1 /\ wf_decs G2 Ds2).
Proof.
  apply sub_mutind; intros.
  - (* T1 <: p.M -- sel2 *)
    split.
    + inversion H0. assumption.
    + eapply wf_sel. apply p0. assumption.
  - (* p.M <: T2 -- sel1 *)
    split.
    + eapply wf_sel. apply p0. assumption.
    + inversion H0. assumption.
  - (* p.M <: T2 -- sel1u *)
    split.
    + eapply wf_selu. apply p0. inversion H. assumption.
    + inversion H. assumption.
  - (* p.M <: p.M -- selx *)
    split.
    + eapply wf_sel. apply p. assumption.
    + eapply wf_sel. apply p0. assumption.
  - (* p.M <: p.M -- selxu *)
    split.
    + eapply wf_selu. apply p. assumption.
    + eapply wf_selu. apply p0. assumption.
  - (* bind *)
    split.
    + apply wf_bind with (L:=L). intros x Frx.
      specialize (H x Frx). inversion H. assumption.
    + assumption.
  - (* transf *)
    split.
    + inversion H. assumption.
    + inversion H0. assumption.
  - (* wrapf *)
    assumption.
  - (* typ *)
    split.
    + apply wf_dec_typ. assumption.
    + apply wf_dec_typ. assumption.
  - (* tyu *)
    split.
    + apply wf_dec_tyu. inversion H. assumption.
    + apply wf_dec_tyu. inversion H. assumption.
  - (* typu *)
    split.
    + apply wf_dec_typ. assumption.
    + apply wf_dec_tyu. inversion H0. assumption.
  - (* mtd *)
    split.
    + apply wf_dec_mtd. inversion H. assumption. inversion H0. assumption.
    + apply wf_dec_mtd. inversion H. assumption. inversion H0. assumption.
  - (* Ds1 <: {} -- nil *)
    split.
    + assumption.
    + apply wf_decs_nil.
  - (* Ds1 <: D2::Ds2 -- cons *)
    split.
    + inversion H0. assumption.
    + apply wf_decs_cons.
        inversion H. assumption.
        inversion H0. assumption.
        assumption.
Qed.

Definition stp_reg := proj1 sub_reg.
Definition sdc_reg := proj1 (proj2 sub_reg).
Definition sdcs_reg := proj2 (proj2 sub_reg).

Lemma stp_reg1: forall b G1 T1 T2 G2,
  stp b G1 T1 T2 G2 ->
  wf_typ G1 T1.
Proof.
  intros b G1 T1 T2 G2 H.
  apply (proj1 (stp_reg H)).
Qed.

Lemma sdc_reg2: forall G1 D1 D2 G2,
  sdc G1 D1 D2 G2 ->
  wf_dec G2 D2.
Proof.
  intros G1 Ds1 Ds2 G2 H.
  apply (proj2 (sdc_reg H)).
Qed.

Lemma sdcs_reg1: forall G1 Ds1 Ds2 G2,
  sdcs G1 Ds1 Ds2 G2 ->
  wf_decs G1 Ds1.
Proof.
  intros G1 Ds1 Ds2 G2 H.
  apply (proj1 (sdcs_reg H)).
Qed.

Lemma decs_has_or_hasnt: forall Ds D D',
  decs_hasnt Ds (label_of_dec D) ->
  decs_has Ds D' ->
  label_of_dec D <> label_of_dec D'.
Proof.
  intros Ds D D' H H'.
  induction H.
  + inversion H'.
  + inversion H'; subst.
    - congruence.
    - apply IHdecs_hasnt. assumption.
Qed.

Lemma sdcs_cons1: forall G1 Ds1 Ds2 G2 D1,
  sdcs G1 Ds1 Ds2 G2 ->
  wf_dec G1 D1 ->
  decs_hasnt Ds1 (label_of_dec D1) ->
  sdcs G1 (decs_cons D1 Ds1) Ds2 G2.
Proof.
  intros.
  induction H.
  + apply sdcs_nil. apply wf_decs_cons; assumption.
  + apply sdcs_cons with (D1:=D0).
    - apply decs_has_skip. assumption.
      apply decs_has_or_hasnt with (Ds:=Ds1); assumption.
    - assumption.
    - apply IHsdcs. assumption. assumption.
    - assumption.
Qed.

Theorem sub_refl:
  (forall b G1 T1 T2 G2, stp b G1 T1 T2 G2 -> stp b G1 T1 T1 G1 /\ stp b G2 T2 T2 G2) /\
  (forall G1 D1 D2 G2, sdc G1 D1 D2 G2 -> sdc G1 D1 D1 G1 /\ sdc G2 D2 D2 G2) /\
  (forall G1 Ds1 Ds2 G2, sdcs G1 Ds1 Ds2 G2 -> sdcs G1 Ds1 Ds1 G1 /\ sdcs G2 Ds2 Ds2 G2) /\
  (forall G T, wf_typ G T -> stp true G T T G) /\
  (forall G D, wf_dec G D -> sdc G D D G) /\
  (forall G Ds, wf_decs G Ds -> sdcs G Ds Ds G).
Proof.
  apply sw_mutind; intros.
  - (* T1 <: p.M -- sel2 *)
    split.
    + inversion H0. assumption.
    + eapply stp_selx.
      apply p0. apply p0.
      assumption. assumption.
      apply same_rfl. apply same_rfl.
  - (* p.M <: T2 -- sel1 *)
    split.
    + eapply stp_selx.
      apply p0. apply p0.
      assumption. assumption.
      apply same_rfl. apply same_rfl.
    + inversion H0. assumption.
  - (* p.M <: T2 -- sel1u *)
    split.
    + eapply stp_selxu.
      apply p0. apply p0.
      inversion H. eapply stp_reg1. apply H0.
      inversion H. eapply stp_reg1. apply H0.
      apply same_rfl.
    + inversion H. assumption.
  - (* p.M <: p.M -- selx *)
    split.
    + eapply stp_selx.
      apply p. apply p.
      assumption. assumption.
      apply same_rfl. apply same_rfl.
    + eapply stp_selx.
      apply p0. apply p0.
      assumption. assumption.
      apply same_rfl. apply same_rfl.
  - (* p.M <: p.M -- selxu *)
    split.
    + eapply stp_selxu.
      apply p. apply p.
      assumption. assumption.
      apply same_rfl.
    + eapply stp_selxu.
      apply p0. apply p0.
      assumption. assumption.
      apply same_rfl.
  - (* bind *)
    split.
    + apply stp_bind with (L:=L).
      apply wf_bind with (L:=L).
      intros x Frx. eapply sdcs_reg1. specialize (s x Frx). apply s.
      intros x Frx. specialize (H0 x Frx). inversion H0. assumption.
    + assumption.
  - (* transf *)
    split.
    + inversion H. apply stp_wrapf. assumption.
    + inversion H0. assumption.
  - (* wrapf *)
    split.
    + inversion H. apply stp_wrapf. assumption.
    + inversion H. apply stp_wrapf. assumption.
  - (* sdc_typ *)
    split.
    + apply sdc_typ; try assumption.
      inversion H1. assumption.
      inversion H. assumption.
    + apply sdc_typ; try assumption.
      inversion H1. assumption.
      inversion H0. assumption.
  - (* sdc_tyu *)
    split.
    + apply sdc_tyu. inversion H. assumption.
    + apply sdc_tyu. inversion H. assumption.
  - (* sdc_typu *)
    split.
    + apply sdc_typ; try assumption.
      inversion H. apply stp_wrapf. assumption.
      inversion H. assumption.
    + apply sdc_tyu. inversion H0. assumption.
  - (* sdc_mtd *)
    split.
    + apply sdc_mtd. inversion H. assumption. inversion H0. assumption.
    + apply sdc_mtd. inversion H. assumption. inversion H0. assumption.
  - (* Ds1 <: {} -- nil *)
    split.
    + assumption.
    + apply sdcs_nil. apply wf_decs_nil.
  - (* Ds1 <: D2::Ds2 -- cons *)
    split.
    + inversion H0. assumption.
    + apply sdcs_cons with (D1:=D2).
        apply decs_has_hit. assumption.
        inversion H. assumption.
        apply sdcs_cons1.
          inversion H0. assumption.
          eapply sdc_reg2. apply s.
          assumption.
          assumption.
  - (* wf_sel *)
    apply stp_selx with (TL1:=TL) (TL2:=TL) (TU1:=TU) (TU2:=TU) (Gp1:=Gp) (Gp2:=Gp);
    try assumption; try solve [apply same_rfl].
  - (* wf_selu *)
    apply stp_selxu with (TU1:=TU) (TU2:=TU) (Gp1:=Gp) (Gp2:=Gp);
    try assumption; try solve [apply same_rfl].
  - (* wf_bind *)
    apply stp_bind with (L:=L); try assumption.
    apply wf_bind with (L:=L); assumption.
  - (* wf_dec_typ *)
    inversion H.
    apply sdc_typ; try assumption.
    apply stp_wrapf. assumption.
  - (* wf_dec_tyu *)
    apply sdc_tyu; try assumption.
  - (* wf_dec_mtd *)
    apply sdc_mtd; try assumption.
    apply stp_wrapf. assumption.
  - (* wf_decs_nil *)
    apply sdcs_nil. apply wf_decs_nil.
  - (* wf_decs_cons *)
    apply sdcs_cons with (D1:=D); try assumption.
    + apply decs_has_hit. assumption.
    + apply sdcs_cons1; try assumption.
Qed.

Theorem sub_extending:
  (forall b G1 T1 T2 G2, stp b G1 T1 T2 G2 ->
   forall G1A G1B G1C G2A G2B G2C,
     G1 = G1A & G1C ->
     G2 = G2A & G2C ->
     stp b (G1A & G1B & G1C) T1 T2 (G2A & G2B & G2C)
  ) /\
  (forall G1 D1 D2 G2, sdc G1 D1 D2 G2 ->
   forall G1A G1B G1C G2A G2B G2C,
     G1 = G1A & G1C ->
     G2 = G2A & G2C ->
     sdc (G1A & G1B & G1C) D1 D2 (G2A & G2B & G2C)
  ) /\
  (forall G1 Ds1 Ds2 G2, sdcs G1 Ds1 Ds2 G2 ->
   forall G1A G1B G1C G2A G2B G2C,
     G1 = G1A & G1C ->
     G2 = G2A & G2C ->
     sdcs (G1A & G1B & G1C) Ds1 Ds2 (G2A & G2B & G2C)
  ) /\
  (forall G T, wf_typ G T ->
   forall GA GB GC,
     G = GA & GC ->
     wf_typ (GA & GB & GC) T
  ) /\
  (forall G D, wf_dec G D ->
   forall GA GB GC,
     G = GA & GC ->
     wf_dec (GA & GB & GC) D
  ) /\
  (forall G Ds, wf_decs G Ds ->
   forall GA GB GC,
     G = GA & GC ->
     wf_decs (GA & GB & GC) Ds
  ) /\
  (forall G T Ds G', exp G T Ds G' ->
   forall GA GB GC GA' GB' GC',
     G = GA & GC ->
     G' = GA' & GC' ->
     exp (GA & GB & GC) T Ds (GA' & GB' & GC')
  ) /\
  (forall G p D Gp, pth_has G p D Gp ->
   forall GA GB GC GAp GBp GCp,
     G = GA & GC ->
     Gp = GAp & GCp ->
     pth_has (GA & GB & GC) p D (GAp & GBp & GCp)
  ).
Proof.
  apply sa_mutind; intros.
  - (* stp_sel2 *)
    apply stp_sel2 with (TL:=TL) (TU:=TU) (Gp:= Gp & empty & empty); auto.
    apply H; try assumption.
    rewrite concat_empty_r. reflexivity.
    rewrite concat_empty_r. rewrite concat_empty_r. assumption.
    apply H1; try assumption.
    rewrite concat_empty_r. reflexivity.
  - (* stp_sel1 *)
    apply stp_sel1 with (TL:=TL) (TU:=TU) (Gp:= Gp & empty & empty); auto.
    apply H; try assumption.
    rewrite concat_empty_r. reflexivity.
    rewrite concat_empty_r. rewrite concat_empty_r. assumption.
    apply H1; try assumption.
    rewrite concat_empty_r. reflexivity.
  - (* stp_sel1u *)
    apply stp_sel1u with (TU:=TU) (Gp:= Gp & empty & empty); auto.
    apply H; try assumption.
    rewrite concat_empty_r. reflexivity.
    apply H0; try assumption.
    rewrite concat_empty_r. reflexivity.
  - (* stp_selx *)
    admit. (* TODO: need same_extending *)
  - (* stp_selxu *)
    admit. (* TODO: need same_extending *)
  - (* stp_bind *)
    apply stp_bind with (L:=L).
    apply H. assumption.
    intros z Fr.
    admit. (* TODO *)
    (* tricky because the bind closes over the extended env now,
       while the induction hypothesis closes over the non-extended one
     *)
  - (* stp_transf *)
    apply stp_transf with (T2:=T2) (G2:=G2 & empty & empty); auto.
    apply H; try assumption.
    rewrite concat_empty_r. reflexivity.
    apply H0; try assumption.
    rewrite concat_empty_r. reflexivity.
  - (* stp_wrapf *)
    apply stp_wrapf; auto.
  - (* sdc_typ *)
    apply sdc_typ; auto.
  - (* sdc_tyu *)
    apply sdc_tyu; auto.
  - (* sdc_typu *)
    apply sdc_typu; auto.
  - (* sdc_mtd *)
    apply sdc_mtd; auto.
  - (* sdcs_nil *)
    apply sdcs_nil; auto.
  - (* sdcs_cons *)
    apply sdcs_cons with (D1:=D1); auto.
  - (* wf_typ *)
    apply wf_sel with (TL:=TL) (TU:=TU) (Gp:=Gp & empty & empty); auto.
    apply H; try assumption.
    rewrite concat_empty_r. reflexivity.
    rewrite concat_empty_r. rewrite concat_empty_r. assumption.
  - (* wf_tyu *)
    apply wf_selu with (TU:=TU) (Gp:=Gp & empty & empty); auto.
    apply H; try assumption.
    rewrite concat_empty_r. reflexivity.
    rewrite concat_empty_r. rewrite concat_empty_r. assumption.
  - (* wf_bind *)
    admit. (* tricky like stp_bind *)
  - (* wf_dec_typ *)
    apply wf_dec_typ; auto.
  - (* wf_dec_tyu *)
    apply wf_dec_tyu; auto.
  - (* wf_dec_mtd *)
    apply wf_dec_mtd; auto.
  - (* wf_decs_nil *)
    apply wf_decs_nil; auto.
  - (* wf_decs_cons *)
    apply wf_decs_cons; auto.
  - (* exp_bind *)
    admit. (* TODO: issue unifying the input and output envs *)
  - (* exp_sel *)
    apply exp_sel with (TL:=TL) (TU:=TU) (G':=G' & empty & empty).
    apply H; try assumption.
    rewrite concat_empty_r. reflexivity.
    apply H0; try assumption.
    rewrite concat_empty_r. reflexivity.
  - (* pth_has_any *)
    admit. (* TODO: output env doesn't match expected pattern *)
Qed.


Theorem trans: forall G1 T1 G2 T2 G3 T3,
  stp true G1 T1 T2 G2 ->
  stp true G2 T2 T3 G3 ->
  stp true G1 T1 T3 G3.
Proof. admit. Qed.

(* ###################################################################### *)
(** ** Inversion Lemmas *)

Lemma invert_tc_var: forall G x T,
  tc_trm G (trm_var (avar_f x)) T ->
  exists Gx Tx, binds x (typ_clo Gx Tx) G /\ stp true Gx Tx T G.
Proof.
  intros G x T H.
  remember (trm_var (avar_f x)) as t.
  induction H; inversion Heqt; subst.
  + exists Gx Tx. split; assumption.
  + specialize (IHtc_trm H1). inversion IHtc_trm as [Gx [Tx [IHb IHstp]]].
    exists Gx Tx. split.
    - assumption.
    - apply trans with (G2:=G) (T2:=T); assumption.
Qed.

(* ###################################################################### *)
(** ** Preservation Lemmas *)

Lemma binds_preserved: forall H G x v CT,
  tc_ctx H G ->
  binds x CT G ->
  binds x v H ->
  tc_val v CT.
Proof.
  intros H G x v CT H_HG H_G H_H.
  induction H_HG.
  - unfold binds in H_G. rewrite get_empty in H_G. inversion H_G.
  - unfold binds in H_G. rewrite get_push in H_G.
    unfold binds in H_H. rewrite get_push in H_H.
    destruct (classicT (x = x0)).
    + inversion H_G. inversion H_H. subst. assumption.
    + unfold binds in IHH_HG. apply IHH_HG; assumption.
Qed.

(* ###################################################################### *)
(** ** Preservation *)

Theorem preservation: forall t H v G T,
  ev H t v ->
  tc_ctx H G ->
  tc_trm G t T ->
  wf_val G v T.
Proof.
  intros t H v G T Hev HG Ht.
  induction Hev.
  + apply invert_tc_var in Ht.
    inversion Ht as [Gx [Tx [IHb IHstp]]].
    apply wf_val_any with (Tv:=Tx) (Gv:=Gx); try assumption.
    apply binds_preserved with (H:=H) (G:=G) (x:=x); assumption.
  + admit.
  + admit.
Qed.

(* ###################################################################### *)
(** ** Examples *)

Module Examples.

Definition typ_top := typ_bind decs_nil.
Definition M := labels.M.
Definition m := labels.m.
Parameter m_in: mtd_label.
Parameter m_out: mtd_label.
Parameter m_in_neq_out: m_in <> m_out.

Hint Constructors stp sdc sdcs wf_typ wf_dec wf_decs tc_trm tc_def tc_defs.
Hint Constructors exp.
Hint Constructors decs_has decs_hasnt.

Lemma ex_stp_top_top: forall G1 G2,
  stp true G1 (typ_bind decs_nil) (typ_bind decs_nil) G2.
Proof.
  intros.
  apply stp_bind with (L:=\{}); intros; auto.
  apply wf_bind with (L:=\{}); intros; auto.
Qed.

Hint Resolve ex_stp_top_top.

Ltac crush :=
  try solve [intros; constructor; compute; auto; crush];
  try solve [apply stp_bind with (L:=\{}); crush];
  try solve [apply wf_bind with (L:=\{}); crush];
  try solve [discriminate; auto; crush].

Example tc1:
  tc_trm empty
         (trm_new (defs_cons (def_typ M typ_top typ_top) defs_nil))
         (typ_bind (decs_cons (dec_typ M typ_top typ_top) decs_nil)).
Proof.
  apply tc_new with (L:=\{}); crush.
Qed.


Example tc2:
  tc_trm empty
         (trm_new (defs_cons (def_typ M typ_top typ_top) defs_nil))
         (typ_bind (decs_cons (dec_tyu M typ_top) decs_nil)).
Proof.
  apply tc_sub with (T:=(typ_bind (decs_cons (dec_typ M typ_top typ_top) decs_nil))).
  + apply tc1.
  + apply stp_bind with (L:=\{}); crush.
    intros.
    apply sdcs_cons with (D1:=(dec_typ M typ_top typ_top)); crush.
Qed.


Example tc3:
  tc_trm empty
         (trm_new (defs_cons (def_typ M typ_top typ_top) (defs_cons (def_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top (trm_var (avar_b 0))) defs_nil)))
         (typ_bind (decs_cons (dec_typ M typ_top typ_top) (decs_cons (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top) decs_nil))).
Proof.
  apply tc_new with (L:=\{}); crush.
  + intros.
    apply tc_defs_cons; crush.
    apply tc_defs_cons; crush.
    apply tc_def_mtd with (L:=\{z}); crush.
    - compute. erewrite If_l; auto.
      eapply wf_sel with (TL:=(typ_bind decs_nil)) (TU:=(typ_bind decs_nil)); crush.
      change (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil)) with
             (open_dec z (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil))).
      eapply pth_has_any; auto; crush.
    - intros x Frx. simpl. erewrite If_l; auto. erewrite If_r; auto.
      unfold open_trm. unfold open_rec_trm.
      unfold open_rec_avar. erewrite If_l; auto.
      eapply tc_var. auto.
      eapply stp_sel1 with (TL:=(typ_bind decs_nil)) (TU:=(typ_bind decs_nil)); crush.
      change (dec_typ M (typ_bind decs_nil) (typ_bind decs_nil)) with
             (open_dec z (dec_typ M (typ_bind decs_nil) (typ_bind decs_nil))).
       eapply pth_has_any; auto; crush.
Qed.

Example tc4:
  tc_trm empty
         (trm_new (defs_cons
                     (def_typ M typ_top typ_top)
                  (defs_cons
                     (def_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top
                              (trm_var (avar_b 0)))
                  (defs_cons
                     (def_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M)
                              (trm_var (avar_b 0)))
                  defs_nil))))
         (typ_bind (decs_cons
                      (dec_typ M typ_top typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil)))).
Proof.
  apply tc_new with (L:=\{}); crush.
  + intros.
    apply tc_defs_cons; crush.
    apply tc_defs_cons; crush.
    apply tc_def_mtd with (L:=\{z}); crush.
    - compute. erewrite If_l; auto.
      eapply wf_sel with (TL:=(typ_bind decs_nil)) (TU:=(typ_bind decs_nil)); crush.
      change (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil)) with
             (open_dec z (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil))).
      eapply pth_has_any; auto; crush.
    - intros x Frx. simpl. erewrite If_l; auto. erewrite If_r; auto.
      unfold open_trm. unfold open_rec_trm.
      unfold open_rec_avar. erewrite If_l; auto.
      eapply tc_var. auto.
      eapply stp_sel1 with (TL:=(typ_bind decs_nil)) (TU:=(typ_bind decs_nil)); crush.
      change (dec_typ M (typ_bind decs_nil) (typ_bind decs_nil)) with
             (open_dec z (dec_typ M (typ_bind decs_nil) (typ_bind decs_nil))).
       eapply pth_has_any; auto; crush.
    - apply tc_defs_cons; crush. {
    apply tc_def_mtd with (L:=\{z}); crush.
    - intros x Frx. simpl. erewrite If_r; auto. erewrite If_l; auto.
      unfold open_trm. unfold open_rec_trm.
      unfold open_rec_avar. erewrite If_l; auto.
      eapply tc_var. auto.
      eapply stp_sel2 with (TL:=(typ_bind decs_nil)) (TU:=(typ_bind decs_nil)); crush.
      change (dec_typ M (typ_bind decs_nil) (typ_bind decs_nil)) with
             (open_dec z (dec_typ M (typ_bind decs_nil) (typ_bind decs_nil))).
       eapply pth_has_any; auto; crush.
    }
Qed.

Example ex_stp_in_out:
  stp true empty
         (typ_bind (decs_cons
                      (dec_typ M typ_top typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil))))
         (typ_bind (decs_cons
                      (dec_tyu M typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil))))
      empty.
Proof.
  apply stp_bind with (L:=\{}); crush.
  + apply wf_bind with (L:=\{}); crush.
    intros z Fr.
    apply wf_decs_cons; crush.
    apply wf_decs_cons; crush.
    apply wf_dec_mtd; crush.
    eapply wf_selu with (TU:=typ_top); crush.
    simpl. erewrite If_l; auto.
    change (dec_tyu M typ_top) with (open_dec z (dec_tyu M typ_top)).
    eapply pth_has_any; auto; crush.
    apply wf_decs_cons; crush.
    apply wf_dec_mtd; crush.
    eapply wf_selu with (TU:=typ_top); crush.
    simpl. erewrite If_l; auto.
    change (dec_tyu M typ_top) with (open_dec z (dec_tyu M typ_top)).
    eapply pth_has_any; auto; crush.
    simpl. apply decs_hasnt_cons; crush.
    simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
  + intros z Fr.
    compute. erewrite If_l; auto.
    apply sdcs_cons with (D1:=dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil)); crush.
    apply sdcs_cons with (D1:=dec_mtd m_in (typ_sel (pth_var (avar_f z)) labels.M) (typ_bind decs_nil)); crush.
    apply decs_has_skip; crush. apply decs_has_hit; crush.
    apply decs_hasnt_cons; crush.
    simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
    apply sdc_mtd; crush.
    apply stp_wrapf.
    eapply stp_selx with (TL1:=typ_bind decs_nil) (TU1:=typ_bind decs_nil) (TL2:=typ_bind decs_nil) (TU2:=typ_bind decs_nil); crush.
    change (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil)) with
    (open_dec z (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil))); crush.
    eapply pth_has_any; auto; crush.
    change (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil)) with
    (open_dec z (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil))); crush.
    eapply pth_has_any; auto; crush.
    apply sdcs_cons with (D1:=dec_mtd m_out (typ_bind decs_nil) (typ_sel (pth_var (avar_f z)) labels.M)); crush.
    apply decs_has_skip; crush. apply decs_has_skip; crush.
    simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
    apply sdc_mtd; crush.
    eapply stp_selx with (TL1:=typ_bind decs_nil) (TU1:=typ_bind decs_nil) (TL2:=typ_bind decs_nil) (TU2:=typ_bind decs_nil); crush.
    change (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil)) with
    (open_dec z (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil))); crush.
    eapply pth_has_any; auto; crush.
    change (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil)) with
    (open_dec z (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil))); crush.
    eapply pth_has_any; auto; crush.
    apply sdcs_nil; crush.
    apply wf_decs_cons; crush.
    apply wf_decs_cons; crush.
    apply wf_dec_mtd; crush.
    eapply wf_sel with (TL:=typ_bind decs_nil) (TU:=typ_bind decs_nil); crush.
    change (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil)) with
    (open_dec z (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil))); crush.
    eapply pth_has_any; auto; crush.
    apply wf_decs_cons; crush.
    apply wf_dec_mtd; crush.
    eapply wf_sel with (TL:=typ_bind decs_nil) (TU:=typ_bind decs_nil); crush.
    change (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil)) with
    (open_dec z (dec_typ labels.M (typ_bind decs_nil) (typ_bind decs_nil))); crush.
    eapply pth_has_any; auto; crush.
    apply decs_hasnt_cons; crush.
    simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
    apply decs_hasnt_cons; crush.
    simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
Qed.

Example tc5:
  tc_trm empty
         (trm_new (defs_cons
                     (def_typ M typ_top typ_top)
                  (defs_cons
                     (def_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top
                              (trm_var (avar_b 0)))
                  (defs_cons
                     (def_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M)
                              (trm_var (avar_b 0)))
                  defs_nil))))
         (typ_bind (decs_cons
                      (dec_tyu M typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil)))).
Proof.
  apply tc_sub with (T:=(typ_bind
                   (decs_cons
                      (dec_typ M typ_top typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil))))).
  + apply tc4.
  + apply ex_stp_in_out.
Qed.

Example tc6:
  tc_trm empty
         (trm_new (defs_cons (def_mtd m
         (typ_bind (decs_cons
                      (dec_tyu M typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil))))
         typ_top
         (trm_call (trm_var (avar_b 0)) m_in
         (trm_call (trm_var (avar_b 0)) m_out
         (trm_new defs_nil))))
         defs_nil))
         (typ_bind (decs_cons (dec_mtd m
         (typ_bind (decs_cons
                      (dec_tyu M typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil))))
         typ_top)
         decs_nil)).
Proof.
  apply tc_new with (L:=\{}); crush.
  intros z Fr.
  compute. erewrite If_r; auto.
  apply tc_defs_cons; crush.
  apply tc_def_mtd with (L:=\{z}); crush.
  apply wf_bind with (L:=\{z}); crush.
  intros x Frx.
  apply wf_decs_cons; crush.
  apply wf_decs_cons; crush.
  apply wf_dec_mtd; crush.
  compute. erewrite If_l; auto.
  eapply wf_selu with (TU:=typ_bind decs_nil); crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec x (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  apply wf_decs_cons; crush.
  apply wf_dec_mtd; crush.
  eapply wf_selu with (TU:=typ_bind decs_nil); crush.
  compute. erewrite If_l; auto.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec x (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  apply decs_hasnt_cons; crush.
  simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
  intros x Frx.
  compute. erewrite If_l; auto.
  apply tc_call with (T2:=(typ_sel (pth_var (avar_f x)) labels.M)); crush.
  eapply trm_has_var with (Dp:=(open_dec x (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) labels.M) (typ_bind decs_nil)))).
  eapply pth_has_any; auto; crush.
  apply decs_has_skip; crush. apply decs_has_hit; crush.
  apply decs_hasnt_cons; crush.
  simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
  compute. erewrite If_l; auto.
  apply sdc_mtd; crush.
  apply stp_wrapf.
  eapply stp_selxu with (TU1:=typ_bind decs_nil) (TU2:=typ_bind decs_nil); crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec x (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec x (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  apply tc_call with (T2:=typ_bind decs_nil); crush.
  eapply trm_has_var with (Dp:=(open_dec x (dec_mtd m_out (typ_bind decs_nil) (typ_sel (pth_var (avar_b 0)) labels.M)))).
  eapply pth_has_any; auto; crush.
  apply decs_has_skip; crush. apply decs_has_skip; crush.
  simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
  compute. erewrite If_l; auto.
  apply sdc_mtd; crush.
  eapply stp_selxu with (TU1:=typ_bind decs_nil) (TU2:=typ_bind decs_nil); crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec x (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec x (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  apply tc_new with (L:=\{}); crush.
Qed.

Example th6:
  trm_has empty
         (trm_new (defs_cons (def_mtd m
         (typ_bind (decs_cons
                      (dec_tyu M typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil))))
         typ_top
         (trm_call (trm_var (avar_b 0)) m_in
         (trm_call (trm_var (avar_b 0)) m_out
         (trm_new defs_nil))))
         defs_nil))
         (dec_mtd m
         (typ_bind (decs_cons
                      (dec_tyu M typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil))))
         typ_top).
Proof.
  eapply trm_has_trm with (L:=\{}) (G:=empty).
  apply tc6.
  auto.
  crush.
  intros x Fr.
  simpl. erewrite If_r; auto.
  apply sdc_mtd; crush.
  apply stp_wrapf.
  apply stp_bind with (L:=\{}); crush.
  apply wf_bind with (L:=\{}); crush.
  intros z Fr.
  compute. erewrite If_l; auto.
  apply wf_decs_cons; crush.
  apply wf_decs_cons; crush.
  apply wf_dec_mtd; crush.
  eapply wf_selu with (TU:=typ_bind decs_nil); crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec z (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  apply wf_decs_cons; crush.
  apply wf_dec_mtd; crush.
  eapply wf_selu with (TU:=typ_bind decs_nil); crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec z (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  apply decs_hasnt_cons; crush.
  simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
  intros z Fr.
  compute. erewrite If_l; auto.
  apply sdcs_cons with (D1:=dec_tyu labels.M (typ_bind decs_nil)); crush.
  apply sdcs_cons with (D1:=dec_mtd m_in (typ_sel (pth_var (avar_f z)) labels.M) (typ_bind decs_nil)); crush.
  apply decs_has_skip; crush. apply decs_has_hit; crush.
  apply decs_hasnt_cons; crush.
  simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
  apply sdc_mtd; crush.
  apply stp_wrapf.
  eapply stp_selxu with (TU1:=typ_bind decs_nil) (TU2:=typ_bind decs_nil); crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec z (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec z (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  apply sdcs_cons with (D1:=dec_mtd m_out (typ_bind decs_nil) (typ_sel (pth_var (avar_f z)) labels.M)); crush.
  apply decs_has_skip; crush. apply decs_has_skip; crush.
  simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
  apply sdc_mtd; crush.
  eapply stp_selxu with (TU1:=typ_bind decs_nil) (TU2:=typ_bind decs_nil); crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec z (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec z (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  apply sdcs_nil.
  apply wf_decs_cons; crush.
  apply wf_decs_cons; crush.
  apply wf_dec_mtd; crush.
  eapply wf_selu with (TU:=typ_bind decs_nil); crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec z (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  apply wf_decs_cons; crush.
  apply wf_dec_mtd; crush.
  eapply wf_selu with (TU:=typ_bind decs_nil); crush.
  change (dec_tyu labels.M (typ_bind decs_nil)) with
  (open_dec z (dec_tyu labels.M (typ_bind decs_nil))); crush.
  eapply pth_has_any; auto; crush.
  apply decs_hasnt_cons; crush.
  simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
  apply decs_hasnt_cons; crush.
  simpl. assert (m_in <> m_out). apply m_in_neq_out. congruence.
Qed.

Example tc7:
  tc_trm empty
         (trm_call
         (trm_new (defs_cons (def_mtd m
         (typ_bind (decs_cons
                      (dec_tyu M typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil))))
         typ_top
         (trm_call (trm_var (avar_b 0)) m_in
         (trm_call (trm_var (avar_b 0)) m_out
         (trm_new defs_nil))))
         defs_nil))
         m
         (trm_new (defs_cons
                     (def_typ M typ_top typ_top)
                  (defs_cons
                     (def_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top
                              (trm_var (avar_b 0)))
                  (defs_cons
                     (def_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M)
                              (trm_var (avar_b 0)))
                  defs_nil)))))
         typ_top.
Proof.
  apply tc_call with (T2:=(typ_bind
                   (decs_cons
                      (dec_tyu M typ_top)
                   (decs_cons
                      (dec_mtd m_in (typ_sel (pth_var (avar_b 0)) M) typ_top)
                   (decs_cons
                      (dec_mtd m_out typ_top (typ_sel (pth_var (avar_b 0)) M))
                   decs_nil))))).
  + apply th6.
  + apply tc5.
Qed.

End Examples.
