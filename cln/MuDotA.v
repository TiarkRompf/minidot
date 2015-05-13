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

Inductive exp: ctx -> typ -> decs -> ctx -> Prop :=
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
  x' = var_gen (dom G') ->
  pth_has G (pth_var (avar_f x)) (open_dec x' D) (G' & (x' ~ (typ_clo Gx Tx)))
.

Inductive stp: nat -> bool -> ctx -> typ -> typ -> ctx -> Prop :=
| stp_sel2: forall n1 n2 n3 G1 T1 G2 p M TL TU Gp,
  pth_has G2 p (dec_typ M TL TU) Gp ->
  stp n1 true Gp TL TU Gp ->
  stp n2 true G1 T1 TL Gp ->
  stp n3 true G1 T1 TU Gp ->
  stp (S (n1+n2+n3)) true G1 T1 (typ_sel p M) G2
| stp_sel1: forall n1 n2 G1 G2 T2 p M TL TU Gp,
  pth_has G1 p (dec_typ M TL TU) Gp ->
  stp n1 true Gp TL TU Gp ->
  stp n2 true Gp TU T2 G2 ->
  stp (S (n1+n2)) true G1 (typ_sel p M) T2 G2
| stp_sel1u: forall n1 G1 G2 T2 p M TU Gp,
  pth_has G1 p (dec_tyu M TU) Gp ->
  stp n1 true Gp TU T2 G2 ->
  stp (S n1) true G1 (typ_sel p M) T2 G2
| stp_selx: forall n1 n2 G1 G2 p1 p2 M TL1 TU1 TL2 TU2 Gp1 Gp2,
  pth_has G1 p1 (dec_typ M TL1 TU1) Gp1 ->
  pth_has G2 p2 (dec_typ M TL2 TU2) Gp2 ->
  stp n1 true Gp1 TL1 TU1 Gp1 ->
  stp n2 true Gp2 TL2 TU2 Gp2 ->
  same_typ Gp2 TL2 TL1 Gp1 ->
  same_typ Gp1 TU1 TU2 Gp2 ->
  stp (S (n1+n2)) true G1 (typ_sel p1 M) (typ_sel p2 M) G2
| stp_selxu: forall n1 G1 G2 p1 p2 M TU1 TU2 Gp1 Gp2,
  pth_has G1 p1 (dec_tyu M TU1) Gp1 ->
  pth_has G2 p2 (dec_tyu M TU2) Gp2 ->
  wf_typ Gp1 TU1 ->
  wf_typ Gp2 TU2 ->
  same_typ Gp1 TU1 TU2 Gp2 ->
  stp (S n1) true G1 (typ_sel p1 M) (typ_sel p2 M) G2
| stp_bind: forall n1 L G1 Ds1 G2 Ds2,
  wf_typ G2 (typ_bind Ds2) ->
  (forall x, x \notin L ->
   sdcs n1
        (G1 & (x ~ typ_clo G1 (typ_bind Ds1)))
        (open_decs x Ds1)
        (open_decs x Ds2)
        (G2 & (x ~ typ_clo G1 (typ_bind Ds1)))
  ) ->
  stp (S n1) true G1 (typ_bind Ds1) (typ_bind Ds2) G2
| stp_transf: forall n1 n2 G1 G2 G3 T1 T2 T3,
  stp n1 false G1 T1 T2 G2 ->
  stp n2 false G2 T2 T3 G3 ->
  stp (S (n1+n2)) false G1 T1 T3 G3
| stp_wrapf: forall n1 G1 G2 T1 T2,
  stp n1 true G1 T1 T2 G2 ->
  stp (S n1) false G1 T1 T2 G2

with sdc: nat -> ctx -> dec -> dec -> ctx -> Prop :=
| sdc_typ: forall n1 n2 n3 n4 G1 G2 M TL1 TL2 TU1 TU2,
  stp n1 true G1 TL1 TU1 G1 ->
  stp n2 true G2 TL2 TU2 G2 ->
  stp n3 false G2 TL2 TL1 G1 ->
  stp n4 true G1 TU1 TU2 G2 ->
  sdc (S (n1+n2+n3+n4)) G1 (dec_typ M TL1 TU1) (dec_typ M TL2 TU2) G2
| sdc_tyu: forall n1 G1 G2 M TU1 TU2,
  stp n1 true G1 TU1 TU2 G2 ->
  sdc (S n1) G1 (dec_tyu M TU1) (dec_tyu M TU2) G2
| sdc_typu: forall n1 n2 G1 G2 M TL1 TU1 TU2,
  stp n1 true G1 TL1 TU1 G1 ->
  stp n2 true G1 TU1 TU2 G2 ->
  sdc (S (n1+n2)) G1 (dec_typ M TL1 TU1) (dec_tyu M TU2) G2
| sdc_mtd: forall n1 n2 G1 G2 m TL1 TL2 TU1 TU2,
  stp n1 false G2 TL2 TL1 G1 ->
  stp n2 true G1 TU1 TU2 G2 ->
  sdc (S (n1+n2)) G1 (dec_mtd m TL1 TU1) (dec_mtd m TL2 TU2) G2

with sdcs: nat -> ctx -> decs -> decs -> ctx -> Prop :=
| sdcs_nil: forall n1 G1 Ds1 G2,
  wf_decs G1 Ds1 ->
  sdcs (S n1) G1 Ds1 decs_nil G2
| sdcs_cons: forall n1 n2 G1 Ds1 G2 Ds2 D1 D2,
  decs_has Ds1 D1 ->
  sdc n1 G1 D1 D2 G2 ->
  sdcs n2 G1 Ds1 Ds2 G2 ->
  decs_hasnt Ds2 (label_of_dec D2) ->
  sdcs (S (n1+n2)) G1 Ds1 (decs_cons D2 Ds2) G2

with wf_typ: ctx -> typ -> Prop :=
| wf_sel: forall n1 G p M TL TU Gp,
  pth_has G p (dec_typ M TL TU) Gp ->
  stp n1 true Gp TL TU Gp ->
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
| wf_dec_typ: forall n1 G M TL TU,
  stp n1 true G TL TU G ->
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
.

Definition stpn b G1 T1 T2 G2 := exists n, stp n b G1 T1 T2 G2.
Definition sdcn G1 D1 D2 G2 := exists n, sdc n G1 D1 D2 G2.
Definition sdcsn G1 Ds1 Ds2 G2 := exists n, sdcs n G1 Ds1 Ds2 G2.

Inductive tc_trm: ctx -> trm -> typ -> Prop :=
| tc_var: forall G T x Gx Tx,
  binds x (typ_clo Gx Tx) G ->
  stpn true Gx Tx T G ->
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
  stpn true G T TU G ->
  tc_trm G t TU
with tc_def: ctx -> def -> dec -> Prop :=
| tc_def_typ: forall G M TL TU,
  stpn true G TL TU G ->
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
  sdcn Gp Dp D G ->
  trm_has G (trm_var (avar_f x)) D
| trm_has_trm: forall L G G' t T Ds D,
  tc_trm G t T ->
  exp G T Ds G' ->
  decs_has Ds D ->
  (forall x, x \notin L ->
   x \notin fv_dec (open_dec x D)
  ) ->
  sdcn G' D D G ->
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
  stpn true Gv Tv T G ->
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

Scheme exp_mut_ep     := Induction for exp Sort Prop
with   pth_has_mut_ep := Induction for pth_has Sort Prop.
Combined Scheme ep_mutind from exp_mut_ep, pth_has_mut_ep.

(* ###################################################################### *)
(** ** Properties *)

Theorem sub_reg:
  (forall n b G1 T1 T2 G2, stp n b G1 T1 T2 G2 -> wf_typ G1 T1 /\ wf_typ G2 T2) /\
  (forall n G1 D1 D2 G2, sdc n G1 D1 D2 G2 -> wf_dec G1 D1 /\ wf_dec G2 D2) /\
  (forall n G1 Ds1 Ds2 G2, sdcs n G1 Ds1 Ds2 G2 -> wf_decs G1 Ds1 /\ wf_decs G2 Ds2).
Proof.
  apply sub_mutind; intros.
  - (* T1 <: p.M -- sel2 *)
    split.
    + inversion H0. assumption.
    + eapply wf_sel. apply p0. eassumption.
  - (* p.M <: T2 -- sel1 *)
    split.
    + eapply wf_sel. apply p0. eassumption.
    + inversion H0. assumption.
  - (* p.M <: T2 -- sel1u *)
    split.
    + eapply wf_selu. apply p0. inversion H. assumption.
    + inversion H. assumption.
  - (* p.M <: p.M -- selx *)
    split.
    + eapply wf_sel. apply p. eassumption.
    + eapply wf_sel. apply p0. eassumption.
  - (* p.M <: p.M -- selxu *)
    split.
    + eapply wf_selu. apply p. assumption.
    + eapply wf_selu. apply p0. assumption.
  - (* bind *)
    split.
    + apply wf_bind with (L:=L); try assumption.
      intros x Frx.
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
    + eapply wf_dec_typ. eassumption.
    + eapply wf_dec_typ. eassumption.
  - (* tyu *)
    split.
    + apply wf_dec_tyu. inversion H. assumption.
    + apply wf_dec_tyu. inversion H. assumption.
  - (* typu *)
    split.
    + eapply wf_dec_typ. eassumption.
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

Lemma stp_reg1: forall n b G1 T1 T2 G2,
  stp n b G1 T1 T2 G2 ->
  wf_typ G1 T1.
Proof.
  intros n b G1 T1 T2 G2 H.
  apply (proj1 (stp_reg H)).
Qed.

Lemma sdc_reg2: forall n G1 D1 D2 G2,
  sdc n G1 D1 D2 G2 ->
  wf_dec G2 D2.
Proof.
  intros n G1 Ds1 Ds2 G2 H.
  apply (proj2 (sdc_reg H)).
Qed.

Lemma sdcs_reg1: forall n G1 Ds1 Ds2 G2,
  sdcs n G1 Ds1 Ds2 G2 ->
  wf_decs G1 Ds1.
Proof.
  intros n G1 Ds1 Ds2 G2 H.
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

Lemma sdcs_cons1: forall n G1 Ds1 Ds2 G2 D1,
  sdcs n G1 Ds1 Ds2 G2 ->
  wf_dec G1 D1 ->
  decs_hasnt Ds1 (label_of_dec D1) ->
  sdcs n G1 (decs_cons D1 Ds1) Ds2 G2.
Proof.
  intros.
  induction H.
  + apply sdcs_nil. apply wf_decs_cons; assumption.
  + apply sdcs_cons with (D1:=D0) (n1:=n1).
    - apply decs_has_skip. assumption.
      apply decs_has_or_hasnt with (Ds:=Ds1); assumption.
    - assumption.
    - apply IHsdcs. assumption. assumption.
    - assumption.
Qed.

(* Problem with cofinite quantification and index-based induction scheme. *)
Axiom sdcs_cofinite_switch: forall L Ds1 Ds2 G1X G2X,
  (forall x, x \notin L ->
   sdcsn
        (G1X & (x ~ typ_clo G1X (typ_bind Ds1)))
        (open_decs x Ds1)
        (open_decs x Ds2)
        (G2X & (x ~ typ_clo G1X (typ_bind Ds1)))) ->
  exists n,
  (forall x, x \notin L ->
   sdcs n
        (G1X & (x ~ typ_clo G1X (typ_bind Ds1)))
        (open_decs x Ds1)
        (open_decs x Ds2)
        (G2X & (x ~ typ_clo G1X (typ_bind Ds1)))).

Theorem sub_refl:
  (forall n b G1 T1 T2 G2, stp n b G1 T1 T2 G2 -> stpn b G1 T1 T1 G1 /\ stpn b G2 T2 T2 G2) /\
  (forall n G1 D1 D2 G2, sdc n G1 D1 D2 G2 -> sdcn G1 D1 D1 G1 /\ sdcn G2 D2 D2 G2) /\
  (forall n G1 Ds1 Ds2 G2, sdcs n G1 Ds1 Ds2 G2 -> sdcsn G1 Ds1 Ds1 G1 /\ sdcsn G2 Ds2 Ds2 G2) /\
  (forall G T, wf_typ G T -> stpn true G T T G) /\
  (forall G D, wf_dec G D -> sdcn G D D G) /\
  (forall G Ds, wf_decs G Ds -> sdcsn G Ds Ds G).
Proof.
  apply sw_mutind; intros.
  - (* T1 <: p.M -- sel2 *)
    split.
    + inversion H0. assumption.
    + exists (S (n1+n1)). eapply stp_selx.
      apply p0. apply p0.
      assumption. assumption.
      apply same_rfl. apply same_rfl.
  - (* p.M <: T2 -- sel1 *)
    split.
    + exists (S (n1+n1)). eapply stp_selx.
      apply p0. apply p0.
      assumption. assumption.
      apply same_rfl. apply same_rfl.
    + inversion H0. assumption.
  - (* p.M <: T2 -- sel1u *)
    split.
    + assert (wf_typ Gp TU) as HwfU. {
        inversion H as [H1 H2].
        inversion H1 as [n H1'].
        apply stp_reg1 with (n:=n) (b:=true) (T2:=TU) (G2:=Gp).
        assumption.
      }
      exists (S 0).
      eapply stp_selxu.
      apply p0. apply p0.
      assumption. assumption.
      apply same_rfl.
    + inversion H. assumption.
  - (* p.M <: p.M -- selx *)
    split.
    + exists (S (n1+n1)). eapply stp_selx.
      apply p. apply p.
      assumption. assumption.
      apply same_rfl. apply same_rfl.
    + exists (S (n2+n2)). eapply stp_selx.
      apply p0. apply p0.
      assumption. assumption.
      apply same_rfl. apply same_rfl.
  - (* p.M <: p.M -- selxu *)
    split.
    + exists (S 0). eapply stp_selxu.
      apply p. apply p.
      assumption. assumption.
      apply same_rfl.
    + exists (S 0). eapply stp_selxu.
      apply p0. apply p0.
      assumption. assumption.
      apply same_rfl.
  - (* bind *)
    split.
    + assert (forall x, x \notin L ->
       sdcsn (G1 & x ~ typ_clo G1 (typ_bind Ds1))
         (open_decs x Ds1) (open_decs x Ds1)
         (G1 & x ~ typ_clo G1 (typ_bind Ds1))) as A. {
        intros x Fr. specialize (H0 x Fr). inversion H0.
        assumption.
      }
      apply sdcs_cofinite_switch in A. inversion A as [n' A'].
      exists (S n').
      apply stp_bind with (L:=L); auto.
      apply wf_bind with (L:=L); auto.
      intros x Frx. eapply sdcs_reg1. specialize (s x Frx). apply s.
    + assumption.
  - (* transf *)
    split.
    + inversion H. inversion H1 as [n H1']. exists n. assumption.
    + inversion H0. assumption.
  - (* wrapf *)
    split.
    + inversion H. inversion H0 as [n H0']. exists (S n). apply stp_wrapf. assumption.
    + inversion H. inversion H1 as [n H1']. exists (S n). apply stp_wrapf. assumption.
  - (* sdc_typ *)
    split.
    + inversion H1 as [_ HL]. inversion HL as [nl HL'].
      inversion H2 as [HU _]. inversion HU as [nu HU'].
      exists (S (n1+n1+nl+nu)). apply sdc_typ; assumption.
    + inversion H1 as [HL _]. inversion HL as [nl HL'].
      inversion H2 as [_ HU]. inversion HU as [nu HU'].
      exists (S (n2+n2+nl+nu)). apply sdc_typ; assumption.
  - (* sdc_tyu *)
    split.
    + inversion H as [HU _]. inversion HU as [nu HU'].
      exists (S nu). apply sdc_tyu; assumption.
    + inversion H as [_ HU]. inversion HU as [nu HU'].
      exists (S nu). apply sdc_tyu; assumption.
  - (* sdc_typu *)
    split.
    + inversion H as [HL HU].
      inversion HL as [nl HL'].
      inversion HU as [nu HU'].
      exists (S (n1+n1+(S nl)+nu)). apply sdc_typ; try assumption.
      apply stp_wrapf. assumption.
    + inversion H0 as [_ HU]. inversion HU as [nu HU'].
      exists (S nu). apply sdc_tyu. assumption.
  - (* sdc_mtd *)
    split.
    + inversion H as [_ HL]. inversion HL as [nl HL'].
      inversion H0 as [HU _]. inversion HU as [nu HU'].
      exists (S (nl+nu)). apply sdc_mtd; assumption.
    + inversion H as [HL _]. inversion HL as [nl HL'].
      inversion H0 as [_ HU]. inversion HU as [nu HU'].
      exists (S (nl+nu)). apply sdc_mtd; assumption.
  - (* Ds1 <: {} -- nil *)
    split.
    + assumption.
    + exists (S 0). apply sdcs_nil. apply wf_decs_nil.
  - (* Ds1 <: D2::Ds2 -- cons *)
    split.
    + inversion H0. assumption.
    + inversion H0 as [_ HDs2]. inversion HDs2 as [n2' HDs2'].
      inversion H as [_ HD2]. inversion HD2 as [n1' HD2'].
      exists (S (n1'+n2')).
      apply sdcs_cons with (D1:=D2) (n1:=n1').
        apply decs_has_hit; assumption.
        assumption.
        apply sdcs_cons1.
          assumption.
          eapply sdc_reg2. apply s.
          assumption.
          assumption.
  - (* wf_sel *)
    exists (S (n1+n1)).
    apply stp_selx with (TL1:=TL) (TL2:=TL) (TU1:=TU) (TU2:=TU) (Gp1:=Gp) (Gp2:=Gp);
    try assumption; try solve [apply same_rfl].
  - (* wf_selu *)
    exists (S 0).
    apply stp_selxu with (TU1:=TU) (TU2:=TU) (Gp1:=Gp) (Gp2:=Gp);
    try assumption; try solve [apply same_rfl].
  - (* wf_bind *)
    apply sdcs_cofinite_switch in H. inversion H as [n' H'].
    exists (S n').
    apply stp_bind with (L:=L);
    try assumption.
    apply wf_bind with (L:=L);
    assumption.
  - (* wf_dec_typ *)
    inversion H as [HL HU].
    inversion HL as [nl HL'].
    inversion HU as [nu HU'].
    exists (S (n1+n1+(S nl)+nu)). apply sdc_typ; try assumption.
    apply stp_wrapf. assumption.
  - (* wf_dec_tyu *)
    inversion H as [nu HU'].
    exists (S nu). apply sdc_tyu; assumption.
  - (* wf_dec_mtd *)
    inversion H as [nl HL'].
    inversion H0 as [nu HU'].
    exists (S ((S nl)+nu)).
    apply sdc_mtd; try assumption.
    apply stp_wrapf. assumption.
  - (* wf_decs_nil *)
    exists (S 0). apply sdcs_nil. apply wf_decs_nil.
  - (* wf_decs_cons *)
    inversion H0 as [n2 HDs'].
    inversion H as [n1 HD'].
    exists (S (n1+n2)).
    apply sdcs_cons with (D1:=D) (n1:=n1); try assumption.
    + apply decs_has_hit. assumption.
    + apply sdcs_cons1; try assumption.
Qed.

Theorem pth_has_extending:
  (forall G p D Gp, pth_has G p D Gp ->
   forall GA GB GC,
     G = GA & GC ->
     pth_has (GA & GB & GC) p D Gp
  ).
Proof.
  intros. inversion H. subst.
  apply pth_has_any with (Ds:=Ds); auto.
  subst. apply binds_weaken.
    assumption.
    admit (* ok (GA & GB & GC) *).
Qed.

(*
Theorem sub_extending:
  (forall n b G1 T1 T2 G2, stp n b G1 T1 T2 G2 ->
   forall G1A G1B G1C G2A G2B G2C,
     G1 = G1A & G1C ->
     G2 = G2A & G2C ->
     stp n b (G1A & G1B & G1C) T1 T2 (G2A & G2B & G2C)
  ) /\
  (forall n G1 D1 D2 G2, sdc n G1 D1 D2 G2 ->
   forall G1A G1B G1C G2A G2B G2C,
     G1 = G1A & G1C ->
     G2 = G2A & G2C ->
     sdc n (G1A & G1B & G1C) D1 D2 (G2A & G2B & G2C)
  ) /\
  (forall n G1 Ds1 Ds2 G2, sdcs n G1 Ds1 Ds2 G2 ->
   forall G1A G1B G1C G2A G2B G2C,
     G1 = G1A & G1C ->
     G2 = G2A & G2C ->
     sdcs n (G1A & G1B & G1C) Ds1 Ds2 (G2A & G2B & G2C)
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
  ).
Proof.
  apply sw_mutind; intros.
  - (* stp_sel2 *)
    apply stp_sel2 with (TL:=TL) (TU:=TU) (Gp:=Gp & empty & empty); auto.
    apply pth_has_extending with (G:=G2).
    rewrite concat_empty_r. rewrite concat_empty_r. assumption.
    assumption.
    rewrite concat_empty_r. rewrite concat_empty_r. assumption.
    apply H0; try assumption.
    rewrite concat_empty_r. reflexivity.
    apply H1; try assumption.
    rewrite concat_empty_r. reflexivity.
  - (* stp_sel1 *)
    apply stp_sel1 with (TL:=TL) (TU:=TU) (Gp:= Gp & empty & empty); auto.
    apply pth_has_extending with (G:=G1).
    rewrite concat_empty_r. rewrite concat_empty_r. assumption.
    assumption.
    rewrite concat_empty_r. rewrite concat_empty_r. assumption.
    apply H0; try assumption.
    rewrite concat_empty_r. reflexivity.
  - (* stp_sel1u *)
    apply stp_sel1u with (TU:=TU) (Gp:= Gp & empty & empty); auto.
    apply pth_has_extending with (G:=G1).
    rewrite concat_empty_r. rewrite concat_empty_r. assumption.
    assumption.
    apply H; try assumption.
    rewrite concat_empty_r. reflexivity.
  - (* stp_selx *)
    apply stp_selx
    with (TL1:=TL1) (TL2:=TL2) (TU1:=TU1) (TU2:=TU2) (Gp1:=Gp1) (Gp2:=Gp2);
    auto.
    apply pth_has_extending with (G:=G1); assumption.
    apply pth_has_extending with (G:=G2); assumption.
  - (* stp_selxu *)
    apply stp_selxu
    with (TU1:=TU1) (TU2:=TU2) (Gp1:=Gp1) (Gp2:=Gp2);
    auto.
    apply pth_has_extending with (G:=G1); assumption.
    apply pth_has_extending with (G:=G2); assumption.
  - (* stp_bind *)
    subst.
    apply stp_bind with (L:=L)
      (G1A:=G1A) (G1B:=G2B & G1B0) (G1C:=G1C) (G1X:=G1A & G1C)
      (G2A:=G2A) (G2B:=G2B & G2B0) (G2C:=G2C) (G2X:=G2A & G2C).
    apply H. assumption.
    admit (* re-ordering env concats *). reflexivity.
    admit (* ditto *). reflexivity.
    assumption.
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
    apply sdcs_cons with (D1:=D1) (n1:=n1); auto.
  - (* wf_typ *)
    apply wf_sel with (n1:=n1) (TL:=TL) (TU:=TU) (Gp:=Gp); auto.
    apply pth_has_extending with (G:=G); assumption.
  - (* wf_tyu *)
    apply wf_selu with (TU:=TU) (Gp:=Gp); auto.
    apply pth_has_extending with (G:=G); assumption.
  - (* wf_bind *)
    subst.
    apply wf_bind with (L:=L)
      (GA:=GA) (GB:=GB & GB0) (GC:=GC) (GX:=GA & GC).
    admit (* re-ordering env concats *). reflexivity.
    assumption.
  - (* wf_dec_typ *)
    apply wf_dec_typ with (n1:=n1); auto.
  - (* wf_dec_tyu *)
    apply wf_dec_tyu; auto.
  - (* wf_dec_mtd *)
    apply wf_dec_mtd; auto.
  - (* wf_decs_nil *)
    apply wf_decs_nil; auto.
  - (* wf_decs_cons *)
    apply wf_decs_cons; auto.
Qed.
 *)

Lemma lookup_unique: forall {A} x G (a: A) (a': A),
  binds x a  G ->
  binds x a' G ->
  a' = a.
Proof.
  introv Hb1 Hb2.
  inversion Hb1 as [Hb1'].
  inversion Hb2 as [Hb2'].
  rewrite Hb2' in Hb1'.
  inversion Hb1'.
  reflexivity.
Qed.

Lemma decs_has_unique: forall Ds D1 D2,
  decs_has Ds D1 ->
  decs_has Ds D2 ->
  label_of_dec D1 = label_of_dec D2 ->
  D1 = D2.
Proof.
  introv H1. induction H1.
  - introv H2 Eq. inversions H2.
    * reflexivity.
    * rewrite Eq in H5. false H5. reflexivity.
  - introv H2 Eq. inversions H2.
    * rewrite Eq in H. false H. reflexivity.
    * apply (IHdecs_has H4 Eq).
Qed.

Lemma ep_unique:
  (forall G T Ds Ge, exp G T Ds Ge ->
   forall Ds' Ge',
   exp G T Ds' Ge' ->
   Ds' = Ds /\ Ge' = Ge) /\
  (forall G p D Gp, pth_has G p D Gp ->
   forall D' Gp',
   pth_has G p D' Gp' ->
   label_of_dec D' = label_of_dec D ->
   D' = D /\ Gp' = Gp).
Proof.
  apply ep_mutind.
  - (* exp_bind *)
    intros; inversion H; subst; split; reflexivity.
  - (* exp_sel *)
    intros G Gp Gpe p M TL TU Ds Hp HIp He HIe Ds' Ge' H.
    inversion H; subst.
    assert (dec_typ M TL0 TU0 = dec_typ M TL TU /\ G' = Gp) as A.
    apply HIp; try assumption.
    compute. reflexivity.
    inversion A as [A1 A2]. inversion A1. subst.
    apply HIe. assumption.
  - (* pth_has_any *)
    intros G x Gx Tx Ds D Gp z Hb He HIe Hd Hz D' Gp' H Hl.
    inversion H. subst.
    assert (typ_clo Gx0 Tx0 = typ_clo Gx Tx) as A. {
      eapply lookup_unique. apply Hb. assumption.
    }
    inversions A.
    assert (Ds0 = Ds /\ G' = Gp) as A. {
      apply HIe. assumption.
    }
    inversions A.
    assert (D0 = D) as A. {
      apply decs_has_unique with (Ds:=Ds); try assumption.
      induction D; induction D0; compute; compute in Hl; apply Hl.
    }
    subst.
    split; reflexivity.
Qed.

Theorem pth_has_unique: forall G p D Gp D' Gp',
  pth_has G p D Gp ->
  pth_has G p D' Gp' ->
  label_of_dec D' = label_of_dec D ->
  D' = D /\ Gp' = Gp.
Proof.
  introv H1.
  apply (proj2 ep_unique).
  apply H1.
Qed.

(* same_typ lemmas *)

Lemma same_typ_sym: forall G1 T1 G2 T2,
  same_typ G1 T1 T2 G2 ->
  same_typ G2 T2 T1 G1.
Proof.
  introv H. induction H.
  - apply same_rfl.
  - eapply same_sel; eassumption.
  - apply same_bind.
Qed.

Lemma same_stp2: forall n G1 T1 G2 T2 G3 T3,
  stp n true G1 T1 T2 G2 ->
  same_typ G2 T2 T3 G3 ->
  stp n true G1 T1 T3 G3.
Proof.
  introv Hstp Hsame. gen G1 T1. induction Hsame; intros; try assumption.
  (* tricky *)
  admit.
Qed.

Lemma same_stp1: forall n G1 T1 G2 T2 G3 T3,
  stp n true G2 T2 T3 G3 ->
  same_typ G1 T1 T2 G2 ->
  stp n true G1 T1 T3 G3.
Proof.
  admit.
Qed.

Lemma same_typ_trans: forall G1 T1 G2 T2 G3 T3,
  same_typ G1 T1 T2 G2 ->
  same_typ G2 T2 T3 G3 ->
  same_typ G1 T1 T3 G3.
Proof.
  introv H12 H23. induction H12; try assumption.
  (* tricky *)
  admit.
Qed.

(* Transivity *)

Definition stp_trans_on n12 n23 :=
  forall G1 T1 G2 T2 G3 T3,
  stp n12 true G1 T1 T2 G2 ->
  stp n23 true G2 T2 T3 G3 ->
  stpn true G1 T1 T3 G3.

Definition sdc_trans_on n12 n23 :=
  forall G1 D1 G2 D2 G3 D3,
  sdc n12 G1 D1 D2 G2 ->
  sdc n23 G2 D2 D3 G3 ->
  sdcn G1 D1 D3 G3.

Definition sdcs_trans_on n12 n23 :=
  forall G1 Ds1 G2 Ds2 G3 Ds3,
  sdcs n12 G1 Ds1 Ds2 G2 ->
  sdcs n23 G2 Ds2 Ds3 G3 ->
  sdcsn G1 Ds1 Ds3 G3.

Definition trans_up (P: nat -> nat -> Prop) n :=
  forall n12 n23, n12 + n23 <= n ->
  P n12 n23.

Lemma trans_le: forall P n n12 n23,
  trans_up P n ->
  n12 + n23 <= n ->
  P n12 n23.
Proof.
  introv H Heq. unfold trans_up in H. apply H. auto.
Qed.

Lemma stpn_sel2: forall G1 T1 G2 p M TL TU Gp,
  pth_has G2 p (dec_typ M TL TU) Gp ->
  stpn true Gp TL TU Gp ->
  stpn true G1 T1 TL Gp ->
  stpn true G1 T1 TU Gp ->
  stpn true G1 T1 (typ_sel p M) G2.
Proof.
  intros.
  inversion H0 as [n1 H1'].
  inversion H1 as [n2 H2'].
  inversion H2 as [n3 H3'].
  exists (S (n1+n2+n3)).
  eapply stp_sel2; try eassumption.
Qed.

Lemma stpn_sel1: forall G1 G2 T2 p M TL TU Gp,
  pth_has G1 p (dec_typ M TL TU) Gp ->
  stpn true Gp TL TU Gp ->
  stpn true Gp TU T2 G2 ->
  stpn true G1 (typ_sel p M) T2 G2.
Proof.
  intros. inversion H0 as [n1 H1']. inversion H1 as [n2 H2'].
  exists (S (n1+n2)).
  eapply stp_sel1; try eassumption.
Qed.

Lemma stpn_sel1u: forall G1 G2 T2 p M TU Gp,
  pth_has G1 p (dec_tyu M TU) Gp ->
  stpn true Gp TU T2 G2 ->
  stpn true G1 (typ_sel p M) T2 G2.
Proof.
  intros. inversion H0 as [n1 H1'].
  exists (S n1).
  eapply stp_sel1u; try eassumption.
Qed.

Ltac inversion_eq :=
  match goal with
    | [ H : _ = _ |- _ ] => inversions H
  end.

Lemma sub_trans: forall n,
  trans_up stp_trans_on n /\
  trans_up sdc_trans_on n /\
  trans_up sdcs_trans_on n.
Proof.
  intros n.
  unfold trans_up.
  unfold stp_trans_on.
  unfold sdc_trans_on.
  unfold sdcs_trans_on.
  induction n.
  - split; try split; intros;
    assert (n12 = 0) by omega;
    assert (n23 = 0) by omega;
    subst;
    inversion H0; inversion H1.
  - inversion IHn as [IHn_stp [IHn_sdc IHn_sdcs]].
    split; try split;
    intros n12 n23 Hneq G1 T1 G2 T2 G3 T3 HS12 HS23;

    inversion HS12; inversion HS23; subst;
    (* 56 cases total *)
    (* 6 cases, stp_sel2 right *)
    try solve [eapply stpn_sel2; [
        eassumption |
        eexists; eassumption |
        eapply trans_le in IHn_stp; [
            eapply IHn_stp; eassumption |
            omega
        ] |
        eapply trans_le in IHn_stp; [
            eapply IHn_stp; eassumption |
            omega
        ]
    ]];
    (* 5 cases, stp_sel1 left *)
    try solve [eapply stpn_sel1; [
        eassumption |
        eexists; eassumption |
        eapply trans_le in IHn_stp; [
            eapply IHn_stp; eassumption |
            omega
        ]
    ]];
    (* 5 cases, stp_sel1u left *)
    try solve [eapply stpn_sel1u; [
        eassumption |
        eapply trans_le in IHn_stp; [
            eapply IHn_stp; eassumption |
            omega
        ]
    ]];
    (* 18 cases *)
    try solve [inversion_eq];
    try inversion_eq.

  + (* sel2 - sel1 *)
    assert (dec_typ M TL0 TU0 = dec_typ M TL TU /\ Gp0 = Gp) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversions A1. clear A.
    eapply trans_le in IHn_stp.
    eapply IHn_stp. apply H2. eassumption.
    omega.

  + (* sel2 - sel1u *)
    assert (dec_tyu M TU0 = dec_typ M TL TU /\ Gp0 = Gp) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversion A1. (* contradiction *)

  + (* sel2 - selx *)
    assert (dec_typ M TL1 TU1 = dec_typ M TL TU /\ Gp1 = Gp) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversions A1. clear A.

    eexists. eapply stp_sel2; try eassumption.

    apply same_stp2 with (T2:=TL) (G2:=Gp); try eassumption.
    apply same_typ_sym. assumption.

    apply same_stp2 with (T2:=TU) (G2:=Gp); eassumption.

  + (* sel2 - selxu *)
    assert (dec_tyu M TU1 = dec_typ M TL TU /\ Gp1 = Gp) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversion A1.

  + (* selx - sel1 *)
    assert (dec_typ M TL2 TU2 = dec_typ M TL TU /\ Gp2 = Gp) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversions A1. clear A.

    eexists. eapply stp_sel1; try eassumption.

    apply same_stp1 with (T2:=TU) (G2:=Gp); try eassumption.

  + (* selxu - sel1 *)
    assert (dec_tyu M TU = dec_typ M TL2 TU2 /\ Gp = Gp2) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversion A1.

  + (* selx - selx *)
    assert (dec_typ M TL2 TU2 = dec_typ M TL0 TU0 /\ Gp2 = Gp0) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversions A1. clear A.

    eexists. eapply stp_selx; try eassumption.
    apply same_typ_trans with (T2:=TL0) (G2:=Gp0); assumption.
    apply same_typ_trans with (T2:=TU0) (G2:=Gp0); assumption.

  + (* selx - selxu *)
    assert (dec_tyu M TU0 = dec_typ M TL2 TU2 /\ Gp0 = Gp2) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversion A1.

  + (* selx - sel1u *)
    assert (dec_tyu M TU2 = dec_typ M TL TU /\ Gp2 = Gp) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversion A1.

  + (* selxu - sel1u *)
    assert (dec_tyu M TU2 = dec_tyu M TU /\ Gp2 = Gp) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversions A1. clear A.

    eexists. eapply stp_sel1u; try eassumption.

    apply same_stp1 with (T2:=TU) (G2:=Gp); try eassumption.

  + (* selxu - selx *)
    assert (dec_tyu M TU2 = dec_typ M TL1 TU0 /\ Gp2 = Gp0) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversion A1.

  + (* selxu - selxu *)
    assert (dec_tyu M TU2 = dec_tyu M TU0 /\ Gp2 = Gp0) as A. {
      eapply pth_has_unique; try eassumption.
      compute. reflexivity.
    }
    inversion A as [A1 A2]. inversions A1. clear A.

    exists (S 0). eapply stp_selxu; try eassumption.
    apply same_typ_trans with (T2:=TU0) (G2:=Gp0); assumption.

  + (* bind - bind *)
    exists (S n).
    apply stp_bind with (L:=L \u L0); try assumption; try reflexivity.
    intros x Frx.
    assert (x \notin L) as FrL by auto.
    assert (x \notin L0) as FrL0 by auto.
    specialize (H0 x FrL). specialize (H7 x FrL0).
    admit.

  + (* sdc_typ - sdc_typ *)
    assert (stpn true G1 TU1 TU3 G3) as HU13. {
     eapply trans_le in IHn_stp; [
        eapply IHn_stp; eassumption |
        omega
      ].
    }
    inversion HU13 as [nu HU13'].
    assert (stpn false G3 TL3 TL1 G1) as HL31. {
      exists (S (n6+n3)).
      apply stp_transf with (G2:=G2) (T2:=TL2);
      assumption.
    }
    inversion HL31 as [nl HL31'].
    exists (S (n1+n5+nl+nu)).
    apply sdc_typ; assumption.

  + (* sdc_typ - sdc_typu *)
    assert (stpn true G1 TU1 TU3 G3) as HU13. {
     eapply trans_le in IHn_stp; [
        eapply IHn_stp; eassumption |
        omega
      ].
    }
    inversion HU13 as [nu HU13'].
    exists (S (n1+nu)).
    apply sdc_typu; assumption.

  + (* sdc_tyu - sdc_tyu *)
    assert (stpn true G1 TU1 TU3 G3) as HU13. {
     eapply trans_le in IHn_stp; [
        eapply IHn_stp; eassumption |
        omega
      ].
    }
    inversion HU13 as [nu HU13'].
    exists (S nu).
    apply sdc_tyu; assumption.

  + (* sdc_typu - sdc_tyu *)
    assert (stpn true G1 TU1 TU3 G3) as HU13. {
     eapply trans_le in IHn_stp; [
        eapply IHn_stp; eassumption |
        omega
      ].
    }
    inversion HU13 as [nu HU13'].
    exists (S (n1+nu)).
    apply sdc_typu; assumption.

  + (* sdc_mtd - sdc_mtd *)
    assert (stpn true G1 TU1 TU3 G3) as HU13. {
     eapply trans_le in IHn_stp; [
        eapply IHn_stp; eassumption |
        omega
      ].
    }
    inversion HU13 as [nu HU13'].
    assert (stpn false G3 TL3 TL1 G1) as HL31. {
      exists (S (n0+n1)).
      apply stp_transf with (G2:=G2) (T2:=TL2);
      assumption.
    }
    inversion HL31 as [nl HL31'].
    exists (S (nl+nu)).
    apply sdc_mtd; assumption.

  + (* sdcs_nil - sdcs_nil *)
    exists (S 0). apply sdcs_nil. assumption.

  + (* sdcs_nil - sdcs_cons -- Ds1 <: [] <: D3::Ds3 *)
    inversion H5. (* decs_has [] D1 *)

  + (* sdcs_cons - sdcs_nil -- Ds1 <: Ds2 <: [] *)
    exists (S 0). apply sdcs_nil.
    eapply sdcs_reg1. apply HS12.

  + (* sdcs_cons - sdcs_cons -- Ds1 <: D2::Ds2 <: D3::Ds3 *)
    (* tricky because D2 and D3 might not have same label *)
    admit.

Qed.

Definition stp_trans n := proj1 (sub_trans n).

Theorem trans: forall G1 T1 G2 T2 G3 T3,
  stpn true G1 T1 T2 G2 ->
  stpn true G2 T2 T3 G3 ->
  stpn true G1 T1 T3 G3.
Proof.
  introv H12 H23.
  destruct H12 as [n12 H12'].
  destruct H23 as [n23 H23'].
  eapply stp_trans with (n:=n12+n23) (n12:=n12) (n23:=n23).
  omega.
  eassumption.
  assumption.
Qed.

(* ###################################################################### *)
(** ** Inversion Lemmas *)

Lemma invert_tc_var: forall G x T,
  tc_trm G (trm_var (avar_f x)) T ->
  exists Gx Tx, binds x (typ_clo Gx Tx) G /\ stpn true Gx Tx T G.
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
