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
  | typ_top : typ
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
  | typ_top     => typ_top
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
  | typ_top     => \{}
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
| same_top: forall G1 G2,
  same_typ G1 typ_top typ_top G2
| same_sel: forall G1 G2 x1 x2 M Gx1 Tx1 Gx2 Tx2,
  binds x1 (typ_clo Gx1 Tx1) G1 ->
  binds x2 (typ_clo Gx2 Tx2) G2 ->
  same_typ Gx1 Tx1 Tx2 Gx2 ->
  same_typ G1
           (typ_sel (pth_var (avar_f x1)) M)
           (typ_sel (pth_var (avar_f x2)) M)
           G2
| same_bind: forall G DS,
  (* TODO: do we need to go in there? *)
  same_typ G (typ_bind DS) (typ_bind DS) G
.

(* TODO: regularity? *)
Inductive stp: ctx -> typ -> typ -> ctx -> Prop :=
| stp_top: forall G1 T1 G2,
  stp G1 T1 typ_top G2
| stp_sel2: forall G1 T1 G2 p M TL TU Gp,
  pth_has G2 p (dec_typ M TL TU) Gp ->
  stp G1 T1 TL Gp ->
  stp G1 T1 (typ_sel p M) G2
| stp_sel1: forall G1 G2 T2 p M TL TU Gp,
  pth_has G1 p (dec_typ M TL TU) Gp ->
  stp Gp TU T2 G2 ->
  stp G1 (typ_sel p M) T2 G2
| stp_sel1u: forall G1 G2 T2 p M TU Gp,
  pth_has G1 p (dec_tyu M TU) Gp ->
  stp Gp TU T2 G2 ->
  stp G1 (typ_sel p M) T2 G2
| stp_selx: forall G1 G2 p1 p2 M TL1 TU1 TL2 TU2 Gp1 Gp2,
  pth_has G1 p1 (dec_typ M TL1 TU1) Gp1 ->
  pth_has G2 p2 (dec_typ M TL2 TU2) Gp2 ->
  same_typ Gp2 TL2 TL1 Gp1 ->
  same_typ Gp1 TU1 TU2 Gp2 ->
  stp G1 (typ_sel p1 M) (typ_sel p2 M) G2
| stp_bind: forall L G1 DS1 G2 DS2,
  (forall x, x \notin L ->
   sdcs (G1 & (x ~ typ_clo G1 (typ_bind DS1)))
        DS1 DS2
        (G2 & (x ~ typ_clo G1 (typ_bind DS1)))
  ) ->
  stp G1 (typ_bind DS1) (typ_bind DS2) G2
with sdcs: ctx -> decs -> decs -> ctx -> Prop :=
with exp: ctx -> typ -> decs -> ctx -> Prop :=
| exp_top: forall G,
  exp G typ_top decs_nil G
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

Inductive env_to_ctx: list var -> env typ -> ctx -> Prop :=
| e2c_nil: forall E,
  env_to_ctx nil E empty
| e2c_cons: forall v V E G T,
  binds v T E ->
  env_to_ctx V E G ->
  env_to_ctx (v::V) E (G & (v ~ typ_clo G T))
.

Inductive tc_trm: list var -> env typ -> trm -> typ -> Prop :=
| tc_var: forall V x T E,
  binds x T E ->
  tc_trm V E (trm_var (avar_f x)) T
| tc_new: forall L V E ds Ds,
  defs_to_decs ds = Ds ->
  (forall x, x \notin L ->
   tc_defs (x::V) (E & (x ~ (typ_bind Ds))) (open_defs x ds) (open_decs x Ds)) ->
  tc_trm V E (trm_new ds) (typ_bind Ds)
| tc_call: forall V E t1 m t2 T2 T,
  trm_has V E t1 (dec_mtd m T2 T) ->
  tc_trm V E t2 T2 ->
  tc_trm V E (trm_call t1 m t2) T
| tc_sub: forall V E G t T TU,
  tc_trm V E t T ->
  env_to_ctx V E G ->
  stp G T TU G ->
  tc_trm V E t TU
with tc_def: list var -> env typ -> def -> dec -> Prop :=
with trm_has: list var -> env typ -> trm -> dec -> Prop :=
with tc_defs: list var -> env typ -> defs -> decs -> Prop :=
| tc_nil: forall V E,
  tc_defs V E defs_nil decs_nil
| tc_cons: forall V E d ds D Ds,
  tc_def V E d D ->
  tc_defs V E ds Ds ->
  tc_defs V E (defs_cons d ds) (decs_cons D Ds)
.