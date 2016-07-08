Require Import LibTactics.
Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Lt.

Definition id := nat.
Definition lb := nat.

Inductive vr: Set :=
| VarF : id -> vr (* absolute position in context, from origin, invariant under context extension *)
| VarB : id -> vr (* bound variable, de Bruijn, locally nameless style -- see open *).

Inductive tm: Set :=
| tVar : vr -> tm
| tLam : ty -> tm -> tm  (* lambda(x: T)t *)
| tTag : ty -> tm        (* "wrapped type" [T] *)
| tObj : defs -> tm      (* {z => (l: T = i)...} where i are initalizations (vars or values) *)
| tSel : tm -> lb -> tm  (* t.l *)
| tApp : tm -> tm -> tm  (* t t *)
with def: Set :=
| dSome : ty -> tm -> def  (* label is given by position in defs list *)
| dNone : def              (* if no member at that label position *)
with defs: Set :=
| dNil  : defs
| dCons : def -> defs -> defs
with ty: Set :=
| TTop  : ty
| TBot  : ty
| TRcd  : lb -> ty -> ty   (* {a: T} record with one val/def/type member *)
| TAll  : ty -> ty -> ty   (* (all: T)U *)
| TTag  : ty -> ty -> ty   (* [T..U] type of type tags, with bounds *)
| TProj : tm -> ty         (* p!  unwrap type tag *)
| TBind : ty -> ty         (* {z => T} bind type *)
| TAnd  : ty -> ty -> ty
| TOr   : ty -> ty -> ty
.

(* We define three subsets of terms: values, initializations (for rhs of fields), and paths: *)

Inductive value: tm -> Prop :=
| value_lam: forall T t,
    value (tLam T t)
| value_tag: forall T,
    value (tTag T)
| value_obj: forall ds,
    dvalues ds -> value (tObj ds)
with dvalue: def -> Prop :=
| value_some: forall T v,
    value v ->
    dvalue (dSome T v)
| value_none:
    dvalue dNone
with dvalues: defs -> Prop :=
| value_nil:
    dvalues dNil
| value_cons: forall d ds,
    dvalue d ->
    dvalues ds ->
    dvalues (dCons d ds).

Inductive initialization: tm -> Prop :=
| i_value: forall v,
    value v ->
    initialization v
| i_var: forall x,
    initialization (tVar x).
Inductive dinitialization: def -> Prop :=
| i_some: forall T i,
    initialization i ->
    dinitialization (dSome T i)
| i_none:
    dinitialization dNone
with dinitializations: defs -> Prop :=
| i_nil:
    dinitializations dNil
| i_cons: forall d ds,
    dinitialization d ->
    dinitializations ds ->
    dinitializations (dCons d ds).

(* Note: This grammar cannot ensure that all paths are well-formed:
   For instance, p.f.l is accepted even if f is a lambda. *)
Inductive path: tm -> Prop :=
| path_var: forall x,
    path (tVar x)
| path_value: forall v,
    value v ->
    path v
| path_sel: forall p l,
    path p ->
    path (tSel p l). 

Fixpoint index {X: Type}(n: id)(l: list X): option X := match l with
| [] => None
| a :: l'  => if beq_nat n (length l') then Some a else index n l'
end.

Fixpoint defs_length(ds: defs): nat := match ds with
| dNil => 0
| dCons d rest => S (defs_length rest)
end.

Fixpoint defs_index(n: nat)(ds: defs): def := match ds with
| dNil => dNone
| dCons d rest => if beq_nat n (defs_length rest) then d else defs_index n rest
end.

Fixpoint defs_concat(ds1 ds2: defs): defs := match ds1 with
| dNil => ds2
| dCons d ds => dCons d (defs_concat ds ds2)
end.

(*
Fixpoint defs_to_list(ds: defs): list def := match ds with
| dNil => []
| dCons d ds => d :: defs_to_list ds
end.
*)

Definition vr_open_rec(k: nat)(u: tm)(v: vr): tm := match v with
| VarF x => tVar (VarF x)
| VarB x => if beq_nat k x then u else (tVar (VarB x))
end.

Fixpoint tm_open_rec(k: nat)(u: tm)(t: tm){struct t}: tm := match t with
| tVar v => vr_open_rec k u v
| tLam T body => tLam (ty_open_rec k u T) (tm_open_rec (S k) u body)
| tTag T => tTag (ty_open_rec k u T)
| tObj ds => tObj (defs_open_rec (S k) u ds)
| tSel t l => tSel (tm_open_rec k u t) l 
| tApp t1 t2 => tApp (tm_open_rec k u t1) (tm_open_rec k u t2)
end
with def_open_rec(k: nat)(u: tm)(d: def){struct d}: def := match d with
| dSome T t => dSome (ty_open_rec k u T) (tm_open_rec k u t)
| dNone => dNone
end
with defs_open_rec(k: nat)(u: tm)(ds: defs){struct ds}: defs := match ds with
| dNil => dNil
| dCons d ds => dCons (def_open_rec k u d) (defs_open_rec k u ds)
end
with ty_open_rec(k: nat)(u: tm)(T: ty){struct T}: ty := match T with
| TTop => TTop
| TBot => TBot
| TRcd l T1 => TRcd l (ty_open_rec k u T1)
| TAll T1 T2 => TAll (ty_open_rec k u T1) (ty_open_rec (S k) u T2)
| TTag T1 T2 => TTag (ty_open_rec k u T1) (ty_open_rec k u T2)
| TProj t => TProj (tm_open_rec k u t)
| TBind T1 => TBind (ty_open_rec (S k) u T1)
| TAnd T1 T2 => TAnd (ty_open_rec k u T1) (ty_open_rec k u T2)
| TOr T1 T2 => TOr (ty_open_rec k u T1) (ty_open_rec k u T2)
end.

Definition   vr_open :=   vr_open_rec 0.
Definition   tm_open :=   tm_open_rec 0.
Definition  def_open :=  def_open_rec 0.
Definition defs_open := defs_open_rec 0.
Definition   ty_open :=   ty_open_rec 0.

Inductive step: tm -> tm -> Prop :=
(* Reduction *)
| step_sel: forall ds l T v,
    defs_index l ds = dSome T v ->
    step (tSel (tObj ds) l) (tm_open (tObj ds) v)
| step_app: forall T t v,
    value v ->
    step (tApp (tLam T t) v) (tm_open v t)
(* Congruence *)
| step_sel1: forall t l t',
    step t t' ->
    step (tSel t l) (tSel t' l)
| step_app1 : forall t1 t1' t2,
    step t1 t1' ->
    step (tApp t1 t2) (tApp t1' t2)
| step_app2 : forall v1 t2 t2',
    value v1 ->
    step t2 t2' ->
    step (tApp v1 t2) (tApp v1 t2').

Lemma values_dont_step: forall v v',
  step v v' -> value v -> False.
Proof.
  intros. inversions H; inversions H0.
Qed.

Lemma objects_dont_step: forall ds t,
  step (tObj ds) t -> False.
Proof.
  intros. inversions H.
Qed.

Lemma step_unique: forall t t1 t2,
  step t t1 ->
  step t t2 ->
  t1 = t2.
Proof.
  intros. generalize dependent t2.
  induction H; intros ? H_other.
  - inversions H_other.
    + rewrite H3 in H. inversions H. reflexivity.
    + exfalso. eapply objects_dont_step. eassumption.
  - inversions H_other.
    + reflexivity.
    + inversions H3.
    + exfalso. eapply values_dont_step; eauto.
  - inversions H_other.
    + inversions H.
    + f_equal. apply IHstep. assumption.
  - inversions H_other.
    + inversions H.
    + f_equal. apply IHstep. assumption.
    + exfalso. eapply values_dont_step. eapply H. assumption.
  - inversions H_other.
    + exfalso. eapply values_dont_step. eapply H0. assumption.
    + exfalso. eapply values_dont_step. eapply H4. assumption.
    + f_equal. apply IHstep. assumption.
Qed.

(* Closed also checks that the grammar is respected (see <----- arrows) *)
Inductive vr_closed: nat(*i:abstract*) -> nat(*k:bound*) -> vr -> Prop :=
| clv_abs: forall i k x,
    i > x ->
    vr_closed i k (VarF x)
| clv_bound: forall i k x,
    k > x ->
    vr_closed i k (VarB x).
Inductive tm_closed: nat -> nat -> tm -> Prop :=
| clt_vr: forall i k v1,
    vr_closed i k v1 ->
    tm_closed i k (tVar v1)
| clt_lam: forall i k T t,
    ty_closed i k T ->
    tm_closed i (S k) t ->
    tm_closed i k (tLam T t)
| clt_tag: forall i k T,
    ty_closed i k T ->
    tm_closed i k (tTag T)
| clt_obj: forall i k ds,
    defs_closed i (S k) ds ->
    tm_closed i k (tObj ds)
| clt_sel: forall i k t l,
    tm_closed i k t ->
    tm_closed i k (tSel t l)
| clt_app: forall i k t1 t2,
    tm_closed i k t1 ->
    tm_closed i k t2 ->
    tm_closed i k (tApp t1 t2)
with def_closed: nat -> nat -> def -> Prop :=
| cld_some: forall i k T t,
    ty_closed i k T ->
    tm_closed i k t ->
    initialization t ->         (* <----- *)
    def_closed i k (dSome T t)
| cld_none: forall i k,
    def_closed i k dNone
with defs_closed: nat -> nat -> defs -> Prop :=
| clds_nil: forall i k,
    defs_closed i k dNil
| clds_cons: forall i k d1 ds2,
    def_closed i k d1 ->
    defs_closed i k ds2 ->
    defs_closed i k (dCons d1 ds2)
with ty_closed: nat -> nat -> ty -> Prop :=
| cl_top: forall i k,
    ty_closed i k TTop
| cl_bot: forall i k,
    ty_closed i k TBot
| cl_rcd: forall i k l T,
    ty_closed i k T ->
    ty_closed i k (TRcd l T)
| cl_all: forall i k T U,
    ty_closed i k T ->
    ty_closed i (S k) U ->
    ty_closed i k (TAll T U)
| cl_tag: forall i k T U,
    ty_closed i k T ->
    ty_closed i k U ->
    ty_closed i k (TTag T U)
| cl_proj: forall i k t,
    tm_closed i k t ->
    path t ->                   (* <----- *)
    ty_closed i k (TProj t)
| cl_bind: forall i k T,
    ty_closed i (S k) T ->
    ty_closed i k (TBind T)
| cl_and: forall i k T1 T2,
    ty_closed i k T1 ->
    ty_closed i k T2 ->
    ty_closed i k (TAnd T1 T2)
| cl_or: forall i k T1 T2,
    ty_closed i k T1 ->
    ty_closed i k T2 ->
    ty_closed i k (TOr T1 T2).

Definition tenv := list ty.

(* Term typing *)
Inductive tty: tenv -> tm -> ty -> nat -> Prop :=
| T_VarF: forall G x T n1,
    index x G = Some T ->
    ty_closed (S x) 0 T ->
    tty G (tVar (VarF x)) T (S n1)
| T_Lam: forall G T1 T2 T2' t2 t2' n1,
    tty (T1::G) t2' T2' n1 ->
    T2' = ty_open (tVar (VarF (length G))) T2 ->
    t2' = tm_open (tVar (VarF (length G))) t2 ->
    ty_closed (length G) 0 T1 ->
    ty_closed (length G) 1 T2 ->
    tm_closed (length G) 1 t2 ->
    tty G (tLam T1 t2) (TAll T1 T2) (S n1)
| T_Tag: forall G T n1,
    ty_closed (length G) 0 T ->
    tty G (tTag T) (TTag T T) (S n1)
| T_Obj: forall G ds ds' T T' TO n1,
    dsty (T'::G) ds' T' n1 ->
    T' = ty_open (tVar (VarF (length G))) T ->
    ds' = defs_open (tVar (VarF (length G))) ds ->
    dinitializations ds ->
    ty_closed (length G) 1 T ->
    defs_closed (length G) 1 ds ->
    TO = ty_open (tObj ds) T ->
    tty G (tObj ds) TO (S n1)
| T_Sel: forall l U G t n1,
    tty G t (TRcd l U) n1 ->
    tty G (tSel t l) U (S n1)
| T_App: forall G t1 t2 T2 T3 T3' n1 n2,
    tty G t1 (TAll T2 T3) n1 ->
    tty G t2 T2 n2 ->
    T3' = ty_open t2 T3 ->
    ty_closed (length G) 0 T3' -> (* ensures that T3 does not depend on arg OR t2 is a path *)
    tty G (tApp t1 t2) T3' (S (n1+n2))
| T_Pack: forall G p T T' n1,
    tty G p T' n1 ->
    T' = ty_open p T ->
    ty_closed (length G) 0 T' ->
    tty G p (TBind T) (S n1)
| T_Unpack: forall G p T T' n1,
    tty G p (TBind T) n1 ->
    T' = (ty_open p T) ->
    ty_closed (length G) 0 T' ->
    tty G p T' (S n1)
| T_Sub: forall G t T1 T2 n1 n2,
    tty G t T1 n1 ->
    stp G T1 T2 n2 ->
    tty G t T2 (S (n1+n2))
with dty: tenv -> lb -> def -> ty -> nat -> Prop :=
| D_Some: forall G l t T n1,
    tty G t T n1 ->
    dty G l (dSome T t) (TRcd l T) (S n1)
| D_None: forall G l n1,
    dty G l dNone TTop (S n1)
with dsty: tenv -> defs -> ty -> nat -> Prop :=
| D_Nil: forall G n1,
    dsty G dNil TTop (S n1)
| D_Cons: forall G l d T ds TS n1 n2,
    l = defs_length ds ->
    dty G l d T n1 ->
    dsty G ds TS n2 ->
    dsty G (dCons d ds) (TAnd T TS) (S (n1+n2))

(* Subtyping *)
with stp: tenv -> ty -> ty -> nat -> Prop :=
| stp_top: forall G T n1,
    ty_closed (length G) 0 T ->
    stp G T TTop (S n1)
| stp_bot: forall G T n1,
    ty_closed (length G) 0 T ->
    stp G TBot T (S n1)
| stp_rcd: forall G l T1 T2 n1,
    stp G T1 T2 n1 ->
    stp G (TRcd l T1) (TRcd l T2) (S n1)
| stp_all: forall G T1 T2 T3 T4 T2' T4' n1 n2,
    T2' = ty_open (tVar (VarF (length G))) T2 ->
    T4' = ty_open (tVar (VarF (length G))) T4 ->
    ty_closed (length G) 1 T2 ->
    ty_closed (length G) 1 T4 ->
    stp G T3 T1 n1 ->
    stp (T3::G) T2' T4' n2 ->
    stp G (TAll T1 T2) (TAll T3 T4) (S (n1+n2))
| stp_tag: forall G T1 T2 T3 T4 n1 n2,
    stp G T3 T1 n2 ->
    stp G T2 T4 n1 ->
    stp G (TTag T1 T2) (TTag T3 T4) (S (n1+n2))
| stp_projx: forall G p n1,
    path p ->
    tm_closed (length G) 0 p ->
    stp G (TProj p) (TProj p) (S n1)
(* stp_proj1/2 are a generalization of stp_strong_proj1/2, so can we get rid of them?
    Or do stp_proj1/2 allow too much?
| stp_strong_proj1: forall G l ds T1 T2 T3 n1,
    (* oh no, subsumption, and we're too general to prevent it! will we get away with this? *)
    defs_index l (defs_open (tObj ds) ds) = dSome (TTag T1 T3) (tTag T2) ->
    defs_closed (length G) 1 ds ->
    stp G (TProj (tSel (tObj ds) l)) T3 (S n1)
| stp_strong_proj2: forall G l ds T1 T2 T3 n1,
    defs_index l (defs_open (tObj ds) ds) = dSome (TTag T1 T3) (tTag T2) ->
    defs_closed (length G) 1 ds ->
    stp G T1 (TProj (tSel (tObj ds) l)) (S n1)
*)
| stp_proj1: forall G p T1 T2 n1,
    pty G p (TTag T1 T2) n1 ->
    stp G (TProj p) T2 (S n1)
| stp_proj2: forall G p T1 T2 n1,
    pty G p (TTag T1 T2) n1 ->
    stp G T1 (TProj p) (S n1)
| stp_bind1: forall G T1 T1' T2 n1,
    pty (T1'::G) (tVar (VarF (length G))) T2 n1 ->
    T1' = ty_open (tVar (VarF (length G))) T1 ->
    ty_closed (length G) 1 T1 ->
    ty_closed (length G) 0 T2 ->
    stp G (TBind T1) T2 (S n1)
| stp_bindx: forall G T1 T1' T2 T2' n1,
    pty (T1'::G) (tVar (VarF (length G))) T2' n1 ->
    T1' = ty_open (tVar (VarF (length G))) T1 ->
    T2' = ty_open (tVar (VarF (length G))) T2 ->
    ty_closed (length G) 1 T1 ->
    ty_closed (length G) 1 T2 ->
    stp G (TBind T1) (TBind T2) (S n1)
| stp_and11: forall G T1 T2 T n1,
    stp G T1 T n1 ->
    ty_closed (length G) 0 T2 ->
    stp G (TAnd T1 T2) T (S n1)
| stp_and12: forall G T1 T2 T n1,
    stp G T2 T n1 ->
    ty_closed (length G) 0 T1 ->
    stp G (TAnd T1 T2) T (S n1)
| stp_and2: forall G T1 T2 T n1 n2,
    stp G T T1 n1 ->
    stp G T T2 n2 ->
    stp G T (TAnd T1 T2) (S (n1+n2))
| stp_or21: forall G T1 T2 T n1,
    stp G T T1 n1 ->
    ty_closed (length G) 0 T2 ->
    stp G T (TOr T1 T2) (S n1)
| stp_or22: forall G T1 T2 T n1,
    stp G T T2 n1 ->
    ty_closed (length G) 0 T1 ->
    stp G T (TOr T1 T2) (S n1)
| stp_or1: forall G T1 T2 T n1 n2,
    stp G T1 T n1 ->
    stp G T2 T n2 ->
    stp G (TOr T1 T2) T (S (n1+n2))
| stp_trans: forall G T1 T2 T3 n1 n2,
    stp G T1 T2 n1 ->
    stp G T2 T3 n2 ->
    stp G T1 T3 (S (n1+n2))

(* Path typing *)
with pty: tenv -> tm -> ty -> nat -> Prop :=
(* let's see when this breaks: *)
| pty_p: forall G p T n1,
    tty G p T n1 ->
    path p ->
    pty G p T (S n1)
(*
| pty_vr: forall G x TX n1,
    index x G = Some TX ->
    ty_closed (S x) 0 TX ->
    pty G x TX (S n1)
| pty_bind: forall G x TX n1,
    pty G x (TBind TX) n1 ->
    ty_closed x 1 TX ->
    pty G x (ty_open 0 (VarF x) TX) (S n1)
| pty_sub: forall G GU GL x T1 T2 n1 n2,
    (* use restricted G. note: this is slightly different
    from the big-step version b/c here we do not distinguish
    if vriables are bound in terms vs types. it would be easy
    to do exactly the same thing by adding this distinction. *)
    pty G x T1 n1 ->
    stp GL T1 T2 n2 ->
    length GL = S x ->
    G = GU ++ GL ->
    pty G x T2 (S (n1+n2))
*).



(* BEWARE: in dot_storeless_tidy, xxx_subst means substitution, but subst_xxx means opening!!! *)

(*
Fixpoint vr_subst (u: vr) (v: vr) {struct v}: vr :=
  match v with
    | VarF i  => if beq_nat i 0 then u else VarF (i-1)
    | VarB i  => VarB i
    | VObj ds => VObj (defs_subst u ds)
  end
with subst (u: vr) (T: ty) {struct T}: ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TMem l T1 T2 => TMem l (subst u T1) (subst u T2)
    | TProj v1 l    => TProj (vr_subst u v1) l
    | TFun l T1 T2 => TFun l (subst u T1) (subst u T2)
    | TBind T2     => TBind (subst u T2)
    | TAnd T1 T2   => TAnd (subst u T1) (subst u T2)
    | TOr T1 T2    => TOr (subst u T1) (subst u T2)
  end
with tm_subst (u: vr) (t: tm) { struct t }: tm :=
   match t with
     | tvr v => tvr (vr_subst u v)
     | tApp t1 l t2 => tApp (tm_subst u t1) l (tm_subst u t2)
   end
with def_subst (u: vr) (d: def) { struct d }: def :=
   match d with
     | dfun T1 T2 t2 => dfun (subst u T1) (subst u T2) (tm_subst u t2)
     | dty T1 => dty (subst u T1)
   end
with defs_subst (u: vr) (ds: defs) { struct ds }: defs :=
   match ds with
     | dNil => dNil
     | dCons d ds => dCons (def_subst u d) (defs_subst u ds)
   end.

Definition subst_defs (u:defs) (ds: defs) := defs_open 0 (VObj u) ds.
Definition subst_def (x:defs) (D: def) := def_open 0 (VObj x) D.
Definition subst_tm (x:defs) (t: tm) := tm_open 0 (VObj x) t.
Definition subst_ty (x:defs) (T: ty) := ty_open 0 (VObj x) T.
Definition substt (x:defs) (T: ty) := (subst (VObj x) T).
Hint Immediate substt.
*)

(* Possible types of a value *)
Inductive vtp: nat(*pack count*) -> tm(*must be a value*) -> ty(*possible type*) -> nat(*size*) -> Prop :=
| vtp_top: forall m v n1,
    value v ->
    tm_closed 0 0 v ->
    vtp m v TTop (S n1)
| vtp_rcd: forall m l ds t T n1,
    defs_index l (defs_open (tObj ds) ds) = dSome T t ->
    defs_closed 0 1 ds ->
    vtp m (tObj ds) (TRcd l T) (S n1)
| vtp_all: forall m T1 T2' T3 T4 T4' t2 n1 n2 n3,
    tty [T1] t2 T2' n1 ->
    stp [] T3 T1 n2 ->
    ty_closed 1 0 T2' ->
    ty_closed 0 1 T4 ->
    tm_closed 0 1 t2 ->
    T4' = ty_open (tVar (VarF 0)) T4 ->
    stp [T3] T2' T4' n3 ->
    vtp m (tLam T1 t2) (TAll T3 T4) (S (n1+n2+n3))
| vtp_tag: forall m T1 TX T2 n1 n2,
    stp [] T1 TX n1 ->
    stp [] TX T2 n2 ->
    vtp m (tTag TX) (TTag T1 T2) (S (n1+n2))
(* Note: only works for paths of length 0 and 1 (keep it simple for the moment) *)
| vtp_proj0: forall m v TX n1,
    vtp m v TX n1 ->
    vtp m v (TProj (tTag TX)) (S n1)
| vtp_proj1: forall l ds m v T1 T2 T3 n1,
    defs_index l (defs_open (tObj ds) ds) = dSome (TTag T1 T3) (tTag T2) ->
    defs_closed 0 1 ds ->
    vtp m v T2 n1 ->
    vtp m v (TProj (tSel (tObj ds) l)) (S n1)
(*
| vtp_proj: forall m v p TX n1,
    tty [] p (TTag TX TTop) n1 -> (* can we afford term typing here??? empty tenv guarantees that 
      p begins with a value, not with a var, but still ... *)
    vtp m v TX n1 ->
    vtp m v (TProj p) (S (n1))
*)
| vtp_bind: forall m ds T2 n1,
    vtp m (tObj ds) (ty_open (tObj ds) T2) n1 ->
    ty_closed 0 1 T2 ->
    vtp (S m) (tObj ds) (TBind T2) (S (n1))
| vtp_and: forall m m1 m2 ds T1 T2 n1 n2,
    vtp m1 ds T1 n1 ->
    vtp m2 ds T2 n2 ->
    m1 <= m -> m2 <= m ->
    vtp m ds (TAnd T1 T2) (S (n1+n2))
| vtp_or1: forall m m1 m2 ds T1 T2 n1,
    vtp m1 ds T1 n1 ->
    ty_closed 0 0 T2 ->
    m1 <= m -> m2 <= m ->
    vtp m ds (TOr T1 T2) (S (n1))
| vtp_or2: forall m m1 m2 ds T1 T2 n1,
    vtp m1 ds T2 n1 ->
    ty_closed 0 0 T1 ->
    m1 <= m -> m2 <= m ->
    vtp m ds (TOr T1 T2) (S (n1)).

Definition ttyd G x T1 := exists n, tty G x T1 n.

Definition stpd G T1 T2 := exists n, stp G T1 T2 n.

Definition ptyd G x T1 := exists n, pty G x T1 n.

Definition vtpd m x T1 := exists n, vtp m x T1 n.

Definition vtpdd m x T1 := exists m1 n, vtp m1 x T1 n /\ m1 <= m.

Hint Unfold tenv.
Hint Constructors stp.
Hint Constructors vtp.

Ltac ep := match goal with
             | [ |- stp ?G ?T1 ?T2 ?N ] => assert (exists (n:nat), stp G T1 T2 n) as EEX
           end.

Ltac eu := match goal with
             | H: ttyd _ _ _ |- _ => destruct H as [? H]
             | H: stpd _ _ _ |- _ => destruct H as [? H]
             | H: ptyd _ _ _ |- _ => destruct H as [? H]
             | H: vtpd _ _ _ |- _ => destruct H as [? H]
             | H: vtpdd _ _ _ |- _ => destruct H as [? [? [H ?]]]
           end.

Lemma stpd_bot: forall G T,
    ty_closed (length G) 0 T ->
    stpd G TBot T.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd_top: forall G T,
    ty_closed (length G) 0 T ->
    stpd G T TTop.
Proof. intros. exists 1. eauto. Qed.


Lemma stpd_trans: forall G T1 T2 T3,
    stpd G T1 T2 ->
    stpd G T2 T3 ->
    stpd G T1 T3.
Proof. intros. repeat eu. eexists. eauto. Qed.




Hint Constructors ty.

Hint Constructors stp.
Hint Constructors vtp.
Hint Constructors pty.
Hint Constructors tty.

Hint Unfold ttyd.
Hint Unfold stpd.
Hint Unfold vtpd.
Hint Unfold vtpdd.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.


Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.





Lemma index_max: forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  Case "nil". intros. inversion H.
  Case "cons".
  intros. inversion H.
  case_eq (beq_nat n (length vs)); intros E.
  SCase "hit".
  rewrite E in H1. inversion H1. subst.
  eapply beq_nat_true in E.
  unfold length. unfold length in E. rewrite E. eauto.
  SCase "miss".
  rewrite E in H1.
  assert (n < length vs). eapply IHvs. apply H1.
  compute. eauto.
Qed.

Lemma index_exists: forall X vs n,
                       n < length vs ->
                       exists (T:X), index n vs = Some T.
Proof.
  intros X vs. induction vs.
  Case "nil". intros. inversion H.
  Case "cons".
  intros. inversion H.
  SCase "hit".
  assert (beq_nat n (length vs) = true) as E. eapply beq_nat_true_iff. eauto.
  simpl. subst n. rewrite E. eauto.
  SCase "miss".
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff. omega.
  simpl. rewrite E. eapply IHvs. eauto.
Qed.


Lemma index_extend: forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply index_max. eauto.
  assert (n <> length vs). omega.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff; eauto.
  unfold index. unfold index in H. rewrite H. rewrite E. reflexivity.
Qed.

Lemma plus_lt_contra: forall a b,
  a + b < b -> False.
Proof.
  intros a b H. induction a.
  - simpl in H. apply lt_irrefl in H. assumption.
  - simpl in H. apply IHa. omega.
Qed.

Lemma index_extend_mult: forall {X} G0 G2 x0 (T:X),
    index x0 G0 = Some T ->
    index x0 (G2++G0) = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl. assumption.
  - simpl.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E.
      apply index_max in H. subst.
      rewrite app_length in H. apply plus_lt_contra in H. inversion H.
    + apply IHG2. assumption.
Qed.

Scheme ty_mut   := Induction for ty   Sort Prop
with   tm_mut   := Induction for tm   Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme syntax_mutind from ty_mut, tm_mut, def_mut, defs_mut.

Scheme ty_cl_mut := Induction for ty_closed Sort Prop
with   tm_cl_mut := Induction for tm_closed Sort Prop
with   def_cl_mut := Induction for def_closed Sort Prop
with   defs_cl_mut := Induction for defs_closed Sort Prop.
Combined Scheme closed_mutind from ty_cl_mut, tm_cl_mut, def_cl_mut, defs_cl_mut.

Lemma closed_upgrade_gh_rec:
  (forall i k v1, vr_closed i k v1 -> forall i1, i <= i1 -> vr_closed i1 k v1) /\
  (forall i k T1, ty_closed i k T1 -> forall i1, i <= i1 -> ty_closed i1 k T1) /\
  (forall i k t1, tm_closed i k t1 -> forall i1, i <= i1 -> tm_closed i1 k t1) /\
  (forall i k d1, def_closed i k d1 -> forall i1, i <= i1 -> def_closed i1 k d1) /\
  (forall i k ds1, defs_closed i k ds1 -> forall i1, i <= i1 -> defs_closed i1 k ds1).
Proof.
  assert (H: (forall i k v1, vr_closed i k v1 -> forall i1, i <= i1 -> vr_closed i1 k v1)). {
    intros. inversions H; econstructor; omega.
  }
  apply (conj H).
  apply closed_mutind; intros; econstructor; eauto.
Qed.

Lemma closed_upgrade_gh: forall i i1 k T1,
  ty_closed i k T1 -> i <= i1 -> ty_closed i1 k T1.
Proof.
  intros. eapply (proj1 (proj2 closed_upgrade_gh_rec)); eauto.
Qed.

Lemma closed_upgrade_rec:
  (forall i k v1, vr_closed i k v1 -> forall k1, k <= k1 -> vr_closed i k1 v1) /\
  (forall i k T1, ty_closed i k T1 -> forall k1, k <= k1 -> ty_closed i k1 T1) /\
  (forall i k t1, tm_closed i k t1 -> forall k1, k <= k1 -> tm_closed i k1 t1) /\
  (forall i k d1, def_closed i k d1 -> forall k1, k <= k1 -> def_closed i k1 d1) /\
  (forall i k ds1, defs_closed i k ds1 -> forall k1, k <= k1 -> defs_closed i k1 ds1).
Proof.
(*
  apply closed_mutind; intros; econstructor; eauto;
  try solve [omega];
  try solve [eapply H; omega];
  try solve [eapply H0; omega];
  try solve [eapply H1; omega].
Qed.
*)
Admitted.

Lemma closed_upgrade: forall i k k1 T1,
  ty_closed i k T1 -> k <= k1 -> ty_closed i k1 T1.
Proof.
  intros. eapply (proj1 (proj2 closed_upgrade_rec)); eauto.
Qed.

Lemma closed_open_rec:
  (forall v1, forall j k v, vr_closed k (j+1) v1 -> tm_closed k j v -> tm_closed k j (vr_open_rec j v v1)) /\
  (forall T1, forall j k v, ty_closed k (j+1) T1 -> tm_closed k j v -> ty_closed k j (ty_open_rec j v T1)) /\
  (forall t1, forall j k v, tm_closed k (j+1) t1 -> tm_closed k j v -> tm_closed k j (tm_open_rec j v t1)) /\
  (forall d1, forall j k v, def_closed k (j+1) d1 -> tm_closed k j v -> def_closed k j (def_open_rec j v d1)) /\
  (forall ds1, forall j k v, defs_closed k (j+1) ds1 -> tm_closed k j v -> defs_closed k j (defs_open_rec j v ds1)).
Proof.
(*
  apply syntax_mutind; intros;
  try solve [
        try inversion H; try inversion H0; try inversion H1; try inversion H2;
        subst; simpl; econstructor;
        try (eapply H; eauto); try (eapply H0; eauto); try (eapply H1; eauto);
        eauto;
        try solve [omega];
        try solve [eapply (proj1 closed_upgrade_rec); eauto]
      ].
  - inversion H; subst. simpl.
    case_eq (beq_nat j i); intros E; eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
Qed.
*)
Admitted.

(*
Lemma closed_open: forall j k v T, ty_closed k (j+1) T -> vr_closed k j v -> ty_closed k j (ty_open j v T).
Proof.
  intros. eapply (proj1 (proj2 closed_open_rec)); eauto.
Qed.

Lemma beq_nat_true_eq: forall A, beq_nat A A = true.
Proof. intros. eapply beq_nat_true_iff. eauto. Qed.



Lemma closed_no_open_rec:
  (forall l j v, vr_closed l j v -> forall vx, v = vr_open j vx v) /\
  (forall l j T, ty_closed l j T -> forall vx, T = ty_open j vx T) /\
  (forall l j t, tm_closed l j t -> forall vx, t = tm_open j vx t) /\
  (forall l j d, def_closed l j d -> forall vx, d = def_open j vx d) /\
  (forall l j ds, defs_closed l j ds -> forall vx, ds = defs_open j vx ds).
Proof.
  apply closed_mutind; intros; eauto; simpl;
  try (rewrite <- H); try (rewrite <- H0); try (rewrite <- H1); eauto.
  - simpl.
    assert (k <> x) as A. omega.
    eapply beq_nat_false_iff in A. rewrite A. reflexivity.
Qed.

Lemma closed_no_open: forall T x l j,
  ty_closed l j T ->
  T = ty_open j (VarF x) T.
Proof.
  intros. eapply (proj1 (proj2 closed_no_open_rec)); eauto.
Qed.

Lemma closed_no_subst_rec:
  (forall v j, vr_closed 0 j v -> forall vx, vr_subst vx v = v) /\
  (forall T j, ty_closed 0 j T -> forall vx, subst vx T = T) /\
  (forall t j, tm_closed 0 j t -> forall vx, tm_subst vx t = t) /\
  (forall d j, def_closed 0 j d -> forall vx, def_subst vx d = d) /\
  (forall ds j, defs_closed 0 j ds -> forall vx, defs_subst vx ds = ds).
Proof.
  apply syntax_mutind; intros;
  try inversion H; try inversion H0; try inversion H1; try inversion H2;
  subst; simpl; f_equal;
  try solve [erewrite H; eauto];
  try solve [erewrite H0; eauto];
  try solve [erewrite H1; eauto];
  eauto; try omega.
Qed.

Lemma closed_no_subst: forall T k TX,
   ty_closed 0 k T ->
   subst TX T = T.
Proof.
  intros. eapply (proj1 (proj2 closed_no_subst_rec)); eauto.
Qed.

Lemma closed_subst_rec:
  (forall v j n V, vr_closed (n+1) j v -> vr_closed n 0 V -> vr_closed n j (vr_subst V v)) /\
  (forall T j n V, ty_closed (n+1) j T -> vr_closed n 0 V -> ty_closed n j (subst V T)) /\
  (forall t j n V, tm_closed (n+1) j t -> vr_closed n 0 V -> tm_closed n j (tm_subst V t)) /\
  (forall d j n V, def_closed (n+1) j d -> vr_closed n 0 V -> def_closed n j (def_subst V d)) /\
  (forall ds j n V, defs_closed (n+1) j ds -> vr_closed n 0 V -> defs_closed n j (defs_subst V ds)).
Proof.
  apply syntax_mutind; intros;
  try inversion H; try inversion H0; try inversion H1; try inversion H2;
  subst; simpl; try econstructor;
  try solve [eapply H; eauto];
  try solve [eapply H0; eauto];
  try solve [eapply H1; eauto];
  eauto; try omega;
  try solve [case_eq (beq_nat i 0); intros E; [
    (eapply (proj1 closed_upgrade_rec); eauto; omega) |
    (econstructor; eapply beq_nat_false_iff in E; omega) ]].
Qed.

Lemma closed_subst: forall j n V T, ty_closed (n+1) j T -> vr_closed n 0 V -> ty_closed n j (subst V T).
Proof.
  intros. eapply (proj1 (proj2 closed_subst_rec)); eauto.
Qed.

Lemma subst_open_distribute: forall k j0 vx v,
  vr_closed k j0 vx ->
  (forall v0 j, j0 <= j -> vr_subst vx (vr_open j v v0) = vr_open j (vr_subst vx v) (vr_subst vx v0)) /\
  (forall T0 j, j0 <= j -> subst vx (ty_open j v T0) = ty_open j (vr_subst vx v) (subst vx T0)) /\
  (forall t0 j, j0 <= j -> tm_subst vx (tm_open j v t0) = tm_open j (vr_subst vx v) (tm_subst vx t0)) /\
  (forall d0 j, j0 <= j -> def_subst vx (def_open j v d0) = def_open j (vr_subst vx v) (def_subst vx d0)) /\
  (forall ds0 j, j0 <= j -> defs_subst vx (defs_open j v ds0) = defs_open j (vr_subst vx v) (defs_subst vx ds0)).
Proof.
  intros k j0 vx v HCx.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat i 0); intros E; simpl; eauto.
    eapply (proj1 closed_no_open_rec).
    eapply (proj1 closed_upgrade_rec). eauto. omega.
  - case_eq (beq_nat j i); intros E; simpl; eauto.
Qed.

Lemma subst_open_commute0_rec:
  (forall v0 j TX, vr_closed 0 (j+1) v0 -> (vr_subst TX (vr_open j (VarF 0) v0)) = vr_open j TX v0) /\
  (forall T0 j TX, ty_closed 0 (j+1) T0 -> (subst TX (ty_open j (VarF 0) T0)) = ty_open j TX T0) /\
  (forall t0 j TX, tm_closed 0 (j+1) t0 -> (tm_subst TX (tm_open j (VarF 0) t0)) = tm_open j TX t0) /\
  (forall d0 j TX, def_closed 0 (j+1) d0 -> (def_subst TX (def_open j (VarF 0) d0)) = def_open j TX d0) /\
  (forall ds0 j TX, defs_closed 0 (j+1) ds0 -> (defs_subst TX (defs_open j (VarF 0) ds0)) = defs_open j TX ds0).
Proof.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - inversion H; subst. omega.
  - inversion H; subst.
    case_eq (beq_nat j i); intros E; simpl; eauto.
Qed.

Lemma subst_open_commute0: forall T0 j TX,
  ty_closed 0 (j+1) T0 ->
  (subst TX (ty_open j (VarF 0) T0)) = ty_open j TX T0.
Proof.
  intros. eapply (proj1 (proj2 subst_open_commute0_rec)); eauto.
Qed.

Lemma subst_open_commute1_rec: forall x x0,
  vr_closed 0 0 (VObj x) ->
  vr_closed 0 0 (VObj x0) ->
  (forall v0 j, (vr_open j (VObj x0) (vr_subst (VObj x) v0)) = (vr_subst (VObj x) (vr_open j (VObj x0) v0))) /\
  (forall T0 j, (ty_open j (VObj x0) (subst (VObj x) T0)) = (subst (VObj x) (ty_open j (VObj x0) T0))) /\
  (forall t0 j, (tm_open j (VObj x0) (tm_subst (VObj x) t0)) = (tm_subst (VObj x) (tm_open j (VObj x0) t0))) /\
  (forall d0 j, (def_open j (VObj x0) (def_subst (VObj x) d0)) = (def_subst (VObj x) (def_open j (VObj x0) d0))) /\
  (forall ds0 j, (defs_open j (VObj x0) (defs_subst (VObj x) ds0)) = (defs_subst (VObj x) (defs_open j (VObj x0) ds0))).
Proof.
  intros x x0 HCx HCx0.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat i 0); intros E; simpl; eauto.
    erewrite <- (proj2 (proj2 (proj2 (proj2 closed_no_open_rec)))).
    reflexivity.
    inversion HCx; subst.
    eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_rec)))); eauto.
    omega.
  - case_eq (beq_nat j i); intros E; simpl; eauto.
    erewrite (proj2 (proj2 (proj2 (proj2 closed_no_subst_rec)))).
    reflexivity.
    inversion HCx0; subst.
    eassumption.
Qed.

Lemma subst_open_commute1: forall x x0,
  vr_closed 0 0 (VObj x) ->
  vr_closed 0 0 (VObj x0) -> forall j T0,
 (ty_open j (VObj x0) (subst (VObj x) T0))
 = (subst (VObj x) (ty_open j (VObj x0) T0)).
Proof.
  intros x x0 Hx Hx0. intros.
  eapply (proj1 (proj2 (subst_open_commute1_rec x x0 Hx Hx0))); eauto.
Qed.
*)

Lemma subst_closed_id: forall x k T2,
  ty_closed 0 k T2 ->
  substt x T2 = T2.
Admitted.
(*
Proof. intros. eapply closed_no_subst. eauto. Qed.

Lemma closed_subst0: forall i k x T2,
  vr_closed i 0 (VObj x) ->
  ty_closed (i + 1) k T2 ->
  ty_closed i k (substt x T2).
Proof. intros. eapply closed_subst. eauto. eauto. Qed.

Lemma closed_subst1: forall i k x T2,
  ty_closed i k T2 -> i <> 0 ->
  vr_closed (i-1) 0 (VObj x) ->
  ty_closed (i-1) k (substt x T2).
Proof.
  intros. eapply closed_subst.
  assert ((i - 1 + 1) = i) as R. omega.
  rewrite R. eauto. eauto.
Qed.

Lemma index_subst: forall G TX T0 T3 x,
  index (length (G ++ [TX])) (T0 :: G ++ [TX]) = Some T3 ->
  index (length G) (map (substt x) (T0 :: G)) = Some (substt x T3).
Proof.
  intros G. induction G; intros; inversion H.
  - eauto.
  - rewrite beq_nat_true_eq in H1. inversion H1. subst. simpl.
    rewrite map_length. rewrite beq_nat_true_eq. eauto.
Qed.

Lemma index_subst1: forall G TX T3 x x0,
  index x0 (G ++ [TX]) = Some T3 -> x0 <> 0 ->
  index (x0-1) (map (substt x) G) = Some (substt x T3).
Proof.
  intros G. induction G; intros; inversion H.
  - eapply beq_nat_false_iff in H0. rewrite H0 in H2. inversion H2.
  - simpl.
    assert (beq_nat (x0 - 1) (length (map (substt x) G)) = beq_nat x0 (length (G ++ [TX]))). {
      case_eq (beq_nat x0 (length (G ++ [TX]))); intros E.
      eapply beq_nat_true_iff. rewrite map_length. eapply beq_nat_true_iff in E. subst x0.
      rewrite app_length. simpl. omega.
      eapply beq_nat_false_iff. eapply beq_nat_false_iff in E.
      rewrite app_length in E. simpl in E. rewrite map_length.
      destruct x0. destruct H0. reflexivity. omega.
    }
    rewrite H1. case_eq (beq_nat x0 (length (G ++ [TX]))); intros E; rewrite E in H2.
    inversion H2. subst. eauto. eauto.
Qed.

Lemma index_hit0: forall (G:tenv) TX T2,
 index 0 (G ++ [TX]) = Some T2 -> T2 = TX.
Proof.
  intros G. induction G; intros; inversion H.
  - eauto.
  - rewrite app_length in H1. simpl in H1.
    remember (length G + 1) as L. destruct L. omega. eauto.
Qed.

Lemma subst_open_rec: forall k x,
  (vr_closed k 0 (VObj x)) ->
  (forall v j n, (vr_subst (VObj x) (vr_open j (VarF (n+1)) v)) = (vr_open j (VarF n) (vr_subst (VObj x) v))) /\
  (forall T j n, (subst (VObj x) (ty_open j (VarF (n+1)) T)) = (ty_open j (VarF n) (subst (VObj x) T))) /\
  (forall t j n, (tm_subst (VObj x) (tm_open j (VarF (n+1)) t)) = (tm_open j (VarF n) (tm_subst (VObj x) t))) /\
  (forall d j n, (def_subst (VObj x) (def_open j (VarF (n+1)) d)) = (def_open j (VarF n) (def_subst (VObj x) d))) /\
  (forall ds j n, (defs_subst (VObj x) (defs_open j (VarF (n+1)) ds)) = (defs_open j (VarF n) (defs_subst (VObj x) ds))).
Proof.
  intros k x Hx.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat i 0); intros E; simpl; eauto.
    f_equal.
    erewrite <- (proj2 (proj2 (proj2 (proj2 closed_no_open_rec)))).
    reflexivity. inversion Hx; subst.
    eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_rec)))). eauto. omega.
  - case_eq (beq_nat j i); intros E; simpl; eauto.
    assert (beq_nat (n + 1) 0 = false) as E1. {
      apply beq_nat_false_iff. omega.
    }
    rewrite E1.
    f_equal. omega.
Qed.

Lemma subst_open: forall k x, vr_closed k 0 (VObj x) ->
  forall TX n j,
  (substt x (ty_open j (VarF (n+1)) TX)) =
  (ty_open j (VarF n) (substt x TX)).
Proof.
  intros k x Hx. intros. eapply (proj1 (proj2 (subst_open_rec k x Hx))); eauto.
Qed.

Lemma subst_open3: forall k x, vr_closed k 0 (VObj x) -> forall TX0 (G:tenv) TX,
  (substt x (ty_open 0 (VarF (length (G ++ [TX]))) TX0)) =
  (ty_open 0 (VarF (length G)) (substt x TX0)).
Proof. intros. rewrite app_length. simpl. eapply subst_open. eauto. Qed.

Lemma subst_open4: forall k x, vr_closed k 0 (VObj x) -> forall T0 (G:tenv) TX,
  substt x (ty_open 0 (VarF (length (G ++ [TX]))) T0) =
  ty_open 0 (VarF (length (map (substt x) G))) (substt x T0).
Proof. intros. rewrite map_length. eapply subst_open3. eauto. Qed.

Lemma subst_open5: forall k x, vr_closed k 0 (VObj x) -> forall (G:tenv) T0 xi,
  xi <> 0 -> substt x (ty_open 0 (VarF xi) T0) =
  ty_open 0 (VarF (xi-1)) (substt x T0).
Proof.
  intros. remember (xi-1) as n. assert (xi=n+1) as R. omega. rewrite R.
  eapply subst_open. eauto.
Qed.

Lemma subst_open_commute0b_rec: forall k x,
  (vr_closed k 0 (VObj x)) ->
  (forall v1 n, vr_subst (VObj x) (vr_open n (VarF 0) v1) = vr_open n (VObj x) (vr_subst (VObj x) v1)) /\
  (forall T1 n, subst (VObj x) (ty_open n (VarF 0) T1) = ty_open n (VObj x) (subst (VObj x) T1)) /\
  (forall t1 n, tm_subst (VObj x) (tm_open n (VarF 0) t1) = tm_open n (VObj x) (tm_subst (VObj x) t1)) /\
  (forall d1 n, def_subst (VObj x) (def_open n (VarF 0) d1) = def_open n (VObj x) (def_subst (VObj x) d1)) /\
  (forall ds1 n, defs_subst (VObj x) (defs_open n (VarF 0) ds1) = defs_open n (VObj x) (defs_subst (VObj x) ds1)).
Proof.
  intros k x Hx.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat i 0); intros E; simpl; eauto.
    erewrite <- (proj2 (proj2 (proj2 (proj2 closed_no_open_rec)))).
    reflexivity.
    inversion Hx; subst.
    eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_rec)))); eauto.
    omega.
  - case_eq (beq_nat n i); intros E; simpl; eauto.
Qed.

Lemma subst_open_commute0b: forall k x,
  (vr_closed k 0 (VObj x)) -> forall T1 n,
  substt x (ty_open n (VarF 0) T1) = ty_open n (VObj x) (substt x T1).
Proof.
  unfold substt.
  intros k x Hx. intros.
  eapply (proj1 (proj2 (subst_open_commute0b_rec k x Hx))); eauto.
Qed.

Lemma subst_open_commute_z_rec: forall k x,
  (vr_closed k 0 (VObj x)) ->
  (forall v1 z n, vr_subst (VObj x) (vr_open n (VarF (z + 1)) v1) = vr_open n (VarF z) (vr_subst (VObj x) v1)) /\
  (forall T1 z n, subst (VObj x) (ty_open n (VarF (z + 1)) T1) = ty_open n (VarF z) (subst (VObj x) T1)) /\
  (forall t1 z n, tm_subst (VObj x) (tm_open n (VarF (z + 1)) t1) = tm_open n (VarF z) (tm_subst (VObj x) t1)) /\
  (forall d1 z n, def_subst (VObj x) (def_open n (VarF (z + 1)) d1) = def_open n (VarF z) (def_subst (VObj x) d1)) /\
  (forall ds1 z n, defs_subst (VObj x) (defs_open n (VarF (z + 1)) ds1) = defs_open n (VarF z) (defs_subst (VObj x) ds1)).
Proof.
  intros k x Hx.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat i 0); intros E; simpl; eauto.
    erewrite <- (proj2 (proj2 (proj2 (proj2 closed_no_open_rec)))).
    reflexivity.
    inversion Hx; subst.
    eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_rec)))); eauto.
    omega.
  - case_eq (beq_nat n i); intros E; simpl; eauto.
    assert (beq_nat (z + 1) 0 = false) as E1. {
      eapply beq_nat_false_iff. omega.
    }
    rewrite E1. f_equal. omega.
Qed.

Lemma subst_open_commute_z: forall k x,
 (vr_closed k 0 (VObj x)) -> forall T1 z n,
 subst (VObj x) (ty_open n (VarF (z + 1)) T1) =
 ty_open n (VarF z) (subst (VObj x) T1).
Proof.
  intros k x Hx. intros.
  eapply (proj1 (proj2 (subst_open_commute_z_rec k x Hx))); eauto.
Qed.

Lemma length_subst_defs: forall ds x,
  (length (defs_to_list ds))=(length (defs_to_list (subst_defs x ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma length_defs_subst: forall ds x,
  (length (defs_to_list ds))=(length (defs_to_list (defs_subst x ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma length_open_defs: forall ds x,
  (length (defs_to_list ds))=(length (defs_to_list (defs_open 0 (VObj x) ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma length_defs_open: forall ds v,
  (length (defs_to_list ds))=(length (defs_to_list (defs_open 0 v ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma index_subst_defs: forall ds ds0 D ds1 x,
  defs_to_list ds = ds0 ++ defs_to_list (dCons D ds1) ->
  index (length (defs_to_list ds1)) (defs_to_list (subst_defs x ds)) = Some (subst_def x D).
Proof.
  intros. generalize dependent ds1. generalize dependent ds. induction ds0; intros.
  - simpl in H. destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite <- length_open_defs. rewrite beq_nat_true_eq. reflexivity.
  - destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite false_beq_nat. eapply IHds0. eauto.
    rewrite <- length_open_defs. rewrite H2. rewrite app_length. simpl.
    omega.
Qed.

Lemma index_defs_open: forall ds ds0 D ds1 v,
  defs_to_list ds = ds0 ++ defs_to_list (dCons D ds1) ->
  index (length (defs_to_list ds1)) (defs_to_list (defs_open 0 v ds)) = Some (def_open 0 v D).
Proof.
  intros. generalize dependent ds1. generalize dependent ds. induction ds0; intros.
  - simpl in H. destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite <- length_defs_open. rewrite beq_nat_true_eq. reflexivity.
  - destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite false_beq_nat. eapply IHds0. eauto.
    rewrite <- length_defs_open. rewrite H2. rewrite app_length. simpl.
    omega.
Qed.

Lemma index_defs: forall ds ds0 D ds1,
  defs_to_list ds = ds0 ++ defs_to_list (dCons D ds1) ->
  index (length (defs_to_list ds1)) (defs_to_list ds) = Some D.
Proof.
  intros. generalize dependent ds1. generalize dependent ds. induction ds0; intros.
  - simpl in H. destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite beq_nat_true_eq. reflexivity.
  - destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite false_beq_nat. eapply IHds0. eauto.
    rewrite H2. rewrite app_length. simpl.
    omega.
Qed.

Lemma index_defs_open_eq: forall l x D Dx,
  vr_closed 0 0 (VObj x) ->
  index l (defs_to_list (subst_defs x x)) = Some D ->
  index l (defs_to_list (defs_open 0 (VarF 0) x)) = Some Dx ->
  def_subst (VObj x) Dx = D.
Proof.
  intros l x D Dx HC HI HIx.
  remember HC as HCx. clear HeqHCx.
  remember x as x0. rewrite Heqx0 in *.
  rewrite <- Heqx0 in HI at 1. rewrite <- Heqx0 in HC. rewrite <- Heqx0.
  clear Heqx0.
  remember x as dsb.
  remember (length (defs_to_list dsb)) as n.
  assert (n = length (defs_to_list (subst_defs x0 dsb))) as Heqn'. {
    subst. rewrite <- length_subst_defs. reflexivity.
  }
  assert (exists dsa,
            defs_to_list x = defs_to_list dsa ++ defs_to_list dsb /\
            defs_to_list (subst_defs x0 x) = defs_to_list (subst_defs x0 dsa) ++ defs_to_list (subst_defs x0 dsb)) as Hds. {
    exists dNil. simpl. subst. eauto.
  }
  destruct Hds as [dsa [Hds Hds']]. clear Heqdsb.
  remember (defs_to_list dsa) as la. clear Heqla.
  remember (defs_to_list (subst_defs x0 dsa)) as la'. clear Heqla'. clear dsa.
  generalize dependent Dx. generalize dependent D.
  generalize dependent la'. generalize dependent la. generalize dependent x.
  generalize dependent l. generalize dependent n.
  inversion HCx; subst. rename H2 into HCdsb. clear HCx.
  induction dsb; intros.
  - simpl in *. inversion HI.
  - simpl in HI. simpl in HIx.
    rewrite <- length_defs_open in HI. rewrite <- length_defs_open in HIx.
    inversion HCdsb; subst.
    case_eq (beq_nat l (length (defs_to_list dsb))); intros E;
    rewrite E in HI; rewrite E in HIx.
    + inversion HI. inversion HIx.
      rewrite (proj1 (proj2 (proj2 (proj2 (subst_open_distribute 0 0 (VObj x0) (VarF 0) HC))))).
      simpl.
      erewrite (proj1 (proj2 (proj2 (proj2 closed_no_subst_rec)))). reflexivity.
      eauto. omega.
    + eapply IHdsb with (x:=x) (la:=la ++ [d]) (la':=la' ++ [(subst_def x0 d)]); eauto.
      rewrite <- app_assoc. rewrite Hds. simpl. reflexivity.
      rewrite <- app_assoc. rewrite Hds'. simpl. reflexivity.
Qed.

Lemma index_subst_defs_eq: forall l ds D D',
  index l (defs_to_list ds) = Some D ->
  index l (defs_to_list (subst_defs ds ds)) = Some D' ->
  subst_def ds D = D'.
Proof.
  intros l ds D D' HI HI'.
  remember ds as x. rewrite Heqx in *. rewrite <- Heqx in HI' at 1.
  rewrite <- Heqx.  clear Heqx.
  remember ds as dsb.
  remember (length (defs_to_list dsb)) as n.
  assert (n = length (defs_to_list (subst_defs x dsb))) as Heqn'. {
    subst. rewrite <- length_subst_defs. reflexivity.
  }
  assert (exists dsa,
            defs_to_list ds = defs_to_list dsa ++ defs_to_list dsb /\
            defs_to_list (subst_defs x ds) = defs_to_list (subst_defs x dsa) ++ defs_to_list (subst_defs x dsb)) as Hds. {
    exists dNil. simpl. subst. eauto.
  }
  destruct Hds as [dsa [Hds Hds']]. clear Heqdsb.
  remember (defs_to_list dsa) as la. clear Heqla.
  remember (defs_to_list (subst_defs x dsa)) as la'. clear Heqla'. clear dsa.
  generalize dependent D'. generalize dependent D.
  generalize dependent la'. generalize dependent la. generalize dependent ds.
  generalize dependent l. generalize dependent n.
  induction dsb; intros.
  - simpl in *. inversion HI.
  - simpl in HI. case_eq (beq_nat l (length (defs_to_list dsb))); intros E;
    rewrite E in HI; simpl in HI'; rewrite <- length_open_defs in HI'; rewrite E in HI'.
    + inversion HI. subst d. inversion HI'. reflexivity.
    + eapply IHdsb with (ds:=ds) (la:=la ++ [d]) (la':=la' ++ [(subst_def x d)]); eauto.
      rewrite <-length_subst_defs. reflexivity.
      rewrite <- app_assoc. rewrite Hds. simpl. reflexivity.
      rewrite <- app_assoc. rewrite Hds'. simpl. reflexivity.
Qed.

Lemma index_def_closed: forall i k l ds D,
  defs_closed i k ds ->
  index l (defs_to_list ds) = Some D ->
  def_closed i k D.
Proof.
  intros. generalize dependent D. induction H; intros.
  - simpl in *. solve by inversion.
  - simpl in *.
    case_eq (beq_nat l (length (defs_to_list ds2))); intros E;
    rewrite E in *.
    + inversion H1. subst. assumption.
    + eapply IHdefs_closed; eauto.
Qed.

Lemma all_closed: forall ni,
  (forall G T1 T2 n,
     stp G T1 T2 n -> n < ni ->
     ty_closed (length G) 0 T1) /\
  (forall G T1 T2 n,
     stp G T1 T2 n -> n < ni ->
     ty_closed (length G) 0 T2) /\
  (forall m x T2 n,
     vtp m x T2 n -> n < ni ->
     ty_closed 0 0 T2) /\
  (forall x G T2 n,
     pty G x T2 n -> n < ni ->
     x < length G) /\
  (forall x G T2 n,
     pty G x T2 n -> n < ni ->
     ty_closed (length G) 0 T2) /\
  (forall G t T n,
     tty G t T n -> n < ni ->
     ty_closed (length G) 0 T) /\
  (forall G l d T n,
     dty G l d T n -> n < ni ->
     ty_closed (length G) 0 T) /\
  (forall G ds T n,
     dsty G ds T n -> n < ni ->
     ty_closed (length G) 0 T) /\
  (forall G t T n,
     tty G t T n -> n < ni ->
     tm_closed (length G) 0 t) /\
  (forall m x T2 n,
     vtp m x T2 n -> n < ni ->
     vr_closed 0 0 (VObj x)) /\
  (forall G l d T n,
     dty G l d T n -> n < ni ->
     def_closed (length G) 0 d) /\
  (forall G ds T n,
     dsty G ds T n -> n < ni ->
     defs_closed (length G) 0 ds).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H; destruct IHn as [IHS1 [IHS2 [IHV2 [IHH1 [IHH2 [IHT [IHD [IHD1 [IHT1 [IHV1 [IHD2 IHD3]]]]]]]]]]].
  (* stp left *)
  - econstructor.
  - eauto.
  - econstructor. eapply IHS2. eauto. omega. eauto.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS1. eauto. omega.
  - subst. econstructor. eauto.
  - subst. econstructor. eauto.
  - subst.
    assert (def_closed (length G) 0 (dty T1)) as A. {
      eapply index_def_closed. inversion H2; subst.
      eapply (proj2 (proj2 (proj2 (proj2 closed_open_rec)))).
      simpl. eassumption. eassumption.
      unfold subst_defs in *. eassumption.
    }
    inversion A; subst. eauto.
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. eauto.
  - econstructor. eauto.
  - econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. eauto. eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  - econstructor. eapply IHS1. eauto. omega. eapply IHS1. eauto. omega.
  - eapply IHS1. eauto. omega.
  (* stp right *)
  - eauto.
  - econstructor.
  - econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - subst. econstructor. eauto.
  - subst.
    assert (def_closed (length G) 0 (dty T2)) as A. {
      eapply index_def_closed. inversion H2; subst.
      eapply (proj2 (proj2 (proj2 (proj2 closed_open_rec)))).
      simpl. eassumption. eassumption.
      unfold subst_defs in *. eassumption.
    }
    inversion A; subst. eauto.
  - subst. econstructor. eauto.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - eauto.
  - econstructor. eauto.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS2. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eauto.
  - econstructor. eauto. eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  (* vtp right *)
  - econstructor.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. eauto.
  - subst. econstructor. eauto.
  - econstructor. eapply IHV2. eauto. omega. eapply IHV2. eauto. omega.
  - econstructor. eapply IHV2. eauto. omega. eauto.
  - econstructor. eauto. eapply IHV2. eauto. omega.
  (* pty left *)
  - eapply index_max. eauto.
  - eapply IHH1. eauto. omega.
  - eapply IHH1. eauto. omega.
  (* pty right *)
  - eapply closed_upgrade_gh. eauto. subst. eapply index_max in H1. omega.
  - eapply IHH1 in H1. eapply closed_open. simpl. eapply closed_upgrade_gh. eauto. omega. econstructor. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHS2. eauto. omega. rewrite H4. rewrite app_length. omega.
  (* tty *)
  - subst. eapply closed_open. simpl. eauto. econstructor. eauto.
  - subst. eapply closed_upgrade_gh. eauto. eapply index_max in H1. omega.
  - econstructor. eapply closed_upgrade_gh. eauto. omega.
  - eapply IHT in H1. inversion H1; subst. eauto. omega.
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHS2. eauto. omega.
  (* dty *)
  - subst. econstructor. eauto. eauto.
  - subst. econstructor. eauto. eauto.
  (* dsty *)
  - econstructor.
  - subst. econstructor. eapply IHD. eauto. omega. eapply IHD1. eauto. omega.
  (* tty 1 *)
  - subst. econstructor. econstructor. eauto.
  - subst. econstructor. econstructor. eauto using index_max.
  - subst. eapply IHT1 in H1. eauto. omega.
  - subst. eapply IHT1 in H1. eauto. omega.
  - subst. eapply IHT1 in H1. eapply IHT1 in H2. econstructor. eauto. eauto. omega. omega.
  - subst. eapply IHT1 in H1. eapply IHT1 in H2. econstructor. eauto. eauto. omega. omega.
  - subst. eapply IHT1 in H1. eauto. omega.
  (* vtp 1 *)
  - subst. eauto.
  - subst. eauto.
  - subst. eauto.
  - subst. eapply IHV1 in H1. eauto. omega.
  - subst. eapply IHV1 in H3. eauto. omega.
  - subst. eapply IHV1 in H1. eauto. omega.
  - subst. eapply IHV1 in H1. eauto. omega.
  - subst. eapply IHV1 in H1. eauto. omega.
  (* dty 1 *)
  - subst. econstructor. eauto.
  - subst. econstructor. eauto. eauto. eauto.
  (* dsty 1 *)
  - econstructor.
  - subst. econstructor. eapply IHD2. eauto. omega. eapply IHD3. eauto. omega.
Qed.

Lemma pty_closed: forall x G T2 n,
  pty G x T2 n ->
  ty_closed (length G) 0 T2.
Proof. intros. eapply all_closed with (x:=x). eauto. eauto. Qed.
*)

Lemma vtp_closed: forall m x T2 n1,
  vtp m x T2 n1 ->
  ty_closed 0 0 T2.
Admitted.
(*
Proof. intros. eapply all_closed. eauto. eauto. Qed.

Lemma vtp_closed1: forall m x T2 n1,
  vtp m x T2 n1 ->
  vr_closed 0 0 (VObj x).
Proof. intros. eapply all_closed. eauto. eauto. Qed.

Lemma tty_closed: forall G t T n1,
  tty G t T n1 ->
  ty_closed (length G) 0 T.
Proof. intros. eapply all_closed with (t:=t). eauto. eauto. Qed.

Lemma tty_closed1: forall G t T n1,
  tty G t T n1 ->
  tm_closed (length G) 0 t.
Proof. intros. eapply all_closed with (t:=t). eauto. eauto. Qed.

Lemma dsty_closed: forall G t T n1,
  dsty G t T n1 ->
  ty_closed (length G) 0 T.
Proof. intros. eapply all_closed with (ds:=t). eauto. eauto. Qed.

Lemma tty_closed_z: forall G z T n1,
  tty G (tvr (VarF z)) T n1 ->
  z < length G.
Proof.
  intros. remember (tvr (VarF z)) as t. generalize dependent z.
  induction H; intros; inversion Heqt; subst; eauto using index_max.
Qed.

Lemma tty_closed_b: forall v T n1,
  tty [] (tvr v) T n1 ->
  exists ds, v = VObj ds.
 Proof.
 intros.
 remember [] as G.
 remember (tvr v) as t.
 generalize HeqG. clear HeqG.
 induction H; intros; inversion Heqt; try subst; eauto using index_max.
 - simpl in H. inversion H.
Qed.

Lemma stp_closed1: forall G T1 T2 n1,
                      stp G T1 T2 n1 ->
                      ty_closed (length G) 0 T1.
Proof. intros. edestruct all_closed. eapply H0. eauto. eauto. Qed.

Lemma stp_closed2: forall G T1 T2 n1,
                      stp G T1 T2 n1 ->
                      ty_closed (length G) 0 T2.
Proof. intros. edestruct all_closed. destruct H1. eapply H1. eauto. eauto. Qed.

Lemma stpd_closed1: forall G T1 T2,
                      stpd G T1 T2 ->
                      ty_closed (length G) 0 T1.
Proof. intros. eu. eapply stp_closed1. eauto. Qed.


Lemma stpd_closed2: forall G T1 T2,
                      stpd G T1 T2 ->
                      ty_closed (length G) 0 T2.
Proof. intros. eu. eapply stp_closed2. eauto. Qed.


Fixpoint tsize (T: ty) { struct T }: nat :=
  match T with
    | TTop        => 1
    | TBot        => 1
    | TProj _ l   => 1
    | TFun l T1 T2 => S (tsize T1 + tsize T2)
    | TMem l T1 T2 => S (tsize T1 + tsize T2)
    | TBind T1    => S (tsize T1)
    | TAnd T1 T2  => S (tsize T1 + tsize T2)
    | TOr T1 T2   => S (tsize T1 + tsize T2)
  end.

Lemma ty_open_preserves_size: forall T v j,
  tsize T = tsize (ty_open j v T).
Proof.
  intros T. induction T; intros; simpl; eauto.
Qed.

Lemma stpd_refl_aux: forall n G T1,
  ty_closed (length G) 0 T1 ->
  tsize T1 < n ->
  stpd G T1 T1.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst; simpl in H0.
  - Case "bot". exists 1. eauto.
  - Case "top". exists 1. eauto.
  - Case "fun". eapply stpd_fun; eauto.
    eapply IHn; eauto; omega.
    eapply IHn; eauto.
    simpl. apply closed_open. simpl. eapply closed_upgrade_gh. eauto. omega.
    econstructor. omega.
    rewrite <- ty_open_preserves_size. omega.
  - Case "mem". eapply stpd_mem; try eapply IHn; eauto; try omega.
  - Case "sel". exists 1. eapply stp_selx. eauto.
  - Case "bind".
    eexists. eapply stp_bindx. eapply pty_vr. simpl. rewrite beq_nat_true_eq. eauto.
    instantiate (1:=open 0 (VarF (length G)) T0).
    eapply closed_open. eapply closed_upgrade_gh. eauto. omega. econstructor. omega.
    eauto. eauto. eauto. eauto.
  - Case "and".
    destruct (IHn G T0 H1). omega.
    destruct (IHn G T2 H2). omega.
    eexists. eapply stp_and2. eapply stp_and11. eauto. eauto. eapply stp_and12. eauto. eauto.
  - Case "or".
    destruct (IHn G T0 H1). omega.
    destruct (IHn G T2 H2). omega.
    eexists. eapply stp_or1. eapply stp_or21. eauto. eauto. eapply stp_or22. eauto. eauto.
Grab Existential Variables.
apply 0.
Qed.

Lemma stpd_refl: forall G T1,
  ty_closed (length G) 0 T1 ->
  stpd G T1 T1.
Proof.
  intros. apply stpd_refl_aux with (n:=S (tsize T1)); eauto.
Qed.

Lemma stpd_reg1: forall G T1 T2,
                      stpd G T1 T2 ->
                      stpd G T1 T1.
Proof. intros. eapply stpd_refl. eapply stpd_closed1. eauto. Qed.

Lemma stpd_reg2: forall G T1 T2,
                      stpd G T1 T2 ->
                      stpd G T2 T2.
Proof. intros. eapply stpd_refl. eapply stpd_closed2. eauto. Qed.



Ltac index_subst := match goal with
                      | H1: index ?x ?G = ?V1 , H2: index ?x ?G = ?V2 |- _ => rewrite H1 in H2; inversion H2; subst
                      | _ => idtac
                    end.

Ltac invty := match goal with
                | H1: TBot     = _ |- _ => inversion H1
                | H1: TProj _ _   = _ |- _ => inversion H1
                | H1: TMem _ _ _ = _ |- _ => inversion H1
                | H1: TFun _ _ _ = _ |- _ => inversion H1
                | H1: TBind  _ = _ |- _ => inversion H1
                | H1: TAnd _ _ = _ |- _ => inversion H1
                | H1: TOr _ _ = _ |- _ => inversion H1
                | _ => idtac
              end.

Lemma gh_match1: forall (GU:tenv) G GL TX,
  G ++ [TX] = GU ++ GL ->
  length GL > 0 ->
  exists GL1, GL = GL1 ++ [TX] /\ G = GU ++ GL1.
Proof.
  intros GU. induction GU; intros.
  - eexists. simpl in H. eauto.
  - destruct G. simpl in H.
    assert (length [TX] = 1). eauto.
    rewrite H in H1. simpl in H1. rewrite app_length in H1. omega.
    destruct (IHGU G GL TX).
    simpl in H. inversion H. eauto. eauto.
    eexists. split. eapply H1. simpl. destruct H1. simpl in H. inversion H. subst. eauto.
Qed.

Lemma gh_match: forall (G:tenv) GU GL TX T0,
  T0 :: G ++ [TX] = GU ++ GL ->
  length GL = S (length (G ++ [TX])) ->
  GU = [] /\ GL = T0 :: G ++ [TX].
Proof.
  intros. edestruct gh_match1. rewrite app_comm_cons in H. eapply H. omega.
  assert (length (T0 :: G ++ [TX]) = length (GU ++ GL)). rewrite H. eauto.
  assert (GU = []). destruct GU. eauto. simpl in H.
  simpl in H2. rewrite app_length in H2. simpl in H2. rewrite app_length in H2.
  simpl in H2. rewrite H0 in H2. rewrite app_length in H2. simpl in H2.
  omega.
  split. eauto. rewrite H3 in H1. simpl in H1. subst. simpl in H1. eauto.
Qed.

Lemma sub_env1: forall (GL:tenv) GU G TX,
  G ++ [TX] = GU ++ GL ->
  length GL = 1 ->
  GL = [TX].
Proof.
  intros.
  destruct GL. inversion H0. destruct GL.
  eapply app_inj_tail in H. destruct H. subst. eauto.
  inversion H0.
Qed.

Lemma def_subst_self: forall k x ds l D,
  vr_closed 0 0 (VObj x) ->
  vr_closed k 0 (VObj ds) ->
  index l (defs_to_list (subst_defs ds ds)) = Some D ->
  index l (defs_to_list (subst_defs (defs_subst (VObj x) ds) (defs_subst (VObj x) ds))) = Some (def_subst (VObj x) D).
Proof.
  intros k x ds l D HCx HCds HI.
  inversion HCds; subst. clear HCds. rename H2 into HCds.
  remember ds as ds0. rewrite Heqds0 in *.
  rewrite <- Heqds0 in HI at 1. rewrite <- Heqds0 at 1. clear Heqds0.
  generalize dependent D. generalize dependent ds0.
  induction HCds; intros.
  - simpl in *. solve by inversion.
  - simpl in *.
    rewrite <- length_defs_open in *. rewrite <- length_defs_subst in *.
    case_eq (beq_nat l (length (defs_to_list ds2))); intros E;
    rewrite E in *.
    + inversion HI; subst. f_equal.
      rewrite (proj1 (proj2 (proj2 (proj2 (subst_open_distribute 0 0 (VObj x) (VObj ds0) HCx))))).
      simpl. reflexivity. omega.
    + unfold subst_defs in *. specialize (IHHCds ds0 D HI). rewrite IHHCds.
      reflexivity.
Qed.

(* upgrade_gh interlude begin *)

Lemma index_at_index: forall {A} x0 G0 G1 (v:A),
  beq_nat x0 (length G1) = true ->
  index x0 (G0 ++ v :: G1) = Some v.
Proof.
  intros. apply beq_nat_true in H. subst.
  induction G0.
  - simpl. rewrite <- beq_nat_refl. reflexivity.
  - simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    rewrite false_beq_nat. assumption. omega.
Qed.

Lemma index_same: forall {A} x0 (v0:A) G0 G1 (v:A) (v':A),
  beq_nat x0 (length G1) = false ->
  index x0 (G0 ++ v :: G1) = Some v0 ->
  index x0 (G0 ++ v' :: G1) = Some v0.
Proof.
  intros ? ? ? ? ? ? ? E H.
  induction G0.
  - simpl. rewrite E. simpl in H. rewrite E in H. apply H.
  - simpl.
    rewrite app_length. simpl.
    case_eq (beq_nat x0 (length G0 + S (length G1))); intros E'.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite H. reflexivity.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite IHG0. reflexivity. assumption.
Qed.

Lemma exists_G1L: forall {X} (GU: list X) (GL: list X) (G1: list X) (G0: list X),
  GU ++ GL = G1 ++ G0 ->
  length G0 <= length GL ->
  exists G1L, G1 = GU ++ G1L /\ GL = G1L ++ G0.
Proof.
  intros X GU. induction GU; intros.
  - eexists. rewrite app_nil_l. split. reflexivity. simpl in H0. assumption.
  - induction G1.

    simpl in H.
    assert (length (a :: GU ++ GL) = length G0) as Contra. {
      rewrite H. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H. inversion H.
    specialize (IHGU GL G1 G0 H3 H0).
    destruct IHGU as [G1L [IHA IHB]].
    exists G1L. split. simpl. rewrite IHA. reflexivity. apply IHB.
Qed.

Lemma exists_G0U: forall {X} (G1: list X) (G0: list X) (GU: list X) (GL: list X),
  GU ++ GL = G1 ++ G0 ->
  length GL < S (length G0) ->
  exists G0U, G0 = G0U ++ GL.
Proof.
  intros X G1. induction G1; intros.
  - simpl in H. exists GU. symmetry. assumption.
  - induction GU.

    simpl in H.
    assert (length GL = length (a :: G1 ++ G0)) as Contra. {
      rewrite H. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H. inversion H.
    specialize (IHG1 G0 GU GL H3 H0).
    destruct IHG1 as [G0U IH].
    exists G0U. apply IH.
Qed.

(* splicing -- for stp_extend. *)

Definition splice_vr n i := if le_lt_dec n i then (i+1) else i.
Hint Unfold splice_vr.

Fixpoint vr_splice n (v: vr) {struct v}: vr :=
  match v with
    | VarF i => VarF (splice_vr n i)
    | VarB i => VarB i
    | VObj ds => VObj (defs_splice n ds)
  end
with splice n (T: ty) {struct T}: ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TMem l T1 T2 => TMem l (splice n T1) (splice n T2)
    | TProj v1 l    => TProj (vr_splice n v1) l
    | TFun l T1 T2 => TFun l (splice n T1) (splice n T2)
    | TBind T2     => TBind (splice n T2)
    | TAnd T1 T2   => TAnd (splice n T1) (splice n T2)
    | TOr T1 T2    => TOr (splice n T1) (splice n T2)
  end
with tm_splice n (t: tm) {struct t}: tm :=
  match t with
    | tvr v => tvr (vr_splice n v)
    | tApp t1 l t2 => tApp (tm_splice n t1) l (tm_splice n t2)
  end
with def_splice n (d: def) {struct d}: def :=
  match d with
    | dfun T1 T2 t2 => dfun (splice n T1) (splice n T2) (tm_splice n t2)
    | dty T1 => dty (splice n T1)
  end
with defs_splice n (ds: defs) {struct ds}: defs :=
  match ds with
    | dNil => dNil
    | dCons d ds => dCons (def_splice n d) (defs_splice n ds)
  end
.

Lemma splice_open_distribute_rec:
  (forall v0 v j k, vr_splice k (vr_open j v v0) = vr_open j (vr_splice k v) (vr_splice k v0)) /\
  (forall T0 v j k, splice k (ty_open j v T0) = ty_open j (vr_splice k v) (splice k T0)) /\
  (forall t0 v j k, tm_splice k (tm_open j v t0) = tm_open j (vr_splice k v) (tm_splice k t0)) /\
  (forall d0 v j k, def_splice k (def_open j v d0) = def_open j (vr_splice k v) (def_splice k d0)) /\
  (forall ds0 v j k, defs_splice k (defs_open j v ds0) = defs_open j (vr_splice k v) (defs_splice k ds0)).
Proof.
  apply syntax_mutind; intros; simpl;
  try inversion H0; try inversion H1; try inversion H2;
  subst;
  try rewrite H; try rewrite H0; try rewrite H1;
  eauto.
  - case_eq (beq_nat j i); intros E; simpl; eauto.
Qed.

Lemma splice_open_permute: forall {X} (G0:list X) T2 n j,
(ty_open j (VarF (n + S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (ty_open j (VarF (n + length G0)) T2)).
Proof.
  intros.
  assert (VarF (n + S (length G0)) = vr_splice (length G0) (VarF (n + length G0))) as A. {
    simpl. unfold splice_vr.
    case_eq (le_lt_dec (length G0) (n + length G0)); intros EL LE.
    f_equal. omega. omega.
  }
  rewrite A. symmetry.
  eapply (proj2 splice_open_distribute_rec).
Qed.

Lemma splice_open_permute0: forall {X} (G0:list X) T2 j,
(ty_open j (VarF (S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (ty_open j (VarF (length G0)) T2)).
Proof.
  intros.
  change (VarF (length G0)) with (VarF (0 + (length G0))).
  rewrite <- splice_open_permute. reflexivity.
Qed.

Lemma index_splice_hi: forall G0 G2 x0 v1 T,
    index x0 (G2 ++ G0) = Some T ->
    length G0 <= x0 ->
    index (x0 + 1) (map (splice (length G0)) G2 ++ v1 :: G0) = Some (splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply index_max in H. simpl in H. omega.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply index_extend. eapply H. eauto.
Qed.

Lemma index_splice_lo0: forall {X} G0 G2 x0 (T:X),
    index x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    index x0 G0 = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl in H. apply H.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E. subst.
      rewrite app_length in H0. apply plus_lt_contra in H0. inversion H0.
    + rewrite E in H. apply IHG2. apply H. apply H0.
Qed.

Lemma index_splice_lo: forall G0 G2 x0 v1 T f,
    index x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    index x0 (map (splice f) G2 ++ v1 :: G0) = Some T.
Proof.
  intros.
  assert (index x0 G0 = Some T). eapply index_splice_lo0; eauto.
  eapply index_extend_mult. eapply index_extend. eauto.
Qed.

Lemma closed_splice_rec:
  (forall i k v1, vr_closed i k v1 -> forall n, vr_closed (S i) k (vr_splice n v1)) /\
  (forall i k T1, ty_closed i k T1 -> forall n, ty_closed (S i) k (splice n T1)) /\
  (forall i k t1, tm_closed i k t1 -> forall n, tm_closed (S i) k (tm_splice n t1)) /\
  (forall i k d1, def_closed i k d1 -> forall n, def_closed (S i) k (def_splice n d1)) /\
  (forall i k ds1, defs_closed i k ds1 -> forall n, defs_closed (S i) k (defs_splice n ds1)).
Proof.
  apply closed_mutind; intros; econstructor; eauto;
  try solve [omega];
  try solve [eapply H; omega];
  try solve [eapply H0; omega];
  try solve [eapply H1; omega].
  unfold splice_vr.
  case_eq (le_lt_dec n x); intros E LE; omega.
Qed.

Lemma closed_splice: forall i k T n,
  ty_closed i k T ->
  ty_closed (S i) k (splice n T).
Proof.
  intros.
  eapply (proj2 closed_splice_rec); eauto.
Qed.

Lemma map_splice_length_inc: forall G0 G2 v1,
   (length (map (splice (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_inc_mult: forall i k T,
  ty_closed i k T -> forall i' k',
  i' >= i -> k' >= k ->
  ty_closed i' k' T.
Proof.
  intros.
  eapply closed_upgrade_gh.
  eapply closed_upgrade.
  eassumption.
  omega. omega.
Qed.

Lemma closed_inc: forall i k T,
  ty_closed i k T ->
  ty_closed (S i) k T.
Proof.
  intros. apply (closed_inc_mult i k T H (S i) k); omega.
Qed.

Lemma closed_splice_idem_rec:
  (forall i k v1, vr_closed i k v1 -> forall n, n >= i -> vr_splice n v1 = v1) /\
  (forall i k T1, ty_closed i k T1 -> forall n, n >= i -> splice n T1 = T1) /\
  (forall i k t1, tm_closed i k t1 -> forall n, n >= i -> tm_splice n t1 = t1) /\
  (forall i k d1, def_closed i k d1 -> forall n, n >= i -> def_splice n d1 = d1) /\
  (forall i k ds1, defs_closed i k ds1 -> forall n, n >= i -> defs_splice n ds1 = ds1).
Proof.
  apply closed_mutind; intros; eauto; simpl;
  try (rewrite H); try (rewrite H0); try (rewrite H1); eauto.
  unfold splice_vr.
  case_eq (le_lt_dec n x); intros E LE.
  omega. reflexivity.
Qed.

Lemma closed_splice_idem: forall i k T n,
                            ty_closed i k T ->
                            n >= i ->
                            splice n T = T.
Proof.
  intros.
  eapply (proj2 closed_splice_idem_rec); eauto.
Qed.

Lemma length_defs_splice: forall ds n,
  (length (defs_to_list ds))=(length (defs_to_list (defs_splice n ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma def_splice_self: forall k n ds l D,
  vr_closed k 0 (VObj ds) ->
  index l (defs_to_list (subst_defs ds ds)) = Some D ->
  index l (defs_to_list (subst_defs (defs_splice n ds) (defs_splice n ds))) = Some (def_splice n D).
Proof.
  intros k n ds l D HCds HI.
  inversion HCds; subst. clear HCds. rename H2 into HCds.
  remember ds as ds0. rewrite Heqds0 in *.
  rewrite <- Heqds0 in HI at 1. rewrite <- Heqds0 at 1. clear Heqds0.
  generalize dependent D. generalize dependent ds0.
  induction HCds; intros.
  - simpl in *. solve by inversion.
  - simpl in *.
    rewrite <- length_defs_open in *. rewrite <- length_defs_splice in *.
    case_eq (beq_nat l (length (defs_to_list ds2))); intros E;
    rewrite E in *.
    + inversion HI; subst. f_equal.
      rewrite (proj1 (proj2 (proj2 (proj2 splice_open_distribute_rec)))).
      simpl. reflexivity.
    + unfold subst_defs in *. specialize (IHHCds ds0 D HI). rewrite IHHCds.
      reflexivity.
Qed.

Lemma def_splice_self_dty: forall k n ds l T,
  vr_closed k 0 (VObj ds) ->
  index l (defs_to_list (subst_defs ds ds)) = Some (dty T) ->
  index l (defs_to_list (subst_defs (defs_splice n ds) (defs_splice n ds))) = Some (dty (splice n T)).
Proof.
  intros.
  assert (dty (splice n T) = def_splice n (dty T)) as A by eauto.
  rewrite A.
  eapply def_splice_self; eauto.
Qed.

Lemma stp_splice_aux: forall ni, (forall G0 G1 T1 T2 v1 n,
   stp (G1++G0) T1 T2 n -> n < ni ->
   stp ((map (splice (length G0)) G1) ++ v1::G0)
   (splice (length G0) T1) (splice (length G0) T2) n) /\
  (forall G0 G1 x1 T1 v1 n,
   pty (G1++G0) x1 T1 n -> n < ni ->
   pty ((map (splice (length G0)) G1) ++ v1::G0)
   (splice_vr (length G0) x1) (splice (length G0) T1) n).
Proof.
  intro ni. induction ni. split; intros; omega.
  destruct IHni as [IHstp IHpty].
  split; intros; inversion H; subst.
  - Case "bot".
    eapply stp_bot.
    rewrite map_splice_length_inc.
    simpl. apply closed_splice.
    assumption.
  - Case "top".
    eapply stp_top.
    rewrite map_splice_length_inc.
    apply closed_splice.
    assumption.
  - Case "fun".
    eapply stp_fun.
    eauto. eauto.
    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.
    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.
    eapply IHstp. eauto. omega.
    specialize (IHstp G0 (T4::G1)).
    simpl in IHstp. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    eapply IHstp. rewrite <- app_length. eauto. omega.
  - Case "mem".
    eapply stp_mem.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "selx". simpl. inversion H1; subst.
    + simpl. unfold splice_vr.
      case_eq (le_lt_dec (length G0) x); intros E LE.
      * eapply stp_selx.
        rewrite map_splice_length_inc. econstructor. omega.
      * eapply stp_selx.
        rewrite map_splice_length_inc. econstructor. omega.
    + simpl. inversion H1; subst. omega.
    + simpl. eapply stp_selx.
      rewrite map_splice_length_inc. econstructor.
      eapply (proj2 (proj2 (proj2 (proj2 closed_splice_rec)))). eauto.
  - Case "ssel1". simpl.
    eapply stp_strong_sel1.
    eapply def_splice_self_dty; eauto.
    rewrite map_splice_length_inc.
    assert (VObj (defs_splice (length G0) ds) = vr_splice (length G0) (VObj ds)) as A. {
      simpl. reflexivity.
    }
    rewrite A. eapply (proj1 closed_splice_rec). eauto.
  - Case "ssel2". simpl.
    eapply stp_strong_sel2.
    eapply def_splice_self_dty; eauto.
    rewrite map_splice_length_inc.
    assert (VObj (defs_splice (length G0) ds) = vr_splice (length G0) (VObj ds)) as A. {
      simpl. reflexivity.
    }
    rewrite A. eapply (proj1 closed_splice_rec). eauto.
  - Case "sel1".
    eapply stp_sel1.
    specialize (IHpty G0 G1 x (TMem l TBot T2)). simpl in IHpty.
    eapply IHpty. eauto. omega.
  - Case "sel2".
    eapply stp_sel2.
    specialize (IHpty G0 G1 x (TMem l T1 TTop)). simpl in IHpty.
    eapply IHpty. eauto. omega.
  - Case "bind1".
    eapply stp_bind1.
    rewrite map_splice_length_inc.
    assert (splice_vr (length G0) (length (G1 ++ G0)) = (S (length (G1 ++ G0)))) as A. {
      unfold splice_vr.
      case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros E LE.
      omega. clear LE. rewrite app_length in E. omega.
    }
    rewrite <- A.
    specialize (IHpty G0 (ty_open 0 (VarF (length (G1 ++ G0))) T0 :: G1)).
    simpl in IHpty. eapply IHpty. eauto. omega.
    rewrite app_length. rewrite <- splice_open_permute.
    rewrite map_splice_length_inc. rewrite app_length.
    assert (length G1 + S (length G0)=(S (length G1 + length G0))) as B by omega.
    rewrite B. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "bindx".
    assert (length G1 + S (length G0)=(S (length G1 + length G0))) as B by omega.
    eapply stp_bindx.
    rewrite map_splice_length_inc.
    assert (splice_vr (length G0) (length (G1 ++ G0)) = (S (length (G1 ++ G0)))) as A. {
      unfold splice_vr.
      case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros E LE.
      omega. clear LE. rewrite app_length in E. omega.
    }
    rewrite <- A.
    specialize (IHpty G0 (ty_open 0 (VarF (length (G1 ++ G0))) T0 :: G1)).
    simpl in IHpty. eapply IHpty. eauto. omega.
    rewrite app_length. rewrite <- splice_open_permute.
    rewrite map_splice_length_inc. rewrite app_length.
    rewrite B. eauto.
    rewrite app_length. rewrite <- splice_open_permute.
    rewrite map_splice_length_inc. rewrite app_length.
    rewrite B. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "and11".
    simpl. eapply stp_and11.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "and12".
    simpl. eapply stp_and12.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "and2".
    simpl. eapply stp_and2.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "or21".
    simpl. eapply stp_or21.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "or22".
    simpl. eapply stp_or22.
    eapply IHstp. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "or1".
    simpl. eapply stp_or1.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "trans".
    eapply stp_trans.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "pty_vr".
    unfold splice_vr.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + eapply pty_vr.
      apply index_splice_hi. eauto. eauto.
      eapply closed_splice.
      assert (S x1 = x1 + 1) as A by omega.
      rewrite <- A. eauto.
    + assert (splice (length G0) T1=T1) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      eapply pty_vr.
      eapply index_splice_lo.
      rewrite A. eauto. omega.
      rewrite A. eauto.
  - Case "pty_bind".
    unfold splice_vr.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + remember (x1 - (length G0)) as n.
      assert (x1 = n + length G0) as A. {
        clear LE. apply le_plus_minus in E.
        rewrite E. unfold id in *. omega.
      }
      rewrite A at 2.
      rewrite <- splice_open_permute.
      assert (n + S (length G0)=x1+1) as B. {
        rewrite Heqn. omega.
      }
      rewrite B.
      eapply pty_bind.
      specialize (IHpty G0 G1 x1 (TBind TX)).
      simpl in IHpty. unfold splice_vr in IHpty. rewrite LE in IHpty.
      eapply IHpty. eauto. omega.
      assert (S x1 = x1 + 1) as C by omega. rewrite <- C.
      eapply closed_splice. eauto.
    + assert (splice (length G0) TX = TX) as A. {
        eapply closed_splice_idem. eauto. omega.
      }
      assert (splice (length G0) (ty_open 0 (VarF x1) TX)=open 0 (VarF x1) TX) as B. {
        eapply closed_splice_idem.
        eapply closed_open. eapply closed_upgrade_gh. eauto.
        instantiate (1:=S x1). omega.
        econstructor. omega. omega.
      }
      rewrite B.
      eapply pty_bind.
      specialize (IHpty G0 G1 x1 (TBind TX)).
      simpl in IHpty. unfold splice_vr in IHpty. rewrite LE in IHpty.
      rewrite <- A. eapply IHpty. eauto. omega. eauto.
  - Case "pty_sub".
    unfold splice_vr.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + assert (S x1 = x1 + 1) as A by omega.
      assert (exists G1L, G1 = GU ++ G1L /\ GL = G1L ++ G0) as EQG. {
        eapply exists_G1L. eauto. omega.
      }
      destruct EQG as [G1L [EQG1 EQGL]].
      assert (splice_vr (length G0) x1=x1+1) as B. {
        unfold splice_vr. rewrite LE. reflexivity.
      }
      rewrite <- B.
      eapply pty_sub.
      eapply IHpty. eauto. omega.
      eapply IHstp. subst. eauto. omega.
      rewrite app_length. rewrite map_length. simpl.
      unfold splice_vr. rewrite LE. subst. rewrite app_length in *. omega.
      subst. rewrite map_app. simpl. rewrite app_assoc. reflexivity.
    + assert (splice (length G0) T1=T1) as A1. {
        eapply closed_splice_idem. eapply stp_closed2. eauto. omega.
      }
      assert (splice (length G0) T0=T0) as A0. {
        eapply closed_splice_idem. eapply stp_closed1. eauto. omega.
      }
      assert (exists G0U, G0 = G0U ++ GL) as EQG. {
        eapply exists_G0U. eauto. omega.
      }
      destruct EQG as [G0U EQG].
      assert (splice_vr (length G0) x1=x1) as C. {
        unfold splice_vr. rewrite LE. reflexivity.
      }
      rewrite <- C.
      eapply pty_sub.
      eapply IHpty. eauto. omega.
      rewrite A1. rewrite A0. eauto.
      rewrite C. eauto.
      instantiate (1:=(map (splice (length G0)) G1 ++ v1 :: G0U)).
      rewrite <- app_assoc. simpl. rewrite EQG. reflexivity.
Qed.

Lemma stp_splice: forall G0 G1 T1 T2 v1 n,
   stp (G1++G0) T1 T2 n ->
   stp ((map (splice (length G0)) G1) ++ v1::G0)
   (splice (length G0) T1) (splice (length G0) T2) n.
Proof. intros. eapply stp_splice_aux. eauto. eauto. Qed.

Lemma pty_splice: forall G0 G1 x1 T1 v1 n,
   pty (G1++G0) x1 T1 n ->
   pty ((map (splice (length G0)) G1) ++ v1::G0)
   (splice_vr (length G0) x1) (splice (length G0) T1) n.
Proof. intros. eapply stp_splice_aux. eauto. eauto. Qed.

Lemma stp_upgrade_gh_aux: forall ni,
  (forall G T T1 T2 n,
     stp G T1 T2 n -> n < ni ->
     stp (T::G) T1 T2 n) /\
  (forall T x G T2 n,
     pty G x T2 n -> n < ni ->
     pty (T::G) x T2 n).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H.
  (* stp *)
  - econstructor. eapply closed_upgrade_gh. eauto. simpl. omega.
  - econstructor. eapply closed_upgrade_gh. eauto. simpl. omega.
  - econstructor. eauto. eauto.
    eapply closed_upgrade_gh. eauto. simpl. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply IHn. eauto. omega.
    subst.
    assert (splice (length G) T0 = T0) as A. {
      eapply closed_splice_idem. eapply stp_closed2. eauto. omega.
    }
    assert (splice (length G) T4 = T4) as B. {
      eapply closed_splice_idem. eapply stp_closed1. eauto. omega.
    }
    assert (splice (length G) T3 = T3) as C. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length G) T5 = T5) as D. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (map (splice (length G)) [T4] ++ T::G =
          (T4::T::G)) as HGX. {
      simpl. rewrite B. eauto.
    }
    simpl. change (S (length G)) with (0 + (S (length G))).
    rewrite <- C. rewrite <- D.
    rewrite splice_open_permute. rewrite splice_open_permute.
    rewrite <- HGX.
    apply stp_splice. simpl. eauto.

  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - subst. econstructor. simpl. eapply (proj1 closed_upgrade_gh_rec). eauto. omega.
  - subst. econstructor. eauto. simpl. eapply (proj1 closed_upgrade_gh_rec). eauto. omega.
  - subst. econstructor. eauto. simpl. eapply (proj1 closed_upgrade_gh_rec). eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - subst.
    assert (splice (length G) T0 = T0) as A. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length G) T2 = T2) as B. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (length (T :: G)=splice_vr (length G) (length G)) as C. {
      unfold splice_vr. simpl.
      case_eq (le_lt_dec (length G) (length G)); intros E LE; omega.
    }
    assert (map (splice (length G)) [(ty_open 0 (VarF (length G)) T0)] ++ T::G =
          (((ty_open 0 (VarF (S (length G))) (splice (length G) T0)))::T::G)) as HGX. {
      simpl. rewrite <- splice_open_permute0. reflexivity.
    }
    eapply stp_bind1.
    rewrite <- B.
    instantiate (1:=(ty_open 0 (VarF (S (length G))) (splice (length G) T0))).
    rewrite <- HGX. rewrite C.
    apply pty_splice. simpl. eauto. simpl. rewrite A. reflexivity.
    eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply closed_upgrade_gh. eauto. simpl. omega.

  - subst.
    assert (splice (length G) T0 = T0) as A. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length G) T3 = T3) as B. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (length (T :: G)=splice_vr (length G) (length G)) as C. {
      unfold splice_vr. simpl.
      case_eq (le_lt_dec (length G) (length G)); intros E LE; omega.
    }
    assert (map (splice (length G)) [(ty_open 0 (VarF (length G)) T0)] ++ T::G =
          (((ty_open 0 (VarF (S (length G))) (splice (length G) T0)))::T::G)) as HGX. {
      simpl. rewrite <- splice_open_permute0. reflexivity.
    }
    eapply stp_bindx.
    instantiate (2:=(ty_open 0 (VarF (S (length G))) (splice (length G) T0))).
    rewrite <- HGX. rewrite C.
    apply pty_splice. simpl. eauto. simpl. rewrite A. reflexivity.
    simpl. rewrite <- splice_open_permute0. rewrite B. reflexivity.
    eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply closed_upgrade_gh. eauto. simpl. omega.

  - eapply stp_and11. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_and12. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_and2. eapply IHn. eauto. omega. eapply IHn. eauto. omega.

  - eapply stp_or21. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_or22. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply stp_or1. eapply IHn. eauto. omega. eapply IHn. eauto. omega.

  - eapply stp_trans. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  (* pty *)
  - econstructor. eapply index_extend. eauto. eapply closed_upgrade_gh. eauto. omega.
  - eapply pty_bind. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. omega.
  - eapply pty_sub. eapply IHn. eauto. omega. eauto. eauto. subst G.
    instantiate (1:=T::GU). eauto.
Qed.

Lemma stp_upgrade_gh: forall G T T1 T2 n,
                      stp G T1 T2 n ->
                      stp (T::G) T1 T2 n.
Proof.
  intros. eapply stp_upgrade_gh_aux. eauto. eauto.
Qed.

Lemma stp_upgrade_gh_mult: forall G G' T1 T2 n,
                      stp G T1 T2 n ->
                      stp (G'++G) T1 T2 n.
Proof. intros. induction G'. simpl. eauto. simpl. eapply stp_upgrade_gh. eauto. Qed.

Lemma stp_upgrade_gh_mult0: forall G T1 T2 n,
                      stp [] T1 T2 n ->
                      stp G T1 T2 n.
Proof. intros. rewrite <- (app_nil_r G). eapply stp_upgrade_gh_mult. eauto. Qed.

Lemma hastp_splice_aux: forall ni, (forall G0 G1 t1 T2 v1 n,
   tty (G1++G0) t1 T2 n -> n < ni ->
   tty ((map (splice (length G0)) G1) ++ v1::G0)
   (tm_splice (length G0) t1) (splice (length G0) T2) n) /\
   (forall G0 G1 l d1 T2 v1 n,
   dty (G1++G0) l d1 T2 n -> n < ni ->
   dty ((map (splice (length G0)) G1) ++ v1::G0) l
   (def_splice (length G0) d1) (splice (length G0) T2) n) /\
   (forall G0 G1 ds1 T2 v1 n,
   dsty (G1++G0) ds1 T2 n -> n < ni ->
   dsty ((map (splice (length G0)) G1) ++ v1::G0)
   (defs_splice (length G0) ds1) (splice (length G0) T2) n).
Proof.
  intro ni. induction ni. repeat split; intros; omega.
  destruct IHni as [IHT [IHD IHDS]].
  repeat split; intros; inversion H; subst.
  - assert ((length (G1 ++ G0) + 1) = S (length (G1 ++ G0))) as EqInc by omega.
    assert (dsty (map (splice (length G0)) (ty_open 0 (VarF (length (G1 ++ G0))) T :: G1) ++ v1::G0)
         (defs_splice (length G0) (defs_open 0 (VarF (length (G1 ++ G0))) ds))
         (splice (length G0) (ty_open 0 (VarF (length (G1 ++ G0))) T)) n1) as IH. {
      eapply IHDS. simpl in *. eapply H1. omega.
    }
    simpl. eapply T_Obj.
    + eapply IH.
    + rewrite (proj1 (proj2 splice_open_distribute_rec)).
      simpl. unfold splice_vr.
      case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros LE E.
      rewrite map_splice_length_inc. rewrite EqInc. reflexivity.
      clear E. rewrite app_length in LE. omega.
    + rewrite (proj2 (proj2 (proj2 (proj2 splice_open_distribute_rec)))).
      simpl. unfold splice_vr.
      case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros LE E.
      rewrite map_splice_length_inc. rewrite EqInc. reflexivity.
      clear E. rewrite app_length in LE. omega.
    + rewrite map_splice_length_inc. eapply closed_splice. eauto.
    + rewrite map_splice_length_inc. eapply closed_splice_rec. eauto.
    + rewrite (proj1 (proj2 splice_open_distribute_rec)).
      simpl. reflexivity.
  - simpl. unfold splice_vr.
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply T_VarF. apply index_splice_hi. eauto. omega.
      eapply closed_splice.
      assert (S x = x + 1) as A by omega.
      rewrite <- A. eauto.
    + assert (splice (length G0) T2=T2) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite A. eapply T_VarF. eapply index_splice_lo. eauto. omega. eauto.
  - simpl. eapply T_VarPack.
    assert (tvr (vr_splice (length G0) v) = tm_splice (length G0) (tvr v)) as A. {
      simpl. reflexivity.
    }
    rewrite A. eapply IHT. eauto. omega.
    rewrite (proj1 (proj2 splice_open_distribute_rec)). reflexivity.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - simpl. eapply T_VarUnpack.
    specialize (IHT G0 G1 (tvr v) (TBind T1) v1 n1). simpl in IHT.
    eapply IHT. eauto. omega.
    rewrite (proj1 (proj2 splice_open_distribute_rec)). reflexivity.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - simpl. eapply T_App.
    specialize (IHT G0 G1 t0 (TFun l T1 T2) v1 n1). simpl in IHT.
    eapply IHT. eauto. omega.
    eapply IHT. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - simpl. eapply T_AppVar.
    specialize (IHT G0 G1 t0 (TFun l T1 T0) v1 n1). simpl in IHT.
    eapply IHT. eauto. omega.
    specialize (IHT G0 G1 (tvr v2) T1 v1 n2). simpl in IHT.
    eapply IHT. eauto. omega.
    rewrite map_splice_length_inc. eapply closed_splice_rec. eauto.
    rewrite (proj1 (proj2 splice_open_distribute_rec)). reflexivity.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - eapply T_Sub. eapply IHT. eauto. omega. eapply stp_splice. eauto.
  - simpl. eapply D_Mem.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - assert ((length (G1 ++ G0) + 1) = S (length (G1 ++ G0))) as EqInc by omega.
    simpl. eapply D_Fun.
    assert (splice (length G0) T11 :: map (splice (length G0)) G1 ++ v1 :: G0 =
            map (splice (length G0)) (T11::G1) ++ v1 :: G0) as A. {
      simpl. reflexivity.
    }
    rewrite A. eapply IHT. simpl. eauto. omega.
    rewrite (proj1 (proj2 splice_open_distribute_rec)).
    simpl. rewrite map_splice_length_inc. unfold splice_vr.
    case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros LE E.
    rewrite EqInc. reflexivity.
    clear E. rewrite app_length in LE. omega.
    rewrite (proj1 (proj2 (proj2 splice_open_distribute_rec))).
    simpl. rewrite map_splice_length_inc. unfold splice_vr.
    case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros LE E.
    rewrite EqInc. reflexivity.
    clear E. rewrite app_length in LE. omega.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice_rec. eauto.
  - eapply D_Nil.
  - eapply D_Cons.
    * fold defs_splice in *. reflexivity.
    * fold splice in *. fold def_splice in *. eapply IHD.
      + rewrite <- length_defs_splice. eauto.
      + omega.
    * fold splice in *. fold defs_splice in *. eapply IHDS.
      + assumption.
      + omega.
Qed.

Lemma defs_hastp_splice: forall G0 G1 ds1 T2 v1 n,
   dsty (G1++G0) ds1 T2 n ->
   dsty ((map (splice (length G0)) G1) ++ v1::G0)
   (defs_splice (length G0) ds1) (splice (length G0) T2) n.
Proof. intros. eapply hastp_splice_aux. eauto. eauto. Qed.

Lemma hastp_upgrade_gh_aux: forall ni,
  (forall G T t1 T2 n,
     tty G t1 T2 n -> n < ni ->
     tty (T::G) t1 T2 n).
Proof.
  intros n. induction n. repeat split; intros; omega.
  intros; inversion H; subst.
  - assert (dsty (map (splice (length G)) [(ty_open 0 (VarF (length G)) T0)] ++ (T::G))
                         (defs_splice (length G) (defs_open 0 (VarF (length G)) ds))
                         (splice (length G) (ty_open 0 (VarF (length G)) T0)) n1) as IH'. {
      eapply defs_hastp_splice. simpl. eauto.
    }
    assert ((length G + 1) = (S (length G))) as EqInc by omega.
    assert (splice (length G) T0 = T0) as EqT0. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (defs_splice (length G) ds = ds) as Eqds. {
      eapply closed_splice_idem_rec. eauto. omega.
    }
    assert (dsty (ty_open 0 (VarF (S (length G))) T0 :: T :: G) (defs_open 0 (VarF (S (length G))) ds) (ty_open 0 (VarF (S (length G))) T0) n1) as IH. {
      simpl in IH'.
      rewrite (proj1 (proj2 splice_open_distribute_rec)) in IH'.
      rewrite (proj2 (proj2 (proj2 (proj2 splice_open_distribute_rec)))) in IH'.
      simpl in IH'. unfold splice_vr in IH'. simpl in IH'.
      case_eq (le_lt_dec (length G) (length G)); intros LE E.
      rewrite E in IH'. rewrite EqInc in IH'. rewrite EqT0 in IH'. rewrite Eqds in IH'.
      eapply IH'.
      omega.
    }
    eapply T_Obj. eapply IH.
    simpl. reflexivity. simpl. reflexivity.
    simpl. eapply closed_upgrade_gh. eauto. omega.
    simpl. eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_gh_rec)))). eauto. omega.
    eauto.
  - eapply T_VarF. eapply index_extend. eauto.
    simpl. eapply closed_upgrade_gh. eauto. omega.
  - eapply T_VarPack. eapply IHn. eauto. omega. eauto.
    simpl. eapply closed_upgrade_gh. eauto. omega.
  - eapply T_VarUnpack. eapply IHn. eauto. omega. eauto.
    simpl. eapply closed_upgrade_gh. eauto. omega.
  - eapply T_App. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
    simpl. eapply closed_upgrade_gh. eauto. omega.
  - eapply T_AppVar. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
    simpl. eapply (proj1 closed_upgrade_gh_rec). eauto. omega.
    eauto.
    simpl. eapply closed_upgrade_gh. eauto. omega.
  - eapply T_Sub. eapply IHn. eauto. omega. eapply stp_upgrade_gh. eauto.
Qed.

Lemma hastp_upgrade_gh: forall G T t1 T2 n,
                      tty G t1 T2 n ->
                      tty (T::G) t1 T2 n.
Proof.
  intros. eapply hastp_upgrade_gh_aux. eauto. eauto.
Qed.

Lemma hastp_upgrade_gh_mult: forall G G' t1 T2 n,
                      tty G t1 T2 n ->
                      tty (G'++G) t1 T2 n.
Proof. intros. induction G'. simpl. eauto. simpl. eapply hastp_upgrade_gh. eauto. Qed.

Lemma hastp_upgrade_gh_mult0: forall G t1 T2 n,
                      tty [] t1 T2 n ->
                      tty G t1 T2 n.
Proof. intros. rewrite <- (app_nil_r G). eapply hastp_upgrade_gh_mult. eauto. Qed.

Lemma hastp_upgrade_gh_vr: forall G x T n1,
  tty [] (tvr (VObj x)) T n1 ->
  tty G (tvr (VObj x)) T n1.
Proof.
  intros. eapply hastp_upgrade_gh_mult0. eauto.
Qed.

Lemma hastp_upgrade_gh_vr_ex: forall G x T n1,
  tty [] (tvr (VObj x)) T n1 ->
  exists n, tty G (tvr (VObj x)) T n.
Proof.
  intros. exists n1.
  induction G. simpl. eauto. simpl. eapply hastp_upgrade_gh_vr. eauto.
Qed.

(* upgrade_gh interlude ends *)
*)

(*
Lemma stp_subst_narrow0: forall x, vr_closed 0 0 (VObj x) ->
   forall n, forall G T1 T2 TX n2,
   stp (G++[TX]) T1 T2 n2 -> n2 < n ->
   (forall G (T3: ty) (n1: nat),
      pty (G++[TX]) 0 T3 n1 -> n1 < n ->
      exists m2, vtpd m2 x (substt x T3)) ->
   stpd (map (substt x) G) (substt x T1) (substt x T2).
Proof.
  intros x Hx.
  intros n. induction n. intros. omega.
  intros ? ? ? ? ? ? ? narrowX.

  (* helper lemma for pty *)
  assert (forall ni n2, forall G T2 xi,
    pty (G ++ [TX]) xi T2 n2 -> xi <> 0 -> n2 < ni -> ni < S n ->
    ptyd (map (substt x) G) (xi-1) (substt x T2)) as pty_subst_narrow02. {
      induction ni. intros. omega.
      intros. inversion H1.
      + (* vr *) subst.
        repeat eexists. eapply pty_vr. eapply index_subst1. eauto. eauto.
        eapply closed_subst0.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
        eapply closed_upgrade_gh. eauto. omega.
      + (* bind *) subst.
        assert (ptyd (map (substt x) (G0)) (xi-1) (substt x (TBind TX0))) as BB.
        eapply IHni. eapply H5. eauto. omega. omega.
        erewrite subst_open5.
        eu. repeat eexists. eapply pty_bind. eauto. eapply closed_subst1. eauto. eauto.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega. eauto.
        eauto. eauto.
      + (* sub *) subst.
        assert (exists GL0, GL = GL0 ++ [TX] /\ G0 = GU ++ GL0) as A. eapply gh_match1. eauto. omega.
        destruct A as [GL0 [? ?]]. subst GL.
        assert (ptyd (map (substt x) G0) (xi-1) (substt x T3)) as AA.
        eapply IHni. eauto. eauto. omega. omega.
        assert (stpd (map (substt x) GL0) (substt x T3) (substt x T0)) as BB.
        eapply IHn. eauto. eauto. omega. { intros. eapply narrowX. eauto. eauto. }
        eu. eu. repeat eexists. eapply pty_sub. eauto. eauto.
        (* - *)
        rewrite map_length. rewrite app_length in H7. simpl in H7. unfold id in *. omega.
        subst G0. rewrite map_app. eauto.
  }
  (* special case *)
  assert (forall ni n2, forall T0 T2,
    pty (T0 :: G ++ [TX]) (length (G ++ [TX])) T2 n2 -> n2 < ni -> ni < S n ->
    ptyd (map (substt x) (T0::G)) (length G) (substt x T2)) as pty_subst_narrow0. {
      intros.
      rewrite app_comm_cons in H1.
      remember (T0::G) as G1. remember (length (G ++ [TX])) as xi.
      rewrite app_length in Heqxi. simpl in Heqxi.
      assert (length G = xi-1) as R. omega.
      rewrite R. eapply pty_subst_narrow02. eauto. omega. eauto. eauto.
  }


  (* main logic *)
  inversion H.
  - Case "bot". subst.
    eapply stpd_bot; eauto. rewrite map_length. simpl.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H1. simpl in H1. eapply H1.
  - Case "top". subst.
    eapply stpd_top; eauto. rewrite map_length. simpl.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H1. simpl in H1. eapply H1.
  - Case "fun". subst.
    eapply stpd_fun. eauto. eauto.
    rewrite map_length.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in *. simpl in *. eauto.
    rewrite map_length.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in *. simpl in *. eauto.
    eapply IHn; eauto. omega.
    erewrite <- subst_open_commute_z. erewrite <- subst_open_commute_z.
    specialize (IHn (T4::G)). simpl in IHn.
    unfold substt in IHn at 2.  unfold substt in IHn at 3. unfold substt in IHn at 3.
    simpl in IHn. eapply IHn.
    rewrite map_length. rewrite app_length in *. eassumption.
    omega. eauto. eauto. eauto.
  - Case "mem". subst.
    eapply stpd_mem. eapply IHn; eauto. omega. eapply IHn; eauto. omega.


  - Case "selx". subst.
    eexists. eapply stp_selx.
    eapply (proj1 closed_subst_rec).
    rewrite map_length. rewrite app_length in H1. simpl in H1. eapply H1.
    eapply (proj1 closed_upgrade_gh_rec); eauto. omega.

  - Case "ssel1". subst.
    unfold substt at 2. unfold substt at 2. simpl.
    eexists. eapply stp_strong_sel1.
    eapply def_subst_self in H1; eauto.
    rewrite app_length in H2. simpl in H2. inversion H2; subst.
    rewrite map_length. econstructor.
    eapply (proj2 (proj2 (proj2 (proj2 closed_subst_rec)))). eauto.
    eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
  - Case "ssel2". subst.
    unfold substt at 2. unfold substt at 2. simpl.
    eexists. eapply stp_strong_sel2.
    eapply def_subst_self in H1; eauto.
    rewrite app_length in H2. simpl in H2. inversion H2; subst.
    rewrite map_length. econstructor.
    eapply (proj2 (proj2 (proj2 (proj2 closed_subst_rec)))). eauto.
    eapply (proj1 closed_upgrade_gh_rec); eauto. omega.

  - Case "sel1". subst. (* invert pty to vtp and create strong_sel node *)
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0.
      assert (exists m0, vtpd m0 x (substt x (TMem l TBot T2))) as A. eapply narrowX. eauto. omega.
      destruct A as [? A]. eu. inversion A. subst.
      repeat eexists. eapply stp_trans. eapply stp_strong_sel1. eauto.
      eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
      eapply stp_upgrade_gh_mult0; eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      eapply pty_subst_narrow02 in H1.
      eu. repeat eexists. unfold substt. simpl. rewrite E. eapply stp_sel1. eapply H1. eauto. eauto. eauto.

  - Case "sel2". subst. (* invert pty to vtp and create strong_sel node *)
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0.
      assert (exists m0, vtpd m0 x (substt x (TMem l T1 TTop))) as A. eapply narrowX. eauto. omega.
      destruct A as [? A]. eu. inversion A. subst.
      repeat eexists. eapply stp_trans.
      eapply stp_upgrade_gh_mult0; eauto.
      eapply stp_strong_sel2. eauto.
      eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    + assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      eapply pty_subst_narrow02 in H1.
      eu. repeat eexists. unfold substt. simpl. rewrite E. eapply stp_sel2. eapply H1. eauto. eauto. eauto.

  - Case "bind1".
    assert (ptyd (map (substt x) (T1'::G)) (length G) (substt x T2)).
    eapply pty_subst_narrow0. eauto. eauto. omega.
    eu. repeat eexists. eapply stp_bind1. rewrite map_length. eapply H9.
    simpl. subst T1'. fold subst. eapply subst_open4. eauto.
    fold subst.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H3. simpl in H3. rewrite map_length. eauto. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite map_length. rewrite app_length in H4. simpl in H4. eauto.

  - Case "bindx".
    assert (ptyd (map (substt x) (T1'::G)) (length G) (substt x T2')).
    eapply pty_subst_narrow0. eauto. eauto. omega.
    eu. repeat eexists. eapply stp_bindx. rewrite map_length. eapply H10.
    subst T1'. fold subst. eapply subst_open4. eauto.
    subst T2'. fold subst. eapply subst_open4. eauto.
    rewrite app_length in H4. simpl in H4. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite map_length. eauto.
    rewrite app_length in H5. simpl in H5. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite map_length. eauto.

  - Case "and11".
    assert (stpd (map (substt x) G) (substt x T0) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_and11. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H2. rewrite map_length. eauto.
  - Case "and12".
    assert (stpd (map (substt x) G) (substt x T3) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_and12. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H2. rewrite map_length. eauto.
  - Case "and2".
    assert (stpd (map (substt x) G) (substt x T1) (substt x T0)). eapply IHn. eauto. eauto. omega. eauto.
    assert (stpd (map (substt x) G) (substt x T1) (substt x T3)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eu. eexists. eapply stp_and2. eauto. eauto.

  - Case "or21".
    assert (stpd (map (substt x) G) (substt x T1) (substt x T0)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_or21. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H2. rewrite map_length. eauto.
  - Case "or22".
    assert (stpd (map (substt x) G) (substt x T1) (substt x T3)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_or22. eauto.
    eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    rewrite app_length in H2. rewrite map_length. eauto.
  - Case "or1".
    assert (stpd (map (substt x) G) (substt x T0) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    assert (stpd (map (substt x) G) (substt x T3) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eu. eexists. eapply stp_or1. eauto. eauto.

  - Case "trans".
    assert (stpd (map (substt x) G) (substt x T1) (substt x T3)).
    eapply IHn; eauto. omega.
    assert (stpd (map (substt x) G) (substt x T3) (substt x T2)).
    eapply IHn; eauto. omega.
    eu. eu. repeat eexists. eapply stp_trans. eauto. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


Lemma stp_subst_narrowX: forall x, vr_closed 0 0 (VObj x) ->
   forall ml, forall nl, forall m G T2 TX n1 n2,
   vtp m x (substt x TX) n1 ->
   pty (G++[TX]) 0 T2 n2 -> m < ml -> n2 < nl ->
   (forall (m0: nat) x (T2 T3: ty) (n1 n2: nat),
        vtp m0 x T2 n1 ->
        stp [] T2 T3 n2 -> m0 <= m ->
        vtpdd m0 x T3) ->
   vtpdd m x (substt x T2). (* decrease b/c transitivity *)
Proof.
  intros x Hx.
  intros ml. (* induction ml. intros. omega. *)
  intros nl. induction nl. intros. omega.
  intros.
  inversion H0.
  - Case "vr". subst.
    assert (T2 = TX). eapply index_hit0. eauto.
    subst T2.
    repeat eexists. eauto. eauto.
  - Case "bind". subst.
    assert (vtpdd m x (substt x (TBind TX0))) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    destruct A as [? [? [A ?]]]. inversion A. subst.
    repeat eexists. unfold substt. erewrite subst_open_commute0.
    assert (ty_closed 0 0 (TBind (substt x TX0))). eapply vtp_closed. unfold substt in A. simpl in A. eapply A.
    assert ((substt x (TX0)) = TX0) as R. eapply subst_closed_id. eauto.
    unfold substt in R. rewrite R in H8. eapply H8. simpl. eauto. omega.
  - Case "sub". subst.
    destruct GL.

    assert (vtpdd m x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    eu.
    assert (stpd [] (substt x T1) (substt x T2)) as B.
    erewrite subst_closed_id. erewrite subst_closed_id. eexists. eassumption.
    eapply stp_closed2 in H5. simpl in H5. eapply H5.
    eapply stp_closed1 in H5. simpl in H5. eapply H5.
    simpl in B. eu.
    assert (vtpdd x0 x (substt x T2)).
    eapply H3. eauto. eauto. eauto.
    eu. repeat eexists. eauto. omega.

    assert (length GL = 0) as LenGL. simpl in *. omega.
    assert (GL = []). destruct GL. reflexivity. simpl in LenGL. inversion LenGL.
    subst GL.
    assert (TX = t). eapply proj2. apply app_inj_tail. eassumption.
    subst t.
    assert (vtpdd m x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    eu.
    assert (stpd (map (substt x) []) (substt x T1) (substt x T2)) as B.
    eapply stp_subst_narrow0. eauto. eauto. eauto. {
      intros. eapply IHnl in H. eu. repeat eexists. eauto. eauto. eauto. eauto. omega. eauto.
    }
    simpl in B. eu.
    assert (vtpdd x0 x (substt x T2)).
    eapply H3. eauto. eauto. eauto.
    eu. repeat eexists. eauto. omega.
Qed.

Lemma stp_narrow_aux: forall n,
  (forall G x T n0,
  pty G x T n0 -> n0 <= n ->
  forall G1 G0 G' TX1 TX2,
    G=G1++[TX2]++G0 ->
    G'=G1++[TX1]++G0 ->
    stpd G0 TX1 TX2 ->
    ptyd G' x T) /\
  (forall G T1 T2 n0,
  stp G T1 T2 n0 -> n0 <= n ->
  forall G1 G0 G' TX1 TX2,
    G=G1++[TX2]++G0 ->
    G'=G1++[TX1]++G0 ->
    stpd G0 TX1 TX2 ->
    stpd G' T1 T2).
Proof.
  intros n.
  induction n.
  - Case "z". split; intros; inversion H0; subst; inversion H; eauto.
  - Case "s n". destruct IHn as [IHn_pty IHn_stp].
    split.
    {
    intros G x T n0 H NE. inversion H; subst;
    intros G1 G0 G' TX1 TX2 EG EG' HX.
    + SCase "vr".
      case_eq (beq_nat x (length G0)); intros E.
      * assert (index x ([TX2]++G0) = Some TX2) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (index x G = Some TX2) as A2'. {
          rewrite EG. eapply index_extend_mult. apply A2.
        }
        rewrite A2' in H0. inversion H0. subst.
        destruct HX as [nx HX].
        eexists. eapply pty_sub. eapply pty_vr. eapply index_extend_mult.
        simpl. rewrite E. reflexivity.
        eapply stp_closed1 in HX. eapply closed_upgrade_gh.
        eapply HX. apply beq_nat_true in E. subst. omega.
        eapply stp_upgrade_gh. eauto. simpl.
        f_equal. apply beq_nat_true in E. subst. reflexivity.
        simpl. reflexivity.
      * assert (index x G' = Some T) as A. {
          subst.
          eapply index_same. apply E. eassumption.
        }
        eexists. eapply pty_vr. eapply A.
        subst. eauto.
    + SCase "bind".
      edestruct IHn_pty with (G:=G) (G':=G').
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply pty_bind; eauto.
    + SCase "sub".
      edestruct IHn_pty as [? Htp].
      eapply H0. omega. eapply EG. eapply EG'. assumption.
      case_eq (le_lt_dec (S (length G0)) (length GL)); intros E' LE'.
      assert (exists G1L, G1 = GU ++ G1L /\ GL = G1L ++ (TX2) :: G0) as EQG. {
        eapply exists_G1L. eassumption. simpl. eassumption.
      }
      destruct EQG as [G1L [EQG1 EQGL]].
      edestruct IHn_stp as [? Hsub].
      eapply H1. omega. simpl. eapply EQGL. simpl. reflexivity. eapply HX.

      eexists. eapply pty_sub. eapply Htp. eapply Hsub.
      subst. rewrite app_length in *. simpl in *. eauto.
      rewrite EG'. simpl. rewrite EQG1. rewrite <- app_assoc. reflexivity.
      assert (exists G0U, TX2::G0 = G0U ++ GL) as EQG. {
        eapply exists_G0U. eassumption. simpl. omega.
      }
      destruct EQG as [G0U EQG].
      destruct G0U. simpl in EQG.
      assert (length (TX2::G0)=length GL) as Contra. {
        rewrite EQG. reflexivity.
      }
      simpl in Contra. rewrite <- Contra in H2. subst. omega.
      simpl in EQG. inversion EQG.
      eexists. eapply pty_sub. eapply Htp. eassumption. eauto.
      instantiate (1:=G1 ++ [TX1] ++ G0U). subst.
      rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
    }

    intros G T1 T2 n0 H NE. inversion H; subst;
    intros G1 G0 G' TX1 TX2 EG EG' HX;
    assert (length G' = length G) as EGLEN by solve [
      subst; repeat rewrite app_length; simpl; reflexivity
    ].
    + SCase "bot". eapply stpd_bot. rewrite EGLEN; assumption.
    + SCase "top". eapply stpd_top. rewrite EGLEN; assumption.
    + SCase "fun". eapply stpd_fun.
      reflexivity. reflexivity.
      rewrite EGLEN; assumption. rewrite EGLEN; assumption.
      eapply IHn_stp; try eassumption. omega.
      eapply IHn_stp with (G1:=(T4::G1)); try eassumption.
      rewrite EGLEN. eauto. omega.
      subst. simpl. reflexivity. subst. simpl. reflexivity.
    + SCase "mem". eapply stpd_mem.
      eapply IHn_stp; try eassumption. omega.
      eapply IHn_stp; try eassumption. omega.
    + SCase "selx". eexists. eapply stp_selx.
      rewrite EGLEN; assumption.
    + SCase "ssel1". eexists. eapply stp_strong_sel1; try eassumption.
      rewrite EGLEN; assumption.
    + SCase "ssel2". eexists. eapply stp_strong_sel2; try eassumption.
      rewrite EGLEN; assumption.
    + SCase "sel1".
      edestruct IHn_pty as [? Htp]; eauto. omega.
    + SCase "sel2".
      edestruct IHn_pty as [? Htp]; eauto. omega.
    + SCase "bind1".
      edestruct IHn_pty with (G1:=(ty_open 0 (VarF (length G)) T0 :: G1)) as [? Htp].
      eapply H0. omega. rewrite EG. reflexivity. reflexivity. eapply HX.
      eexists. eapply stp_bind1.
      rewrite EGLEN. subst. simpl. simpl in Htp. eapply Htp.
      rewrite EGLEN. subst. simpl. reflexivity.
      rewrite EGLEN. assumption. rewrite EGLEN. assumption.
    + SCase "bindx".
      edestruct IHn_pty with (G1:=(ty_open 0 (VarF (length G)) T0 :: G1)) as [? Htp].
      eapply H0. omega. rewrite EG. reflexivity. reflexivity. eapply HX.
      eexists. eapply stp_bindx.
      rewrite EGLEN. subst. simpl. simpl in Htp. eapply Htp.
      rewrite EGLEN. subst. simpl. reflexivity.
      rewrite EGLEN. subst. simpl. reflexivity.
      rewrite EGLEN. assumption. rewrite EGLEN. assumption.
    + SCase "and11".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_and11. eapply IH. rewrite EGLEN. assumption.
    + SCase "and12".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_and12. eapply IH. rewrite EGLEN. assumption.
    + SCase "and2".
      edestruct IHn_stp as [? IH1].
      eapply H0. omega. eauto. eauto. eauto.
      edestruct IHn_stp as [? IH2].
      eapply H1. omega. eauto. eauto. eauto.
      eexists. eapply stp_and2. eapply IH1. eapply IH2.
    + SCase "or21".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_or21. eapply IH. rewrite EGLEN. assumption.
    + SCase "or22".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_or22. eapply IH. rewrite EGLEN. assumption.
    + SCase "or1".
      edestruct IHn_stp as [? IH1].
      eapply H0. omega. eauto. eauto. eauto.
      edestruct IHn_stp as [? IH2].
      eapply H1. omega. eauto. eauto. eauto.
      eexists. eapply stp_or1. eapply IH1. eapply IH2.
    + SCase "trans".
      edestruct IHn_stp as [? IH1].
      eapply H0. omega. eauto. eauto. eauto.
      edestruct IHn_stp as [? IH2].
      eapply H1. omega. eauto. eauto. eauto.
      eexists. eapply stp_trans. eapply IH1. eapply IH2.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stp_narrow: forall TX1 TX2 G0 T1 T2 n nx,
  stp ([TX2]++G0) T1 T2 n ->
  stp G0 TX1 TX2 nx ->
  stpd ([TX1]++G0) T1 T2.
Proof.
  intros. eapply stp_narrow_aux. eapply H. reflexivity.
  instantiate(3:=nil). simpl. reflexivity. simpl. reflexivity.
  eauto.
Qed.
*)

(* possible types closure *)
Lemma vtp_widen: forall l, forall n, forall k, forall m1 x T2 T3 n1 n2,
  vtp m1 x T2 n1 ->
  stp [] T2 T3 n2 ->
  m1 < l -> n2 < n -> n1 < k ->
  vtpdd m1 x T3.
Admitted.
(*
Proof.
  intros l. induction l. intros. solve by inversion.
  intros n. induction n. intros. solve by inversion.
  intros k. induction k; intros. solve by inversion.
  inversion H.
  - Case "top". inversion H0; subst; invty.
    + SCase "top". repeat eexists; eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. simpl in *. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H8. omega.
    + SCase "and".
      assert (vtpdd m1 x T1). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T0). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T1). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T0). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T0) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "mem". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eauto. eauto.
    + SCase "mem". invty. subst.
      repeat eexists. eapply vtp_mem. eauto.
      eapply stp_trans. eauto. eauto.
      eapply stp_trans. eauto. eauto.
      eauto. eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. simpl in *. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H11. omega.
    + SCase "and".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T5). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T5). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T5) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "fun". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eauto. eauto.
    + SCase "fun". invty. subst.
      assert (stpd [T8] (ty_open 0 (VarF 0) T5) (ty_open 0 (VarF 0) T4)) as A. {
        eapply stp_narrow. simpl. eassumption. simpl. eassumption.
      }
      eu.
      repeat eexists. eapply vtp_fun. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      eauto. eauto.
      eapply stp_trans. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. simpl in *. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. subst. inversion H11. omega.
    + SCase "and".
      assert (vtpdd m1 x T6). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T7). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T6). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T7). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T7) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "bind".
    inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top.
      eapply vtp_closed1. eauto. eauto.
    + SCase "sel2".
      repeat eexists. eapply vtp_sel. eauto. simpl in *. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H9. omega.
    + SCase "bind1".
      invty. subst.
      remember (VarF (length [])) as VZ.
      remember (VObj x) as VX.

      (* left *)
      assert (vtpd m x (ty_open 0 VX T0)) as LHS. eexists. eassumption.
      eu.
      (* right *)
      assert (substt x (ty_open 0 VZ T0) = (ty_open 0 VX T0)) as R. unfold substt. subst. eapply subst_open_commute0. eauto.
      assert (substt x T3 = T3) as R1. eapply subst_closed_id. eauto.

      assert (vtpdd m x (substt x T3)) as BB. {
        eapply stp_subst_narrowX.
        eapply vtp_closed1. eauto.
        rewrite <-R in LHS.
        eauto.
        instantiate (2:=nil). simpl. eapply H10. eauto. eauto.
        { intros. eapply IHl. eauto. eauto. omega. eauto. eauto. }
      }
      rewrite R1 in BB.
      eu. repeat eexists. eauto. omega.
    + SCase "bindx".
      invty. subst.
      remember (VarF (length [])) as VZ.
      remember (VObj x) as VX.

      (* left *)
      assert (vtpd m x (ty_open 0 VX T0)) as LHS. eexists. eassumption.
      eu.
      (* right *)
      assert (substt x (ty_open 0 VZ T0) = (ty_open 0 VX T0)) as R. unfold substt. subst. eapply subst_open_commute0. eauto.

      assert (vtpdd m x (substt x (ty_open 0 VZ T4))) as BB. {
        eapply stp_subst_narrowX.
        eapply vtp_closed1. eauto.
        rewrite <-R in LHS. eapply LHS.
        instantiate (2:=nil). simpl. eapply H10. eauto. eauto.
        { intros. eapply IHl. eauto. eauto. omega. eauto. eauto. }
      }
      unfold substt in BB. subst. erewrite subst_open_commute0 in BB.
      clear R.
      eu. repeat eexists. eapply vtp_bind. eauto. eauto. omega. eauto. (* enough slack to add bind back *)
    + SCase "and".
      assert (vtpdd (S m) x T1). eapply IHn; eauto. omega. eu.
      assert (vtpdd (S m) x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd (S m) x T1). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd (S m) x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd (S m) x T4) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "ssel2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top.
      eapply vtp_closed1. eauto. eauto.
    + SCase "ssel1".
      repeat eexists. eauto. omega.
    + SCase "ssel2".
      rewrite H4 in H10. inversion H10; subst.
      repeat eexists. eauto. omega.
    + SCase "sel1".
      repeat eexists. eapply vtp_sel. eassumption.
      eapply stp_closed2 in H0. simpl in H0. inversion H0; subst. assumption.
      eauto. omega.
    + SCase "selx".
      eapply stp_closed2 in H0. simpl in H0. inversion H0; subst. inversion H11; subst.
      omega.
    + SCase "and".
      assert (vtpdd m1 x T1). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T1). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T2) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "and". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top.
      eapply vtp_closed1. eauto. eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and11". eapply IHn in H4. eu. repeat eexists. eauto. omega. eauto. omega. omega. eauto.
    + SCase "and12". eapply IHn in H5. eu. repeat eexists. eauto. omega. eauto. omega. omega. eauto.
    + SCase "and".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 x T4) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.

  - Case "or1". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top.
      eapply vtp_closed1. eauto. eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "or...".
      eapply IHn in H4. eu.
      repeat eexists. eapply H4. omega. eauto. omega. omega. eauto.
    + SCase "or...".
      assert (vtpdd m1 x T4) as A. eapply IHn. eapply H. eauto. omega. omega. eauto. eu.
      eapply IHn in A. eu.
      repeat eexists. eauto. omega. eauto. omega. omega. eauto.

  - Case "or2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top.
      eapply vtp_closed1. eauto. eauto.
    + SCase "ssel2".
      repeat eexists. eapply vtp_sel. eauto. eauto. eauto. omega.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "or...".
      eapply IHn in H4. eu.
      repeat eexists. eapply H4. omega. eauto. omega. omega. eauto.
    + SCase "or...".
      assert (vtpdd m1 x T4) as A. eapply IHn. eapply H. eauto. omega. omega. eauto. eu.
      eapply IHn in A. eu.
      repeat eexists. eauto. omega. eauto. omega. omega. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


(* Reduction semantics  *)
Inductive step: tm -> tm -> Prop :=
| step_app: forall f l x T1 T2 t12,
    index l (defs_to_list (subst_defs f f)) = Some (dfun T1 T2 t12) ->
    step (tApp (tvr (VObj f)) l (tvr (VObj x))) (subst_tm x t12)
| step_app1: forall t1 t1' l t2,
    step t1 t1' ->
    step (tApp t1 l t2) (tApp t1' l t2)
| step_app2: forall f t2 l t2',
    step t2 t2' ->
    step (tApp (tvr (VObj f)) l t2) (tApp (tvr (VObj f)) l t2')
.
*)


Lemma stp_subst_narrow_z: forall G0 TX T1 T2 x m n1 n2,
  stp (G0 ++ [TX]) T1 T2 n2 ->
  vtp m x (substt x TX) n1 ->
  stpd (map (substt x) G0) (substt x T1) (substt x T2).
Admitted.
(*
Proof.
  intros.
  edestruct stp_subst_narrow0.
  eapply vtp_closed1. eauto.
  eauto. eauto.
  { intros. edestruct stp_subst_narrowX.
    eapply vtp_closed1. eauto.
    eauto. eauto. eauto. eauto.
    { intros. eapply vtp_widen; eauto. }
    ev. repeat eexists. eauto.
  }
  eexists. eassumption.
Qed.

Lemma defs_hastp_inv_aux_rec: forall T0 T00 ds0 ds0' n0',
  ty_closed 0 0 (substt ds0 T0) ->
  defs_closed 0 1 ds0 ->
  ds0' = defs_open 0 (VarF 0) ds0 ->
  T0 = ty_open 0 (VarF 0) T00 ->
  ty_closed 0 1 T00 ->
  dsty [T0] ds0' T0 n0' -> forall n0, forall n1 T' ds ds',
  dsty [T0] ds' T' n1 -> n1 <= n0 ->
  ty_closed 0 0 (substt ds0 T') ->
  defs_closed 0 1 ds ->
  ds' = defs_open 0 (VarF 0) ds -> forall dsa dsa',
  defs_to_list ds0 = dsa ++ defs_to_list ds ->
  defs_to_list ds0' = dsa' ++ defs_to_list ds' ->
  exists m n, vtp m ds0 (substt ds0 T') n.
Proof.
  intros T0 T00 ds0 ds0' n0' HC0 Hds0 Eq0' Eq00 HC00 HD0 n0.
  induction n0. intros. inversion H; subst; omega.
  intros n1 T' ds ds' HD LE.
  intros HC Hds Eq'.
  intros dsa dsa' Eqa Eqa'.
  inversion HD; subst.
  - repeat eexists. eapply vtp_top.
    econstructor. eauto.

  - inversion H0; subst.

  { unfold substt in *.
    destruct ds; simpl in H3; try solve [inversion H3].
    inversion H3; subst.
    destruct d; simpl in H4; try solve [inversion H4].
    inversion H4; subst.
    unfold substt in *. simpl in HC. inversion HC; subst. inversion Hds; subst.
    edestruct IHn0 as [? [? IH]]. eapply H1. omega. eauto. eassumption. reflexivity.
    instantiate (1:=dsa ++ [(dty t)]). rewrite <- app_assoc. eauto.
    instantiate (1:=dsa' ++ [(def_open 0 (VarF 0) (dty t))]). rewrite <- app_assoc. eauto.
    simpl.

    assert (ty_closed 0 1 t) as A1. {
      simpl. inversion H10; subst. eassumption.
    }
    assert ((subst (VObj ds0) (ty_open 0 (VarF 0) t))=(ty_open 0 (VObj ds0) t)) as B1. {
      rewrite subst_open_commute0. reflexivity. simpl. eauto.
    }
    assert (stpd [] (ty_open 0 (VObj ds0) t) (ty_open 0 (VObj ds0) t)) as C1. {
      eapply stpd_refl.
      simpl. eapply closed_open. simpl. eauto. econstructor. eauto.
    }
    eu.

    exists x. eexists. eapply vtp_and.
    eapply vtp_mem. rewrite <- length_defs_open.
    instantiate (1:=(subst_ty ds0 t)).
    assert (dty (subst_ty ds0 t) = subst_def ds0 (dty t)) as R1. {
      unfold subst_ty. unfold subst_def. simpl. reflexivity.
    }
    rewrite R1. eapply index_subst_defs. instantiate (1:=dsa). simpl. eauto.
    unfold subst_ty. rewrite B1. eauto. unfold subst_ty. rewrite B1. eauto.
    econstructor. eauto.
    eapply IH. eauto. omega.
  }

  { unfold substt in *.
    destruct ds; simpl in H3; try solve [inversion H3].
    inversion H3.
    destruct d; simpl in H4; try solve [inversion H4].
    inversion H4; subst.
    unfold substt in *. simpl in HC. inversion HC; subst. inversion Hds; subst.
    edestruct IHn0 as [? [? IH]]. eapply H1. omega. eauto. eassumption. reflexivity.
    instantiate (1:=dsa ++ [(dfun t t0 t1)]). rewrite <- app_assoc. eauto.
    instantiate (1:=dsa' ++ [(def_open 0 (VarF 0) (dfun t t0 t1))]). rewrite <- app_assoc. eauto.
    simpl.

    assert (ty_closed 0 1 t) as A1. {
      simpl. inversion H13; subst. eassumption.
    }
    assert ((subst (VObj ds0) (ty_open 0 (VarF 0) t))=(ty_open 0 (VObj ds0) t)) as B1. {
      rewrite subst_open_commute0. reflexivity. simpl. eauto.
    }
    assert (stpd [] (ty_open 0 (VObj ds0) t) (ty_open 0 (VObj ds0) t)) as C1. {
      eapply stpd_refl.
      simpl. eapply closed_open. simpl. eauto. econstructor. eauto.
    }
    eu.

    assert (ty_closed 0 2 t0) as A2. {
      simpl. inversion H13; subst. eassumption.
    }
    assert (subst (VObj ds0) (ty_open 1 (VarF 0) t0)=(ty_open 1 (VObj ds0) t0)) as B2. {
      rewrite subst_open_commute0. reflexivity. simpl. eauto.
    }
    assert (stpd [subst (VObj ds0) (ty_open 0 (VarF 0) t)]
                (ty_open 0 (VarF 0) (ty_open 1 (VObj ds0) t0))
                (ty_open 0 (VarF 0) (ty_open 1 (VObj ds0) t0))) as C2. {
      eapply stpd_refl.
      simpl. eapply closed_open. simpl. eapply closed_open. simpl.
      eapply closed_upgrade_gh. eauto. omega.
      econstructor.
      eapply (proj2 (proj2 (proj2 closed_upgrade_rec))).
      eapply (proj2 (proj2 (proj2 closed_upgrade_gh_rec))).
      eauto. omega. omega.
      econstructor. omega.
    }
    eu.

    exists x. eexists. eapply vtp_and.
    eapply vtp_fun. rewrite <- length_defs_open.
    instantiate (1:=(tm_open 1 (VObj ds0) t1)).
    instantiate (1:=(ty_open 1 (VObj ds0) t0)).
    instantiate (1:=(subst_ty ds0 t)).
    assert (dfun (subst_ty ds0 t) (ty_open 1 (VObj ds0) t0) (tm_open 1 (VObj ds0) t1) =
            subst_def ds0 (dfun t t0 t1)) as R1. {
      unfold subst_def. simpl. reflexivity.
    }
    rewrite R1. eapply index_subst_defs. instantiate (1:=dsa). simpl. eauto.
    eapply HD0.
    eauto. eauto. eauto.
    rewrite <- length_defs_open.
    instantiate (1:=(tm_open 1 (VarF 0) t1)).
    instantiate (1:=(ty_open 1 (VarF 0) t0)).
    instantiate (1:=(ty_open 0 (VarF 0) t)).
    assert (dfun (ty_open 0 (VarF 0) t) (ty_open 1 (VarF 0) t0) (tm_open 1 (VarF 0) t1) =
            def_open 0 (VarF 0) (dfun t t0 t1)) as R1'. {
      simpl. reflexivity.
    }
    rewrite R1'. eapply index_defs_open. instantiate (1:=dsa). simpl. eauto.
    eauto. eauto. eauto.
    unfold subst_ty. rewrite B1. eauto.
    eauto. eauto. simpl in *.
    inversion H11; subst. eapply closed_open. simpl. eauto.
    econstructor.
    eapply (proj2 (proj2 (proj2 (proj2 closed_upgrade_rec)))). eauto. omega.
    eapply closed_subst. simpl. eauto. econstructor. eauto.
    inversion H13; subst.
    eapply (proj1 (proj2 (proj2 closed_open_rec))). simpl.
    eapply (proj1 (proj2 (proj2 closed_upgrade_gh_rec))). eauto. omega.
    econstructor. omega.
    rewrite B2. eapply C2.
    econstructor. eauto.
    eapply IH. eauto. omega.
  }
Grab Existential Variables.
apply 0. apply 0.
Qed.

Lemma defs_hastp_inv: forall ds T n1,
  dsty [open 0 (VarF 0) T] (defs_open 0 (VarF 0) ds) (ty_open 0 (VarF 0) T) n1 ->
  ty_closed 0 1 T ->
  defs_closed 0 1 ds ->
  exists m n, vtp m ds (ty_open 0 (VObj ds) T) n.
Proof.
  intros ds T n H HCT HCds.
  assert (ty_open 0 (VObj ds) T=substt ds (ty_open 0 (VarF 0) T)) as A. {
    unfold substt. rewrite subst_open_commute0. reflexivity.
    simpl. eauto.
  }
  rewrite A. eapply defs_hastp_inv_aux_rec; eauto.
  rewrite <- A.
  eapply closed_open; eauto. econstructor. eauto.
  rewrite <- A.
  eapply closed_open; eauto. econstructor. eauto.
  instantiate (1:=[]). rewrite app_nil_l. reflexivity.
  instantiate (1:=[]). rewrite app_nil_l. reflexivity.
Qed.
*)

Lemma hastp_inv: forall v T n1,
  tty [] v T n1 ->
  value v ->
  exists m n2, vtp m v T n2.
Proof.
  intros. remember [] as G. revert H0.
  induction H; subst; intro HV; try solve [inversion HV].
(*
  - Case "vr". subst. simpl in *. eapply defs_hastp_inv; eauto.
  - Case "pack". subst.
    destruct IHtty. eauto. eauto. ev.
    repeat eexists. eapply vtp_bind. eauto. eauto.
  - Case "unpack". subst.
    destruct IHtty. eauto. eauto. ev. inversion H0.
    repeat eexists. eauto.
  - Case "sub".
    destruct IHtty. eauto. eauto. ev.
    assert (exists m0, vtpdd m0 x T2). eexists. eapply vtp_widen; eauto.
    ev. eu. repeat eexists. eauto.
Qed.
*)
Admitted.

(*
Lemma hastp_subst_aux_z: forall ni, (forall G TX T x t n1 n2,
  tty (G++[TX]) t T n2 -> n2 < ni ->
  tty [] (tvr (VObj x)) (substt x TX) n1 ->
  exists n3, tty (map (substt x) G) (tm_subst (VObj x) t) (substt x T) n3) /\
  (forall G TX T x l d n1 n2,
  dty (G++[TX]) l d T n2 -> n2 < ni ->
  tty [] (tvr (VObj x)) (substt x TX) n1 ->
  exists n3, dty (map (substt x) G) l (def_subst (VObj x) d) (substt x T) n3) /\
  (forall G TX T x ds n1 n2,
  dsty (G++[TX]) ds T n2 -> n2 < ni ->
  tty [] (tvr (VObj x)) (substt x TX) n1 ->
  exists n3, dsty (map (substt x) G) (defs_subst (VObj x) ds) (substt x T) n3).
Proof.
  intro ni. induction ni. repeat split; intros; omega. destruct IHni as [IHniT [IHniD IHniDs]].
  repeat split;
  intros; remember (G++[TX]) as G0; revert G HeqG0; inversion H; intros.
  - Case "vobj".
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply tty_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }
    edestruct IHniDs with (G:=T'::G1) as [? IH]. subst. eauto. omega. subst. eauto.
    subst. simpl.
    eexists. eapply T_Obj. eapply IH.
    rewrite app_length. simpl. rewrite map_length. unfold substt.
    assert (substt x (ty_open 0 (VarF (length G1 + 1)) T0) = ty_open 0 (VarF (length G1)) (substt x T0)) as A. {
      erewrite subst_open. reflexivity. eauto.
    }
    unfold substt in A. rewrite A. reflexivity.
    rewrite app_length. simpl. rewrite map_length. unfold subst_defs.
    rewrite (proj2 (proj2 (proj2 (proj2 (subst_open_rec 0 x HCx))))).
    reflexivity.
    eapply closed_subst.
    rewrite app_length in *. simpl in *. rewrite map_length. eauto.
    eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    eapply (proj2 (proj2 (proj2 (proj2 closed_subst_rec)))).
    rewrite app_length in *. simpl in *. rewrite map_length. eauto.
    eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    unfold substt.
    assert (subst (VObj x) (ty_open 0 (VObj ds) T0) = ty_open 0 (vr_subst (VObj x) (VObj ds)) (subst (VObj x) T0)) as B. {
      eapply (proj2 (subst_open_distribute 0 0 (VObj x) (VObj ds) HCx)).
      omega.
    }
    rewrite B. simpl. reflexivity.

  - Case "vrz". subst. simpl.
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0.
      eapply index_hit0 in H2. subst.
      eapply hastp_upgrade_gh_vr_ex. eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff; eauto.
      eexists. eapply T_VarF.
      eapply index_subst1. eauto. eauto.
      eapply closed_subst0. eapply (proj1 closed_upgrade_gh_rec).
      eapply tty_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
      omega.
      assert (S (x0 - 1) + 1 = S x0) as Eq. {
        unfold id in *. omega.
      }
      rewrite Eq. eauto.

  - Case "pack". subst. simpl.
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply tty_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }
    edestruct IHniT as [? IH]. eauto. omega. eauto.
    assert (substt x (TBind T1) = (TBind (substt x T1))) as A. {
      eauto.
    }
    rewrite A.
    destruct v.
    + case_eq (beq_nat i 0); intros E.
      * assert (i = 0). eapply beq_nat_true_iff; eauto. subst.
        simpl in IH.
        eexists. eapply T_VarPack. eapply IH.
        erewrite subst_open_commute0b. eauto. eapply HCx.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4. simpl in H4.
        eapply H4.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
      * assert (i <> 0). eapply beq_nat_false_iff; eauto.
        simpl in IH. rewrite E in IH.
        eexists. eapply T_VarPack.
        simpl. rewrite E. eapply IH.
        remember (i - 1) as z.
        assert (i = z + 1) as B. {
          unfold id in *. omega.
        }
        rewrite B. unfold substt.
        erewrite subst_open_commute_z. simpl. rewrite <- B. rewrite E.
        rewrite Heqz. reflexivity. eapply HCx.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4.
        simpl in H4. eapply H4.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    + eapply tty_closed1 in H. inversion H; subst. inversion H7; subst.
      omega.
    + eexists. eapply T_VarPack. eapply IH.
      unfold substt.
      eapply (proj2 (subst_open_distribute 0 0 (VObj x) (VObj d) HCx)).
      omega.
      rewrite map_length. eapply closed_subst0.
      eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
      rewrite app_length in H4. simpl in H4.
      apply H4.

  - Case "unpack". subst. simpl.
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply tty_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }
    edestruct IHniT as [? IH]. eapply H2. omega. eauto.
    assert (substt x (TBind T1) = (TBind (substt x T1))) as A. {
      eauto.
    }
    rewrite A in IH.
    destruct v.
    + case_eq (beq_nat i 0); intros E.
      * assert (i = 0). eapply beq_nat_true_iff; eauto. subst.
        simpl in IH.
        eexists. eapply T_VarUnpack. eapply IH.
        erewrite subst_open_commute0b. simpl. reflexivity. eapply HCx.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4. simpl in H4.
        eapply H4.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
      * assert (i <> 0). eapply beq_nat_false_iff; eauto.
        simpl in IH. rewrite E in IH.
        eexists. eapply T_VarUnpack.
        simpl. rewrite E. eapply IH.
        remember (i - 1) as z.
        assert (i = z + 1) as B. {
          unfold id in *. omega.
        }
        rewrite B. unfold substt.
        erewrite subst_open_commute_z. simpl. rewrite <- B. rewrite E.
        rewrite Heqz. reflexivity. eapply HCx.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4.
        simpl in H4. eapply H4.
        eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
    + eapply tty_closed1 in H. inversion H; subst. inversion H7; subst.
      omega.
    + eexists. eapply T_VarUnpack. eapply IH.
      unfold substt.
      eapply (proj2 (subst_open_distribute 0 0 (VObj x) (VObj d) HCx)).
      omega.
      rewrite map_length. eapply closed_subst0.
      eapply (proj1 closed_upgrade_gh_rec); eauto. omega.
      rewrite app_length in H4. simpl in H4.
      apply H4.

  - Case "app". subst. simpl.
    edestruct IHniT as [? IH1]. eapply H2. omega. eauto.
    edestruct IHniT as [? IH2]. eapply H3. omega. eauto.
    eexists. eapply T_App. eauto. eauto. eapply closed_subst.
    subst. rewrite map_length. rewrite app_length in *. simpl in *. eauto.
    subst. rewrite map_length.
    eapply (proj1 closed_upgrade_gh_rec).
    eapply tty_closed1 in H1. inversion H1; subst. simpl in *. eauto. omega.
  - Case "appvr". subst. simpl.
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply tty_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }

    edestruct IHniT as [? IH1]. eapply H2. omega. eauto.
    edestruct IHniT as [? IH2]. eapply H3. omega. eauto.
    destruct v2.

    case_eq (beq_nat i 0); intros E.

    eapply beq_nat_true in E. subst.
    erewrite subst_open_commute0b.
    eexists. eapply T_AppVar. eauto. eauto.
    simpl. eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega.
    eauto.
    rewrite map_length. erewrite <- subst_open_commute0b.
    eapply closed_subst. eapply closed_upgrade_gh. eassumption.
    rewrite app_length. simpl. omega.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega. eauto. eauto.

    erewrite subst_open5.
    simpl in *. rewrite E in *.
    eexists. eapply T_AppVar. eauto. eauto.
    eapply tty_closed1 in IH2. inversion IH2; subst. eassumption.
    eauto.
    erewrite <- subst_open5. eapply closed_subst.
    subst. rewrite map_length. rewrite app_length in *. simpl in *. eassumption.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega. eauto.
    apply []. apply beq_nat_false. apply E.
    eauto.
    apply []. apply beq_nat_false. apply E.

    eapply tty_closed1 in IH2. inversion IH2; subst. inversion H9; subst. omega.

    eexists. eapply T_AppVar. eauto. eauto.
    eapply tty_closed1 in IH2. inversion IH2; subst. eassumption.
    unfold substt.
    eapply (proj2 (subst_open_distribute 0 0 (VObj x) (VObj d) HCx)). omega.
    eapply closed_subst. subst. rewrite map_length. rewrite app_length in *. simpl in *.
    eapply closed_upgrade_gh. eassumption. omega.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega.

  - Case "sub". subst.
    edestruct hastp_inv as [? [? HV]]; eauto.
    edestruct stp_subst_narrow_z. eapply H3. eapply HV.
    edestruct IHniT as [? IH]. eapply H2. omega. eauto.
    eexists. eapply T_Sub. eauto. eauto.
  - Case "mem". subst. simpl.
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply tty_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }
    eexists. eapply D_Mem. eauto. eapply closed_subst0. rewrite app_length in H2. rewrite map_length. eauto.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega.
    rewrite app_length in *. simpl in *. rewrite map_length. eassumption.
  - Case "fun". subst. simpl.
    assert (vr_closed 0 0 (VObj x)) as HCx. {
      eapply tty_closed1 in H1. simpl in H1. inversion H1; subst. eauto.
    }
    edestruct IHniT with (G:=T11::G1) as [? HI] . eauto. omega. eauto.
    simpl in HI.
    eexists. eapply D_Fun. eapply HI.
    rewrite map_length. rewrite app_length. simpl.
    erewrite subst_open. unfold substt. reflexivity. eapply HCx.
    rewrite map_length. rewrite app_length. simpl.
    erewrite (proj1 (proj2 (proj2 (subst_open_rec 0 x HCx)))). reflexivity.
    rewrite map_length in *. rewrite app_length in *. simpl in *.
    eapply closed_subst0.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega. eauto.
    rewrite map_length in *. rewrite app_length in *. simpl in *.
    eapply closed_subst0.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega. eauto.
    rewrite map_length in *. rewrite app_length in *. simpl in *.
    eapply (proj1 (proj2 (proj2 closed_subst_rec))). eauto.
    eapply (proj1 closed_upgrade_gh_rec). eapply HCx. omega.

  - Case "dNil". subst. simpl.
    eexists. eapply D_Nil.

  - Case "dCons". subst. simpl.
    edestruct IHniDs as [? IHDs]. eapply H4. omega. eauto.
    edestruct IHniD as [? IHD]. eapply H3. omega. eauto.
    eexists. eapply D_Cons.
    + reflexivity.
    + fold subst. rewrite <- length_defs_subst. eapply IHD.
    + fold subst. eapply IHDs.
Grab Existential Variables.
apply 0. apply 0. apply 0.
Qed.

Lemma hastp_subst_z: forall G TX T x t n1 n2,
  tty (G++[TX]) t T n2 ->
  tty [] (tvr (VObj x)) (substt x TX) n1 ->
  exists n3, tty (map (substt x) G) (tm_subst (VObj x) t) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_aux_z with (t:=t). eauto. eauto. eauto.
Qed.

Lemma hastp_subst: forall G TX T x t n1 n2,
  tty (G++[TX]) t T n2 ->
  tty [] (tvr (VObj x)) TX n1 ->
  exists n3, tty (map (substt x) G) (tm_subst (VObj x) t) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_z with (t:=t). eauto.
  erewrite subst_closed_id. eauto. eapply tty_closed in H0. eauto.
Qed.
*)

Lemma stp_subst_narrow: forall G0 TX T1 T2 x m n1 n2,
  stp (G0 ++ [TX]) T1 T2 n2 ->
  vtp m x TX n1 ->
  stpd (map (substt x) G0) (substt x T1) (substt x T2).
Proof.
  intros. eapply stp_subst_narrow_z. eauto.
  erewrite subst_closed_id. eauto. eapply vtp_closed in H0. eauto.
Qed.

Theorem type_safety: forall t T n1,
  tty [] t T n1 ->
  (value t) \/
  (exists t' n2, step t t' /\ tty [] t' T n2).
Proof.
  intros.
  assert (ty_closed (length ([]:tenv)) 0 T) as CL. admit. (* eapply tty_closed. eauto. *)
  remember [] as G. remember t as tt. remember T as TT.
  revert T t HeqTT HeqG Heqtt CL.
  induction H; intros.
  - Case "VarF". subst. simpl in H. inversions H. (* contradiction *)
  - Case "Lam". left. constructor.
  - Case "Tag". left. constructor.
  - Case "Obj". left. constructor. subst. admit.
  - Case "Sel".
    (* TODO *) admit.
  - Case "App". right. subst.
    assert (value t2 \/ (exists t2' n2, step t2 t2' /\ tty [] t2' T2 n2)) as HX. {
      eapply IHtty2. eauto. eauto. eauto. admit.
    }
    assert (value t1 \/ (exists t1' n2, step t1 t1' /\ tty [] t1' (TAll T2 T3) n2)) as HF. {
      eapply IHtty1. eauto. eauto. eauto. admit.
    }
    destruct HF.
    + SCase "fun-val".
      destruct HX.
      * SSCase "arg-val".
        assert (exists m n1, vtp m t1 (TAll T2 T3) n1). { eapply hastp_inv; eauto. }
        assert (exists m n1, vtp m t2 T2 n1). { eapply hastp_inv; eauto. }
        ev. inversions H4.
        assert (vtpdd x t2 T1). { eapply vtp_widen. eauto. eauto. eauto. eauto. eauto. }
        eu.
(*
        assert (exists n1, tty [] (tvr (VObj x)) (ty_open 0 (VObj x) T0) n1) as A. {
          eexists. eapply T_Obj. eauto. simpl. reflexivity. simpl. reflexivity.
          simpl. eauto. simpl. inversion H26; subst. eauto. eauto.
        }
        destruct A as [? A].
        assert (substt x (ty_open 0 (VarF 0) T0) = ty_open 0 (VObj x) T0) as EqTx. {
          unfold substt. rewrite subst_open_commute0. reflexivity.
          simpl. assumption.
        }
        assert (ttyd (map (substt x) [T1x]) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx)) (substt x (ty_open 0 (VarF 1) T2x))) as HIx. {
          eapply hastp_subst_z. eapply H15. rewrite EqTx. eapply A.
        }
        eu. simpl in HIx.
        assert (def_subst (VObj x) (dfun T1x T2x tx) = dfun T2 T5 t) as EqD. {
          erewrite index_defs_open_eq; eauto.
        }
        simpl in EqD. inversion EqD.
        assert (ttyd (map (substt x0) []) (tm_subst (VObj x0) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx))) (substt x0 (substt x (ty_open 0 (VarF 1) T2x)))) as HIx0. {
          eapply hastp_subst. rewrite app_nil_l. eapply HIx. unfold substt. rewrite H9. eauto.
        }
        eu. simpl in HIx0.
        assert ((substt x (ty_open 0 (VarF 1) T2x))=(ty_open 0 (VarF 0) (substt x T2x))) as EqT2x. {
          change 1 with (0+1). erewrite subst_open. reflexivity. eauto.
        }
        assert (vr_closed 0 0 (VObj x0)) as HC0. {
          eapply vtp_closed1; eauto.
        }
        assert (vr_closed 0 0 (VObj x)) as HC. {
          eapply vtp_closed1; eauto.
        }
        assert ((tm_subst (VObj x0) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx))) =
                (subst_tm x0 t)) as Eqtx0. {
          subst. unfold subst_tm.
          change 1 with (0+1).
          rewrite (proj1 (proj2 (proj2 (subst_open_rec 0 x HC)))).
          rewrite (proj1 (proj2 (proj2 subst_open_commute0_rec))).
          reflexivity.
          simpl.
          eapply (proj1 (proj2 (proj2 closed_subst_rec))).
          simpl. eauto.
          eauto.
        }
        assert (ttyd [] (subst_tm x0 t) (substt x0 (ty_open 0 (VarF 0) T5))) as HI. {
          subst. rewrite <- Eqtx0. unfold substt in EqT2x. rewrite <- EqT2x. eauto.
        }
        eu. simpl in HI.
        edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H25. eauto.
        simpl in HI2.
        assert (substt x0 (ty_open 0 (VarF 0) T) = T) as EqT. {
          erewrite <- closed_no_open. erewrite subst_closed_id. reflexivity.
          eassumption. eassumption.
        }
        rewrite EqT in HI2.
*)
        repeat eexists. eapply step_app. eauto. eauto.
      * SSCase "arg_step".
        ev. subst.
        right. repeat eexists. eapply step_app2. eauto. eapply T_App.
        eauto. eauto.
        simpl in *. eassumption.
    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply step_app1. eauto. eapply T_App.
      eauto. eauto.
      simpl in *. eassumption.


  - Case "Pack".
  - Case "Unpack".
  - Case "Sub".
  - Case "vrz". subst G. inversion H.
  - Case "pack". subst G.
    eapply tty_closed_b in H. destruct H. subst.
    left. eexists. reflexivity.
  - Case "unpack". subst G.
    eapply tty_closed_b in H. destruct H. subst.
    left. eexists. reflexivity.
  - Case "app". subst.
    assert (ty_closed (length ([]:tenv)) 0 (TFun l T1 T)) as TF. eapply tty_closed. eauto.
    assert ((exists x, t2 = tvr (VObj x)) \/
                (exists (t': tm) n2,
                   step t2 t' /\ tty [] t' T1 n2)) as HX.
    eapply IHtty2. eauto. eauto. eauto. inversion TF. eauto.
    assert ((exists x, t1 = tvr (VObj x)) \/
                (exists (t': tm) n2,
                   step t1 t' /\ tty [] t' (TFun l T1 T) n2)) as HF.
    eapply IHtty1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      destruct HX.
      * SSCase "arg-val".
        ev. ev. subst.
        assert (exists m n1, vtp m x (TFun l T1 T) n1). { eapply hastp_inv. eauto. }
        assert (exists m n1, vtp m x0 T1 n1). { eapply hastp_inv. eauto. }
        ev. inversion H2. subst.
        assert (vtpdd x1 x0 T2). { eapply vtp_widen. eauto. eauto. eauto. eauto. eauto. }
        eu.
        assert (exists n1, tty [] (tvr (VObj x)) (ty_open 0 (VObj x) T0) n1) as A. {
          eexists. eapply T_Obj. eauto. simpl. reflexivity. simpl. reflexivity.
          simpl. eauto. simpl. inversion H26; subst. eauto. eauto.
        }
        destruct A as [? A].
        assert (substt x (ty_open 0 (VarF 0) T0) = ty_open 0 (VObj x) T0) as EqTx. {
          unfold substt. rewrite subst_open_commute0. reflexivity.
          simpl. assumption.
        }
        assert (ttyd (map (substt x) [T1x]) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx)) (substt x (ty_open 0 (VarF 1) T2x))) as HIx. {
          eapply hastp_subst_z. eapply H15. rewrite EqTx. eapply A.
        }
        eu. simpl in HIx.
        assert (def_subst (VObj x) (dfun T1x T2x tx) = dfun T2 T5 t) as EqD. {
          erewrite index_defs_open_eq; eauto.
        }
        simpl in EqD. inversion EqD.
        assert (ttyd (map (substt x0) []) (tm_subst (VObj x0) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx))) (substt x0 (substt x (ty_open 0 (VarF 1) T2x)))) as HIx0. {
          eapply hastp_subst. rewrite app_nil_l. eapply HIx. unfold substt. rewrite H9. eauto.
        }
        eu. simpl in HIx0.
        assert ((substt x (ty_open 0 (VarF 1) T2x))=(ty_open 0 (VarF 0) (substt x T2x))) as EqT2x. {
          change 1 with (0+1). erewrite subst_open. reflexivity. eauto.
        }
        assert (vr_closed 0 0 (VObj x0)) as HC0. {
          eapply vtp_closed1; eauto.
        }
        assert (vr_closed 0 0 (VObj x)) as HC. {
          eapply vtp_closed1; eauto.
        }
        assert ((tm_subst (VObj x0) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx))) =
                (subst_tm x0 t)) as Eqtx0. {
          subst. unfold subst_tm.
          change 1 with (0+1).
          rewrite (proj1 (proj2 (proj2 (subst_open_rec 0 x HC)))).
          rewrite (proj1 (proj2 (proj2 subst_open_commute0_rec))).
          reflexivity.
          simpl.
          eapply (proj1 (proj2 (proj2 closed_subst_rec))).
          simpl. eauto.
          eauto.
        }
        assert (ttyd [] (subst_tm x0 t) (substt x0 (ty_open 0 (VarF 0) T5))) as HI. {
          subst. rewrite <- Eqtx0. unfold substt in EqT2x. rewrite <- EqT2x. eauto.
        }
        eu. simpl in HI.
        edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H25. eauto.
        simpl in HI2.
        assert (substt x0 (ty_open 0 (VarF 0) T) = T) as EqT. {
          erewrite <- closed_no_open. erewrite subst_closed_id. reflexivity.
          eassumption. eassumption.
        }
        rewrite EqT in HI2.
        right. repeat eexists. eapply step_app. eauto. eauto.
      * SSCase "arg_step".
        ev. subst.
        right. repeat eexists. eapply step_app2. eauto. eapply T_App.
        eauto. eauto.
        simpl in *. eassumption.
    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply step_app1. eauto. eapply T_App.
      eauto. eauto.
      simpl in *. eassumption.

  - Case "appvr". subst.
    assert (ty_closed (length ([]:tenv)) 0 (TFun l T1 T2)) as TF. eapply tty_closed. eauto.
    assert ((exists x, tvr v2 = tvr (VObj x)) \/
                (exists (t': tm) n2,
                   step (tvr v2) t' /\ tty [] t' T1 n2)) as HX.
    eapply IHtty2. eauto. eauto. eauto. inversion TF. eauto.
    assert (exists x2, v2 = (VObj x2)) as HXeq. {
      destruct HX as [[? HX] | Contra]. inversion HX. eexists. reflexivity.
      destruct Contra as [t' [n' [Hstep Htyp]]].
      inversion Hstep.
    }
    clear HX. destruct HXeq as [x2 HXeq]. subst v2.
    assert ((exists x, t1 = tvr (VObj x)) \/
                (exists (t': tm) n2,
                   step t1 t' /\ tty [] t' (TFun l T1 T2) n2)) as HF.
    eapply IHtty1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      ev. ev. subst.
      assert (exists m n1, vtp m x (TFun l T1 T2) n1). eapply hastp_inv. eauto.
      assert (exists m n1, vtp m x2 T1 n1). eapply hastp_inv. eauto.
      ev. inversion H2. subst.
      assert (vtpdd x0 x2 T0). { eapply vtp_widen. eauto. eauto. eauto. eauto. eauto. }
      eu.
      assert (exists n1, tty [] (tvr (VObj x)) (ty_open 0 (VObj x) T) n1) as A. {
        eexists. eapply T_Obj. eauto. simpl. reflexivity. simpl. reflexivity.
        simpl. eauto. simpl. inversion H27; subst. eauto. eauto.
      }
      destruct A as [? A].
      assert (substt x (ty_open 0 (VarF 0) T) = ty_open 0 (VObj x) T) as EqTx. {
        unfold substt. rewrite subst_open_commute0. reflexivity.
        simpl. assumption.
      }
      assert (ttyd (map (substt x) [T1x]) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx)) (substt x (ty_open 0 (VarF 1) T2x))) as HIx. {
        eapply hastp_subst_z. eapply H16. rewrite EqTx. eapply A.
      }
      eu. simpl in HIx.
      assert (def_subst (VObj x) (dfun T1x T2x tx) = dfun T0 T5 t) as EqD. {
        erewrite index_defs_open_eq; eauto.
      }
      simpl in EqD. inversion EqD.
      assert (ttyd (map (substt x2) []) (tm_subst (VObj x2) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx))) (substt x2 (substt x (ty_open 0 (VarF 1) T2x)))) as HIx0. {
        eapply hastp_subst. rewrite app_nil_l. eapply HIx. unfold substt. rewrite H10. eauto.
      }
      eu. simpl in HIx0.
      assert ((substt x (ty_open 0 (VarF 1) T2x))=(ty_open 0 (VarF 0) (substt x T2x))) as EqT2x. {
        change 1 with (0+1). erewrite subst_open. reflexivity. eauto.
      }
      assert (vr_closed 0 0 (VObj x2)) as HC0. {
        eapply vtp_closed1; eauto.
      }
      assert (vr_closed 0 0 (VObj x)) as HC. {
        eapply vtp_closed1; eauto.
      }
      assert ((tm_subst (VObj x2) (tm_subst (VObj x) (tm_open 0 (VarF 1) tx))) =
              (subst_tm x2 t)) as Eqtx0. {
        subst. unfold subst_tm.
        change 1 with (0+1).
        rewrite (proj1 (proj2 (proj2 (subst_open_rec 0 x HC)))).
        rewrite (proj1 (proj2 (proj2 subst_open_commute0_rec))).
        reflexivity.
        simpl.
        eapply (proj1 (proj2 (proj2 closed_subst_rec))).
        simpl. eauto.
        eauto.
      }
      assert (ttyd [] (subst_tm x2 t) (substt x2 (ty_open 0 (VarF 0) T5))) as HI. {
        subst. rewrite <- Eqtx0. unfold substt in EqT2x. rewrite <- EqT2x. eauto.
      }
      eu. simpl in HI.
      edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H26. eauto.
      simpl in HI2.
      assert (substt x2 (ty_open 0 (VarF 0) T2) = (ty_open 0 (VObj x2) T2)) as EqT. {
        erewrite subst_open_commute0b. erewrite subst_closed_id. reflexivity.
        eassumption. eauto.
      }
      rewrite EqT in HI2.
      right. repeat eexists. eapply step_app. eauto. eauto.

    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply step_app1. eauto. eapply T_AppVar.
      eauto. eauto. eauto. eauto.
      simpl in *. eassumption.

  - Case "sub". subst.
    assert ((exists x, t0 = tvr (VObj x)) \/
               (exists (t': tm) n2,
                  step t0 t' /\ tty [] t' T1 n2)) as HH.
    eapply IHtty; eauto. change 0 with (length ([]:tenv)) at 1. eapply stpd_closed1; eauto.
    destruct HH.
    + SCase "val".
      ev. subst. left. eexists. eauto.
    + SCase "step".
      ev. subst.
      right. repeat eexists. eauto. eapply T_Sub. eauto. eauto.
Qed.
