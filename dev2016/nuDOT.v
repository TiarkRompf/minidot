(*
nuDOT
T ::= Bot | Top | T1 /\ T2 | T1 \/ T2 |
      { def m(x: S): U^x } | { type A: S..U } | x.A | { z => T^z } |
      [x:S | T]  // T will always be an intersection of record types
t ::= x | t.m(t) | new t | [x:S | d^x... ] | t1 & t2
d ::= { def m(x: S): U^x = t^x } | { type A = T }
*)

(* in small-step *)
Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Lt.

Module DOT.

Definition id := nat.
Definition lb := nat.

Inductive ty : Type :=
  | TCls   : ty -> ty -> ty (* [x: S | T], T intersection type *)
  | TBot   : ty
  | TTop   : ty
  | TFun   : lb -> ty -> ty -> ty
  | TMem   : lb -> ty -> ty -> ty
  | TVar   : bool(*true for concrete context, false for abstract context *) ->
             id(*absolute position in context, from origin, invariant under context extension*) -> ty
  | TVarB  : id(*bound variable, de Bruijn, locally nameless style -- see open *) -> ty
  | TSel   : ty -> lb -> ty
  | TBind  : ty -> ty
  | TAnd   : ty -> ty -> ty
  | TOr    : ty -> ty -> ty
.

Inductive tm : Type :=
  | tvar  : bool(*like TVar*) -> id -> tm
(*| tobj  : dms(*self is next slot in abstract context -- see subst_tm*) -> tm *)
  | tapp  : tm -> lb -> tm -> tm
  | tnew  : tm -> tm  (* new t, where t must be of type TCls *)
  | tcls  : ty -> dms -> tm
  | tmix  : tm -> tm -> tm

with dm : Type :=
  | dnone : dm
  | dfun : ty -> ty -> tm -> dm
  | dty  : ty -> dm

(* we need our own list-like structure for stuctural recursion, e.g. in subst_tm *)
with dms : Type :=
  | dnil : dms
  | dcons : dm -> dms -> dms
.

Fixpoint dms_to_list (ds: dms) : list dm :=
  match ds with
    | dnil => []
    | dcons d ds => d :: dms_to_list ds
  end.

Inductive vl : Type :=
  | vobj  : dms -> vl
  | vcls  : ty -> dms -> vl
.

Definition venv := list vl.
Definition tenv := list ty.

Hint Unfold venv.
Hint Unfold tenv.

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

(* (index 3 (4 :: 3 :: 2 :: 1 :: 0 :: nil)) === Some 3 *)


Inductive closed: nat(*abstract, TVar false i*) -> nat(*concrete, TVar true j*) -> nat(*bound, TVarB k*)
                  -> ty -> Prop :=
| cl_cls: forall i j k S1 T1,
    closed i j (S k) S1 ->
    closed i j (S k) T1 ->
    closed i j k (TCls S1 T1)
| cl_bot: forall i j k,
    closed i j k TBot
| cl_top: forall i j k,
    closed i j k TTop
| cl_fun: forall i j k l T1 T2,
    closed i j k T1 ->
    closed i j (S k) T2 ->
    closed i j k (TFun l T1 T2)
| cl_mem: forall i j k l T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TMem l T1 T2)
| cl_var0: forall i j k x,
    i > x ->
    closed i j k (TVar false x)
| cl_var1: forall i j k x,
    j > x ->
    closed i j k (TVar true x)
| cl_varB: forall i j k x,
    k > x ->
    closed i j k (TVarB x)
| cl_sel: forall i j k T1 l,
    closed i j k T1 ->
    closed i j k (TSel T1 l)
| cl_bind: forall i j k T1,
    closed i j (S k) T1 ->
    closed i j k (TBind T1)
| cl_and: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TAnd T1 T2)
| cl_or: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TOr T1 T2)
.


Fixpoint open (k: nat) (u: ty) (T: ty) { struct T }: ty :=
  match T with
    | TCls S1 T1 => TCls (open (S k) u S1) (open (S k) u T1)
    | TVar b x => TVar b x (* free var remains free. functional, so we can't check for conflict *)
    | TVarB x => if beq_nat k x then u else TVarB x
    | TTop        => TTop
    | TBot        => TBot
    | TSel T1 l     => TSel (open k u T1) l
    | TFun l T1 T2  => TFun l (open k u T1) (open (S k) u T2)
    | TMem l T1 T2  => TMem l (open k u T1) (open k u T2)
    | TBind T1    => TBind (open (S k) u T1)
    | TAnd T1 T2  => TAnd (open k u T1) (open k u T2)
    | TOr T1 T2   => TOr (open k u T1) (open k u T2)
  end.

Fixpoint subst (U : ty) (T : ty) {struct T} : ty :=
  match T with
    | TCls S1 T1   => TCls (subst U S1) (subst U T1)
    | TTop         => TTop
    | TBot         => TBot
    | TMem l T1 T2 => TMem l (subst U T1) (subst U T2)
    | TSel T1 l    => TSel (subst U T1) l
    | TVarB i      => TVarB i
    | TVar true i  => TVar true i
    (* subst the _first_ aka _oldest_ abstract variables,
       the other abstract variables are shifted to resolve in the shrinked context *)
    | TVar false i => if beq_nat i 0 then U else TVar false (i-1)
    | TFun l T1 T2 => TFun l (subst U T1) (subst U T2)
    | TBind T2     => TBind (subst U T2)
    | TAnd T1 T2   => TAnd (subst U T1) (subst U T2)
    | TOr T1 T2    => TOr (subst U T1) (subst U T2)
  end.

(* substitutes the first variable of the abstract context by u, which refers to the concrete context *)
Fixpoint subst_tm (u:nat) (T : tm) {struct T} : tm :=
  match T with
    | tvar true i         => tvar true i
    | tvar false i        => if beq_nat i 0 then (tvar true u) else tvar false (i-1)
    | tapp t1 l t2        => tapp (subst_tm u t1) l (subst_tm u t2)
    | tnew t              => tnew (subst_tm u t)
    | tcls S1 ds          => tcls (subst (TVar true u) S1) (subst_dms u ds)
    | tmix t1 t2          => tmix (subst_tm u t1) (subst_tm u t2)
  end
with subst_dm (u:nat) (d: dm) {struct d} : dm :=
  match d with
    | dnone        => dnone
    | dty T        => dty (subst (TVar true u) T)
    | dfun T1 T2 t => dfun (subst (TVar true u) T1) (subst (TVar true u) T2) (subst_tm u t)
  end
with subst_dms (u:nat) (ds: dms) {struct ds} : dms :=
  match ds with
    | dnil        => dnil
    | dcons d ds1  => dcons (subst_dm u d) (subst_dms u ds1)
  end.

Definition substt x T := (subst (TVar true x) T).
Hint Immediate substt.

Fixpoint zip_n{A: Type}(n: nat)(l1 l2: list A)(f: A -> A -> A) : list A := match n with
| O => nil
| S m => match (index m l1), (index m l2) with
   | Some a1, Some a2 => (f a1 a2) :: (zip_n m l1 l2 f)
   | Some a1, None    =>    a1     :: (zip_n m l1 l2 f)
   | None   , Some a2 =>       a2  :: (zip_n m l1 l2 f)
   | None   , None   =>               (zip_n m l1 l2 f)
   end
end.

Definition zip{A: Type}(l1 l2: list A)(f: A -> A -> A) : list A :=
  zip_n (max (length l1) (length l2)) l1 l2 f.

Fixpoint listOfNone{A: Type}(n: nat): list (option A) := match n with
| O => nil
| S m => None :: (listOfNone m)
end.

Fixpoint sort_rcd_by_label(T: ty): list (option ty) := match T with
| TAnd T1 T2 => zip (sort_rcd_by_label T1) (sort_rcd_by_label T2)
                    (fun o1 o2 => match o1, o2 with
                     | Some U1, Some U2 => Some (TAnd U1 U2)
                     | Some U1, None    => Some U1
                     | None   , Some U2 => Some U2
                     | None   , None    => None
                     end)
| TMem l T1 T2 => (Some T) :: (listOfNone l)
| TFun l T1 T2 => (Some T) :: (listOfNone l)
| _ => nil
end.

Fixpoint list_to_rcd(l: list (option ty)): ty := match l with
| Some T :: tail => TAnd T (list_to_rcd tail)
| None :: tail => list_to_rcd tail
| nil => TTop
end.

Definition override_rcd(T1 T2: ty): ty :=
  list_to_rcd (zip (sort_rcd_by_label T1)
                   (sort_rcd_by_label T2)
                   (fun o1 o2 => match o2 with
                                 | Some U2 => Some U2
                                 | None => o1
                                 end)).

Fixpoint list_to_dms (l: list dm): dms :=
  match l with
    | nil => dnil
    | d :: ds => dcons d (list_to_dms ds)
  end.

Definition override_dms(ds1 ds2: dms): dms :=
  list_to_dms (zip (dms_to_list ds1)
                   (dms_to_list ds2)
                   (fun d1 d2 => match d2 with
                                 | dnone => d1
                                 | _ => d2
                                 end)).


(* Reduction semantics  *)
Inductive step : venv -> tm -> venv -> tm -> Prop :=
(* reduction *)
| ST_New : forall x G1 S ds,
    index x G1 = Some (vcls S ds) ->
    step G1 (tnew (tvar true x)) (vobj (subst_dms (length G1) ds) :: G1) (tvar true (length G1))
| ST_Cls : forall G1 S ds,
    step G1 (tcls S ds) ((vcls S ds) :: G1) (tvar true (length G1))
| ST_Mix : forall x1 x2 G1 S1 ds1 S2 ds2,
    index x1 G1 = Some (vcls S1 ds1) ->
    index x2 G1 = Some (vcls S2 ds2) ->
    step G1 (tmix (tvar true x1) (tvar true x2)) G1 (tcls (TAnd S1 S2) (override_dms ds1 ds2))
| ST_AppAbs : forall G1 f l x ds T1 T2 t12,
    index f G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dfun T1 T2 t12) ->
    step G1 (tapp (tvar true f) l (tvar true x)) G1 (subst_tm x t12)
(* congruence *)
| ST_App1 : forall G1 G1' t1 t1' l t2,
    step G1 t1 G1' t1' ->
    step G1 (tapp t1 l t2) G1' (tapp t1' l t2)
| ST_App2 : forall G1 G1' f t2 l t2',
    step G1 t2 G1' t2' ->
    step G1 (tapp (tvar true f) l t2) G1' (tapp (tvar true f) l t2')
| ST_New1 : forall G1 G1' t1 t1',
    step G1 t1 G1' t1' ->
    step G1 (tnew t1) G1' (tnew t1')
| ST_Mix1 : forall G1 G1' t1 t1' t2,
    step G1 t1 G1' t1' ->
    step G1 (tmix t1 t2) G1' (tmix t1' t2)
| ST_Mix2 : forall G1 G1' x t2 t2',
    step G1 t2 G1' t2' ->
    step G1 (tmix (tvar true x) t2) G1' (tmix (tvar true x) t2')
.

(*
  abstract env: GH = (xn:Tn) :: ... :: (x1:T1) :: (x0:T0) :: nil
  concrete env: G1 = (yn=vn) :: ... :: (y1=v1) :: (y0=v0) :: nil

*)

Inductive has_type : tenv -> venv -> tm -> ty -> nat -> Prop :=
  | T_Varc : forall GH G1 x ds S1 T1 n1,
      (* Note: In (vcls S1 ds) of G1, the self ref of ds is x0, because it was put into G1 during
      evaluation, where the abstract env is empty. *)
      index x G1 = Some (vcls S1 ds) ->
      dms_has_type [open 0 (TVar false 0) S1] G1
                   ds (open 0 (TVar false 0) T1) n1 ->
      closed 0 (length G1) 1 S1 ->
      closed 0 (length G1) 1 T1 ->
      has_type GH G1 (tvar true x) (TCls S1 T1) (S n1)
  | T_Vary : forall GH G1 x ds ds' T T' n1,
      index x G1 = Some (vobj ds) ->
      dms_has_type [T'] G1 ds' T' n1 ->
      subst_dms x ds' = ds ->
      substt x T' = T ->
      closed 0 (length G1) 0 T ->
      has_type GH G1 (tvar true x) T (S n1)
  | T_Varz : forall G1 GH x T n1,
      index x GH = Some T ->
      closed (length GH) (length G1) 0 T ->
      has_type GH G1 (tvar false x) T (S n1)
  | T_VarPack : forall GH G1 b x T1 T1' n1,
      has_type GH G1 (tvar b x) T1' n1 ->
      T1' = (open 0 (TVar b x) T1) ->
      closed (length GH) (length G1) 1 T1 ->
      has_type GH G1 (tvar b x) (TBind T1) (S n1)
  | T_VarUnpack : forall GH G1 b x T1 T1' n1,
      has_type GH G1 (tvar b x) (TBind T1) n1 ->
      T1' = (open 0 (TVar b x) T1) ->
      closed (length GH) (length G1) 0 T1' ->
      has_type GH G1 (tvar b x) T1' (S n1)
  (* T1 only has type aliases, so if S1 is a supertype of T1, it has good bounds *)
  | T_New : forall GH G1 t1 S1 T1 n1 n2,
      has_type GH G1 t1 (TCls S1 T1) n1 ->
      (* (actual type) <: (intersection of all self type requirements) *)
      stp ((open 0 (TVar false (length GH)) T1)::GH) G1
           (open 0 (TVar false (length GH)) T1) (open 0 (TVar false (length GH)) S1)
           n2 ->
      has_type GH G1 (tnew t1) (TBind T1) (S (n1+n2))
  | T_Cls : forall GH G1 S1 T1 ds n1,
      dms_has_type ((open 0 (TVar false (length GH)) S1) :: GH) G1
                 ds (open 0 (TVar false (length GH)) T1) n1 ->
      closed (length GH) (length G1) 1 S1 ->
      closed (length GH) (length G1) 1 T1 ->
      has_type GH G1 (tcls S1 ds) (TCls S1 T1) (S n1)
  | T_Mix : forall GH G1 t1 t2 S1 S2 T1 T2 n1 n2,
      has_type GH G1 t1 (TCls S1 T1) n1 ->
      has_type GH G1 t2 (TCls S2 T2) n2 ->
      has_type GH G1 (tmix t1 t2) (TCls (TAnd S1 S2) (override_rcd T1 T2)) (S (n1+n2))
  | T_App : forall l T1 T2 GH G1 t1 t2 n1 n2,
      has_type GH G1 t1 (TFun l T1 T2) n1 ->
      has_type GH G1 t2 T1 n2 ->
      closed (length GH) (length G1) 0 T2 ->
      has_type GH G1 (tapp t1 l t2) T2 (S (n1+n2))
  | T_AppVar : forall l T1 T2 T2' GH G1 t1 b2 x2 n1 n2,
      has_type GH G1 t1 (TFun l T1 T2) n1 ->
      has_type GH G1 (tvar b2 x2) T1 n2 ->
      T2' = (open 0 (TVar b2 x2) T2) ->
      closed (length GH) (length G1) 0 T2' ->
      has_type GH G1 (tapp t1 l (tvar b2 x2)) T2' (S (n1+n2))
  | T_Sub : forall GH G1 t T1 T2 n1 n2,
      has_type GH G1 t T1 n1 ->
      stp GH G1 T1 T2 n2 ->
      has_type GH G1 t T2 (S (n1 + n2))
with dms_has_type: tenv -> venv -> dms -> ty -> nat -> Prop :=
  | D_Nil : forall GH G1 n1,
      dms_has_type GH G1 dnil TTop (S n1)
  | D_None : forall GH G1 ds T n1,
      dms_has_type GH G1 ds T n1 ->
      dms_has_type GH G1 (dcons dnone ds) T (S n1)
  | D_Mem : forall GH G1 l T11 ds TS T n1,
      dms_has_type GH G1 ds TS n1 ->
      closed (length GH) (length G1) 0 T11 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TMem l T11 T11) TS ->
      dms_has_type GH G1 (dcons (dty T11) ds) T (S n1)
  | D_Abs : forall GH G1 l T11 T12 T12' t12 ds TS T n1 n2,
      dms_has_type GH G1 ds TS n1 ->
      has_type (T11::GH) G1 t12 T12' n2 ->
      T12' = (open 0 (TVar false (length GH)) T12) ->
      closed (length GH) (length G1) 0 T11 ->
      closed (length GH) (length G1) 1 T12 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TFun l T11 T12) TS ->
      dms_has_type GH G1 (dcons (dfun T11 T12 t12) ds) T (S (n1+n2))

with stp: tenv -> venv -> ty -> ty -> nat -> Prop :=
| stp_cls_refl: forall GH G1 S1 T n1,
    closed (length GH) (length G1) 1 S1 ->
    closed (length GH) (length G1) 1 T ->
    stp GH G1 (TCls S1 T) (TCls S1 T) (S n1)
| stp_bot: forall GH G1 T n1,
    closed (length GH) (length G1) 0  T ->
    stp GH G1 TBot T (S n1)
| stp_top: forall GH G1 T n1,
    closed (length GH) (length G1) 0 T ->
    stp GH G1 T  TTop (S n1)
| stp_fun: forall GH G1 l T1 T2 T3 T4 T2' T4' n1 n2,
    T2' = (open 0 (TVar false (length GH)) T2) ->
    T4' = (open 0 (TVar false (length GH)) T4) ->
    closed (length GH) (length G1) 1 T2 ->
    closed (length GH) (length G1) 1 T4 ->
    stp GH G1 T3 T1 n1 ->
    stp (T3::GH) G1 T2' T4' n2 ->
    stp GH G1 (TFun l T1 T2) (TFun l T3 T4) (S (n1+n2))
| stp_mem: forall GH G1 l T1 T2 T3 T4 n1 n2,
    stp GH G1 T3 T1 n2 ->
    stp GH G1 T2 T4 n1 ->
    stp GH G1 (TMem l T1 T2) (TMem l T3 T4) (S (n1+n2))

| stp_varx: forall GH G1 x n1,
    x < length G1 ->
    stp GH G1 (TVar true x) (TVar true x) (S n1)
| stp_varax: forall GH G1 x n1,
    x < length GH ->
    stp GH G1 (TVar false x) (TVar false x) (S n1)

| stp_strong_sel1: forall GH G1 l T2 ds TX x n1,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] G1 TX T2 n1 ->
    stp GH G1 (TSel (TVar true x) l) T2 (S n1)
| stp_strong_sel2: forall GH G1 l T1 ds TX x n1,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] G1 T1 TX n1 ->
    stp GH G1 T1 (TSel (TVar true x) l) (S n1)

| stp_sel1: forall GH G1 l T2 x n1,
    htp  GH G1 x (TMem l TBot T2) n1 ->
    stp GH G1 (TSel (TVar false x) l) T2 (S n1)

| stp_sel2: forall GH G1 l T1 x n1,
    htp  GH G1 x (TMem l T1 TTop) n1 ->
    stp GH G1 T1 (TSel (TVar false x) l) (S n1)

| stp_selx: forall GH G1 l T1 n1,
    closed (length GH) (length G1) 0 T1 ->
    stp GH G1 (TSel T1 l) (TSel T1 l) (S n1)



| stp_bind1: forall GH G1 T1 T1' T2 n1,
    htp (T1'::GH) G1 (length GH) T2 n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp GH G1 (TBind T1) T2 (S n1)

| stp_bindx: forall GH G1 T1 T1' T2 T2' n1,
    htp (T1'::GH) G1 (length GH) T2' n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    T2' = (open 0 (TVar false (length GH)) T2) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 1 T2 ->
    stp GH G1 (TBind T1) (TBind T2) (S n1)

| stp_and11: forall GH G1 T1 T2 T n1,
    stp GH G1 T1 T n1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp GH G1 (TAnd T1 T2) T (S n1)
| stp_and12: forall GH G1 T1 T2 T n1,
    stp GH G1 T2 T n1 ->
    closed (length GH) (length G1) 0 T1 ->
    stp GH G1 (TAnd T1 T2) T (S n1)
| stp_and2: forall GH G1 T1 T2 T n1 n2,
    stp GH G1 T T1 n1 ->
    stp GH G1 T T2 n2 ->
    stp GH G1 T (TAnd T1 T2) (S (n1+n2))

| stp_or21: forall GH G1 T1 T2 T n1,
    stp GH G1 T T1 n1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp GH G1 T (TOr T1 T2) (S n1)
| stp_or22: forall GH G1 T1 T2 T n1,
    stp GH G1 T T2 n1 ->
    closed (length GH) (length G1) 0 T1 ->
    stp GH G1 T (TOr T1 T2) (S n1)
| stp_or1: forall GH G1 T1 T2 T n1 n2,
    stp GH G1 T1 T n1 ->
    stp GH G1 T2 T n2 ->
    stp GH G1 (TOr T1 T2) T (S (n1+n2))

| stp_trans: forall GH G1 T1 T2 T3 n1 n2,
    stp GH G1 T1 T2 n1 ->
    stp GH G1 T2 T3 n2 ->
    stp GH G1 T1 T3 (S (n1+n2))


with htp: tenv -> venv -> id -> ty -> nat -> Prop :=
| htp_var: forall GH G1 x TX n1,
    index x GH = Some TX ->
    closed (S x) (length G1) 0 TX ->
    htp GH G1 x TX (S n1)
| htp_bind: forall GH G1 x TX n1,
    htp GH G1 x (TBind TX) n1 ->
    closed x (length G1) 1 TX ->
    htp GH G1 x (open 0 (TVar false x) TX) (S n1)
| htp_sub: forall GH GU GL G1 x T1 T2 n1 n2,
    (* use restricted GH. note: this is slightly different
    from the big-step version b/c here we do not distinguish
    if variables are bound in terms vs types. it would be easy
    to do exactly the same thing by adding this distinction. *)
    htp GH G1 x T1 n1 ->
    stp GL G1 T1 T2 n2 ->
    length GL = S x ->
    GH = GU ++ GL ->
    htp GH G1 x T2 (S (n1+n2)).

Inductive vtp(*possible types*) : nat(*pack count*) -> venv -> id -> ty -> nat(*size*) -> Prop :=
| vtp_cls: forall m G1 x S1 T1 ds n1,
    index x G1 = Some (vcls S1 ds) ->
    dms_has_type ((open 0 (TVar false 0) S1) :: nil) G1
               ds (open 0 (TVar false 0) T1) n1 ->
    closed 0 (length G1) 1 S1 ->
    closed 0 (length G1) 1 T1 ->
    vtp m G1 x (TCls S1 T1) (S n1)
| vtp_top: forall m G1 x n1,
    x < length G1 ->
    vtp m G1 x TTop (S n1)
| vtp_mem: forall m G1 x l ds TX T1 T2 n1 n2,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] G1 T1 TX n1 ->
    stp [] G1 TX T2 n2 ->
    vtp m G1 x (TMem l T1 T2) (S (n1+n2))
| vtp_fun: forall m G1 x l ds dsx T1 T2 T3 T4 T2' T4' t T1x T2x tx T' T2x' n1 n2 n3 n4,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dfun T1 T2 t) ->
    subst_dms x dsx = ds ->
    dms_has_type [T'] G1 dsx T' n4 ->
    subst_dm x (dfun T1x T2x tx) = (dfun T1 T2 t) ->
    T2x' = (open 0 (TVar false 1) T2x) ->
    has_type [T1x;T'] G1 tx T2x' n3 ->
    stp [] G1 T3 T1 n1 ->
    T2' = (open 0 (TVar false 0) T2) ->
    T4' = (open 0 (TVar false 0) T4) ->
    closed 0 (length G1) 1 T2 ->
    closed 0 (length G1) 1 T4 ->
    stp [T3] G1 T2' T4' n2 ->
    vtp m G1 x (TFun l T3 T4) (S (n1+n2+n3+n4))
| vtp_bind: forall m G1 x T2 n1,
    vtp m G1 x (open 0 (TVar true x) T2) n1 ->
    closed 0 (length G1) 1 T2 ->
    vtp (S m) G1 x (TBind T2) (S (n1))
| vtp_sel: forall m G1 x y l ds TX n1,
    index y G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    vtp m G1 x TX n1 ->
    vtp m G1 x (TSel (TVar true y) l) (S (n1))
| vtp_and: forall m m1 m2 G1 x T1 T2 n1 n2,
    vtp m1 G1 x T1 n1 ->
    vtp m2 G1 x T2 n2 ->
    m1 <= m -> m2 <= m ->
    vtp m G1 x (TAnd T1 T2) (S (n1+n2))
| vtp_or1: forall m m1 m2 G1 x T1 T2 n1,
    vtp m1 G1 x T1 n1 ->
    closed 0 (length G1) 0 T2 ->
    m1 <= m -> m2 <= m ->
    vtp m G1 x (TOr T1 T2) (S (n1))
| vtp_or2: forall m m1 m2 G1 x T1 T2 n1,
    vtp m1 G1 x T2 n1 ->
    closed 0 (length G1) 0 T1 ->
    m1 <= m -> m2 <= m ->
    vtp m G1 x (TOr T1 T2) (S (n1))
.

Definition has_typed GH G1 x T1 := exists n, has_type GH G1 x T1 n.

Definition stpd2 GH G1 T1 T2 := exists n, stp GH G1 T1 T2 n.

Definition htpd GH G1 x T1 := exists n, htp GH G1 x T1 n.

Definition vtpd m G1 x T1 := exists n, vtp m G1 x T1 n.

Definition vtpdd m G1 x T1 := exists m1 n, vtp m1 G1 x T1 n /\ m1 <= m.

Hint Constructors stp.
Hint Constructors vtp.

Ltac ep := match goal with
             | [ |- stp ?GH ?G1 ?T1 ?T2 ?N ] => assert (exists (n:nat), stp GH G1 T1 T2 n) as EEX
           end.

Ltac eu := match goal with
             | H: has_typed _ _ _ _ |- _ => destruct H as [? H]
             | H: stpd2 _ _ _ _ |- _ => destruct H as [? H]
             | H: htpd _ _ _ _ |- _ => destruct H as [? H]
             | H: vtpd _ _ _ _ |- _ => destruct H as [? H]
             | H: vtpdd _ _ _ _ |- _ => destruct H as [? [? [H ?]]]
           end.

Lemma stpd2_cls_refl: forall GH G1 S1 T,
  closed (length GH) (length G1) 1 S1 ->
  closed (length GH) (length G1) 1 T ->
  stpd2 GH G1 (TCls S1 T) (TCls S1 T).
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_bot: forall GH G1 T,
    closed (length GH) (length G1) 0 T ->
    stpd2 GH G1 TBot T.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_top: forall GH G1 T,
    closed (length GH) (length G1) 0 T ->
    stpd2 GH G1 T TTop.
Proof. intros. exists 1. eauto. Qed.
Lemma stpd2_fun: forall GH G1 l T1 T2 T3 T4 T2' T4',
    T2' = (open 0 (TVar false (length GH)) T2) ->
    T4' = (open 0 (TVar false (length GH)) T4) ->
    closed (length GH) (length G1) 1 T2 ->
    closed (length GH) (length G1) 1 T4 ->
    stpd2 GH G1 T3 T1 ->
    stpd2 (T3::GH) G1 T2' T4' ->
    stpd2 GH G1 (TFun l T1 T2) (TFun l T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.
Lemma stpd2_mem: forall GH G1 l T1 T2 T3 T4,
    stpd2 GH G1 T3 T1 ->
    stpd2 GH G1 T2 T4 ->
    stpd2 GH G1 (TMem l T1 T2) (TMem l T3 T4).
Proof. intros. repeat eu. eexists. eauto. Qed.



Lemma stpd2_trans: forall GH G1 T1 T2 T3,
    stpd2 GH G1 T1 T2 ->
    stpd2 GH G1 T2 T3 ->
    stpd2 GH G1 T1 T3.
Proof. intros. repeat eu. eexists. eauto. Qed.




Hint Constructors ty.
Hint Constructors vl.


Hint Constructors stp.
Hint Constructors vtp.
Hint Constructors htp.
Hint Constructors has_type.

Hint Unfold has_typed.
Hint Unfold stpd2.
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

Lemma index_max : forall X vs n (T: X),
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

Lemma index_exists : forall X vs n,
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


Lemma index_extend : forall X vs n a (T: X),
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

Lemma closed_extend : forall T X (a:X) i k G,
                       closed i (length G) k T ->
                       closed i (length (a::G)) k T.
Proof.
  intros T. induction T; intros; inversion H;  econstructor; eauto.
  simpl. omega.
Qed.

Lemma all_extend: forall ni,
  (forall GH  v1 G1 T1 T2 n,
     stp GH G1 T1 T2 n -> n < ni ->
     stp GH (v1::G1) T1 T2 n) /\
  (forall m v1 x G1 T2 n,
     vtp m G1 x T2 n -> n < ni ->
     vtp m (v1::G1) x T2 n) /\
  (forall v1 x GH G1 T2 n,
     htp GH G1 x T2 n -> n < ni ->
     htp GH (v1::G1) x T2 n) /\
  (forall GH G1 t T v n,
     has_type GH G1 t T n -> n < ni ->
     has_type GH (v::G1) t T n) /\
  (forall GH G1 ds T v n,
     dms_has_type GH G1 ds T n -> n < ni ->
     dms_has_type GH (v::G1) ds T n).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H.
  (* stp *)
  - econstructor; eapply closed_extend; assumption.
  - econstructor. eapply closed_extend. eauto.
  - econstructor. eapply closed_extend. eauto.
  - econstructor. eauto. eauto.
    eapply closed_extend. eauto. eapply closed_extend. eauto.
    eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. simpl. eauto.
  - econstructor. eauto.
  - econstructor. eapply index_extend. eauto. eauto. eapply IHn. eauto. omega.
  - econstructor. eapply index_extend. eauto. eauto. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto. eapply closed_extend. eauto.
  - eapply stp_bindx. eapply IHn. eauto. omega. eauto. eauto. eapply closed_extend. eauto. eapply closed_extend. eauto.
  - eapply stp_and11. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply stp_and12. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply stp_and2. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - eapply stp_or21. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply stp_or22. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply stp_or1. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - eapply stp_trans. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  (* vtp *)
  - econstructor.
    + eapply index_extend. eauto.
    + eapply IHn. assumption. omega.
    + eapply closed_extend. assumption.
    + eapply closed_extend. assumption.
  - econstructor. simpl. eauto.
  - econstructor. eapply index_extend. eauto. eauto. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eapply index_extend. eauto. eauto. eauto. eapply IHn. eauto. omega. eauto. eauto. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eauto. eauto. eapply closed_extend. eauto. eapply closed_extend. eauto. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - econstructor. eapply index_extend. eauto. eauto. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eauto. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply closed_extend. eauto. omega. eauto.
  - eapply vtp_or2. eapply IHn. eauto. omega. eapply closed_extend. eauto. omega. eauto.
  (* htp *)
  - econstructor. eauto. eapply closed_extend. eauto.
  - eapply htp_bind. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply htp_sub. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eauto. eauto.
  (* has_type *)
  - econstructor. eapply index_extend. eauto. eapply IHn. eauto. omega. eapply closed_extend. eauto. eapply closed_extend. eauto.
  - econstructor. eapply index_extend. eauto. eapply IHn. eauto. omega. eauto. eauto. eapply closed_extend. eauto.
  - econstructor. eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply closed_extend. eauto.
    eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eapply closed_extend. eauto.
  - eapply T_AppVar. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  (* dms_has_type *)
  - econstructor.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega. eapply closed_extend. eauto. eauto. eauto.
  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega. eauto. eapply closed_extend. eauto. eapply closed_extend. eauto. eauto. eauto.
Qed.

Lemma closed_upgrade_gh: forall i i1 j k T1,
  closed i j k T1 -> i <= i1 -> closed i1 j k T1.
Proof.
  intros. generalize dependent i1. induction H; intros; econstructor; eauto. omega.
Qed.

Lemma closed_extend_mult : forall T i j j' k,
                             closed i j k T -> j <= j' ->
                             closed i j' k T.
Proof.
  intros. generalize dependent j'. induction H; intros; econstructor; eauto. omega.
Qed.

Lemma closed_upgrade: forall i j k k1 T1,
  closed i j k T1 -> k <= k1 -> closed i j k1 T1.
Proof.
  intros. generalize dependent k1. induction H; intros; econstructor; eauto.
  eapply IHclosed1. omega.
  eapply IHclosed2. omega.
  eapply IHclosed2. omega.
  omega.
  eapply IHclosed. omega.
Qed.

Lemma closed_open: forall j k n b V T,
  closed k n (j+1) T ->
  closed k n j (TVar b V) ->
  closed k n j (open j (TVar b V) T).
Proof.
  intros. generalize dependent j.
  induction T; intros; inversion H; try econstructor; try eapply IHT1; eauto;
    try eapply IHT2; eauto; try eapply IHT; eauto.
  - eapply closed_upgrade; eauto.
  - eapply closed_upgrade; eauto.
  - eapply closed_upgrade; eauto.
  - Case "TVarB". simpl.
    case_eq (beq_nat j i); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
  - eapply closed_upgrade; eauto.
Qed.

Lemma closed_override_rcd: forall i j k T1 T2,
  closed i j k T1 ->
  closed i j k T2 ->
  closed i j k (override_rcd T1 T2).
Proof.
Admitted.

Lemma all_closed: forall ni,
  (forall GH G1 T1 T2 n,
     stp GH G1 T1 T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T1) /\
  (forall GH G1 T1 T2 n,
     stp GH G1 T1 T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T2) /\
  (forall m x G1 T2 n,
     vtp m G1 x T2 n -> n < ni ->
     x < length G1) /\
  (forall m x G1 T2 n,
     vtp m G1 x T2 n -> n < ni ->
     closed 0 (length G1) 0 T2) /\
  (forall x GH G1 T2 n,
     htp GH G1 x T2 n -> n < ni ->
     x < length GH) /\
  (forall x GH G1 T2 n,
     htp GH G1 x T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T2) /\
  (forall GH G1 t T n,
     has_type GH G1 t T n -> n < ni ->
     closed (length GH) (length G1) 0 T) /\
  (forall GH G1 ds T n,
     dms_has_type GH G1 ds T n -> n < ni ->
     closed (length GH) (length G1) 0 T).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H; destruct IHn as [IHS1 [IHS2 [IHV1 [IHV2 [IHH1 [IHH2 [IHT IHD]]]]]]].
  (* stp left *)
  - eapply closed_upgrade_gh. econstructor. eauto. eauto. eauto.
  - econstructor.
  - eauto.
  - econstructor. eapply IHS2. eauto. omega. eauto.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS1. eauto. omega.
  - econstructor. simpl. eauto.
  - econstructor. eauto.
  - econstructor. econstructor. eapply index_max. eauto.
  - eapply closed_upgrade_gh. eapply IHS1. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. eauto.
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
  - eapply closed_upgrade_gh. econstructor. eauto. eauto. eauto.
  - eauto.
  - econstructor.
  - econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - econstructor. simpl. eauto.
  - econstructor. eauto.
  - eapply closed_upgrade_gh. eapply IHS2. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply index_max. eauto.
  - eapply closed_upgrade_gh. eapply IHH2 in H1. inversion H1. eauto. omega. simpl. omega.
  - econstructor. econstructor. eapply IHH1. eauto. omega.
  - econstructor. eauto.
  - eauto.
  - econstructor. eauto.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eapply IHS2. eauto. omega.
  - econstructor. eapply IHS2. eauto. omega. eauto.
  - econstructor. eauto. eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  - eapply IHS2. eauto. omega.
  (* vtp left *)
  - eapply index_max. eauto.
  - assumption.
  - eapply index_max. eauto.
  - eapply index_max. eauto.
  - eapply IHV1. eauto. omega.
  - eapply IHV1. eauto. omega.
  - eapply IHV1. eauto. omega.
  - eapply IHV1. eauto. omega.
  - eapply IHV1. eauto. omega.
  (* vtp right *)
  - econstructor; assumption.
  - econstructor.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply IHS1. eauto. omega. eapply IHS2. eauto. omega.
  - change 0 with (length ([]:tenv)) at 1. econstructor. eapply IHS1. eauto. omega. eauto.
  - econstructor. eauto. (* eapply IHV2 in H1. eauto. omega. *)
  - econstructor. econstructor. eapply index_max. eauto.
  - econstructor. eapply IHV2. eauto. omega. eapply IHV2. eauto. omega.
  - econstructor. eapply IHV2. eauto. omega. eauto.
  - econstructor. eauto. eapply IHV2. eauto. omega.
  (* htp left *)
  - eapply index_max. eauto.
  - eapply IHH1. eauto. omega.
  - eapply IHH1. eauto. omega.
  (* htp right *)
  - eapply closed_upgrade_gh. eauto. subst. eapply index_max in H1. omega.
  - eapply IHH1 in H1. eapply closed_open. simpl. eapply closed_upgrade_gh. eauto. omega. econstructor. eauto. omega.
  - eapply closed_upgrade_gh. eapply IHS2. eauto. omega. rewrite H4. rewrite app_length. omega.
  (* has_type *)
  - subst. econstructor; eapply closed_upgrade_gh; eauto; omega.
  - subst. eapply closed_upgrade_gh. eauto. omega.
  - eauto.
  - econstructor. eapply closed_upgrade_gh. eauto. omega.
  - eapply IHT in H1. inversion H1; subst. eauto. omega.
  - eapply IHT in H1. inversion H1. econstructor. assumption. omega. 
  - econstructor. eauto. eauto.
  - eapply IHT in H1; try omega. eapply IHT in H2; try omega. inversion H1. inversion H2.
    repeat econstructor; try assumption.
    apply closed_override_rcd; assumption.
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHT in H1. inversion H1. eauto. omega.
  - eapply IHS2. eauto. omega.
  (* dms_has_type *)
  - econstructor.
  - subst. eapply IHD in H1. assumption. omega.
  - subst. econstructor. econstructor. eauto. eauto. eapply IHD. eauto. omega.
  - subst. econstructor. econstructor. eauto. eauto. eapply IHD. eauto. omega.
Qed.



Lemma vtp_extend : forall m v1 x G1 T2 n,
                      vtp m G1 x T2 n ->
                      vtp m (v1::G1) x T2 n.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma htp_extend : forall v1 x GH G1 T2 n,
                      htp GH G1 x T2 n ->
                      htp GH (v1::G1) x T2 n.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma stp_extend : forall GH  v1 G1 T1 T2 n,
                      stp GH G1 T1 T2 n ->
                      stp GH (v1::G1) T1 T2 n.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma stp_extend_mult : forall GH G1 G' T1 T2 n,
                      stp GH G1 T1 T2 n ->
                      stp GH (G'++G1) T1 T2 n.
Proof. intros. induction G'. simpl. eauto. simpl. eapply stp_extend. eauto. Qed.

Lemma has_type_extend: forall GH G1 t T v n1,
  has_type GH G1 t T n1 ->
  has_type GH (v::G1) t T n1.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma dms_has_type_extend: forall GH G1 t T v n1,
  dms_has_type GH G1 t T n1 ->
  dms_has_type GH (v::G1) t T n1.
Proof. intros. eapply all_extend. eauto. eauto. Qed.

Lemma has_type_extend_mult: forall GH G1 t T G' n1,
  has_type GH G1 t T n1 ->
  has_type GH (G'++G1) t T n1.
Proof. intros. induction G'. simpl. eauto. simpl. eapply has_type_extend. eauto. Qed.

Lemma htp_closed: forall x GH G1 T2 n,
  htp GH G1 x T2 n ->
  closed (length GH) (length G1) 0 T2.
Proof. intros. eapply all_closed with (x:=x). eauto. eauto. Qed.

Lemma vtp_closed: forall m G1 x T2 n1,
  vtp m G1 x T2 n1 ->
  closed 0 (length G1) 0 T2.
Proof. intros. eapply all_closed. eauto. eauto. Qed.

Lemma vtp_closed1: forall m G1 x T2 n1,
  vtp m G1 x T2 n1 ->
  x < length G1.
Proof. intros. eapply all_closed. eauto. eauto. Qed.

Lemma has_type_closed: forall GH G1 t T n1,
  has_type GH G1 t T n1 ->
  closed (length GH) (length G1) 0 T.
Proof. intros. eapply all_closed with (t:=t). eauto. eauto. Qed.

Lemma dms_has_type_closed: forall GH G1 t T n1,
  dms_has_type GH G1 t T n1 ->
  closed (length GH) (length G1) 0 T.
Proof. intros. eapply all_closed with (ds:=t). eauto. eauto. Qed.

Lemma has_type_closed_z: forall GH G1 z T n1,
  has_type GH G1 (tvar false z) T n1 ->
  z < length GH.
Proof.
  intros. remember (tvar false z) as t. generalize dependent z.
  induction H; intros; inversion Heqt; subst; eauto using index_max.
Qed.


Lemma has_type_closed1: forall GH G1 x T n1,
  has_type GH G1 (tvar true x) T n1 ->
  x < length G1.
Proof.
  intros. remember (tvar true x) as t. generalize dependent x.
  induction H; intros; inversion Heqt; subst; eauto using index_max.
Qed.

Lemma has_type_closed_b: forall G1 b x T n1,
  has_type [] G1 (tvar b x) T n1 ->
  b = true /\ x < length G1.
 Proof.
 intros.
 remember [] as GH.
 remember (tvar b x) as t.
 generalize dependent x. generalize dependent b. generalize HeqGH. clear HeqGH.
 induction H; intros; inversion Heqt; subst; eauto using index_max.
 - simpl in H. inversion H.
Qed.

Lemma stp_closed1 : forall GH G1 T1 T2 n1,
                      stp GH G1 T1 T2 n1 ->
                      closed (length GH) (length G1) 0 T1.
Proof. intros. edestruct all_closed. eapply H0. eauto. eauto. Qed.

Lemma stp_closed2 : forall GH G1 T1 T2 n1,
                      stp GH G1 T1 T2 n1 ->
                      closed (length GH) (length G1) 0 T2.
Proof. intros. edestruct all_closed. destruct H1. eapply H1. eauto. eauto. Qed.

Lemma stpd2_closed1 : forall GH G1 T1 T2,
                      stpd2 GH G1 T1 T2 ->
                      closed (length GH) (length G1) 0 T1.
Proof. intros. eu. eapply stp_closed1. eauto. Qed.


Lemma stpd2_closed2 : forall GH G1 T1 T2,
                      stpd2 GH G1 T1 T2 ->
                      closed (length GH) (length G1) 0 T2.
Proof. intros. eu. eapply stp_closed2. eauto. Qed.


Lemma beq_nat_true_eq: forall A, beq_nat A A = true.
Proof. intros. eapply beq_nat_true_iff. eauto. Qed.


Fixpoint tsize (T: ty) { struct T }: nat :=
  match T with
    | TCls S1 T1 => S (tsize S1 + tsize T1)
    | TVar b x => 1
    | TVarB x => 1
    | TTop        => 1
    | TBot        => 1
    | TSel T1 l   => S (tsize T1)
    | TFun l T1 T2 => S (tsize T1 + tsize T2)
    | TMem l T1 T2 => S (tsize T1 + tsize T2)
    | TBind T1    => S (tsize T1)
    | TAnd T1 T2  => S (tsize T1 + tsize T2)
    | TOr T1 T2   => S (tsize T1 + tsize T2)
  end.

Lemma open_preserves_size: forall T b x j,
  tsize T = tsize (open j (TVar b x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  - destruct (beq_nat j i); eauto.
Qed.

Lemma stpd2_refl_aux: forall n GH G1 T1,
  closed (length GH) (length G1) 0 T1 ->
  tsize T1 < n ->
  stpd2 GH G1 T1 T1.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst; simpl in H0.
  - Case "cls". exists 1. eauto.
  - Case "bot". exists 1. eauto.
  - Case "top". exists 1. eauto.
  - Case "fun". eapply stpd2_fun; eauto.
    eapply IHn; eauto; omega.
    eapply IHn; eauto.
    simpl. apply closed_open. simpl. eapply closed_upgrade_gh. eauto. omega.
    econstructor. omega.
    rewrite <- open_preserves_size. omega.
  - Case "mem". eapply stpd2_mem; try eapply IHn; eauto; try omega.
  - Case "var0". exists 1. eauto.
  - Case "var1". exists 1. eauto.
  - Case "varb". omega.
  - Case "sel". exists 1. eapply stp_selx. eauto.
  - Case "bind".
    eexists. eapply stp_bindx. eapply htp_var. simpl. rewrite beq_nat_true_eq. eauto.
    instantiate (1:=open 0 (TVar false (length GH)) T0).
    eapply closed_open. eapply closed_upgrade_gh. eauto. omega. econstructor. omega.
    eauto. eauto. eauto. eauto.
  - Case "and".
    destruct (IHn GH G1 T0 H1). omega.
    destruct (IHn GH G1 T2 H2). omega.
    eexists. eapply stp_and2. eapply stp_and11. eauto. eauto. eapply stp_and12. eauto. eauto.
  - Case "or".
    destruct (IHn GH G1 T0 H1). omega.
    destruct (IHn GH G1 T2 H2). omega.
    eexists. eapply stp_or1. eapply stp_or21. eauto. eauto. eapply stp_or22. eauto. eauto.
Grab Existential Variables.
apply 0.
Qed.

Lemma stpd2_refl: forall GH G1 T1,
  closed (length GH) (length G1) 0 T1 ->
  stpd2 GH G1 T1 T1.
Proof.
  intros. apply stpd2_refl_aux with (n:=S (tsize T1)); eauto.
Qed.

Lemma stpd2_reg1 : forall GH G1 T1 T2,
                      stpd2 GH G1 T1 T2 ->
                      stpd2 GH G1 T1 T1.
Proof. intros. eapply stpd2_refl. eapply stpd2_closed1. eauto. Qed.

Lemma stpd2_reg2 : forall GH G1 T1 T2,
                      stpd2 GH G1 T1 T2 ->
                      stpd2 GH G1 T2 T2.
Proof. intros. eapply stpd2_refl. eapply stpd2_closed2. eauto. Qed.



Ltac index_subst := match goal with
                      | H1: index ?x ?G = ?V1 , H2: index ?x ?G = ?V2 |- _ => rewrite H1 in H2; inversion H2; subst
                      | _ => idtac
                    end.

Ltac invty := match goal with
                | H1: TCls _ _ = _ |- _ => inversion H1
                | H1: TBot     = _ |- _ => inversion H1
                | H1: TSel _ _   = _ |- _ => inversion H1
                | H1: TMem _ _ _ = _ |- _ => inversion H1
                | H1: TVar _ _ = _ |- _ => inversion H1
                | H1: TFun _ _ _ = _ |- _ => inversion H1
                | H1: TBind  _ = _ |- _ => inversion H1
                | H1: TAnd _ _ = _ |- _ => inversion H1
                | H1: TOr _ _ = _ |- _ => inversion H1
                | _ => idtac
              end.

Ltac invstp_var := match goal with
  | H1: stp _ true _ _ TBot        (TVar _ _) _ |- _ => inversion H1
  | H1: stp _ true _ _ TTop        (TVar _ _) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TFun _ _ _)  (TVar _ _) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TMem _ _ _)  (TVar _ _) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TAnd _ _)  (TVar _ _) _ |- _ => inversion H1
  | H1: stp _ true _ _ (TOr _ _)  (TVar _ _) _ |- _ => inversion H1
  | _ => idtac
end.

Lemma closed_no_open: forall T x k l j,
  closed l k j T ->
  T = open j (TVar false x) T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed; rewrite <-IHclosed; auto];
  try solve [compute; compute in IHclosed1; compute in IHclosed2; rewrite <-IHclosed1; rewrite <-IHclosed2; auto].

  Case "TSelB".
    simpl.
    assert (k <> x0). omega.
    apply beq_nat_false_iff in H0.
    rewrite H0. auto.
Qed.


Lemma closed_no_subst: forall T j k TX,
   closed 0 j k T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
    try solve [erewrite IHT; eauto];
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto];
    try omega.
Qed.

Lemma closed_subst: forall j n k V T, closed (n+1) k j T -> closed n k 0 V -> closed n k j (subst V T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H; try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - Case "TSelH". simpl.
    case_eq (beq_nat i 0); intros E. eapply closed_upgrade. eapply closed_upgrade_gh. eauto. eauto. omega. econstructor. subst.
    assert (i > 0). eapply beq_nat_false_iff in E. omega. omega.
Qed.

(* not used? *)
Lemma subst_open_commute_m: forall j k n m V T2, closed (n+1) k (j+1) T2 -> closed m k 0 V ->
    subst V (open j (TVar false (n+1)) T2) = open j (TVar false n) (subst V T2).
Proof.
  intros. generalize dependent j. generalize dependent n.
  induction T2; intros; inversion H; simpl; eauto;
          try rewrite IHT2_1; try rewrite IHT2_2; try rewrite IHT2; eauto.

  simpl. case_eq (beq_nat i 0); intros E.
  eapply closed_no_open. eapply closed_upgrade. eauto. omega.
  simpl. eauto.

  simpl. case_eq (beq_nat j i); intros E.
  simpl. case_eq (beq_nat (n+1) 0); intros E2. eapply beq_nat_true_iff in E2. omega.
  assert (n+1-1 = n) as A. omega. rewrite A. eauto.
  eauto.
Qed.

(* not used? *)
Lemma subst_open_commute: forall j k n V T2, closed (n+1) k (j+1) T2 -> closed 0 k 0 V ->
    subst V (open j (TVar false (n+1)) T2) = open j (TVar false n) (subst V T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_commute0: forall T0 n j TX,
  closed 0 n (j+1) T0 ->
  (subst TX (open j (TVar false 0) T0)) = open j TX T0.
Proof.
  intros T0 n. induction T0; intros.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  eauto. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. inversion H. omega. eauto.
  simpl. inversion H. subst. destruct i. case_eq (beq_nat j 0); intros E; simpl; eauto.
  case_eq (beq_nat j (S i)); intros E; simpl; eauto.

  simpl. inversion H. rewrite IHT0. eauto. eauto.
  simpl. inversion H. rewrite IHT0. eauto. subst. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. inversion H. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
Qed.


Lemma subst_open_commute1: forall T0 x x0 j,
 (open j (TVar true x0) (subst (TVar true x) T0))
 = (subst (TVar true x) (open j (TVar true x0) T0)).
Proof.
  induction T0; intros.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto.
  eauto. eauto. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto. eauto. eauto.
  simpl. destruct b. simpl. eauto.
  case_eq (beq_nat i 0); intros E. simpl. eauto. simpl. eauto.

  simpl. case_eq (beq_nat j i); intros E. simpl. eauto. simpl. eauto.

  simpl. rewrite IHT0. eauto.
  simpl. rewrite IHT0. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto.
  simpl. rewrite IHT0_1. rewrite IHT0_2. eauto.
Qed.


Lemma subst_closed_id: forall x j k T2,
  closed 0 j k T2 ->
  substt x T2 = T2.
Proof. intros. eapply closed_no_subst. eauto. Qed.

Lemma closed_subst0: forall i j k x T2,
  closed (i + 1) j k T2 -> x < j ->
  closed i j k (substt x T2).
Proof. intros. eapply closed_subst. eauto. econstructor. eauto. Qed.

Lemma closed_subst1: forall i j k x T2,
  closed i j k T2 -> x < j -> i <> 0 ->
  closed (i-1) j k (substt x T2).
Proof.
  intros. eapply closed_subst.
  assert ((i - 1 + 1) = i) as R. omega.
  rewrite R. eauto. econstructor. eauto.
Qed.

Lemma index_subst: forall GH TX T0 T3 x,
  index (length (GH ++ [TX])) (T0 :: GH ++ [TX]) = Some T3 ->
  index (length GH) (map (substt x) (T0 :: GH)) = Some (substt x T3).
Proof.
  intros GH. induction GH; intros; inversion H.
  - eauto.
  - rewrite beq_nat_true_eq in H1. inversion H1. subst. simpl.
    rewrite map_length. rewrite beq_nat_true_eq. eauto.
Qed.

Lemma index_subst1: forall GH TX T3 x x0,
  index x0 (GH ++ [TX]) = Some T3 -> x0 <> 0 ->
  index (x0-1) (map (substt x) GH) = Some (substt x T3).
Proof.
  intros GH. induction GH; intros; inversion H.
  - eapply beq_nat_false_iff in H0. rewrite H0 in H2. inversion H2.
  - simpl.
    assert (beq_nat (x0 - 1) (length (map (substt x) GH)) = beq_nat x0 (length (GH ++ [TX]))). {
      case_eq (beq_nat x0 (length (GH ++ [TX]))); intros E.
      eapply beq_nat_true_iff. rewrite map_length. eapply beq_nat_true_iff in E. subst x0.
      rewrite app_length. simpl. omega.
      eapply beq_nat_false_iff. eapply beq_nat_false_iff in E.
      rewrite app_length in E. simpl in E. rewrite map_length.
      destruct x0. destruct H0. reflexivity. omega.
    }
    rewrite H1. case_eq (beq_nat x0 (length (GH ++ [TX]))); intros E; rewrite E in H2.
    inversion H2. subst. eauto. eauto.
Qed.

Lemma index_hit0: forall (GH:tenv) TX T2,
 index 0 (GH ++ [TX]) = Some T2 -> T2 = TX.
Proof.
  intros GH. induction GH; intros; inversion H.
  - eauto.
  - rewrite app_length in H1. simpl in H1.
    remember (length GH + 1) as L. destruct L. omega. eauto.
Qed.

Lemma subst_open: forall TX n x j,
  (substt x (open j (TVar false (n+1)) TX)) =
  (open j (TVar false n) (substt x TX)).
Proof.
  intros TX. induction TX; intros; eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
  - unfold substt. simpl. destruct b. eauto.
    case_eq (beq_nat i 0); intros E. eauto. eauto.
  - unfold substt. simpl.
    case_eq (beq_nat j i); intros E. simpl.
    assert (beq_nat (n + 1) 0 = false). eapply beq_nat_false_iff. omega.
    assert ((n + 1 - 1 = n)). omega.
    rewrite H. rewrite H0. eauto. eauto.
  - unfold substt. simpl. unfold substt in IHTX. erewrite <-IHTX. eauto.
  - unfold substt. simpl. unfold substt in IHTX. erewrite <-IHTX. eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
  - unfold substt. simpl. unfold substt in IHTX1. unfold substt in IHTX2. erewrite <-IHTX1. erewrite <-IHTX2. eauto.
Qed.

Lemma subst_open3: forall TX0 (GH:tenv) TX  x,
  (substt x (open 0 (TVar false (length (GH ++ [TX]))) TX0)) =
  (open 0 (TVar false (length GH)) (substt x TX0)).
Proof. intros. rewrite app_length. simpl. eapply subst_open. Qed.

Lemma subst_open4: forall T0 (GH:tenv) TX x,
  substt x (open 0 (TVar false (length (GH ++ [TX]))) T0) =
  open 0 (TVar false (length (map (substt x) GH))) (substt x T0).
Proof. intros. rewrite map_length. eapply subst_open3. Qed.

Lemma subst_open5: forall (GH:tenv) T0 x xi,
  xi <> 0 -> substt x (open 0 (TVar false xi) T0) =
  open 0 (TVar false (xi-1)) (substt x T0).
Proof.
  intros. remember (xi-1) as n. assert (xi=n+1) as R. omega. rewrite R.
  eapply subst_open.
Qed.

Lemma subst_open_commute0b: forall x T1 n,
  substt x (open n (TVar false 0) T1) = open n (TVar true x) (substt x T1).
Proof.
  unfold substt.
  intros x T1.
  induction T1; intros n; simpl;
  try rewrite IHT1; try rewrite IHT1_1; try rewrite IHT1_2;
  eauto.
  destruct b; eauto.
  case_eq (beq_nat i 0); intros; simpl; eauto.
  case_eq (beq_nat n i); intros; simpl; eauto.
Qed.

Lemma subst_open_commute_z: forall x T1 z n,
 subst (TVar true x) (open n (TVar false (z + 1)) T1) =
 open n (TVar false z) (subst (TVar true x) T1).
Proof.
  intros x T1 z.
  induction T1; intros n; simpl;
  try rewrite IHT1; try rewrite IHT1_1; try rewrite IHT1_2;
  eauto.
  destruct b; eauto.
  case_eq (beq_nat i 0); intros; simpl; eauto.
  case_eq (beq_nat n i); intros; simpl; eauto.
  assert (beq_nat (z + 1) 0 = false) as A. {
    apply false_beq_nat. omega.
  }
  rewrite A. f_equal. omega.
Qed.

Lemma gh_match1: forall (GU:tenv) GH GL TX,
  GH ++ [TX] = GU ++ GL ->
  length GL > 0 ->
  exists GL1, GL = GL1 ++ [TX] /\ GH = GU ++ GL1.
Proof.
  intros GU. induction GU; intros.
  - eexists. simpl in H. eauto.
  - destruct GH. simpl in H.
    assert (length [TX] = 1). eauto.
    rewrite H in H1. simpl in H1. rewrite app_length in H1. omega.
    destruct (IHGU GH GL TX).
    simpl in H. inversion H. eauto. eauto.
    eexists. split. eapply H1. simpl. destruct H1. simpl in H. inversion H. subst. eauto.
Qed.

Lemma gh_match: forall (GH:tenv) GU GL TX T0,
  T0 :: GH ++ [TX] = GU ++ GL ->
  length GL = S (length (GH ++ [TX])) ->
  GU = [] /\ GL = T0 :: GH ++ [TX].
Proof.
  intros. edestruct gh_match1. rewrite app_comm_cons in H. eapply H. omega.
  assert (length (T0 :: GH ++ [TX]) = length (GU ++ GL)). rewrite H. eauto.
  assert (GU = []). destruct GU. eauto. simpl in H.
  simpl in H2. rewrite app_length in H2. simpl in H2. rewrite app_length in H2.
  simpl in H2. rewrite H0 in H2. rewrite app_length in H2. simpl in H2.
  omega.
  split. eauto. rewrite H3 in H1. simpl in H1. subst. simpl in H1. eauto.
Qed.

Lemma sub_env1: forall (GL:tenv) GU GH TX,
  GH ++ [TX] = GU ++ GL ->
  length GL = 1 ->
  GL = [TX].
Proof.
  intros.
  destruct GL. inversion H0. destruct GL.
  eapply app_inj_tail in H. destruct H. subst. eauto.
  inversion H0.
Qed.

Lemma app_cons1: forall (G1:venv) v,
  v::G1 = [v]++G1.
Proof.
  intros. simpl. eauto.
Qed.



Lemma stp_subst_narrow0: forall n, forall GH G1 T1 T2 TX x n2,
   stp (GH++[TX]) G1 T1 T2 n2 -> x < length G1 -> n2 < n ->
   (forall GH (T3 : ty) (n1 : nat),
      htp (GH++[TX]) G1 0 T3 n1 -> n1 < n ->
      exists m2, vtpd m2 G1 x (substt x T3)) ->
   stpd2 (map (substt x) GH) G1 (substt x T1) (substt x T2).
Proof.
  intros n. induction n. intros. omega.
  intros ? ? ? ? ? ? ? ? ? ? narrowX.

  (* helper lemma for htp *)
  assert (forall ni n2, forall GH T2 xi,
    htp (GH ++ [TX]) G1 xi T2 n2 -> xi <> 0 -> n2 < ni -> ni < S n ->
    htpd (map (substt x) GH) G1 (xi-1) (substt x T2)) as htp_subst_narrow02. {
      induction ni. intros. omega.
      intros. inversion H2.
      + (* var *) subst.
        repeat eexists. eapply htp_var. eapply index_subst1. eauto. eauto.
        eapply closed_subst0. eapply closed_upgrade_gh. eauto. omega. eauto.
      + (* bind *) subst.
        assert (htpd (map (substt x) (GH0)) G1 (xi-1) (substt x (TBind TX0))) as BB.
        eapply IHni. eapply H6. eauto. omega. omega.
        rewrite subst_open5.
        eu. repeat eexists. eapply htp_bind. eauto. eapply closed_subst1. eauto. eauto. eauto. apply []. eauto.
      + (* sub *) subst.
        assert (exists GL0, GL = GL0 ++ [TX] /\ GH0 = GU ++ GL0) as A. eapply gh_match1. eauto. omega.
        destruct A as [GL0 [? ?]]. subst GL.
        assert (htpd (map (substt x) GH0) G1 (xi-1) (substt x T3)) as AA.
        eapply IHni. eauto. eauto. omega. omega.
        assert (stpd2 (map (substt x) GL0) G1 (substt x T3) (substt x T0)) as BB.
        eapply IHn. eauto. eauto. omega. { intros. eapply narrowX. eauto. eauto. }
        eu. eu. repeat eexists. eapply htp_sub. eauto. eauto.
        (* - *)
        rewrite map_length. rewrite app_length in H8. simpl in H8. unfold id in *. omega.
        subst GH0. rewrite map_app. eauto.
  }
  (* special case *)
  assert (forall ni n2, forall T0 T2,
    htp (T0 :: GH ++ [TX]) G1 (length (GH ++ [TX])) T2 n2 -> n2 < ni -> ni < S n ->
    htpd (map (substt x) (T0::GH)) G1 (length GH) (substt x T2)) as htp_subst_narrow0. {
      intros.
      rewrite app_comm_cons in H2.
      remember (T0::GH) as GH1. remember (length (GH ++ [TX])) as xi.
      rewrite app_length in Heqxi. simpl in Heqxi.
      assert (length GH = xi-1) as R. omega.
      rewrite R. eapply htp_subst_narrow02. eauto. omega. eauto. eauto.
  }


  (* main logic *)
  inversion H.
  - Case "cls". subst. eapply stpd2_cls_refl; fold subst; rewrite map_length.
    + eapply closed_subst0.
      * rewrite app_length in H2. simpl in H2. eapply H2.
      * eauto.
    + eapply closed_subst0.
      * rewrite app_length in H3. simpl in H3. eapply H3.
      * eauto.
  - Case "bot". subst.
    eapply stpd2_bot; eauto. rewrite map_length. simpl. eapply closed_subst0. rewrite app_length in H2. simpl in H2. eapply H2. eauto.
  - Case "top". subst.
    eapply stpd2_top; eauto. rewrite map_length. simpl. eapply closed_subst0. rewrite app_length in H2. simpl in H2. eapply H2. eauto.
  - Case "fun". subst.
    eapply stpd2_fun. eauto. eauto.
    rewrite map_length. eapply closed_subst0. rewrite app_length in *. simpl in *. eauto. omega.
    rewrite map_length. eapply closed_subst0. rewrite app_length in *. simpl in *. eauto. omega.
    eapply IHn; eauto. omega.
    rewrite <- subst_open_commute_z. rewrite <- subst_open_commute_z.
    specialize (IHn (T4::GH)). simpl in IHn.
    unfold substt in IHn at 2.  unfold substt in IHn at 3. unfold substt in IHn at 3.
    simpl in IHn. eapply IHn.
    rewrite map_length. rewrite app_length in *. eassumption.
    omega. omega. eauto.
  - Case "mem". subst.
    eapply stpd2_mem. eapply IHn; eauto. omega. eapply IHn; eauto. omega.


  - Case "varx". subst.
    eexists. eapply stp_varx. eauto.
  - Case "varax". subst.
    case_eq (beq_nat x0 0); intros E.
    + (* hit *)
      assert (x0 = 0). eapply beq_nat_true_iff. eauto.
      repeat eexists. unfold substt. subst x0. simpl. eapply stp_varx. eauto.
    + (* miss *)
      assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      repeat eexists. unfold substt. simpl. rewrite E. eapply stp_varax. rewrite map_length. rewrite app_length in H2. simpl in H2. omega.
  - Case "ssel1". subst.
    assert (substt x T2 = T2) as R. eapply subst_closed_id. eapply stpd2_closed2 with (GH:=[]). eauto.
    eexists. eapply stp_strong_sel1. eauto. eauto. rewrite R. eauto.

  - Case "ssel2". subst.
    assert (substt x T1 = T1) as R. eapply subst_closed_id. eapply stpd2_closed1 with (GH:=[]). eauto.
    eexists. eapply stp_strong_sel2. eauto. eauto. rewrite R. eauto.

  - Case "sel1". subst. (* invert htp to vtp and create strong_sel node *)
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0.
      assert (exists m0, vtpd m0 G1 x (substt x (TMem l TBot T2))) as A. eapply narrowX. eauto. omega.
      destruct A as [? A]. eu. inversion A. subst.
      repeat eexists. eapply stp_strong_sel1. eauto. eauto. unfold substt.
      eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      eapply htp_subst_narrow02 in H2.
      eu. repeat eexists. unfold substt. simpl. rewrite E. eapply stp_sel1. eapply H2. eauto. eauto. eauto.

  - Case "sel2". subst. (* invert htp to vtp and create strong_sel node *)
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff. eauto. subst x0.
      assert (exists m0, vtpd m0 G1 x (substt x (TMem l T1 TTop))) as A. eapply narrowX. eauto. omega.
      destruct A as [? A]. eu. inversion A. subst.
      repeat eexists. eapply stp_strong_sel2. eauto. eauto. unfold substt.
      eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff. eauto.
      eapply htp_subst_narrow02 in H2.
      eu. repeat eexists. unfold substt. simpl. rewrite E. eapply stp_sel2. eapply H2. eauto. eauto. eauto.
  - Case "selx".
    eexists. eapply stp_selx. eapply closed_subst0. rewrite app_length in H2. simpl in H2. rewrite map_length. eauto. eauto.

  - Case "bind1".
    assert (htpd (map (substt x) (T1'::GH)) G1 (length GH) (substt x T2)).
    eapply htp_subst_narrow0. eauto. eauto. omega.
    eu. repeat eexists. eapply stp_bind1. rewrite map_length. eapply H11.
    simpl. subst T1'. fold subst. eapply subst_open4.
    fold subst. eapply closed_subst0. rewrite app_length in H4. simpl in H4. rewrite map_length. eauto. eauto.
    eapply closed_subst0. rewrite map_length. rewrite app_length in H5. simpl in H5. eauto. eauto.

  - Case "bindx".
    assert (htpd (map (substt x) (T1'::GH)) G1 (length GH) (substt x T2')).
    eapply htp_subst_narrow0. eauto. eauto. omega.
    eu. repeat eexists. eapply stp_bindx. rewrite map_length. eapply H12.
    subst T1'. fold subst. eapply subst_open4.
    subst T2'. fold subst. eapply subst_open4.
    rewrite app_length in H5. simpl in H5. eauto. eapply closed_subst0. rewrite map_length. eauto. eauto.
    rewrite app_length in H6. simpl in H6. eauto. eapply closed_subst0. rewrite map_length. eauto. eauto.

  - Case "and11".
    assert (stpd2 (map (substt x) GH) G1 (substt x T0) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_and11. eauto. eapply closed_subst0. rewrite app_length in H3. rewrite map_length. eauto. eauto.
  - Case "and12".
    assert (stpd2 (map (substt x) GH) G1 (substt x T3) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_and12. eauto. eapply closed_subst0. rewrite app_length in H3. rewrite map_length. eauto. eauto.
  - Case "and2".
    assert (stpd2 (map (substt x) GH) G1 (substt x T1) (substt x T0)). eapply IHn. eauto. eauto. omega. eauto.
    assert (stpd2 (map (substt x) GH) G1 (substt x T1) (substt x T3)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eu. eexists. eapply stp_and2. eauto. eauto.

  - Case "or21".
    assert (stpd2 (map (substt x) GH) G1 (substt x T1) (substt x T0)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_or21. eauto. eapply closed_subst0. rewrite app_length in H3. rewrite map_length. eauto. eauto.
  - Case "or22".
    assert (stpd2 (map (substt x) GH) G1 (substt x T1) (substt x T3)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eexists. eapply stp_or22. eauto. eapply closed_subst0. rewrite app_length in H3. rewrite map_length. eauto. eauto.
  - Case "or1".
    assert (stpd2 (map (substt x) GH) G1 (substt x T0) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    assert (stpd2 (map (substt x) GH) G1 (substt x T3) (substt x T2)). eapply IHn. eauto. eauto. omega. eauto.
    eu. eu. eexists. eapply stp_or1. eauto. eauto.

  - Case "trans".
    assert (stpd2 (map (substt x) GH) G1 (substt x T1) (substt x T3)).
    eapply IHn; eauto. omega.
    assert (stpd2 (map (substt x) GH) G1 (substt x T3) (substt x T2)).
    eapply IHn; eauto. omega.
    eu. eu. repeat eexists. eapply stp_trans. eauto. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


Lemma stp_subst_narrowX: forall ml, forall nl, forall m GH G1 T2 TX x n1 n2,
   vtp m G1 x (substt x TX) n1 ->
   htp (GH++[TX]) G1 0 T2 n2 -> x < length G1 -> m < ml -> n2 < nl ->
   (forall (m0 : nat) (G1 : venv) x (T2 T3 : ty) (n1 n2 : nat),
        vtp m0 G1 x T2 n1 ->
        stp [] G1 T2 T3 n2 -> m0 <= m ->
        vtpdd m0 G1 x T3) ->
   vtpdd m G1 x (substt x T2). (* decrease b/c transitivity *)
Proof.
  intros ml. (* induction ml. intros. omega. *)
  intros nl. induction nl. intros. omega.
  intros.
  inversion H0.
  - Case "var". subst.
    assert (T2 = TX). eapply index_hit0. eauto.
    subst T2.
    repeat eexists. eauto. eauto.
  - Case "bind". subst.
    assert (vtpdd m G1 x (substt x (TBind TX0))) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    destruct A as [? [? [A ?]]]. inversion A. subst.
    repeat eexists. unfold substt. erewrite subst_open_commute0.
    assert (closed 0 (length G1) 0 (TBind (substt x TX0))). eapply vtp_closed. unfold substt in A. simpl in A. eapply A.
    assert ((substt x (TX0)) = TX0) as R. eapply subst_closed_id. eauto.
    unfold substt in R. rewrite R in H9. eapply H9. simpl. eauto. omega.
  - Case "sub". subst.
    destruct GL.

    assert (vtpdd m G1 x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    eu.
    assert (stpd2 [] G1 (substt x T1) (substt x T2)) as B.
    erewrite subst_closed_id. erewrite subst_closed_id. eexists. eassumption.
    eapply stp_closed2 in H6. simpl in H6. eapply H6.
    eapply stp_closed1 in H6. simpl in H6. eapply H6.
    simpl in B. eu.
    assert (vtpdd x0 G1 x (substt x T2)).
    eapply H4. eauto. eauto. eauto.
    eu. repeat eexists. eauto. omega.

    assert (length GL = 0) as LenGL. simpl in *. omega.
    assert (GL = []). destruct GL. reflexivity. simpl in LenGL. inversion LenGL.
    subst GL.
    assert (TX = t). eapply proj2. apply app_inj_tail. eassumption.
    subst t.
    assert (vtpdd m G1 x (substt x T1)) as A.
    eapply IHnl. eauto. eauto. eauto. eauto. omega. eauto.
    eu.
    assert (stpd2 (map (substt x) []) G1 (substt x T1) (substt x T2)) as B.
    eapply stp_subst_narrow0. eauto. eauto. eauto. {
      intros. eapply IHnl in H. eu. repeat eexists. eauto. eauto. eauto. eauto. omega. eauto.
    }
    simpl in B. eu.
    assert (vtpdd x0 G1 x (substt x T2)).
    eapply H4. eauto. eauto. eauto.
    eu. repeat eexists. eauto. omega.
Qed.


Lemma index_at_index: forall {A} x0 GH0 GH1 (v:A),
  beq_nat x0 (length GH1) = true ->
  index x0 (GH0 ++ v :: GH1) = Some v.
Proof.
  intros. apply beq_nat_true in H. subst.
  induction GH0.
  - simpl. rewrite <- beq_nat_refl. reflexivity.
  - simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    rewrite false_beq_nat. assumption. omega.
Qed.

Lemma index_same: forall {A} x0 (v0:A) GH0 GH1 (v:A) (v':A),
  beq_nat x0 (length GH1) = false ->
  index x0 (GH0 ++ v :: GH1) = Some v0 ->
  index x0 (GH0 ++ v' :: GH1) = Some v0.
Proof.
  intros ? ? ? ? ? ? ? E H.
  induction GH0.
  - simpl. rewrite E. simpl in H. rewrite E in H. apply H.
  - simpl.
    rewrite app_length. simpl.
    case_eq (beq_nat x0 (length GH0 + S (length GH1))); intros E'.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite H. reflexivity.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite IHGH0. reflexivity. assumption.
Qed.

Lemma exists_GH1L: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GH0 <= length GL ->
  exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ GH0.
Proof.
  intros X GU. induction GU; intros.
  - eexists. rewrite app_nil_l. split. reflexivity. simpl in H0. assumption.
  - induction GH1.

    simpl in H.
    assert (length (a :: GU ++ GL) = length GH0) as Contra. {
      rewrite H. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H. inversion H.
    specialize (IHGU GL GH1 GH0 H3 H0).
    destruct IHGU as [GH1L [IHA IHB]].
    exists GH1L. split. simpl. rewrite IHA. reflexivity. apply IHB.
Qed.

Lemma exists_GH0U: forall {X} (GH1: list X) (GH0: list X) (GU: list X) (GL: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GL < S (length GH0) ->
  exists GH0U, GH0 = GH0U ++ GL.
Proof.
  intros X GH1. induction GH1; intros.
  - simpl in H. exists GU. symmetry. assumption.
  - induction GU.

    simpl in H.
    assert (length GL = length (a :: GH1 ++ GH0)) as Contra. {
      rewrite H. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H. inversion H.
    specialize (IHGH1 GH0 GU GL H3 H0).
    destruct IHGH1 as [GH0U IH].
    exists GH0U. apply IH.
Qed.

(* upgrade_gh interlude begin *)

(* splicing -- for stp_extend. *)

Definition splice_var n i := if le_lt_dec n i then (i+1) else i.
Hint Unfold splice_var.

Fixpoint splice n (T : ty) {struct T} : ty :=
  match T with
    | TCls S1 T1   => TCls (splice n S1) (splice n T1)
    | TTop         => TTop
    | TBot         => TBot
    | TMem l T1 T2 => TMem l (splice n T1) (splice n T2)
    | TSel T1 l    => TSel (splice n T1) l
    | TVarB i      => TVarB i
    | TVar true i  => TVar true i
    | TVar false i => TVar false (splice_var n i)
    | TFun l T1 T2 => TFun l (splice n T1) (splice n T2)
    | TBind T2     => TBind (splice n T2)
    | TAnd T1 T2   => TAnd (splice n T1) (splice n T2)
    | TOr T1 T2    => TOr (splice n T1) (splice n T2)
  end.

Definition spliceat n (V: (venv*ty)) :=
  match V with
    | (G,T) => (G,splice n T)
  end.

Lemma splice_open_permute: forall {X} (G0:list X) T2 n j,
(open j (TVar false (n + S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open j (TVar false (n + length G0)) T2)).
Proof.
  intros X G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto.
  destruct b; eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  unfold splice_var.
  case_eq (le_lt_dec (length G) (n + length G)); intros EL LE.
  assert (n + S (length G) = n + length G + 1). omega.
  rewrite H. eauto.
  omega.
Qed.

Lemma splice_open_permute0: forall {X} (G0:list X) T2 j,
(open j (TVar false (S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open j (TVar false (length G0)) T2)).
Proof.
  intros.
  change (TVar false (length G0)) with (TVar false (0 + (length G0))).
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

Lemma index_spliceat_hi: forall G0 G2 x0 v1 G T,
    index x0 (G2 ++ G0) = Some (G, T) ->
    length G0 <= x0 ->
    index (x0 + 1) (map (spliceat (length G0)) G2 ++ v1 :: G0) =
    Some (G, splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply index_max in H. simpl in H. omega.
  - simpl in H. destruct a.
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

Lemma index_spliceat_lo: forall G0 G2 x0 v1 G T f,
    index x0 (G2 ++ G0) = Some (G, T) ->
    x0 < length G0 ->
    index x0 (map (spliceat f) G2 ++ v1 :: G0) = Some (G, T).
Proof.
  intros.
  assert (index x0 G0 = Some (G, T)). eapply index_splice_lo0; eauto.
  eapply index_extend_mult. eapply index_extend. eauto.
Qed.

Lemma closed_splice: forall i j k T n,
  closed i j k T ->
  closed (S i) j k (splice n T).
Proof.
  intros.
  Hint Constructors closed.
  induction H; simpl; eauto.
  unfold splice_var.
  case_eq (le_lt_dec n x); intros E LE;
  econstructor; omega.
Qed.

Lemma map_splice_length_inc: forall G0 G2 v1,
   (length (map (splice (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma map_spliceat_length_inc: forall G0 G2 v1,
   (length (map (spliceat (length G0)) G2 ++ v1 :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_inc_mult: forall i j k T,
  closed i j k T ->
  forall i' j' k',
  i' >= i -> j' >= j -> k' >= k ->
  closed i' j' k' T.
Proof.
  intros i j k T H. induction H; intros; eauto; try solve [constructor; omega].
  - econstructor. apply IHclosed1; omega. apply IHclosed2; omega.
  - econstructor. apply IHclosed1; omega. apply IHclosed2; omega.
  - econstructor. apply IHclosed; omega.
Qed.

Lemma closed_inc: forall i j k T,
  closed i j k T ->
  closed (S i) j k T.
Proof.
  intros. apply (closed_inc_mult i j k T H (S i) j k); omega.
Qed.

Lemma closed_splice_idem: forall i j k T n,
                            closed i j k T ->
                            n >= i ->
                            splice n T = T.
Proof.
  intros. induction H; eauto;
  simpl; try rewrite IHclosed; try rewrite IHclosed1; try rewrite IHclosed2; eauto.
  unfold splice_var.
  case_eq (le_lt_dec n x); intros E LE.
  omega. reflexivity.
Qed.

Lemma stp_splice_aux: forall ni, (forall GX G0 G1 T1 T2 v1 n,
   stp (G1++G0) GX T1 T2 n -> n < ni ->
   stp ((map (splice (length G0)) G1) ++ v1::G0) GX
   (splice (length G0) T1) (splice (length G0) T2) n) /\
  (forall GX G0 G1 x1 T1 v1 n,
   htp (G1++G0) GX x1 T1 n -> n < ni ->
   htp ((map (splice (length G0)) G1) ++ v1::G0) GX
   (splice_var (length G0) x1) (splice (length G0) T1) n).
Proof.
  intro ni. induction ni. split; intros; omega.
  destruct IHni as [IHstp IHhtp].
  split; intros; inversion H; subst.
  - Case "cls".
    eapply stp_cls_refl.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
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
    specialize (IHstp GX G0 (T4::G1)).
    simpl in IHstp. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    eapply IHstp. rewrite <- app_length. eauto. omega.
  - Case "mem".
    eapply stp_mem.
    eapply IHstp. eauto. omega.
    eapply IHstp. eauto. omega.
  - Case "varx".
    simpl. eapply stp_varx. omega.
  - Case "varax". simpl.
    unfold splice_var.
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_varax.
      rewrite map_splice_length_inc. omega.
    + eapply stp_varax.
      rewrite map_splice_length_inc. omega.
  - Case "ssel1".
    eapply stp_strong_sel1. eauto. eauto.
    assert (splice (length G0) T2=T2) as A. {
      eapply closed_splice_idem. eapply stp_closed2. eapply H3. simpl. omega.
    }
    rewrite A. assumption.
  - Case "ssel2".
    eapply stp_strong_sel2. eauto. eauto.
    assert (splice (length G0) T1=T1) as A. {
      eapply closed_splice_idem. eapply stp_closed1. eapply H3. simpl. omega.
    }
    rewrite A. assumption.
  - Case "sel1".
    eapply stp_sel1.
    specialize (IHhtp GX G0 G1 x (TMem l TBot T2)). simpl in IHhtp.
    eapply IHhtp. eauto. omega.
  - Case "sel2".
    eapply stp_sel2.
    specialize (IHhtp GX G0 G1 x (TMem l T1 TTop)). simpl in IHhtp.
    eapply IHhtp. eauto. omega.
  - Case "selx".
    eapply stp_selx.
    rewrite map_splice_length_inc. eapply closed_splice. eauto.
  - Case "bind1".
    eapply stp_bind1.
    rewrite map_splice_length_inc.
    assert (splice_var (length G0) (length (G1 ++ G0)) = (S (length (G1 ++ G0)))) as A. {
      unfold splice_var.
      case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros E LE.
      omega. clear LE. rewrite app_length in E. omega.
    }
    rewrite <- A.
    specialize (IHhtp GX G0 (open 0 (TVar false (length (G1 ++ G0))) T0 :: G1)).
    simpl in IHhtp. eapply IHhtp. eauto. omega.
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
    assert (splice_var (length G0) (length (G1 ++ G0)) = (S (length (G1 ++ G0)))) as A. {
      unfold splice_var.
      case_eq (le_lt_dec (length G0) (length (G1 ++ G0))); intros E LE.
      omega. clear LE. rewrite app_length in E. omega.
    }
    rewrite <- A.
    specialize (IHhtp GX G0 (open 0 (TVar false (length (G1 ++ G0))) T0 :: G1)).
    simpl in IHhtp. eapply IHhtp. eauto. omega.
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
  - Case "htp_var".
    unfold splice_var.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + eapply htp_var.
      apply index_splice_hi. eauto. eauto.
      eapply closed_splice.
      assert (S x1 = x1 + 1) as A by omega.
      rewrite <- A. eauto.
    + assert (splice (length G0) T1=T1) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      eapply htp_var.
      eapply index_splice_lo.
      rewrite A. eauto. omega.
      rewrite A. eauto.
  - Case "htp_bind".
    unfold splice_var.
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
      eapply htp_bind.
      specialize (IHhtp GX G0 G1 x1 (TBind TX)).
      simpl in IHhtp. unfold splice_var in IHhtp. rewrite LE in IHhtp.
      eapply IHhtp. eauto. omega.
      assert (S x1 = x1 + 1) as C by omega. rewrite <- C.
      eapply closed_splice. eauto.
    + assert (splice (length G0) TX = TX) as A. {
        eapply closed_splice_idem. eauto. omega.
      }
      assert (splice (length G0) (open 0 (TVar false x1) TX)=open 0 (TVar false x1) TX) as B. {
        eapply closed_splice_idem.
        eapply closed_open. eapply closed_upgrade_gh. eauto.
        instantiate (1:=S x1). omega.
        econstructor. omega. omega.
      }
      rewrite B.
      eapply htp_bind.
      specialize (IHhtp GX G0 G1 x1 (TBind TX)).
      simpl in IHhtp. unfold splice_var in IHhtp. rewrite LE in IHhtp.
      rewrite <- A. eapply IHhtp. eauto. omega. eauto.
  - Case "htp_sub".
    unfold splice_var.
    case_eq (le_lt_dec (length G0) x1); intros E LE.
    + assert (S x1 = x1 + 1) as A by omega.
      assert (exists GH1L, G1 = GU ++ GH1L /\ GL = GH1L ++ G0) as EQGH. {
        eapply exists_GH1L. eauto. omega.
      }
      destruct EQGH as [GH1L [EQGH1 EQGL]].
      assert (splice_var (length G0) x1=x1+1) as B. {
        unfold splice_var. rewrite LE. reflexivity.
      }
      rewrite <- B.
      eapply htp_sub.
      eapply IHhtp. eauto. omega.
      eapply IHstp. subst. eauto. omega.
      rewrite app_length. rewrite map_length. simpl.
      unfold splice_var. rewrite LE. subst. rewrite app_length in *. omega.
      subst. rewrite map_app. simpl. rewrite app_assoc. reflexivity.
    + assert (splice (length G0) T1=T1) as A1. {
        eapply closed_splice_idem. eapply stp_closed2. eauto. omega.
      }
      assert (splice (length G0) T0=T0) as A0. {
        eapply closed_splice_idem. eapply stp_closed1. eauto. omega.
      }
      assert (exists GH0U, G0 = GH0U ++ GL) as EQGH. {
        eapply exists_GH0U. eauto. omega.
      }
      destruct EQGH as [GH0U EQGH].
      assert (splice_var (length G0) x1=x1) as C. {
        unfold splice_var. rewrite LE. reflexivity.
      }
      rewrite <- C.
      eapply htp_sub.
      eapply IHhtp. eauto. omega.
      rewrite A1. rewrite A0. eauto.
      rewrite C. eauto.
      instantiate (1:=(map (splice (length G0)) G1 ++ v1 :: GH0U)).
      rewrite <- app_assoc. simpl. rewrite EQGH. reflexivity.
Qed.

Lemma stp_splice: forall GX G0 G1 T1 T2 v1 n,
   stp (G1++G0) GX T1 T2 n ->
   stp ((map (splice (length G0)) G1) ++ v1::G0) GX
   (splice (length G0) T1) (splice (length G0) T2) n.
Proof. intros. eapply stp_splice_aux. eauto. eauto. Qed.

Lemma htp_splice: forall GX G0 G1 x1 T1 v1 n,
   htp (G1++G0) GX x1 T1 n ->
   htp ((map (splice (length G0)) G1) ++ v1::G0) GX
   (splice_var (length G0) x1) (splice (length G0) T1) n.
Proof. intros. eapply stp_splice_aux. eauto. eauto. Qed.

Lemma stp_upgrade_gh_aux: forall ni,
  (forall GH T G1 T1 T2 n,
     stp GH G1 T1 T2 n -> n < ni ->
     stp (T::GH) G1 T1 T2 n) /\
  (forall T x GH G1 T2 n,
     htp GH G1 x T2 n -> n < ni ->
     htp (T::GH) G1 x T2 n).
Proof.
  intros n. induction n. repeat split; intros; omega.
  repeat split; intros; inversion H.
  (* stp *)
  - econstructor; eapply closed_upgrade_gh; eauto; simpl; omega.
  - econstructor. eapply closed_upgrade_gh. eauto. simpl. omega.
  - econstructor. eapply closed_upgrade_gh. eauto. simpl. omega.
  - econstructor. eauto. eauto.
    eapply closed_upgrade_gh. eauto. simpl. omega. eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply IHn. eauto. omega.
    subst.
    assert (splice (length GH) T0 = T0) as A. {
      eapply closed_splice_idem. eapply stp_closed2. eauto. omega.
    }
    assert (splice (length GH) T4 = T4) as B. {
      eapply closed_splice_idem. eapply stp_closed1. eauto. omega.
    }
    assert (splice (length GH) T3 = T3) as C. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length GH) T5 = T5) as D. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (map (splice (length GH)) [T4] ++ T::GH =
          (T4::T::GH)) as HGX. {
      simpl. rewrite B. eauto.
    }
    simpl. change (S (length GH)) with (0 + (S (length GH))).
    rewrite <- C. rewrite <- D.
    rewrite splice_open_permute. rewrite splice_open_permute.
    rewrite <- HGX.
    apply stp_splice. simpl. eauto.

  - econstructor. eapply IHn. eauto. omega. eapply IHn. eauto. omega.
  - econstructor. simpl. eauto.
  - econstructor. simpl. omega.
  - econstructor. eauto. eauto. eauto.
  - econstructor. eauto. eauto. eauto.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply IHn. eauto. omega.
  - econstructor. eapply closed_upgrade_gh. eauto. simpl. omega.
  - subst.
    assert (splice (length GH) T0 = T0) as A. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length GH) T2 = T2) as B. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (length (T :: GH)=splice_var (length GH) (length GH)) as C. {
      unfold splice_var. simpl.
      case_eq (le_lt_dec (length GH) (length GH)); intros E LE; omega.
    }
    assert (map (splice (length GH)) [(open 0 (TVar false (length GH)) T0)] ++ T::GH =
          (((open 0 (TVar false (S (length GH))) (splice (length GH) T0)))::T::GH)) as HGX. {
      simpl. rewrite <- splice_open_permute0. reflexivity.
    }
    eapply stp_bind1.
    rewrite <- B.
    instantiate (1:=(open 0 (TVar false (S (length GH))) (splice (length GH) T0))).
    rewrite <- HGX. rewrite C.
    apply htp_splice. simpl. eauto. simpl. rewrite A. reflexivity.
    eapply closed_upgrade_gh. eauto. simpl. omega.
    eapply closed_upgrade_gh. eauto. simpl. omega.

  - subst.
    assert (splice (length GH) T0 = T0) as A. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (splice (length GH) T3 = T3) as B. {
      eapply closed_splice_idem. eauto. omega.
    }
    assert (length (T :: GH)=splice_var (length GH) (length GH)) as C. {
      unfold splice_var. simpl.
      case_eq (le_lt_dec (length GH) (length GH)); intros E LE; omega.
    }
    assert (map (splice (length GH)) [(open 0 (TVar false (length GH)) T0)] ++ T::GH =
          (((open 0 (TVar false (S (length GH))) (splice (length GH) T0)))::T::GH)) as HGX. {
      simpl. rewrite <- splice_open_permute0. reflexivity.
    }
    eapply stp_bindx.
    instantiate (2:=(open 0 (TVar false (S (length GH))) (splice (length GH) T0))).
    rewrite <- HGX. rewrite C.
    apply htp_splice. simpl. eauto. simpl. rewrite A. reflexivity.
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
  (* htp *)
  - econstructor. eapply index_extend. eauto. eapply closed_upgrade_gh. eauto. omega.
  - eapply htp_bind. eapply IHn. eauto. omega. eapply closed_upgrade_gh. eauto. omega.
  - eapply htp_sub. eapply IHn. eauto. omega. eauto. eauto. subst GH.
    instantiate (1:=T::GU). eauto.
Qed.

Lemma stp_upgrade_gh : forall GH T G1 T1 T2 n,
                      stp GH G1 T1 T2 n ->
                      stp (T::GH) G1 T1 T2 n.
Proof. intros. eapply stp_upgrade_gh_aux. eauto. eauto. Qed.

Lemma stp_upgrade_gh_mult : forall GH GH' G1 T1 T2 n,
                      stp GH G1 T1 T2 n ->
                      stp (GH'++GH) G1 T1 T2 n.
Proof. intros. induction GH'. simpl. eauto. simpl. eapply stp_upgrade_gh. eauto. Qed.

Lemma stp_upgrade_gh_mult0 : forall GH G1 T1 T2 n,
                      stp [] G1 T1 T2 n ->
                      stp GH G1 T1 T2 n.
Proof. intros. rewrite <- (app_nil_r GH). eapply stp_upgrade_gh_mult. eauto. Qed.

Lemma hastp_upgrade_gh_var: forall G1 GH x T n1,
  has_type [] G1 (tvar true x) T n1 ->
  has_type GH G1 (tvar true x) T n1.
Proof.
  intros.
  remember (tvar true x) as t.  remember [] as GH0.
  induction H; eauto; inversion Heqt; subst.
  - eapply T_VarPack. eauto. eauto. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply T_VarUnpack. eauto. eauto. eapply closed_upgrade_gh. eauto. simpl. omega.
  - eapply T_Sub. eauto. eapply stp_upgrade_gh_mult0. eauto.
Qed.

Lemma hastp_upgrade_gh: forall G1 GH x T n1,
  has_type [] G1 (tvar true x) T n1 ->
  exists n, has_type GH G1 (tvar true x) T n.
Proof.
  intros. exists n1.
  induction GH. simpl. eauto. simpl. eapply hastp_upgrade_gh_var. eauto.
Qed.

(* upgrade_gh interlude ends *)

Lemma stp_narrow_aux: forall n,
  (forall GH G x T n0,
  htp GH G x T n0 -> n0 <= n ->
  forall GH1 GH0 GH' TX1 TX2,
    GH=GH1++[TX2]++GH0 ->
    GH'=GH1++[TX1]++GH0 ->
    stpd2 ([TX1]++GH0) G TX1 TX2 ->
    htpd GH' G x T) /\
  (forall GH G T1 T2 n0,
  stp GH G T1 T2 n0 -> n0 <= n ->
  forall GH1 GH0 GH' TX1 TX2,
    GH=GH1++[TX2]++GH0 ->
    GH'=GH1++[TX1]++GH0 ->
    stpd2 ([TX1]++GH0) G TX1 TX2 ->
    stpd2 GH' G T1 T2).
Proof.
  intros n.
  induction n.
  - Case "z". split; intros; inversion H0; subst; inversion H; eauto.
  - Case "s n". destruct IHn as [IHn_htp IHn_stp].
    split.
    {
    intros GH G x T n0 H NE. inversion H; subst;
    intros GH1 GH0 GH' TX1 TX2 EGH EGH' HX.
    + SCase "var".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (index x ([TX2]++GH0) = Some TX2) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (index x GH = Some TX2) as A2'. {
          rewrite EGH. eapply index_extend_mult. apply A2.
        }
        rewrite A2' in H0. inversion H0. subst.
        destruct HX as [nx HX].
        eexists. eapply htp_sub. eapply htp_var. eapply index_extend_mult.
        simpl. rewrite E. reflexivity.
        eapply stp_closed1 in HX. simpl in HX. eapply closed_upgrade_gh.
        eapply HX. apply beq_nat_true in E. subst. omega.
        eapply HX. simpl.
        f_equal. apply beq_nat_true in E. subst. reflexivity.
        simpl. reflexivity.
      * assert (index x GH' = Some T) as A. {
          subst.
          eapply index_same. apply E. eassumption.
        }
        eexists. eapply htp_var. eapply A.
        subst. eauto.
    + SCase "bind".
      edestruct IHn_htp with (GH:=GH) (GH':=GH').
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply htp_bind; eauto.
    + SCase "sub".
      edestruct IHn_htp as [? Htp].
      eapply H0. omega. eapply EGH. eapply EGH'. assumption.
      case_eq (le_lt_dec (S (length GH0)) (length GL)); intros E' LE'.
      assert (exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ (TX2) :: GH0) as EQGH. {
        eapply exists_GH1L. eassumption. simpl. eassumption.
      }
      destruct EQGH as [GH1L [EQGH1 EQGL]].
      edestruct IHn_stp as [? Hsub].
      eapply H1. omega. simpl. eapply EQGL. simpl. reflexivity. eapply HX.

      eexists. eapply htp_sub. eapply Htp. eapply Hsub.
      subst. rewrite app_length in *. simpl in *. eauto.
      rewrite EGH'. simpl. rewrite EQGH1. rewrite <- app_assoc. reflexivity.
      assert (exists GH0U, TX2::GH0 = GH0U ++ GL) as EQGH. {
        eapply exists_GH0U. eassumption. simpl. omega.
      }
      destruct EQGH as [GH0U EQGH].
      destruct GH0U. simpl in EQGH.
      assert (length (TX2::GH0)=length GL) as Contra. {
        rewrite EQGH. reflexivity.
      }
      simpl in Contra. rewrite <- Contra in H2. subst. omega.
      simpl in EQGH. inversion EQGH.
      eexists. eapply htp_sub. eapply Htp. eassumption. eauto.
      instantiate (1:=GH1 ++ [TX1] ++ GH0U). subst.
      rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
    }

    intros GH G T1 T2 n0 H NE. inversion H; subst;
    intros GH1 GH0 GH' TX1 TX2 EGH EGH' HX;
    assert (length GH' = length GH) as EGHLEN by solve [
      subst; repeat rewrite app_length; simpl; reflexivity
    ].
    + SCase "cls". eapply stpd2_cls_refl. rewrite EGHLEN; assumption. rewrite EGHLEN; assumption.
    + SCase "bot". eapply stpd2_bot. rewrite EGHLEN; assumption.
    + SCase "top". eapply stpd2_top. rewrite EGHLEN; assumption.
    + SCase "fun". eapply stpd2_fun.
      reflexivity. reflexivity.
      rewrite EGHLEN; assumption. rewrite EGHLEN; assumption.
      eapply IHn_stp; try eassumption. omega.
      eapply IHn_stp with (GH1:=(T4::GH1)); try eassumption.
      rewrite EGHLEN. eauto. omega.
      subst. simpl. reflexivity. subst. simpl. reflexivity.
    + SCase "mem". eapply stpd2_mem.
      eapply IHn_stp; try eassumption. omega.
      eapply IHn_stp; try eassumption. omega.
    + SCase "varx". eexists. eapply stp_varx. omega.
    + SCase "varax". eexists. eapply stp_varax.
      subst. rewrite app_length in *. simpl in *. omega.
    + SCase "ssel1". eexists. eapply stp_strong_sel1; try eassumption.
    + SCase "ssel2". eexists. eapply stp_strong_sel2; try eassumption.
    + SCase "sel1".
      edestruct IHn_htp as [? Htp]; eauto. omega.
    + SCase "sel2".
      edestruct IHn_htp as [? Htp]; eauto. omega.
    + SCase "selx".
      eexists. eapply stp_selx.
      subst. rewrite app_length in *. simpl in *. assumption.
    + SCase "bind1".
      edestruct IHn_htp with (GH1:=(open 0 (TVar false (length GH)) T0 :: GH1)) as [? Htp].
      eapply H0. omega. rewrite EGH. reflexivity. reflexivity. eapply HX.
      eexists. eapply stp_bind1.
      rewrite EGHLEN. subst. simpl. simpl in Htp. eapply Htp.
      rewrite EGHLEN. subst. simpl. reflexivity.
      rewrite EGHLEN. assumption. rewrite EGHLEN. assumption.
    + SCase "bindx".
      edestruct IHn_htp with (GH1:=(open 0 (TVar false (length GH)) T0 :: GH1)) as [? Htp].
      eapply H0. omega. rewrite EGH. reflexivity. reflexivity. eapply HX.
      eexists. eapply stp_bindx.
      rewrite EGHLEN. subst. simpl. simpl in Htp. eapply Htp.
      rewrite EGHLEN. subst. simpl. reflexivity.
      rewrite EGHLEN. subst. simpl. reflexivity.
      rewrite EGHLEN. assumption. rewrite EGHLEN. assumption.
    + SCase "and11".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_and11. eapply IH. rewrite EGHLEN. assumption.
    + SCase "and12".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_and12. eapply IH. rewrite EGHLEN. assumption.
    + SCase "and2".
      edestruct IHn_stp as [? IH1].
      eapply H0. omega. eauto. eauto. eauto.
      edestruct IHn_stp as [? IH2].
      eapply H1. omega. eauto. eauto. eauto.
      eexists. eapply stp_and2. eapply IH1. eapply IH2.
    + SCase "or21".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_or21. eapply IH. rewrite EGHLEN. assumption.
    + SCase "or22".
      edestruct IHn_stp as [? IH].
      eapply H0. omega. eauto. eauto. eauto.
      eexists. eapply stp_or22. eapply IH. rewrite EGHLEN. assumption.
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

Lemma stp_narrow: forall TX1 TX2 GH0 G T1 T2 n nx,
  stp ([TX2]++GH0) G T1 T2 n ->
  stp GH0 G TX1 TX2 nx -> (* note: only GH0, not TX2::GH0, even though that would hold as well *)
  stpd2 ([TX1]++GH0) G T1 T2.
Proof.
  intros. eapply stp_narrow_aux. eapply H. reflexivity.
  instantiate(3:=nil). simpl. reflexivity. simpl. reflexivity.
  eexists. eapply stp_upgrade_gh. eauto.
Qed.

Lemma hastp_narrow_aux: forall n,
  (forall GH G t T n0,
  has_type GH G t T n0 -> n0 <= n ->
  forall GH1 GH0 GH' TX1 TX2,
    GH=GH1++[TX2]++GH0 ->
    GH'=GH1++[TX1]++GH0 ->
    stpd2 ([TX1]++GH0) G TX1 TX2 ->
    exists n2, has_type GH' G t T n2) /\
  (forall GH G ds T n0,
  dms_has_type GH G ds T n0 -> n0 <= n ->
  forall GH1 GH0 GH' TX1 TX2,
    GH=GH1++[TX2]++GH0 ->
    GH'=GH1++[TX1]++GH0 ->
    stpd2 ([TX1]++GH0) G TX1 TX2 ->
    exists n2, dms_has_type GH' G ds T n2).
Proof.
  intros n.
  induction n.
  - Case "z". split; intros; inversion H0; subst; inversion H; eauto.
  - Case "s n". destruct IHn as [IH1 IH2]. split. {
    intros GH G t T n0 H Le. inversion H; subst;
    intros GH1 GH0 GH' TX1 TX2 EGH EGH' HX;
    assert (length GH' = length GH) as EGHLEN by solve [
      subst; repeat rewrite app_length; simpl; reflexivity
    ].
    + SCase "T_Varc". eauto.
    + SCase "T_Vary". eauto.
    + SCase "T_Varz".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (index x ([TX2]++GH0) = Some TX2) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (index x GH = Some TX2) as A2'. {
          rewrite EGH. eapply index_extend_mult. apply A2.
        }
        rewrite A2' in H0. inversion H0. subst.
        destruct HX as [nx HX].
        eexists. eapply T_Sub.
        - eapply T_Varz.
          { eapply index_extend_mult. simpl. rewrite E. reflexivity. }
          { eapply stp_closed1 in HX. eapply closed_upgrade_gh.
            * eapply HX.
            * do 3 rewrite app_length. omega. }
        - eapply stp_upgrade_gh_mult. eapply HX.
      * assert (index x GH' = Some T) as A. {
          subst.
          eapply index_same. apply E. eassumption.
        }
        eexists. eapply T_Varz. eapply A.
        subst.
        rewrite EGHLEN. assumption.
    + SCase "T_VarPack".
      edestruct IH1 with (GH:=GH) (GH':=GH').
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply T_VarPack; eauto.
      rewrite EGHLEN. assumption.
    + SCase "T_VarUnpack".
      edestruct IH1 with (GH:=GH) (GH':=GH').
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply T_VarUnpack; eauto.
      rewrite EGHLEN. assumption.
    + SCase "T_New".
      edestruct IH1 with (GH:=GH) (GH':=GH').
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      subst. rewrite app_comm_cons in H1.
      destruct (stp_narrow_aux n2) as [_ NS].
      edestruct NS as [nn NS1].
      eapply H1. omega. reflexivity. reflexivity. eassumption.
      simpl in NS1.
      eexists. eapply T_New. eauto.
      rewrite EGHLEN. eassumption.
    + SCase "T_Cls".
      edestruct IH2 with (GH :=(open 0 (TVar false (length GH)) S1 :: GH))
                         (GH':=(open 0 (TVar false (length GH)) S1 :: GH'))
      as [n2 IH].
      - eapply H0.
      - omega.
      - subst. rewrite app_comm_cons. reflexivity.
      - subst. rewrite <- app_comm_cons. reflexivity.
      - assumption.
      - eexists. rewrite <- EGHLEN in H1, H2. apply T_Cls.
        * rewrite EGHLEN. eapply IH.
        * assumption.
        * assumption.
    + SCase "T_Mix".
      edestruct IH1 with (GH:=GH) (GH':=GH') as [nt1 IHt1].
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      edestruct IH1 with (GH:=GH) (GH':=GH') as [nt2 IHt2].
      eapply H1. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply T_Mix. eapply IHt1. eapply IHt2.
    + SCase "T_App".
      edestruct IH1 with (GH:=GH) (GH':=GH') as [nt1 IHt1].
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      edestruct IH1 with (GH:=GH) (GH':=GH') as [nt2 IHt2].
      eapply H1. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply T_App. eapply IHt1. eapply IHt2.
      rewrite EGHLEN. eassumption.
    + SCase "T_AppVar".
      edestruct IH1 with (GH:=GH) (GH':=GH') as [nt1 IHt1].
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      edestruct IH1 with (GH:=GH) (GH':=GH') as [nt2 IHt2].
      eapply H1. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply T_AppVar. eapply IHt1. eapply IHt2.
      reflexivity.
      rewrite EGHLEN. eassumption.
    + SCase "T_Sub".
      edestruct IH1 with (GH:=GH) (GH':=GH').
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      subst.
      destruct (stp_narrow_aux n2) as [_ NS].
      edestruct NS as [nn NS1].
      eapply H1. omega. reflexivity. reflexivity. eassumption.
      simpl in NS1.
      eexists. eapply T_Sub. eauto. eapply NS1.
    } {
    intros GH G t T n0 H Le. inversion H; subst;
    intros GH1 GH0 GH' TX1 TX2 EGH EGH' HX;
    assert (length GH' = length GH) as EGHLEN by solve [
      subst; repeat rewrite app_length; simpl; reflexivity
    ].
    + SCase "D_Nil".
      eexists. eapply D_Nil.
    + SCase "D_None".
      edestruct IH2 with (GH:=GH) (GH':=GH') as [nt1 IH].
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply D_None. eapply IH.
    + SCase "D_Mem".
      edestruct IH2 with (GH:=GH) (GH':=GH') as [nt1 IH].
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      eexists. eapply D_Mem. eapply IH.
      rewrite EGHLEN. eassumption. reflexivity. reflexivity.
    + SCase "D_Abs".
      edestruct IH2 with (GH:=GH) (GH':=GH') as [nt1 IH2a].
      eapply H0. omega. subst. reflexivity. subst. reflexivity. assumption.
      edestruct IH1 with (GH := T11 :: GH) (GH':= T11 :: GH') as [n11 IH1a].
      - eapply H1.
      - omega.
      - subst. rewrite app_comm_cons. reflexivity.
      - subst. rewrite <- app_comm_cons. reflexivity.
      - assumption.
      - eexists. eapply D_Abs.
        * eapply IH2a.
        * eapply IH1a.
        * rewrite EGHLEN. reflexivity.
        * rewrite EGHLEN. assumption.
        * rewrite EGHLEN. assumption.
        * reflexivity.
        * reflexivity.
    }
  Grab Existential Variables. apply 0. apply 0. apply 0. 
Qed.

Lemma narrow_dms_has_type: forall G1 T1 S1 n1 ds n2,
  stp [T1] G1 T1 S1 n1 ->
  dms_has_type [S1] G1 ds T1 n2 ->
  exists n3, dms_has_type [T1] G1 ds T1 n3.
Proof.
  intros. eapply hastp_narrow_aux. eapply H0. reflexivity.
  instantiate(3:=nil). simpl. reflexivity. simpl. reflexivity. simpl. eauto.
Qed.

(* Note: TCls can be a subtype of a path type, or of an TAnd type, etc, ... do we want
   all these features? *)

(* possible types closure *)
Lemma vtp_widen: forall l, forall n, forall k, forall m1 G1 x T2 T3 n1 n2,
  vtp m1 G1 x T2 n1 ->
  stp [] G1 T2 T3 n2 ->
  m1 < l -> n2 < n -> n1 < k ->
  vtpdd m1 G1 x T3.
Proof.
  intros l. induction l. intros. solve by inversion.
  intros n. induction n. intros. solve by inversion.
  intros k. induction k; intros. solve by inversion.
  inversion H.
  - Case "cls". subst. inversion H0; subst.
    + SCase "cls". repeat eexists. simpl in *. econstructor; eauto. eauto.
    + SCase "top". repeat eexists. simpl in *. econstructor. eapply index_max. eauto. eauto.
    + SCase "ssel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
       eapply stp_closed2 in H0. simpl in H0. subst. inversion H0. inversion H13. omega.
    + SCase "and".
      assert (VT0: vtpdd m1 G1 x T0). { eapply IHn. eauto. eauto. omega. omega. eauto. }
      assert (VT2: vtpdd m1 G1 x T2). { eapply IHn. eauto. eauto. omega. omega. eauto. }
      eu. eu.
      repeat eexists. eapply vtp_and; eauto. omega.
    + SCase "or1".
      assert (vtpdd m1 G1 x T0). { eapply IHn; eauto. omega. } eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T2) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "top". inversion H0; subst; invty.
    + SCase "top". repeat eexists; eauto.
    + SCase "ssel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H9. omega.
    + SCase "and".
      assert (vtpdd m1 G1 x T1). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 G1 x T0). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T1). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T0). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T0) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "mem". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply index_max. eauto. eauto.
    + SCase "mem". invty. subst.
      repeat eexists. eapply vtp_mem. eauto. eauto.
      eapply stp_trans. eauto. eauto.
      eapply stp_trans. eauto. eauto.
      eauto.
    + SCase "sel2".
      assert (vtpdd m1 G1 x TX0). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H12. omega.
    + SCase "and".
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 G1 x T5). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T5). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T5) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "fun". inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply index_max. eauto. eauto.
    + SCase "fun". invty. subst.
      assert (stpd2 [T8] G1 (open 0 (TVar false 0) T0) (open 0 (TVar false 0) T5)) as A. {
        eapply stp_narrow. simpl. eassumption. simpl. eassumption.
      }
      destruct A as [na A].
      repeat eexists. eapply vtp_fun. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      eapply stp_trans. eauto. eauto. eauto. eauto. eauto. eauto. eauto. reflexivity.
    + SCase "sel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. subst. inversion H17. omega.
    + SCase "and".
      assert (vtpdd m1 G1 x T6). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 G1 x T7). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T6). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T7). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T7) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "bind".
    inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto.
    + SCase "sel2".
      assert (vtpdd (S m) G1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H10. omega.
    + SCase "bind1".
      invty. subst.
      remember (TVar false (length [])) as VZ.
      remember (TVar true x) as VX.

      (* left *)
      assert (vtpd m G1 x (open 0 VX T0)) as LHS. eexists. eassumption.
      eu.
      (* right *)
      assert (substt x (open 0 VZ T0) = (open 0 VX T0)) as R. unfold substt. subst. eapply subst_open_commute0. eauto.
      assert (substt x T3 = T3) as R1. eapply subst_closed_id. eauto.

      assert (vtpdd m G1 x (substt x T3)) as BB. {
        eapply stp_subst_narrowX. rewrite <-R in LHS. eapply LHS.
        instantiate (2:=nil). simpl. eapply H11. eapply vtp_closed1. eauto. eauto. eauto.
        { intros. eapply IHl. eauto. eauto. omega. eauto. eauto. }
      }
      rewrite R1 in BB.
      eu. repeat eexists. eauto. omega.
    + SCase "bindx".
      invty. subst.
      remember (TVar false (length [])) as VZ.
      remember (TVar true x) as VX.

      (* left *)
      assert (vtpd m G1 x (open 0 VX T0)) as LHS. eexists. eassumption.
      eu.
      (* right *)
      assert (substt x (open 0 VZ T0) = (open 0 VX T0)) as R. unfold substt. subst. eapply subst_open_commute0. eauto.

      assert (vtpdd m G1 x (substt x (open 0 VZ T4))) as BB. {
        eapply stp_subst_narrowX. rewrite <-R in LHS. eapply LHS.
        instantiate (2:=nil). simpl. eapply H11. eapply vtp_closed1. eauto. eauto. eauto.
        { intros. eapply IHl. eauto. eauto. omega. eauto. eauto. }
      }
      unfold substt in BB. subst. erewrite subst_open_commute0 in BB.
      clear R.
      eu. repeat eexists. eapply vtp_bind. eauto. eauto. omega. eauto. (* enough slack to add bind back *)
    + SCase "and".
      assert (vtpdd (S m) G1 x T1). eapply IHn; eauto. omega. eu.
      assert (vtpdd (S m) G1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd (S m) G1 x T1). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd (S m) G1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd (S m) G1 x T4) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "ssel2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto.
    + SCase "ssel1". index_subst. index_subst. eapply IHn. eapply H6. eauto. eauto. omega. eauto.
    + SCase "ssel2".
      assert (vtpdd m1 G1 x TX0). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel1".
      assert (closed (length ([]:tenv)) (length G1) 0 (TSel (TVar false x0) l1)) as A.
      eapply stpd2_closed2. eauto.
      simpl in A. inversion A. inversion H12. omega.
    + SCase "selx".
      eauto.
    + SCase "and".
      assert (vtpdd m1 G1 x T1). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T1). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T2) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.
  - Case "and". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto.
    + SCase "sel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H13. omega.
    + SCase "and11". eapply IHn in H4. eu. repeat eexists. eauto. omega. eauto. omega. omega. eauto.
    + SCase "and12". eapply IHn in H5. eu. repeat eexists. eauto. omega. eauto. omega. omega. eauto.
    + SCase "and".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "trans".
      assert (vtpdd m1 G1 x T4) as LHS. eapply IHn. eauto. eauto. eauto. omega. eauto. eu.
      assert (vtpdd x0 G1 x T3) as BB. eapply IHn. eapply LHS. eauto. omega. omega. eauto. eu.
      repeat eexists. eauto. omega.

  - Case "or1". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto.
    + SCase "sel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H13. omega.
    + SCase "and".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "or...".
      eapply IHn in H4. eu.
      repeat eexists. eapply H4. omega. eauto. omega. omega. eauto.
    + SCase "or...".
      assert (vtpdd m1 G1 x T4) as A. eapply IHn. eapply H. eauto. omega. omega. eauto. eu.
      eapply IHn in A. eu.
      repeat eexists. eauto. omega. eauto. omega. omega. eauto.

  - Case "or2". subst. inversion H0; subst; invty.
    + SCase "top". repeat eexists. eapply vtp_top. eapply vtp_closed1. eauto. eauto.
    + SCase "sel2".
      assert (vtpdd m1 G1 x TX). eapply IHn; eauto. omega.
      eu. repeat eexists. eapply vtp_sel. eauto. eauto. eauto. eauto.
    + SCase "sel2".
      eapply stp_closed2 in H0. simpl in H0. inversion H0. inversion H13. omega.
    + SCase "and".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. eu.
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_and; eauto. eauto.
    + SCase "or1".
      assert (vtpdd m1 G1 x T2). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or1; eauto. eauto.
    + SCase "or2".
      assert (vtpdd m1 G1 x T4). eapply IHn; eauto. omega. eu.
      repeat eexists. eapply vtp_or2; eauto. eauto.
    + SCase "or...".
      eapply IHn in H4. eu.
      repeat eexists. eapply H4. omega. eauto. omega. omega. eauto.
    + SCase "or...".
      assert (vtpdd m1 G1 x T4) as A. eapply IHn. eapply H. eauto. omega. omega. eauto. eu.
      eapply IHn in A. eu.
      repeat eexists. eauto. omega. eauto. omega. omega. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


Lemma stp_subst_narrow_z: forall GH0 TX G1 T1 T2 x m n1 n2,
  stp (GH0 ++ [TX]) G1 T1 T2 n2 ->
  vtp m G1 x (substt x TX) n1 ->
  stpd2 (map (substt x) GH0) G1 (substt x T1) (substt x T2).
Proof.
  intros.
  edestruct stp_subst_narrow0. eauto. eapply vtp_closed1. eauto. eauto.
  { intros. edestruct stp_subst_narrowX. eauto. eauto.
    eapply vtp_closed1. eauto. eauto. eauto.
    { intros. eapply vtp_widen; eauto. }
    ev. repeat eexists. eauto.
  }
  eexists. eassumption.
Qed.

Lemma length_subst_dms: forall ds x,
  (length (dms_to_list ds))=(length (dms_to_list (subst_dms x ds))).
Proof.
  intros. induction ds; eauto.
  simpl. rewrite IHds. reflexivity.
Qed.

Lemma index_subst_dms: forall ds ds0 D ds1 x,
  dms_to_list ds = ds0 ++ dms_to_list (dcons D ds1) ->
  index (length (dms_to_list ds1)) (dms_to_list (subst_dms x ds)) = Some (subst_dm x D).
Proof.
  intros. generalize dependent ds1. generalize dependent ds. induction ds0; intros.
  - simpl in H. destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite <- length_subst_dms. rewrite beq_nat_true_eq. reflexivity.
  - destruct ds. simpl in H. inversion H. simpl in H. inversion H. subst.
    simpl. rewrite false_beq_nat. eapply IHds0. eauto.
    rewrite <- length_subst_dms. rewrite H2. rewrite app_length. simpl.
    omega.
Qed.

Lemma dms_hastp_inv: forall G1 x ds' T' n,
  dms_has_type [T'] G1 ds' T' n ->
  closed 0 (length G1) 0 (substt x T') ->
  index x G1 = Some (vobj (subst_dms x ds')) ->
  exists m n, vtp m G1 x (substt x T') n.
Proof.
  intros G1 x ds' T' n H HC HI.
  remember T' as T0. remember H as HT0. clear HeqHT0.
  rewrite HeqT0 in H at 2. rewrite HeqT0. rewrite HeqT0 in HC. clear HeqT0.
  remember ds' as ds0. rewrite Heqds0 in H.
  assert (exists dsa, dms_to_list ds0 = dsa ++ dms_to_list ds') as Hds. {
    exists []. rewrite app_nil_l. subst. reflexivity.
  }
  clear Heqds0.
  remember n as n0. rewrite Heqn0 in *. rewrite <- Heqn0 in HT0. clear Heqn0.
  remember [T0] as GH. generalize dependent T0.
  induction H; intros.
  - repeat eexists. eapply vtp_top. eapply index_max. eauto.
  - eapply IHdms_has_type; eauto. simpl in Hds. destruct Hds as [dsb Hds].
    exists (dsb ++ [dnone]). rewrite <- app_assoc. apply Hds.
  - subst.
    assert (closed 0 (length G1) 0 (substt x TS)) as HCS. {
      unfold substt in *. simpl in HC. inversion HC; subst.
      eauto.
    }
    assert (closed 0 (length G1) 0 (substt x T11)) as HC11. {
      unfold substt in *. simpl in HC. inversion HC; subst.
      inversion H6; subst. eauto.
    }
    assert (stpd2 [] G1 (substt x T11) (substt x T11)) as A. {
      eapply stpd2_refl. eauto.
    }
    eu.
    destruct Hds as [dsa Hdsa]. simpl in Hdsa.
    edestruct IHdms_has_type as [? [? AS]]. eauto. eauto. eauto. exists (dsa ++ [dty T11]). rewrite <- app_assoc. simpl. eauto. eauto. eauto.
    unfold substt in *. simpl.
    repeat eexists. eapply vtp_and. eapply vtp_mem. eauto.
    erewrite index_subst_dms with (D:=dty T11). simpl. reflexivity. eauto.
    eauto. eauto. eauto. eauto. eauto.
  - subst.
    assert (closed 0 (length G1) 0 (substt x TS)) as HCS. {
      unfold substt in *. simpl in HC. inversion HC; subst.
      eauto.
    }
    assert (closed 0 (length G1) 0 (substt x T11)) as HC11. {
      unfold substt in *. simpl in HC. inversion HC; subst.
      inversion H8; subst. eauto.
    }
    assert (closed 1 (length G1) 0 (open 0 (TVar false 0) (substt x T12))) as HC12. {
      unfold substt in *. simpl in HC. inversion HC; subst. inversion H8; subst.
      eapply closed_open. eapply closed_upgrade_gh. eauto. omega.
      econstructor. omega.
    }
    assert (stpd2 [] G1 (substt x T11) (substt x T11)) as A. {
      eapply stpd2_refl. eauto.
    }
    eu.
    assert (stpd2 [(substt x T11)] G1 (open 0 (TVar false 0) (substt x T12)) (open 0 (TVar false 0) (substt x T12))) as B. {
      eapply stpd2_refl. eauto.
    }
    eu.
    destruct Hds as [dsa Hdsa]. simpl in Hdsa.
    edestruct IHdms_has_type as [? [? AS]]. eauto. eauto. eauto. exists (dsa ++ [dfun T11 T12 t12]). rewrite <- app_assoc. simpl. eauto. eauto. eauto.
    unfold substt in *. simpl.
    repeat eexists. eapply vtp_and. eapply vtp_fun. eauto.
    erewrite index_subst_dms with (D:=dfun T11 T12 t12). simpl. reflexivity. eauto.
    eauto. eapply HT0. simpl. reflexivity. eauto. eauto. eauto. eauto. eauto.
    eapply closed_subst. eauto. econstructor. eapply index_max. eauto.
    eapply closed_subst. eauto. econstructor. eapply index_max. eauto.
    eauto. eauto. eauto. eauto.
Grab Existential Variables.
apply 0. apply 0.
Qed.

Lemma hastp_inv: forall G1 x T n1,
  has_type [] G1 (tvar true x) T n1 ->
  exists m n1, vtp m G1 x T n1.
Proof.
  intros. remember [] as GH. remember (tvar true x) as t.
  induction H; subst; try inversion Heqt.
  - Case "cls". subst. repeat eexists. eapply vtp_cls; eauto.
  - Case "var". subst. eapply dms_hastp_inv; eauto.
  - Case "pack". subst.
    destruct IHhas_type. eauto. eauto. ev.
    repeat eexists. eapply vtp_bind. eauto. eauto.
  - Case "unpack". subst.
    destruct IHhas_type. eauto. eauto. ev. inversion H0.
    repeat eexists. eauto.
  - Case "sub".
    destruct IHhas_type. eauto. eauto. ev.
    assert (exists m0, vtpdd m0 G1 x T2). eexists. eapply vtp_widen; eauto.
    ev. eu. repeat eexists. eauto.
  Grab Existential Variables. apply 0.
Qed.

Lemma substt_override_rcd: forall x T1 T2,
  substt x (override_rcd T1 T2) = override_rcd (substt x T1) (substt x T2).
Admitted.

Lemma substt_cls: forall x S1 T1,
  substt x (TCls S1 T1) = TCls (substt x S1) (substt x T1).
Proof.
  intros. unfold substt. simpl. reflexivity.
Qed.

Lemma substt_and: forall x T1 T2,
  substt x (TAnd T1 T2) = TAnd (substt x T1) (substt x T2).
Proof.
  intros. unfold substt. simpl. reflexivity.
Qed.

Lemma hastp_subst_aux_z: forall ni, 
   (forall G1 GH TX T x t n1 n2,
    has_type (GH++[TX]) G1 t T n2 -> n2 < ni ->
    has_type [] G1 (tvar true x) (substt x TX) n1 ->
    exists n3, has_type (map (substt x) GH) G1 (subst_tm x t) (substt x T) n3)
/\ (forall G1 GH TX T x ds n1 n2,
    dms_has_type (GH++[TX]) G1 ds T n2 -> n2 < ni ->
    has_type [] G1 (tvar true x) (substt x TX) n1 ->
    exists n3, dms_has_type (map (substt x) GH) G1 (subst_dms x ds) (substt x T) n3).
Proof.
  intro ni. induction ni. split; intros; omega. destruct IHni as [IHniT IHniD].
  split;
  intros; remember (GH++[TX]) as GH0; revert GH HeqGH0; inversion H; intros.
  - Case "varc". subst.
    assert (substt x S1 = S1) as EqS1. {
      erewrite subst_closed_id. reflexivity. eauto.
    }
    assert (substt x T1 = T1) as EqT1. {
      erewrite subst_closed_id. reflexivity. eauto.
    }
    rewrite substt_cls. rewrite EqS1. rewrite EqT1.
    simpl. eexists. eapply T_Varc; eauto.
  - Case "vary".
    assert (substt x T = T) as EqT. {
      erewrite subst_closed_id. reflexivity. eauto.
    }
    subst. simpl. eexists. eapply T_Vary. eauto. eauto. eauto.
    rewrite EqT. reflexivity. rewrite EqT. eauto.
  - Case "varz". subst. simpl.
    case_eq (beq_nat x0 0); intros E.
    + assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0.
      eapply index_hit0 in H2. subst.
      eapply hastp_upgrade_gh. eauto.
    + assert (x0 <> 0). eapply beq_nat_false_iff; eauto.
      eexists. eapply T_Varz. eapply index_subst1. eauto. eauto. rewrite map_length. eapply closed_subst0. rewrite app_length in H3. simpl in H3. eapply H3. eapply has_type_closed1. eauto.
  - Case "pack". subst. simpl.
    edestruct IHniT as [? IH]. eauto. omega. eauto.
    assert (substt x (TBind T1) = (TBind (substt x T1))) as A. {
      eauto.
    }
    rewrite A.
    destruct b.
    + eexists. eapply T_VarPack. eapply IH.
      unfold substt. rewrite subst_open_commute1. reflexivity.
      rewrite map_length. eapply closed_subst0. rewrite app_length in H4. simpl in H4.
      apply H4. eapply has_type_closed1. eauto.
    + case_eq (beq_nat x0 0); intros E.
      * assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0.
        simpl in IH.
        eexists. eapply T_VarPack. eapply IH. rewrite subst_open_commute0b. eauto.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4. simpl in H4.
        eapply H4. econstructor. eapply has_type_closed1. eauto.
      * assert (x0 <> 0). eapply beq_nat_false_iff; eauto.
        simpl in IH. rewrite E in IH.
        eexists. eapply T_VarPack. eapply IH.
        remember (x0 - 1) as z.
        assert (x0 = z + 1) as B. {
          intuition. destruct x0. specialize (H3 eq_refl). inversion H3.
          subst. simpl. rewrite <- minus_n_O. rewrite Nat.add_1_r.
          reflexivity.
        }
        rewrite B. unfold substt.
        rewrite subst_open_commute_z. reflexivity.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4.
        simpl in H4. eapply H4.
        econstructor. eapply has_type_closed1. eauto.
  - Case "unpack". subst. simpl.
    edestruct IHniT as [? IH]. eapply H2. omega. eauto.
    assert (substt x (TBind T1) = (TBind (substt x T1))) as A. {
      eauto.
    }
    rewrite A in IH.
    destruct b.
    + eexists. eapply T_VarUnpack. eapply IH.
      unfold substt. rewrite subst_open_commute1. reflexivity.
      rewrite map_length. eapply closed_subst0. rewrite app_length in H4. simpl in H4.
      apply H4. eapply has_type_closed1. eauto.
    + case_eq (beq_nat x0 0); intros E.
      * assert (x0 = 0). eapply beq_nat_true_iff; eauto. subst x0.
        simpl in IH.
        eexists. eapply T_VarUnpack. eapply IH. rewrite subst_open_commute0b. eauto.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4. simpl in H4.
        eapply H4. econstructor. eapply has_type_closed1. eauto.
      * assert (x0 <> 0). eapply beq_nat_false_iff; eauto.
        simpl in IH. rewrite E in IH.
        eexists. eapply T_VarUnpack. eapply IH.
        remember (x0 - 1) as z.
        assert (x0 = z + 1) as B. {
          intuition. destruct x0. specialize (H3 eq_refl). inversion H3.
          subst. simpl. rewrite <- minus_n_O. rewrite Nat.add_1_r.
          reflexivity.
        }
        rewrite B. unfold substt.
        rewrite subst_open_commute_z. reflexivity.
        rewrite map_length. eapply closed_subst. rewrite app_length in H4.
        simpl in H4. eapply H4.
        econstructor. eapply has_type_closed1. eauto.
  - Case "new". subst. simpl.
    edestruct IHniT as [? IH1]. eapply H2. omega. eauto. unfold substt in IH1. simpl in IH1.
    rewrite app_length in *. simpl in *.
    remember (TVar false (length GH1 + 1)) as y.
    assert (E: stpd2 (subst (TVar true x) (open 0 y T1) :: map (substt x) GH1) G1 
                       (subst (TVar true x) (open 0 y T1)) (subst (TVar true x) (open 0 y S1))). {
      apply hastp_inv in H1. destruct H1 as [? [? Vx]].
      rewrite <- map_cons.
      refine (stp_subst_narrow_z _ _ _ _ _ _ _ _ _ _ Vx). apply H3.
    }
    destruct E as [? ?].
    eexists. eapply T_New; fold subst; fold subst_tm.
    + apply IH1.
    + repeat rewrite <- subst_open_commute_z.
      rewrite <- map_cons. rewrite map_length. rewrite <- Heqy. apply H4.
  - Case "cls". subst.
    remember (TVar false ((length GH1) + 1)) as y.
    assert (E: exists n, dms_has_type (map (substt x) (open 0 y S1 :: GH1)) G1
      (subst_dms x ds) (subst (TVar true x) (open 0 y T1)) n). {
      eapply IHniD.
      rewrite app_length in *. simpl in *. rewrite <- Heqy in H2. apply H2. omega. apply H1.
    }
    destruct E as [n E].
    eexists. refine (T_Cls _ _ _ _ _ _ _ _ _ ).
    + repeat rewrite <- subst_open_commute_z.
      rewrite map_length. rewrite <- map_cons. rewrite <- Heqy.
      apply E.
    + rewrite map_length. rewrite app_length in *. simpl in *.
      eapply closed_subst0. assumption. eapply has_type_closed1. eauto.
    + rewrite map_length. rewrite app_length in *. simpl in *.
      eapply closed_subst0. assumption. eapply has_type_closed1. eauto.
  - Case "mix". subst. simpl.
    assert (A1: exists n,
      has_type (map (substt x) GH1) G1 (subst_tm x t1) (substt x (TCls S1 T1)) n). {
      eapply IHniT. eassumption. omega. eassumption.
    }
    assert (A2: exists n,
      has_type (map (substt x) GH1) G1 (subst_tm x t2) (substt x (TCls S2 T2)) n). {
      eapply IHniT. eassumption. omega. eassumption.
    }
    destruct A1 as [n11 A1]. destruct A2 as [n12 A2].
    eexists. rewrite substt_cls. rewrite substt_and. rewrite substt_override_rcd.
    refine (T_Mix _ _ _ _ _ _ _ _ _ _ _ _); rewrite <- substt_cls.
    + eapply A1.
    + eapply A2.
  - Case "app". subst. simpl.
    edestruct IHniT as [? IH1]. eapply H2. omega. eauto.
    edestruct IHniT as [? IH2]. eapply H3. omega. eauto.
    eexists. eapply T_App. eauto. eauto. eapply closed_subst.
    subst. rewrite map_length. rewrite app_length in *. simpl in *. eauto.
    subst. rewrite map_length. econstructor. eapply has_type_closed1. eauto.
  - Case "appvar". subst. simpl.
    edestruct IHniT as [? IH1]. eapply H2. omega. eauto.
    edestruct IHniT as [? IH2]. eapply H3. omega. eauto.
    destruct b2.

    eexists. eapply T_AppVar. eauto. eauto.
    rewrite subst_open_commute1. eauto.
    eapply closed_subst. subst. rewrite map_length. rewrite app_length in *. simpl in *.
    eapply closed_upgrade_gh. eassumption. omega.
    subst. rewrite map_length. econstructor. eapply has_type_closed1. eauto.

    case_eq (beq_nat x2 0); intros E.

    eapply beq_nat_true in E. subst.
    rewrite subst_open_commute0b.
    eexists. eapply T_AppVar. eauto. eauto. eauto.
    rewrite map_length. rewrite <- subst_open_commute0b.
    eapply closed_subst. eapply closed_upgrade_gh. eassumption.
    rewrite app_length. simpl. omega.
    econstructor. eapply has_type_closed1. eauto.

    rewrite subst_open5.
    simpl in *. rewrite E in *.
    eexists. eapply T_AppVar. eauto. eauto. eauto.
    rewrite <- subst_open5. eapply closed_subst.
    subst. rewrite map_length. rewrite app_length in *. simpl in *. eassumption.
    subst. rewrite map_length. econstructor. eapply has_type_closed1. eauto.
    apply []. apply beq_nat_false. apply E. apply []. apply beq_nat_false. apply E.
  - Case "sub". subst.
    edestruct hastp_inv as [? [? HV]]; eauto.
    edestruct stp_subst_narrow_z. eapply H3. eapply HV.
    edestruct IHniT as [? IH]. eapply H2. omega. eauto.
    eexists. eapply T_Sub. eauto. eauto.
  - Case "dnil". subst. simpl.
    eexists. eapply D_Nil.
  - Case "dnone". subst. simpl.
    edestruct IHniD as [? IH]. eapply H2. omega. eauto.
    eexists. eapply D_None. eauto.
  - Case "mem". subst. simpl.
    edestruct IHniD as [? IH]. eapply H2. omega. eauto.
    eexists. eapply D_Mem. eauto. eapply closed_subst0. rewrite app_length in H3. rewrite map_length. eauto. eapply has_type_closed1. eauto. eauto.
    unfold substt. simpl. rewrite <- length_subst_dms. reflexivity.
  - Case "abs". subst. simpl.
    edestruct IHniD as [? IHD]. eapply H2. omega. eauto.
    edestruct IHniT with (GH:=T11::GH1) as [? HI] . eauto. omega. eauto.
    simpl in HI.
    eexists. eapply D_Abs. eapply IHD. eapply HI.
    rewrite map_length. rewrite app_length. simpl.
    rewrite subst_open. unfold substt. reflexivity.
    eapply closed_subst0. rewrite map_length. rewrite app_length in H5. simpl in H5. eauto. eauto. eapply has_type_closed1. eauto.
    eapply closed_subst0. rewrite map_length. rewrite app_length in H6. simpl in H6. eauto. eapply has_type_closed1. eauto. eauto.
    unfold substt. simpl. rewrite <- length_subst_dms. reflexivity.
Grab Existential Variables.
apply 0. apply 0.
Qed.

Lemma hastp_subst_z: forall G1 GH TX T x t n1 n2,
  has_type (GH++[TX]) G1 t T n2 ->
  has_type [] G1 (tvar true x) (substt x TX) n1 ->
  exists n3, has_type (map (substt x) GH) G1 (subst_tm x t) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_aux_z with (t:=t). eauto. eauto. eauto.
Qed.

Lemma hastp_subst: forall G1 GH TX T x t n1 n2,
  has_type (GH++[TX]) G1 t T n2 ->
  has_type [] G1 (tvar true x) TX n1 ->
  exists n3, has_type (map (substt x) GH) G1 (subst_tm x t) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_z with (t:=t). eauto.
  erewrite subst_closed_id. eauto. eapply has_type_closed in H0. eauto.
Qed.

Lemma dms_hastp_subst_z: forall G1 GH TX T x ds n1 n2,
  dms_has_type (GH++[TX]) G1 ds T n2 ->
  has_type [] G1 (tvar true x) (substt x TX) n1 ->
  exists n3, dms_has_type (map (substt x) GH) G1 (subst_dms x ds) (substt x T) n3.
Proof.
  intros. eapply hastp_subst_aux_z with (ds:=ds). eauto. eauto. eauto.
Qed.

Lemma dms_hastp_subst: forall G1 GH TX T x ds n1 n2,
  dms_has_type (GH++[TX]) G1 ds T n2 ->
  has_type [] G1 (tvar true x) TX n1 ->
  exists n3, dms_has_type (map (substt x) GH) G1 (subst_dms x ds) (substt x T) n3.
Proof.
  intros. eapply dms_hastp_subst_z with (ds:=ds). eauto.
  erewrite subst_closed_id. eauto. eapply has_type_closed in H0. eauto.
Qed.

Lemma dms_hastp_subst_1: forall G1 TX T x ds n1 n2,
  dms_has_type [TX] G1 ds T n2 ->
  has_type [] G1 (tvar true x) TX n1 ->
  exists n3, dms_has_type [] G1 (subst_dms x ds) (substt x T) n3.
Proof.
  intros. rewrite <- (app_nil_l [TX]) in H. 
  assert (E: [] = map (substt x) []) by reflexivity. rewrite E.
  eapply dms_hastp_subst; eauto.
Qed.

Lemma stp_subst_narrow: forall GH0 TX G1 T1 T2 x m n1 n2,
  stp (GH0 ++ [TX]) G1 T1 T2 n2 ->
  vtp m G1 x TX n1 ->
  stpd2 (map (substt x) GH0) G1 (substt x T1) (substt x T2).
Proof.
  intros. eapply stp_subst_narrow_z. eauto.
  erewrite subst_closed_id. eauto. eapply vtp_closed in H0. eauto.
Qed.

Lemma mix_dms_hastp: forall G1 S1 S2 T1 T2 ds1 ds2 n1 n2,
  dms_has_type [open 0 (TVar false 0) S1] G1 ds1 (open 0 (TVar false 0) T1) n1 ->
  dms_has_type [open 0 (TVar false 0) S2] G1 ds2 (open 0 (TVar false 0) T2) n2 ->
  exists n3,
    dms_has_type [TAnd (open 0 (TVar false 0) S1) (open 0 (TVar false 0) S2)] G1 
                 (override_dms ds1 ds2) (open 0 (TVar false 0) (override_rcd T1 T2)) n3.
Admitted.

Lemma step_unique: forall G G1 G2 t t1 t2,
  step G t G1 t1 ->
  step G t G2 t2 ->
  G1 = G2 /\ t1 = t2.
Proof.
  intros. generalize dependent t2. generalize dependent G2.
  induction H; intros ? ? H_other;
  inversion H_other; subst;
  (* transitivity *)
  repeat match goal with
    | E1: ?X = ?Y, E2: ?X = ?Z |- _ => assert (EE: Y = Z) by (
        transitivity X; [symmetry; assumption | assumption]
      ); inversion EE; clear EE E1 E2; subst
  end;
  subst; eauto;
  (* contradiction: vars don't step *)
  try match goal with
  | C: step _ (tvar _ _) _ _ |- _ => inversion C
  end;
  (* applying IH *)
  match goal with
  | IH: forall _ _, _ -> _ |- _ => edestruct IH; eauto; subst; eauto
  end.
Qed.

Theorem type_safety : forall G t T n1,
  has_type [] G t T n1 ->
  (exists x, t = tvar true x) \/
  (exists G' t' n2, step G t (G'++G) t' /\ has_type [] (G'++G) t' T n2).
Proof.
  intros.
  assert (closed (length ([]:tenv)) (length G) 0 T) as CL. eapply has_type_closed. eauto.
  remember [] as GH. remember t as tt. remember T as TT.
  revert T t HeqTT HeqGH Heqtt CL.
  induction H; intros.
  - Case "varc". eauto.
  - Case "vary". eauto.
  - Case "varz". subst GH. inversion H.
  - Case "pack". subst GH.
    eapply has_type_closed_b in H. destruct H. subst.
    left. eexists. reflexivity.
  - Case "unpack". subst GH.
    eapply has_type_closed_b in H. destruct H. subst.
    left. eexists. reflexivity.
  - Case "new". subst. right.
    assert (closed (length ([]:tenv)) (length G1) 0 (TCls S1 T1)) as ClCl. {
      eapply has_type_closed. eauto.
    }
    assert ((exists x, t1 = tvar true x) \/
            (exists G' t1' n2, step G1 t1 (G'++G1) t1' /\ has_type [] (G'++G1) t1' (TCls S1 T1) n2)
    ) as IH. {
      eapply IHhas_type; eauto.
    }
    destruct IH as [IH | IH].
    + SCase "step". destruct IH as [x IH]. subst.
      assert (exists m n1, vtp m G1 x (TCls S1 T1) n1). { eapply hastp_inv. eauto. }
      destruct H1 as [m [n11 H1]]. inversion H1. subst. simpl in *.
      assert (DmsN: exists n11, 
        dms_has_type [open 0 (TVar false 0) T1] (vobj (subst_dms (length G1) ds) :: G1)
                     ds (open 0 (TVar false 0) T1) n11). {
        eapply narrow_dms_has_type.
        - eapply stp_extend. apply H0.
        - eapply dms_has_type_extend. apply H5. 
      }
      destruct DmsN as [x11 DmsN].
      repeat eexists; rewrite <- app_cons1.
      * eapply ST_New. eassumption.
      * eapply T_VarPack.
        { eapply T_Vary.
          - simpl. rewrite beq_nat_true_eq. eauto.
          - apply DmsN.
          - eauto.
          - eauto.
          - eapply closed_subst.
            + eapply closed_open.
              * eapply closed_extend. eapply closed_upgrade_gh. eauto. omega.
              * simpl. econstructor. econstructor.
            + econstructor. simpl. omega.
        }
        { rewrite subst_open_commute0b. erewrite subst_closed_id. reflexivity. eauto. }
        { eapply closed_extend. simpl. eauto. }
    + SCase "cong".
      ev. repeat eexists. eapply ST_New1. eauto. eapply T_New. eauto. eapply stp_extend_mult. eauto.
  - Case "cls". subst. right. repeat eexists.
    + rewrite <- app_cons1. eapply ST_Cls.
    + eapply T_Varc.
      * simpl. rewrite beq_nat_true_eq. eauto.
      * eapply dms_has_type_extend. eauto.
      * eapply closed_extend. eauto.
      * eapply closed_extend. eauto.
  - Case "mix". subst.
    assert (IH1: (exists x : id, t1 = tvar true x) \/
                 (exists (G' : list vl) (t' : tm) (n2 : nat),
                   step G1 t1 (G' ++ G1) t' /\ has_type [] (G' ++ G1) t' (TCls S1 T1) n2)). {
      eapply IHhas_type1; eauto.
      eapply has_type_closed. eassumption.
    }
    assert (IH2: (exists x : id, t2 = tvar true x) \/
                 (exists (G' : list vl) (t' : tm) (n2 : nat),
                   step G1 t2 (G' ++ G1) t' /\ has_type [] (G' ++ G1) t' (TCls S2 T2) n2)). {
      eapply IHhas_type2; eauto.
      eapply has_type_closed. eassumption.
    }
    right.
    destruct IH1 as [IH1 | IH1].
    + SCase "t1-val".
      destruct IH2 as [IH2 | IH2].
      * SSCase "t2-val".
        ev. subst. apply hastp_inv in H. apply hastp_inv in H0.
        ev. inversion H. inversion H0. subst.
        destruct (mix_dms_hastp _ _ _ _ _ _ _ _ _ H4 H14) as [n4 C4].
        repeat eexists.
        { rewrite app_nil_l. eapply ST_Mix; eauto. }
        { eapply T_Cls; simpl.
          - eapply C4.
          - eauto.
          - apply closed_override_rcd; assumption. }
      * SSCase "t2-step".
        ev. subst. repeat eexists. eapply ST_Mix2. eauto. eapply T_Mix.
        { eapply has_type_extend_mult. eauto. }
        { eauto. }
    + SCase "t1-step".
      ev. subst. repeat eexists. eapply ST_Mix1. eauto. eapply T_Mix.
      { eauto. }
      { eapply has_type_extend_mult. eauto. }
  - Case "app". subst.
    assert (closed (length ([]:tenv)) (length G1) 0 (TFun l T1 T)) as TF. eapply has_type_closed. eauto.
    assert ((exists x : id, t2 = tvar true x) \/
                (exists (G' : venv) (t' : tm) n2,
                   step G1 t2 (G'++G1) t' /\ has_type [] (G'++G1) t' T1 n2)) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto.
    assert ((exists x : id, t1 = tvar true x) \/
                (exists (G' : venv) (t' : tm) n2,
                   step G1 t1 (G'++G1) t' /\ has_type [] (G'++G1) t' (TFun l T1 T) n2)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      destruct HX.
      * SSCase "arg-val".
        ev. ev. subst.
        assert (exists m n1, vtp m G1 x (TFun l T1 T) n1). eapply hastp_inv. eauto.
        assert (exists m n1, vtp m G1 x0 T1 n1). eapply hastp_inv. eauto.
        ev. inversion H2. subst.
        assert (vtpdd x1 G1 x0 T0). eapply vtp_widen. eauto. eauto. eauto. eauto. eauto.
        eu.
        assert (exists T, (exists n1, has_type [] G1 (tvar true x) T n1) /\ substt x T' = T) as A. eexists. split. eexists. eapply T_Vary. eauto. eauto. eauto. eauto. eapply closed_subst. eapply dms_has_type_closed in H10. eauto. econstructor. eapply index_max in H7. omega. reflexivity.
        destruct A as [Tx [[na A] EqTx]].
        assert (has_typed (map (substt x) [T1x]) G1 (subst_tm x tx) (substt x (open 0 (TVar false 1) T2x))) as HIx.
        eapply hastp_subst_z. eapply H13. rewrite EqTx. eapply A.
        eu. simpl in HIx.
        assert (has_typed (map (substt x0) []) G1 (subst_tm x0 (subst_tm x tx)) (substt x0 (substt x (open 0 (TVar false 1) T2x)))) as HIx0.
        eapply hastp_subst. rewrite app_nil_l. eapply HIx. simpl in H11. inversion H11. unfold substt. rewrite H9. eauto.
        eu. simpl in HIx0.
        assert ((substt x (open 0 (TVar false 1) T2x))=(open 0 (TVar false 0) (substt x T2x))) as EqT2x. {
          change 1 with (0+1). rewrite subst_open. reflexivity.
        }
        assert (has_typed [] G1 (subst_tm x0 t) (substt x0 (open 0 (TVar false 0) T2))) as HI. {
          inversion H11; subst. unfold substt in EqT2x. rewrite <- EqT2x. eauto.
        }
        eu. simpl in HI.
        edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H23. eauto.
        simpl in HI2.
        assert (substt x0 (open 0 (TVar false 0) T) = T) as EqT. {
          erewrite <- closed_no_open. erewrite subst_closed_id. reflexivity.
          eassumption. eassumption.
        }
        rewrite EqT in HI2.
        right. repeat eexists. rewrite app_nil_l. eapply ST_AppAbs. eauto. eauto.
        eapply T_Sub. eauto. eauto.
      * SSCase "arg_step".
        ev. subst.
        right. repeat eexists. eapply ST_App2. eauto. eapply T_App.
        eapply has_type_extend_mult. eauto. eauto.
        simpl in *. rewrite app_length. eapply closed_extend_mult. eassumption. omega.
    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply ST_App1. eauto. eapply T_App.
      eauto. eapply has_type_extend_mult. eauto.
      simpl in *. rewrite app_length. eapply closed_extend_mult. eassumption. omega.

  - Case "appvar". subst.
    assert (closed (length ([]:tenv)) (length G1) 0 (TFun l T1 T2)) as TF. eapply has_type_closed. eauto.
    assert ((exists x : id, tvar b2 x2 = tvar true x) \/
                (exists (G' : venv) (t' : tm) n2,
                   step G1 (tvar b2 x2) (G'++G1) t' /\ has_type [] (G'++G1) t' T1 n2)) as HX.
    eapply IHhas_type2. eauto. eauto. eauto. inversion TF. eauto.
    assert (b2 = true) as HXeq. {
      destruct HX as [[? HX] | Contra]. inversion HX. reflexivity.
      destruct Contra as [G' [t' [n' [Hstep Htyp]]]].
      inversion Hstep.
    }
    clear HX. subst b2.
    assert ((exists x : id, t1 = tvar true x) \/
                (exists (G' : venv) (t' : tm) n2,
                   step G1 t1 (G'++G1) t' /\ has_type [] (G'++G1) t' (TFun l T1 T2) n2)) as HF.
    eapply IHhas_type1. eauto. eauto. eauto. eauto.
    destruct HF.
    + SCase "fun-val".
      ev. ev. subst.
      assert (exists m n1, vtp m G1 x (TFun l T1 T2) n1). eapply hastp_inv. eauto.
      assert (exists m n1, vtp m G1 x2 T1 n1). eapply hastp_inv. eauto.
      ev. inversion H1. subst.
      assert (vtpdd x0 G1 x2 T0). eapply vtp_widen. eauto. eauto. eauto. eauto. eauto.
      eu.
      assert (exists T, (exists n1, has_type [] G1 (tvar true x) T n1) /\ substt x T' = T) as A. eexists. split. eexists. eapply T_Vary. eauto. eauto. eauto. eauto. eapply closed_subst. eapply dms_has_type_closed in H10. eauto. econstructor. eapply index_max in H7. omega. reflexivity.
      destruct A as [Tx [[na A] EqTx]].
      assert (has_typed (map (substt x) [T1x]) G1 (subst_tm x tx) (substt x (open 0 (TVar false 1) T2x))) as HIx.
      eapply hastp_subst_z. eapply H13. rewrite EqTx. eapply A.
      eu. simpl in HIx.
      assert (has_typed (map (substt x2) []) G1 (subst_tm x2 (subst_tm x tx)) (substt x2 (substt x (open 0 (TVar false 1) T2x)))) as HIx0.
      eapply hastp_subst. rewrite app_nil_l. eapply HIx. simpl in H11. inversion H11. unfold substt. rewrite H9. eauto.
      eu. simpl in HIx0.
      assert ((substt x (open 0 (TVar false 1) T2x))=(open 0 (TVar false 0) (substt x T2x))) as EqT2x. {
        change 1 with (0+1). rewrite subst_open. reflexivity.
      }
      assert (has_typed [] G1 (subst_tm x2 t) (substt x2 (open 0 (TVar false 0) T3))) as HI. {
        inversion H11; subst. unfold substt in EqT2x. rewrite <- EqT2x. eauto.
      }
      eu. simpl in HI.
      edestruct stp_subst_narrow as [? HI2]. rewrite app_nil_l. eapply H23. eauto.
      simpl in HI2.
      assert ((substt x2 (open 0 (TVar false 0) T2))=(open 0 (TVar true x2) T2)) as EqT2. {
        rewrite subst_open_commute0b. erewrite subst_closed_id. reflexivity.
        eassumption.
      }
      rewrite EqT2 in HI2.
      right. repeat eexists. rewrite app_nil_l. eapply ST_AppAbs. eauto. eauto.
      eapply T_Sub. eauto. eauto.
    + SCase "fun_step".
      ev. subst. right. repeat eexists. eapply ST_App1. eauto. eapply T_AppVar.
      eauto. eapply has_type_extend_mult. eauto. reflexivity.
      simpl in *. rewrite app_length. eapply closed_extend_mult. eassumption. omega.

  - Case "sub". subst.
    assert ((exists x : id, t0 = tvar true x) \/
               (exists (G' : venv) (t' : tm) n2,
                  step G1 t0 (G'++G1) t' /\ has_type [] (G'++G1) t' T1 n2)) as HH.
    eapply IHhas_type; eauto. change 0 with (length ([]:tenv)) at 1. eapply stpd2_closed1; eauto.
    destruct HH.
    + SCase "val".
      ev. subst. left. eexists. eauto.
    + SCase "step".
      ev. subst.
      right. repeat eexists. eauto. eapply T_Sub. eauto. eapply stp_extend_mult. eauto.
Qed.


End DOT.