(* Full safety for DOT *)

(* this version is based on dot12.v *)
(* based on that, it adds multiple labels for functions *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.

Module FSUB.

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TBot   : ty
  | TTop   : ty
  | TFun   : id -> ty -> ty -> ty
  | TMem   : ty -> ty -> ty
  | TSel   : id -> ty
  | TSelH  : id -> ty
  | TSelB  : id -> ty
  | TAll   : ty -> ty -> ty
  | TBind  : ty -> ty
  | TAnd   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : id -> tm
  | ttyp   : ty -> tm
  | tapp   : tm -> id -> tm -> tm (* \o.m(x) *)
  | tabs   : id -> list (id * (id * tm)) -> tm (* \o {val m = \x.y} *)
  | ttapp  : tm -> tm -> tm (* f[X] *)
  | ttabs  : id -> ty -> tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
| vty   : list (id*vl) -> ty -> vl
| vbool : bool -> vl
| vabs  : list (id*vl) -> id -> list (id * (id * tm)) -> vl
| vtabs : list (id*vl) -> id -> ty -> tm -> vl
.


Definition tenv := list (id*ty).
Definition venv := list (id*vl).
Definition aenv := list (id*(venv*ty)).

Hint Unfold venv.
Hint Unfold tenv.

Fixpoint fresh {X: Type} (l : list (id * X)): nat :=
  match l with
    | [] => 0
    | (n',a)::l' => 1 + n'
  end.

Fixpoint index {X : Type} (n : id) (l : list (id * X)) : option X :=
  match l with
    | [] => None
    | (n',a) :: l'  =>
      if le_lt_dec (fresh l') n' then
        if (beq_nat n n') then Some a else index n l'
      else None
  end.

Fixpoint indexr {X : Type} (n : id) (l : list (id * X)) : option X :=
  match l with
    | [] => None
    | (n',a) :: l'  => (* DeBrujin *)
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.


(*
Fixpoint update {X : Type} (n : nat) (x: X)
               (l : list X) { struct l }: list X :=
  match l with
    | [] => []
    | a :: l'  => if beq_nat n (length l') then x::l' else a :: update n x l'
  end.
*)


(* LOCALLY NAMELESS *)

Inductive closed_rec: nat -> nat -> ty -> Prop :=
| cl_top: forall k l,
    closed_rec k l TTop
| cl_bot: forall k l,
    closed_rec k l TBot
| cl_bool: forall k l,
    closed_rec k l TBool
| cl_fun: forall k l m T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TFun m T1 T2)
| cl_mem: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TMem T1 T2)
| cl_all: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec (S k) l T2 ->
    closed_rec k l (TAll T1 T2)
| cl_bind: forall k l T2,
    closed_rec (S k) l T2 ->
    closed_rec k l (TBind T2)
| cl_sel: forall k l x,
    closed_rec k l (TSel x)
| cl_and: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TAnd T1 T2)
| cl_selh: forall k l x,
    l > x ->
    closed_rec k l (TSelH x)
| cl_selb: forall k l i,
    k > i ->
    closed_rec k l (TSelB i)
.

Hint Constructors closed_rec.

Definition closed j l T := closed_rec j l T.


Fixpoint open_rec (k: nat) (u: ty) (T: ty) { struct T }: ty :=
  match T with
    | TSel x      => TSel x (* free var remains free. functional, so we can't check for conflict *)
    | TSelH i     => TSelH i (*if beq_nat k i then u else TSelH i *)
    | TSelB i     => if beq_nat k i then u else TSelB i
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TBind T2    => TBind (open_rec (S k) u T2)
    | TTop        => TTop
    | TBot        => TBot
    | TBool       => TBool
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
    | TFun m T1 T2  => TFun m (open_rec k u T1) (open_rec k u T2)
    | TAnd T1 T2  => TAnd (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

(* sanity check *)
Example open_ex1: open (TSel 9) (TAll TBool (TFun 0 (TSelB 1) (TSelB 0))) =
                      (TAll TBool (TFun 0 (TSel 9) (TSelB 0))).
Proof. compute. eauto. Qed.


Fixpoint subst (U : ty) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TBool        => TBool
    | TMem T1 T2   => TMem (subst U T1) (subst U T2)
    | TFun m T1 T2   => TFun m (subst U T1) (subst U T2)
    | TSelB i      => TSelB i
    | TSel i       => TSel i
    | TSelH i      => if beq_nat i 0 then U else TSelH (i-1)
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TBind T2     => TBind (subst U T2)
    | TAnd T1 T2   => TAnd (subst U T1) (subst U T2)
  end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TBot         => True
    | TBool        => True
    | TMem T1 T2   => nosubst T1 /\ nosubst T2
    | TFun m T1 T2   => nosubst T1 /\ nosubst T2
    | TSelB i      => True
    | TSel i       => True
    | TSelH i      => i <> 0
    | TAll T1 T2   => nosubst T1 /\ nosubst T2
    | TBind T2     => nosubst T2
    | TAnd T1 T2   => nosubst T1 /\ nosubst T2
  end.


Hint Unfold open.
Hint Unfold closed.


Inductive stp: tenv -> tenv -> ty -> ty -> Prop :=
| stp_topx: forall G1 GH,
    stp G1 GH TTop TTop
| stp_botx: forall G1 GH,
    stp G1 GH TBot TBot
| stp_top: forall G1 GH T1,
    stp G1 GH T1 T1 -> (* regularity *)
    stp G1 GH T1 TTop
| stp_bot: forall G1 GH T2,
    stp G1 GH T2 T2 -> (* regularity *)
    stp G1 GH TBot T2
| stp_bool: forall G1 GH,
    stp G1 GH TBool TBool
| stp_fun: forall G1 GH m T1 T2 T3 T4,
    stp G1 GH T3 T1 ->
    stp G1 GH T2 T4 ->
    stp G1 GH (TFun m T1 T2) (TFun m T3 T4)
| stp_mem: forall G1 GH T1 T2 T3 T4,
    stp G1 GH T3 T1 ->
    stp G1 GH T2 T4 ->
    stp G1 GH (TMem T1 T2) (TMem T3 T4)
| stp_sel1: forall G1 GH TX T2 x,
    index x G1 = Some TX ->
    closed 0 0 TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH T2 T2 -> (* regularity of stp2 *)
    stp G1 GH (TSel x) T2
| stp_sel2: forall G1 GH TX T1 x,
    index x G1 = Some TX ->
    closed 0 0 TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 T1 -> (* regularity of stp2 *)
    stp G1 GH T1 (TSel x)
| stp_selb1: forall G1 GH TX T2 x,
    index x G1 = Some TX ->
    stp G1 [] TX (TBind (TMem TBot T2)) ->   (* Note GH = [] *)
    stp G1 GH (open (TSel x) T2) (open (TSel x) T2) -> (* regularity *)
    stp G1 GH (TSel x) (open (TSel x) T2)
| stp_selb2: forall G1 GH TX T1 x,
    index x G1 = Some TX ->
    stp G1 [] TX (TBind (TMem T1 TTop)) ->   (* Note GH = [] *)
    stp G1 GH (open (TSel x) T1) (open (TSel x) T1) -> (* regularity *)
    stp G1 GH (open (TSel x) T1) (TSel x)
| stp_selx: forall G1 GH TX x,
    index x G1 = Some TX ->
    stp G1 GH (TSel x) (TSel x)
| stp_sela1: forall G1 GH TX T2 x,
    indexr x GH = Some TX ->
    closed 0 (S x) TX ->
    stp G1 GH TX (TMem TBot T2) ->   (* not using self name for now *)
    stp G1 GH T2 T2 -> (* regularity of stp2 *)
    stp G1 GH (TSelH x) T2
| stp_sela2: forall G1 GH TX T1 x,
    indexr x GH = Some TX ->
    closed 0 (S x) TX ->
    stp G1 GH TX (TMem T1 TTop) ->   (* not using self name for now *)
    stp G1 GH T1 T1 -> (* regularity of stp2 *)
    stp G1 GH T1 (TSelH x)
| stp_selab1: forall G1 GH GU GL TX T2 T2' x,
    indexr x GH = Some TX ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem TBot T2)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp G1 GL TX (TBind (TMem TBot T2)) ->
    T2' = (open (TSelH x) T2) ->
    stp G1 GH T2' T2' -> (* regularity *)
    stp G1 GH (TSelH x) T2'
| stp_selab2: forall G1 GH GU GL TX T1 T1' x,
    indexr x GH = Some TX ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem T1 TTop)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp G1 GL TX (TBind (TMem T1 TTop)) ->
    T1' = (open (TSelH x) T1) ->
    stp G1 GH T1' T1' -> (* regularity *)
    stp G1 GH T1' (TSelH x)
| stp_selax: forall G1 GH TX x,
    indexr x GH = Some TX  ->
    stp G1 GH (TSelH x) (TSelH x)
| stp_all: forall G1 GH T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) T2 -> (* must not accidentally bind x *)
    closed 1 (length GH) T4 ->
    stp G1 ((0,T1)::GH) (open (TSelH x) T2) (open (TSelH x) T2) -> (* regularity *)
    stp G1 ((0,T3)::GH) (open (TSelH x) T2) (open (TSelH x) T4) ->
    stp G1 GH (TAll T1 T2) (TAll T3 T4)
| stp_bindx: forall G1 GH T1 T2 x,
    x = length GH ->
    closed 1 (length GH) T1 -> (* must not accidentally bind x *)
    closed 1 (length GH) T2 ->
    stp G1 ((0,open (TSelH x) T2)::GH) (open (TSelH x) T2) (open (TSelH x) T2) -> (* regularity *)
    stp G1 ((0,open (TSelH x) T1)::GH) (open (TSelH x) T1) (open (TSelH x) T2) ->
    stp G1 GH (TBind T1) (TBind T2)
| stp_and11: forall G GH T1 T2 T,
    stp G GH T1 T ->
    stp G GH T2 T2 -> (* regularity *)
    stp G GH (TAnd T1 T2) T
| stp_and12: forall G GH T1 T2 T,
    stp G GH T2 T ->
    stp G GH T1 T1 -> (* regularity *)
    stp G GH (TAnd T1 T2) T
| stp_and2: forall G GH T1 T2 T,
    stp G GH T T1 ->
    stp G GH T T2 ->
    stp G GH T (TAnd T1 T2)
.


(*
with path_type: tenv -> tenv -> id -> ty -> Prop :=
| pt_var: forall G1 GH TX x,
    index x G1 = Some TX ->
    path_type G1 GH x TX
| pt_sub: forall G1 GH TX x,
    path_type has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2

with pathH_type: tenv -> tenv -> id -> ty -> Prop :=
| pth_var: forall G1 GH TX T x,
    indexr x GH = Some TX ->
    stp G1 GH TX T ->
    pathH_type G1 GH x T
*)


Hint Constructors stp.


Function tand (t1: ty) (t2: ty) :=
  match t2 with
    | TTop => t1
    | _ => TAnd t1 t2
  end.

(* TODO *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           index x env = Some T1 ->
           stp env [] T1 T1 ->
           has_type env (tvar x) T1
| t_var_pack: forall x env T1,
           has_type env (tvar x) (open (TSel x) T1) ->
           stp env [] (TBind T1) (TBind T1) ->
           has_type env (tvar x) (TBind T1)
| t_var_unpack: forall x env T1,
           has_type env (tvar x) (TBind T1) ->
           stp env [] (open (TSel x) T1) (open (TSel x) T1) ->
           has_type env (tvar x) (open (TSel x) T1)
| t_typ: forall env x T1 T1X,
           fresh env = x ->
           open (TSel x) T1 = T1X ->
           stp ((x,TMem T1X T1X)::env) [] T1X T1X ->
           stp env [] (TBind (TMem T1 T1)) (TBind (TMem T1 T1)) ->
           has_type env (ttyp T1) (TBind (TMem T1 T1))
| t_app: forall env f l x T1 T2,
           has_type env f (TFun l T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f l x) T2
| t_abs: forall env f ds T,
           dcs_has_type ((f,T)::env) ds T ->
           fresh env <= f ->
           has_type env (tabs f ds) T
| t_tapp: forall env f x T11 T12,
           has_type env f (TAll T11 T12) ->
           has_type env x T11 ->
           stp env [] T12 T12 ->
           has_type env (ttapp f x) T12
(*
NOTE: both the POPLmark paper and Cardelli's paper use this rule:
Does it make a difference? It seems like we can always widen f?

| t_tapp: forall env f T2 T11 T12 ,
           has_type env f (TAll T11 T12) ->
           stp env T2 T11 ->
           has_type env (ttapp f T2) (open T2 T12)

*)
| t_tabs: forall env x y T1 T2,
           has_type ((x,T1)::env) y (open (TSel x) T2) ->
           stp env [] (TAll T1 T2) (TAll T1 T2) ->
           fresh env = x ->
           has_type env (ttabs x T1 y) (TAll T1 T2)

| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2

with dcs_has_type: tenv -> list (id * (id * tm)) -> ty -> Prop :=
| dt_nil: forall env,
            dcs_has_type env nil TTop
| dt_fun: forall env x y m T1 T2 dcs TS T,
            has_type ((x,T1)::env) y T2 ->
            dcs_has_type env dcs TS ->
            fresh env = x ->
            m = length dcs ->
            T = tand (TFun m T1 T2) TS ->
            dcs_has_type env ((m, (x, y))::dcs) T
.


Definition base (v:vl): venv :=
  match v with
    | vty GX _ => GX
    | vbool _ => nil
    | vabs GX _ _ => GX
    | vtabs GX _ _ _ => GX
  end.


Definition MAX := 2.

Inductive stp2: nat -> bool -> venv -> ty -> venv -> ty -> list (id*(venv*ty)) -> nat -> Prop :=
| stp2_topx: forall m G1 G2 GH n1,
    stp2 m true G1 TTop G2 TTop GH (S n1)
| stp2_botx: forall m G1 G2 GH n1,
    stp2 m true G1 TBot G2 TBot GH (S n1)
| stp2_top: forall m G1 G2 GH T n1,
    stp2 m true G1 T G1 T GH n1 -> (* regularity *)
    stp2 m true G1 T G2 TTop GH (S n1)
| stp2_bot: forall m G1 G2 GH T n1,
    stp2 m true G2 T G2 T GH n1 -> (* regularity *)
    stp2 m true G1 TBot G2 T GH (S n1)
| stp2_bool: forall m G1 G2 GH n1,
    stp2 m true G1 TBool G2 TBool GH (S n1)
| stp2_fun: forall m G1 G2 l T1 T2 T3 T4 GH n1 n2,
    stp2 MAX false G2 T3 G1 T1 GH n1 ->
    stp2 MAX false G1 T2 G2 T4 GH n2 ->
    stp2 m true G1 (TFun l T1 T2) G2 (TFun l T3 T4) GH (S (n1+n2))
| stp2_mem: forall G1 G2 T1 T2 T3 T4 GH n1 n2,
    stp2 0 false G2 T3 G1 T1 GH n1 ->
    stp2 0 true G1 T2 G2 T4 GH n2 ->
    stp2 0 true G1 (TMem T1 T2) G2 (TMem T3 T4) GH (S (n1+n2))

| stp2_mem2: forall m G1 G2 T1 T2 T3 T4 GH n1 n2,
    stp2 (S m) false G2 T3 G1 T1 GH n1 ->
    stp2 (S m) false G1 T2 G2 T4 GH n2 ->
    stp2 (S m) true G1 (TMem T1 T2) G2 (TMem T3 T4) GH (S (n1+n2))


(* strong version, with precise/invertible bounds *)
| stp2_strong_sel1: forall G1 G2 GX TX x T2 GH GX' TX' n1 n2 nv,
    index x G1 = Some (vty GX TX) ->
    val_type GX' (vty GX TX) TX' nv -> (* for downgrade *)
    stp2 0 false GX' TX' G2 (TMem TBot T2) GH n2 -> (* for downgrade *)
    closed 1 0 TX ->
    stp2 0 true ((fresh GX, vty GX TX)::GX) (open (TSel (fresh GX)) TX) G2 T2 GH n1 ->
    stp2 0 true G1 (TSel x) G2 T2 GH (S (n1+n2))

| stp2_strong_sel2: forall G1 G2 GX TX x T1 GH GX' TX' n1 n2 nv,
    index x G2 = Some (vty GX TX) ->
    val_type GX' (vty GX TX) TX' nv -> (* for downgrade *)
    stp2 0 false GX' TX' G1 (TMem T1 TTop) GH n2 -> (* for downgrade *)
    closed 1 0 TX ->
    stp2 0 false G1 T1 ((fresh GX, vty GX TX)::GX) (open (TSel (fresh GX)) TX) GH n1 ->
    stp2 0 true G1 T1 G2 (TSel x) GH (S (n1+n2))

| stp2_strong_selx: forall G1 G2 v x1 x2 GH n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 0 true G1 (TSel x1) G2 (TSel x2) GH n1


(* existing object, but imprecise type *)
| stp2_sel1: forall m G1 G2 GX TX x T2 GH n1 n2 v nv,
    index x G1 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stp2 (S m) false GX TX G2 (TMem TBot T2) GH n1 ->
    stp2 (S m) true G2 T2 G2 T2 GH n2 -> (* regularity *)
    stp2 (S m) true G1 (TSel x) G2 T2 GH (S (n1+n2))

| stp2_selb1: forall m G1 G2 GX TX x x' T2 GH n1 n2 v nv,
    index x G1 = Some v -> (index x' G2 = Some v \/ closed 0 0 T2) ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stp2 (S (S m)) false GX TX G2 (TBind (TMem TBot T2)) [] n1 -> (* Note GH = [] *)
    stp2 (S (S m)) true G2 (open (TSel x') T2) G2 (open (TSel x') T2) GH n2 -> (* regularity *)
    stp2 (S (S m)) true G1 (TSel x) G2 (open (TSel x') T2) GH (S (n1+n2))


| stp2_sel2: forall m G1 G2 GX TX x T1 GH n1 n2 v nv,
    index x G2 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stp2 (S m) false GX TX G1 (TMem T1 TTop) GH n1 ->
    stp2 (S m) true G1 T1 G1 T1 GH n2 -> (* regularity *)
    stp2 (S m) true G1 T1 G2 (TSel x) GH (S (n1+n2))

| stp2_selb2: forall m G1 G2 GX TX x x' T1 GH n1 n2 v nv,
    index x G2 = Some v -> (index x' G1 = Some v \/ closed 0 0 T1) ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stp2 (S (S m)) false GX TX G1 (TBind (TMem T1 TTop)) [] n1 -> (* Note GH = [] *)
    stp2 (S (S m)) true G1 (open (TSel x') T1) G1 (open (TSel x') T1) GH n2 -> (* regularity *)
    stp2 (S (S m)) true G1 (open (TSel x') T1) G2 (TSel x) GH (S (n1+n2))

| stp2_selx: forall m G1 G2 v x1 x2 GH n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 (S m) true G1 (TSel x1) G2 (TSel x2) GH (S n1)

(* hypothetical object *)
| stp2_sela1: forall m G1 G2 GX TX x T2 GH n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    stp2 (S m) false GX TX G2 (TMem TBot T2) GH n1 ->
    stp2 (S m) true G2 T2 G2 T2 GH n2 -> (* regularity *)
    stp2 (S m) true G1 (TSelH x) G2 T2 GH (S (n1+n2))

| stp2_selab1: forall m G1 G2 GX TX x T2 T2' GH GU GL n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem TBot T2)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp2 (S m) false GX TX G2 (TBind (TMem TBot T2)) GL n1 ->
    T2' = (open (TSelH x) T2) ->
    stp2 (S m) true G2 T2' G2 T2' GH n2 -> (* regularity *)
    stp2 (S m) true G1 (TSelH x) G2 T2' GH (S (n1+n2))

| stp2_selab2: forall m G1 G2 GX TX x T1 T1' GH GU GL n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem T1 TTop)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp2 (S m) false GX TX G1 (TBind (TMem T1 TTop)) GL n1 ->
    T1' = (open (TSelH x) T1) ->
    stp2 (S m) true G1 T1' G1 T1' GH n2 -> (* regularity *)
    stp2 (S m) true G1 T1' G2 (TSelH x) GH (S (n1+n2))

| stp2_sela2: forall m G1 G2 GX TX x T1 GH n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    stp2 (S m) false GX TX G1 (TMem T1 TTop) GH n1 ->
    stp2 (S m) true G1 T1 G1 T1 GH n2 -> (* regularity *)
    stp2 (S m) true G1 T1 G2 (TSelH x) GH (S (n1+n2))


| stp2_selax: forall m G1 G2 GX TX x GH n1,
    indexr x GH = Some (GX, TX) ->
    stp2 (S m) true G1 (TSelH x) G2 (TSelH x) GH (S n1)


| stp2_all: forall m G1 G2 T1 T2 T3 T4 GH n1 n1' n2,
    stp2 MAX false G2 T3 G1 T1 GH n1 ->
    closed 1 (length GH) T2 -> (* must not accidentally bind x *)
    closed 1 (length GH) T4 ->
    stp2 MAX false G1 (open (TSelH (length GH)) T2) G1 (open (TSelH (length GH)) T2) ((0,(G1, T1))::GH) n1' -> (* regularity *)
    stp2 MAX false G1 (open (TSelH (length GH)) T2) G2 (open (TSelH (length GH)) T4) ((0,(G2, T3))::GH) n2 ->
    stp2 m true G1 (TAll T1 T2) G2 (TAll T3 T4) GH (S (n1+n1'+n2))

| stp2_bind: forall G1 G2 T1 T2 GH n1 n2,
    closed 1 (length GH) T1 -> (* must not accidentally bind x *)
    closed 1 (length GH) T2 ->
    stp2 1 false G2 (open (TSelH (length GH)) T2) G2 (open (TSelH (length GH)) T2) ((0,(G2, open (TSelH (length GH)) T2))::GH) n2 -> (* regularity *)
    stp2 1 false G1 (open (TSelH (length GH)) T1) G2 (open (TSelH (length GH)) T2) ((0,(G1, open (TSelH (length GH)) T1))::GH) n1 ->
    stp2 0 true G1 (TBind T1) G2 (TBind T2) GH (S (n1+n2))

| stp2_bindb: forall m G1 G2 T1 T2 GH n1 n2,
    closed 1 (length GH) T1 -> (* must not accidentally bind x *)
    closed 1 (length GH) T2 ->
    stp2 (S m) false G2 (open (TSelH (length GH)) T2) G2 (open (TSelH (length GH)) T2) ((0,(G2, open (TSelH (length GH)) T2))::GH) n2 -> (* regularity *)
    stp2 (S m) false G1 (open (TSelH (length GH)) T1) G2 (open (TSelH (length GH)) T2) ((0,(G1, open (TSelH (length GH)) T1))::GH) n1 ->
    stp2 (S m) true G1 (TBind T1) G2 (TBind T2) GH (S (n1+n2))

| stp2_and11: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m true G1 T1 G2 T GH n1 ->
    stp2 m true G1 T2 G1 T2 GH n2 -> (* regularity *)
    stp2 m true G1 (TAnd T1 T2) G2 T GH (S (n1+n2))
| stp2_and12: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m true G1 T2 G2 T GH n1 ->
    stp2 m true G1 T1 G1 T1 GH n2 -> (* regularity *)
    stp2 m true G1 (TAnd T1 T2) G2 T GH (S (n1+n2))
| stp2_and2: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m false G1 T G2 T1 GH n1 ->
    stp2 m false G1 T G2 T2 GH n2 ->
    stp2 m true G1 T G2 (TAnd T1 T2) GH (S (n1+n2))

| stp2_wrapf: forall m G1 G2 T1 T2 GH n1,
    stp2 m true G1 T1 G2 T2 GH n1 ->
    stp2 m false G1 T1 G2 T2 GH (S n1)
| stp2_transf: forall m G1 G2 G3 T1 T2 T3 GH n1 n2,
    stp2 m true G1 T1 G2 T2 GH n1 ->
    stp2 m false G2 T2 G3 T3 GH n2 ->
    stp2 m false G1 T1 G3 T3 GH (S (n1+n2))



with wf_env : venv -> tenv -> Prop :=
| wfe_nil : wf_env nil nil
| wfe_cons : forall n v t vs ts nv,
    val_type ((n,v)::vs) v t nv ->
    wf_env vs ts ->
    wf_env (cons (n,v) vs) (cons (n,t) ts)

with val_type : venv -> vl -> ty -> nat -> Prop :=
| v_ty: forall env venv tenv  T1 T1X TE,
    wf_env venv tenv -> (* T1 wf in tenv ? *)
    open (TSel (fresh venv)) T1 = T1X ->
    (exists n, stp2 0 true ((fresh venv, vty venv T1)::venv) (TMem T1X T1X) env TE [] n)->
    val_type env (vty venv T1) TE 1
| v_bool: forall venv b TE,
    (exists n, stp2 0 true [] TBool venv TE [] n) ->
    val_type venv (vbool b) TE 1
| v_abs: forall env venv tenv f ds T TE,
    wf_env venv tenv ->
    dcs_has_type ((f,T)::tenv) ds T ->
    fresh venv <= f ->
    (exists n, stp2 0 true venv T env TE [] n)->
    val_type env (vabs venv f ds) TE 1
| v_tabs: forall env venv tenv x y T1 T2 TE,
    wf_env venv tenv ->
    has_type ((x,T1)::tenv) y (open (TSel x) T2) ->
    fresh venv = x ->
    (exists n, stp2 0 true venv (TAll T1 T2) env TE [] n) ->
    val_type env (vtabs venv x T1 y) TE 1
| v_pack: forall venv venv3 x v T T2 T3 n,
    index x venv = Some v ->
    val_type venv v T n ->
    open (TSel x) T2 = T ->
    (exists n, stp2 0 true venv (TBind T2) venv3 T3 [] n) ->
    val_type venv3 v T3 (S n)
.


Inductive wf_envh : venv -> aenv -> tenv -> Prop :=
| wfeh_nil : forall vvs, wf_envh vvs nil nil
| wfeh_cons : forall n t vs vvs ts,
    wf_envh vvs vs ts ->
    wf_envh vvs (cons (n,(vvs,t)) vs) (cons (n,t) ts)
.

Inductive valh_type : venv -> aenv -> (venv*ty) -> ty -> Prop :=
| v_tya: forall aenv venv T1,
    valh_type venv aenv (venv, T1) T1
.



Definition stpd2 b G1 T1 G2 T2 GH := exists n, stp2 MAX b G1 T1 G2 T2 GH n.
Definition atpd2 b G1 T1 G2 T2 GH := exists n, stp2 1 b G1 T1 G2 T2 GH n.
Definition sstpd2 b G1 T1 G2 T2 GH := exists n, stp2 0 b G1 T1 G2 T2 GH n.

Definition valtpd G v T := exists n, val_type G v T n.




Ltac ep := match goal with
             | [ |- stp2 ?M1 ?M2 ?G1 ?T1 ?G2 ?T2 ?GH ?N ] => assert (exists (x:nat), stp2 M1 M2 G1 T1 G2 T2 GH x) as EEX
           end.

Ltac eu := match goal with
             | H: stpd2 _ _ _ _ _ _ |- _ => destruct H as [? H]
             | H: atpd2 _ _ _ _ _ _ |- _ => destruct H as [? H]
             | H: sstpd2 _ _ _ _ _ _ |- _ => destruct H as [? H]
(*             | H: exists n: nat ,  _ |- _  =>
               destruct H as [e P] *)
           end.

Hint Constructors stp2.
Hint Unfold stpd2.

Lemma stpd2_topx: forall G1 G2 GH,
    stpd2 true G1 TTop G2 TTop GH.
Proof. intros. repeat exists (S 0). eauto. Qed.
Lemma stpd2_botx: forall G1 G2 GH,
    stpd2 true G1 TBot G2 TBot GH.
Proof. intros. repeat exists (S 0). eauto. Qed.
Lemma stpd2_top: forall G1 G2 GH T,
    stpd2 true G1 T G1 T GH ->
    stpd2 true G1 T G2 TTop GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_bot: forall G1 G2 GH T,
    stpd2 true G2 T G2 T GH ->
    stpd2 true G1 TBot G2 T GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_bool: forall G1 G2 GH,
    stpd2 true G1 TBool G2 TBool GH.
Proof. intros. repeat exists (S 0). eauto. Qed.
Lemma stpd2_fun: forall G1 G2 GH l T11 T12 T21 T22,
    stpd2 false G2 T21 G1 T11 GH ->
    stpd2 false G1 T12 G2 T22 GH ->
    stpd2 true G1 (TFun l T11 T12) G2 (TFun l T21 T22) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_mem: forall G1 G2 GH T11 T12 T21 T22,
    stpd2 false G2 T21 G1 T11 GH ->
    stpd2 false G1 T12 G2 T22 GH ->
    stpd2 true G1 (TMem T11 T12) G2 (TMem T21 T22) GH.
Proof. intros. repeat eu. eauto. unfold stpd2. eexists. eapply stp2_mem2; eauto. Qed.

Lemma stpd2_sel1: forall G1 G2 GX TX x T2 GH v nv,
    index x G1 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stpd2 false GX TX G2 (TMem TBot T2) GH ->
    stpd2 true G2 T2 G2 T2 GH ->
    stpd2 true G1 (TSel x) G2 T2 GH.
Proof. intros. repeat eu. eexists. eapply stp2_sel1; eauto. Qed.

Lemma stpd2_selb1: forall G1 G2 GX TX x x' T2 GH v nv,
    index x G1 = Some v -> (index x' G2 = Some v \/ closed 0 0 T2) ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stpd2 false GX TX G2 (TBind (TMem TBot T2)) [] -> (* Note GH = [] *)
    stpd2 true G2 (open (TSel x') T2) G2 (open (TSel x') T2) GH ->
    stpd2 true G1 (TSel x) G2 (open (TSel x') T2) GH.
Proof. intros. repeat eu. eexists. eapply stp2_selb1; eauto. Qed.

Lemma stpd2_sel2: forall G1 G2 GX TX x T1 GH v nv,
    index x G2 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stpd2 false GX TX G1 (TMem T1 TTop) GH ->
    stpd2 true G1 T1 G1 T1 GH ->
    stpd2 true G1 T1 G2 (TSel x) GH.
Proof. intros. repeat eu. eexists. eapply stp2_sel2; eauto. Qed.

Lemma stpd2_selb2: forall G1 G2 GX TX x x' T1 GH v nv,
    index x G2 = Some v -> (index x' G1 = Some v \/ closed 0 0 T1) ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stpd2 false GX TX G1 (TBind (TMem T1 TTop)) [] -> (* Note GH = [] *)
    stpd2 true G1 (open (TSel x') T1) G1 (open (TSel x') T1) GH ->
    stpd2 true G1 (open (TSel x') T1) G2 (TSel x) GH.
Proof. intros. repeat eu. eexists. eapply stp2_selb2; eauto. Qed.

Lemma stpd2_selx: forall G1 G2 x1 x2 GH v,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stpd2 true G1 (TSel x1) G2 (TSel x2) GH.
Proof. intros. eauto. exists (S 0). eapply stp2_selx; eauto. Qed.

Lemma stpd2_selab1: forall G1 G2 GX TX x T2 GH GU GL,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem TBot T2)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stpd2 false GX TX G2 (TBind (TMem TBot T2)) GL ->
    stpd2 true G2 (open (TSelH x) T2) G2 (open (TSelH x) T2) GH ->
    stpd2 true G1 (TSelH x) G2 (open (TSelH x) T2) GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_selab1; eauto. Qed.

Lemma stpd2_selab2: forall G1 G2 GX TX x T1 T1' GH GU GL,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem T1 TTop)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stpd2 false GX TX G1 (TBind (TMem T1 TTop)) GL ->
    T1' = (open (TSelH x) T1) ->
    stpd2 true G1 T1' G1 T1' GH ->
    stpd2 true G1 T1' G2 (TSelH x) GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_selab2; eauto. Qed.

Lemma stpd2_sela1: forall G1 G2 GX TX x T2 GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    stpd2 false GX TX G2 (TMem TBot T2) GH ->
    stpd2 true G2 T2 G2 T2 GH ->
    stpd2 true G1 (TSelH x) G2 T2 GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_sela1; eauto. Qed.

Lemma stpd2_sela2: forall G1 G2 GX TX x T1 GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    stpd2 false GX TX G1 (TMem T1 TTop) GH ->
    stpd2 true G1 T1 G1 T1 GH ->
    stpd2 true G1 T1 G2 (TSelH x) GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_sela2; eauto. Qed.


Lemma stpd2_selax: forall G1 G2 GX TX x GH,
    indexr x GH = Some (GX, TX) ->
    stpd2 true G1 (TSelH x) G2 (TSelH x) GH.
Proof. intros. exists (S 0). eauto. eapply stp2_selax; eauto. Qed.


Lemma stpd2_all: forall G1 G2 T1 T2 T3 T4 GH,
    stpd2 false G2 T3 G1 T1 GH ->
    closed 1 (length GH) T2 ->
    closed 1 (length GH) T4 ->
    stpd2 false G1 (open (TSelH (length GH)) T2) G1 (open (TSelH (length GH)) T2) ((0,(G1, T1))::GH) ->
    stpd2 false G1 (open (TSelH (length GH)) T2) G2 (open (TSelH (length GH)) T4) ((0,(G2, T3))::GH) ->
    stpd2 true G1 (TAll T1 T2) G2 (TAll T3 T4) GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_bind: forall G1 G2 T1 T2 GH,
    closed 1 (length GH) T1 ->
    closed 1 (length GH) T2 ->
    stpd2 false G2 (open (TSelH (length GH)) T2) G2 (open (TSelH (length GH)) T2) ((0,(G2, open (TSelH (length GH)) T2))::GH) ->
    stpd2 false G1 (open (TSelH (length GH)) T1) G2 (open (TSelH (length GH)) T2) ((0,(G1, open (TSelH (length GH)) T1))::GH) ->
    stpd2 true G1 (TBind T1) G2 (TBind T2) GH.
Proof. intros. repeat eu. eauto. unfold stpd2. eexists. eapply stp2_bindb; eauto. Qed.

Lemma stpd2_and11: forall G1 G2 GH T1 T2 T,
    stpd2 true G1 T1 G2 T GH ->
    stpd2 true G1 T2 G1 T2 GH ->
    stpd2 true G1 (TAnd T1 T2) G2 T GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_and12: forall G1 G2 GH T1 T2 T,
    stpd2 true G1 T2 G2 T GH ->
    stpd2 true G1 T1 G1 T1 GH ->
    stpd2 true G1 (TAnd T1 T2) G2 T GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_and2: forall G1 G2 GH T1 T2 T,
    stpd2 false G1 T G2 T1 GH ->
    stpd2 false G1 T G2 T2 GH ->
    stpd2 true G1 T G2 (TAnd T1 T2) GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_wrapf: forall G1 G2 T1 T2 GH,
    stpd2 true G1 T1 G2 T2 GH ->
    stpd2 false G1 T1 G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_transf: forall G1 G2 G3 T1 T2 T3 GH,
    stpd2 true G1 T1 G2 T2 GH ->
    stpd2 false G2 T2 G3 T3 GH ->
    stpd2 false G1 T1 G3 T3 GH.
Proof. intros. repeat eu. eauto. Qed.


Lemma sstpd2_wrapf: forall G1 G2 T1 T2 GH,
    sstpd2 true G1 T1 G2 T2 GH ->
    sstpd2 false G1 T1 G2 T2 GH.
Proof. intros. repeat eu. eexists. eapply stp2_wrapf. eauto. Qed.
Lemma sstpd2_transf: forall G1 G2 G3 T1 T2 T3 GH,
    sstpd2 true G1 T1 G2 T2 GH ->
    sstpd2 false G2 T2 G3 T3 GH ->
    sstpd2 false G1 T1 G3 T3 GH.
Proof. intros. repeat eu. eexists. eapply stp2_transf; eauto. Qed.


Lemma atpd2_transf: forall G1 G2 G3 T1 T2 T3 GH,
    atpd2 true G1 T1 G2 T2 GH ->
    atpd2 false G2 T2 G3 T3 GH ->
    atpd2 false G1 T1 G3 T3 GH.
Proof. intros. repeat eu. eexists. eapply stp2_transf; eauto. Qed.

(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v

Could use do-notation to clean up syntax.
 *)

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (index x env)
        | tabs f ds => Some (Some (vabs env f ds))
        | ttabs x T y  => Some (Some (vtabs env x T y))
        | ttyp T     => Some (Some (vty env T))
        | tapp ef m ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vbool _)) => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vtabs _ _ _ _)) => Some None
                | Some (Some (vabs env2 f ds)) =>
                  match index m ds with
                    | None => Some None
                    | Some (x, ey) =>
                      teval n ((x,vx)::(f,vabs env2 f ds)::env2) ey
                  end
              end
          end
        | ttapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vbool _)) => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vabs _ _ _)) => Some None
                | Some (Some (vtabs env2 x T ey)) =>
                  teval n ((x,vx)::env2) ey
              end
          end
      end
  end.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Hint Constructors closed_rec.
Hint Constructors has_type dcs_has_type.
Hint Constructors val_type.
Hint Constructors wf_env.
Hint Constructors stp.
Hint Constructors stp2.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.
Hint Unfold closed.
Hint Unfold open.

Hint Resolve ex_intro.


(* ############################################################ *)
(* Examples *)
(* ############################################################ *)


(*
match goal with
        | |- has_type _ (tvar _) _ =>
          try solve [apply t_vara;
                      repeat (econstructor; eauto)]
          | _ => idtac
      end;
*)

Ltac crush_has_tp :=
  try solve [eapply stp_selx; compute; eauto; crush_has_tp];
  try solve [eapply stp_selax; compute; eauto; crush_has_tp];
  try solve [eapply cl_selb; compute; eauto; crush_has_tp];
  try solve [(econstructor; compute; eauto; crush_has_tp)].

Ltac crush2 :=
  try solve [(eapply stp_selx; compute; eauto; crush2)];
  try solve [(eapply stp_selax; compute; eauto; crush2)];
  try solve [(eapply stp_sel1; compute; eauto; crush2)];
  try solve [(eapply stp_sela1; compute; eauto; crush2)];
  try solve [(eapply cl_selb; compute; eauto; crush2)];
  try solve [(econstructor; compute; eauto; crush2)];
  try solve [(eapply t_sub; eapply t_var; compute; eauto; crush2)].


(* define polymorphic identity function *)

Definition polyId := TAll (TBind (TMem TBot TTop)) (TFun 0 (TSelB 0) (TSelB 0)).

Example ex1: has_type [] (ttabs 0 (TBind (TMem TBot TTop)) (tabs 1 [(0, (2, (tvar 2)))])) polyId.
Proof.
  crush2.
Qed.


(* instantiate it to bool *)

Example ex2: has_type [(0,polyId)] (ttapp (tvar 0) (ttyp TBool)) (TFun 0 TBool TBool).
Proof.
  eapply t_tapp. instantiate (1:= (TBind (TMem TBool TBool))).
    { eapply t_sub.
      { eapply t_var. simpl. eauto. crush2. }
      { eapply stp_all; eauto. { eapply stp_bindx; crush2. } compute. eapply cl_fun; eauto.
        eapply stp_fun. compute. eapply stp_selax; crush2. crush2.
        eapply stp_fun. compute. eapply stp_selab2. crush2.
        crush2. instantiate (1:=TBool). crush2.
        instantiate (1:=[(0, TBind (TMem TBool TBool))]). simpl. reflexivity.
        rewrite app_nil_l. reflexivity.
        crush2. crush2. crush2.
        simpl. eapply stp_selab1. crush2.
        crush2. instantiate (1:=TBool). crush2.
        instantiate (1:=[(0, TBind (TMem TBool TBool))]). simpl. reflexivity.
        rewrite app_nil_l. reflexivity.
        crush2. crush2. crush2.
      }
    }
    { eapply t_typ; crush2. }
    crush2.
Qed.



(* define brand / unbrand client function *)

Definition brandUnbrand :=
  TAll (TBind (TMem TBot TTop))
       (TFun 0
          (TFun 0 TBool (TSelB 0)) (* brand *)
          (TFun 0
             (TFun 0 (TSelB 0) TBool) (* unbrand *)
             TBool)).

Example ex3:
  has_type []
           (ttabs 0 (TBind (TMem TBot TTop))
                  (tabs 1 [(0, (2,
                        (tabs 3 [(0, (4,
                              (tapp (tvar 4) 0 (tapp (tvar 2) 0 ttrue))))])))]))
           brandUnbrand.
Proof.
  crush2.
Qed.


(* instantiating it at bool is admissible *)

Example ex4:
  has_type [(1,TFun 0 TBool TBool);(0,brandUnbrand)]
           (tvar 0) (TAll (TBind (TMem TBool TBool)) (TFun 0 (TFun 0 TBool TBool) (TFun 0 (TFun 0 TBool TBool) TBool))).
Proof.
  eapply t_sub. crush2. crush2. eapply stp_all; crush2. compute. eapply stp_fun. eapply stp_fun. crush2.
  eapply stp_selab2. crush2. crush2. instantiate(1:=TBool). crush2.
  instantiate (1:=[(0, TBind (TMem TBool TBool))]). simpl. reflexivity.
  rewrite app_nil_l. reflexivity.
  crush2. crush2. crush2.
  eapply stp_fun. crush2. eapply stp_fun.
  eapply stp_selab1. crush2. crush2. instantiate(1:=TBool). crush2.
  instantiate (1:=[(0, TBind (TMem TBool TBool))]). simpl. reflexivity.
  rewrite app_nil_l. reflexivity.
  crush2. crush2. crush2.
  crush2. crush2.
Qed.

Hint Resolve ex4.

(* apply it to identity functions *)

Example ex5:
  has_type [(1,TFun 0 TBool TBool);(0,brandUnbrand)]
           (tapp (tapp (ttapp (tvar 0) (ttyp TBool)) 0 (tvar 1)) 0 (tvar 1)) TBool.
Proof.
  crush2.
Qed.


(* test expansion *)

Example ex6:
  has_type [(1,TSel 0);(0,TMem TBot (TBind (TFun 0 TBool (TSelB 0))))]
           (tvar 1) (TFun 0 TBool (TSel 1)).
Proof.
  remember (TFun 0 TBool (TSel 1)) as T.
  assert (T = open (TSel 1) (TFun 0 TBool (TSelB 0))). compute. eauto.
  rewrite H.
  eapply t_var_unpack. eapply t_sub. eapply t_var. compute. eauto. crush2. crush2. crush2.
Qed.


Example ex7:
  stp [(1,TSel 0);(0,TMem TBot (TBind (TMem TBot (TFun 0 TBool (TSelB 0)))))] []
           (TSel 1) (TFun 0 TBool (TSel 1)).
Proof.
  remember (TFun 0 TBool (TSel 1)) as T.
  assert (T = open (TSel 1) (TFun 0 TBool (TSelB 0))). compute. eauto.
  rewrite H.
  eapply stp_selb1. compute. eauto.
  eapply stp_sel1. compute. eauto.
  crush2.
  eapply stp_mem. eauto.
  eapply stp_bindx; crush2.
  eapply stp_bindx; crush2.
  crush2.
Qed.





(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)





Lemma wf_fresh : forall vs ts,
                    wf_env vs ts ->
                    (fresh vs = fresh ts).
Proof.
  intros. induction H. auto.
  compute. eauto.
Qed.

Hint Immediate wf_fresh.


Lemma wfh_length : forall vvs vs ts,
                    wf_envh vvs vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  compute. eauto.
Qed.

Hint Immediate wf_fresh.

Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < fresh vs.
Proof.
  intros X vs. induction vs.
  - Case "nil". intros. inversion H.
  - Case "cons".
    intros. inversion H. destruct a.
    case_eq (le_lt_dec (fresh vs) i); intros ? E1.
    + SCase "ok".
      rewrite E1 in H1.
      case_eq (beq_nat n i); intros E2.
      * SSCase "hit".
        eapply beq_nat_true in E2. subst n. compute. eauto.
      * SSCase "miss".
        rewrite E2 in H1.
        assert (n < fresh vs). eapply IHvs. apply H1.
        compute. omega.
    + SCase "bad".
      rewrite E1 in H1. inversion H1.
Qed.

Lemma indexr_max : forall X vs n (T: X),
                       indexr n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  - Case "nil". intros. inversion H.
  - Case "cons".
    intros. inversion H. destruct a.
    case_eq (beq_nat n (length vs)); intros E2.
    + SSCase "hit".
      eapply beq_nat_true in E2. subst n. compute. eauto.
    + SSCase "miss".
      rewrite E2 in H1.
      assert (n < length vs). eapply IHvs. apply H1.
      compute. eauto.
Qed.



Lemma le_xx : forall a b,
                       a <= b ->
                       exists E, le_lt_dec a b = left E.
Proof. intros.
  case_eq (le_lt_dec a b). intros. eauto.
  intros. omega.
Qed.
Lemma le_yy : forall a b,
                       a > b ->
                       exists E, le_lt_dec a b = right E.
Proof. intros.
  case_eq (le_lt_dec a b). intros. omega.
  intros. eauto.
Qed.

Lemma index_extend : forall X vs n n' x (T: X),
                       index n vs = Some T ->
                       fresh vs <= n' ->
                       index n ((n',x)::vs) = Some T.

Proof.
  intros.
  assert (n < fresh vs). eapply index_max. eauto.
  assert (n <> n'). omega.
  assert (beq_nat n n' = false) as E. eapply beq_nat_false_iff; eauto.
  assert (fresh vs <= n') as E2. omega.
  elim (le_xx (fresh vs) n' E2). intros ? EX.
  unfold index. unfold index in H. rewrite H. rewrite E. rewrite EX. reflexivity.
Qed.

Lemma indexr_extend : forall X vs n n' x (T: X),
                       indexr n vs = Some T ->
                       indexr n ((n',x)::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply indexr_max. eauto.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff. omega.
  unfold indexr. unfold indexr in H. rewrite H. rewrite E. reflexivity.
Qed.


(* splicing -- for stp_extend. not finished *)

Fixpoint splice n (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TBool        => TBool
    | TMem T1 T2   => TMem (splice n T1) (splice n T2)
    | TFun m T1 T2   => TFun m (splice n T1) (splice n T2)
    | TSelB i      => TSelB i
    | TSel i       => TSel i
    | TSelH i      => if le_lt_dec n i  then TSelH (i+1) else TSelH i
    | TAll T1 T2   => TAll (splice n T1) (splice n T2)
    | TBind T2   => TBind (splice n T2)
    | TAnd T1 T2 => TAnd (splice n T1) (splice n T2)
  end.

Definition splicett n (V: (id*ty)) :=
  match V with
    | (x,T) => (x,(splice n T))
  end.

Definition spliceat n (V: (id*(venv*ty))) :=
  match V with
    | (x,(G,T)) => (x,(G,splice n T))
  end.

Lemma splice_open_permute: forall {X} (G:list (id*X)) T n j k,
n + k >= length G ->
(open_rec j (TSelH (n + S k)) (splice (length G) T)) =
(splice (length G) (open_rec j (TSelH (n + k)) T)).
Proof.
  intros X G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto.

  case_eq (le_lt_dec (length G) i); intros E LE; simpl; eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  case_eq (le_lt_dec (length G) (n + length G)); intros EL LE.
  assert (n + S (length G) = n + length G + 1). omega.
  case_eq (le_lt_dec (length G) (n+k)); intros E' LE'; simpl; eauto.
  assert (n + S k=n + k + 1) as R by omega. rewrite R. reflexivity.
  omega. omega.
Qed.

Lemma indexr_splice_hi: forall G0 G2 x0 x v1 T,
    indexr x0 (G2 ++ G0) = Some T ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (splicett (length G0)) G2 ++ (x, v1) :: G0) = Some (splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. omega.
  - simpl in H. destruct a.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma indexr_spliceat_hi: forall G0 G2 x0 x v1 G T,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (spliceat (length G0)) G2 ++ (x, v1) :: G0) = Some (G, splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. omega.
  - simpl in H. destruct a.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. destruct p. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma plus_lt_contra: forall a b,
  a + b < b -> False.
Proof.
  intros a b H. induction a.
  - simpl in H. apply lt_irrefl in H. assumption.
  - simpl in H. apply IHa. omega.
Qed.

Lemma indexr_splice_lo0: forall {X} G0 G2 x0 (T:X),
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 G0 = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl in H. apply H.
  - simpl in H. destruct a.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E. subst.
      rewrite app_length in H0. apply plus_lt_contra in H0. inversion H0.
    + rewrite E in H. apply IHG2. apply H. apply H0.
Qed.

Lemma indexr_extend_mult: forall {X} G0 G2 x0 (T:X),
    indexr x0 G0 = Some T ->
    indexr x0 (G2++G0) = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl. assumption.
  - destruct a. simpl.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E.
      apply indexr_max in H. subst.
      rewrite app_length in H. apply plus_lt_contra in H. inversion H.
    + apply IHG2. assumption.
Qed.

Lemma indexr_splice_lo: forall G0 G2 x0 x v1 T f,
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 (map (splicett f) G2 ++ (x, v1) :: G0) = Some T.
Proof.
  intros.
  assert (indexr x0 G0 = Some T). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.

Lemma indexr_spliceat_lo: forall G0 G2 x0 x v1 G T f,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    x0 < length G0 ->
    indexr x0 (map (spliceat f) G2 ++ (x, v1) :: G0) = Some (G, T).
Proof.
  intros.
  assert (indexr x0 G0 = Some (G, T)). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.


Lemma fresh_splice_ctx: forall G n,
  fresh G = fresh (map (splicett n) G).
Proof.
  intros. induction G.
  - simpl. reflexivity.
  - destruct a. simpl. reflexivity.
Qed.

Lemma index_splice_ctx: forall G x T n,
  index x G = Some T ->
  index x (map (splicett n) G) = Some (splice n T).
Proof.
  intros. induction G.
  - simpl in H. inversion H.
  - destruct a. simpl in H.
    case_eq (le_lt_dec (fresh G) i); intros E LE; rewrite LE in H.
    case_eq (beq_nat x i); intros Eq; rewrite Eq in H.
    inversion H. simpl. erewrite <- (fresh_splice_ctx). rewrite LE.
    rewrite Eq. reflexivity.
    simpl. erewrite <- (fresh_splice_ctx). rewrite LE.
    rewrite Eq. apply IHG. apply H.
    inversion H.
Qed.

Lemma closed_splice: forall j l T n,
  closed j l T ->
  closed j (S l) (splice n T).
Proof.
  intros. induction H; simpl; eauto.
  case_eq (le_lt_dec n x); intros E LE.
  unfold closed. apply cl_selh. omega.
  unfold closed. apply cl_selh. omega.
Qed.

Lemma map_splice_length_inc: forall G0 G2 x v1,
   (length (map (splicett (length G0)) G2 ++ (x, v1) :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma map_spliceat_length_inc: forall G0 G2 x v1,
   (length (map (spliceat (length G0)) G2 ++ (x, v1) :: G0)) = (S (length (G2 ++ G0))).
Proof.
  intros. rewrite app_length. rewrite map_length. induction G2.
  - simpl. reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_inc: forall j l T,
  closed j l T ->
  closed j (S l) T.
Proof.
  intros. induction H; simpl; eauto.
  unfold closed. apply cl_selh. omega.
Qed.

Lemma closed_inc_mult: forall j l l' T,
  closed j l T ->
  l' >= l ->
  closed j l' T.
Proof.
  intros j l l' T H LE. induction LE.
  - assumption.
  - apply closed_inc. assumption.
Qed.

Ltac sp :=
  match goal with
    | A : ?P, H : ?P -> _ |- _ => specialize (H A)
  end.

Lemma closed_splice_idem: forall k l T n,
                            closed k l T ->
                            n >= l ->
                            splice n T = T.
Proof.
  intros. induction H; simpl; repeat sp; repeat (match goal with
    | H: splice ?N ?T = ?T |- _ => rewrite H
  end); eauto.
  case_eq (le_lt_dec n x); intros E LE. omega. reflexivity.
Qed.

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.

Lemma closed_upgrade: forall i j l T,
 closed_rec i l T ->
 j >= i ->
 closed_rec j l T.
Proof.
 intros. generalize dependent j. induction H; intros; eauto.
 Case "TAll". econstructor. eapply IHclosed_rec1. omega. eapply IHclosed_rec2. omega.
 Case "TBind". econstructor. eapply IHclosed_rec. omega.
 Case "TSelB". econstructor. omega.
Qed.

Lemma closed_upgrade_free: forall i l k T,
 closed_rec i l T ->
 k >= l ->
 closed_rec i k T.
Proof.
 intros. generalize dependent k. induction H; intros; eauto.
 Case "TSelH". econstructor. omega.
Qed.


Lemma closed_open: forall j n TX T, closed (j+1) n T -> closed j n TX -> closed j n (open_rec j TX T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H; unfold closed; try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto. eapply closed_upgrade. eauto. eauto.

  - Case "TSelB". simpl.
    case_eq (beq_nat j i); intros E. eauto.

    econstructor. eapply beq_nat_false_iff in E. omega.

  - eauto.
  - eapply closed_upgrade; eauto.
  - eapply closed_upgrade; eauto.
Qed.

Lemma stp_closed : forall G GH T1 T2,
                     stp G GH T1 T2 ->
                     closed 0 (length GH) T1 /\ closed 0 (length GH) T2.
Proof.
  intros. induction H;
    try solve [repeat ev; split; eauto using indexr_max];
    try solve [try inversion IHstp; split; eauto; apply cl_selh; eapply indexr_max; eassumption];
    try solve [inversion IHstp1 as [IH1 IH2]; inversion IH2; split; eauto; apply cl_selh; eapply indexr_max; eassumption].
Qed.

Lemma stp_closed2 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) T2.
Proof.
  intros. apply (proj2 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp_closed1 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) T1.
Proof.
  intros. apply (proj1 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp2_closed: forall G1 G2 T1 T2 GH s m n1,
                     stp2 s m G1 T1 G2 T2 GH n1 ->
                     closed 0 (length GH) T1 /\ closed 0 (length GH) T2.
  intros. induction H;
    try solve [repeat ev; split; eauto];
    try solve [try inversion IHstp2_1; try inversion IHstp2_2; split; eauto; apply cl_selh; eapply indexr_max; eassumption];
    try solve [inversion IHstp2 as [IH1 IH2]; inversion IH2; split; eauto; apply cl_selh; eapply indexr_max; eassumption].
Qed.

Lemma stp2_closed2 : forall G1 G2 T1 T2 GH s m n1,
                       stp2 s m G1 T1 G2 T2 GH n1 ->
                       closed 0 (length GH) T2.
Proof.
  intros. apply (proj2 (stp2_closed G1 G2 T1 T2 GH s m n1 H)).
Qed.

Lemma stp2_closed1 : forall G1 G2 T1 T2 GH s m n1,
                       stp2 s m G1 T1 G2 T2 GH n1 ->
                       closed 0 (length GH) T1.
Proof.
  intros. apply (proj1 (stp2_closed G1 G2 T1 T2 GH s m n1 H)).
Qed.


Lemma valtp_closed: forall G v T n,
  val_type G v T n -> closed 0 0 T.
Proof.
  intros. inversion H; subst; repeat ev;
  match goal with
      [ H : stp2 ?s ?m ?G1 ?T1 G T [] ?n |- _ ] =>
      eapply stp2_closed2 in H; simpl in H; apply H
  end.
Qed.

Lemma concat_same_length: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GU = length GH1 ->
  GU=GH1 /\ GL=GH0.
Proof.
  intros. generalize dependent GH1. induction GU; intros.
  - simpl in H0. induction GH1. rewrite app_nil_l in H. rewrite app_nil_l in H.
    split. reflexivity. apply H.
    simpl in H0. omega.
  - simpl in H0. induction GH1. simpl in H0. omega.
    simpl in H0. inversion H0. simpl in H. inversion H. specialize (IHGU GH1 H4 H2).
    destruct IHGU. subst. split; reflexivity.
Qed.

Lemma concat_same_length': forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X),
  GU ++ GL = GH1 ++ GH0 ->
  length GL = length GH0 ->
  GU=GH1 /\ GL=GH0.
Proof.
  intros.
  assert (length (GU ++ GL) = length (GH1 ++ GH0)) as A. {
    rewrite H. reflexivity.
  }
  rewrite app_length in A. rewrite app_length in A.
  rewrite H0 in A. apply NPeano.Nat.add_cancel_r in A.
  apply concat_same_length; assumption.
Qed.

Lemma exists_GH1L: forall {X} (GU: list X) (GL: list X) (GH1: list X) (GH0: list X) x0,
  length GL = S x0 ->
  GU ++ GL = GH1 ++ GH0 ->
  length GH0 <= x0 ->
  exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ GH0.
Proof.
  intros X GU. induction GU; intros.
  - eexists. rewrite app_nil_l. split. reflexivity. simpl in H0. assumption.
  - induction GH1.

    simpl in H0.
    assert (length (a :: GU ++ GL) = length GH0) as Contra. {
      rewrite H0. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H0. inversion H0.
    specialize (IHGU GL GH1 GH0 x0 H H4 H1).
    destruct IHGU as [GH1L [IHA IHB]].
    exists GH1L. split. simpl. rewrite IHA. reflexivity. apply IHB.
Qed.

Lemma exists_GH0U: forall {X} (GH1: list X) (GH0: list X) (GU: list X) (GL: list X) x0,
  length GL = S x0 ->
  GU ++ GL = GH1 ++ GH0 ->
  x0 < length GH0 ->
  exists GH0U, GH0 = GH0U ++ GL.
Proof.
  intros X GH1. induction GH1; intros.
  - simpl in H0. exists GU. symmetry. assumption.
  - induction GU.

    simpl in H0.
    assert (length GL = length (a :: GH1 ++ GH0)) as Contra. {
      rewrite H0. reflexivity.
    }
    simpl in Contra. rewrite app_length in Contra. omega.

    simpl in H0. inversion H0.
    specialize (IHGH1 GH0 GU GL x0 H H4 H1).
    destruct IHGH1 as [GH0U IH].
    exists GH0U. apply IH.
Qed.

Lemma stp_splice : forall GX G0 G1 T1 T2 x v1,
   stp GX (G1++G0) T1 T2 ->
   stp GX ((map (splicett (length G0)) G1) ++ (x,v1)::G0) (splice (length G0) T1) (splice (length G0) T2).
Proof.
  intros GX G0 G1 T1 T2 x v1 H. remember (G1++G0) as G.
  revert G0 G1 HeqG.
  induction H; intros; subst GH; simpl; eauto.
  - Case "sel1".
    eapply stp_sel1. apply H. assumption.
    assert (splice (length G0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp1. reflexivity.
    apply IHstp2. reflexivity.
  - Case "sel2".
    eapply stp_sel2. apply H. assumption.
    assert (splice (length G0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp1. reflexivity.
    apply IHstp2. reflexivity.
  - Case "selb1".
    assert (splice (length G0) (open (TSel x0) T2)=(open (TSel x0) T2)) as A. {
      eapply closed_splice_idem. apply stp_closed2 in H0. inversion H0. subst.
      simpl in H5. inversion H5. subst.
      eapply closed_open. simpl. eassumption. eauto.
      omega.
    }
    rewrite A. eapply stp_selb1; eauto.
    rewrite <- A. apply IHstp2; eauto.
  - Case "selb2".
    assert (splice (length G0) (open (TSel x0) T1)=(open (TSel x0) T1)) as A. {
      eapply closed_splice_idem. apply stp_closed2 in H0. inversion H0. subst.
      simpl in H5. inversion H5. subst.
      eapply closed_open. simpl. eassumption. eauto.
      omega.
    }
    rewrite A. eapply stp_selb2; eauto.
    rewrite <- A. apply IHstp2; eauto.
  - Case "sela1".
    case_eq (le_lt_dec (length G0) x0); intros E LE.
    + eapply stp_sela1. eapply indexr_splice_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x0 = x0 +1) as A by omega.
      rewrite <- A. eapply H0.
      eapply IHstp1. eauto.
      eapply IHstp2. eauto.
    + eapply stp_sela1. eapply indexr_splice_lo. eauto. eauto. eauto. eauto.
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp1. eauto.
      eapply IHstp2. eauto.
  - Case "sela2".
    case_eq (le_lt_dec (length G0) x0); intros E LE.
    + eapply stp_sela2. eapply indexr_splice_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x0 = x0 +1) as A by omega.
      rewrite <- A. eapply H0.
      eapply IHstp1. eauto.
      eapply IHstp2. eauto.
    + eapply stp_sela2. eapply indexr_splice_lo. eauto. eauto. eauto. eauto.
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp1. eauto.
      eapply IHstp2. eauto.
  - Case "selab1".
    case_eq (le_lt_dec (length G0) x0); intros E LE.
    + assert (S x0 = x0 + 1) as EQ by omega.
      assert ((splice (length G0) (TBind (TMem TBot T2)))=(TBind (TMem TBot T2))) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (exists GH1L, G2 = GU ++ GH1L /\ GL = GH1L ++ G0) as EQGH. {
        eapply exists_GH1L. eassumption. eassumption. eassumption.
      }
      destruct EQGH as [GH1L [EQGH1 EQGL]].
      eapply stp_selab1.
      eapply indexr_splice_hi; eauto. rewrite <- HeqG. eassumption.
      rewrite <- EQ. eapply closed_splice in H0. eapply H0.
      eassumption.
      instantiate (1:=(map (splicett (length G0)) GH1L) ++ (x, v1)::G0).
      rewrite app_length. simpl.
      rewrite EQGL in H2. rewrite app_length in H2.
      rewrite map_length. omega.
      rewrite EQGH1. rewrite map_app. rewrite app_assoc. reflexivity.
      rewrite <- A.
      eapply IHstp1; eauto.
      inversion A. unfold open. rewrite splice_open_permute.
      rewrite H5. unfold open.
      assert (TSelH x0=TSelH (x0+0)) as B. {
        rewrite <- plus_n_O. reflexivity.
      }
      rewrite <- B. reflexivity.
      omega.
      apply IHstp2; eauto.
    + assert (closed 1 0 T2) as C2. {
        inversion H1. subst. inversion H9. subst. eassumption.
      }
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (splice (length G0) (TBind (TMem TBot T2))=(TBind (TMem TBot T2))) as B. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (exists GH0U, G0 = GH0U ++ GL) as EQGH. {
        eapply exists_GH0U. eassumption. eassumption. eassumption.
      }
      destruct EQGH as [GH0U EQGH].
      eapply stp_selab1.
      eapply indexr_splice_lo; eauto. rewrite <- HeqG. eassumption.
      eassumption. eassumption.
      instantiate (1:=GL). eassumption.
      rewrite EQGH. instantiate (1:=map (splicett (length (GH0U ++ GL))) G2 ++ (x, v1) :: GH0U). rewrite <- app_assoc. reflexivity.
      eauto.
      inversion B. rewrite H5. rewrite H7.
      erewrite closed_splice_idem. reflexivity.
      eapply closed_open. eapply closed_upgrade_free. eapply C2. omega.
      eapply cl_selh. instantiate (1:=(length G0)). omega. omega.
      apply IHstp2; eauto.
  - Case "selab2".
    case_eq (le_lt_dec (length G0) x0); intros E LE.
    + assert (S x0 = x0 + 1) as EQ by omega.
      assert ((splice (length G0) (TBind (TMem T1 TTop)))=(TBind (TMem T1 TTop))) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (exists GH1L, G2 = GU ++ GH1L /\ GL = GH1L ++ G0) as EQGH. {
        eapply exists_GH1L. eassumption. eassumption. eassumption.
      }
      destruct EQGH as [GH1L [EQGH1 EQGL]].
      eapply stp_selab2.
      eapply indexr_splice_hi; eauto. rewrite <- HeqG. eassumption.
      rewrite <- EQ. eapply closed_splice in H0. eapply H0.
      eassumption.
      instantiate (1:=(map (splicett (length G0)) GH1L) ++ (x, v1)::G0).
      rewrite app_length. simpl.
      rewrite EQGL in H2. rewrite app_length in H2.
      rewrite map_length. omega.
      rewrite EQGH1. rewrite map_app. rewrite app_assoc. reflexivity.
      rewrite <- A.
      eapply IHstp1; eauto.
      inversion A. unfold open. rewrite splice_open_permute.
      rewrite H5. unfold open.
      assert (TSelH x0=TSelH (x0+0)) as B. {
        rewrite <- plus_n_O. reflexivity.
      }
      rewrite <- B. reflexivity.
      omega.
      apply IHstp2; eauto.
    + assert (closed 1 0 T1) as C2. {
        inversion H1. subst. inversion H9. subst. eassumption.
      }
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (splice (length G0) (TBind (TMem T1 TTop))=(TBind (TMem T1 TTop))) as B. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (exists GH0U, G0 = GH0U ++ GL) as EQGH. {
        eapply exists_GH0U. eassumption. eassumption. eassumption.
      }
      destruct EQGH as [GH0U EQGH].
      eapply stp_selab2.
      eapply indexr_splice_lo; eauto. rewrite <- HeqG. eassumption.
      eassumption. eassumption.
      instantiate (1:=GL). eassumption.
      rewrite EQGH. instantiate (1:=map (splicett (length (GH0U ++ GL))) G2 ++ (x, v1) :: GH0U). rewrite <- app_assoc. reflexivity.
      eauto.
      inversion B. rewrite H5. rewrite H7.
      erewrite closed_splice_idem. reflexivity.
      eapply closed_open. eapply closed_upgrade_free. eapply C2. omega.
      eapply cl_selh. instantiate (1:=(length G0)). omega. omega.
      apply IHstp2; eauto.
  - Case "selax".
    case_eq (le_lt_dec (length G0) x0); intros E LE.
    + eapply stp_selax. eapply indexr_splice_hi. eauto. eauto.
    + eapply stp_selax. eapply indexr_splice_lo. eauto. eauto.
  - Case "all".
    eapply stp_all.
    eapply IHstp1. eauto. eauto. eauto.

    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.

    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.

    specialize IHstp2 with (G3:=G0) (G4:=(0, T1) :: G2).
    simpl in IHstp2. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x0.
    rewrite app_length in IHstp2. simpl in IHstp2.
    eapply IHstp2. eauto. omega.

    specialize IHstp3 with (G3:=G0) (G4:=(0, T3) :: G2).
    simpl in IHstp2. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x0.
    rewrite app_length in IHstp3. simpl in IHstp3.
    eapply IHstp3. eauto. omega. omega.

  - Case "bind".
    eapply stp_bindx.
    eauto.

    rewrite map_splice_length_inc. apply closed_splice. assumption.
    rewrite map_splice_length_inc. apply closed_splice. assumption.

    rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x0.
    specialize IHstp1 with (G3:=G0) (G4:=(0, (open (TSelH (length G2 + length G0)) T2))::G2).
    rewrite app_length in IHstp1. simpl in IHstp1. unfold open in IHstp1.
    eapply IHstp1. eauto. omega.

    rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x0.
    specialize IHstp2 with (G3:=G0) (G4:=(0, (open (TSelH (length G2 + length G0)) T1))::G2).
    rewrite app_length in IHstp2. simpl in IHstp2. unfold open in IHstp2.
    eapply IHstp2. eauto. omega. omega.
Qed.

Lemma stp2_splice : forall G1 T1 G2 T2 GH1 GH0 x v1 s m n1,
   stp2 s m G1 T1 G2 T2 (GH1++GH0) n1 ->
   stp2 s m G1 (splice (length GH0) T1) G2 (splice (length GH0) T2) ((map (spliceat (length GH0)) GH1) ++ (x,v1)::GH0) n1.
Proof.
  intros G1 T1 G2 T2 GH1 GH0 x v1 s m n1 H. remember (GH1++GH0) as GH.
  revert GH0 GH1 HeqGH.
  induction H; intros; subst GH; simpl; eauto.
  - Case "strong_sel1".
    eapply stp2_strong_sel1. apply H. eassumption.
    assert (splice (length GH0) TX' = TX') as B. {
      eapply closed_splice_idem. eapply valtp_closed. eassumption. omega.
    }
    rewrite <- B. simpl in IHstp2_1. eapply IHstp2_1. reflexivity.
    eassumption.
    assert (splice (length GH0) (open (TSel (fresh GX)) TX)=(open (TSel (fresh GX)) TX)) as A.  {
      eapply closed_splice_idem. eapply closed_open. eassumption. eauto. omega.
    }
    rewrite <- A. apply IHstp2_2.
    reflexivity.
  - Case "strong_sel2".
    eapply stp2_strong_sel2. apply H. eassumption.
    assert (splice (length GH0) TX' = TX') as B. {
      eapply closed_splice_idem. eapply valtp_closed. eassumption. omega.
    }
    rewrite <- B. simpl in IHstp2_1. eapply IHstp2_1. reflexivity.
    eassumption.
    assert (splice (length GH0) (open (TSel (fresh GX)) TX)=(open (TSel (fresh GX)) TX)) as A.  {
      eapply closed_splice_idem. eapply closed_open. eassumption. eauto. omega.
    }
    rewrite <- A. apply IHstp2_2.
    reflexivity.
  - Case "sel1".
    eapply stp2_sel1. apply H. eassumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp2_1.
    reflexivity.
    apply IHstp2_2. reflexivity.

  - Case "selb1".
    assert (splice (length GH0) (open (TSel x') T2)=(open (TSel x') T2)) as A. {
      eapply closed_splice_idem. apply stp2_closed2 in H3. inversion H3. subst.
      simpl in H8. inversion H8. subst.
      eapply closed_open. simpl. eassumption. eauto.
      omega.
    }
    rewrite A. eapply stp2_selb1; eauto.
    rewrite <- A. apply IHstp2_2; eauto.
  - Case "sel2".
    eapply stp2_sel2. apply H. eassumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp2_1.
    reflexivity.
    apply IHstp2_2. reflexivity.
  - Case "selb2".
    assert (splice (length GH0) (open (TSel x') T1)=(open (TSel x') T1)) as A. {
      eapply closed_splice_idem. apply stp2_closed2 in H3. inversion H3. subst.
      simpl in H8. inversion H8. subst.
      eapply closed_open. simpl. eassumption. eauto.
      omega.
    }
    rewrite A. eapply stp2_selb2; eauto.
    rewrite <- A. apply IHstp2_2; eauto.
  - Case "sela1".
    case_eq (le_lt_dec (length GH0) x0); intros E LE.
    + eapply stp2_sela1. eapply indexr_spliceat_hi. apply H. eauto.
      eapply closed_splice in H0. assert (S x0 = x0 +1) as EQ by omega. rewrite <- EQ.
      eapply H0.
      eapply IHstp2_1. eauto.
      eapply IHstp2_2. eauto.
    + eapply stp2_sela1. eapply indexr_spliceat_lo. apply H. eauto. eauto.
      assert (splice (length GH0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp2_1. eauto. eapply IHstp2_2. eauto.

  - Case "selab1".
    case_eq (le_lt_dec (length GH0) x0); intros E LE.
    + assert (S x0 = x0 + 1) as EQ by omega.
      assert ((splice (length GH0) (TBind (TMem TBot T2)))=(TBind (TMem TBot T2))) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ GH0) as EQGH. {
        eapply exists_GH1L. eassumption. eassumption. eassumption.
      }
      destruct EQGH as [GH1L [EQGH1 EQGL]].
      eapply stp2_selab1.
      eapply indexr_spliceat_hi; eauto. rewrite <- HeqGH. eassumption.
      eapply closed_splice in H0. rewrite <- EQ. eapply H0.
      eassumption.
      instantiate (1:=(map (spliceat (length GH0)) GH1L) ++ (x, v1)::GH0).
      rewrite app_length. simpl.
      rewrite EQGL in H2. rewrite app_length in H2.
      rewrite map_length. omega.
      rewrite EQGH1. rewrite map_app. rewrite app_assoc. reflexivity.
      rewrite <- A.
      eapply IHstp2_1; eauto.
      inversion A. unfold open.
      rewrite splice_open_permute.
      rewrite H5. unfold open.
      assert (TSelH x0=TSelH (x0+0)) as B. {
        rewrite <- plus_n_O. reflexivity.
      }
      rewrite <- B. reflexivity.
      omega.
      apply IHstp2_2; eauto.
    + assert (closed 1 0 T2) as C2. {
        inversion H1. subst. inversion H9. subst. eassumption.
      }
      assert (splice (length GH0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (splice (length GH0) (TBind (TMem TBot T2))=(TBind (TMem TBot T2))) as B. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (exists GH0U, GH0 = GH0U ++ GL) as EQGH. {
        eapply exists_GH0U. eassumption. eassumption. eassumption.
      }
      destruct EQGH as [GH0U EQGH].
      eapply stp2_selab1.
      eapply indexr_spliceat_lo; eauto. rewrite <- HeqGH. eassumption.
      eassumption. eassumption.
      instantiate (1:=GL). eassumption.
      rewrite EQGH. instantiate (1:=map (spliceat (length (GH0U ++ GL))) GH1 ++ (x, v1) :: GH0U). rewrite <- app_assoc. reflexivity.
      eauto.
      inversion B. rewrite H5. rewrite H7.
      erewrite closed_splice_idem. reflexivity.
      eapply closed_open. eapply closed_upgrade_free. eapply C2. omega.
      eapply cl_selh. instantiate (1:=(length GH0)). omega. omega.
      apply IHstp2_2; eauto.

  - Case "selab2".
    case_eq (le_lt_dec (length GH0) x0); intros E LE.
    + assert (S x0 = x0 + 1) as EQ by omega.
      assert ((splice (length GH0) (TBind (TMem T1 TTop)))=(TBind (TMem T1 TTop))) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ GH0) as EQGH. {
        eapply exists_GH1L. eassumption. eassumption. eassumption.
      }
      destruct EQGH as [GH1L [EQGH1 EQGL]].
      eapply stp2_selab2.
      eapply indexr_spliceat_hi; eauto. rewrite <- HeqGH. eassumption.
      eapply closed_splice in H0. rewrite <- EQ. eapply H0.
      eassumption.
      instantiate (1:=(map (spliceat (length GH0)) GH1L) ++ (x, v1)::GH0).
      rewrite app_length. simpl.
      rewrite EQGL in H2. rewrite app_length in H2.
      rewrite map_length. omega.
      rewrite EQGH1. rewrite map_app. rewrite app_assoc. reflexivity.
      rewrite <- A.
      eapply IHstp2_1; eauto.
      inversion A. unfold open.
      rewrite splice_open_permute.
      rewrite H5. unfold open.
      assert (TSelH x0=TSelH (x0+0)) as B. {
        rewrite <- plus_n_O. reflexivity.
      }
      rewrite <- B. reflexivity.
      omega.
      apply IHstp2_2; eauto.
    + assert (closed 1 0 T1) as C2. {
        inversion H1. subst. inversion H9. subst. eassumption.
      }
      assert (splice (length GH0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (splice (length GH0) (TBind (TMem T1 TTop))=(TBind (TMem T1 TTop))) as B. {
        eapply closed_splice_idem. eassumption. omega.
      }
      assert (exists GH0U, GH0 = GH0U ++ GL) as EQGH. {
        eapply exists_GH0U. eassumption. eassumption. eassumption.
      }
      destruct EQGH as [GH0U EQGH].
      eapply stp2_selab2.
      eapply indexr_spliceat_lo; eauto. rewrite <- HeqGH. eassumption.
      eassumption. eassumption.
      instantiate (1:=GL). eassumption.
      rewrite EQGH. instantiate (1:=map (spliceat (length (GH0U ++ GL))) GH1 ++ (x, v1) :: GH0U). rewrite <- app_assoc. reflexivity.
      eauto.
      inversion B. rewrite H5. rewrite H7.
      erewrite closed_splice_idem. reflexivity.
      eapply closed_open. eapply closed_upgrade_free. eapply C2. omega.
      eapply cl_selh. instantiate (1:=(length GH0)). omega. omega.
      apply IHstp2_2; eauto.

  - Case "sela2".
    case_eq (le_lt_dec (length GH0) x0); intros E LE.
    + eapply stp2_sela2. eapply indexr_spliceat_hi. apply H. eauto.
      eapply closed_splice in H0. assert (S x0 = x0 +1) as EQ by omega. rewrite <- EQ.
      eapply H0.
      eapply IHstp2_1. eauto.
      eapply IHstp2_2. eauto.
    + eapply stp2_sela2. eapply indexr_spliceat_lo. apply H. eauto. eauto.
      assert (splice (length GH0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp2_1. eauto. eapply IHstp2_2. eauto.
  - Case "selax".
    case_eq (le_lt_dec (length GH0) x0); intros E LE.
    + eapply stp2_selax.
      eapply indexr_spliceat_hi. apply H. eauto.
    + eapply stp2_selax.
      eapply indexr_spliceat_lo. apply H. eauto.
  - Case "all".
    eapply stp2_all.
    eapply IHstp2_1. reflexivity.

    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.

    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.

    specialize IHstp2_2 with (GH2:=GH0) (GH3:=(0, (G1, T1)) :: GH1).
    simpl in IHstp2_2. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    rewrite app_length in IHstp2_2. simpl in IHstp2_2.
    eapply IHstp2_2. reflexivity. omega.

    specialize IHstp2_3 with (GH2:=GH0) (GH3:=(0, (G2, T3)) :: GH1).
    simpl in IHstp2_3. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    rewrite app_length in IHstp2_3. simpl in IHstp2_3.
    eapply IHstp2_3. reflexivity. omega. omega.
  - Case "bind".
    eapply stp2_bind.

    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.

    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.

    rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    specialize IHstp2_1 with (GH2:=GH0) (GH3:=(0, (G2,(open (TSelH (length GH1 + length GH0)) T2)))::GH1).
    rewrite app_length in IHstp2_1. simpl in IHstp2_1. unfold open in IHstp2_1.
    eapply IHstp2_1. eauto. omega.

    rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    specialize IHstp2_2 with (GH2:=GH0) (GH3:=(0, (G1,(open (TSelH (length GH1 + length GH0)) T1)))::GH1).
    rewrite app_length in IHstp2_2. simpl in IHstp2_2. unfold open in IHstp2_2.
    eapply IHstp2_2. eauto. omega. omega.
  - Case "bindb".
    eapply stp2_bindb.

    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.

    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.

    rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    specialize IHstp2_1 with (GH2:=GH0) (GH3:=(0, (G2,(open (TSelH (length GH1 + length GH0)) T2)))::GH1).
    rewrite app_length in IHstp2_1. simpl in IHstp2_1. unfold open in IHstp2_1.
    eapply IHstp2_1. eauto. omega.

    rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    specialize IHstp2_2 with (GH2:=GH0) (GH3:=(0, (G1,(open (TSelH (length GH1 + length GH0)) T1)))::GH1).
    rewrite app_length in IHstp2_2. simpl in IHstp2_2. unfold open in IHstp2_2.
    eapply IHstp2_2. eauto. omega. omega.
Qed.

Lemma stp_extend : forall G1 GH T1 T2 x v1,
                       stp G1 GH T1 T2 ->
                       stp G1 ((x,v1)::GH) T1 T2.
Proof.
  intros. induction H; eauto using indexr_extend.
  - Case "selab1".
    eapply stp_selab1; try eassumption.
    eapply indexr_extend. eassumption.
    instantiate (1:=(x,v1)::GU). simpl. rewrite H3. reflexivity.
  - Case "selab2".
    eapply stp_selab2; try eassumption.
    eapply indexr_extend. eassumption.
    instantiate (1:=(x,v1)::GU). simpl. rewrite H3. reflexivity.
  - Case "all".
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. apply H1. omega.
  }
  assert (splice (length GH) T4 = T4) as A4. {
    eapply closed_splice_idem. apply H2. omega.
  }
  assert (TSelH (S (length GH)) = splice (length GH) (TSelH (length GH))) as AH. {
    simpl. case_eq (le_lt_dec (length GH) (length GH)); intros E LE.
    simpl. rewrite NPeano.Nat.add_1_r. reflexivity.
    clear LE. apply lt_irrefl in E. inversion E.
  }
  assert (closed 0 (length GH) T1).  eapply stp_closed2. eauto.
  assert (splice (length GH) T1 = T1) as A1. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (closed 0 (length GH) T3). eapply stp_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (splicett (length GH)) [(0,T1)] ++(x,v1)::GH =((0,T1)::(x,v1)::GH)) as HGX1. {
    simpl. rewrite A1. eauto.
  }
  assert (map (splicett (length GH)) [(0,T3)] ++(x,v1)::GH =((0,T3)::(x,v1)::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  apply stp_all with (x:=length ((x,v1) :: GH)).
  apply IHstp1.
  reflexivity.
  apply closed_inc. apply H1.
  apply closed_inc. apply H2.
  simpl.
  rewrite <- A2. rewrite <- A2.
  unfold open.
  change (TSelH (S (length GH))) with (TSelH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite <- HGX1.
  apply stp_splice.
  rewrite A2. simpl. unfold open in H3. rewrite <- H0. apply H3.
  omega.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (TSelH (S (length GH))) with (TSelH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  rewrite <- HGX3.
  apply stp_splice.
  simpl. unfold open in H4. rewrite <- H0. apply H4.
  omega. omega.

  - Case "bind".
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. apply H1. omega.
  }
  assert (splice (length GH) T1 = T1) as A1. {
    eapply closed_splice_idem. eauto. omega.
  }
  apply stp_bindx with (x:=length ((x,v1) :: GH)).
  reflexivity.
  apply closed_inc. apply H0.
  apply closed_inc. apply H1.
  simpl.
  unfold open.
  rewrite <- A2.
  change (TSelH (S (length GH))) with (TSelH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. simpl.
  assert (
      stp G1
     ((map (splicett (length GH)) [(0, (open_rec 0 (TSelH (length GH)) T2))])++(x, v1)::GH)
     (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     ->
     stp G1
     ((0, splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
      :: (x, v1) :: GH)
     (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
    ) as HGX1. {
    simpl. intros A. apply A.
  }
  apply HGX1.
  apply stp_splice.
  simpl. unfold open in H2. rewrite <- H. apply H2.
  simpl. apply le_refl.
  rewrite <- A1. rewrite <- A2.
  unfold open. simpl.
  change (TSelH (S (length GH))) with (TSelH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  assert (
     (stp G1
     ((map (splicett (length GH)) [(0, (open_rec 0 (TSelH (length GH)) T1))])++(x, v1)::GH)
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T1))
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T2)))
     ->
     (stp G1
     ((0, splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T1))
      :: (x, v1) :: GH)
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T1))
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T2)))
    ) as HGX2. {
    simpl. intros A. apply A.
  }
  apply HGX2.
  apply stp_splice.
  simpl. unfold open in H3. rewrite <- H. apply H3.
  simpl. apply le_refl. simpl. apply le_refl.
Qed.


Lemma indexr_at_index: forall {A} x0 GH0 GH1 x (v:A),
  beq_nat x0 (length GH1) = true ->
  indexr x0 (GH0 ++ (x, v) :: GH1) = Some v.
Proof.
  intros. apply beq_nat_true in H. subst.
  induction GH0.
  - simpl. rewrite <- beq_nat_refl. reflexivity.
  - destruct a. simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    rewrite false_beq_nat. assumption. omega.
Qed.

Lemma indexr_same: forall {A} x0 (v0:A) GH0 GH1 x (v:A) (v':A),
  beq_nat x0 (length GH1) = false ->
  indexr x0 (GH0 ++ (x, v) :: GH1) = Some v0 ->
  indexr x0 (GH0 ++ (x, v') :: GH1) = Some v0.
Proof.
  intros ? ? ? ? ? ? ? ? E H.
  induction GH0.
  - simpl. rewrite E. simpl in H. rewrite E in H. apply H.
  - destruct a. simpl.
    rewrite app_length. simpl.
    case_eq (beq_nat x0 (length GH0 + S (length GH1))); intros E'.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite H. reflexivity.
    simpl in H. rewrite app_length in H. simpl in H. rewrite E' in H.
    rewrite IHGH0. reflexivity. assumption.
Qed.

Inductive venv_ext : venv -> venv -> Prop :=
| venv_ext_refl : forall G, venv_ext G G
| venv_ext_cons : forall x T G1 G2, fresh G1 <= x -> venv_ext G1 G2 -> venv_ext ((x,T)::G1) G2.

Inductive aenv_ext : aenv -> aenv -> Prop :=
| aenv_ext_nil : aenv_ext nil nil
| aenv_ext_cons : forall x T G' G A A', aenv_ext A' A -> venv_ext G' G -> aenv_ext ((x,(G',T))::A') ((x,(G,T))::A).

Lemma aenv_ext_refl: forall GH, aenv_ext GH GH.
Proof.
  intros. induction GH.
  - apply aenv_ext_nil.
  - destruct a. destruct p. apply aenv_ext_cons.
    assumption.
    apply venv_ext_refl.
Qed.

Lemma index_extend_mult : forall G G' x T,
                       index x G = Some T ->
                       venv_ext G' G ->
                       index x G' = Some T.
Proof.
  intros G G' x T H HV.
  induction HV.
  - assumption.
  - apply index_extend. apply IHHV. apply H. assumption.
Qed.

Lemma aenv_ext__same_length:
  forall GH GH',
    aenv_ext GH' GH ->
    length GH = length GH'.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. rewrite IHaenv_ext. reflexivity.
Qed.

Lemma aenv_ext__concat:
  forall GH GH' GU GL,
    aenv_ext GH' GH ->
    GH = GU ++ GL ->
    exists GU' GL', GH' = GU' ++ GL' /\ aenv_ext GU' GU /\ aenv_ext GL' GL.
Proof.
  intros. generalize dependent GU. generalize dependent GL. induction H.
  - intros. symmetry in H0. apply app_eq_nil in H0. destruct H0.
    exists []. exists []. simpl. split; eauto. subst. split. apply aenv_ext_refl. apply aenv_ext_refl.
  - intros. induction GU. rewrite app_nil_l in H1. subst.
    exists []. eexists. rewrite app_nil_l. split. reflexivity.
    split. apply aenv_ext_refl.
    apply aenv_ext_cons. eassumption. eassumption.

    simpl in H1. inversion H1.
    specialize (IHaenv_ext GL GU H4).
    destruct IHaenv_ext as [GU' [GL' [IHA [IHU IHL]]]].
    exists ((x, (G', T))::GU'). exists GL'.
    split. simpl. rewrite IHA. reflexivity.
    split. apply aenv_ext_cons. apply IHU. assumption. apply IHL.
Qed.

 Lemma indexr_at_ext :
  forall GH GH' x T G,
    aenv_ext GH' GH ->
    indexr x GH = Some (G, T) ->
    exists G', indexr x GH' = Some (G', T) /\ venv_ext G' G.
Proof.
  intros GH GH' x T G Hext Hindex. induction Hext.
  - simpl in Hindex. inversion Hindex.
  - simpl. simpl in Hindex.
    case_eq (beq_nat x (length A)); intros E.
    rewrite E in Hindex.  inversion Hindex. subst.
    rewrite <- (@aenv_ext__same_length A A'). rewrite E.
    exists G'. split. reflexivity. assumption. assumption.
    rewrite E in Hindex.
    rewrite <- (@aenv_ext__same_length A A'). rewrite E.
    apply IHHext. assumption. assumption.
Qed.


Lemma stp2_closure_extend_rec :
  forall G1 G2 T1 T2 GH s m n1,
    stp2 s m G1 T1 G2 T2 GH n1 ->
    (forall G1' G2' GH',
       aenv_ext GH' GH ->
       venv_ext G1' G1 ->
       venv_ext G2' G2 ->
       stp2 s m G1' T1 G2' T2 GH' n1).
Proof.
  intros G1 G2 T1 T2 GH s m n1 H.
  induction H; intros; eauto;
  try solve [inversion IHstp2_1; inversion IHstp2_2; eauto];
  try solve [inversion IHstp2; eauto].
  - Case "strong_sel1".
    eapply stp2_strong_sel1. eapply index_extend_mult. apply H.
    assumption. eassumption.
    apply IHstp2_1. assumption. apply venv_ext_refl. assumption.
    assumption.
    apply IHstp2_2. assumption. apply venv_ext_refl. assumption.
  - Case "strong_sel2".
    eapply stp2_strong_sel2. eapply index_extend_mult. apply H.
    assumption. eassumption.
    apply IHstp2_1. assumption. apply venv_ext_refl. assumption.
    assumption.
    apply IHstp2_2. assumption. assumption. apply venv_ext_refl.
  - Case "strong_selx".
    eapply stp2_strong_selx.
    eapply index_extend_mult. apply H. assumption.
    eapply index_extend_mult. apply H0. assumption.
  - Case "sel1".
    eapply stp2_sel1. eapply index_extend_mult. apply H.
    assumption. eassumption. assumption.
    apply IHstp2_1. assumption. apply venv_ext_refl. assumption.
    apply IHstp2_2. assumption. assumption. assumption.
  - Case "selb1".
    eapply stp2_selb1. eapply index_extend_mult. apply H. assumption.
    destruct H0. left. eapply index_extend_mult. eapply H0. assumption. right. eapply H0.
    eassumption. assumption.
    apply IHstp2_1. apply aenv_ext_refl. apply venv_ext_refl. assumption.
    apply IHstp2_2. assumption. assumption. assumption.
  - Case "sel2".
    eapply stp2_sel2. eapply index_extend_mult. apply H.
    assumption. eassumption. assumption.
    apply IHstp2_1. assumption. apply venv_ext_refl. assumption.
    apply IHstp2_2. assumption. assumption. assumption.
  - Case "selb2".
    eapply stp2_selb2. eapply index_extend_mult. apply H. assumption.
    destruct H0. left. eapply index_extend_mult. eapply H0. assumption. right. eapply H0.
    eassumption. assumption.
    apply IHstp2_1. apply aenv_ext_refl. apply venv_ext_refl. assumption.
    apply IHstp2_2. assumption. assumption. assumption.
  - Case "selx".
    eapply stp2_selx.
    eapply index_extend_mult. apply H. assumption.
    eapply index_extend_mult. apply H0. assumption.
  - Case "sela1".
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_sela1 with (GX:=GX') (TX:=TX).
    assumption. assumption.
    apply IHstp2_1; assumption.
    apply IHstp2_2; assumption.
  - Case "selab1".
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    assert (exists GU' GL', GH' = GU' ++ GL' /\ aenv_ext GU' GU /\ aenv_ext GL' GL) as B. {
      eapply aenv_ext__concat. eassumption. eassumption.
    }
    destruct B as [GU' [GL' [BEQ [BU BL]]]].
    eapply stp2_selab1 with (GX:=GX') (TX:=TX) (GL:=GL') (GU:=GU').
    assumption. eassumption. eassumption.
    rewrite <- H2. symmetry. apply aenv_ext__same_length. eassumption.
    eassumption.
    apply IHstp2_1; eauto.
    eassumption.
    apply IHstp2_2; eauto.
  - Case "selab2".
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    assert (exists GU' GL', GH' = GU' ++ GL' /\ aenv_ext GU' GU /\ aenv_ext GL' GL) as B. {
      eapply aenv_ext__concat. eassumption. eassumption.
    }
    destruct B as [GU' [GL' [BEQ [BU BL]]]].
    eapply stp2_selab2 with (GX:=GX') (TX:=TX) (GL:=GL') (GU:=GU').
    assumption. eassumption. eassumption.
    rewrite <- H2. symmetry. apply aenv_ext__same_length. eassumption.
    eassumption.
    apply IHstp2_1; eauto.
    eassumption.
    apply IHstp2_2; eauto.
  - Case "sela2".
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_sela2 with (GX:=GX') (TX:=TX).
    assumption. assumption.
    apply IHstp2_1; assumption.
    apply IHstp2_2; assumption.
  - Case "selax".
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_selax with (GX:=GX') (TX:=TX).
    assumption.
  - Case "all".
    assert (length GH = length GH') as A. {
      apply aenv_ext__same_length. assumption.
    }
    apply stp2_all.
    apply IHstp2_1; assumption.
    subst. rewrite <- A. assumption.
    subst. rewrite <- A. assumption.
    subst. rewrite <- A.
    apply IHstp2_2. apply aenv_ext_cons. assumption. assumption. assumption. assumption.
    subst. rewrite <- A.
    apply IHstp2_3. apply aenv_ext_cons. assumption. assumption. assumption. assumption.
  - Case "bind".
    assert (length GH = length GH') as A. {
      apply aenv_ext__same_length. assumption.
    }
    apply stp2_bind.
    subst. rewrite A in H. assumption.
    subst. rewrite A in H0. assumption.
    rewrite A in IHstp2_1. apply IHstp2_1. apply aenv_ext_cons. assumption. assumption. assumption. assumption.
    subst.
    rewrite A in IHstp2_2. apply IHstp2_2. apply aenv_ext_cons. assumption. assumption. assumption. assumption.
  - Case "bindb".
    assert (length GH = length GH') as A. {
      apply aenv_ext__same_length. assumption.
    }
    apply stp2_bindb.
    subst. rewrite A in H. assumption.
    subst. rewrite A in H0. assumption.
    rewrite A in IHstp2_1. apply IHstp2_1. apply aenv_ext_cons. assumption. assumption. assumption. assumption.
    subst.
    rewrite A in IHstp2_2. apply IHstp2_2. apply aenv_ext_cons. assumption. assumption. assumption. assumption.
  - Case "trans".
    eapply stp2_transf.
    eapply IHstp2_1.
    assumption. assumption. apply venv_ext_refl.
    eapply IHstp2_2.
    assumption. apply venv_ext_refl. assumption.
Qed.


Lemma stp2_closure_extend : forall G1 T1 G2 T2 GH GX T x v s m n1,
                              stp2 s m G1 T1 G2 T2 ((0,(GX,T))::GH) n1 ->
                              fresh GX <= x ->
                              stp2 s m G1 T1 G2 T2 ((0,((x,v)::GX,T))::GH) n1.
Proof.
  intros. eapply stp2_closure_extend_rec. apply H.
  apply aenv_ext_cons. apply aenv_ext_refl. apply venv_ext_cons.
  assumption. apply venv_ext_refl. apply venv_ext_refl. apply venv_ext_refl.
Qed.


Lemma stp2_extend : forall x v1 G1 G2 T1 T2 H s m n1,
                      stp2 s m G1 T1 G2 T2 H n1 ->
                      (fresh G1 <= x ->
                       stp2 s m ((x,v1)::G1) T1 G2 T2 H n1) /\
                      (fresh G2 <= x ->
                       stp2 s m G1 T1 ((x,v1)::G2) T2 H n1) /\
                      (fresh G1 <= x -> fresh G2 <= x ->
                       stp2 s m ((x,v1)::G1) T1 ((x,v1)::G2) T2 H n1).
Proof.
  intros. induction H0;
    try solve [split; try split; repeat ev; intros; eauto using index_extend];
    try solve [split; try split; intros; inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]]; inversion IHstp2_3 as [? [? ?]]; constructor; eauto; apply stp2_closure_extend; eauto];
    try solve [split; try split; intros; inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]]; eapply stp2_bind; eauto; apply stp2_closure_extend; eauto];
    try solve [split; try split; intros; inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]]; eapply stp2_bindb; eauto; apply stp2_closure_extend; eauto].

  - split; try split; intros; inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]]; eapply stp2_selb1; eauto using index_extend.
    inversion H0. left. eauto using index_extend. right. eauto.
    inversion H0. left. eauto using index_extend. right. eauto.

  - split; try split; intros; inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]]; eapply stp2_selb2; eauto using index_extend.
    inversion H0. left. eauto using index_extend. right. eauto.
    inversion H0. left. eauto using index_extend. right. eauto.
Qed.

Lemma stp2_extend2 : forall x v1 G1 G2 T1 T2 H s m n1,
                       stp2 s m G1 T1 G2 T2 H n1 ->
                       fresh G2 <= x ->
                       stp2 s m G1 T1 ((x,v1)::G2) T2 H n1.
Proof.
  intros. apply (proj2 (stp2_extend x v1 G1 G2 T1 T2 H s m n1 H0)). assumption.
Qed.

Lemma stp2_extend1 : forall x v1 G1 G2 T1 T2 H s m n1,
                       stp2 s m G1 T1 G2 T2 H n1 ->
                       fresh G1 <= x ->
                       stp2 s m ((x,v1)::G1) T1 G2 T2 H n1.
Proof.
  intros. apply (proj1 (stp2_extend x v1 G1 G2 T1 T2 H s m n1 H0)). assumption.
Qed.

Lemma stp2_extendH : forall x v1 G1 G2 T1 T2 GH s m n1,
                       stp2 s m G1 T1 G2 T2 GH n1 ->
                       stp2 s m G1 T1 G2 T2 ((x,v1)::GH) n1.
Proof.
  intros. induction H; eauto using indexr_extend.
  - Case "selab1".
    eapply stp2_selab1; try eassumption. eapply indexr_extend. eassumption.
    rewrite H3. instantiate (1:=(x, v1)::GU). simpl. reflexivity.
  - Case "selab2".
    eapply stp2_selab2; try eassumption. eapply indexr_extend. eassumption.
    rewrite H3. instantiate (1:=(x, v1)::GU). simpl. reflexivity.
  - Case "all".
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. apply H0. omega.
  }
  assert (splice (length GH) T4 = T4) as A4. {
    eapply closed_splice_idem. apply H1. omega.
  }
  assert (TSelH (S (length GH)) = splice (length GH) (TSelH (length GH))) as AH. {
    simpl. case_eq (le_lt_dec (length GH) (length GH)); intros E LE.
    simpl. rewrite NPeano.Nat.add_1_r. reflexivity.
    clear LE. apply lt_irrefl in E. inversion E.
  }
  assert (closed 0 (length GH) T1). eapply stp2_closed2. eauto.
  assert (splice (length GH) T1 = T1) as A1. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (spliceat (length GH)) [(0,(G1, T1))] ++(x,v1)::GH =((0, (G1, T1))::(x,v1)::GH)) as HGX1. {
    simpl. rewrite A1. eauto.
  }
  assert (closed 0 (length GH) T3). eapply stp2_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (spliceat (length GH)) [(0,(G2, T3))] ++(x,v1)::GH =((0, (G2, T3))::(x,v1)::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  eapply stp2_all.
  apply IHstp2_1.
  apply closed_inc. apply H0.
  apply closed_inc. apply H1.
  simpl.
  unfold open.
  rewrite <- A2.
  unfold open.
  change (TSelH (S (length GH))) with (TSelH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite <- HGX1.
  apply stp2_splice.
  simpl. unfold open in H2. apply H2.
  simpl. omega.
  rewrite <- A2. rewrite <- A4.
  unfold open. simpl.
  change (TSelH (S (length GH))) with (TSelH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite -> splice_open_permute.
  rewrite <- HGX3.
  apply stp2_splice.
  simpl. unfold open in H3. apply H3.
  omega. omega.

  - Case "bind".
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (splice (length GH) T1 = T1) as A1. {
    eapply closed_splice_idem. eauto. omega.
  }
  eapply stp2_bind.
  apply closed_inc. eauto.
  apply closed_inc. eauto.
  simpl.
  unfold open.
  rewrite <- A2.
  change (TSelH (S (length GH))) with (TSelH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. simpl.
  assert (
   stp2 1 false G2 (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     G2 (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     ((map (spliceat (length GH)) [(0, (G2, open_rec 0 (TSelH (length GH)) T2))])++((x, v1)::GH))
      n2
   ->
   stp2 1 false G2 (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     G2 (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     ((0, (G2, splice (length GH) (open_rec 0 (TSelH (length GH)) T2)))
      :: (x, v1) :: GH) n2
    ) as HGX1. {
    simpl. intros A. apply A.
  }
  apply HGX1.
  apply stp2_splice.
  simpl. unfold open in H1. apply H1.
  simpl. apply le_refl.
  rewrite <- A1. rewrite <- A2.
  unfold open. simpl.
  change (TSelH (S (length GH))) with (TSelH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  assert (
   stp2 1 false G1
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T1)) G2
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T2))
     ((map (spliceat (length GH)) [(0, (G1, (open_rec 0 (TSelH (0 + length GH)) T1)))])++((x, v1) :: GH)) n1
      ->
   stp2 1 false G1
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T1)) G2
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T2))
     ((0, (G1, splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T1)))
        :: (x, v1) :: GH) n1
   ) as HGX2. {
    simpl. intros A. apply A.
  }
  apply HGX2.
  apply stp2_splice.
  simpl. unfold open in H2. apply H2.
  simpl. apply le_refl. simpl. apply le_refl.

  - Case "bindb".
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (splice (length GH) T1 = T1) as A1. {
    eapply closed_splice_idem. eauto. omega.
  }
  eapply stp2_bindb.
  apply closed_inc. eauto.
  apply closed_inc. eauto.
  simpl.
  unfold open.
  rewrite <- A2.
  change (TSelH (S (length GH))) with (TSelH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. simpl.
  assert (
   stp2 (S m) false G2 (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     G2 (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     ((map (spliceat (length GH)) [(0, (G2, open_rec 0 (TSelH (length GH)) T2))])++((x, v1)::GH))
      n2
   ->
   stp2 (S m) false G2 (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     G2 (splice (length GH) (open_rec 0 (TSelH (length GH)) T2))
     ((0, (G2, splice (length GH) (open_rec 0 (TSelH (length GH)) T2)))
      :: (x, v1) :: GH) n2
    ) as HGX1. {
    simpl. intros A. apply A.
  }
  apply HGX1.
  apply stp2_splice.
  simpl. unfold open in H1. apply H1.
  simpl. apply le_refl.
  rewrite <- A1. rewrite <- A2.
  unfold open. simpl.
  change (TSelH (S (length GH))) with (TSelH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  assert (
   stp2 (S m) false G1
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T1)) G2
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T2))
     ((map (spliceat (length GH)) [(0, (G1, (open_rec 0 (TSelH (0 + length GH)) T1)))])++((x, v1) :: GH)) n1
      ->
   stp2 (S m) false G1
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T1)) G2
     (splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T2))
     ((0, (G1, splice (length GH) (open_rec 0 (TSelH (0 + length GH)) T1)))
        :: (x, v1) :: GH) n1
   ) as HGX2. {
    simpl. intros A. apply A.
  }
  apply HGX2.
  apply stp2_splice.
  simpl. unfold open in H2. apply H2.
  simpl. apply le_refl. simpl. apply le_refl.
Qed.

Lemma stp2_extendH_mult : forall G1 G2 T1 T2 H H2 s m n1,
                       stp2 s m G1 T1 G2 T2 H n1->
                       stp2 s m G1 T1 G2 T2 (H2++H) n1.
Proof. intros. induction H2.
  simpl. eauto. destruct a.
  simpl. eapply stp2_extendH. eauto.
Qed.

Lemma stp2_extendH_mult0 : forall G1 G2 T1 T2 H2 s m n1,
                       stp2 s m G1 T1 G2 T2 [] n1 ->
                       stp2 s m G1 T1 G2 T2 H2 n1.
Proof. intros. eapply stp2_extendH_mult with (H2:=H2) in H; eauto. rewrite app_nil_r in H. eauto. Qed.

Lemma stp2_reg  : forall G1 G2 T1 T2 GH s m n1,
                    stp2 s m G1 T1 G2 T2 GH n1 ->
                    (exists n0, stp2 s true G1 T1 G1 T1 GH n0) /\
                    (exists n0, stp2 s true G2 T2 G2 T2 GH n0).
Proof.
  intros. induction H;
    try solve [repeat ev; split; eexists; eauto].
  - Case "and11".
    repeat ev; split; eexists.
    eapply stp2_and2.
    eapply stp2_wrapf. eapply stp2_and11; eassumption.
    eapply stp2_wrapf. eapply stp2_and12; eassumption.
    eassumption.
  - Case "and12".
    repeat ev; split; eexists.
    eapply stp2_and2.
    eapply stp2_wrapf. eapply stp2_and11; eassumption.
    eapply stp2_wrapf. eapply stp2_and12; eassumption.
    eassumption.
  - Case "and2".
    repeat ev; split; eexists.
    eassumption.
    eapply stp2_and2.
    eapply stp2_wrapf. eapply stp2_and11; eassumption.
    eapply stp2_wrapf. eapply stp2_and12; eassumption.
  Grab Existential Variables.
  apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
  apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
  apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stp2_reg2 : forall G1 G2 T1 T2 GH s m n1,
                       stp2 s m G1 T1 G2 T2 GH n1 ->
                       (exists n0, stp2 s true G2 T2 G2 T2 GH n0).
Proof.
  intros. apply (proj2 (stp2_reg G1 G2 T1 T2 GH s m n1 H)).
Qed.

Lemma stp2_reg1 : forall G1 G2 T1 T2 GH s m n1,
                       stp2 s m G1 T1 G2 T2 GH n1 ->
                       (exists n0, stp2 s true G1 T1 G1 T1 GH n0).
Proof.
  intros. apply (proj1 (stp2_reg G1 G2 T1 T2 GH s m n1 H)).
Qed.

Lemma stp_reg  : forall G GH T1 T2,
                    stp G GH T1 T2 ->
                    stp G GH T1 T1 /\ stp G GH T2 T2.
Proof.
  intros. induction H;
    try solve [repeat ev; split; eauto].
Qed.

Lemma stpd2_extend2 : forall x v1 G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       fresh G2 <= x ->
                       stpd2 m G1 T1 ((x,v1)::G2) T2 H.
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extend2; assumption.
Qed.

Lemma stpd2_extend1 : forall x v1 G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       fresh G1 <= x ->
                       stpd2 m ((x,v1)::G1) T1 G2 T2 H.
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extend1; assumption.
Qed.

Lemma stpd2_extendH : forall x v1 G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       stpd2 m G1 T1 G2 T2 ((x,v1)::H).
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extendH; assumption.
Qed.

Lemma stpd2_extendH_mult : forall G1 G2 T1 T2 H H2 m,
                       stpd2 m G1 T1 G2 T2 H->
                       stpd2 m G1 T1 G2 T2 (H2++H).
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extendH_mult; assumption.
Qed.

Lemma stpd2_extendH_mult0 : forall G1 G2 T1 T2 H2 m,
                       stpd2 m G1 T1 G2 T2 [] ->
                       stpd2 m G1 T1 G2 T2 H2.
Proof.
  intros. inversion H as [n1 Hsub]. exists n1.
  apply stp2_extendH_mult0; assumption.
Qed.


Lemma stpd2_reg2 : forall G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       stpd2 true G2 T2 G2 T2 H.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_reg2; eassumption.
Qed.

Lemma stpd2_reg1 : forall G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       stpd2 true G1 T1 G1 T1 H.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_reg1; eassumption.
Qed.


Lemma stpd2_closed2 : forall G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       closed 0 (length H) T2.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_closed2; eassumption.
Qed.

Lemma stpd2_closed1 : forall G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       closed 0 (length H) T1.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_closed1; eassumption.
Qed.

(* atpd2 variants below *)
Lemma atpd2_extend2 : forall x v1 G1 G2 T1 T2 H m,
                       atpd2 m G1 T1 G2 T2 H ->
                       fresh G2 <= x ->
                       atpd2 m G1 T1 ((x,v1)::G2) T2 H.
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extend2; assumption.
Qed.

Lemma atpd2_extend1 : forall x v1 G1 G2 T1 T2 H m,
                       atpd2 m G1 T1 G2 T2 H ->
                       fresh G1 <= x ->
                       atpd2 m ((x,v1)::G1) T1 G2 T2 H.
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extend1; assumption.
Qed.

Lemma atpd2_extendH : forall x v1 G1 G2 T1 T2 H m,
                       atpd2 m G1 T1 G2 T2 H ->
                       atpd2 m G1 T1 G2 T2 ((x,v1)::H).
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extendH; assumption.
Qed.

Lemma atpd2_extendH_mult : forall G1 G2 T1 T2 H H2 m,
                       atpd2 m G1 T1 G2 T2 H->
                       atpd2 m G1 T1 G2 T2 (H2++H).
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extendH_mult; assumption.
Qed.

Lemma atpd2_extendH_mult0 : forall G1 G2 T1 T2 H2 m,
                       atpd2 m G1 T1 G2 T2 [] ->
                       atpd2 m G1 T1 G2 T2 H2.
Proof.
  intros. inversion H as [n1 Hsub]. exists n1.
  apply stp2_extendH_mult0; assumption.
Qed.


Lemma atpd2_reg2 : forall G1 G2 T1 T2 H m,
                       atpd2 m G1 T1 G2 T2 H ->
                       atpd2 true G2 T2 G2 T2 H.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_reg2; eassumption.
Qed.

Lemma atpd2_reg1 : forall G1 G2 T1 T2 H m,
                       atpd2 m G1 T1 G2 T2 H ->
                       atpd2 true G1 T1 G1 T1 H.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_reg1; eassumption.
Qed.


Lemma atpd2_closed2 : forall G1 G2 T1 T2 H m,
                       atpd2 m G1 T1 G2 T2 H ->
                       closed 0 (length H) T2.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_closed2; eassumption.
Qed.

Lemma atpd2_closed1 : forall G1 G2 T1 T2 H m,
                       atpd2 m G1 T1 G2 T2 H ->
                       closed 0 (length H) T1.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_closed1; eassumption.
Qed.

(* sstpd2 variants below *)

Lemma sstpd2_extend2 : forall x v1 G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       fresh G2 <= x ->
                       sstpd2 m G1 T1 ((x,v1)::G2) T2 H.
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extend2; assumption.
Qed.

Lemma sstpd2_extend1 : forall x v1 G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       fresh G1 <= x ->
                       sstpd2 m ((x,v1)::G1) T1 G2 T2 H.
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extend1; assumption.
Qed.

Lemma sstpd2_extendH : forall x v1 G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       sstpd2 m G1 T1 G2 T2 ((x,v1)::H).
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extendH; assumption.
Qed.

Lemma sstpd2_extendH_mult : forall G1 G2 T1 T2 H H2 m,
                       sstpd2 m G1 T1 G2 T2 H->
                       sstpd2 m G1 T1 G2 T2 (H2++H).
Proof.
  intros. inversion H0 as [n1 Hsub]. exists n1.
  apply stp2_extendH_mult; assumption.
Qed.

Lemma sstpd2_extendH_mult0 : forall G1 G2 T1 T2 H2 m,
                       sstpd2 m G1 T1 G2 T2 [] ->
                       sstpd2 m G1 T1 G2 T2 H2.
Proof.
  intros. inversion H as [n1 Hsub]. exists n1.
  apply stp2_extendH_mult0; assumption.
Qed.

Lemma sstpd2_reg2 : forall G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       sstpd2 true G2 T2 G2 T2 H.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_reg2; eassumption.
Qed.

Lemma sstpd2_reg1 : forall G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       sstpd2 true G1 T1 G1 T1 H.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_reg1; eassumption.
Qed.

Lemma sstpd2_closed2 : forall G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       closed 0 (length H) T2.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_closed2; eassumption.
Qed.

Lemma sstpd2_closed1 : forall G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       closed 0 (length H) T1.
Proof.
  intros. inversion H0 as [n1 Hsub].
  eapply stp2_closed1; eassumption.
Qed.

Lemma valtp_extend : forall vs v x v1 T n,
                       val_type vs v T n ->
                       fresh vs <= x ->
                       val_type ((x,v1)::vs) v T n.
Proof.
  intros. induction H; eauto; econstructor; eauto; eapply sstpd2_extend2; eauto.
Qed.


Lemma index_safe_ex: forall H1 G1 TF i,
             wf_env H1 G1 ->
             index i G1 = Some TF ->
             exists v n, index i H1 = Some v /\ val_type H1 v TF n.
Proof. intros. induction H.
   - Case "nil". inversion H0.
   - Case "cons". inversion H0.
     case_eq (le_lt_dec (fresh ts) n); intros ? E1.
     + SCase "ok".
       rewrite E1 in H3.
       assert ((fresh ts) <= n) as QF. eauto. rewrite <-(wf_fresh vs ts H1) in QF.
       elim (le_xx (fresh vs) n QF). intros ? EX.

       case_eq (beq_nat i n); intros E2.
       * SSCase "hit".
         assert (index i ((n, v) :: vs) = Some v). eauto. unfold index. rewrite EX. rewrite E2. eauto.
         assert (t = TF).
         unfold index in H0. rewrite E1 in H0. rewrite E2 in H0. inversion H0. eauto.
         subst t. eauto.
       * SSCase "miss".
         rewrite E2 in H3.
         assert (exists v0 n0, index i vs = Some v0 /\ val_type vs v0 TF n0) as HI. eapply IHwf_env. eauto.
         inversion HI as [v0 [n0 HI1]]. inversion HI1.
         eexists. eexists. econstructor. eapply index_extend; eauto. eapply valtp_extend; eauto.
     + SSCase "bad".
       rewrite E1 in H3. inversion H3.
Qed.


Lemma index_exists: forall H1 G1 TF i,
             wf_env H1 G1 ->
             index i G1 = Some TF ->
             exists v, index i H1 = Some v.
Proof.
  intros.
  assert (exists v n, index i H1 = Some v /\ val_type H1 v TF n) as A. {
    eapply index_safe_ex; eauto.
  }
  destruct A as [v [n [A1 A2]]].
  exists v. apply A1.
Qed.

Lemma index_safeh_ex: forall H1 H2 G1 GH TF i,
             wf_env H1 G1 -> wf_envh H1 H2 GH ->
             indexr i GH = Some TF ->
             exists v, indexr i H2 = Some v /\ valh_type H1 H2 v TF.
Proof. intros. induction H0.
   - Case "nil". inversion H3.
   - Case "cons". inversion H3.
     case_eq (beq_nat i (length ts)); intros E2.
     * SSCase "hit".
       rewrite E2 in H2. inversion H2. subst. clear H2.
       assert (length ts = length vs). symmetry. eapply wfh_length. eauto.
       simpl. rewrite H1 in E2. rewrite E2.
       eexists. split. eauto. econstructor.
     * SSCase "miss".
       rewrite E2 in H2.
       assert (exists v : venv * ty,
                 indexr i vs = Some v /\ valh_type vvs vs v TF). eauto.
       destruct H1. destruct H1.
       eexists. split. eapply indexr_extend. eauto.
       inversion H4. subst.
       eapply v_tya. (* aenv is not constrained -- bit of a cheat?*)
Qed.


Lemma indexr_exists: forall H1 H2 GH TF i,
             wf_envh H1 H2 GH ->
             indexr i GH = Some TF ->
             exists v, indexr i H2 = Some v.
Proof.
  intros. induction H.
  - inversion H0.
  - unfold indexr.
    case_eq (beq_nat i (length vs)); intros E.
    + eexists. reflexivity.
    + eapply IHwf_envh. unfold indexr in H0.
      assert (length vs = length ts) as A. {
        eapply wfh_length. eauto.
      }
      rewrite <- A in H0. rewrite E in H0. unfold indexr. apply H0.
Qed.

Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T n,
      val_type venv v T n ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.



Lemma stpd2_trans_aux: forall n, forall G1 G2 G3 T1 T2 T3 H n1,
  stp2 MAX false G1 T1 G2 T2 H n1 -> n1 < n ->
  stpd2 false G2 T2 G3 T3 H ->
  stpd2 false G1 T1 G3 T3 H.
Proof.
  intros n. induction n; intros; try omega; repeat eu; subst; inversion H0.
  - Case "wrapf". eapply stpd2_transf; eauto.
  - Case "transf". eapply stpd2_transf. eauto. eapply IHn. eauto. omega. eauto.
Qed.

Lemma sstpd2_trans_axiom_aux: forall n, forall G1 G2 G3 T1 T2 T3 H n1,
  stp2 0 false G1 T1 G2 T2 H n1 -> n1 < n ->
  sstpd2 false G2 T2 G3 T3 H ->
  sstpd2 false G1 T1 G3 T3 H.
Proof.
  intros n. induction n; intros; try omega; repeat eu; subst; inversion H0.
  - Case "wrapf". eapply sstpd2_transf. eexists. eauto. eexists. eauto.
  - Case "transf". eapply sstpd2_transf. eexists. eauto. eapply IHn. eauto. omega. eexists. eauto.
Qed.

Lemma atpd2_trans_axiom_aux: forall n, forall G1 G2 G3 T1 T2 T3 H n1,
  stp2 1 false G1 T1 G2 T2 H n1 -> n1 < n ->
  atpd2 false G2 T2 G3 T3 H ->
  atpd2 false G1 T1 G3 T3 H.
Proof.
  intros n. induction n; intros; try omega; repeat eu; subst; inversion H0.
  - Case "wrapf". eapply atpd2_transf. eexists. eauto. eexists. eauto.
  - Case "transf". eapply atpd2_transf. eexists. eauto. eapply IHn. eauto. omega. eexists. eauto.
Qed.

Lemma stpd2_trans: forall G1 G2 G3 T1 T2 T3 H,
  stpd2 false G1 T1 G2 T2 H ->
  stpd2 false G2 T2 G3 T3 H ->
  stpd2 false G1 T1 G3 T3 H.
Proof. intros. repeat eu. eapply stpd2_trans_aux; eauto. Qed.

Lemma sstpd2_trans_axiom: forall G1 G2 G3 T1 T2 T3 H,
  sstpd2 false G1 T1 G2 T2 H ->
  sstpd2 false G2 T2 G3 T3 H ->
  sstpd2 false G1 T1 G3 T3 H.
Proof. intros. repeat eu.
       eapply sstpd2_trans_axiom_aux; eauto.
       eexists. eauto.
Qed.

Lemma atpd2_trans_axiom: forall G1 G2 G3 T1 T2 T3 H,
  atpd2 false G1 T1 G2 T2 H ->
  atpd2 false G2 T2 G3 T3 H ->
  atpd2 false G1 T1 G3 T3 H.
Proof.
  intros. repeat eu. eapply atpd2_trans_axiom_aux; eauto. eexists. eauto.
Qed.

Lemma stp2_narrow_aux: forall n, forall m G1 T1 G2 T2 GH n0,
  stp2 MAX m G1 T1 G2 T2 GH n0 ->
  n0 <= n ->
  forall x GH1 GH0 GH' GX1 TX1 GX2 TX2,
    GH=GH1++[(x,(GX2,TX2))]++GH0 ->
    GH'=GH1++[(x,(GX1,TX1))]++GH0 ->
    stpd2 false GX1 TX1 GX2 TX2 ([(x,(GX1,TX1))]++GH0) ->
    stpd2 m G1 T1 G2 T2 GH'.
Proof.
  intros n.
  induction n.
  - Case "z". intros. inversion H0. subst. inversion H; eauto.
  - Case "s n". intros m G1 T1 G2 T2 GH n0 H NE. inversion H; subst;
      intros x0 GH1 GH0 GH' GX1 TX1 GX2 TX2 EGH EGH' HX; eauto.
    + SCase "top". eapply stpd2_top. eapply IHn; try eassumption. omega.
    + SCase "bot". eapply stpd2_bot. eapply IHn; try eassumption. omega.
    + SCase "fun". eapply stpd2_fun.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "mem". eapply stpd2_mem.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "sel1". eapply stpd2_sel1; try eassumption.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "selb1". eapply stpd2_selb1; try eassumption.
      eexists; eassumption.
      eapply IHn; try eassumption. omega.
    + SCase "sel2". eapply stpd2_sel2; try eassumption.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "selb2". eapply stpd2_selb2; try eassumption.
      eexists; eassumption.
      eapply IHn; try eassumption. omega.
    + SCase "selx". eapply stpd2_selx; try eassumption.
    + SCase "sela1".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        rewrite A2' in H1. inversion H1. subst.
        inversion HX as [nx HX'].
        eapply stpd2_sela1.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        apply beq_nat_true in E. rewrite E.
        change (S (length GH0)) with (length ([(x0, (GX1, TX1))]++GH0)).
        eapply stp2_closed1. eassumption.
        eapply stpd2_trans.
        eexists. eapply stp2_extendH_mult. eassumption.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_sela1. eapply A. assumption.
        eapply IHn; try eassumption. omega.
        eapply IHn; try eassumption. omega.
    + SCase "selab1".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x (GU ++ GL) = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        assert (Some (GX2,TX2) = Some (GX, TX)) as E2. {
          rewrite A2' in H1. apply H1.
        }
        inversion E2. subst.
        eapply stpd2_selab1.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        eapply stpd2_closed1 in HX. simpl in HX. eapply beq_nat_true in E. rewrite E. eapply HX.
        eassumption.
        instantiate (1:=([(x0, (GX1, TX1))]++GH0)). simpl. apply beq_nat_true in E. rewrite E. reflexivity.
        reflexivity.
        eapply stpd2_trans. eapply HX.
        eapply IHn; try eassumption. omega. rewrite app_nil_l.
        eapply proj2. eapply concat_same_length'. eassumption.
        eapply beq_nat_true in E. subst. eauto.
        simpl. reflexivity.
        eapply IHn; try eassumption. omega.
        reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. rewrite EGH in H1. eassumption.
        }
        simpl in EGH. simpl in EGH'. simpl in IHn. simpl in HX.
        case_eq (le_lt_dec (S (length GH0)) x); intros E' LE'.
        assert (exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ (x0, (GX2, TX2)) :: GH0) as EQGH. {
          eapply exists_GH1L. eassumption. eassumption. simpl. eassumption.
        }
        destruct EQGH as [GH1L [EQGH1 EQGL]].
        eapply stpd2_selab1 with (GH:=GH'). eapply A.
        eassumption. eassumption.
        instantiate (1:=GH1L ++ (x0, (GX1, TX1)) :: GH0).
        rewrite app_length. simpl.
        rewrite EQGL in H4. rewrite app_length in H4. simpl in H4. eassumption.
        instantiate (1:=GU). rewrite app_assoc. rewrite EQGH1 in EGH'. assumption.
        eapply IHn; try eassumption. omega. reflexivity.
        eapply IHn; try eassumption. omega.
        assert (exists GH0U, (x0, (GX2, TX2))::GH0 = GH0U ++ GL) as EQGH. {
          eapply exists_GH0U. eassumption. eassumption. simpl. eassumption.
        }
        destruct EQGH as [GH0U EQGH].
        destruct GH0U. simpl in EQGH.
        assert (length ((x0, (GX2, TX2))::GH0)=length GL) as Contra. {
          rewrite EQGH. reflexivity.
        }
        simpl in Contra. rewrite H4 in Contra. inversion Contra. apply beq_nat_false in E. omega.
        simpl in EQGH. inversion EQGH.
        eapply stpd2_selab1 with (GH:=GH'). eapply A.
        eassumption. eassumption. eassumption.
        rewrite H7 in EGH'. simpl in EGH'. instantiate (1:=GH1 ++ (x0, (GX1, TX1)) :: GH0U).
        rewrite <- app_assoc. simpl. eapply EGH'.
        eexists. eassumption.
        eapply IHn; try eassumption. omega.
    + SCase "selab2".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x (GU ++ GL) = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        assert (Some (GX2,TX2) = Some (GX, TX)) as E2. {
          rewrite A2' in H1. apply H1.
        }
        inversion E2. subst.
        eapply stpd2_selab2.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        eapply stpd2_closed1 in HX. simpl in HX. eapply beq_nat_true in E. rewrite E. eapply HX.
        eassumption.
        instantiate (1:=([(x0, (GX1, TX1))]++GH0)). simpl. apply beq_nat_true in E. rewrite E. reflexivity.
        reflexivity.
        eapply stpd2_trans. eapply HX.
        eapply IHn; try eassumption. omega. rewrite app_nil_l.
        eapply proj2. eapply concat_same_length'. eassumption.
        eapply beq_nat_true in E. subst. eauto.
        simpl. reflexivity. reflexivity.
        eapply IHn; try eassumption. omega.
        reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. rewrite EGH in H1. eassumption.
        }
        simpl in EGH. simpl in EGH'. simpl in IHn. simpl in HX.
        case_eq (le_lt_dec (S (length GH0)) x); intros E' LE'.
        assert (exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ (x0, (GX2, TX2)) :: GH0) as EQGH. {
          eapply exists_GH1L. eassumption. eassumption. simpl. eassumption.
        }
        destruct EQGH as [GH1L [EQGH1 EQGL]].
        eapply stpd2_selab2 with (GH:=GH'). eapply A.
        eassumption. eassumption.
        instantiate (1:=GH1L ++ (x0, (GX1, TX1)) :: GH0).
        rewrite app_length. simpl.
        rewrite EQGL in H4. rewrite app_length in H4. simpl in H4. eassumption.
        instantiate (1:=GU). rewrite app_assoc. rewrite EQGH1 in EGH'. assumption.
        eapply IHn; try eassumption. omega. reflexivity. reflexivity.
        eapply IHn; try eassumption. omega.
        assert (exists GH0U, (x0, (GX2, TX2))::GH0 = GH0U ++ GL) as EQGH. {
          eapply exists_GH0U. eassumption. eassumption. simpl. eassumption.
        }
        destruct EQGH as [GH0U EQGH].
        destruct GH0U. simpl in EQGH.
        assert (length ((x0, (GX2, TX2))::GH0)=length GL) as Contra. {
          rewrite EQGH. reflexivity.
        }
        simpl in Contra. rewrite H4 in Contra. inversion Contra. apply beq_nat_false in E. omega.
        simpl in EQGH. inversion EQGH.
        eapply stpd2_selab2 with (GH:=GH'). eapply A.
        eassumption. eassumption. eassumption.
        rewrite H7 in EGH'. simpl in EGH'. instantiate (1:=GH1 ++ (x0, (GX1, TX1)) :: GH0U).
        rewrite <- app_assoc. simpl. eapply EGH'.
        eexists. eassumption. reflexivity.
        eapply IHn; try eassumption. omega.
    + SCase "sela2".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        rewrite A2' in H1. inversion H1. subst.
        inversion HX as [nx HX'].
        eapply stpd2_sela2.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        apply beq_nat_true in E. rewrite E.
        change (S (length GH0)) with (length ([(x0, (GX1, TX1))]++GH0)).
        eapply stp2_closed1. eassumption.
        eapply stpd2_trans.
        eexists. eapply stp2_extendH_mult. eassumption.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_sela2. eapply A. assumption.
        eapply IHn; try eassumption. omega.
        eapply IHn; try eassumption. omega.
    + SCase "selax".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        rewrite A2' in H1. inversion H1. subst.
        inversion HX as [nx HX'].
        eapply stpd2_selax.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_selax. eapply A.
    + SCase "all".
      assert (length GH = length GH') as A. {
        subst. clear.
        induction GH1.
        - simpl. reflexivity.
        - simpl. simpl in IHGH1. rewrite IHGH1. reflexivity.
      }
      eapply stpd2_all.
      eapply IHn; try eassumption. omega.
      rewrite <- A. assumption. rewrite <- A. assumption.
      rewrite <- A. subst.
      eapply IHn with (GH1:=(0, (G1, T0)) :: GH1); try eassumption. omega.
      simpl. reflexivity. simpl. reflexivity.
      rewrite <- A. subst.
      eapply IHn with (GH1:=(0, (G2, T4)) :: GH1); try eassumption. omega.
      simpl. reflexivity. simpl. reflexivity.
    + SCase "bind".
      assert (length GH = length GH') as A. {
        subst. clear.
        induction GH1.
        - simpl. reflexivity.
        - simpl. simpl in IHGH1. rewrite IHGH1. reflexivity.
      }
      eapply stpd2_bind.
      assert (closed 1 (length GH) T0 -> closed 1 (length GH') T0) as C0. {
        rewrite A. intros P. apply P.
      }
      apply C0; assumption.
      assert (closed 1 (length GH) T3 -> closed 1 (length GH') T3) as C3. {
        rewrite A. intros P. apply P.
      }
      apply C3; assumption.
      assert (
          stpd2 false G2 (open (TSelH (length GH)) T3) G2
                (open (TSelH (length GH)) T3)
                ((0, (G2, open (TSelH (length GH)) T3)) :: GH')
                ->
          stpd2 false G2 (open (TSelH (length GH')) T3) G2
                (open (TSelH (length GH')) T3)
                ((0, (G2, open (TSelH (length GH')) T3)) :: GH')) as CS1. {
        rewrite A. intros P. apply P.
      }
      apply CS1. eapply IHn. eassumption. omega.
      instantiate (5:=(0, (G2, open (TSelH (length GH)) T3)) :: GH1).
      subst. simpl. reflexivity. subst. simpl. reflexivity.
      assumption.
      assert (
          stpd2 false G1 (open (TSelH (length GH)) T0) G2
                (open (TSelH (length GH)) T3)
                ((0, (G1, open (TSelH (length GH)) T0)) :: GH')
                ->
          stpd2 false G1 (open (TSelH (length GH')) T0) G2
                (open (TSelH (length GH')) T3)
                ((0, (G1, open (TSelH (length GH')) T0)) :: GH')
        ) as CS2. {
        rewrite A. intros P. apply P.
      }
      apply CS2. eapply IHn. eassumption. omega.
      instantiate (5:=(0, (G1, open (TSelH (length GH)) T0)) :: GH1).
      subst. simpl. reflexivity. subst. simpl. reflexivity.
      assumption.
    + SCase "and11".
      eapply stpd2_and11.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "and12".
      eapply stpd2_and12.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "and2".
      eapply stpd2_and2.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "wrapf".
      eapply stpd2_wrapf.
      eapply IHn; try eassumption. omega.
    + SCase "transf".
      eapply stpd2_transf.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
Grab Existential Variables.
apply 0. apply 0. apply 0.
Qed.

Lemma stpd2_narrow: forall x G1 G2 G3 G4 T1 T2 T3 T4,
  stpd2 false G1 T1 G2 T2 [] -> (* careful about H! *)
  stpd2 false G3 T3 G4 T4 ((x,(G2,T2))::[]) ->
  stpd2 false G3 T3 G4 T4 ((x,(G1,T1))::[]).
Proof.
  intros. inversion H0 as [n H'].
  eapply (stp2_narrow_aux n) with (GH1:=[]) (GH0:=[]). eapply H'. omega.
  simpl. reflexivity. reflexivity.
  eapply stpd2_extendH. assumption.
Qed.


Lemma atpd2_to_stpd2: forall m0 G1 G2 T1 T2 GH,
  atpd2 m0 G1 T1 G2 T2 GH ->
  stpd2 m0 G1 T1 G2 T2 GH.
Proof.
  intros. destruct H as [n H]. remember 1 as m. induction H;
    try solve [eexists; eauto 2];
    try solve [inversion Heqm];
    try solve [specialize (IHstp2 Heqm); destruct IHstp2; eexists; econstructor; eauto 2];
    try solve [specialize (IHstp2_1 Heqm); destruct IHstp2_1;
               specialize (IHstp2_2 Heqm); destruct IHstp2_2;
               eexists; econstructor; eauto 2].
  - Case "selx".
    eexists. eapply stp2_selx; eauto.
  - Case "selab1".
    specialize (IHstp2_1 Heqm); destruct IHstp2_1;
    specialize (IHstp2_2 Heqm); destruct IHstp2_2.
    eexists. eapply stp2_selab1; eauto.
   - Case "sela2".
    specialize (IHstp2_1 Heqm); destruct IHstp2_1;
    specialize (IHstp2_2 Heqm); destruct IHstp2_2.
    eexists. eapply stp2_sela2; eauto.
  - Case "selabx".
    eexists. eapply stp2_selax; eauto.
  - Case "and12".
    specialize (IHstp2_1 Heqm); destruct IHstp2_1;
    specialize (IHstp2_2 Heqm); destruct IHstp2_2.
    eexists. eapply stp2_and12; eauto.
  - Case "transf".
    specialize (IHstp2_1 Heqm); destruct IHstp2_1;
    specialize (IHstp2_2 Heqm); destruct IHstp2_2.
    eexists. eapply stp2_transf; eauto.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

(* begin atpd helpers *)
Lemma atpd2_topx: forall G1 G2 GH,
    atpd2 true G1 TTop G2 TTop GH.
Proof. intros. repeat exists (S 0). eauto. Qed.
Lemma atpd2_botx: forall G1 G2 GH,
    atpd2 true G1 TBot G2 TBot GH.
Proof. intros. repeat exists (S 0). eauto. Qed.
Lemma atpd2_top: forall G1 G2 GH T,
    atpd2 true G1 T G1 T GH ->
    atpd2 true G1 T G2 TTop GH.
Proof. intros. repeat eu. eexists. econstructor. eauto. Qed.
Lemma atpd2_bot: forall G1 G2 GH T,
    atpd2 true G2 T G2 T GH ->
    atpd2 true G1 TBot G2 T GH.
Proof. intros. repeat eu. eexists. econstructor. eauto. Qed.
Lemma atpd2_bool: forall G1 G2 GH,
    atpd2 true G1 TBool G2 TBool GH.
Proof. intros. repeat exists (S 0). eauto. Qed.
Lemma atpd2_fun: forall G1 G2 GH l T11 T12 T21 T22,
    stpd2 false G2 T21 G1 T11 GH ->
    stpd2 false G1 T12 G2 T22 GH ->
    atpd2 true G1 (TFun l T11 T12) G2 (TFun l T21 T22) GH.
Proof. intros. repeat eu. eexists. econstructor; eauto. Qed.
Lemma atpd2_mem: forall G1 G2 GH T11 T12 T21 T22,
    atpd2 false G2 T21 G1 T11 GH ->
    atpd2 false G1 T12 G2 T22 GH ->
    atpd2 true G1 (TMem T11 T12) G2 (TMem T21 T22) GH.
Proof. intros. repeat eu. eauto. unfold atpd2. eexists. eapply stp2_mem2; eauto. Qed.

Lemma atpd2_sel1: forall G1 G2 GX TX x T2 GH v nv,
    index x G1 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    atpd2 false GX TX G2 (TMem TBot T2) GH ->
    atpd2 true G2 T2 G2 T2 GH ->
    atpd2 true G1 (TSel x) G2 T2 GH.
Proof. intros. repeat eu. eexists. eapply stp2_sel1; eauto. Qed.

Lemma atpd2_sel2: forall G1 G2 GX TX x T1 GH v nv,
    index x G2 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    atpd2 false GX TX G1 (TMem T1 TTop) GH ->
    atpd2 true G1 T1 G1 T1 GH ->
    atpd2 true G1 T1 G2 (TSel x) GH.
Proof. intros. repeat eu. eexists. eapply stp2_sel2; eauto. Qed.

Lemma atpd2_selx: forall G1 G2 x1 x2 GH v,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    atpd2 true G1 (TSel x1) G2 (TSel x2) GH.
Proof. intros. eauto. exists (S 0). eapply stp2_selx; eauto. Qed.

Lemma atpd2_sela1: forall G1 G2 GX TX x T2 GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    atpd2 false GX TX G2 (TMem TBot T2) GH ->
    atpd2 true G2 T2 G2 T2 GH ->
    atpd2 true G1 (TSelH x) G2 T2 GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_sela1; eauto. Qed.

Lemma atpd2_sela2: forall G1 G2 GX TX x T1 GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    atpd2 false GX TX G1 (TMem T1 TTop) GH ->
    atpd2 true G1 T1 G1 T1 GH ->
    atpd2 true G1 T1 G2 (TSelH x) GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_sela2; eauto. Qed.


Lemma atpd2_selax: forall G1 G2 GX TX x GH,
    indexr x GH = Some (GX, TX) ->
    atpd2 true G1 (TSelH x) G2 (TSelH x) GH.
Proof. intros. exists (S 0). eauto. Qed.


Lemma atpd2_selab1: forall G1 G2 GX TX x T2 GH GU GL,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem TBot T2)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    atpd2 false GX TX G2 (TBind (TMem TBot T2)) GL ->
    atpd2 true G2 (open (TSelH x) T2) G2 (open (TSelH x) T2) GH ->
    atpd2 true G1 (TSelH x) G2 (open (TSelH x) T2) GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_selab1; eauto. Qed.

Lemma atpd2_selab2: forall G1 G2 GX TX x T1 T1' GH GU GL,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem T1 TTop)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    atpd2 false GX TX G1 (TBind (TMem T1 TTop)) GL ->
    T1' = (open (TSelH x) T1) ->
    atpd2 true G1 T1' G1 T1' GH ->
    atpd2 true G1 T1' G2 (TSelH x) GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_selab2; eauto. Qed.

Lemma atpd2_all: forall G1 G2 T1 T2 T3 T4 GH,
    stpd2 false G2 T3 G1 T1 GH ->
    closed 1 (length GH) T2 ->
    closed 1 (length GH) T4 ->
    stpd2 false G1 (open (TSelH (length GH)) T2) G1 (open (TSelH (length GH)) T2) ((0,(G1, T1))::GH) ->
    stpd2 false G1 (open (TSelH (length GH)) T2) G2 (open (TSelH (length GH)) T4) ((0,(G2, T3))::GH) ->
    atpd2 true G1 (TAll T1 T2) G2 (TAll T3 T4) GH.
Proof. intros. repeat eu. eexists. eapply stp2_all; eauto. Qed.

Lemma atpd2_bind: forall G1 G2 T1 T2 GH,
    closed 1 (length GH) T1 ->
    closed 1 (length GH) T2 ->
    atpd2 false G2 (open (TSelH (length GH)) T2) G2 (open (TSelH (length GH)) T2) ((0,(G2, open (TSelH (length GH)) T2))::GH) ->
    atpd2 false G1 (open (TSelH (length GH)) T1) G2 (open (TSelH (length GH)) T2) ((0,(G1, open (TSelH (length GH)) T1))::GH) ->
    atpd2 true G1 (TBind T1) G2 (TBind T2) GH.
Proof. intros. repeat eu. eauto. unfold atpd2. eexists. eapply stp2_bindb; eauto. Qed.

Lemma atpd2_and11: forall G1 G2 GH T1 T2 T,
    atpd2 true G1 T1 G2 T GH ->
    atpd2 true G1 T2 G1 T2 GH ->
    atpd2 true G1 (TAnd T1 T2) G2 T GH.
Proof. intros. repeat eu. eexists. eapply stp2_and11; eauto. Qed.
Lemma atpd2_and12: forall G1 G2 GH T1 T2 T,
    atpd2 true G1 T2 G2 T GH ->
    atpd2 true G1 T1 G1 T1 GH ->
    atpd2 true G1 (TAnd T1 T2) G2 T GH.
Proof. intros. repeat eu. eexists. eapply stp2_and12; eauto. Qed.
Lemma atpd2_and2: forall G1 G2 GH T1 T2 T,
    atpd2 false G1 T G2 T1 GH ->
    atpd2 false G1 T G2 T2 GH ->
    atpd2 true G1 T G2 (TAnd T1 T2) GH.
Proof. intros. repeat eu. eexists. eapply stp2_and2; eauto. Qed.

Lemma atpd2_wrapf: forall G1 G2 T1 T2 GH,
    atpd2 true G1 T1 G2 T2 GH ->
    atpd2 false G1 T1 G2 T2 GH.
Proof. intros. repeat eu. eexists. eapply stp2_wrapf; eauto. Qed.

(* end atpd helpers *)

Lemma atpd2_narrow_aux: forall n, forall m G1 T1 G2 T2 GH n0,
  stp2 1 m G1 T1 G2 T2 GH n0 ->
  n0 <= n ->
  forall x GH1 GH0 GH' GX1 TX1 GX2 TX2,
    GH=GH1++[(x,(GX2,TX2))]++GH0 ->
    GH'=GH1++[(x,(GX1,TX1))]++GH0 ->
    atpd2 false GX1 TX1 GX2 TX2 ([(x,(GX1,TX1))]++GH0) ->
    atpd2 m G1 T1 G2 T2 GH'.
Proof.
  intros n.
  induction n.
  - Case "z". intros. inversion H0. subst. inversion H; eauto.
  - Case "s n". intros m G1 T1 G2 T2 GH n0 H NE. inversion H; subst;
    intros x0 GH1 GH0 GH' GX1 TX1 GX2 TX2 EGH EGH' HX.
    + SCase "topx". eapply atpd2_topx.
    + SCase "botx". eapply atpd2_botx.
    + SCase "top". eapply atpd2_top. eapply IHn; try eassumption. omega.
    + SCase "bot". eapply atpd2_bot. eapply IHn; try eassumption. omega.
    + SCase "bool". eapply atpd2_bool.
    + SCase "fun". eapply atpd2_to_stpd2 in HX. eapply atpd2_fun.
      eapply stp2_narrow_aux; eauto.
      eapply stp2_narrow_aux; eauto.
    + SCase "mem". eapply atpd2_mem.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "sel1". eapply atpd2_sel1; try eassumption.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "sel2". eapply atpd2_sel2; try eassumption.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "selx". eapply atpd2_selx; try eassumption.
    + SCase "sela1".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        rewrite A2' in H1. inversion H1. subst.
        inversion HX as [nx HX'].
        eapply atpd2_sela1.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        apply beq_nat_true in E. rewrite E.
        change (S (length GH0)) with (length ([(x0, (GX1, TX1))]++GH0)).
        eapply stp2_closed1. eassumption.
        eapply atpd2_trans_axiom.
        eexists. eapply stp2_extendH_mult. eassumption.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply atpd2_sela1. eapply A. assumption.
        eapply IHn; try eassumption. omega.
        eapply IHn; try eassumption. omega.
    + SCase "selab1".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x (GU ++ GL) = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        assert (Some (GX2,TX2) = Some (GX, TX)) as E2. {
          rewrite A2' in H1. apply H1.
        }
        inversion E2. subst.
        eapply atpd2_selab1.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        eapply atpd2_closed1 in HX. simpl in HX. eapply beq_nat_true in E. rewrite E. eapply HX.
        eassumption.
        instantiate (1:=([(x0, (GX1, TX1))]++GH0)). simpl. apply beq_nat_true in E. rewrite E. reflexivity.
        reflexivity.
        eapply atpd2_trans_axiom. eapply HX.
        eapply IHn; try eassumption. omega. rewrite app_nil_l.
        eapply proj2. eapply concat_same_length'. eassumption.
        eapply beq_nat_true in E. subst. eauto.
        simpl. reflexivity.
        eapply IHn; try eassumption. omega.
        reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. rewrite EGH in H1. eassumption.
        }
        simpl in EGH. simpl in EGH'. simpl in IHn. simpl in HX.
        case_eq (le_lt_dec (S (length GH0)) x); intros E' LE'.
        assert (exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ (x0, (GX2, TX2)) :: GH0) as EQGH. {
          eapply exists_GH1L. eassumption. eassumption. simpl. eassumption.
        }
        destruct EQGH as [GH1L [EQGH1 EQGL]].
        eapply atpd2_selab1 with (GH:=GH'). eapply A.
        eassumption. eassumption.
        instantiate (1:=GH1L ++ (x0, (GX1, TX1)) :: GH0).
        rewrite app_length. simpl.
        rewrite EQGL in H4. rewrite app_length in H4. simpl in H4. eassumption.
        instantiate (1:=GU). rewrite app_assoc. rewrite EQGH1 in EGH'. assumption.
        eapply IHn; try eassumption. omega. reflexivity.
        eapply IHn; try eassumption. omega.
        assert (exists GH0U, (x0, (GX2, TX2))::GH0 = GH0U ++ GL) as EQGH. {
          eapply exists_GH0U. eassumption. eassumption. simpl. eassumption.
        }
        destruct EQGH as [GH0U EQGH].
        destruct GH0U. simpl in EQGH.
        assert (length ((x0, (GX2, TX2))::GH0)=length GL) as Contra. {
          rewrite EQGH. reflexivity.
        }
        simpl in Contra. rewrite H4 in Contra. inversion Contra. apply beq_nat_false in E. omega.
        simpl in EQGH. inversion EQGH.
        eapply atpd2_selab1 with (GH:=GH'). eapply A.
        eassumption. eassumption. eassumption.
        rewrite H7 in EGH'. simpl in EGH'. instantiate (1:=GH1 ++ (x0, (GX1, TX1)) :: GH0U).
        rewrite <- app_assoc. simpl. eapply EGH'.
        eexists. eassumption.
        eapply IHn; try eassumption. omega.
    + SCase "selab2".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x (GU ++ GL) = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        assert (Some (GX2,TX2) = Some (GX, TX)) as E2. {
          rewrite A2' in H1. apply H1.
        }
        inversion E2. subst.
        eapply atpd2_selab2.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        eapply atpd2_closed1 in HX. simpl in HX. eapply beq_nat_true in E. rewrite E. eapply HX.
        eassumption.
        instantiate (1:=([(x0, (GX1, TX1))]++GH0)). simpl. apply beq_nat_true in E. rewrite E. reflexivity.
        reflexivity.
        eapply atpd2_trans_axiom. eapply HX.
        eapply IHn; try eassumption. omega. rewrite app_nil_l.
        eapply proj2. eapply concat_same_length'. eassumption.
        eapply beq_nat_true in E. subst. eauto.
        simpl. reflexivity. reflexivity.
        eapply IHn; try eassumption. omega.
        reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. rewrite EGH in H1. eassumption.
        }
        simpl in EGH. simpl in EGH'. simpl in IHn. simpl in HX.
        case_eq (le_lt_dec (S (length GH0)) x); intros E' LE'.
        assert (exists GH1L, GH1 = GU ++ GH1L /\ GL = GH1L ++ (x0, (GX2, TX2)) :: GH0) as EQGH. {
          eapply exists_GH1L. eassumption. eassumption. simpl. eassumption.
        }
        destruct EQGH as [GH1L [EQGH1 EQGL]].
        eapply atpd2_selab2 with (GH:=GH'). eapply A.
        eassumption. eassumption.
        instantiate (1:=GH1L ++ (x0, (GX1, TX1)) :: GH0).
        rewrite app_length. simpl.
        rewrite EQGL in H4. rewrite app_length in H4. simpl in H4. eassumption.
        instantiate (1:=GU). rewrite app_assoc. rewrite EQGH1 in EGH'. assumption.
        eapply IHn; try eassumption. omega. reflexivity. reflexivity.
        eapply IHn; try eassumption. omega.
        assert (exists GH0U, (x0, (GX2, TX2))::GH0 = GH0U ++ GL) as EQGH. {
          eapply exists_GH0U. eassumption. eassumption. simpl. eassumption.
        }
        destruct EQGH as [GH0U EQGH].
        destruct GH0U. simpl in EQGH.
        assert (length ((x0, (GX2, TX2))::GH0)=length GL) as Contra. {
          rewrite EQGH. reflexivity.
        }
        simpl in Contra. rewrite H4 in Contra. inversion Contra. apply beq_nat_false in E. omega.
        simpl in EQGH. inversion EQGH.
        eapply atpd2_selab2 with (GH:=GH'). eapply A.
        eassumption. eassumption. eassumption.
        rewrite H7 in EGH'. simpl in EGH'. instantiate (1:=GH1 ++ (x0, (GX1, TX1)) :: GH0U).
        rewrite <- app_assoc. simpl. eapply EGH'.
        eexists. eassumption. reflexivity.
        eapply IHn; try eassumption. omega.
    + SCase "sela2".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        rewrite A2' in H1. inversion H1. subst.
        inversion HX as [nx HX'].
        eapply atpd2_sela2.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        apply beq_nat_true in E. rewrite E.
        change (S (length GH0)) with (length ([(x0, (GX1, TX1))]++GH0)).
        eapply stp2_closed1. eassumption.
        eapply atpd2_trans_axiom.
        eexists. eapply stp2_extendH_mult. eassumption.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply atpd2_sela2. eapply A. assumption.
        eapply IHn; try eassumption. omega.
        eapply IHn; try eassumption. omega.
    + SCase "selax".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        rewrite A2' in H1. inversion H1. subst.
        inversion HX as [nx HX'].
        eapply atpd2_selax.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply atpd2_selax. eapply A.
    + SCase "all".
      assert (length GH = length GH') as A. {
        subst. clear.
        induction GH1.
        - simpl. reflexivity.
        - simpl. simpl in IHGH1. rewrite IHGH1. reflexivity.
      }
      eapply atpd2_to_stpd2 in HX.
      eapply atpd2_all.
      eapply stp2_narrow_aux; eauto.
      rewrite <- A. assumption. rewrite <- A. assumption.
      rewrite <- A. subst.
      eapply stp2_narrow_aux with (GH1:=(0, (G1, T0)) :: GH1); try eassumption.
      simpl. reflexivity. simpl. reflexivity. reflexivity.
      rewrite <- A. subst.
      eapply stp2_narrow_aux with (GH1:=(0, (G2, T4)) :: GH1); try eassumption.
      eauto. simpl. reflexivity. reflexivity.
    + SCase "bind".
      assert (length GH = length GH') as A. {
        subst. clear.
        induction GH1.
        - simpl. reflexivity.
        - simpl. simpl in IHGH1. rewrite IHGH1. reflexivity.
      }
      eapply atpd2_bind.
      assert (closed 1 (length GH) T0 -> closed 1 (length GH') T0) as C0. {
        rewrite A. intros P. apply P.
      }
      apply C0; assumption.
      assert (closed 1 (length GH) T3 -> closed 1 (length GH') T3) as C3. {
        rewrite A. intros P. apply P.
      }
      apply C3; assumption.
      assert (
          atpd2 false G2 (open (TSelH (length GH)) T3) G2
                (open (TSelH (length GH)) T3)
                ((0, (G2, open (TSelH (length GH)) T3)) :: GH')
                ->
          atpd2 false G2 (open (TSelH (length GH')) T3) G2
                (open (TSelH (length GH')) T3)
                ((0, (G2, open (TSelH (length GH')) T3)) :: GH')) as CS1. {
        rewrite A. intros P. apply P.
      }
      apply CS1. eapply IHn. eassumption. omega.
      instantiate (5:=(0, (G2, open (TSelH (length GH)) T3)) :: GH1).
      subst. simpl. reflexivity. subst. simpl. reflexivity.
      assumption.
      assert (
          atpd2 false G1 (open (TSelH (length GH)) T0) G2
                (open (TSelH (length GH)) T3)
                ((0, (G1, open (TSelH (length GH)) T0)) :: GH')
                ->
          atpd2 false G1 (open (TSelH (length GH')) T0) G2
                (open (TSelH (length GH')) T3)
                ((0, (G1, open (TSelH (length GH')) T0)) :: GH')
        ) as CS2. {
        rewrite A. intros P. apply P.
      }
      apply CS2. eapply IHn. eassumption. omega.
      instantiate (5:=(0, (G1, open (TSelH (length GH)) T0)) :: GH1).
      subst. simpl. reflexivity. subst. simpl. reflexivity.
      assumption.
    + SCase "and11".
      eapply atpd2_and11.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "and12".
      eapply atpd2_and12.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "and2".
      eapply atpd2_and2.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "wrapf".
      eapply atpd2_wrapf.
      eapply IHn; try eassumption. omega.
    + SCase "transf".
      eapply atpd2_transf.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
Qed.

Lemma atpd2_narrow: forall x G1 G2 G3 G4 T1 T2 T3 T4 H,
  atpd2 false G1 T1 G2 T2 ((x,(G1,T1))::H) -> (* careful about H! *)
  atpd2 false G3 T3 G4 T4 ((x,(G2,T2))::H) ->
  atpd2 false G3 T3 G4 T4 ((x,(G1,T1))::H).
Proof.
  intros. inversion H1 as [n H'].
  eapply (atpd2_narrow_aux n) with (GH1:=[]).
  eapply H'. omega.
  simpl. reflexivity. simpl. reflexivity.
  assumption.
Qed.


Lemma sstpd2_trans_aux: forall n, forall m G1 G2 G3 T1 T2 T3 n1,
  stp2 0 m G1 T1 G2 T2 nil n1 -> n1 < n ->
  sstpd2 true G2 T2 G3 T3 nil ->
  sstpd2 true G1 T1 G3 T3 nil.
Proof.
  intros n. induction n; intros; try omega. eu.
  inversion H.
  - Case "topx". subst. inversion H1.
    + SCase "topx". eexists. eauto.
    + SCase "top". eexists. eauto.
    + SCase "sel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem TTop TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eapply stp2_topx.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "botx". subst. inversion H1.
    + SCase "botx". eexists. eauto.
    + SCase "top". eexists. eauto.
    + SCase "?". eexists. eauto.
    + SCase "sel2".
      assert (sstpd2 false GX' TX' G1 (TMem TBot TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf; eapply stp2_botx.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "top". subst. inversion H1.
    + SCase "topx". eexists. eauto.
    + SCase "top". eexists. eauto.
    + SCase "sel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem T1 TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eapply stp2_top. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "bot". subst.
    apply stp2_reg2 in H1. inversion H1 as [n1' H1'].
    exists (S n1'). apply stp2_bot. apply H1'.
  - Case "bool". subst. inversion H1.
    + SCase "top". eexists. eauto.
    + SCase "bool". eexists. eauto.
    + SCase "sel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem TBool TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eapply stp2_bool.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "fun". subst. inversion H1.
    + SCase "top".
      assert (stpd2 false G1 T0 G1 T0 []) as A0 by solve [eapply stpd2_wrapf; eapply stp2_reg2; eassumption].
      inversion A0 as [na0 HA0].
      assert (stpd2 false G1 T4 G1 T4 []) as A4 by solve [eapply stpd2_wrapf; eapply stp2_reg1; eassumption].
      inversion A4 as [na4 HA4].
      eexists. eapply stp2_top. subst. eapply stp2_fun.
      eassumption. eassumption.
    + SCase "fun". subst.
      assert (stpd2 false G3 T7 G1 T0 []) as A by solve [eapply stpd2_trans; eauto].
      inversion A as [na A'].
      assert (stpd2 false G1 T4 G3 T8 []) as B by solve [eapply stpd2_trans; eauto].
      inversion B as [nb B'].
      eexists. eapply stp2_fun. apply A'. apply B'.
    + SCase "sel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem (TFun l T0 T4) TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "mem". subst. inversion H1.
    + SCase "top".
      apply stp2_reg1 in H. inversion H. eexists. eapply stp2_top. eassumption.
    + SCase "mem". subst.
      assert (sstpd2 false G3 T7 G1 T0 []) as A. {
        eapply sstpd2_trans_axiom; eexists; eauto.
      }
      inversion A as [na A'].
      assert (sstpd2 true G1 T4 G3 T8 []) as B. {
        eapply IHn. eassumption. omega. eexists. eassumption.
      }
      inversion B as [nb B'].
      eexists. eapply stp2_mem. apply A'. apply B'.
    + SCase "sel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem (TMem T0 T4) TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "ssel1". subst.
    assert (sstpd2 true ((fresh GX, vty GX TX) :: GX) (open (TSel (fresh GX)) TX) G3 T3 []). eapply IHn. eauto. omega. eexists. eapply H1.
    assert (sstpd2 false GX' TX' G3 (TMem TBot T3) []). {
      eapply sstpd2_wrapf. eapply IHn. eassumption. omega.
      eexists. eapply stp2_mem.
      eapply stp2_wrapf. eapply stp2_botx.
      eapply H1.
    }
    repeat eu.
    eexists. eapply stp2_strong_sel1; eauto.
  - Case "ssel2". subst. inversion H1.
    + SCase "top". subst.
      apply stp2_reg1 in H6. inversion H6.
      eexists. eapply stp2_top. eassumption.
    + SCase "ssel1".  (* interesting one *)
      subst. rewrite H8 in H2. inversion H2. subst.
      eapply IHn. eapply H6. omega. eexists. eauto.
    + SCase "ssel2". subst.
      assert (sstpd2 false GX'0 TX'0 G1 (TMem T1 TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "sselx".
      subst. rewrite H2 in H8. inversion H8. subst.
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "sselx". subst. inversion H1.
    + SCase "top". subst.
      apply stp2_reg1 in H. inversion H.
      eexists. eapply stp2_top. eassumption.
    + SCase "ssel1".
      subst. rewrite H5 in H3. inversion H3. subst.
      eexists. eapply stp2_strong_sel1; eauto.
    + SCase "ssel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem (TSel x1) TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "sselx".
      subst. rewrite H5 in H3. inversion H3. subst.
      eexists. eapply stp2_strong_selx. eauto. eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "all". subst. inversion H1.
    + SCase "top".
      apply stp2_reg1 in H. inversion H.
      eexists. eapply stp2_top. eassumption.
    + SCase "ssel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem (TAll T0 T4) TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "all".
      subst.
      assert (stpd2 false G3 T7 G1 T0 []). eapply stpd2_trans. eauto. eauto.
      assert (stpd2 false G1 (open (TSelH (length ([]:aenv))) T4)
                          G3 (open (TSelH (length ([]:aenv))) T8)
                          [(0, (G3, T7))]).
        eapply stpd2_trans. eapply stpd2_narrow. eexists. eapply H9. eauto. eauto.
        repeat eu. eexists. eapply stp2_all. eauto. eauto. eauto. eauto. eapply H8.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "bind". subst. inversion H1; subst.
    + SCase "top".
      apply stp2_reg1 in H. inversion H.
      eexists. eapply stp2_top. eassumption.
    + SCase "ssel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem (TBind T0) TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "bind".
      subst.
      assert (atpd2 false G1 (open (TSelH 0) T0) G3 (open (TSelH 0) T2)
                    [(0, (G1, open (TSelH 0) T0))]) as A. {
        simpl in H5. simpl in H10.
        eapply atpd2_trans_axiom.
        eexists; eauto.
        change ([(0, (G1, open (TSelH 0) T0))]) with ((0, (G1, open (TSelH 0) T0))::[]).
        eapply atpd2_narrow. eexists. eassumption. eexists. eassumption.
      }
      inversion A.
      eexists. eapply stp2_bind; try eassumption.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "and11". subst. inversion H1; subst;
                         try solve [eapply IHn in H2;
                         [inversion H2; eexists; eapply stp2_and11; eassumption
                         | omega | eexists; eassumption]].
  - Case "and12". subst. inversion H1; subst;
                         try solve [eapply IHn in H2;
                         [inversion H2; eexists; eapply stp2_and12; eassumption
                         | omega | eexists; eassumption]].
  - Case "and2". subst. inversion H1; subst.
    + SCase "top". eapply stp2_reg1 in H. inversion H. eexists. eapply stp2_top; eassumption.
    + SCase "sel2".
      assert (sstpd2 false GX' TX' G1 (TMem T1 TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and11". subst. eapply IHn. apply H2. omega. eexists. eassumption.
    + SCase "and12". subst. eapply IHn. apply H3. omega. eexists. eassumption.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
  - Case "wrapf". subst. eapply IHn. eapply H2. omega. eexists. eauto.
  - Case "transf". subst. eapply IHn. eapply H2. omega. eapply IHn. eapply H3. omega. eexists. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma sstpd2_trans: forall G1 G2 G3 T1 T2 T3,
  sstpd2 true G1 T1 G2 T2 nil ->
  sstpd2 true G2 T2 G3 T3 nil ->
  sstpd2 true G1 T1 G3 T3 nil.
Proof. intros. repeat eu. eapply sstpd2_trans_aux; eauto. eexists. eauto. Qed.


Lemma sstpd2_untrans_aux: forall n, forall G1 G2 T1 T2 n1,
  stp2 0 false G1 T1 G2 T2 nil n1 -> n1 < n ->
  sstpd2 true G1 T1 G2 T2 nil.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst.
  - Case "wrapf". eexists. eauto.
  - Case "transf". eapply sstpd2_trans_aux. eapply H1. eauto. eapply IHn. eauto. omega.
Qed.

Lemma sstpd2_untrans: forall G1 G2 T1 T2,
  sstpd2 false G1 T1 G2 T2 nil ->
  sstpd2 true G1 T1 G2 T2 nil.
Proof. intros. repeat eu. eapply sstpd2_untrans_aux; eauto. Qed.



Lemma valtp_widen: forall vf H1 H2 T1 T2 n,
  val_type H1 vf T1 n ->
  sstpd2 true H1 T1 H2 T2 [] ->
  val_type H2 vf T2 n.
Proof.
  intros. inversion H; econstructor; eauto; eapply sstpd2_trans; eauto.
Qed.

Lemma restp_widen: forall vf H1 H2 T1 T2,
  res_type H1 vf T1 ->
  sstpd2 true H1 T1 H2 T2 [] ->
  res_type H2 vf T2.
Proof.
  intros. inversion H. eapply not_stuck. eapply valtp_widen; eauto.
Qed.

Lemma tand_shape: forall T1 T2,
  tand T1 T2 = TAnd T1 T2 \/ tand T1 T2 = T1.
Proof.
  intros. destruct T2; eauto.
Qed.

Lemma dcs_has_type_shape: forall G ds T,
  dcs_has_type G ds T ->
  T = TTop \/ (exists l T1 T2, T = TFun l T1 T2) \/
  (exists l T1 T2 ds' T', T = TAnd (TFun l T1 T2) T' /\
   dcs_has_type G ds' T').
Proof.
  intros. inversion H.
  - left. reflexivity.
  - subst. destruct dcs. inversion H1. subst.
    + right. left. eexists. eexists. eexists.
      simpl. reflexivity.
    + right. right. eexists. eexists. eexists. eexists. eexists.
      split. inversion H1. subst.
      destruct TS0; try solve [simpl; reflexivity].
      eassumption.
Qed.

Lemma dcs_tbind_aux: forall n, forall G ds venv1 T venv0 T0 n0,
  n0 <= n ->
  dcs_has_type G ds T ->
  stp2 0 true venv1 T venv0 (TBind T0) [] n0 ->
  False.
Proof.
  intros n. induction n.
  intros. inversion H1; omega.
  intros. eapply dcs_has_type_shape in H0.
  destruct H0. subst. inversion H1.
  destruct H0.
  destruct H0 as [l [T1' [T2' H0]]]. subst. inversion H1.
  destruct H0 as [l [T1' [T2' [ds' [T' [H0 HR]]]]]]. subst. inversion H1.
  subst. inversion H4.
  subst. eapply IHn in HR. apply HR. instantiate (1:=n1). omega. eassumption.
Qed.

Lemma dcs_tbind: forall G ds venv1 T venv0 T0 n0,
  dcs_has_type G ds T ->
  stp2 0 true venv1 T venv0 (TBind T0) [] n0 ->
  False.
Proof.
  intros. eapply dcs_tbind_aux. instantiate (1:=n0). eauto. eassumption. eassumption.
Qed.

Lemma dcs_tmem: forall n, forall G ds venv1 T venv0 T1 T2 n0,
  n0 <= n ->
  dcs_has_type G ds T ->
  stp2 0 true venv1 T venv0 (TMem T1 T2) [] n0 ->
  False.
Proof.
  intros n. induction n.
  intros. inversion H1; omega.
  intros. eapply dcs_has_type_shape in H0.
  destruct H0. subst. inversion H1.
  destruct H0.
  destruct H0 as [l [T1' [T2' H0]]]. subst. inversion H1.
  destruct H0 as [l [T1' [T2' [ds' [T' [H0 HR]]]]]]. subst. inversion H1.
  subst. inversion H4.
  subst. eapply IHn in HR. apply HR. instantiate (1:=n1). omega. eassumption.
Qed.

Lemma invert_typ: forall venv vx T1 T2 n,
  val_type venv vx (TMem T1 T2) n ->
  exists GX TX,
    vx = (vty GX TX) /\
    sstpd2 false venv T1 ((fresh GX,vty GX TX)::GX) (open (TSel (fresh GX)) TX) [] /\
    sstpd2 true ((fresh GX,vty GX TX)::GX) (open (TSel (fresh GX)) TX) venv T2 [].
Proof.
  intros. inversion H; ev; try solve by inversion. inversion H1.
  subst. inversion H2. subst. eexists. eexists. split. eauto. split. eexists. eauto. eexists. eauto.
  subst. assert False as A. {
    eapply dcs_tmem. instantiate (1:=x). eauto. eassumption. eassumption.
  }
  inversion A.
Qed.

Lemma inv_closed_open: forall j n TX T, closed j n (open_rec j TX T) -> closed j n TX -> closed (j+1) n T.
Proof.
  intros. generalize dependent j. induction T; try solve [
  intros; inversion H; subst; unfold closed; try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto].

  - Case "TSelB". intros. simpl.
    unfold open_rec in H.
    case_eq (beq_nat j i); intros E.

    + eapply beq_nat_true_iff in E. subst. eapply cl_selb. omega.

    + rewrite E in H. eapply closed_upgrade; eauto. omega.

  - intros. inversion H. subst. eapply cl_all.
    eapply IHT1. eassumption. eassumption.
    simpl. change (S (j+1)) with ((S j) + 1). eapply IHT2. eassumption.
    eapply closed_upgrade; eauto.
  - intros. inversion H. subst. eapply cl_bind.
    simpl. change (S (j+1)) with ((S j) + 1). eapply IHT. eassumption.
    eapply closed_upgrade; eauto.
Qed.


(* begin substitute *)

Lemma index_miss {X}: forall x x1 (B:X) A G,
  index x ((x1,B)::G) = A ->
  fresh G <= x1 ->
  x <> x1 ->
  index x G = A.
Proof.
  intros.
  unfold index in H.
  elim (le_xx (fresh G) x1 H0). intros.
  rewrite H2 in H.
  assert (beq_nat x x1 = false). eapply beq_nat_false_iff. eauto.
  rewrite H3 in H. eapply H.
Qed.

Lemma index_hit {X}: forall x x1 (B:X) A G,
  index x ((x1,B)::G) = Some A ->
  fresh G <= x1 ->
  x = x1 ->
  B = A.
Proof.
  intros.
  unfold index in H.
  elim (le_xx (fresh G) x1 H0). intros.
  rewrite H2 in H.
  assert (beq_nat x x1 = true). eapply beq_nat_true_iff. eauto.
  rewrite H3 in H. inversion H. eauto.
Qed.

Lemma index_hit2 {X}: forall x x1 (B:X) A G,
  fresh G <= x1 ->
  x = x1 ->
  B = A ->
  index x ((x1,B)::G) = Some A.
Proof.
  intros.
  unfold index.
  elim (le_xx (fresh G) x1 H). intros.
  rewrite H2.
  assert (beq_nat x x1 = true). eapply beq_nat_true_iff. eauto.
  rewrite H3. rewrite H1. eauto.
Qed.


Lemma indexr_miss {X}: forall x x1 (B:X) A G,
  indexr x ((x1,B)::G) = A ->
  x <> (length G)  ->
  indexr x G = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = false). eapply beq_nat_false_iff. eauto.
  rewrite H1 in H. eauto.
Qed.

Lemma indexr_hit {X}: forall x x1 (B:X) A G,
  indexr x ((x1,B)::G) = Some A ->
  x = length G ->
  B = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1 in H. inversion H. eauto.
Qed.


Lemma indexr_hit0: forall GH (GX0:venv) (TX0:ty),
      indexr 0 (GH ++ [(0,(GX0, TX0))]) =
      Some (GX0, TX0).
Proof.
  intros GH. induction GH.
  - intros. simpl. eauto.
  - intros. simpl. destruct a. simpl. rewrite app_length. simpl.
    assert (length GH + 1 = S (length GH)). omega. rewrite H.
    eauto.
Qed.





Hint Resolve beq_nat_true_iff.
Hint Resolve beq_nat_false_iff.


Lemma closed_no_open: forall T x l j,
  closed_rec j l T ->
  T = open_rec j x T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed_rec; rewrite <-IHclosed_rec; auto];
  try solve [compute; compute in IHclosed_rec1; compute in IHclosed_rec2; rewrite <-IHclosed_rec1; rewrite <-IHclosed_rec2; auto].

  Case "TSelB".
    unfold open_rec. assert (k <> i). omega.
    apply beq_nat_false_iff in H0.
    rewrite H0. auto.
Qed.


Lemma open_subst_commute: forall T2 TX (n:nat) x j,
closed j n TX ->
(open_rec j (TSelH x) (subst TX T2)) =
(subst TX (open_rec j (TSelH (x+1)) T2)).
Proof.
  intros T2 TX n. induction T2; intros; eauto.
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
  -  simpl. case_eq (beq_nat i 0); intros E. symmetry. eapply closed_no_open. eauto. simpl. eauto.
  - simpl. case_eq (beq_nat j i); intros E. simpl.
    assert (x+1<>0). omega. eapply beq_nat_false_iff in H0.
    assert (x=x+1-1). unfold id. omega.
    rewrite H0. eauto.
    simpl. eauto.
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eapply closed_upgrade. eauto. eauto. eauto.
  -  simpl. rewrite IHT2. eauto. eapply closed_upgrade. eauto. eauto.
  - simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
Qed.




Lemma closed_no_subst: forall T j TX,
   closed_rec j 0 T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
    try rewrite (IHT (S j) TX); eauto;
    try rewrite (IHT2 (S j) TX); eauto;
    try rewrite (IHT j TX); eauto;
    try rewrite (IHT1 j TX); eauto;
    try rewrite (IHT2 j TX); eauto.

  eapply closed_upgrade. eauto. eauto.
  eapply closed_upgrade. eauto. eauto.
  subst. omega.
  subst. eapply closed_upgrade. eassumption. omega.
Qed.

Lemma closed_subst: forall j n TX T, closed j (n+1) T -> closed 0 n TX -> closed j (n) (subst TX T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H; unfold closed; try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - Case "TSelH". simpl.
    case_eq (beq_nat i 0); intros E. eapply closed_upgrade. eapply closed_upgrade_free. eauto. omega. eauto. omega.
    econstructor. assert (i > 0). eapply beq_nat_false_iff in E. omega. omega.
Qed.


Lemma subst_open_commute_m: forall j n m TX T2, closed (j+1) (n+1) T2 -> closed 0 m TX ->
    subst TX (open_rec j (TSelH (n+1)) T2) = open_rec j (TSelH n) (subst TX T2).
Proof.
  intros. generalize dependent j. generalize dependent n.
  induction T2; intros; inversion H; simpl; eauto;
          try rewrite IHT2_1; try rewrite IHT2_2; try rewrite IHT2; eauto.

  - Case "TSelH". simpl. case_eq (beq_nat i 0); intros E.
    eapply closed_no_open. eapply closed_upgrade. eauto. omega.
    eauto.
  - Case "TSelB". simpl. case_eq (beq_nat j i); intros E.
    simpl. case_eq (beq_nat (n+1) 0); intros E2. eapply beq_nat_true_iff in E2. omega.
    assert (n+1-1 = n). omega. eauto.
    eauto.
Qed.

Lemma subst_open_commute: forall j n TX T2, closed (j+1) (n+1) T2 -> closed 0 0 TX ->
    subst TX (open_rec j (TSelH (n+1)) T2) = open_rec j (TSelH n) (subst TX T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_zero: forall j k TX T2, closed k 0 T2 ->
    subst TX (open_rec j (TSelH 0) T2) = open_rec j TX T2.
Proof.
  intros. generalize dependent k. generalize dependent j. induction T2; intros; inversion H; simpl; eauto; try rewrite (IHT2_1 _ k); try rewrite (IHT2_2 _ (S k)); try rewrite (IHT2_2 _ (S k)); try rewrite (IHT2 _ (S k)); try rewrite (IHT2 _ k); eauto.

  eapply closed_upgrade; eauto.
  eapply closed_upgrade; eauto.

  case_eq (beq_nat i 0); intros E. omega. omega.

  case_eq (beq_nat j i); intros E. eauto. eauto.

  eapply closed_upgrade; eauto.
Qed.



Lemma Forall2_length: forall A B f (G1:list A) (G2:list B),
                        Forall2 f G1 G2 -> length G1 = length G2.
Proof.
  intros. induction H.
  eauto.
  simpl. eauto.
Qed.


Lemma nosubst_intro: forall j T, closed j 0 T -> nosubst T.
Proof.
  intros. generalize dependent j. induction T; intros; inversion H; simpl; eauto.
  omega.
Qed.

Lemma nosubst_open: forall j TX T2, nosubst TX -> nosubst T2 -> nosubst (open_rec j TX T2).
Proof.
  intros. generalize dependent j. induction T2; intros; try inversion H0; simpl; eauto.

  case_eq (beq_nat j i); intros E. eauto. eauto.
Qed.

Lemma nosubst_open_rev: forall j TX T2, nosubst (open_rec j TX T2) -> nosubst TX -> nosubst T2.
Proof.
  intros. generalize dependent j. induction T2; intros; try inversion H; simpl in H; simpl; eauto.
Qed.

Lemma nosubst_zero_closed: forall j T2, nosubst (open_rec j (TSelH 0) T2) -> closed_rec (j+1) 0 T2 -> closed_rec j 0 T2.
Proof.
  intros. generalize dependent j. induction T2; intros; simpl in H; try destruct H; inversion H0; eauto.

  omega.
  econstructor.

  case_eq (beq_nat j i); intros E. rewrite E in H. destruct H. eauto.
  eapply beq_nat_false_iff in E. omega.
Qed.




(* substitution for one-env stp. not necessary, but good sanity check *)

Definition substt (UX: ty) (V: (id*ty)) :=
  match V with
    | (x,T) => (x-1,(subst UX T))
  end.

Lemma indexr_subst: forall GH0 x TX TX',
   indexr x (GH0 ++ [(0, TX)]) = Some (TX') ->
   x = 0 /\ TX = TX' \/
   x > 0 /\ indexr (x-1) (map (substt TX) GH0) = Some (subst TX TX').
Proof.
  intros GH0. induction GH0; intros.
  - simpl in H. case_eq (beq_nat x 0); intros E.
    + rewrite E in H. inversion H.
      left. split. eapply beq_nat_true_iff. eauto. eauto.
    + rewrite E in H. inversion H.
  -  destruct a. unfold id in H. remember ((length (GH0 ++ [(0, TX)]))) as L.
     case_eq (beq_nat x L); intros E.
     + assert (x = L). eapply beq_nat_true_iff. eauto.
       eapply indexr_hit in H.
       right. split. rewrite app_length in HeqL. simpl in HeqL. omega.
       assert ((x - 1) = (length (map (substt TX) GH0))).
       rewrite map_length. rewrite app_length in HeqL. simpl in HeqL. unfold id. omega.
       simpl.
       eapply beq_nat_true_iff in H1. unfold id in H1. unfold id. rewrite H1. subst. eauto. eauto. subst. eauto.
     + assert (x <> L). eapply beq_nat_false_iff. eauto.
       eapply indexr_miss in H. eapply IHGH0 in H.
       inversion H. left. eapply H1.
       right. inversion H1. split. eauto.
       simpl.
       assert ((x - 1) <> (length (map (substt TX) GH0))).
       rewrite app_length in HeqL. simpl in HeqL. rewrite map_length.
       unfold not. intros. subst L. unfold id in H0. unfold id in H2. unfold not in H0. eapply H0. unfold id in H4. rewrite <-H4. omega.
       eapply beq_nat_false_iff in H4. unfold id in H4. unfold id. rewrite H4.
       eauto. subst. eauto.
Qed.

(*
when and how we can replace with multiple environments:

stp2 G1 T1 G2 T2 (GH0 ++ [(0,vtya GX TX)])

1) T1 closed

   stp2 G1 T1 G2' T2' (subst GH0)

2) G1 contains (GX TX) at some index x1

   index x1 G1 = (GX TX)
   stp2 G (subst (TSel x1) T1) G2' T2'

3) G1 = GX <----- valid for Fsub, but not for DOT !

   stp2 G1 (subst TX T1) G2' T2'

4) G1 and GX unrelated

   stp2 ((GX,TX) :: G1) (subst (TSel (length G1)) T1) G2' T2'

*)






(* ---- two-env substitution. first define what 'compatible' types mean. ---- *)


Definition compat (GX:venv) (TX: ty) (TX': ty) (V: option vl) (G1:venv) (T1:ty) (T1':ty) :=
  (exists x1 v nv, index x1 G1 = Some v /\ V = Some v /\ GX = GX /\ val_type GX v (subst TX' TX) nv /\ T1' = (subst (TSel x1) T1)) \/
  (*  (G1 = GX /\ T1' = (subst TX T1)) \/ *)   (* this is doesn't work for DOT *)
  (* ((forall TA TB, TX <> TMem TA TB) /\ T1' = subst TTop T1) \/ *)(* can remove all term-only bindings -- may not be necessary after all since it applies nosubst *)
  (closed_rec 0 0 T1 /\ T1' = T1) \/ (* this one is for convenience: redundant with next *)
  (nosubst T1 /\ T1' = subst TTop T1).


Definition compat2 (GX:venv) (TX: ty) (TX': ty) (V: option vl) (p1:id*(venv*ty)) (p2:id*(venv*ty)) :=
  match p1, p2 with
      (n1,(G1,T1)), (n2,(G2,T2)) => n1=n2(*+1 disregarded*) /\ G1 = G2 /\ compat GX TX TX' V G1 T1 T2
  end.


Lemma closed_compat: forall GX TX TX' V GXX TXX TXX' j k,
  compat GX TX TX' V GXX TXX TXX' ->
  closed 0 k TX ->
  closed j (k+1) TXX ->
  closed j k TXX'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2. destruct H2. destruct H2. destruct H2. destruct H3.
    destruct H4. destruct H5. rewrite H6.
    eapply closed_subst. eauto. eauto.
  - destruct H2. rewrite H3.
    eapply closed_upgrade. eapply closed_upgrade_free. eauto. omega. omega.
  - rewrite H3.
    eapply closed_subst. eauto. eauto.
Qed.

Lemma closed_compat': forall GX TX TX' V GXX TXX TXX' j k,
  compat GX TX TX' V GXX TXX TXX' ->
  closed 0 k TX' ->
  closed j (k+1) TXX ->
  closed j k TXX'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2. destruct H2. destruct H2. destruct H2. destruct H3.
    destruct H4. destruct H5. rewrite H6.
    eapply closed_subst. eauto. eauto.
  - destruct H2. rewrite H3.
    eapply closed_upgrade. eapply closed_upgrade_free. eauto. omega. omega.
  - rewrite H3.
    eapply closed_subst. eauto. eauto.
Qed.

Lemma indexr_compat_miss0: forall GH GH' GX TX TX' V (GXX:venv) (TXX:ty) n,
      Forall2 (compat2 GX TX TX' V) GH GH' ->
      indexr (n+1) (GH ++ [(0,(GX, TX))]) = Some (GXX,TXX) ->
      exists TXX', indexr n GH' = Some (GXX,TXX') /\ compat GX TX TX' V GXX TXX TXX'.
Proof.
  intros. revert n H0. induction H.
  - intros. simpl. eauto. simpl in H0. assert (n+1 <> 0). omega. eapply beq_nat_false_iff in H. rewrite H in H0. inversion H0.
  - intros. simpl. destruct y.
    case_eq (beq_nat n (length l')); intros E.
    + simpl in H1. destruct x. rewrite app_length in H1. simpl in H1.
      assert (n = length l'). eapply beq_nat_true_iff. eauto.
      assert (beq_nat (n+1) (length l + 1) = true). eapply beq_nat_true_iff.
      rewrite (Forall2_length _ _ _ _ _ H0). omega.
      rewrite H3 in H1. destruct p. destruct p0. inversion H1. subst. simpl in H.
      destruct H. destruct H2. subst. inversion H1. subst.
      eexists. eauto.
    + simpl in H1. destruct x.
      assert (n <> length l'). eapply beq_nat_false_iff. eauto.
      assert (beq_nat (n+1) (length l + 1) = false). eapply beq_nat_false_iff.
      rewrite (Forall2_length _ _ _ _ _ H0). omega.
      rewrite app_length in H1. simpl in H1.
      rewrite H3 in H1.
      eapply IHForall2. eapply H1.
Qed.



Lemma compat_top: forall GX TX TX' V G1 T1',
  compat GX TX TX' V G1 TTop T1' -> closed 0 1 TX -> T1' = TTop.
Proof.
  intros ? ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.

Lemma compat_bot: forall GX TX TX' V G1 T1',
  compat GX TX TX' V G1 TBot T1' -> closed 0 1 TX -> T1' = TBot.
Proof.
  intros ? ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.


Lemma compat_bool: forall GX TX TX' V G1 T1',
  compat GX TX TX' V G1 TBool T1' -> closed 0 1 TX -> T1' = TBool.
Proof.
  intros ? ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.

Lemma compat_mem: forall GX TX TX' V G1 T1 T2 T1',
    compat GX TX TX' V G1 (TMem T1 T2) T1' ->
    closed 0 1 TX ->
    exists TA TB, T1' = TMem TA TB /\
                  compat GX TX TX' V G1 T1 TA /\
                  compat GX TX TX' V G1 T2 TB.
Proof.
  intros ? ? ? ? ? ? ? ? CC CLX. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. + left. repeat eexists; eauto.
  - ev. repeat eexists; eauto. + right. left. inversion H. eauto. + right. left. inversion H. eauto.
  - ev. repeat eexists; eauto. + right. right. inversion H. eauto. + right. right. inversion H. eauto.
Qed.


Lemma compat_mem_fwd2: forall GX TX TX' V G1 T2 T2',
    compat GX TX TX' V G1 T2 T2' ->
    compat GX TX TX' V G1 (TMem TBot T2) (TMem TBot T2').
Proof.
  intros. repeat destruct H as [|H].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. rewrite H3. eauto.
  - ev. repeat eexists; eauto. + right. left. subst. eauto.
  - ev. repeat eexists; eauto. + right. right. subst. simpl. eauto.
Qed.

Lemma compat_mem_fwd1: forall GX TX TX' V G1 T2 T2',
    compat GX TX TX' V G1 T2 T2' ->
    compat GX TX TX' V G1 (TMem T2 TTop) (TMem T2' TTop).
Proof.
  intros. repeat destruct H as [|H].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. rewrite H3. eauto.
  - ev. repeat eexists; eauto. + right. left. subst. eauto.
  - ev. repeat eexists; eauto. + right. right. subst. simpl. eauto.
Qed.

Lemma compat_mem_fwdx: forall GX TX TX' V G1 T2 T2',
    compat GX TX TX' V G1 T2 T2' ->
    compat GX TX TX' V G1 (TMem T2 T2) (TMem T2' T2').
Proof.
  intros. repeat destruct H as [|H].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. rewrite H3. eauto.
  - ev. repeat eexists; eauto. + right. left. subst. eauto.
  - ev. repeat eexists; eauto. + right. right. subst. simpl. eauto.
Qed.


Lemma compat_fun: forall GX TX TX' V G1 l T1 T2 T1',
    compat GX TX TX' V G1 (TFun l T1 T2) T1' ->
    closed_rec 0 1 TX ->
    exists TA TB, T1' = TFun l TA TB /\
                  compat GX TX TX' V G1 T1 TA /\
                  compat GX TX TX' V G1 T2 TB.
Proof.
  intros ? ? ? ? ? ? ? ? ? CC CLX. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. + left. repeat eexists; eauto.
  - ev. repeat eexists; eauto. + right. left. inversion H. eauto. + right. left. inversion H. eauto.
  - ev. repeat eexists; eauto. + right. right. inversion H. eauto. + right. right. inversion H. eauto.
Qed.

Lemma compat_and: forall GX TX TX' V G1 T1 T2 T1',
    compat GX TX TX' V G1 (TAnd T1 T2) T1' ->
    closed_rec 0 1 TX ->
    exists TA TB, T1' = TAnd TA TB /\
                  compat GX TX TX' V G1 T1 TA /\
                  compat GX TX TX' V G1 T2 TB.
Proof.
  intros ? ? ? ? ? ? ? ? CC CLX. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. + left. repeat eexists; eauto.
  - ev. repeat eexists; eauto. + right. left. inversion H. eauto. + right. left. inversion H. eauto.
  - ev. repeat eexists; eauto. + right. right. inversion H. eauto. + right. right. inversion H. eauto.
Qed.


Lemma compat_sel: forall GX TX TX' V G1 T1' (GXX:venv) (TXX:ty) x v n,
    compat GX TX TX' V G1 (TSel x) T1' ->
    closed 0 1 TX ->
    closed 0 0 TXX ->
    index x G1 = Some v ->
    val_type GXX v TXX n ->
    exists TXX', T1' = (TSel x) /\ TXX' = TXX /\ compat GX TX TX' V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? CC CL CL1 IX. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto. + right. left. simpl in H0. eauto.
  - ev. repeat eexists; eauto. + right. left. simpl in H0. eauto.
  - ev. repeat eexists; eauto. + right. left. simpl in H0. eauto.
Qed.

Lemma compat_selb: forall GX TX TX' V G1 T1' (GXX:venv) (TXX:ty) x T0 v n,
    compat GX TX TX' V G1 (open (TSel x) T0) T1' ->
    closed 0 1 TX ->
    closed 0 0 TXX ->
    closed 1 0 T0 ->
    (* index x G1 = Some v -> *)
    val_type GXX v TXX n ->
    exists TXX', T1' = (open (TSel x) T0) /\ TXX' = TXX /\ compat GX TX TX' V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? CC CL CL1. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto.
    erewrite <- closed_no_subst. eassumption.
    unfold open. eapply closed_open. simpl. eassumption. eauto.
    + right. left. simpl in H0. eauto.
  - ev. repeat eexists; eauto. + right. left. simpl in H0. eauto.
  - ev. repeat eexists; eauto.
    erewrite <- closed_no_subst. eassumption.
    unfold open. eapply closed_open. simpl. eassumption. eauto.
    + right. left. simpl in H0. eauto.
Qed.


Lemma compat_selh: forall GX TX TX' V G1 T1' GH0 GH0' (GXX:venv) (TXX:ty) x,
    compat GX TX TX' V G1 (TSelH x) T1' ->
    closed 0 1 TX ->
    indexr x (GH0 ++ [(0, (GX, TX))]) = Some (GXX, TXX) ->
    Forall2 (compat2 GX TX TX' V) GH0 GH0' ->
    (x = 0 /\ GXX = GX /\ TXX = TX) \/
    exists TXX',
      x > 0 /\ T1' = TSelH (x-1) /\
      indexr (x-1) GH0' = Some (GXX, TXX') /\
      compat GX TX TX' V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? CC CL IX FA.
  unfold id in x.
  case_eq (beq_nat x 0); intros E.
  - left. assert (x = 0). eapply beq_nat_true_iff. eauto. subst x. rewrite indexr_hit0 in IX. inversion IX. eauto.
  - right. assert (x <> 0). eapply beq_nat_false_iff. eauto.
    assert (x > 0). omega. remember (x-1) as y. assert (x = y+1) as Y. omega. subst x.
    eapply (indexr_compat_miss0 GH0 GH0' _ _ _ _ _ _ _ FA) in IX.
    repeat destruct CC as [|CC].
    + ev. simpl in H7. rewrite E in H7. rewrite <-Heqy in H7. eexists. eauto.
    + ev. inversion H1. omega.
    + ev. simpl in H4. rewrite E in H4. rewrite <-Heqy in H4. eexists. eauto.
Qed.


Lemma compat_all: forall GX TX TX' V G1 T1 T2 T1' n,
    compat GX TX TX' V G1 (TAll T1 T2) T1' ->
    closed 0 1 TX ->
    closed 1 (n+1) T2 ->
    exists TA TB, T1' = TAll TA TB /\
                  closed 1 n TB /\
                  compat GX TX TX' V G1 T1 TA /\
                  compat GX TX TX' V G1 (open_rec 0 (TSelH (n+1)) T2) (open_rec 0 (TSelH n) TB).
Proof.
  intros ? ? ? ? ? ? ? ? ? CC CLX CL2. repeat destruct CC as [|CC].

  - ev. simpl in H0. repeat eexists; eauto. eapply closed_subst; eauto.
    + unfold compat. left. repeat eexists; eauto.
    + unfold compat. left. repeat eexists; eauto. rewrite subst_open_commute; eauto.

  - ev. simpl in H0. inversion H. repeat eexists; eauto. eapply closed_upgrade_free; eauto. omega.
    + unfold compat. right. right. split. eapply nosubst_intro; eauto. symmetry. eapply closed_no_subst; eauto.
    + unfold compat. right. right. split.
      * eapply nosubst_open. simpl. omega. eapply nosubst_intro. eauto.
      * rewrite subst_open_commute.  assert (T2 = subst TTop T2) as E. symmetry. eapply closed_no_subst; eauto. rewrite <-E. eauto. eauto. eauto.

  - ev. simpl in H0. destruct H. repeat eexists; eauto. eapply closed_subst; eauto. eauto.
    + unfold compat. right. right. eauto.
    + unfold compat. right. right. split.
      * eapply nosubst_open. simpl. omega. eauto.
      * rewrite subst_open_commute; eauto.
Qed.


Lemma compat_bind: forall GX TX TX' V G1 T2 T1' n,
    compat GX TX TX' V G1 (TBind T2) T1' ->
    closed 0 1 TX ->
    closed 1 (n+1) T2 ->
    exists TB, T1' = TBind TB /\
                  closed 1 n TB /\
                  compat GX TX TX' V G1 (open_rec 0 (TSelH (n+1)) T2) (open_rec 0 (TSelH n) TB).
Proof.
  intros ? ? ? ? ? ? ? ? CC CLX CL2. repeat destruct CC as [|CC].

  - ev. simpl in H0. repeat eexists; eauto. eapply closed_subst; eauto.
    + unfold compat. left. repeat eexists; eauto. rewrite subst_open_commute; eauto.

  - ev. simpl in H0. inversion H. repeat eexists; eauto. eapply closed_upgrade_free; eauto. omega.
    + unfold compat. right. right. split.
      * eapply nosubst_open. simpl. omega. eapply nosubst_intro. eauto.
      * rewrite subst_open_commute.  assert (T2 = subst TTop T2) as E. symmetry. eapply closed_no_subst; eauto. rewrite <-E. eauto. eauto. eauto.

  - ev. simpl in H0. simpl in H. repeat eexists; eauto. eapply closed_subst; eauto. eauto.
    + unfold compat. right. right. split.
      * eapply nosubst_open. simpl. omega. eauto.
      * rewrite subst_open_commute; eauto.
Qed.


Lemma subst_open1_aux: forall j x T,
closed (j+1) 0 T ->
(subst (TSel x) (open_rec j (TSelH 0) T)) = (open_rec j (TSel x) T).
Proof.
  intros. generalize dependent j. induction T; intros; eauto.
  - simpl.
    rewrite <- IHT1.
    rewrite <- IHT2.
    reflexivity.
    inversion H. eauto.
    inversion H. eauto.
  - simpl.
    rewrite <- IHT1.
    rewrite <- IHT2.
    reflexivity.
    inversion H. eauto.
    inversion H. eauto.
  - inversion H. subst. inversion H3.
  - inversion H. subst.
    simpl.
    case_eq (beq_nat j i); intros E.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl.
    rewrite <- IHT1.
    assert (S j = j+1) as A by omega.
    rewrite A. rewrite <- IHT2.
    reflexivity.
    inversion H. subst.
    assert (j + 1 + 1 = S (j + 1)) as B by omega.
    rewrite B. eassumption.
    inversion H. subst. eauto.
  - simpl.
    assert (S j = j+1) as A by omega.
    rewrite A. rewrite <- IHT.
    reflexivity.
    inversion H. subst.
    assert (j + 1 + 1 = S (j + 1)) as B by omega.
    rewrite B. eassumption.
  - simpl.
    rewrite <- IHT1.
    rewrite <- IHT2.
    reflexivity.
    inversion H. eauto.
    inversion H. eauto.
Qed.

Lemma subst_open1: forall x T,
closed 1 0 T ->
(subst (TSel x) (open (TSelH 0) T)) = (open (TSel x) T).
Proof.
  intros. eapply subst_open1_aux. simpl. eassumption.
Qed.

Lemma closed_open_tselh: forall j x T,
                                closed j 0 (open_rec j (TSelH x) T) ->
                                closed j 0 T.
Proof.
  intros. generalize dependent j. induction T; intros; eauto.
  - simpl in H. inversion H. subst.
    apply cl_fun. apply IHT1. eassumption. apply IHT2. eassumption.
  - simpl in H. inversion H. subst.
    apply cl_mem. apply IHT1. eassumption. apply IHT2. eassumption.
  - simpl in H.
    case_eq (beq_nat j i); intros E.
    + rewrite E in H. inversion H. subst. omega.
    + rewrite E in H. assumption.
  - simpl in H. inversion H. subst.
    apply cl_all. apply IHT1. eassumption. apply IHT2. eassumption.
  - simpl in H. inversion H. subst.
    apply cl_bind. apply IHT. eassumption.
  - simpl in H. inversion H. subst.
    apply cl_and. apply IHT1. eassumption. apply IHT2. eassumption.
Qed.

Lemma open_noop : forall i j T1 T0,
                    closed i j T0 ->
                    open_rec i T1 T0 = T0.
Proof.
  intros. induction H; eauto.
  - simpl. rewrite IHclosed_rec1. rewrite IHclosed_rec2. reflexivity.
  - simpl. rewrite IHclosed_rec1. rewrite IHclosed_rec2. reflexivity.
  - simpl. rewrite IHclosed_rec1. rewrite IHclosed_rec2. reflexivity.
  - simpl. rewrite IHclosed_rec. reflexivity.
  - simpl. rewrite IHclosed_rec1. rewrite IHclosed_rec2. reflexivity.
  - simpl. assert (beq_nat k i = false) as E. {
      apply false_beq_nat. omega.
    }
    rewrite E. reflexivity.
Qed.

Lemma stpd2_to_sstpd2_aux1: forall n, forall G1 G2 T1 T2 m n1,
  stp2 1 m G1 T1 G2 T2 nil n1 -> n1 < n ->
  sstpd2 m G1 T1 G2 T2 nil.
Proof.
  intros n. induction n; intros; try omega.
  inversion H.
  - Case "topx". eexists. eauto.
  - Case "botx". eexists. eauto.
  - Case "top". subst.
    eapply IHn in H1. inversion H1. eexists. eauto. omega.
  - Case "bot". subst.
    eapply IHn in H1. inversion H1. eexists. eauto. omega.
  - Case "bool". eexists. eauto.
  - Case "fun". eexists. eapply stp2_fun. eauto. eauto.
  - Case "mem".
    eapply IHn in H2. eapply sstpd2_untrans in H2. eu.
    eapply IHn in H3. eapply sstpd2_untrans in H3. eu.
    eexists. eapply stp2_mem. eauto. eauto. omega. omega.
  - Case "sel1".
    remember H3 as Hv. clear HeqHv.
    eapply IHn in H5. eapply sstpd2_untrans in H5. eapply valtp_widen with (2:=H5) in H3.
    eapply invert_typ in H3. ev. repeat eu. subst.
    assert (closed (0+1) (length ([]:aenv)) x1). eapply inv_closed_open. eapply stp2_closed2; eauto. eauto.
    eexists. eapply stp2_strong_sel1. eauto.
    eassumption. eapply stp2_wrapf. eassumption.
    eauto. eauto. omega.
  - Case "sel2".
    remember H3 as Hv. clear HeqHv.
    eapply IHn in H5. eapply sstpd2_untrans in H5. eapply valtp_widen with (2:=H5) in H3.
    eapply invert_typ in H3. ev. repeat eu. subst.
    assert (closed (0+1) (length ([]:aenv)) x1). eapply inv_closed_open. eapply stp2_closed2; eauto. eauto. eauto.
    eexists. eapply stp2_strong_sel2. eauto.
    eassumption. eapply stp2_wrapf. eassumption.
    eauto. eauto. omega.
  - Case "selx".
    eexists. eapply stp2_strong_selx. eauto. eauto.
  - Case "sela1". inversion H2.
  - Case "selab1". inversion H2.
  - Case "selab2". inversion H2.
  - Case "sela2". inversion H2.
  - Case "selax". inversion H2.
  - Case "all". eexists. eapply stp2_all. eauto. eauto. eauto. eauto. eauto.
  - Case "bind". eexists. eapply stp2_bind. eauto. eauto. eauto. eauto.
  - Case "and11". subst. eapply IHn in H1. inversion H1. eapply IHn in H2. inversion H2.
    eexists. eapply stp2_and11; eauto. omega. omega.
  - Case "and12". subst. eapply IHn in H1. inversion H1. eapply IHn in H2. inversion H2.
    eexists. eapply stp2_and12; eauto. omega. omega.
  - Case "and2". subst. eapply IHn in H1. inversion H1. eapply IHn in H2. inversion H2.
    eexists. eapply stp2_and2; eauto. omega. omega.
  - Case "wrapf". eapply IHn in H1. eu. eexists. eapply stp2_wrapf. eauto. omega.
  - Case "transf". eapply IHn in H1. eapply IHn in H2. eu. eu. eexists.
    eapply stp2_transf. eauto. eauto. omega. omega.
    Grab Existential Variables.
    apply 0. apply 0. apply 0. apply 0.
Qed.


(* can be called on level >= 1 *)

Lemma stp2_substitute_aux: forall ni nj, forall d m G1 G2 T1 T2 GH n1,
   stp2 (S d) m G1 T1 G2 T2 GH n1 -> n1 < nj ->
   forall GH0 GH0' GX TX TX' T1' T2' V,
     GH = (GH0 ++ [(0,(GX, TX))]) ->
     val_type GX V (subst TX' TX) ni ->
     (* When we're replacing binds from a pack/unpack sequence, the
        type in GH may refer to itself (contain TSelH 0).
        It should be safe for TX to refer to itself. *)
     closed 0 1 TX ->
     closed 0 0 TX' ->
     compat GX TX TX' (Some V) G1 T1 T1' ->
     compat GX TX TX' (Some V) G2 T2 T2' ->
     Forall2 (compat2 GX TX TX' (Some V)) GH0 GH0' ->
     compat GX TX TX' (Some V) GX TX (subst TX' TX) ->
     exists n1', stp2 (S d) m G1 T1' G2 T2' GH0' n1'.
Proof.
  intros ni. induction ni.
  intros. inversion H2. (* ni=0 case: can't happen, invert val_type *)
  intros n. induction n; intros d m G1 G2 T1 T2 GH n1 H ?. inversion H0.
  inversion H; subst.
  - Case "topx".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_top in IX1.
    eapply compat_top in IX2.
    subst. eexists. eapply stp2_topx. eauto. eauto.

  - Case "botx".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_bot in IX1.
    eapply compat_bot in IX2.
    subst. eexists. eapply stp2_botx. eauto. eauto.

  - Case "top".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_top in IX2.
    subst.
    eapply IHn in H1. destruct H1.
    eexists. eapply stp2_top. eauto. omega.
    eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.

  - Case "bot".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_bot in IX1.
    subst.
    eapply IHn in H1. destruct H1.
    eexists. eapply stp2_bot. eauto. omega.
    eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.

  - Case "bool".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_bool in IX1.
    eapply compat_bool in IX2.
    subst. eexists. eapply stp2_bool; eauto.
    eauto. eauto.

  - Case "fun".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_fun in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_fun in IX2. repeat destruct IX2 as [? IX2].
    subst.
    eapply IHn in H1. destruct H1.
    eapply IHn in H2. destruct H2.
    eexists. eapply stp2_fun. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto. eauto.

  - Case "mem".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_mem in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_mem in IX2. repeat destruct IX2 as [? IX2].
    subst.
    eapply IHn in H2. destruct H2.
    eapply IHn in H3. destruct H3.
    eexists. eapply stp2_mem2. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto. eauto.

  - Case "sel1".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX TXX' (Some V) G1 T1' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    assert (compat GXX TXX TXX' (Some V) GX TX TX) as CPX. right. left. eauto.

    subst.
    eapply IHn in H5. destruct H5.
    eapply IHn in H6. destruct H6.
    eexists.
    eapply stp2_sel1. eauto. eauto. eauto.
    eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto.
    eapply compat_mem_fwd2. eauto. eauto.
    eauto.
    eauto. eauto. eauto. eauto.

  - Case "selb1".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (closed 0 (length ([]:aenv)) (TBind (TMem TBot T0))). {
      eapply stp2_closed2; eauto.
    }

    simpl in H7. unfold closed in H9. inversion H9. subst. inversion H13. subst.

    eapply compat_selb in IX2.
    repeat destruct IX2 as [? IX2]. subst.
    eapply compat_sel in IX1.
    repeat destruct IX1 as [? IX1]. subst.

    eapply IHn in H7. destruct H7.
    eexists.
    eapply stp2_selb1; try eassumption.
    omega. eauto. eauto. eauto. eauto.
    right. left. split. apply closed_open; eauto.  reflexivity.
    right. left. split. apply closed_open; eauto.  reflexivity.
    eapply FA. eauto. eauto. eapply H5. eassumption. eassumption. eassumption. eapply H5.
    eauto. eassumption.

  - Case "sel2".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX TXX' (Some V) G2 T2' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    assert (compat GXX TXX TXX' (Some V) GX TX TX) as CPX. right. left. eauto.

    subst.
    eapply IHn in H5. destruct H5.
    eapply IHn in H6. destruct H6.
    eexists.
    eapply stp2_sel2. eauto. eauto. eauto.
    eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eapply compat_mem_fwd1. eauto. eauto. eauto.
    eauto. eauto. eauto. eauto.

  - Case "selb2".
     intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (closed 0 (length ([]:aenv)) (TBind (TMem T0 TTop))). eapply stp2_closed2; eauto.
    simpl in  H7. unfold closed in H9. inversion H9. subst. inversion H13. subst.

    eapply compat_selb in IX1.
    repeat destruct IX1 as [? IX1]. subst.
    eapply compat_sel in IX2.
    repeat destruct IX2 as [? IX2]. subst.

    eapply IHn in H7. destruct H7.
    eexists.
    eapply stp2_selb2; try eassumption.
    omega. eauto. eauto. eauto. eauto.
    right. left. split. apply closed_open; eauto.  reflexivity.
    right. left. split. apply closed_open; eauto.  reflexivity.
    eapply FA. eauto. eauto. eapply H5. eassumption. eassumption. eassumption. eapply H5.
    eauto. eassumption.

  - Case "selx".

    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (T1' = TSel x1). destruct IX1. ev. eauto. destruct H6. ev. auto. ev. eauto.
    assert (T2' = TSel x2). destruct IX2. ev. eauto. destruct H7. ev. auto. ev. eauto.

    subst.
    eexists.
    eapply stp2_selx. eauto. eauto.

  - Case "sela1".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX TXX' (Some V) G1 (TSelH x) T1') as IXX. eauto.

    eapply (compat_selh GXX TXX TXX' (Some V) G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    destruct IX1.
    + SCase "x = 0".
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H10. subst.
        eapply IHn in H4. destruct H4.
        eapply IHn in H5. destruct H5.
        eexists.
        eapply stp2_sel1. eauto. eauto. eapply closed_subst. eapply closed_upgrade_free. eauto. omega. eauto.
        eauto.
        eauto.
        omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
        omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
        eauto.
        eapply compat_mem_fwd2. eauto.
        eauto. eauto.
      * subst. inversion H9. omega.
      * subst. destruct H9. eauto.
    + SCase "x > 0".
      ev. subst.
      eapply IHn in H4. destruct H4.
      eapply IHn in H5. destruct H5.
      eexists.

      eapply stp2_sela1. eauto.

      assert (S (x - 1) = x) as A. {
        destruct x. omega. (* contradiction *)
        simpl. omega.
      }
      rewrite A.
      eapply closed_compat'. eauto.
      eapply closed_upgrade_free. eauto. omega.
      assert (x + 1 = (S x)) as B by omega. rewrite B. eassumption.

      eauto.
      eauto.
      omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      omega. eauto. eauto. eauto. eauto. eauto. eapply compat_mem_fwd2. eauto. eauto. eauto.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.

  - Case "selab1".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length (GU ++ GL) = length GH0 + 1). rewrite H1. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX TXX' (Some V) G1 (TSelH x) T1') as IXX. eauto.

    eapply (compat_selh GXX TXX TXX' (Some V) G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    destruct IX1.
    + SCase "x = 0". ev. subst.
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H11. subst.


        assert (GL = [(0, (GXX, TXX))]) as EQGL. {
          eapply proj2. eapply concat_same_length'. eassumption.
          simpl. eassumption.
        }

        assert (exists nb, stp2 (S d) false GXX (subst TXX' TXX) G2 (TBind (TMem TBot T0)) [] nb) as SBind. {
          eapply IHn. eauto. omega. rewrite app_nil_l. eauto. eauto. eapply CX. eauto. eauto.
          right. left. split. eassumption. reflexivity.
          eauto. eauto.
        }
        destruct SBind as [nb SBind].

        (* If the input level is 1, we cannot create a selb node.
           A potential avenue is to create a sel node directly.
           But this is not straightforward: we have an imprecise bind which we need to invert.
           Inversion requires transitivity, which increases the size.
           Then on the internal stp obtained from the inverted bind, we need to call
           subst again, but it need not be smaller than our own input.

           Fortunately, we know that we are unpacking a bind in the valtp,
           which becomes the new self object, so we can do an outer
           induction on the valtp depth.

           TODO: Can we use the same approach for selb, and get rid of the
           level 2 pushback altogether?
         *)

        destruct d. { (* first case: level = 1 *)

        assert (exists n1, stp2 0 true GXX (subst TXX' TXX) G2 (TBind (TMem TBot T0)) [] n1) as SBind0. {
          eapply sstpd2_untrans. eapply stpd2_to_sstpd2_aux1. eauto. eauto.
        }
        destruct SBind0 as [n1 SBind0].

        assert (val_type G2 x0 (TBind (TMem TBot T0)) (S ni)) as VSB. eapply valtp_widen. eapply VS. eexists. eapply SBind0.
        inversion VSB; subst; ev.
        inversion H14.
        inversion H14.
        eapply dcs_tbind in H16. inversion H16. eassumption.
        inversion H14.
        inversion H14. (* invert bind/bind *) subst.


        assert (closed 0 0 (open (TSel x2) T2)) as CL. eapply closed_open. eauto. eauto.

        assert (compat venv0 (open (TSelH 0) T2) (TSel x2)
                       (Some x0) venv0 (open (TSelH 0) T2)
                       (open (TSel x2) T2)) as CP1. {
          left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        }
        assert (compat venv0 (open (TSelH 0) T2) (TSel x2)
     (Some x0) G2 (open (TSelH 0) (TMem TBot T0))
     (TMem TBot T2')) as CP2. {
          destruct IX2 as [IX2 | [IX2 | IX2]].
        (*1*)repeat destruct IX2 as [|IX2]; ev. inversion H18; subst.
        rewrite subst_open1.
        left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        inversion H4. inversion H28. eauto. (* closed 1 0 T0 *)
        (*2*)destruct IX2 as [IX21 IX22]. right. left. split. econstructor; eauto. rewrite IX22. eauto.
        (*3*)destruct IX2 as [IX21 IX22]. right. right. split. econstructor; simpl; eauto. rewrite IX22. eauto.
        }
        assert (compat venv0 (open (TSelH 0) T2) (TSel x2)
     (Some x0) venv0 (open (TSelH 0) T2)
     (subst (TSel x2) (open (TSelH 0) T2))) as CPH. {
           left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        }



        assert (exists n7, stp2 1 false venv0 (open (TSel x2) T2) G2 (TMem TBot T2') [] n7) as ST1. {
          subst.
          eapply IHni in H22. destruct H22 as [? H22].
          eexists.
          eapply H22.
          eauto. rewrite app_nil_l. eauto.
          rewrite subst_open1. eauto. eauto.
          eapply closed_open. eapply closed_upgrade_free. eauto. eauto. eauto. eauto.
          eauto. eauto. eauto. eauto.
        }
        destruct ST1 as [n7 ST1].

        assert (stp2 1 false venv0 (open (TSel x2) T2) G2 (TMem TBot T2') GH0' n7) as ST1'.
        eapply stp2_extendH_mult in ST1. rewrite app_nil_r in ST1. eapply ST1.

        assert (exists n9, stp2 1 true G2 (TMem TBot T2') G2 (TMem TBot T2') GH0' n9) as REG1.
        eapply stp2_reg2. eauto.
        destruct REG1 as [n9 REG1].

        assert (exists n8, stp2 1 true G2 T2' G2 T2' GH0' n8) as REG1'.
        inversion REG1.
        eapply stp2_reg2. eapply H31.
        destruct REG1' as [n8 REG1'].

        eexists. eapply stp2_sel1. eauto. eauto. eauto.
        eapply ST1'. eapply REG1'.
        }

        (* second case: input is at level 2 (or greater). this means we can create a selb node *)

        destruct IX2 as [IX2 | [IX2 | IX2]].
        repeat destruct IX2 as [|IX2]; ev. inversion H15; subst.
        rewrite subst_open1.
        eapply IHn in H9. destruct H9.
        eexists.
        eapply stp2_selb1. eauto. eauto. eauto. eapply closed_subst. eapply closed_upgrade_free. eauto. omega. eauto.
        eapply SBind.
        eauto.
        omega. eauto. eauto. eauto. eauto.
        left. eexists. eexists. eexists. split. eassumption. split. reflexivity. split. reflexivity.  split. eassumption. rewrite subst_open1. reflexivity.
        inversion H4. subst. inversion H21. subst. eassumption.
        left. eexists. eexists. eexists. split. eassumption. split. reflexivity. split. reflexivity.  split. eassumption. rewrite subst_open1. reflexivity.
        inversion H4. subst. inversion H21. subst. eassumption.
        eauto. eauto.
        inversion H4. subst. inversion H21. subst. eassumption.

        destruct IX2 as [IX21 IX22].
        assert (T2' = open (TSel x) T0) as A. {
          unfold open. erewrite open_noop.
          rewrite IX22. unfold open. erewrite open_noop.
          reflexivity.
          eapply closed_open_tselh. eassumption.
          eapply closed_open_tselh. eassumption.
        }
        rewrite A.
        eapply IHn in H9. destruct H9.
        eexists.
        eapply stp2_selb1. eassumption. right. eapply closed_open_tselh. eassumption.
        eassumption. eapply closed_subst. eapply closed_upgrade_free. eauto. omega. eauto.
        eapply SBind.
        eauto.
        omega. eauto. eauto. eauto. eauto.
        right. left. split. eassumption.
        unfold open. erewrite open_noop. erewrite open_noop. reflexivity.
        eapply closed_open_tselh. eassumption.
        eapply closed_open_tselh. eassumption.
        right. left. split. eassumption.
        unfold open. erewrite open_noop. erewrite open_noop. reflexivity.
        eapply closed_open_tselh. eassumption.
        eapply closed_open_tselh. eassumption.
        eauto. eauto.

        destruct IX2 as [IX21 IX22].
        assert (closed_rec 0 0 T0) as C0. {
          eapply nosubst_zero_closed. eassumption. simpl. inversion H4. subst. inversion H17. subst.
          eassumption.
        }
        assert (T2' = T0) as C1. {
          rewrite IX22. erewrite closed_no_subst. unfold open. erewrite open_noop. reflexivity.
          eauto. unfold open. erewrite open_noop. eassumption. eassumption.
        }
        assert (T2' = open (TSel x) T0) as C2. {
          unfold open. erewrite open_noop. eassumption. eassumption.
        }
        rewrite C2.
        eapply IHn in H9. destruct H9.
        eexists.
        eapply stp2_selb1. eassumption. right. eassumption.
        eassumption. eapply closed_subst. eapply closed_upgrade_free. eauto. omega. eauto.
        eapply SBind.
        eauto.
        omega. eauto. eauto. eauto. eauto.
        right. left. split. unfold open. erewrite open_noop. eassumption. eassumption.
        unfold open. erewrite open_noop. erewrite open_noop. reflexivity.
        eassumption.
        eassumption.
        right. left. split. unfold open. erewrite open_noop. eassumption. eassumption.
        unfold open. erewrite open_noop. erewrite open_noop. reflexivity.
        eassumption.
        eassumption.
        eauto. eauto.

      * subst. inversion H10. omega.
      * subst. destruct H10. eauto.
    + SCase "x > 0".
      ev. subst.
      assert (exists GH0L, GH0 = GU ++ GH0L /\ GL = GH0L ++ [(0, (GXX, TXX))]) as EQGH. {
        eapply exists_GH1L. eassumption. eassumption. simpl. omega.
      }
      destruct EQGH as [GH0L [EQGH0 EQGL]].
      assert (exists GU' GL', GH0' = GU' ++ GL' /\
              Forall2 (compat2 GXX TXX TXX' (Some V)) GH0L GL') as EQGH'. {
        rewrite EQGH0 in FA.
        eapply Forall2_app_inv_l in FA.
        destruct FA as [GU' [GL' [FAU [FAL EQFA]]]].
        exists GU'. exists GL'. split; eassumption.
      }
      destruct EQGH' as [GU' [GL' [EQGH0' FAGL']]].

      remember (x-1) as x_1.

      eapply IHn in H7. destruct H7.
      eapply IHn in H9. destruct H9.
      eexists.
      eapply stp2_selab1. eauto.

      eapply closed_compat'. eauto.
      eapply closed_upgrade_free. eauto. omega.
      rewrite Heqx_1. simpl.
      assert (x - 1 + 1 = x) as B. {
        omega.
      }
      rewrite B.
      eassumption.

      eassumption.

      instantiate (1:=GL'). rewrite EQGL in H5. rewrite app_length in H5. simpl in H5.
      rewrite NPeano.Nat.add_1_r in H5. inversion H5. rewrite Heqx_1.
      erewrite <- Forall2_length; try eassumption. omega.
      instantiate (1:=GU'). eassumption.

      eauto.

      destruct IX2 as [IX2 | [IX2 | IX2]].
      repeat destruct IX2 as [|IX2]; ev. inversion H14. subst V. rewrite H17.
      assert (x_1 + 1 = x) as C. {
        omega.
      }
      rewrite <- C.
      unfold open. rewrite subst_open_commute.
      erewrite closed_no_subst. reflexivity.
      inversion H4. clear C. subst. inversion H21. subst. eassumption.
      rewrite C. clear C. simpl. inversion H4. subst. inversion H21. subst. eapply closed_upgrade_free. eassumption. omega. eauto.

      destruct IX2 as [IX2A IX2B]. unfold open. erewrite open_noop.
      rewrite IX2B. unfold open. erewrite open_noop. reflexivity.
      eapply closed_open_tselh. eassumption.
      eapply closed_open_tselh. eassumption.

      destruct IX2 as [IX2A IX2B].
      assert (x_1 + 1 = x) as C. {
        omega.
      }
      rewrite IX2B. rewrite <- C.
      unfold open. rewrite subst_open_commute.
      erewrite closed_no_subst. reflexivity.
      inversion H4. clear C. subst. inversion H16. subst. eassumption.
      rewrite C. clear C. simpl. inversion H4. subst. inversion H16. subst. eapply closed_upgrade_free. eassumption. omega. eauto.

      eauto.

      omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      omega. eapply EQGL. eauto. eauto. eauto. eauto.
      right. left. split. eassumption. reflexivity.
      eauto. eauto.

    (* remaining obligations *)
    + eauto. + rewrite <- H1. eauto. + eauto.


  - Case "selab2".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length (GU ++ GL) = length GH0 + 1). rewrite H1. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX TXX' (Some V) G2 (TSelH x) T2') as IXX. eauto.

    eapply (compat_selh GXX TXX TXX' (Some V) G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    destruct IX2.
    + SCase "x = 0". ev. subst.
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H11. subst.


        assert (GL = [(0, (GXX, TXX))]) as EQGL. {
          eapply proj2. eapply concat_same_length'. eassumption.
          simpl. eassumption.
        }

        assert (exists nb, stp2 (S d) false GXX (subst TXX' TXX) G1 (TBind (TMem T0 TTop)) [] nb) as SBind. {
          eapply IHn. eauto. omega. rewrite app_nil_l. eauto. eauto. eapply CX. eauto. eauto.
          right. left. split. eassumption. reflexivity.
          eauto. eauto.
        }
        destruct SBind as [nb SBind].

        destruct d. { (* first case: level = 1 *)

        assert (exists n1, stp2 0 true GXX (subst TXX' TXX) G1 (TBind (TMem T0 TTop)) [] n1) as SBind0. {
          eapply sstpd2_untrans. eapply stpd2_to_sstpd2_aux1. eauto. eauto.
        }
        destruct SBind0 as [n1 SBind0].

        assert (val_type G1 x0 (TBind (TMem T0 TTop)) (S ni)) as VSB. eapply valtp_widen. eapply VS. eexists. eapply SBind0.
        inversion VSB; subst; ev.
        inversion H14.
        inversion H14.
        eapply dcs_tbind in H16. inversion H16. eassumption.
        inversion H14.
        inversion H14. (* invert bind/bind *) subst.


        assert (closed 0 0 (open (TSel x2) T2)) as CL. eapply closed_open. eauto. eauto.

        assert (compat venv0 (open (TSelH 0) T2) (TSel x2)
                       (Some x0) venv0 (open (TSelH 0) T2)
                       (open (TSel x2) T2)) as CP1. {
          left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        }
        assert (compat venv0 (open (TSelH 0) T2) (TSel x2)
     (Some x0) G1 (open (TSelH 0) (TMem T0 TTop))
     (TMem T1' TTop)) as CP2. {
          destruct IX1 as [IX1 | [IX1 | IX1]].
        (*1*)repeat destruct IX2 as [|IX2]; ev. inversion H18; subst.
        rewrite subst_open1.
        left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        inversion H4. inversion H28. eauto. (* closed 1 0 T0 *)
        (*2*)destruct IX1 as [IX11 IX12]. right. left. split. econstructor; eauto. rewrite IX12. eauto.
        (*3*)destruct IX1 as [IX11 IX12]. right. right. split. econstructor; simpl; eauto. rewrite IX12. eauto.
        }
        assert (compat venv0 (open (TSelH 0) T2) (TSel x2)
     (Some x0) venv0 (open (TSelH 0) T2)
     (subst (TSel x2) (open (TSelH 0) T2))) as CPH. {
           left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        }



        assert (exists n7, stp2 1 false venv0 (open (TSel x2) T2) G1 (TMem T1' TTop) [] n7) as ST1. {
          subst.
          eapply IHni in H22. destruct H22 as [? H22].
          eexists.
          eapply H22.
          eauto. rewrite app_nil_l. eauto.
          rewrite subst_open1. eauto. eauto.
          eapply closed_open. eapply closed_upgrade_free. eauto. eauto. eauto. eauto.
          eauto. eauto. eauto. eauto.
        }
        destruct ST1 as [n7 ST1].

        assert (stp2 1 false venv0 (open (TSel x2) T2) G1 (TMem T1' TTop) GH0' n7) as ST1'.
        eapply stp2_extendH_mult in ST1. rewrite app_nil_r in ST1. eapply ST1.

        assert (exists n9, stp2 1 true G1 (TMem T1' TTop) G1 (TMem T1' TTop) GH0' n9) as REG1.
        eapply stp2_reg2. eauto.
        destruct REG1 as [n9 REG1].

        assert (exists n8, stp2 1 true G1 T1' G1 T1' GH0' n8) as REG1'.
        inversion REG1.
        eapply stp2_reg2. eapply H28.
        destruct REG1' as [n8 REG1'].

        eexists. eapply stp2_sel2. eauto. eauto. eauto.
        eapply ST1'. eapply REG1'.
        }

        (* second case: input is at level 2 (or greater). this means we can create a selb node *)

        destruct IX1 as [IX1 | [IX1 | IX1]].
        repeat destruct IX1 as [|IX1]; ev. inversion H15; subst.
        rewrite subst_open1.
        eapply IHn in H9. destruct H9.
        eexists.
        eapply stp2_selb2. eauto. eauto. eauto. eapply closed_subst. eapply closed_upgrade_free. eauto. omega. eauto.
        eapply SBind.
        eauto.
        omega. eauto. eauto. eauto. eauto.
        left. eexists. eexists. eexists. split. eassumption. split. reflexivity. split. reflexivity.  split. eassumption. rewrite subst_open1. reflexivity.
        inversion H4. subst. inversion H21. subst. eassumption.
        left. eexists. eexists. eexists. split. eassumption. split. reflexivity. split. reflexivity.  split. eassumption. rewrite subst_open1. reflexivity.
        inversion H4. subst. inversion H21. subst. eassumption.
        eauto. eauto.
        inversion H4. subst. inversion H21. subst. eassumption.

        destruct IX1 as [IX11 IX12].
        assert (T1' = open (TSel x) T0) as A. {
          unfold open. erewrite open_noop.
          rewrite IX12. unfold open. erewrite open_noop.
          reflexivity.
          eapply closed_open_tselh. eassumption.
          eapply closed_open_tselh. eassumption.
        }
        rewrite A.
        eapply IHn in H9. destruct H9.
        eexists.
        eapply stp2_selb2. eassumption. right. eapply closed_open_tselh. eassumption.
        eassumption. eapply closed_subst. eapply closed_upgrade_free. eauto. omega. eauto.
        eapply SBind.
        eauto.
        omega. eauto. eauto. eauto. eauto.
        right. left. split. eassumption.
        unfold open. erewrite open_noop. erewrite open_noop. reflexivity.
        eapply closed_open_tselh. eassumption.
        eapply closed_open_tselh. eassumption.
        right. left. split. eassumption.
        unfold open. erewrite open_noop. erewrite open_noop. reflexivity.
        eapply closed_open_tselh. eassumption.
        eapply closed_open_tselh. eassumption.
        eauto. eauto.

        destruct IX1 as [IX11 IX12].
        assert (closed_rec 0 0 T0) as C0. {
          eapply nosubst_zero_closed. eassumption. simpl. inversion H4. subst. inversion H17. subst.
          eassumption.
        }
        assert (T1' = T0) as C1. {
          rewrite IX12. erewrite closed_no_subst. unfold open. erewrite open_noop. reflexivity.
          eauto. unfold open. erewrite open_noop. eassumption. eassumption.
        }
        assert (T1' = open (TSel x) T0) as C2. {
          unfold open. erewrite open_noop. eassumption. eassumption.
        }
        rewrite C2.
        eapply IHn in H9. destruct H9.
        eexists.
        eapply stp2_selb2. eassumption. right. eassumption.
        eassumption. eapply closed_subst. eapply closed_upgrade_free. eauto. omega. eauto.
        eapply SBind.
        eauto.
        omega. eauto. eauto. eauto. eauto.
        right. left. split. unfold open. erewrite open_noop. eassumption. eassumption.
        unfold open. erewrite open_noop. erewrite open_noop. reflexivity.
        eassumption.
        eassumption.
        right. left. split. unfold open. erewrite open_noop. eassumption. eassumption.
        unfold open. erewrite open_noop. erewrite open_noop. reflexivity.
        eassumption.
        eassumption.
        eauto. eauto.

      * subst. inversion H10. omega.
      * subst. destruct H10. eauto.
    + SCase "x > 0".
      ev. subst.
      assert (exists GH0L, GH0 = GU ++ GH0L /\ GL = GH0L ++ [(0, (GXX, TXX))]) as EQGH. {
        eapply exists_GH1L. eassumption. eassumption. simpl. omega.
      }
      destruct EQGH as [GH0L [EQGH0 EQGL]].
      assert (exists GU' GL', GH0' = GU' ++ GL' /\
              Forall2 (compat2 GXX TXX TXX' (Some V)) GH0L GL') as EQGH'. {
        rewrite EQGH0 in FA.
        eapply Forall2_app_inv_l in FA.
        destruct FA as [GU' [GL' [FAU [FAL EQFA]]]].
        exists GU'. exists GL'. split; eassumption.
      }
      destruct EQGH' as [GU' [GL' [EQGH0' FAGL']]].

      remember (x-1) as x_1.

      eapply IHn in H7. destruct H7.
      eapply IHn in H9. destruct H9.
      eexists.
      eapply stp2_selab2. eauto.

      eapply closed_compat'. eauto.
      eapply closed_upgrade_free. eauto. omega.
      rewrite Heqx_1. simpl.
      assert (x - 1 + 1 = x) as B. {
        omega.
      }
      rewrite B.
      eassumption.

      eassumption.

      instantiate (1:=GL'). rewrite EQGL in H5. rewrite app_length in H5. simpl in H5.
      rewrite NPeano.Nat.add_1_r in H5. inversion H5. rewrite Heqx_1.
      erewrite <- Forall2_length; try eassumption. omega.
      instantiate (1:=GU'). eassumption.

      eauto.

      destruct IX1 as [IX1 | [IX1 | IX1]].
      repeat destruct IX1 as [|IX1]; ev. inversion H14. subst V. rewrite H17.
      assert (x_1 + 1 = x) as C. {
        omega.
      }
      rewrite <- C.
      unfold open. rewrite subst_open_commute.
      erewrite closed_no_subst. reflexivity.
      inversion H4. clear C. subst. inversion H21. subst. eassumption.
      rewrite C. clear C. simpl. inversion H4. subst. inversion H21. subst. eapply closed_upgrade_free. eassumption. omega. eauto.

      destruct IX1 as [IX1A IX1B]. unfold open. erewrite open_noop.
      rewrite IX1B. unfold open. erewrite open_noop. reflexivity.
      eapply closed_open_tselh. eassumption.
      eapply closed_open_tselh. eassumption.

      destruct IX1 as [IX1A IX1B].
      assert (x_1 + 1 = x) as C. {
        omega.
      }
      rewrite IX1B. rewrite <- C.
      unfold open. rewrite subst_open_commute.
      erewrite closed_no_subst. reflexivity.
      inversion H4. clear C. subst. inversion H16. subst. eassumption.
      rewrite C. clear C. simpl. inversion H4. subst. inversion H16. subst. eapply closed_upgrade_free. eassumption. omega. eauto.

      eauto.

      omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      omega. eapply EQGL. eauto. eauto. eauto. eauto.
      right. left. split. eassumption. reflexivity.
      eauto. eauto.

    (* remaining obligations *)
    + eauto. + rewrite <- H1. eauto. + eauto.

  - Case "sela2".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX TXX' (Some V) G2 (TSelH x) T2') as IXX by eauto.

    eapply (compat_selh GXX TXX TXX' (Some V) G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    destruct IX2.
    + SCase "x = 0".
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H10. subst.
        eapply IHn in H4. destruct H4.
        eapply IHn in H5. destruct H5.
        eexists.
        eapply stp2_sel2. eauto. eauto. eapply closed_subst. eapply closed_upgrade_free. eauto. omega. eauto.
        eauto.
        eauto.
        omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
        omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
        eauto.
        eapply compat_mem_fwd1. eauto.
        eauto. eauto.
      * subst. inversion H9. omega.
      * subst. destruct H9. eauto.
    + SCase "x > 0".
      ev. subst.
      eapply IHn in H4. destruct H4.
      eapply IHn in H5. destruct H5.
      eexists.

      eapply stp2_sela2. eauto.

      assert (S (x - 1) = x) as A. {
        destruct x. omega. (* contradiction *)
        simpl. omega.
      }
      rewrite A.
      eapply closed_compat'. eauto.
      eapply closed_upgrade_free. eauto. omega.
      assert (x + 1 = (S x)) as B by omega. rewrite B. eassumption.

      eauto.
      eauto.
      omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      omega. eauto. eauto. eauto. eauto. eauto. eapply compat_mem_fwd1. eauto. eauto. eauto.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.

  - Case "selax".

    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX TXX' (Some V) G1 (TSelH x) T1') as IXX1. eauto.
    assert (compat GXX TXX TXX' (Some V) G2 (TSelH x) T2') as IXX2. eauto.

    eapply (compat_selh GXX TXX TXX' (Some V) G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].
    eapply (compat_selh GXX TXX TXX' (Some V) G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].
    assert (not (nosubst (TSelH 0))). unfold not. intros. simpl in H1. eauto.
    assert (not (closed 0 0 (TSelH 0))). unfold not. intros. inversion H6. omega.

    destruct x; destruct IX1; ev; try omega; destruct IX2; ev; try omega; subst.
    + SCase "x = 0".
      repeat destruct IXX1 as [IXX1|IXX1]; ev; try contradiction.
      repeat destruct IXX2 as [IXX2|IXX2]; ev; try contradiction.
      * SSCase "sel-sel".
        subst. inversion H16. subst. inversion H8. subst.
        simpl. eexists. eapply stp2_selx. subst. eauto. eauto.
    + SCase "x > 0".
      destruct IXX1; destruct IXX2; ev; subst; eexists; eapply stp2_selax; eauto.
    (* leftovers *)
    + eauto. + subst. eauto. + eauto. + eauto. + subst. eauto. + eauto.

  - Case "all".
    intros GH0 GH0' GX TX TX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply compat_all in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_all in IX2. repeat destruct IX2 as [? IX2].

    subst.

    eapply IHn in H1. destruct H1.
    eapply IHn in H4. destruct H4.
    eapply IHn in H5. destruct H5.
    eexists.
    eapply stp2_all.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    omega.
    instantiate (3:= (0, (G2, T4))::GH0). reflexivity.
    eauto. eapply CX. eauto.
    rewrite app_length. simpl. rewrite EL. eauto.
    rewrite app_length. simpl. rewrite EL. eauto.
    eapply Forall2_cons. simpl. eauto. eauto.
    eauto.
    omega.
      change ((0, (G1, T0)) :: GH0 ++ [(0, (GX, TX))]) with
      (((0, (G1, T0)) :: GH0) ++ [(0, (GX, TX))]).
      reflexivity.
      eauto. eapply CX. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto.
      eauto.
    eauto.
    omega.
      eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
    eauto.
    eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.

  - Case "bind".
    intros GH0 GH0' GX TX TX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply compat_bind in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_bind in IX2. repeat destruct IX2 as [? IX2].

    subst.

    eapply IHn in H4. destruct H4.
    eapply IHn in H5. destruct H5.
    eexists.
    eapply stp2_bindb.
    eauto.
    eauto.
    eauto.
    eauto.
    omega.
      instantiate (3:=(0, (G1,  open (TSelH (length (GH0 ++ [(0, (GX, TX))]))) T0))::GH0).
      reflexivity.
      eauto. eapply CX. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto. repeat split. rewrite app_length. simpl. rewrite EL. eapply IX1. eauto.
      eauto.
    omega.
      change
        ((0, (G2, open (TSelH (length (GH0 ++ [(0, (GX, TX))]))) T3))
           :: GH0 ++ [(0, (GX, TX))]) with
      (((0, (G2, open (TSelH (length (GH0 ++ [(0, (GX, TX))]))) T3))
          :: GH0) ++ [(0, (GX, TX))]).
      reflexivity.
      eauto. eapply CX. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto. repeat split. rewrite app_length. simpl. rewrite EL. eapply IX2. eauto.
      eauto.
    eauto.
    eauto. subst GH. fold id. rewrite <- EL.
    eapply closed_upgrade_free. eauto. unfold id in H5.
    rewrite app_length. simpl. omega.
    eauto.
    eauto. subst GH. fold id. rewrite <-EL.
      eapply closed_upgrade_free. eauto. unfold id in H5.
      rewrite app_length. simpl. omega.

  - Case "and11".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    subst. apply compat_and in IX1. repeat destruct IX1 as [? IX1].
    eapply IHn in H1. destruct H1.
    eapply IHn in H2. destruct H2.
    eexists.
    subst. eapply stp2_and11; eassumption.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.
  - Case "and12".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    subst. apply compat_and in IX1. repeat destruct IX1 as [? IX1].
    eapply IHn in H1. destruct H1.
    eapply IHn in H2. destruct H2.
    eexists.
    subst. eapply stp2_and12; eassumption.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.
  - Case "and2".
    intros GH0 GH0' GXX TXX TXX' T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    subst. apply compat_and in IX2. repeat destruct IX2 as [? IX2].
    eapply IHn in H1. destruct H1.
    eapply IHn in H2. destruct H2.
    eexists.
    subst. eapply stp2_and2. eapply H1. eapply H2.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.

  - Case "wrapf".
    intros. subst.
    eapply IHn in H1. destruct H1.
    eexists.
    eapply stp2_wrapf. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.

  - Case "transf".
    intros. subst.

    assert (exists T3',
              compat GX TX TX' (Some V) ((fresh G3,V)::G3) T3 T3') as A.
    {
      eexists.
      unfold compat. simpl. left. exists (fresh G3). exists V. exists (S ni).
      case_eq (le_lt_dec (fresh G3) (fresh G3)); intros LTE LE.
      rewrite <- beq_nat_refl.
      split; try split; try split; try split; eauto.
      omega.
    }
    destruct A as [T3' A].

    assert (stp2 (S d) true G1 T1 ((fresh G3,V)::G3) T3 (GH0 ++ [(0, (GX, TX))]) n0) as S1.
    eapply stp2_extend2; eauto.
    assert (stp2 (S d) false ((fresh G3,V)::G3) T3 G2 T2 (GH0 ++ [(0, (GX, TX))]) n2) as S2.
    eapply stp2_extend1; eauto.

    eapply IHn in S1. destruct S1 as [? S1].
    eapply IHn in S2. destruct S2 as [? S2].
    eexists.
    eapply stp2_transf. eapply S1. eapply S2.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.

Qed.


Lemma stpd2_substitute: forall m G1 G2 T1 T2 GH,
   stpd2 m G1 T1 G2 T2 GH ->
   forall GH0 GH0' GX TX TX' T1' T2' V n,
     GH = (GH0 ++ [(0,(GX, TX))]) ->
     val_type GX V (subst TX' TX) n ->
     closed 0 1 TX ->
     closed 0 0 TX' ->
     compat GX TX TX' (Some V) G1 T1 T1' ->
     compat GX TX TX' (Some V) G2 T2 T2' ->
     compat GX TX TX' (Some V) GX TX (subst TX' TX) ->
     Forall2 (compat2 GX TX TX' (Some V)) GH0 GH0' ->
     stpd2 m G1 T1' G2 T2' GH0'.
Proof. intros. repeat eu. eapply stp2_substitute_aux; eauto. Qed.

(* end substitute *)



Lemma stpd2_to_sstpd2_aux2: forall n, forall G1 G2 GH T1 T2 m n1,
  stp2 2 m G1 T1 G2 T2 GH n1 -> n1 < n ->
  exists n2, stp2 1 m G1 T1 G2 T2 GH n2.
Proof.
  intros n. induction n; intros; try omega.
  inversion H.
  - Case "topx". eexists. eauto.
  - Case "botx". eexists. eauto.
  - Case "top". subst.
    eapply IHn in H1. inversion H1. eexists. eauto. omega.
  - Case "bot". subst.
    eapply IHn in H1. inversion H1. eexists. eauto. omega.
  - Case "bool". eexists. eauto.
  - Case "fun". eexists. eapply stp2_fun. eauto. eauto.
  - Case "mem".
    eapply IHn in H2. ev. eapply IHn in H3. ev.
    eexists. eapply stp2_mem2; eauto. omega. omega.
  - Case "sel1". subst.
    eapply IHn in H5. eapply IHn in H6. ev. ev.
    eexists. eapply stp2_sel1; eauto. omega. omega.
  - Case "selb1". subst.
    eapply IHn in H6. eapply IHn in H7. ev. ev. eapply stpd2_to_sstpd2_aux1 in H6. eapply sstpd2_untrans in H6. eapply valtp_widen with (2:=H6) in H4.
    remember H4 as Hv. clear HeqHv.
    (* now invert base on TBind knowledge -- TODO: helper lemma*)
    inversion H4; ev. subst.
    inversion H9. subst.
    inversion H7. subst.
    eapply dcs_tbind in H8. inversion H8. eassumption.
    inversion H10. (* 1 case left *)
    subst. inversion H10. subst.

    assert (exists n, stp2 1 false
                           venv0 (open (TSel x2) T2)
                           G2 (open (TSel x') (TMem TBot T0)) [] n) as ST. {

      eapply stp2_substitute_aux with (GH0:=[]).
      eauto.
      eauto.
      simpl. reflexivity.
      erewrite subst_open1. eassumption. eauto.
      apply closed_open. simpl. eapply closed_upgrade. eauto. eapply closed_upgrade_free. eauto. simpl. omega. omega. eauto. eauto.

      left. eexists. eexists. eexists. split. eassumption. split. reflexivity. split. reflexivity.
      split. erewrite subst_open1. eassumption. eauto.
      rewrite subst_open1. reflexivity. eauto.

      inversion H3.
      left. eexists. eexists. eexists. split. eassumption. split. reflexivity. split. reflexivity.

      split.
      erewrite subst_open1. eassumption. eauto.
      simpl. erewrite subst_open1. eauto.
      eapply valtp_closed in H4. inversion H4. subst. inversion H18. subst. eauto.
      eauto.

      right. left. split. simpl. unfold open. erewrite open_noop.
      eauto. eauto. unfold open. erewrite open_noop. erewrite open_noop.
      reflexivity. eauto. eauto.

      eauto.

      left. eexists. eexists. eexists. split. eassumption. split. reflexivity. split. reflexivity.

      split.
      erewrite subst_open1. eassumption. eauto.
      simpl. erewrite subst_open1. eauto.
      eapply valtp_closed in H4. inversion H4. subst. inversion H17. subst. eauto.
    }
    destruct ST as [? ST].
    (* NOTE: this crucially depends on the result of inverting stp_bind having
       level 1, so we don't need to do induction on it.

       Right now, this is quite a limitation: we cannot use level 2 derivations inside binds.

       - We cannot lower levels in hypothetical contexts, because we need to untrans above.

         So we cannot change the bind's body elsewhere, before inverting here.

         (UPDATE: actually that's what we're doing now. We get away with it
         because GH = [], which means that we may not be able to  unfold nontrivial
         binds for selections on hypothetical vars)

       - Doing induction on ST here would be difficult, because the size is wrong.

         We're inverting from valtp, which does not count towards our own size.
         It may seem that it should. But then it needs to be inserted by stp_substitute,
         ergo stp_substitute will no longer keep things at const size, and will
         return larger terms.

         That makes it seem unlikely that we'd be able to use IHn on the result.

         We know the size of what we're putting into ST. But we have the same problem
         as previously in narrowing: we do not know how many times the added term
         is used, so we cannot bound the result size.
    *)
    assert (closed 0 (length (nil:aenv)) (open (TSel x2) T2)) as C. eapply stp2_closed1. eauto. simpl in C.
    eexists. eapply stp2_sel1. eauto. eapply H8. eauto.
    eapply stp2_extendH_mult0. eauto. eauto. eauto. omega. omega.
  - Case "sel2". subst.
    eapply IHn in H5. eapply IHn in H6. ev. ev.
    eexists. eapply stp2_sel2; eauto. omega. omega.
  - Case "selb2".

    eapply IHn in H6. eapply IHn in H7. ev. ev. eapply stpd2_to_sstpd2_aux1 in H6. eapply sstpd2_untrans in H6. eapply valtp_widen with (2:=H6) in H4.
    remember H4 as Hv. clear HeqHv.
    subst.
    (* now invert base on TBind knowledge -- TODO: helper lemma*)
    inversion H4; ev. subst.
    inversion H9. subst.
    inversion H1. subst.
    eapply dcs_tbind in H8. inversion H8. eassumption.
    inversion H10. subst.
    inversion H10.  subst.

    assert (exists n, stp2 1 false
                           venv0 (open (TSel x2) T2)
                           G1 (open (TSel x') (TMem T0 TTop)) [] n) as ST. {

      eapply stp2_substitute_aux with (GH0:=[]).
      eauto.
      eauto.
      simpl. reflexivity.
      erewrite subst_open1. eassumption. eauto.
      apply closed_open. simpl. eapply closed_upgrade. eauto. eapply closed_upgrade_free. eauto. simpl. omega. omega. eauto. eauto.

      left. eexists. eexists. eexists. split. eassumption. split. reflexivity. split. reflexivity.
      split. erewrite subst_open1. eassumption. eauto.
      rewrite subst_open1. reflexivity. eauto.

      inversion H3.
      left. eexists. eexists. eexists. split. eassumption. split. reflexivity. split. reflexivity.

      split.
      erewrite subst_open1. eassumption. eauto.
      simpl. erewrite subst_open1. eauto.
      eapply valtp_closed in H4. inversion H4. subst. inversion H18. subst. eauto.
      eauto.

      right. left. split. simpl. unfold open. erewrite open_noop.
      eauto. eauto. unfold open. erewrite open_noop. erewrite open_noop.
      reflexivity. eauto. eauto.

      eauto.

      left. eexists. eexists. eexists. split. eassumption. split. reflexivity. split. reflexivity.

      split.
      erewrite subst_open1. eassumption. eauto.
      simpl. erewrite subst_open1. eauto.
      eapply valtp_closed in H4. inversion H4. subst. inversion H17. subst. eauto.
    }
    destruct ST as [? ST].

    assert (closed 0 (length (nil:aenv)) (open (TSel x2) T2)) as C. eapply stp2_closed1. eauto. simpl in C.
    eexists. eapply stp2_sel2. eauto. eapply H8. eauto.
    eapply stp2_extendH_mult0. eauto. eauto. eauto. omega. omega.
  - Case "selx". subst.
    eexists. eapply stp2_selx. eauto. eauto.
  - Case "sela1". subst. eapply IHn in H4. eapply IHn in H5. ev. ev.
    eexists. eapply stp2_sela1; eauto. omega. omega.
  - Case "selab1".
    (* THIS ONE WILL NOT WORK AT LEVEL 2 (no way to remove *)
    (* so we use it at level 1, and translate during subst *)
    subst.
    eapply IHn in H7. eapply IHn in H9. ev. ev.
    eexists. eapply stp2_selab1; eauto. omega. omega.
  - Case "selab2".
    subst.
    eapply IHn in H7. eapply IHn in H9. ev. ev.
    eexists. eapply stp2_selab2; eauto. omega. omega.
  - Case "sela2". eapply IHn in H4. eapply IHn in H5. ev. ev.
    eexists. eapply stp2_sela2; eauto. omega. omega.
  - Case "selhx". eexists. eapply stp2_selax. eauto.
  - Case "all". eexists. eapply stp2_all. eauto. eauto. eauto. eapply H4. eapply H5.
  - Case "bind".
    eapply IHn in H4. eapply IHn in H5. ev. ev.
    eexists. eapply stp2_bindb. eauto. eauto. eauto. eauto. omega. omega.
  - Case "and11". subst. eapply IHn in H1. inversion H1. eapply IHn in H2. inversion H2.
    eexists. eapply stp2_and11; eauto. omega. omega.
  - Case "and12". subst. eapply IHn in H1. inversion H1. eapply IHn in H2. inversion H2.
    eexists. eapply stp2_and12; eauto. omega. omega.
  - Case "and2". subst. eapply IHn in H1. inversion H1. eapply IHn in H2. inversion H2.
    eexists. eapply stp2_and2; eauto. omega. omega.
  - Case "wrapf". eapply IHn in H1. ev. eexists. eapply stp2_wrapf. eauto. omega.
  - Case "transf". eapply IHn in H1. eapply IHn in H2. ev. ev. eexists.
    eapply stp2_transf. eauto. eauto. omega. omega.
    Grab Existential Variables.
    apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


Lemma stpd2_to_atpd2: forall G1 G2 T1 T2 GH m,
  stpd2 m G1 T1 G2 T2 GH ->
  atpd2 m G1 T1 G2 T2 GH.
Proof.
  intros. eu. eapply stpd2_to_sstpd2_aux2.
  eassumption. eauto.
Qed.

Lemma stpd2_to_sstpd2: forall G1 G2 T1 T2 m,
  stpd2 m G1 T1 G2 T2 nil ->
  sstpd2 m G1 T1 G2 T2 nil.
Proof.
  intros. eu.
  eapply stpd2_to_sstpd2_aux2 in H. ev.
  eapply stpd2_to_sstpd2_aux1; eauto. eauto.
Qed.


Lemma stpd2_upgrade: forall G1 G2 T1 T2,
  stpd2 false G1 T1 G2 T2 nil ->
  sstpd2 true G1 T1 G2 T2 nil.
Proof.
  intros.
  eapply sstpd2_untrans. eapply stpd2_to_sstpd2. eauto.
Qed.

Lemma sstpd2_downgrade_true: forall G1 G2 T1 T2 H,
  sstpd2 true G1 T1 G2 T2 H ->
  stpd2 true G1 T1 G2 T2 H.
Proof.
  intros. inversion H0. remember 0 as m. induction H1;
    try solve [eexists; eauto]; try solve [inversion Heqm].
  - Case "top".
    eapply stpd2_top. eapply IHstp2. eapply sstpd2_reg1. eassumption. eauto.
  - Case "bot".
    eapply stpd2_bot. eapply IHstp2. eapply sstpd2_reg2. eassumption. eauto.
  - Case "mem".
    eapply stpd2_mem.
    eapply IHstp2_1; eauto. eexists. eassumption.
    eapply stpd2_wrapf. eapply IHstp2_2; eauto. eexists. eassumption.
  - Case "sel1".
    eapply stpd2_sel1.
    eassumption. eassumption. eapply valtp_closed. eassumption.
    eapply IHstp2_1. eexists. eassumption. eauto.
    eapply stpd2_reg2. eapply IHstp2_2. eexists. eassumption. eauto.
  - Case "sel2".
    eapply stpd2_sel2.
    eassumption. eassumption. eapply valtp_closed. eassumption.
    eapply IHstp2_1. eexists. eassumption. eauto.
    eapply stpd2_reg1. eapply IHstp2_2. eexists. eassumption. eauto.
  - Case "selx".
    eapply stpd2_selx; eauto.
  - Case "bind".
    eapply stpd2_bind; eauto.
    eapply atpd2_to_stpd2. eexists. eassumption.
    eapply atpd2_to_stpd2. eexists. eassumption.
  - Case "and11".
    eapply stpd2_and11; eauto.
    eapply IHstp2_1; eauto. eexists. rewrite <- Heqm. eassumption.
    eapply IHstp2_2; eauto. eexists. rewrite <- Heqm. eassumption.
  - Case "and12".
    eapply stpd2_and12; eauto.
    eapply IHstp2_1; eauto. eexists. rewrite <- Heqm. eassumption.
    eapply IHstp2_2; eauto. eexists. rewrite <- Heqm. eassumption.
  - Case "and2".
    eapply stpd2_and2; eauto.
    eapply IHstp2_1; eauto. eexists. rewrite <- Heqm. eassumption.
    eapply IHstp2_2; eauto. eexists. rewrite <- Heqm. eassumption.
  - Case "wrap". destruct m.
    + eapply stpd2_wrapf. eapply IHstp2. eexists. eassumption. eauto.
    + inversion Heqm.
  - Case "trans". destruct m.
    + eapply stpd2_transf. eapply IHstp2_1. eexists; eauto. eauto.
      eapply IHstp2_2. eexists. eauto. eauto.
    + inversion Heqm.
  Grab Existential Variables.
  apply 0. apply 0. apply 0.
Qed.

Lemma sstpd2_downgrade: forall G1 G2 T1 T2 H,
  sstpd2 true G1 T1 G2 T2 H ->
  stpd2 false G1 T1 G2 T2 H.
Proof.
  intros. eapply stpd2_wrapf. eapply sstpd2_downgrade_true. eassumption.
Qed.


(* --------------------------------- *)

Hint Constructors wf_envh.

Lemma exists_GYL: forall GX GY GU GL,
  wf_envh GX GY (GU ++ GL) ->
  exists GYU GYL, GY = GYU ++ GYL /\ wf_envh GX GYL GL.
Proof.
  intros. remember (GU ++ GL) as G. generalize dependent HeqG. generalize dependent GU. generalize dependent GL. induction H; intros.
  - exists []. exists []. simpl. split. reflexivity. symmetry in HeqG. apply app_eq_nil in HeqG.
    inversion HeqG. subst. eauto.
  - induction GU.
    + rewrite app_nil_l in HeqG.
      exists []. eexists. rewrite app_nil_l. split. reflexivity.
      rewrite <- HeqG. eauto.
    + simpl in HeqG. inversion HeqG.
      specialize (IHwf_envh GL GU H2). destruct IHwf_envh as [GYU [GYL [IHA IHB]]].
      exists ((n, (vvs, t))::GYU). exists GYL. split. rewrite IHA. simpl. reflexivity.
      apply IHB.
Qed.

Lemma stp_to_stp2_aux: forall G1 GH T1 T2,
  stp G1 GH T1 T2 ->
  forall GX GY, wf_env GX G1 -> wf_envh GX GY GH ->
  stpd2 true GX T1 GX T2 GY.
Proof.
  intros G1 G2 T1 T2 ST. induction ST; intros GX GY WX WY.
  - Case "topx". eapply stpd2_topx.
  - Case "botx". eapply stpd2_botx.
  - Case "top".
    eapply stpd2_top.
    specialize (IHST GX GY WX WY).
    apply stpd2_reg2 in IHST.
    apply IHST.
  - Case "bot".
    eapply stpd2_bot.
    specialize (IHST GX GY WX WY).
    apply stpd2_reg2 in IHST.
    apply IHST.
  - Case "bool". eapply stpd2_bool; eauto.
  - Case "fun". eapply stpd2_fun; eapply stpd2_wrapf; eauto.
  - Case "mem". eapply stpd2_mem; eapply stpd2_wrapf; eauto.
  - Case "sel1".
    assert (exists (v : vl) n, index x GX = Some v /\ val_type GX v TX n) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? [? VT]]].
    eapply stpd2_sel1. eauto. eauto. eapply valtp_closed; eauto.
    eapply stpd2_wrapf. eauto.
    specialize (IHST2 GX GY WX WY).
    apply stpd2_reg2 in IHST2.
    apply IHST2.
  - Case "sel2".
    assert (exists (v : vl) n, index x GX = Some v /\ val_type GX v TX n) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? [? VT]]].
    eapply stpd2_sel2. eauto. eauto. eapply valtp_closed; eauto.
    eapply stpd2_wrapf. eauto.
    specialize (IHST2 GX GY WX WY).
    apply stpd2_reg2 in IHST2.
    apply IHST2.
  - Case "selb1".
    assert (exists (v : vl) n, index x GX = Some v /\ val_type GX v TX n) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? [? VT]]].
    eapply stpd2_selb1. eauto. eauto. eauto. eapply valtp_closed; eauto.
    eapply stpd2_wrapf. eauto.
    specialize (IHST2 GX GY WX WY).
    apply stpd2_reg2 in IHST2.
    apply IHST2.
  - Case "selb2".
    assert (exists (v : vl) n, index x GX = Some v /\ val_type GX v TX n) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? [? VT]]].
    eapply stpd2_selb2. eauto. eauto. eauto. eapply valtp_closed; eauto.
    eapply stpd2_wrapf. eauto.
    specialize (IHST2 GX GY WX WY).
    apply stpd2_reg2 in IHST2.
    apply IHST2.
  - Case "selx".
    assert (exists (v : vl) n, index x GX = Some v /\ val_type GX v TX n) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? [? VT]]].
    eapply stpd2_selx. eauto. eauto.
  - Case "sela1".
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    inversion VT. subst.
    eapply stpd2_sela1. eauto. eauto.
    eapply stpd2_wrapf. eapply IHST1. eauto. eauto.
    specialize (IHST2 _ _ WX WY).
    apply stpd2_reg2 in IHST2.
    apply IHST2.
  - Case "sela2".
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    inversion VT. subst.
    eapply stpd2_sela2. eauto. eauto.
    eapply stpd2_wrapf. eapply IHST1. eauto. eauto.
    specialize (IHST2 _ _ WX WY).
    apply stpd2_reg2 in IHST2.
    apply IHST2.
  - Case "selab1".
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]].
    inversion VT. subst.
    assert (exists GYU GYL, GY = GYU ++ GYL /\ wf_envh GX GYL GL) as EQG. {
      eapply exists_GYL. eassumption.
    }
    destruct EQG as [GYU [GYL [EQY WYL]]].
    eapply stpd2_selab1. eauto. eauto. eauto.
    instantiate (1:=GYL). erewrite wfh_length. eassumption. eassumption.
    eassumption.
    eapply stpd2_wrapf. eapply IHST1. eauto. eauto.
    specialize (IHST2 _ _ WX WY).
    apply stpd2_reg2 in IHST2.
    apply IHST2.
  - Case "selab2".
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]].
    inversion VT. subst.
    assert (exists GYU GYL, GY = GYU ++ GYL /\ wf_envh GX GYL GL) as EQG. {
      eapply exists_GYL. eassumption.
    }
    destruct EQG as [GYU [GYL [EQY WYL]]].
    eapply stpd2_selab2. eauto. eauto. eauto.
    instantiate (1:=GYL). erewrite wfh_length. eassumption. eassumption.
    eassumption.
    eapply stpd2_wrapf. eapply IHST1. eauto. eauto. eauto.
    specialize (IHST2 _ _ WX WY).
    apply stpd2_reg2 in IHST2.
    apply IHST2.
  - Case "selax".
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto. ev. destruct x0.
    eapply stpd2_selax. eauto.
  - Case "all".
    subst x. assert (length GY = length GH). eapply wfh_length; eauto.
    eapply stpd2_all.
    eapply stpd2_wrapf. eauto.
    rewrite H. eauto. rewrite H.  eauto.
    rewrite H.
    eapply stpd2_wrapf. eapply IHST2. eauto. eapply wfeh_cons. eauto.
    rewrite H.
    eapply stpd2_wrapf. apply IHST3; eauto.
  - Case "bind".
    subst x. assert (length GY = length GH). eapply wfh_length; eauto. unfold id in H.
    eapply stpd2_bind. rewrite H. eauto. rewrite H. eauto.
    rewrite H.
    eapply stpd2_wrapf. eapply IHST1. eauto. eapply wfeh_cons. eauto.
    rewrite H.
    eapply stpd2_wrapf. eapply IHST2; eauto.
  - Case "and11".
    eapply stpd2_and11.
    eapply IHST1; eauto.
    eapply IHST2; eauto.
  - Case "and12".
    eapply stpd2_and12.
    eapply IHST1; eauto.
    eapply IHST2; eauto.
  - Case "and2".
    eapply stpd2_and2.
    eapply stpd2_wrapf. eapply IHST1; eauto.
    eapply stpd2_wrapf. eapply IHST2; eauto.
Qed.

Lemma stp_to_stp2: forall G1 GH T1 T2,
  stp G1 GH T1 T2 ->
  forall GX GY, wf_env GX G1 -> wf_envh GX GY GH ->
  stpd2 false GX T1 GX T2 GY.
Proof.
  intros. eapply stpd2_wrapf. eapply stp_to_stp2_aux; eauto.
Qed.


Inductive wf_tp: tenv -> tenv -> ty -> Prop :=
| wf_top: forall G1 GH,
    wf_tp G1 GH TTop
| wf_bot: forall G1 GH,
    wf_tp G1 GH TBot
| wf_bool: forall G1 GH,
    wf_tp G1 GH TBool
| wf_fun: forall G1 GH l T1 T2,
    wf_tp G1 GH T1 ->
    wf_tp G1 GH T2 ->
    wf_tp G1 GH (TFun l T1 T2)
| wf_mem: forall G1 GH T1 T2,
    wf_tp G1 GH T1 ->
    wf_tp G1 GH T2 ->
    wf_tp G1 GH (TMem T1 T2)
| wf_sel: forall G1 GH TX x,
    index x G1 = Some TX ->
    wf_tp G1 GH (TSel x)
| wf_sela: forall G1 GH TX x,
    indexr x GH = Some TX  ->
    wf_tp G1 GH (TSelH x)
| wf_all: forall G1 GH T1 T2 x,
    wf_tp G1 GH T1 ->
    x = length GH ->
    closed 1 (length GH) T2 ->
    wf_tp G1 ((0,T1)::GH) (open (TSelH x) T2) ->
    wf_tp G1 GH (TAll T1 T2)
| wf_bind: forall G1 GH T1 x,
    x = length GH ->
    closed 1 (length GH) T1 ->
    wf_tp G1 ((0,open (TSelH x) T1)::GH) (open (TSelH x) T1) ->
    wf_tp G1 GH (TBind T1)
| wf_and: forall G1 GH T1 T2,
    wf_tp G1 GH T1 ->
    wf_tp G1 GH T2 ->
    wf_tp G1 GH (TAnd T1 T2)
.
Hint Constructors wf_tp.

Lemma stp_to_wf_tp_aux: forall G GH T1 T2,
                          stp G GH T1 T2 ->
                          wf_tp G GH T1 /\ wf_tp G GH T2.
Proof.
  intros. induction H;
  try solve [repeat ev; split; eauto].
Qed.

Lemma stp_to_wf_tp: forall G GH T,
                      stp G GH T T ->
                      wf_tp G GH T.
Proof.
  intros. apply (proj1 (stp_to_wf_tp_aux G GH T T H)).
Qed.

Lemma wf_tp_to_stp2_cycle_aux: forall T v G GH,
  wf_tp ((fresh G, TMem T T) :: G) GH T ->
  forall GX GY, wf_env GX G -> wf_envh ((fresh G, v)::GX) GY GH ->
  stpd2 true ((fresh G, v) :: GX) T
             ((fresh G, v) :: GX) T GY.
Proof.
  intros T t G GH ST. remember (TMem T T) as T0. clear HeqT0.
  dependent induction ST; intros GX GY WX WY.
  - Case "top". eapply stpd2_topx.
  - Case "bot". eapply stpd2_botx.
  - Case "bool". eapply stpd2_bool; eauto.
  - Case "fun". eapply stpd2_fun; eapply stpd2_wrapf; eauto.
  - Case "mem". eapply stpd2_mem; eapply stpd2_wrapf; eauto.
  - Case "selx".
    assert (exists v, index x ((fresh G, t) :: GX) = Some v) as A. {
      simpl. simpl in H.
      case_eq (le_lt_dec (fresh G) (fresh G)); intros E1 LE1.
      rewrite (wf_fresh GX G). rewrite LE1. rewrite LE1 in H.
      case_eq (beq_nat x (fresh G)); intros E2.
      eexists. reflexivity.
      eapply index_exists. eapply WX. rewrite E2 in H. eapply H.
      assumption.
      omega.
    }
    destruct A as [v A].
    eapply stpd2_selx; eapply A.
  - Case "selax".
    assert (exists v, indexr x GY = Some v) as A. {
      eapply indexr_exists; eauto.
    }
    destruct A as [v A]. destruct v.
    eapply stpd2_selax. eassumption.
  - Case "all".
    assert (length GY = length GH) as A. { eapply wfh_length; eauto. }
    eapply stpd2_all.
    eapply stpd2_wrapf. eapply IHST1; eauto.
    rewrite A. eauto.
    rewrite A. eauto.
    rewrite A. eapply stpd2_wrapf. eapply IHST2; eauto.
    rewrite A. eapply stpd2_wrapf. eapply IHST2; eauto.
  - Case "bind".
    assert (length (GY:aenv) = length GH) as A. { eapply wfh_length; eauto. }
    assert (closed 1 (length GY) T1) by solve [rewrite A; eauto].
    eapply stpd2_bind; try eassumption.
    rewrite <- A in IHST. eapply stpd2_wrapf. eapply IHST; eauto.
    rewrite <- A in IHST. eapply stpd2_wrapf. eapply IHST; eauto.
  - Case "and".
    eapply stpd2_and2; eapply stpd2_wrapf.
    eapply stpd2_and11. eapply IHST1; eauto. eapply IHST2; eauto.
    eapply stpd2_and12. eapply IHST2; eauto. eapply IHST1; eauto.
Qed.

Lemma stp_to_stp2_cycle: forall venv env T t,
  wf_env venv env ->
  stp ((fresh env, TMem T T) :: env) [] T T->
  stpd2 false ((fresh env, vty venv t) :: venv) (TMem T T)
              ((fresh env, vty venv t) :: venv) (TMem T T) [].
Proof.
  intros. apply stpd2_wrapf.
  eapply stp_to_wf_tp in H0.
  apply stpd2_mem; apply stpd2_wrapf; eapply wf_tp_to_stp2_cycle_aux; eauto.
Qed.

Lemma invert_abs: forall venv vf l T1 T2 n,
  val_type venv vf (TFun l T1 T2) n ->
  exists env tenv f TF ds x y T3 T4,
    vf = (vabs env f ds) /\
    fresh env <= f /\
    1 + f = x /\
    wf_env env tenv /\
    has_type ((x,T3)::(f,TF)::tenv) y T4 /\
    sstpd2 true venv T1 env T3 [] /\
    sstpd2 true env T4 venv T2 [].
Proof.
  intros. inversion H; repeat ev; try solve by inversion. subst.
  admit.
Qed.

(*
Lemma invert_abs: forall venv vf T1 T2 n,
  val_type venv vf (TFun T1 T2) n ->
  exists env tenv f x y T3 T4,
    vf = (vabs env f x y) /\
    fresh env <= f /\
    1 + f <= x /\
    wf_env env tenv /\
    has_type ((x,T3)::(f,TFun T3 T4)::tenv) y T4 /\
    sstpd2 true venv T1 env T3 [] /\
    sstpd2 true env T4 venv T2 [].
Proof.
  intros. inversion H; repeat ev; try solve by inversion. inversion H4.
  assert (stpd2 false venv0 T1 venv1 T0 []) as E1. eauto.
  assert (stpd2 false venv1 T3 venv0 T2 []) as E2. eauto.
  eapply stpd2_upgrade in E1. eapply stpd2_upgrade in E2.
  repeat eu. repeat eexists; eauto.
Qed.
*)



Lemma dcs_tall_aux: forall n, forall G ds venv1 T venv0 T1 T2 n0,
  n0 <= n ->
  dcs_has_type G ds T ->
  stp2 0 true venv1 T venv0 (TAll T1 T2) [] n0 ->
  False.
Proof.
  intros n. induction n.
  intros. inversion H1; omega.
  intros. eapply dcs_has_type_shape in H0.
  destruct H0. subst. inversion H1.
  destruct H0.
  destruct H0 as [l [T1' [T2' H0]]]. subst. inversion H1.
  destruct H0 as [l [T1' [T2' [ds' [T' [H0 HR]]]]]]. subst. inversion H1.
  subst. inversion H4.
  subst. eapply IHn in HR. apply HR. instantiate (1:=n1). omega. eassumption.
Qed.

Lemma dcs_tall: forall G ds venv1 T venv0 T1 T2 n0,
  dcs_has_type G ds T ->
  stp2 0 true venv1 T venv0 (TAll T1 T2) [] n0 ->
  False.
Proof.
  intros. eapply dcs_tall_aux. instantiate (1:=n0). eauto. eassumption. eassumption.
Qed.

Lemma invert_tabs: forall venv vf vx T1 T2 nf nx,
  val_type venv vf (TAll T1 T2) nf ->
  val_type venv vx T1 nx ->
  sstpd2 true venv T2 venv T2 [] ->
  exists env tenv x y T3 T4,
    vf = (vtabs env x T3 y) /\
    fresh env = x /\
    wf_env env tenv /\
    has_type ((x,T3)::tenv) y (open (TSel x) T4) /\
    sstpd2 true venv T1 env T3 [] /\
    sstpd2 true ((x,vx)::env) (open (TSel x) T4) venv T2 []. (* (open T1 T2) []. *)
Proof.
  intros venv0 vf vx T1 T2 nf nx VF VX STY. inversion VF; ev; try solve by inversion.
  subst. eapply dcs_tall in H0. inversion H0. eassumption.
  inversion H2. subst.
  eexists. eexists. eexists. eexists. eexists. eexists.
  repeat split; eauto.
  remember (fresh venv1) as x.
  remember (x + fresh venv0) as xx.

  eapply stpd2_upgrade; eauto.

  (* -- new goal: result -- *)

  (* inversion of TAll < TAll *)
  assert (stpd2 false venv0 T1 venv1 T0 []) as ARG. eauto.
  assert (stpd2 false venv1 (open (TSelH 0) T3) venv0 (open (TSelH 0) T2) [(0,(venv0, T1))]) as KEY. {
    eauto.
  }
  eapply stpd2_upgrade in ARG.

  (* need reflexivity *)
  assert (stpd2 false venv0 T1 venv0 T1 []). eapply stpd2_wrapf. eapply stpd2_reg1. eauto.
  assert (closed 0 0 T1). eapply stpd2_closed1 in H1. simpl in H1. eauto.

  (* now rename *)

  assert (stpd2 false ((fresh venv1,vx) :: venv1) (open_rec 0 (TSel (fresh venv1)) T3) venv0 (T2) []). { (* T2 was open T1 T2 *)

    assert (closed 0 (length ([]:aenv)) T2). eapply sstpd2_closed1; eauto.
    assert (open (TSelH 0) T2 = T2) as OP2. symmetry. eapply closed_no_open; eauto.

    eapply stpd2_substitute with (GH0:=nil).
    eapply stpd2_extend1. eapply KEY. (* previously: stpd2_narrow. inv_vtp_half. eapply KEY. *)
    eauto. simpl. eauto.
    erewrite closed_no_subst. eapply VX. eassumption.
    eapply closed_upgrade_free. eauto. omega. eauto.
    left. repeat eexists. eapply index_hit2. eauto. eauto. eauto.
    rewrite (closed_no_subst) with (j:=0). eauto. eauto.
    rewrite (subst_open_zero 0 1). eauto. eauto.
    right. left. split. rewrite OP2. eauto. eauto.
    right. left. split. eauto. rewrite closed_no_subst with (j:=0). eauto. eauto.
    eauto.
  }
  eapply stpd2_upgrade in H4.

  (* done *)
  subst. eauto.
Qed.



Lemma valtp_reg: forall G v T n,
                   val_type G v T n ->
                   sstpd2 true G T G T [].
Proof. intros. induction H; eapply sstpd2_reg2; eauto. Qed.


Lemma has_type_wf: forall G1 t T,
  has_type G1 t T ->
  stp G1 [] T T.
Proof.
  intros. induction H.
  - Case "true". eauto.
  - Case "false". eauto.
  - Case "var". eauto.
  - Case "vpack". eauto.
  - Case "vunpack". eauto.
  - Case "vtyp". eauto.
  - Case "app". eauto.
    assert (stp env [] (TFun T1 T2) (TFun T1 T2)) as WF. eauto.
    inversion WF; subst. eauto. rewrite H1 in H2. inversion H2.
  - Case "abs".
    eauto.
  - Case "tapp". eauto.
  - Case "tabs". eauto.
  - Case "tsub". eapply stp_reg. eauto.
Qed.

(* if not a timeout, then result not stuck and well-typed *)

Theorem full_safety : forall n e tenv venv res T,
  teval n venv e = Some res -> has_type tenv e T -> wf_env venv tenv ->
  res_type venv res T.

Proof.
  intros n. induction n.
  (* 0 *)   intros. inversion H.
  (* S n *) intros. destruct e; inversion H.

  - Case "True".
    remember (ttrue) as e. induction H0; inversion Heqe; subst.
    + eapply not_stuck. eapply v_bool; eauto.
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

  - Case "False".
    remember (tfalse) as e. induction H0; inversion Heqe; subst.
    + eapply not_stuck. eapply v_bool; eauto.
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

  - Case "Var".
    remember (tvar i) as e.
    assert (stp tenv0 [] T T). eapply has_type_wf. eauto.
    induction H0; inversion Heqe; subst.
    + destruct (index_safe_ex venv0 env T1 i) as [v [? [I V]]]; eauto.
      rewrite I. eapply not_stuck. eapply V.

    + SCase "pack".
      assert (res_type venv0 (index i venv0) (open (TSel i) T1)). eapply IHhas_type; eauto. eapply has_type_wf; eauto.
      inversion H3. subst.
      eapply not_stuck. eapply v_pack. eauto. eauto. eauto.
      eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

    + SCase "unpack".
      assert (res_type venv0 (index i venv0) (TBind T1)). eapply IHhas_type; eauto. eapply has_type_wf; eauto.
      inversion H3. subst.
      inversion H7; subst; ev; try solve by inversion.
      eapply not_stuck. inversion H9. subst.

      assert (exists n, stp2 1 false venv1 (open (TSel x) T2) venv0 (open (TSel i) T1) [] n).
      eapply stp2_substitute_aux with (GH0:=nil).
      eapply H15. eauto. simpl. reflexivity.
      unfold open. erewrite subst_open_zero with (k:=1). eauto. eauto.
      eapply closed_open. eapply closed_upgrade_free. eauto. simpl. eauto. eauto.
      eauto.

      left. eexists. eexists. eexists. split. eauto. split. reflexivity. split. eauto. split. unfold open. rewrite subst_open_zero with (k:=1). eauto. eauto.
      symmetry. eapply subst_open_zero. eauto.

      left. eexists. eexists. eexists. split. eauto. split. reflexivity. split. eauto. split. unfold open. rewrite subst_open_zero with (k:=1). eauto. eauto.
      symmetry. eapply subst_open_zero. eauto.

      eauto.

      left. eexists. eexists. eexists. split. eauto. split. reflexivity. split. eauto. split. unfold open. rewrite subst_open_zero with (k:=1). eauto. eauto. eauto.

      eapply valtp_widen. eauto.

      ev. eapply sstpd2_untrans. eapply stpd2_to_sstpd2_aux1. eapply H10. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply has_type_wf; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

  - Case "Typ".
    remember (ttyp t) as e.
    induction H0; inversion Heqe; subst.
    + remember (fresh env) as i.
      remember (open (TSel i) t) as T1X.
      remember ((i,vty venv0 t)::venv0) as venv1.
      assert (index i venv1 = Some (vty venv0 t)). subst. eapply index_hit2. rewrite wf_fresh with (ts := env). eauto. eauto. eauto. eauto.
      assert (val_type venv1 (vty venv0 t) (TMem T1X T1X) 1). eapply v_ty. eauto. eauto.
      assert ((open (TSel (fresh venv0)) t) = T1X). rewrite wf_fresh with (ts:=env). rewrite <-Heqi. eauto. eauto.
      rewrite H2.

      (* we have everything as stp and 'just' need to convert to stp2. however we're
      working with an env that has a self binding, and the wf_env evidence needs
      the very val_tp what we're trying to construct *)

      eapply stpd2_upgrade. rewrite wf_fresh with (ts:=env). subst. eapply stp_to_stp2_cycle. eauto. eauto. eauto. eauto.

      eapply not_stuck. eapply v_pack. eapply H0. eapply H2. instantiate (1:=TMem t t). simpl. subst T1X. eauto. subst venv1. eapply sstpd2_extend1. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. rewrite wf_fresh with (ts:=env). subst i. eauto. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

  - Case "App".
    remember (tapp e1 e2) as e. induction H0; inversion Heqe; subst.
    +
      remember (teval n venv0 e1) as tf.
      remember (teval n venv0 e2) as tx.


      destruct tx as [rx|]; try solve by inversion.
      assert (res_type venv0 rx T1) as HRX. SCase "HRX". subst. eapply IHn; eauto.
      inversion HRX as [? vx].

      destruct tf as [rf|]; subst rx; try solve by inversion.
      assert (res_type venv0 rf (TFun T1 T2)) as HRF. SCase "HRF". subst. eapply IHn; eauto.
      inversion HRF as [? vf].

      destruct (invert_abs venv0 vf T1 T2 n1) as
          [env1 [tenv [f0 [x0 [y0 [T3 [T4 [EF [FRF [FRX [WF [HTY [STX STY]]]]]]]]]]]]]. eauto.
      (* now we know it's a closure, and we have has_type evidence *)

      assert (res_type ((x0,vx)::(f0,vf)::env1) res T4) as HRY.
        SCase "HRY".
          subst. eapply IHn. eauto. eauto.
          (* wf_env f x *) econstructor. eapply valtp_widen; eauto. eapply sstpd2_extend2. eapply sstpd2_extend2. eauto. eauto. eauto.
          (* wf_env f   *) econstructor. eapply v_abs; eauto. eapply sstpd2_extend2.
          eapply sstpd2_downgrade in STX. eapply sstpd2_downgrade in STY. repeat eu.
          assert (stpd2 false env1 T3 env1 T3 []) as A3. {
            eapply stpd2_wrapf. eapply stpd2_reg2. eauto.
          }
          inversion A3 as [na3 HA3].
          assert (stpd2 false env1 T4 env1 T4 []) as A4 by solve [eapply stpd2_wrapf; eapply stpd2_reg1; eauto].
          inversion A4 as [na4 HA4].
          eexists. eapply stp2_fun. eassumption. eassumption. eauto. eauto.
          (* should add sstpd2_fun constructor? *)

      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto. eapply sstpd2_extend1. eapply sstpd2_extend1. eauto. eauto. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.


  - Case "Abs".
    remember (tabs i i0 e) as xe. induction H0; inversion Heqxe; subst.
    + eapply not_stuck. eapply v_abs; eauto. rewrite (wf_fresh venv0 env H1). eauto. eapply stpd2_upgrade. eapply stp_to_stp2. eauto. eauto. econstructor.
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

  - Case "TApp".
    remember (ttapp e1 e2) as e. induction H0; inversion Heqe; subst.
    +
      remember (teval n venv0 e1) as tf.
      remember (teval n venv0 e2) as tx.

      destruct tx as [rx|]; try solve by inversion.
      assert (res_type venv0 rx T11) as HRX. SCase "HRX". subst. eapply IHn; eauto.
      inversion HRX as [? vx].

      subst rx.

      destruct tf as [rf|]; try solve by inversion.
      assert (res_type venv0 rf (TAll T11 T12)) as HRF. SCase "HRF". subst. eapply IHn; eauto.
      inversion HRF as [? vf].

      destruct (invert_tabs venv0 vf vx T11 T12 n1 n0) as
          [env1 [tenv [x0 [y0 [T3 [T4 [EF [FRX [WF [HTY [STX STY]]]]]]]]]]].
      eauto. eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.
      (* now we know it's a closure, and we have has_type evidence *)

      assert (res_type ((x0,vx)::env1) res (open (TSel x0) T4)) as HRY.
        SCase "HRY".
          subst. eapply IHn. eauto. eauto.
          (* wf_env x *) econstructor. eapply valtp_widen; eauto. eapply sstpd2_extend2. eauto. eauto. eauto.
      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen. eauto. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

  - Case "TAbs".
    remember (ttabs i t e) as xe. induction H0; inversion Heqxe; subst.
    + eapply not_stuck. eapply v_tabs; eauto. subst i. eauto. rewrite (wf_fresh venv0 env H1). eauto. eapply stpd2_upgrade. eapply stp_to_stp2. eauto. eauto. econstructor.
    +  eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

       Grab Existential Variables. apply 0. apply 0.
Qed.

End FSUB.