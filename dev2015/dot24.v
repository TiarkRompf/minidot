(* Full safety for DOT *)

(* copied from dot22.v *)
(* based on that, it removes the 2nd level of pushback,
   and performs the necessary translation while going
   from stp to stp2 *)

(* TODO:
   used closed for regularity and wf
   remove redundant case in compat
   (maybe go back to simpler naming scheme)
*)


Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.

Module FSUB.

Definition id := nat.

Inductive var : Type :=
  | varF   : id -> var
  | varH   : id -> var
  | varB   : id -> var
.

Inductive ty : Type :=
  | TBool  : ty
  | TBot   : ty
  | TTop   : ty
  | TMem   : id -> ty -> ty -> ty
  | TVar   : var -> ty                                 
  | TSel   : var -> id -> ty
  | TAll   : id -> ty -> ty -> ty
  | TBind  : ty -> ty
  | TAnd   : ty -> ty -> ty
  | TOr    : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : id -> tm
  | tapp   : tm -> id -> tm -> tm (* \o.m(x) *)
  | tobj   : id -> list (id * def) -> tm (* \o {d} *)
  | tlet   : id -> tm -> tm -> tm (* let \x = t1 in t2 *)
 with def : Type :=
  | dfun   : id -> tm -> def
  | dmem   : ty -> def                              
.

Inductive vl : Type :=
| vbool : bool -> vl
| vobj  : list (id*vl) -> id -> list (id * def) -> vl
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
| cl_mem: forall k l m T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TMem m T1 T2)
| cl_all: forall k l m T1 T2,
    closed_rec k l T1 ->
    closed_rec (S k) l T2 ->
    closed_rec k l (TAll m T1 T2)
| cl_bind: forall k l T2,
    closed_rec (S k) l T2 ->
    closed_rec k l (TBind T2)
| cl_var: forall k l x,
    closed_rec k l (TVar (varF x))
| cl_sel: forall k l x m,
    closed_rec k l (TSel (varF x) m)
| cl_and: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TAnd T1 T2)
| cl_or: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TOr T1 T2)
| cl_varh: forall k l x,
    l > x ->
    closed_rec k l (TVar (varH x))
| cl_selh: forall k l x m,
    l > x ->
    closed_rec k l (TSel (varH x) m)
| cl_varb: forall k l i,
    k > i ->
    closed_rec k l (TVar (varB i))
| cl_selb: forall k l i m,
    k > i ->
    closed_rec k l (TSel (varB i) m)
.

Hint Constructors closed_rec.

Definition closed j l T := closed_rec j l T.


Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TVar (varF x)   => TVar (varF x)   (* free var remains free. functional, so we can't check for conflict *)
    | TVar (varH i)   => TVar (varH i)  
    | TVar (varB i)   => TVar (if beq_nat k i then u else varB i) 
    | TSel (varF x) m => TSel (varF x) m (* free var remains free. functional, so we can't check for conflict *)
    | TSel (varH i) m => TSel (varH i) m
    | TSel (varB i) m => TSel (if beq_nat k i then u else varB i) m
    | TAll m T1 T2  => TAll m (open_rec k u T1) (open_rec (S k) u T2)
    | TBind T2    => TBind (open_rec (S k) u T2)
    | TTop        => TTop
    | TBot        => TBot
    | TBool       => TBool
    | TMem m T1 T2  => TMem m (open_rec k u T1) (open_rec k u T2)
    | TAnd T1 T2  => TAnd (open_rec k u T1) (open_rec k u T2)
    | TOr  T1 T2  => TOr  (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

(* sanity check *)
Example open_ex1: open (varF 9) (TAll 0 TBool (TAll 0 (TSel (varB 1) 0) (TSel (varB 1) 0))) =
                      (TAll 0 TBool (TAll 0 (TSel (varF 9) 0) (TSel (varB 1) 0))).
Proof. compute. eauto. Qed.


Fixpoint subst (U : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TBool        => TBool
    | TMem m T1 T2   => TMem m (subst U T1) (subst U T2)
    | TVar (varB i)   => TVar (varB i)
    | TVar (varF i)   => TVar (varF i)
    | TVar (varH i)   => TVar (if beq_nat i 0 then U else varH (i-1))
    | TSel (varB i) m => TSel (varB i) m
    | TSel (varF i) m => TSel (varF i) m
    | TSel (varH i) m => TSel (if beq_nat i 0 then U else varH (i-1)) m
    | TAll m T1 T2   => TAll m (subst U T1) (subst U T2)
    | TBind T2     => TBind (subst U T2)
    | TAnd T1 T2   => TAnd (subst U T1) (subst U T2)
    | TOr  T1 T2   => TOr  (subst U T1) (subst U T2)
  end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TBot         => True
    | TBool        => True
    | TMem m T1 T2   => nosubst T1 /\ nosubst T2
    | TVar (varB i)   => True
    | TVar (varF i)   => True
    | TVar (varH i)   => i <> 0
    | TSel (varB i) m => True
    | TSel (varF i) m => True
    | TSel (varH i) m => i <> 0
    | TAll m T1 T2   => nosubst T1 /\ nosubst T2
    | TBind T2     => nosubst T2
    | TAnd T1 T2   => nosubst T1 /\ nosubst T2
    | TOr  T1 T2   => nosubst T1 /\ nosubst T2
  end.


Hint Unfold open.
Hint Unfold closed.

(* TODO: var *)
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
| stp_mem: forall G1 GH m T1 T2 T3 T4,
    stp G1 GH T3 T1 ->
    stp G1 GH T2 T4 ->
    stp G1 GH (TMem m T1 T2) (TMem m T3 T4)
| stp_sel1: forall G1 GH TX m T2 x,
    index x G1 = Some TX ->
    closed 0 0 TX ->
    stp G1 GH TX (TMem m TBot T2) ->
    stp G1 GH T2 T2 -> (* regularity of stp2 *)
    stp G1 GH (TSel (varF x) m) T2
| stp_sel2: forall G1 GH TX m T1 x,
    index x G1 = Some TX ->
    closed 0 0 TX ->
    stp G1 GH TX (TMem m T1 TTop) ->
    stp G1 GH T1 T1 -> (* regularity of stp2 *)
    stp G1 GH T1 (TSel (varF x) m)
| stp_selb1: forall G1 GH TX m T2 x,
    index x G1 = Some TX ->
    stp G1 [] TX (TBind (TMem m TBot T2)) ->   (* Note GH = [] *)
    stp G1 GH (open (varF x) T2) (open (varF x) T2) -> (* regularity *)
    stp G1 GH (TSel (varF x) m) (open (varF x) T2)
| stp_selb2: forall G1 GH TX m T1 x,
    index x G1 = Some TX ->
    stp G1 [] TX (TBind (TMem m T1 TTop)) ->   (* Note GH = [] *)
    stp G1 GH (open (varF x) T1) (open (varF x) T1) -> (* regularity *)
    stp G1 GH (open (varF x) T1) (TSel (varF x) m)
| stp_selx: forall G1 GH TX x m,
    index x G1 = Some TX ->
    stp G1 GH (TSel (varF x) m) (TSel (varF x) m)
| stp_sela1: forall G1 GH TX m T2 x,
    indexr x GH = Some TX ->
    closed 0 (S x) TX ->
    stp G1 GH TX (TMem m TBot T2) ->   (* not using self name for now *)
    stp G1 GH T2 T2 -> (* regularity of stp2 *)
    stp G1 GH (TSel (varH x) m) T2
| stp_sela2: forall G1 GH TX m T1 x,
    indexr x GH = Some TX ->
    closed 0 (S x) TX ->
    stp G1 GH TX (TMem m T1 TTop) ->   (* not using self name for now *)
    stp G1 GH T1 T1 -> (* regularity of stp2 *)
    stp G1 GH T1 (TSel (varH x) m)
| stp_selab1: forall G1 GH GU GL TX m T2 T2' x,
    indexr x GH = Some TX ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem m TBot T2)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp G1 GL TX (TBind (TMem m TBot T2)) ->
    T2' = (open (varH x) T2) ->
    stp G1 GH T2' T2' -> (* regularity *)
    stp G1 GH (TSel (varH x) m) T2'
| stp_selab2: forall G1 GH GU GL TX m T1 T1' x,
    indexr x GH = Some TX ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem m T1 TTop)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp G1 GL TX (TBind (TMem m T1 TTop)) ->
    T1' = (open (varH x) T1) ->
    stp G1 GH T1' T1' -> (* regularity *)
    stp G1 GH T1' (TSel (varH x) m)
| stp_selax: forall G1 GH TX x m,
    indexr x GH = Some TX  ->
    stp G1 GH (TSel (varH x) m) (TSel (varH x) m)
| stp_all: forall G1 GH m T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) T2 -> (* must not accidentally bind x *)
    closed 1 (length GH) T4 ->
    stp G1 ((0,T1)::GH) (open (varH x) T2) (open (varH x) T2) -> (* regularity *)
    stp G1 ((0,T3)::GH) (open (varH x) T2) (open (varH x) T4) ->
    stp G1 GH (TAll m T1 T2) (TAll m T3 T4)
| stp_bindx: forall G1 GH T1 T2 x,
    x = length GH ->
    closed 1 (length GH) T1 -> (* must not accidentally bind x *)
    closed 1 (length GH) T2 ->
    stp G1 ((0,open (varH x) T2)::GH) (open (varH x) T2) (open (varH x) T2) -> (* regularity *)
    stp G1 ((0,open (varH x) T1)::GH) (open (varH x) T1) (open (varH x) T2) ->
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
| stp_or21: forall G GH T1 T2 T,
    stp G GH T T1 ->
    stp G GH T2 T2 -> (* regularity *)
    stp G GH T (TOr T1 T2)
| stp_or22: forall G GH T1 T2 T,
    stp G GH T T2 ->
    stp G GH T1 T1 -> (* regularity *)
    stp G GH T (TOr T1 T2)
| stp_or1: forall G GH T1 T2 T,
    stp G GH T1 T ->
    stp G GH T2 T ->
    stp G GH (TOr T1 T2) T
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
           has_type env (tvar x) (open (varF x) T1) ->
           stp env [] (TBind T1) (TBind T1) ->
           has_type env (tvar x) (TBind T1)
| t_var_unpack: forall x env T1,
           has_type env (tvar x) (TBind T1) ->
           stp env [] (open (varF x) T1) (open (varF x) T1) ->
           has_type env (tvar x) (open (varF x) T1)
| t_obj: forall env f ds T TX,
           fresh env = f ->
           open (varF f) T = TX ->
           dcs_has_type ((f, TX)::env) f ds T ->
           stp ((f, TX)::env) [] TX TX ->
           stp env [] (TBind T) (TBind T) ->
           has_type env (tobj f ds) (TBind T)
| t_app: forall env f l x T1 T2,
           has_type env f (TAll l T1 T2) ->
           has_type env x T1 ->
           stp env [] T2 T2 ->
           has_type env (tapp f l x) T2
| t_app_var: forall env f l x T1 T2 T2X,
           has_type env f (TAll l T1 T2) ->
           has_type env (tvar x) T1 ->
           open (varF x) T2 = T2X ->
           stp env [] T2X T2X ->
           has_type env (tapp f l (tvar x)) T2X
| t_let: forall env x ex e Tx T,
           has_type env ex Tx ->
           fresh env <= x ->
           has_type ((x, Tx)::env) e T ->
           stp env [] T T ->
           has_type env (tlet x ex e) T

| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2

with dcs_has_type: tenv -> id -> list (id * def) -> ty -> Prop :=
| dt_nil: forall env f,
            dcs_has_type env f nil TTop
| dt_fun: forall env f x y m T1 T2 dcs TS T,
            has_type ((x,open (varF f) T1)::env) y (open (varF x) (open_rec 1 (varF f) T2)) ->
            dcs_has_type env f dcs TS ->
            fresh env = x ->
            m = length dcs ->
            T = tand (TAll m T1 T2) TS ->
            dcs_has_type env f ((m, dfun x y)::dcs) T
| dt_mem: forall env f m T1 dcs TS T,
            dcs_has_type env f dcs TS ->
            m = length dcs ->
            T = tand (TMem m T1 T1) TS ->
            dcs_has_type env f ((m, dmem T1)::dcs) T
.


Definition MAX := 1.

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
| stp2_mem: forall G1 G2 l T1 T2 T3 T4 GH n1 n2,
    stp2 0 false G2 T3 G1 T1 GH n1 ->
    stp2 0 true G1 T2 G2 T4 GH n2 ->
    stp2 0 true G1 (TMem l T1 T2) G2 (TMem l T3 T4) GH (S (n1+n2))

| stp2_mem2: forall m G1 G2 l T1 T2 T3 T4 GH n1 n2,
    stp2 (S m) false G2 T3 G1 T1 GH n1 ->
    stp2 (S m) false G1 T2 G2 T4 GH n2 ->
    stp2 (S m) true G1 (TMem l T1 T2) G2 (TMem l T3 T4) GH (S (n1+n2))


(* strong version, with precise/invertible bounds *)
| stp2_strong_var1: forall G1 G2 GX TX x T2 GH v n1 nv,
    index x G1 = Some v ->
    val_type GX v TX nv ->
    stp2 0 true GX TX G2 T2 GH n1 ->
    stp2 0 true G1 (TVar (varF x)) G2 T2 GH (S (n1))

| stp2_strong_varx: forall G1 G2 v x1 x2 GH n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 0 true G1 (TVar (varF x1)) G2 (TVar (varF x2)) GH n1

(* existing object, but imprecise type *)
| stp2_var1: forall m G1 G2 GX TX x T2 GH n1 n2 v nv,
    index x G1 = Some v ->
    val_type GX v TX nv -> (* note: nv > 1 may include bind *)
    closed 0 0 TX ->
    stp2 (S m) false GX TX G2 T2 GH n1 ->
    stp2 (S m) true G2 T2 G2 T2 GH n2 -> (* regularity *)
    stp2 (S m) true G1 (TVar (varF x)) G2 T2 GH (S (n1+n2))
         
| stp2_varx: forall m G1 G2 v x1 x2 GH n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 (S m) true G1 (TVar (varF x1)) G2 (TVar (varF x2)) GH (S n1)

(* hypothetical object *)
| stp2_vara1: forall m G1 G2 GX TX x T2 GH n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    stp2 (S m) false GX TX G2 T2 GH n1 ->
    stp2 (S m) true G2 T2 G2 T2 GH n2 -> (* regularity *)
    stp2 (S m) true G1 (TVar (varH x)) G2 T2 GH (S (n1+n2))

| stp2_varax: forall m G1 G2 GX TX x GH n1,
    indexr x GH = Some (GX, TX) ->
    stp2 (S m) true G1 (TVar (varH x)) G2 (TVar (varH x)) GH (S n1)
         

         
(* strong version, with precise/invertible bounds *)
| stp2_strong_sel1: forall G1 G2 GX l f ds TX x T2 GH GX' TX' n1 n2 nv,
    index x G1 = Some (vobj GX f ds) ->
    val_type GX' (vobj GX f ds) TX' nv -> (* for downgrade *)
    stp2 0 false GX' TX' G2 (TMem l TBot T2) GH n2 -> (* for downgrade *)
    index l ds = Some (dmem TX) ->
    closed 1 0 TX ->
    stp2 0 true ((f, vobj GX f ds)::GX) (open (varF f) TX) G2 T2 GH n1 ->
    stp2 0 true G1 (TSel (varF x) l) G2 T2 GH (S (n1+n2))

| stp2_strong_sel2: forall G1 G2 GX l f ds TX x T1 GH GX' TX' n1 n2 nv,
    index x G2 = Some (vobj GX f ds) ->
    val_type GX' (vobj GX f ds) TX' nv -> (* for downgrade *)
    stp2 0 false GX' TX' G1 (TMem l T1 TTop) GH n2 -> (* for downgrade *)
    index l ds = Some (dmem TX) ->
    closed 1 0 TX ->
    stp2 0 false G1 T1 ((f, vobj GX f ds)::GX) (open (varF f) TX) GH n1 ->
    stp2 0 true G1 T1 G2 (TSel (varF x) l) GH (S (n1+n2))

| stp2_strong_selx: forall G1 G2 l v x1 x2 GH n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 0 true G1 (TSel (varF x1) l) G2 (TSel (varF x2) l) GH n1


(* existing object, but imprecise type *)
| stp2_sel1: forall m G1 G2 GX l TX x T2 GH n1 n2 v nv,
    index x G1 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stp2 (S m) false GX TX G2 (TMem l TBot T2) GH n1 ->
    stp2 (S m) true G2 T2 G2 T2 GH n2 -> (* regularity *)
    stp2 (S m) true G1 (TSel (varF x) l) G2 T2 GH (S (n1+n2))

(*         
| stp2_selb1: forall m G1 G2 GX l TX x x' T2 GH n1 n2 v nv,
    index x G1 = Some v -> (index x' G2 = Some v \/ closed 0 0 T2) ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stp2 (S ( m)) false GX TX G2 (TBind (TMem l TBot T2)) [] n1 -> (* Note GH = [] *)
    stp2 (S ( m)) true G2 (open (varF x') T2) G2 (open (varF x') T2) GH n2 -> (* regularity *)
    stp2 (S ( m)) true G1 (TSel (varF x) l) G2 (open (varF x') T2) GH (S (n1+n2))
*)

| stp2_sel2: forall m G1 G2 GX l TX x T1 GH n1 n2 v nv,
    index x G2 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stp2 (S m) false GX TX G1 (TMem l T1 TTop) GH n1 ->
    stp2 (S m) true G1 T1 G1 T1 GH n2 -> (* regularity *)
    stp2 (S m) true G1 T1 G2 (TSel (varF x) l) GH (S (n1+n2))

(*         
| stp2_selb2: forall m G1 G2 GX l TX x x' T1 GH n1 n2 v nv,
    index x G2 = Some v -> (index x' G1 = Some v \/ closed 0 0 T1) ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stp2 (S ( m)) false GX TX G1 (TBind (TMem l T1 TTop)) [] n1 -> (* Note GH = [] *)
    stp2 (S ( m)) true G1 (open (varF x') T1) G1 (open (varF x') T1) GH n2 -> (* regularity *)
    stp2 (S ( m)) true G1 (open (varF x') T1) G2 (TSel (varF x) l) GH (S (n1+n2))
 *)
         
| stp2_selx: forall m G1 G2 l v x1 x2 GH n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 (S m) true G1 (TSel (varF x1) l) G2 (TSel (varF x2) l) GH (S n1)

(* hypothetical object *)
| stp2_sela1: forall m G1 G2 GX l TX x T2 GH n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    stp2 (S m) false GX TX G2 (TMem l TBot T2) GH n1 ->
    stp2 (S m) true G2 T2 G2 T2 GH n2 -> (* regularity *)
    stp2 (S m) true G1 (TSel (varH x) l) G2 T2 GH (S (n1+n2))

| stp2_selab1: forall m G1 G2 GX l TX x T2 T2' GH GU GL n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem l TBot T2)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp2 (S m) false GX TX G2 (TBind (TMem l TBot T2)) GL n1 ->
    T2' = (open (varH x) T2) ->
    stp2 (S m) true G2 T2' G2 T2' GH n2 -> (* regularity *)
    stp2 (S m) true G1 (TSel (varH x) l) G2 T2' GH (S (n1+n2))

| stp2_selab2: forall m G1 G2 GX l TX x T1 T1' GH GU GL n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem l T1 TTop)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stp2 (S m) false GX TX G1 (TBind (TMem l T1 TTop)) GL n1 ->
    T1' = (open (varH x) T1) ->
    stp2 (S m) true G1 T1' G1 T1' GH n2 -> (* regularity *)
    stp2 (S m) true G1 T1' G2 (TSel (varH x) l) GH (S (n1+n2))

| stp2_sela2: forall m G1 G2 GX l TX x T1 GH n1 n2,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    stp2 (S m) false GX TX G1 (TMem l T1 TTop) GH n1 ->
    stp2 (S m) true G1 T1 G1 T1 GH n2 -> (* regularity *)
    stp2 (S m) true G1 T1 G2 (TSel (varH x) l) GH (S (n1+n2))


| stp2_selax: forall m G1 G2 GX l TX x GH n1,
    indexr x GH = Some (GX, TX) ->
    stp2 (S m) true G1 (TSel (varH x) l) G2 (TSel (varH x) l) GH (S n1)


| stp2_all: forall m G1 G2 l T1 T2 T3 T4 GH n1 n1' n2,
    stp2 1 false G2 T3 G1 T1 GH n1 ->
    closed 1 (length GH) T2 -> (* must not accidentally bind x *)
    closed 1 (length GH) T4 ->
    stp2 1 false G1 (open (varH (length GH)) T2) G1 (open (varH (length GH)) T2) ((0,(G1, T1))::GH) n1' -> (* regularity *)
    stp2 1 false G1 (open (varH (length GH)) T2) G2 (open (varH (length GH)) T4) ((0,(G2, T3))::GH) n2 ->
    stp2 m true G1 (TAll l T1 T2) G2 (TAll l T3 T4) GH (S (n1+n1'+n2))

| stp2_bind: forall m G1 G2 T1 T2 GH n1 n2,
    closed 1 (length GH) T1 -> (* must not accidentally bind x *)
    closed 1 (length GH) T2 ->
    stp2 1 false G2 (open (varH (length GH)) T2) G2 (open (varH (length GH)) T2) ((0,(G2, open (varH (length GH)) T2))::GH) n2 -> (* regularity *)
    stp2 1 false G1 (open (varH (length GH)) T1) G2 (open (varH (length GH)) T2) ((0,(G1, open (varH (length GH)) T1))::GH) n1 ->
    stp2 m true G1 (TBind T1) G2 (TBind T2) GH (S (n1+n2))

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

| stp2_or21: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m false G1 T G2 T1 GH n1 ->
    stp2 m true G2 T2 G2 T2 GH n2 -> (* regularity *)
    stp2 m true G1 T G2 (TOr T1 T2) GH (S (n1+n2))
| stp2_or22: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m false G1 T G2 T2 GH n1 ->
    stp2 m true G2 T1 G2 T1 GH n2 -> (* regularity *)
    stp2 m true G1 T G2 (TOr T1 T2) GH (S (n1+n2))
| stp2_or1: forall m n1 n2 G1 G2 GH T1 T2 T,
    stp2 m true G1 T1 G2 T GH n1 ->
    stp2 m true G1 T2 G2 T GH n2 ->
    stp2 m true G1 (TOr T1 T2) G2 T GH (S (n1+n2))

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
| v_bool: forall venv b TE,
    (exists n, stp2 0 true [] TBool venv TE [] n) ->
    val_type venv (vbool b) TE 1
| v_obj: forall env venv tenv f ds T TX TE,
    wf_env venv tenv ->
    open (varF f) T = TX ->
    dcs_has_type ((f,TX)::tenv) f ds T ->
    fresh venv = f ->
    (exists n, stp2 0 true ((f, vobj venv f ds)::venv) TX env TE [] n)->
    val_type env (vobj venv f ds) TE 1
| v_pack: forall venv venv3 x v T T2 T3 n,
    index x venv = Some v ->
    val_type venv v T n ->
    open (varF x) T2 = T ->
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
Definition sstpd2 b G1 T1 G2 T2 GH := exists n, stp2 0 b G1 T1 G2 T2 GH n.

Definition valtpd G v T := exists n, val_type G v T n.




Ltac ep := match goal with
             | [ |- stp2 ?M1 ?M2 ?G1 ?T1 ?G2 ?T2 ?GH ?N ] => assert (exists (x:nat), stp2 M1 M2 G1 T1 G2 T2 GH x) as EEX
           end.

Ltac eu := match goal with
             | H: stpd2 _ _ _ _ _ _ |- _ => destruct H as [? H]
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
Lemma stpd2_mem: forall G1 G2 GH l T11 T12 T21 T22,
    stpd2 false G2 T21 G1 T11 GH ->
    stpd2 false G1 T12 G2 T22 GH ->
    stpd2 true G1 (TMem l T11 T12) G2 (TMem l T21 T22) GH.
Proof. intros. repeat eu. eauto. unfold stpd2. eexists. eapply stp2_mem2; eauto. Qed.

Lemma stpd2_var1: forall G1 G2 GX TX x T2 GH v nv,
    index x G1 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stpd2 false GX TX G2 T2 GH ->
    stpd2 true G2 T2 G2 T2 GH ->
    stpd2 true G1 (TVar (varF x)) G2 T2 GH.
Proof. intros. repeat eu. eexists. eapply stp2_var1; eauto. Qed.

Lemma stpd2_varx: forall G1 G2 x1 x2 GH v,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stpd2 true G1 (TVar (varF x1)) G2 (TVar (varF x2)) GH.
Proof. intros. eauto. exists (S 0). eapply stp2_varx; eauto. Qed.

Lemma stpd2_vara1: forall G1 G2 GX TX x T2 GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    stpd2 false GX TX G2 T2 GH ->
    stpd2 true G2 T2 G2 T2 GH ->
    stpd2 true G1 (TVar (varH x)) G2 T2 GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_vara1; eauto. Qed.

Lemma stpd2_varax: forall G1 G2 GX TX x GH,
    indexr x GH = Some (GX, TX) ->
    stpd2 true G1 (TVar (varH x)) G2 (TVar (varH x)) GH.
Proof. intros. exists (S 0). eauto. eapply stp2_varax; eauto. Qed.

Lemma stpd2_sel1: forall G1 G2 GX l TX x T2 GH v nv,
    index x G1 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stpd2 false GX TX G2 (TMem l TBot T2) GH ->
    stpd2 true G2 T2 G2 T2 GH ->
    stpd2 true G1 (TSel (varF x) l) G2 T2 GH.
Proof. intros. repeat eu. eexists. eapply stp2_sel1; eauto. Qed.

(*
Lemma stpd2_selb1: forall G1 G2 GX l TX x x' T2 GH v nv,
    index x G1 = Some v -> (index x' G2 = Some v \/ closed 0 0 T2) ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stpd2 false GX TX G2 (TBind (TMem l TBot T2)) [] -> (* Note GH = [] *)
    stpd2 true G2 (open (varF x') T2) G2 (open (varF x') T2) GH ->
    stpd2 true G1 (TSel (varF x) l) G2 (open (varF x') T2) GH.
Proof. intros. repeat eu. eexists. eapply stp2_selb1; eauto. Qed.
 *)

Lemma stpd2_sel2: forall G1 G2 GX l TX x T1 GH v nv,
    index x G2 = Some v ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stpd2 false GX TX G1 (TMem l T1 TTop) GH ->
    stpd2 true G1 T1 G1 T1 GH ->
    stpd2 true G1 T1 G2 (TSel (varF x) l) GH.
Proof. intros. repeat eu. eexists. eapply stp2_sel2; eauto. Qed.

(*
Lemma stpd2_selb2: forall G1 G2 GX l TX x x' T1 GH v nv,
    index x G2 = Some v -> (index x' G1 = Some v \/ closed 0 0 T1) ->
    val_type GX v TX nv ->
    closed 0 0 TX ->
    stpd2 false GX TX G1 (TBind (TMem l T1 TTop)) [] -> (* Note GH = [] *)
    stpd2 true G1 (open (varF x') T1) G1 (open (varF x') T1) GH ->
    stpd2 true G1 (open (varF x') T1) G2 (TSel (varF x) l) GH.
Proof. intros. repeat eu. eexists. eapply stp2_selb2; eauto. Qed.
 *)

Lemma stpd2_selx: forall G1 G2 l x1 x2 GH v,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stpd2 true G1 (TSel (varF x1) l) G2 (TSel (varF x2) l) GH.
Proof. intros. eauto. exists (S 0). eapply stp2_selx; eauto. Qed.

Lemma stpd2_selab1: forall G1 G2 GX l TX x T2 GH GU GL,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem l TBot T2)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stpd2 false GX TX G2 (TBind (TMem l TBot T2)) GL ->
    stpd2 true G2 (open (varH x) T2) G2 (open (varH x) T2) GH ->
    stpd2 true G1 (TSel (varH x) l) G2 (open (varH x) T2) GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_selab1; eauto. Qed.

Lemma stpd2_selab2: forall G1 G2 GX l TX x T1 T1' GH GU GL,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    closed 0 0 (TBind (TMem l T1 TTop)) ->
    length GL = (S x) ->
    GH = GU ++ GL ->
    stpd2 false GX TX G1 (TBind (TMem l T1 TTop)) GL ->
    T1' = (open (varH x) T1) ->
    stpd2 true G1 T1' G1 T1' GH ->
    stpd2 true G1 T1' G2 (TSel (varH x) l) GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_selab2; eauto. Qed.

Lemma stpd2_sela1: forall G1 G2 GX l TX x T2 GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    stpd2 false GX TX G2 (TMem l TBot T2) GH ->
    stpd2 true G2 T2 G2 T2 GH ->
    stpd2 true G1 (TSel (varH x) l) G2 T2 GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_sela1; eauto. Qed.

Lemma stpd2_sela2: forall G1 G2 GX l TX x T1 GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 (S x) TX ->
    stpd2 false GX TX G1 (TMem l T1 TTop) GH ->
    stpd2 true G1 T1 G1 T1 GH ->
    stpd2 true G1 T1 G2 (TSel (varH x) l) GH.
Proof. intros. repeat eu. eauto. eexists. eapply stp2_sela2; eauto. Qed.


Lemma stpd2_selax: forall G1 G2 GX l TX x GH,
    indexr x GH = Some (GX, TX) ->
    stpd2 true G1 (TSel (varH x) l) G2 (TSel (varH x) l) GH.
Proof. intros. exists (S 0). eauto. eapply stp2_selax; eauto. Qed.


Lemma stpd2_all: forall G1 G2 m T1 T2 T3 T4 GH,
    stpd2 false G2 T3 G1 T1 GH ->
    closed 1 (length GH) T2 ->
    closed 1 (length GH) T4 ->
    stpd2 false G1 (open (varH (length GH)) T2) G1 (open (varH (length GH)) T2) ((0,(G1, T1))::GH) ->
    stpd2 false G1 (open (varH (length GH)) T2) G2 (open (varH (length GH)) T4) ((0,(G2, T3))::GH) ->
    stpd2 true G1 (TAll m T1 T2) G2 (TAll m T3 T4) GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_bind: forall G1 G2 T1 T2 GH,
    closed 1 (length GH) T1 ->
    closed 1 (length GH) T2 ->
    stpd2 false G2 (open (varH (length GH)) T2) G2 (open (varH (length GH)) T2) ((0,(G2, open (varH (length GH)) T2))::GH) ->
    stpd2 false G1 (open (varH (length GH)) T1) G2 (open (varH (length GH)) T2) ((0,(G1, open (varH (length GH)) T1))::GH) ->
    stpd2 true G1 (TBind T1) G2 (TBind T2) GH.
Proof. intros. repeat eu. eauto. Qed.

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

Lemma stpd2_or21: forall G1 G2 GH T1 T2 T,
    stpd2 false G1 T G2 T1 GH ->
    stpd2 true G2 T2 G2 T2 GH ->
    stpd2 true G1 T G2 (TOr T1 T2) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_or22: forall G1 G2 GH T1 T2 T,
    stpd2 false G1 T G2 T2 GH ->
    stpd2 true G2 T1 G2 T1 GH ->
    stpd2 true G1 T G2 (TOr T1 T2) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_or1: forall G1 G2 GH T1 T2 T,
    stpd2 true G1 T1 G2 T GH ->
    stpd2 true G1 T2 G2 T GH ->
    stpd2 true G1 (TOr T1 T2) G2 T GH.
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
        | tobj f ds => Some (Some (vobj env f ds))
        | tapp ef m ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vbool _)) => Some None
                | Some (Some (vobj env2 f ds)) =>
                  match index m ds with
                    | None => Some None
                    | Some (dmem _) => Some None
                    | Some (dfun x ey) =>
                      teval n ((x,vx)::(f,vobj env2 f ds)::env2) ey
                  end
              end
          end
        | tlet x ex ey =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) => teval n ((x,vx)::env) ey
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
(*
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
  try solve [(eapply stp_and2; [eapply stp_and11; crush2 | eapply stp_and12; crush2])];
  try solve [(econstructor; compute; eauto; crush2)];
  try solve [(eapply t_sub; eapply t_var; compute; eauto; crush2)].

Ltac crush_cl :=
  try solve [(econstructor; compute; eauto; crush_cl)].

Ltac crush_wf :=
  try solve [(eapply stp_topx; crush_wf)];
  try solve [(eapply stp_botx; crush_wf)];
  try solve [(eapply stp_bool; crush_wf)];
  try solve [(eapply stp_selx; compute; eauto; crush_wf)];
  try solve [(eapply stp_selax; compute; eauto; crush_wf)];
  try solve [(eapply stp_mem; crush_wf)];
  try solve [(eapply stp_all; [crush_wf | (compute; eauto) | crush_cl | crush_cl | crush_wf | crush_wf])];
  try solve [(eapply stp_bindx; [(compute; eauto) | crush_cl | crush_cl | crush_wf | crush_wf])];
  try solve [(eapply stp_and2; [eapply stp_and11; crush_wf | eapply stp_and12; crush_wf])].

(* define polymorphic identity function *)

Definition polyId := TAll 0 (TBind (TMem 0 TBot TTop)) (TAll 0 (TSel (varB 0) 0) (TSel (varB 1) 0)).

Example ex1: has_type [] (tlet 0 (tobj 0 [(0, dfun 1 (tlet 2 (tobj 2 [(0, (dfun 3 (tvar 3)))]) (tvar 2)))]) (tvar 0)) polyId.
Proof.
  apply t_let with (Tx:=(TBind polyId)).
  apply t_obj with (TX:=polyId).
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=(TBind (TMem 0 TBot TTop))) (T2:=TAll 0 (TSel (varB 0) 0) (TSel (varB 1) 0)).
  unfold open. simpl. apply t_let with (Tx:=(TBind (TAll 0 (TSel (varF 1) 0) (TSel (varF 1) 0)))); crush2.
  assert ((open (varF 2) (TAll 0 (TSel (varF 1) 0) (TSel (varF 1) 0)))=(TAll 0 (TSel (varF 1) 0) (TSel (varF 1) 0))) as A. { unfold open. simpl. reflexivity. }
  rewrite <- A.
  eapply t_var_unpack; crush2.
  eapply dt_nil.
  crush2. crush2. crush2.
  unfold polyId. crush_wf.
  unfold polyId. crush_wf. crush2.
  assert (open (varF 0) polyId=polyId) as A. { unfold open. simpl. reflexivity. }
  rewrite <- A at 2.
  eapply t_var_unpack; crush2.
  unfold polyId. crush_wf.
Qed.


(* instantiate it to bool *)

Example ex2: has_type [(0,polyId)] (tapp (tvar 0) 0 (tlet 1 (tobj 1 [(0,dmem TBool)]) (tvar 1))) (TAll 0 TBool TBool).
Proof.
  eapply t_app. instantiate (1:= (TBind (TMem 0 TBool TBool))).
    { eapply t_sub.
      { eapply t_var. simpl. eauto. crush2. }
      { eapply stp_all; eauto. { eapply stp_bindx; crush2. } compute. eapply cl_all; eauto.
        eapply stp_all. compute. eapply stp_selax; crush2. crush2. crush2. crush2.
        simpl. unfold open. simpl. eapply stp_selax; crush2. crush2.
        eapply stp_all. compute. eapply stp_selab2. crush2.
        crush2. instantiate (1:=TBool). crush2.
        instantiate (1:=[(0, TBind (TMem 0 TBool TBool))]). simpl. reflexivity.
        rewrite app_nil_l. reflexivity.
        crush2. crush2. crush2. crush2. crush2. crush2. crush2.
        simpl. unfold open.
        simpl. eapply stp_selab1. crush2.
        crush2. instantiate (1:=TBool). crush2.
        instantiate (1:=[(0, TBind (TMem 0 TBool TBool))]). simpl. reflexivity.
        instantiate (1:=[(0, TBool)]). simpl. reflexivity.
        crush2. crush2. crush2.
      }
    }
    { eapply t_let; crush2. }
    crush2.
Qed.



(* define brand / unbrand client function *)

Definition brandUnbrand :=
  TAll 0
       (TBind (TMem 0 TBot TTop))
       (TBind (TAll 0
                    (TBind (TAnd
                              (TAll 1 TBool (TSel (varB 3) 0))  (* brand *)
                              (TAll 0 (TSel (varB 2) 0) TBool) (* unbrand *)
                           )
                    )
                    TBool)).

Example ex3:
  has_type []
           (tlet 0
                 (tobj 0 [(0, dfun 1
                  (tobj 2 [(0, dfun 3
                  (tapp (tvar 3) 0 (tapp (tvar 3) 1 ttrue)))]))])
                 (tvar 0))
           brandUnbrand.
Proof.
  apply t_let with (Tx:=(TBind brandUnbrand)).
  apply t_obj with (TX:=brandUnbrand).
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=TBind (TMem 0 TBot TTop))
                     (T2:=       (TBind (TAll 0
                    (TBind (TAnd
                              (TAll 1 TBool (TSel (varB 3) 0))  (* brand *)
                              (TAll 0 (TSel (varB 2) 0) TBool) (* unbrand *)
                           )
                    )
                    TBool))).
  unfold open. simpl. eapply t_obj.
  simpl. reflexivity.
  unfold open. simpl. reflexivity.
  eapply dt_fun.
  instantiate (2:=(TBind (TAnd (TAll 1 TBool (TSel (varF 1) 0)) (TAll 0 (TSel (varF 1) 0) TBool)))). instantiate (1:=TBool).
  eapply t_app.
  instantiate (1:=(TSel (varF 1) 0)).
  assert (open (varF 3) (TAll 0 (TSel (varF 1) 0) TBool)=TAll 0 (TSel (varF 1) 0) TBool) as A. { compute. reflexivity. }
  unfold open. simpl.
  rewrite <- A. eapply t_var_unpack.
  eapply t_sub. eapply t_var. compute. reflexivity.
  crush2.
  eapply stp_bindx. simpl. reflexivity. crush2. crush2.
  unfold open. simpl.
  crush_wf.
  unfold open. simpl.
  eapply stp_and12; crush2.
  unfold open. simpl. crush2.
  eapply t_app.
  instantiate (1:=TBool).
  assert (open (varF 3) (TAll 1 TBool (TSel (varF 1) 0))=TAll 1 TBool (TSel (varF 1) 0) ) as A. { compute. reflexivity. }
  rewrite <- A. eapply t_var_unpack.
  eapply t_sub. eapply t_var. compute. reflexivity.
  crush_wf. crush2. crush_wf. crush2. crush_wf. crush_wf. crush2. crush2. crush2. crush2.
  crush2. crush_wf. crush2. crush2. crush2. crush2. crush_wf. crush_wf. crush2.
  assert (open (varF 0) brandUnbrand=brandUnbrand) as A. { compute. reflexivity. }
  rewrite <- A at 2.
  eapply t_var_unpack. eapply t_var. simpl. reflexivity.
  crush_wf. crush_wf. crush_wf.
Qed.

Example ex4:
  has_type [(1,TAll 0 TBool TBool);(0,brandUnbrand)]
           (tvar 0) (TAll 0 (TBind (TMem 0 TBool TBool)) (TBind (TAll 0 (TBind (TAnd (TAll 1 TBool TBool) (TAll 0 TBool TBool))) TBool))).
Proof.
  eapply t_sub.
  eapply t_var. compute. reflexivity.
  crush_wf.
  eapply stp_all. crush2. crush2. crush2. crush2. crush_wf.
  eapply stp_bindx. crush2. crush2. crush2. crush_wf.
  unfold open. simpl.
  eapply stp_all. eapply stp_bindx. crush2. crush2. crush2.
  unfold open. simpl. crush_wf.
  unfold open. simpl.
  eapply stp_and2.
  eapply stp_and11; crush2. eapply stp_all; crush2.
  unfold open. simpl.
  eapply stp_selab2. compute. reflexivity. crush2.
  instantiate (1:=TBool). crush2.
  instantiate (1:=[(0, TBind (TMem 0 TBool TBool))]). crush2.
  instantiate (1:=[(0, TBool); (0, TAnd (TAll 1 TBool TBool) (TAll 0 TBool TBool));
   (0,
   TAll 0
     (TBind
        (TAnd (TAll 1 TBool (TSel (varH 0) 0))
              (TAll 0 (TSel (varH 0) 0) TBool))) TBool)]). crush2.
  crush2. crush2. crush2.
  eapply stp_and12; crush2.
  eapply stp_all. eapply stp_selab1. compute. reflexivity. crush2.
  instantiate (1:=TBool). crush2.
  instantiate (1:=[(0, TBind (TMem 0 TBool TBool))]). crush2.
  instantiate (1:=[(0, TAnd (TAll 1 TBool TBool) (TAll 0 TBool TBool));
   (0,
   TAll 0
     (TBind
        (TAnd (TAll 1 TBool (TSel (varH 0) 0))
              (TAll 0 (TSel (varH 0) 0) TBool))) TBool)]). crush2.
  crush2. crush2. crush2.
  crush2. crush2. crush2. crush2. crush2. crush2. crush2. crush2. crush2. crush2.
Qed.

Hint Resolve ex4.

(* apply it to identity functions *)

Example ex5:
  has_type [(1,TAll 0 TBool TBool);(0,brandUnbrand)]
           (tapp (tlet 2 (tapp (tvar 0) 0 (tobj 2 [(0,dmem TBool)])) (tvar 2)) 0 (tobj 2 [(1, dfun 3 (tapp (tvar 1) 0 (tvar 3))); (0, dfun 3 (tapp (tvar 1) 0 (tvar 3)))])) TBool.
Proof.
  eapply t_app.
  eapply t_let.
  eapply t_app.
  instantiate (2:=TBind (TMem 0 TBool TBool)).
  instantiate (1:=(TBind (TAll 0
                    (TBind (TAnd
                              (TAll 1 TBool TBool)  (* brand *)
                              (TAll 0 TBool TBool) (* unbrand *)
                           )
                    )
                    TBool))).
  eapply t_sub.
  eapply t_var. compute. reflexivity.
  crush_wf.

  eapply stp_all.
  crush2.
  simpl. reflexivity.
  crush2. crush2. crush_wf.
  unfold open. simpl.
  eapply stp_bindx. simpl. eauto. crush2. crush2. crush_wf.
  unfold open. simpl.
  eapply stp_all. eapply stp_bindx. simpl. eauto. crush2. crush2.
  unfold open. simpl.
  crush_wf.
  unfold open. simpl.
  eapply stp_and2. eapply stp_and11; crush2.
  eapply stp_all.
  crush_wf. crush2. crush2. crush2. crush_wf.
  eapply stp_selab2. compute. reflexivity. crush2.
  instantiate (1:=TBool). crush2.
  instantiate (1:=[(0, TBind (TMem 0 TBool TBool))]). crush2.
  instantiate (1:=[(0, TBool); (0, TAnd (TAll 1 TBool TBool) (TAll 0 TBool TBool));
   (0,
   TAll 0
     (TBind
        (TAnd (TAll 1 TBool (TSel (varH 0) 0))
              (TAll 0 (TSel (varH 0) 0) TBool))) TBool)]). crush2.
  crush2. crush2. crush2.
  eapply stp_and12; crush2.
  eapply stp_all. crush2. eapply stp_selab1. compute. reflexivity. crush2.
  instantiate (1:=TBool). crush2.
  instantiate (1:=[(0, TBind (TMem 0 TBool TBool))]). crush2.
  instantiate (1:=[(0, TAnd (TAll 1 TBool TBool) (TAll 0 TBool TBool));
   (0,
   TAll 0
     (TBind
        (TAnd (TAll 1 TBool (TSel (varH 0) 0))
              (TAll 0 (TSel (varH 0) 0) TBool))) TBool)]). crush2.
  crush2. crush2. crush_wf.
  crush2. crush2.
  crush2. crush_wf. crush_wf. crush2. crush2. crush2. crush_wf. crush_wf.

  crush2.

  crush_wf. crush2.

  instantiate (1:=(TBind (TAnd (TAll 1 TBool TBool) (TAll 0 TBool TBool)))).
  assert (open (varF 2) (TAll 0 (TBind (TAnd (TAll 1 TBool TBool) (TAll 0 TBool TBool))) TBool) = (TAll 0 (TBind (TAnd (TAll 1 TBool TBool) (TAll 0 TBool TBool))) TBool)) as A. {
    compute. reflexivity.
  }
  rewrite <- A. eapply t_var_unpack. eapply t_var. compute. reflexivity.

  crush_wf. crush_wf. crush_wf.

  eapply t_obj. eauto. unfold open. simpl. reflexivity.
  eapply dt_fun.
  instantiate (1:=TBool). unfold open. simpl.
  eapply t_app. eapply t_var. compute. reflexivity.
  crush_wf.
  instantiate (1:=TBool). unfold open. simpl. crush2. crush_wf.
  instantiate (1:=TAll 0 TBool TBool).
  eapply dt_fun.
  instantiate (1:=TBool). unfold open. simpl.
  eapply t_app. eapply t_var. compute. reflexivity.
  crush_wf.
  instantiate (1:=TBool). unfold open. simpl. crush2. crush_wf.
  eapply dt_nil.
  eauto. eauto. simpl. reflexivity. eauto. eauto. eauto.
  crush_wf. crush_wf. crush_wf.
Qed.

(* test expansion *)

Example ex6:
  has_type [(1,TSel (varF 0) 0);(0,TMem 0 TBot (TBind (TAll 0 TBool (TSel (varB 1) 0))))]
           (tvar 1) (TAll 0 TBool (TSel (varF 1) 0)).
Proof.
  remember (TAll 0 TBool (TSel (varF 1) 0)) as T.
  assert (T = open (varF 1) (TAll 0 TBool (TSel (varB 1) 0))). compute. eauto.
  rewrite H.
  eapply t_var_unpack. eapply t_sub. eapply t_var. compute. eauto. crush_wf. crush2. crush_wf.
Qed.


Example ex7:
  stp [(1,TSel (varF 0) 0);(0,TMem 0 TBot (TBind (TMem 0 TBot (TAll 0 TBool (TSel (varB 1) 0)))))] []
           (TSel (varF 1) 0) (TAll 0 TBool (TSel (varF 1) 0)).
Proof.
  remember (TAll 0 TBool (TSel (varF 1) 0)) as T.
  assert (T = open (varF 1) (TAll 0 TBool (TSel (varB 1) 0))). compute. eauto.
  rewrite H.
  eapply stp_selb1. compute. eauto.
  eapply stp_sel1. compute. eauto.
  crush2.
  eapply stp_mem. eauto.
  eapply stp_bindx; crush2.
  eapply stp_bindx; crush2.
  crush2.
Qed.

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

Example paper_list_nil_head:
  has_type
    []
    (tobj 0
          [(1, dfun 1 (tlet 2 (tobj 2 [(1, dfun 3 (tapp (tvar 2) 1 (tvar 3)));
                                       (0, dmem TBot)])
                            (tvar 2)));
           (0, dmem (TBind (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop))))
          ])
    (TBind (TAnd
              (TAll 1 TTop (TAnd (TSel (varB 1) 0) (TBind (TMem 0 TBot TBot))))
              (TMem 0
                    TBot
                    (TBind (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop)))))).
Proof.
  apply t_sub with (T1:=(TBind (TAnd
                           (TAll 1 TTop (TAnd (TSel (varB 1) 0) (TBind (TMem 0 TBot TBot))))
                           (TMem 0
                                 (TBind (TAnd
                                           (TAll 1 TTop (TSel (varB 1) 0))
                                           (TMem 0 TBot TTop)))
                                 (TBind (TAnd
                                           (TAll 1 TTop (TSel (varB 1) 0))
                                           (TMem 0 TBot TTop))))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=TTop) (T2:=(TAnd (TSel (varB 1) 0) (TBind (TMem 0 TBot TBot)))).
  apply t_let with (Tx:=(TBind (TAnd (TAll 1 TTop TBot) (TMem 0 TBot TBot)))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=TTop) (T2:=TBot).
  simpl. unfold open at 3. simpl. eapply t_app.
  eapply t_sub. eapply t_var. compute. reflexivity. crush_wf.
  apply stp_and11. crush_wf. crush_wf. crush2. crush2.
  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto.
  simpl. reflexivity. crush_wf. crush_wf. eauto.
  simpl. unfold open at 2. simpl.
  eapply t_sub. eapply t_var. compute. eauto. crush_wf.
  eapply stp_and2. eapply stp_sel2. compute. reflexivity. crush2.
  eapply stp_and12. crush2. crush_wf. crush_wf.
  eapply stp_bindx. eauto. crush2. crush2. crush_wf.
  unfold open. simpl. eapply stp_and12. crush_wf. crush_wf.
  unfold open. simpl. crush_wf.

  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto.
  simpl. reflexivity. crush_wf. crush_wf.

  crush2.
Qed.

Example paper_list_nil:
  has_type
    []
    (tobj 0
          [(1, dfun 1 (tlet 2 (tobj 2 [(2, dfun 3 (tapp (tvar 2) 2 (tvar 3)));
                                       (1, dfun 3 (tapp (tvar 2) 1 (tvar 3)));
                                       (0, dmem TBot)])
                            (tvar 2)));
           (0, dmem (TBind (TAnd
                              (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                            (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop)))))
          ])
    (TBind (TAnd
              (TAll 1 TTop (TAnd (TSel (varB 1) 0) (TBind (TMem 0 TBot TBot))))
              (TMem 0
                    TBot
                    (TBind (TAnd
                              (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                           (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop))))))).
Proof.
  apply t_sub with (T1:=(TBind (TAnd
                           (TAll 1 TTop (TAnd (TSel (varB 1) 0) (TBind (TMem 0 TBot TBot))))
                           (TMem 0
                                 (TBind (TAnd
                                           (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                                        (TAnd
                                           (TAll 1 TTop (TSel (varB 1) 0))
                                           (TMem 0 TBot TTop))))
                                 (TBind (TAnd
                                           (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                                        (TAnd
                                           (TAll 1 TTop (TSel (varB 1) 0))
                                           (TMem 0 TBot TTop)))))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=TTop) (T2:=(TAnd (TSel (varB 1) 0) (TBind (TMem 0 TBot TBot)))).
  apply t_let with (Tx:=(TBind (TAnd (TAll 2 TTop TBot) (TAnd (TAll 1 TTop TBot) (TMem 0 TBot TBot))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=TTop) (T2:=TBot).
  simpl. unfold open at 3. simpl. eapply t_app.
  eapply t_sub. eapply t_var. compute. reflexivity. crush_wf.
  apply stp_and11. crush_wf. crush_wf. crush2. crush2.
  eapply dt_fun with (T1:=TTop) (T2:=TBot).
  simpl. unfold open at 3. simpl. eapply t_app.
  eapply t_sub. eapply t_var. compute. reflexivity. crush_wf.
  apply stp_and12. apply stp_and11. crush_wf. crush_wf. crush2. crush2. crush2.
  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto.
  simpl. reflexivity. eauto. eauto. simpl. reflexivity.
  crush_wf. crush_wf. eauto.
  simpl. unfold open at 2. simpl.
  eapply t_sub. eapply t_var. compute. eauto. crush_wf.
  eapply stp_and2. eapply stp_sel2. compute. reflexivity. crush2.
  eapply stp_and12.
  eapply stp_mem. eapply stp_bindx. eauto. crush_cl. crush_cl.
  unfold open. simpl. crush_wf. unfold open. simpl.

  apply stp_and2. eapply stp_and11. eapply stp_all. crush_wf. eauto. crush_cl. crush_cl.
  unfold open. simpl. crush_wf. unfold open. simpl. eapply stp_bot. crush_wf. crush_wf.
  eapply stp_and12. eapply stp_and2. eapply stp_and11. eapply stp_all. crush_wf. eauto.
  crush_cl. crush_cl. unfold open. simpl. crush_wf. unfold open. simpl. eapply stp_bot.
  crush_wf. crush_wf. eapply stp_and12. eapply stp_mem. crush_wf. crush2. crush_wf.
  crush_wf. eapply stp_top. crush_wf. crush_wf. crush_wf.

  eapply stp_bindx. eauto. crush2. crush2. crush_wf.
  unfold open. simpl. eapply stp_and12. eapply stp_and12. crush_wf. crush_wf. crush_wf.
  unfold open. simpl. crush_wf.

  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto.
  simpl. reflexivity. crush_wf. crush_wf.

  eapply stp_bindx. eauto. crush_cl. crush_cl. crush_wf. unfold open. simpl.
  eapply stp_and2. eapply stp_and11. crush_wf. crush_wf. eapply stp_and12.
  eapply stp_mem. eapply stp_bot. crush_wf. crush_wf. crush_wf.
Qed.

Example paper_list_cons_head:
  has_type
    []
    (tobj 0
          [(1, dfun 1(*type T*) (tlet 2 (tobj 2
          [(0, dfun 3(*hd*) (tlet 4 (tobj 4 [(0, dfun 5(*tl*) (tlet 6 (tobj 6
          [(1, dfun 7 (tvar 3));
           (0, dmem (TSel (varF 1) 0))]) (tvar 6)))]) (tvar 4)))]) (tvar 2)));
           (0, dmem (TBind (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop))))
          ])
    (TBind (TAnd
              (TAll 1 (TMem 0 TBot TTop)
                    (TAll 0 (TSel (varB 0) 0)
                          (TAll 0 (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0))))
                                (TAnd (TSel (varB 3) 0) (TBind (TMem 0 TBot (TSel (varB 3) 0)))))))
              (TMem 0
                    TBot
                    (TBind (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop)))))).
Proof.
  apply t_sub with (T1:=
    (TBind (TAnd
              (TAll 1 (TMem 0 TBot TTop)
                    (TAll 0 (TSel (varB 0) 0)
                          (TAll 0 (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0))))
                                (TAnd (TSel (varB 3) 0) (TBind (TMem 0 TBot (TSel (varB 3) 0)))))))
              (TMem 0
                    (TBind (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop)))
                    (TBind (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop))))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=(TMem 0 TBot TTop))
                     (T2:=(TAll 0 (TSel (varB 0) 0)
                          (TAll 0 (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0))))
                                (TAnd (TSel (varB 3) 0) (TBind (TMem 0 TBot (TSel (varB 3) 0))))))).
  apply t_let with (Tx:=(TBind
                           (TAll 0 (TSel (varF 1) 0)
                          (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                                (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=(TSel (varF 1) 0))
                     (T2:=(TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                                (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))).
  apply t_let with (Tx:=(TBind (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                                     (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=(TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))
                     (T2:=(TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))).
  apply t_let with (Tx:=(TBind (TAnd (TAll 1 TTop (TSel (varF 1) 0)) (TMem 0 (TSel (varF 1) 0) (TSel (varF 1) 0))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=TTop) (T2:=(TSel (varF 1) 0)).
  simpl. unfold open. simpl. crush2.
  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto.
  simpl. reflexivity. crush_wf. crush_wf. eauto.
  simpl. unfold open. simpl.
  eapply t_sub.
  eapply t_var. compute. eauto. crush_wf.
  compute.
  eapply stp_and2. eapply stp_sel2. compute. reflexivity. crush2.
  eapply stp_and12. eapply stp_mem. eapply stp_bindx.
  eauto. crush2. crush2.
  unfold open. simpl. crush_wf.
  unfold open. simpl.
  eapply stp_and2. eapply stp_and11.
  eapply stp_all. crush_wf. eauto. crush2. crush2.
  unfold open. simpl. crush_wf. unfold open. simpl.
  eapply stp_sela2. compute. reflexivity. crush2.
  eapply stp_and12. crush2. crush2. crush2. crush_wf.
  eapply stp_and12. crush2. crush_wf. crush2. crush_wf. crush_wf.
  eapply stp_bindx. eauto. crush2. crush2. crush_wf.
  unfold open. simpl. eapply stp_and12. crush2. crush_wf. crush_wf.
  eapply dt_nil. eauto. eauto. simpl. reflexivity. crush_wf. crush_wf.
  eauto.
  unfold open. simpl.
  assert (open (varF 4)
               (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                     (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))) =
          (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))) as A. {
    compute. reflexivity.
  }
  rewrite <- A at 3. apply t_var_unpack. apply t_var. compute. reflexivity. crush_wf.
  crush_wf. unfold open. simpl. crush_wf.
  eapply dt_nil. eauto. eauto. simpl. reflexivity. crush_wf. crush_wf. crush2.

  unfold open. simpl.
  assert (open (varF 2) (TAll 0 (TSel (varF 1) 0)
        (TAll 0
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))) =
          (TAll 0 (TSel (varF 1) 0)
        (TAll 0
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))))) as B. {
    compute. reflexivity.
  }
  rewrite <- B at 2. apply t_var_unpack. apply t_var. compute. reflexivity. crush_wf.
  unfold open. simpl. crush_wf. unfold open. simpl. crush_wf.

  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto. simpl. reflexivity.

  crush_wf. crush_wf.

  eapply stp_bindx. eauto. crush_cl. crush_cl. crush_wf.
  unfold open. simpl. eapply stp_and2.
  eapply stp_and11; crush_wf.
  eapply stp_and12. eapply stp_mem. eapply stp_bot. crush_wf. crush_wf. crush_wf.

Qed.

Example paper_list_cons:
  has_type
    []
    (tobj 0
          [(1, dfun 1(*type T*) (tlet 2 (tobj 2
          [(0, dfun 3(*hd*) (tlet 4 (tobj 4 [(0, dfun 5(*tl*) (tlet 6 (tobj 6
          [(2, dfun 7 (tvar 5)); (1, dfun 7 (tvar 3));
           (0, dmem (TSel (varF 1) 0))]) (tvar 6)))]) (tvar 4)))]) (tvar 2)));
           (0, dmem (TBind (TAnd
                              (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                           (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop)))))
          ])
    (TBind (TAnd
              (TAll 1 (TMem 0 TBot TTop)
                    (TAll 0 (TSel (varB 0) 0)
                          (TAll 0 (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0))))
                                (TAnd (TSel (varB 3) 0) (TBind (TMem 0 TBot (TSel (varB 3) 0)))))))
              (TMem 0
                    TBot
                    (TBind (TAnd
                              (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                           (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop))))))).
Proof.
  apply t_sub with (T1:=
    (TBind (TAnd
              (TAll 1 (TMem 0 TBot TTop)
                    (TAll 0 (TSel (varB 0) 0)
                          (TAll 0 (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0))))
                                (TAnd (TSel (varB 3) 0) (TBind (TMem 0 TBot (TSel (varB 3) 0)))))))
              (TMem 0
                    (TBind (TAnd
                              (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                           (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop))))
                    (TBind (TAnd
                              (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                           (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop)))))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=(TMem 0 TBot TTop))
                     (T2:=(TAll 0 (TSel (varB 0) 0)
                          (TAll 0 (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0))))
                                (TAnd (TSel (varB 3) 0) (TBind (TMem 0 TBot (TSel (varB 3) 0))))))).
  apply t_let with (Tx:=(TBind
                           (TAll 0 (TSel (varF 1) 0)
                          (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                                (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=(TSel (varF 1) 0))
                     (T2:=(TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                                (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))).
  apply t_let with (Tx:=(TBind (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                                     (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=(TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))
                     (T2:=(TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))).
  apply t_let with (Tx:=(TBind (TAnd
                                  (TAll 2 TTop (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))
                                  (TAnd (TAll 1 TTop (TSel (varF 1) 0)) (TMem 0 (TSel (varF 1) 0) (TSel (varF 1) 0)))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=TTop) (T2:=(TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))).
  simpl. unfold open. simpl. crush2.
  eapply dt_fun with (T1:=TTop) (T2:=(TSel (varF 1) 0)).
  simpl. unfold open. simpl. crush2.
  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto.
  simpl. reflexivity. eauto. eauto. simpl. reflexivity. crush_wf. crush_wf. eauto.
  simpl. unfold open. simpl.
  eapply t_sub.
  eapply t_var. compute. eauto. crush_wf.

  eapply stp_and2. eapply stp_sel2. compute. reflexivity. crush_cl.
  eapply stp_and12. eapply stp_mem. eapply stp_bindx.
  eauto. crush2. crush2.
  unfold open. simpl. crush_wf.
  unfold open. simpl.
  eapply stp_and2. eapply stp_and11.
  eapply stp_all. crush_wf. eauto. crush2. crush2.
  unfold open. simpl. crush_wf. unfold open. simpl.
  eapply stp_and2. eapply stp_and11. crush_wf. crush_wf. eapply stp_and12.
  eapply stp_bindx. eauto. crush_cl. crush_cl. crush_wf. unfold open. simpl.
  eapply stp_mem. crush_wf. unfold open. simpl.
  eapply stp_sela2. compute. reflexivity. crush_cl.
  eapply stp_and12. eapply stp_and12. crush2. crush_wf. crush_wf. crush_wf. crush_wf.
  crush_wf.
  eapply stp_and12. eapply stp_and2. eapply stp_and11. eapply stp_all. crush_wf. eauto.
  crush_cl. crush_cl. unfold open. simpl. crush_wf. unfold open. simpl.
  eapply stp_sela2. compute. reflexivity. crush_cl.
  eapply stp_and12. eapply stp_and12. crush2. crush_wf. crush_wf. crush_wf. crush_wf.
  eapply stp_and12. crush2. crush_wf. crush_wf. eapply stp_top. crush_wf. crush_wf.
  crush_wf. eapply stp_bindx. eauto. crush_cl. crush_cl. crush_wf. unfold open. simpl.
  eapply stp_and12. eapply stp_and12. crush2. crush_wf. crush_wf. crush_wf.

  eapply dt_nil. eauto. eauto. simpl. reflexivity. crush_wf. crush_wf.
  eauto.
  unfold open. simpl.
  assert (open (varF 4)
               (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                     (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))) =
          (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))) as A. {
    compute. reflexivity.
  }
  rewrite <- A at 3. apply t_var_unpack. apply t_var. compute. reflexivity. crush_wf.
  crush_wf. unfold open. simpl. crush_wf.
  eapply dt_nil. eauto. eauto. simpl. reflexivity. crush_wf. crush_wf. crush2.

  unfold open. simpl.
  assert (open (varF 2) (TAll 0 (TSel (varF 1) 0)
        (TAll 0
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))) =
          (TAll 0 (TSel (varF 1) 0)
        (TAll 0
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))))) as B. {
    compute. reflexivity.
  }
  rewrite <- B at 2. apply t_var_unpack. apply t_var. compute. reflexivity. crush_wf.
  unfold open. simpl. crush_wf. unfold open. simpl. crush_wf.

  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto. simpl. reflexivity.

  crush_wf. crush_wf.

  eapply stp_bindx. eauto. crush_cl. crush_cl. crush_wf.
  unfold open. simpl. eapply stp_and2.
  eapply stp_and11; crush_wf.
  eapply stp_and12. eapply stp_mem. eapply stp_bot. crush_wf. crush_wf. crush_wf.

Qed.

Example paper_list:
  has_type
    []
    (tobj 0
          [(2, dfun 1 (tlet 2 (tobj 2 [(2, dfun 3 (tapp (tvar 2) 2 (tvar 3)));
                                       (1, dfun 3 (tapp (tvar 2) 1 (tvar 3)));
                                       (0, dmem TBot)])
                            (tvar 2)));
           (1, dfun 1(*type T*) (tlet 2 (tobj 2
          [(0, dfun 3(*hd*) (tlet 4 (tobj 4 [(0, dfun 5(*tl*) (tlet 6 (tobj 6
          [(2, dfun 7 (tvar 5)); (1, dfun 7 (tvar 3));
           (0, dmem (TSel (varF 1) 0))]) (tvar 6)))]) (tvar 4)))]) (tvar 2)));
           (0, dmem (TBind (TAnd
                              (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                           (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop)))))
          ])
    (TBind (TAnd
              (TAll 2 TTop (TAnd (TSel (varB 1) 0) (TBind (TMem 0 TBot TBot))))
           (TAnd
              (TAll 1 (TMem 0 TBot TTop)
                    (TAll 0 (TSel (varB 0) 0)
                          (TAll 0 (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0))))
                                (TAnd (TSel (varB 3) 0) (TBind (TMem 0 TBot (TSel (varB 3) 0)))))))
              (TMem 0
                    TBot
                    (TBind (TAnd
                              (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                           (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop)))))))).
Proof.
  apply t_sub with (T1:=
    (TBind (TAnd
              (TAll 2 TTop (TAnd (TSel (varB 1) 0) (TBind (TMem 0 TBot TBot))))
           (TAnd
              (TAll 1 (TMem 0 TBot TTop)
                    (TAll 0 (TSel (varB 0) 0)
                          (TAll 0 (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0))))
                                (TAnd (TSel (varB 3) 0) (TBind (TMem 0 TBot (TSel (varB 3) 0)))))))
              (TMem 0
                    (TBind (TAnd
                              (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                           (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop))))
                    (TBind (TAnd
                              (TAll 2 TTop (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0)))))
                           (TAnd
                              (TAll 1 TTop (TSel (varB 1) 0))
                              (TMem 0 TBot TTop))))))))).
  eapply t_obj.
  eauto. compute. reflexivity.

  eapply dt_fun with (T1:=TTop) (T2:=(TAnd (TSel (varB 1) 0) (TBind (TMem 0 TBot TBot)))).
  apply t_let with (Tx:=(TBind (TAnd (TAll 2 TTop TBot) (TAnd (TAll 1 TTop TBot) (TMem 0 TBot TBot))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=TTop) (T2:=TBot).
  simpl. unfold open at 3. simpl. eapply t_app.
  eapply t_sub. eapply t_var. compute. reflexivity. crush_wf.
  apply stp_and11. crush_wf. crush_wf. crush2. crush2.
  eapply dt_fun with (T1:=TTop) (T2:=TBot).
  simpl. unfold open at 3. simpl. eapply t_app.
  eapply t_sub. eapply t_var. compute. reflexivity. crush_wf.
  apply stp_and12. apply stp_and11. crush_wf. crush_wf. crush2. crush2. crush2.
  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto.
  simpl. reflexivity. eauto. eauto. simpl. reflexivity.
  crush_wf. crush_wf. eauto.
  simpl. unfold open at 2. simpl.
  eapply t_sub. eapply t_var. compute. eauto. crush_wf.
  eapply stp_and2. eapply stp_sel2. compute. reflexivity. crush2.
  eapply stp_and12. eapply stp_and12.
  eapply stp_mem. eapply stp_bindx. eauto. crush_cl. crush_cl.
  unfold open. simpl. crush_wf. unfold open. simpl.

  apply stp_and2. eapply stp_and11. eapply stp_all. crush_wf. eauto. crush_cl. crush_cl.
  unfold open. simpl. crush_wf. unfold open. simpl. eapply stp_bot. crush_wf. crush_wf.
  eapply stp_and12. eapply stp_and2. eapply stp_and11. eapply stp_all. crush_wf. eauto.
  crush_cl. crush_cl. unfold open. simpl. crush_wf. unfold open. simpl. eapply stp_bot.
  crush_wf. crush_wf. eapply stp_and12. eapply stp_mem. crush_wf. crush2. crush_wf.
  crush_wf. eapply stp_top. crush_wf. crush_wf. crush_wf.

  crush_wf.

  eapply stp_bindx. eauto. crush2. crush2. crush_wf.
  unfold open. simpl. eapply stp_and12. eapply stp_and12. crush_wf. crush_wf. crush_wf.
  unfold open. simpl. crush_wf.

  eapply dt_fun with (T1:=(TMem 0 TBot TTop))
                     (T2:=(TAll 0 (TSel (varB 0) 0)
                          (TAll 0 (TAnd (TSel (varB 2) 0) (TBind (TMem 0 TBot (TSel (varB 2) 0))))
                                (TAnd (TSel (varB 3) 0) (TBind (TMem 0 TBot (TSel (varB 3) 0))))))).
  apply t_let with (Tx:=(TBind
                           (TAll 0 (TSel (varF 1) 0)
                          (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                                (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=(TSel (varF 1) 0))
                     (T2:=(TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                                (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))).
  apply t_let with (Tx:=(TBind (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                                     (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=(TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))
                     (T2:=(TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))).
  apply t_let with (Tx:=(TBind (TAnd
                                  (TAll 2 TTop (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))
                                  (TAnd (TAll 1 TTop (TSel (varF 1) 0)) (TMem 0 (TSel (varF 1) 0) (TSel (varF 1) 0)))))).
  eapply t_obj.
  eauto. compute. reflexivity.
  eapply dt_fun with (T1:=TTop) (T2:=(TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))).
  simpl. unfold open. simpl. crush2.
  eapply dt_fun with (T1:=TTop) (T2:=(TSel (varF 1) 0)).
  simpl. unfold open. simpl. crush2.
  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto.
  simpl. reflexivity. eauto. eauto. simpl. reflexivity. crush_wf. crush_wf. eauto.
  simpl. unfold open. simpl.
  eapply t_sub.
  eapply t_var. compute. eauto. crush_wf.

  eapply stp_and2. eapply stp_sel2. compute. reflexivity. crush_cl.
  eapply stp_and12. eapply stp_and12. eapply stp_mem. eapply stp_bindx.
  eauto. crush2. crush2.
  unfold open. simpl. crush_wf.
  unfold open. simpl.
  eapply stp_and2. eapply stp_and11.
  eapply stp_all. crush_wf. eauto. crush2. crush2.
  unfold open. simpl. crush_wf. unfold open. simpl.
  eapply stp_and2. eapply stp_and11. crush_wf. crush_wf. eapply stp_and12.
  eapply stp_bindx. eauto. crush_cl. crush_cl. crush_wf. unfold open. simpl.
  eapply stp_mem. crush_wf. unfold open. simpl.
  eapply stp_sela2. compute. reflexivity. crush_cl.
  eapply stp_and12. eapply stp_and12. crush2. crush_wf. crush_wf. crush_wf. crush_wf.
  crush_wf.
  eapply stp_and12. eapply stp_and2. eapply stp_and11. eapply stp_all. crush_wf. eauto.
  crush_cl. crush_cl. unfold open. simpl. crush_wf. unfold open. simpl.
  eapply stp_sela2. compute. reflexivity. crush_cl.
  eapply stp_and12. eapply stp_and12. crush2. crush_wf. crush_wf. crush_wf. crush_wf.
  eapply stp_and12. crush2. crush_wf. crush_wf. eapply stp_top. crush_wf. crush_wf.
  crush_wf. eapply stp_bindx. eauto. crush_cl. crush_cl. crush_wf. unfold open. simpl.
  crush_wf. eapply stp_bindx. eauto. crush_cl. crush_cl. unfold open. simpl. crush_wf.
  unfold open. simpl.
  eapply stp_and12. eapply stp_and12. crush2. crush_wf. crush_wf. crush_wf.

  eapply dt_nil. eauto. eauto. simpl. reflexivity. crush_wf. crush_wf.
  eauto.
  unfold open. simpl.
  assert (open (varF 4)
               (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                     (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))) =
          (TAll 0 (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
                (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))) as A. {
    compute. reflexivity.
  }
  rewrite <- A at 3. apply t_var_unpack. apply t_var. compute. reflexivity. crush_wf.
  crush_wf. unfold open. simpl. crush_wf.
  eapply dt_nil. eauto. eauto. simpl. reflexivity. crush_wf. crush_wf. crush2.

  unfold open. simpl.
  assert (open (varF 2) (TAll 0 (TSel (varF 1) 0)
        (TAll 0
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0)))))) =
          (TAll 0 (TSel (varF 1) 0)
        (TAll 0
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))
           (TAnd (TSel (varF 0) 0) (TBind (TMem 0 TBot (TSel (varF 1) 0))))))) as B. {
    compute. reflexivity.
  }
  rewrite <- B at 2. apply t_var_unpack. apply t_var. compute. reflexivity. crush_wf.
  unfold open. simpl. crush_wf. unfold open. simpl. crush_wf.

  eapply dt_mem. eapply dt_nil. eauto. simpl. reflexivity. eauto. eauto. simpl. reflexivity.

  eauto. eauto. simpl. reflexivity.
  crush_wf. crush_wf.

  eapply stp_bindx. eauto. crush_cl. crush_cl. crush_wf.
  unfold open. simpl. eapply stp_and2.
  eapply stp_and11; crush_wf.
  eapply stp_and12. eapply stp_and2.
  eapply stp_and11; crush_wf. eapply stp_and12.
  eapply stp_mem. eapply stp_bot. crush_wf. crush_wf. crush_wf.
  crush_wf.

Qed.

*)

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
    | TMem m T1 T2   => TMem m (splice n T1) (splice n T2)
    | TVar (varB i)   => TVar (varB i) 
    | TVar (varF i)   => TVar (varF i) 
    | TVar (varH i)   => TVar (varH (if le_lt_dec n i  then (i+1) else i)) 
    | TSel (varB i) m => TSel (varB i) m
    | TSel (varF i) m => TSel (varF i) m
    | TSel (varH i) m => TSel (varH (if le_lt_dec n i  then (i+1) else i)) m
    | TAll m T1 T2   => TAll m (splice n T1) (splice n T2)
    | TBind T2   => TBind (splice n T2)
    | TAnd T1 T2 => TAnd (splice n T1) (splice n T2)
    | TOr  T1 T2 => TOr  (splice n T1) (splice n T2)
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
(open_rec j (varH (n + S k)) (splice (length G) T)) =
(splice (length G) (open_rec j (varH (n + k)) T)).
Proof.
  intros X G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto.

  destruct v; try solve [compute; reflexivity]. simpl.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  case_eq (le_lt_dec (length G) (n+k)); intros E2 LE; simpl; eauto.
  assert (n + S k=n + k + 1) as R by omega. rewrite R. reflexivity.
  omega.

  destruct v; try solve [compute; reflexivity]. simpl.
  case_eq (beq_nat j i0); intros E; simpl; eauto.
  case_eq (le_lt_dec (length G) (n+k)); intros E2 LE; simpl; eauto.
  assert (n + S k=n + k + 1) as R by omega. rewrite R. reflexivity.
  omega.
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
  unfold closed. apply cl_varh. omega.
  unfold closed. apply cl_varh. omega.
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
  unfold closed. apply cl_varh. omega.
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
  intros. remember H. clear Heqc.
  induction H; simpl; repeat sp; repeat (match goal with
    | H: splice ?N ?T = ?T |- _ => rewrite H
  end); eauto.
  case_eq (le_lt_dec n x); intros E LE. omega. reflexivity.
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
 Case "TVarB". econstructor. omega.
 Case "TSelB". econstructor. omega.
Qed.

Lemma closed_upgrade_free: forall i l k T,
 closed_rec i l T ->
 k >= l ->
 closed_rec i k T.
Proof.
 intros. generalize dependent k. induction H; intros; eauto.
 Case "TVarH". econstructor. omega.
 Case "TSelH". econstructor. omega.
Qed.

Lemma closed_var: forall j n V l2, closed j n (TVar V) -> closed j n (TSel V l2) /\ closed j n (TVar V).
Proof.
  intros. inversion H; subst; split; constructor; assumption.
Qed.

Lemma closed_sel: forall j n V l1 l2, closed j n (TSel V l1) -> closed j n (TSel V l2) /\ closed j n (TVar V).
Proof.
  intros. inversion H; subst; split; constructor; assumption.
Qed.

Lemma closed_open: forall j n V l T, closed (j+1) n T -> closed j n (TSel V l) -> closed j n (open_rec j V T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H; unfold closed; try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto. eapply closed_upgrade. eauto. eauto.

  - Case "TVarB". simpl.
    case_eq (beq_nat j i); intros E. eapply closed_sel. auto. eassumption.
    econstructor. eapply beq_nat_false_iff in E. omega.
  - eauto.

  - Case "TSelB". simpl.
    case_eq (beq_nat j i0); intros E. eapply closed_sel. eassumption.
    econstructor. eapply beq_nat_false_iff in E. omega.

  - eapply closed_upgrade; eauto.
  - eapply closed_upgrade; eauto.
Qed.

Lemma closed_openv: forall j n V T, closed (j+1) n T -> closed j n (TVar V) -> closed j n (open_rec j V T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H; unfold closed; try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto. eapply closed_upgrade. eauto. eauto.

  - Case "TVarB". simpl.
    case_eq (beq_nat j i); intros E. eapply closed_var. auto. eassumption.
    econstructor. eapply beq_nat_false_iff in E. omega.
  - eauto.

  - Case "TSelB". simpl.
    case_eq (beq_nat j i0); intros E. eapply closed_var. eassumption.
    econstructor. eapply beq_nat_false_iff in E. omega.

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
    try solve [inversion IHstp2 as [IH1 IH2]; inversion IH2; split; eauto; apply cl_selh; eapply indexr_max; eassumption];
    try solve [try inversion IHstp2_1; try inversion IHstp2_2; split; eauto; apply cl_varh; eapply indexr_max; eassumption];
    try solve [inversion IHstp2 as [IH1 IH2]; inversion IH2; split; eauto; apply cl_varh; eapply indexr_max; eassumption].
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
    assert (splice (length G0) (open (varF x0) T2)=(open (varF x0) T2)) as A. {
      eapply closed_splice_idem. apply stp_closed2 in H0. inversion H0. subst.
      simpl in H5. inversion H5. subst.
      eapply closed_open. simpl. eassumption. eauto.
      omega.
    }
    rewrite A. eapply stp_selb1; eauto.
    rewrite <- A. apply IHstp2; eauto.
  - Case "selb2".
    assert (splice (length G0) (open (varF x0) T1)=(open (varF x0) T1)) as A. {
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
      assert ((splice (length G0) (TBind (TMem m TBot T2)))=(TBind (TMem m TBot T2))) as A. {
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
      assert (varH x0=varH (x0+0)) as B. {
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
      assert (splice (length G0) (TBind (TMem m TBot T2))=(TBind (TMem m TBot T2))) as B. {
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
      assert ((splice (length G0) (TBind (TMem m T1 TTop)))=(TBind (TMem m T1 TTop))) as A. {
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
      assert (varH x0=varH (x0+0)) as B. {
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
      assert (splice (length G0) (TBind (TMem m T1 TTop))=(TBind (TMem m T1 TTop))) as B. {
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
    specialize IHstp1 with (G3:=G0) (G4:=(0, (open (varH (length G2 + length G0)) T2))::G2).
    rewrite app_length in IHstp1. simpl in IHstp1. unfold open in IHstp1.
    eapply IHstp1. eauto. omega.

    rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x0.
    specialize IHstp2 with (G3:=G0) (G4:=(0, (open (varH (length G2 + length G0)) T1))::G2).
    rewrite app_length in IHstp2. simpl in IHstp2. unfold open in IHstp2.
    eapply IHstp2. eauto. omega. omega.

    Grab Existential Variables.
    apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stp2_splice : forall G1 T1 G2 T2 GH1 GH0 x v1 s m n1,
   stp2 s m G1 T1 G2 T2 (GH1++GH0) n1 ->
   stp2 s m G1 (splice (length GH0) T1) G2 (splice (length GH0) T2) ((map (spliceat (length GH0)) GH1) ++ (x,v1)::GH0) n1.
Proof.
  intros G1 T1 G2 T2 GH1 GH0 x v1 s m n1 H. remember (GH1++GH0) as GH.
  revert GH0 GH1 HeqGH.
  induction H; intros; subst GH; simpl; eauto.
  - Case "strong_var1". admit.
  - Case "var1". admit.
  - Case "vara1". admit.
  - Case "varax". admit.
    
  - Case "strong_sel1".
    eapply stp2_strong_sel1. apply H. eassumption.
    assert (splice (length GH0) TX' = TX') as B. {
      eapply closed_splice_idem. eapply valtp_closed. eassumption. omega.
    }
    rewrite <- B. simpl in IHstp2_1. eapply IHstp2_1. reflexivity.
    eassumption. eassumption.
    assert (splice (length GH0) (open (varF f) TX)=(open (varF f) TX)) as A.  {
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
    eassumption. eassumption.
    assert (splice (length GH0) (open (varF f) TX)=(open (varF f) TX)) as A.  {
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
  - Case "sel2".
    eapply stp2_sel2. apply H. eassumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp2_1.
    reflexivity.
    apply IHstp2_2. reflexivity.
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
      assert ((splice (length GH0) (TBind (TMem l TBot T2)))=(TBind (TMem l TBot T2))) as A. {
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
      assert (varH x0=varH (x0+0)) as B. {
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
      assert (splice (length GH0) (TBind (TMem l TBot T2))=(TBind (TMem l TBot T2))) as B. {
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
      assert ((splice (length GH0) (TBind (TMem l T1 TTop)))=(TBind (TMem l T1 TTop))) as A. {
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
      assert (varH x0=varH (x0+0)) as B. {
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
      assert (splice (length GH0) (TBind (TMem l T1 TTop))=(TBind (TMem l T1 TTop))) as B. {
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
    specialize IHstp2_1 with (GH2:=GH0) (GH3:=(0, (G2,(open (varH (length GH1 + length GH0)) T2)))::GH1).
    rewrite app_length in IHstp2_1. simpl in IHstp2_1. unfold open in IHstp2_1.
    eapply IHstp2_1. eauto. omega.

    rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0).
    specialize IHstp2_2 with (GH2:=GH0) (GH3:=(0, (G1,(open (varH (length GH1 + length GH0)) T1)))::GH1).
    rewrite app_length in IHstp2_2. simpl in IHstp2_2. unfold open in IHstp2_2.
    eapply IHstp2_2. eauto. omega. omega.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0.    
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
  (*
  assert (TSel (varH (S (length GH))) = splice (length GH) (TSel (varH (length GH)))) as AH. {
    simpl. case_eq (le_lt_dec (length GH) (length GH)); intros E LE.
    simpl. rewrite NPeano.Nat.add_1_r. reflexivity.
    clear LE. apply lt_irrefl in E. inversion E.
  }
  *)
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
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite <- HGX1.
  apply stp_splice.
  rewrite A2. simpl. unfold open in H3. rewrite <- H0. apply H3.
  omega.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
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
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. simpl.
  assert (
      stp G1
     ((map (splicett (length GH)) [(0, (open_rec 0 (varH (length GH)) T2))])++(x, v1)::GH)
     (splice (length GH) (open_rec 0 (varH (length GH)) T2))
     (splice (length GH) (open_rec 0 (varH (length GH)) T2))
     ->
     stp G1
     ((0, splice (length GH) (open_rec 0 (varH (length GH)) T2))
      :: (x, v1) :: GH)
     (splice (length GH) (open_rec 0 (varH (length GH)) T2))
     (splice (length GH) (open_rec 0 (varH (length GH)) T2))
    ) as HGX1. {
    simpl. intros A. apply A.
  }
  apply HGX1.
  apply stp_splice.
  simpl. unfold open in H2. rewrite <- H. apply H2.
  simpl. apply le_refl.
  rewrite <- A1. rewrite <- A2.
  unfold open. simpl.
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  assert (
     (stp G1
     ((map (splicett (length GH)) [(0, (open_rec 0 (varH (length GH)) T1))])++(x, v1)::GH)
     (splice (length GH) (open_rec 0 (varH (0 + length GH)) T1))
     (splice (length GH) (open_rec 0 (varH (0 + length GH)) T2)))
     ->
     (stp G1
     ((0, splice (length GH) (open_rec 0 (varH (0 + length GH)) T1))
      :: (x, v1) :: GH)
     (splice (length GH) (open_rec 0 (varH (0 + length GH)) T1))
     (splice (length GH) (open_rec 0 (varH (0 + length GH)) T2)))
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
  - Case "strong_var1". admit.
  - Case "strong_varx". admit.
  - Case "var1". admit.
  - Case "varx". admit.
  - Case "vara1". admit.
  - Case "varax". admit.
    
  - Case "strong_sel1".  
    eapply stp2_strong_sel1. eapply index_extend_mult. apply H.
    assumption. eassumption.
    apply IHstp2_1. assumption. apply venv_ext_refl. assumption.
    eassumption. assumption.
    apply IHstp2_2. assumption. apply venv_ext_refl. assumption.
  - Case "strong_sel2".
    eapply stp2_strong_sel2. eapply index_extend_mult. apply H.
    assumption. eassumption.
    apply IHstp2_1. assumption. apply venv_ext_refl. assumption.
    eassumption. assumption.
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
  - Case "sel2".
    eapply stp2_sel2. eapply index_extend_mult. apply H.
    assumption. eassumption. assumption.
    apply IHstp2_1. assumption. apply venv_ext_refl. assumption.
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
  (*
  assert (TSel (varH (S (length GH))) = splice (length GH) (TSel (varH (length GH)))) as AH. {
    simpl. case_eq (le_lt_dec (length GH) (length GH)); intros E LE.
    simpl. rewrite NPeano.Nat.add_1_r. reflexivity.
    clear LE. apply lt_irrefl in E. inversion E.
  }
  *)
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
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite <- HGX1.
  apply stp2_splice.
  simpl. unfold open in H2. apply H2.
  simpl. omega.
  rewrite <- A2. rewrite <- A4.
  unfold open. simpl.
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
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
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. simpl.
  assert (
   stp2 1 false G2 (splice (length GH) (open_rec 0 (varH (length GH)) T2))
     G2 (splice (length GH) (open_rec 0 (varH (length GH)) T2))
     ((map (spliceat (length GH)) [(0, (G2, open_rec 0 (varH (length GH)) T2))])++((x, v1)::GH))
      n2
   ->
   stp2 1 false G2 (splice (length GH) (open_rec 0 (varH (length GH)) T2))
     G2 (splice (length GH) (open_rec 0 (varH (length GH)) T2))
     ((0, (G2, splice (length GH) (open_rec 0 (varH (length GH)) T2)))
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
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  assert (
   stp2 1 false G1
     (splice (length GH) (open_rec 0 (varH (0 + length GH)) T1)) G2
     (splice (length GH) (open_rec 0 (varH (0 + length GH)) T2))
     ((map (spliceat (length GH)) [(0, (G1, (open_rec 0 (varH (0 + length GH)) T1)))])++((x, v1) :: GH)) n1
      ->
   stp2 1 false G1
     (splice (length GH) (open_rec 0 (varH (0 + length GH)) T1)) G2
     (splice (length GH) (open_rec 0 (varH (0 + length GH)) T2))
     ((0, (G1, splice (length GH) (open_rec 0 (varH (0 + length GH)) T1)))
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
    try solve [repeat ev; split; eexists; eauto 4].
  - Case "all". repeat ev; split; eexists; eauto.
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
  - Case "or21".
    repeat ev; split; eexists.
    eassumption.
    eapply stp2_or1.
    eapply stp2_or21; eauto.
    eapply stp2_or22; eauto.
  - Case "or22".
    repeat ev; split; eexists.
    eassumption.
    eapply stp2_or1.
    eapply stp2_or21; eauto.
    eapply stp2_or22; eauto.
  - Case "or1".
    repeat ev; split; eexists.
    eapply stp2_or1.
    eapply stp2_or21; eauto.
    eapply stp2_or22; eauto.
    eassumption.
  Grab Existential Variables.
  apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
  apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
  apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
  apply 0.
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
      intros x0 GH1 GH0 GH' GX1 TX1 GX2 TX2 EGH EGH' HX. 
    + SCase "top-top". eauto.
    + SCase "bot-bot". eauto.
    + SCase "top". eapply stpd2_top. eapply IHn; try eassumption. omega.
    + SCase "bot". eapply stpd2_bot. eapply IHn; try eassumption. omega.
    + SCase "bool". eauto.
    + SCase "mem". eapply stpd2_mem.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "var1". eapply stpd2_var1; try eassumption.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "varx". eapply stpd2_varx; try eassumption.
    + SCase "vara1".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        rewrite A2' in H1. inversion H1. subst.
        inversion HX as [nx HX'].
        eapply stpd2_vara1.
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
        eapply stpd2_vara1. eapply A. assumption.
        eapply IHn; try eassumption. omega.
        eapply IHn; try eassumption. omega.
    + SCase "varax".
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(x0, (GX2, TX2))]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        rewrite A2' in H1. inversion H1. subst.
        inversion HX as [nx HX'].
        eapply stpd2_varax.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_varax. eapply A.
    + SCase "sel1". eapply stpd2_sel1; try eassumption.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "sel2". eapply stpd2_sel2; try eassumption.
      eapply IHn; try eassumption. omega.
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
          stpd2 false G2 (open (varH (length GH)) T3) G2
                (open (varH (length GH)) T3)
                ((0, (G2, open (varH (length GH)) T3)) :: GH')
                ->
          stpd2 false G2 (open (varH (length GH')) T3) G2
                (open (varH (length GH')) T3)
                ((0, (G2, open (varH (length GH')) T3)) :: GH')) as CS1. {
        rewrite A. intros P. apply P.
      }
      apply CS1. eapply IHn. eassumption. omega.
      instantiate (5:=(0, (G2, open (varH (length GH)) T3)) :: GH1).
      subst. simpl. reflexivity. subst. simpl. reflexivity.
      assumption.
      assert (
          stpd2 false G1 (open (varH (length GH)) T0) G2
                (open (varH (length GH)) T3)
                ((0, (G1, open (varH (length GH)) T0)) :: GH')
                ->
          stpd2 false G1 (open (varH (length GH')) T0) G2
                (open (varH (length GH')) T3)
                ((0, (G1, open (varH (length GH')) T0)) :: GH')
        ) as CS2. {
        rewrite A. intros P. apply P.
      }
      apply CS2. eapply IHn. eassumption. omega.
      instantiate (5:=(0, (G1, open (varH (length GH)) T0)) :: GH1).
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
    + SCase "or21".
      eapply stpd2_or21.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "or22".
      eapply stpd2_or22.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "or1".
      eapply stpd2_or1.
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

Lemma stpd2_narrow: forall x G1 G2 G3 G4 GH T1 T2 T3 T4,
  stpd2 false G1 T1 G2 T2 GH -> (* careful about H! *)
  stpd2 false G3 T3 G4 T4 ((x,(G2,T2))::GH) ->
  stpd2 false G3 T3 G4 T4 ((x,(G1,T1))::GH).
Proof.
  intros. inversion H0 as [n H'].
  eapply (stp2_narrow_aux n) with (GH1:=[]). eapply H'. omega.
  simpl. reflexivity. simpl. reflexivity.
  eapply stpd2_extendH. assumption.
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
      assert (sstpd2 false GX' TX' G1 (TMem l TTop TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eapply stp2_topx.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
  - Case "botx". subst. inversion H1.
    + SCase "botx". eexists. eauto.
    + SCase "top". eexists. eauto.
    + SCase "?". eexists. eauto.
    + SCase "sel2".
      assert (sstpd2 false GX' TX' G1 (TMem l TBot TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf; eapply stp2_botx.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
  - Case "top". subst. inversion H1.
    + SCase "topx". eexists. eauto.
    + SCase "top". eexists. eauto.
    + SCase "sel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem l T1 TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eapply stp2_top. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
  - Case "bot". subst.
    apply stp2_reg2 in H1. inversion H1 as [n1' H1'].
    exists (S n1'). apply stp2_bot. apply H1'.
  - Case "bool". subst. inversion H1.
    + SCase "top". eexists. eauto.
    + SCase "bool". eexists. eauto.
    + SCase "sel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem l TBool TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eapply stp2_bool.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
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
      assert (sstpd2 false GX' TX' G1 (TMem l0 (TMem l T0 T4) TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
  - Case "svar1". subst.
    assert (sstpd2 true GX TX G3 T3 []). {
      eapply IHn. eassumption. omega.
      eexists. eapply H1. 
    }
    repeat eu.
    eexists. eapply stp2_strong_var1; eauto.
  - Case "svarx". subst. inversion H1.
    + SCase "top". subst.
      apply stp2_reg1 in H. inversion H.
      eexists. eapply stp2_top. eassumption.
    + SCase "svar1".
      subst. rewrite H5 in H3. inversion H3. subst.
      eexists. eapply stp2_strong_var1; eauto.
    + SCase "sselx".
      subst. rewrite H5 in H3. inversion H3. subst.
      eexists. eapply stp2_strong_varx. eauto. eauto.
    + SCase "ssel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem l (TVar (varF x1)) TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
  - Case "ssel1". subst.
    assert (sstpd2 true ((f, vobj GX f ds) :: GX) (open (varF f) TX) G3 T3 []). eapply IHn. eauto. omega. eexists. eapply H1.
    assert (sstpd2 false GX' TX' G3 (TMem l TBot T3) []). {
      eapply sstpd2_wrapf. eapply IHn. eassumption. omega.
      eexists. eapply stp2_mem.
      eapply stp2_wrapf. eapply stp2_botx.
      eapply H1.
    }
    repeat eu.
    eexists. eapply stp2_strong_sel1; eauto.
  - Case "ssel2". subst. inversion H1.
    + SCase "top". subst.
      apply stp2_reg1 in H7. inversion H7.
      eexists. eapply stp2_top. eassumption.
    + SCase "ssel1".  (* interesting one *)
      subst. rewrite H10 in H2. inversion H2.
      subst. rewrite H13 in H5. inversion H5.
      subst.
      eapply IHn. eapply H7. omega. eexists. eauto.
    + SCase "ssel2". subst.
      assert (sstpd2 false GX'0 TX'0 G1 (TMem l0 T1 TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "sselx".
      subst. rewrite H2 in H10. inversion H10. subst.
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
  - Case "sselx". subst. inversion H1.
    + SCase "top". subst.
      apply stp2_reg1 in H. inversion H.
      eexists. eapply stp2_top. eassumption.
    + SCase "ssel1".
      subst. rewrite H6 in H3. inversion H3. subst.
      eexists. eapply stp2_strong_sel1; eauto.
    + SCase "ssel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem l0 (TSel (varF x1) l) TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "sselx".
      subst. rewrite H6 in H3. inversion H3. subst.
      eexists. eapply stp2_strong_selx. eauto. eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
  - Case "all". subst. inversion H1.
    + SCase "top".
      apply stp2_reg1 in H. inversion H.
      eexists. eapply stp2_top. eassumption.
    + SCase "ssel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem l0 (TAll l T0 T4) TTop) []) as A. {
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
      assert (stpd2 false G1 (open (varH (length ([]:aenv))) T4)
                          G3 (open (varH (length ([]:aenv))) T8)
                          [(0, (G3, T7))]).
        eapply stpd2_trans. eapply stpd2_narrow. eexists. eapply H10. eauto. eauto.
        repeat eu. eexists. eapply stp2_all. eauto. eauto. eauto. eauto. eapply H8.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
  - Case "bind". subst. inversion H1; subst.
    + SCase "top".
      apply stp2_reg1 in H. inversion H.
      eexists. eapply stp2_top. eassumption.
    + SCase "ssel2". subst.
      assert (sstpd2 false GX' TX' G1 (TMem l (TBind T0) TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "bind".
      subst.
      assert (stpd2 false G1 (open (varH 0) T0) G3 (open (varH 0) T2)
                    [(0, (G1, open (varH 0) T0))]) as A. {
        simpl in H5. simpl in H9.
        eapply stpd2_trans.
        eexists; eauto.
        change ([(0, (G1, open (varH 0) T0))]) with ((0, (G1, open (varH 0) T0))::[]).
        eapply stpd2_narrow. eexists. eassumption. eexists. eassumption.
      }
      inversion A.
      eexists. eapply stp2_bind; try eassumption.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
  - Case "and11". subst.
    eapply IHn in H2. destruct H2 as [? H2].
    eexists. eapply stp2_and11.
    eassumption. eassumption. omega. eexists. eassumption.
  - Case "and12". subst.
    eapply IHn in H2. destruct H2 as [? H2].
    eexists. eapply stp2_and12.
    eassumption. eassumption. omega. eexists. eassumption.
  - Case "and2". subst. inversion H1; subst.
    + SCase "top". eapply stp2_reg1 in H. inversion H. eexists. eapply stp2_top; eassumption.
    + SCase "sel2".
      assert (sstpd2 false GX' TX' G1 (TMem l T1 TTop) []) as A. {
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
    + SCase "or21". subst. eexists. eapply stp2_or21; eauto.
    + SCase "or22". subst. eexists. eapply stp2_or22; eauto.
  - Case "or21". subst. inversion H1; subst.
    + SCase "top". eapply stp2_reg1 in H. inversion H. eexists. eapply stp2_top; eassumption.
    + SCase "sel2".
      assert (sstpd2 false GX' TX' G1 (TMem l T1 TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst.
      assert (sstpd2 false G1 T1 G3 T2 []) as A. {
        eapply sstpd2_trans_axiom.
        eexists. eapply stp2_wrapf. eapply H.
        eexists. eassumption.
      }
      destruct A as [? A].
      eexists. eapply stp2_or21. eapply A. eassumption.
    + SCase "or22". subst.
      assert (sstpd2 false G1 T1 G3 T5 []) as A. {
        eapply sstpd2_trans_axiom.
        eexists. eapply stp2_wrapf. eapply H.
        eexists. eassumption.
      }
      destruct A as [? A].
      eexists. eapply stp2_or22. eapply A. eassumption.
    + SCase "or1". subst. eapply IHn. apply H2. omega. eexists. eassumption.
  - Case "or22". subst. inversion H1; subst.
    + SCase "top". eapply stp2_reg1 in H. inversion H. eexists. eapply stp2_top; eassumption.
    + SCase "sel2".
      assert (sstpd2 false GX' TX' G1 (TMem l T1 TTop) []) as A. {
        eapply sstpd2_trans_axiom. eexists. eassumption.
        eexists. eapply stp2_wrapf. eapply stp2_mem.
        eapply stp2_wrapf. eassumption.
        eapply stp2_topx.
      }
      destruct A as [? A].
      eexists. eapply stp2_strong_sel2; eauto.
    + SCase "and2". subst. eexists. eapply stp2_and2; eauto.
    + SCase "or21". subst.
      assert (sstpd2 false G1 T1 G3 T2 []) as A. {
        eapply sstpd2_trans_axiom.
        eexists. eapply stp2_wrapf. eapply H.
        eexists. eassumption.
      }
      destruct A as [? A].
      eexists. eapply stp2_or21. eapply A. eassumption.
    + SCase "or22". subst.
      assert (sstpd2 false G1 T1 G3 T5 []) as A. {
        eapply sstpd2_trans_axiom.
        eexists. eapply stp2_wrapf. eapply H.
        eexists. eassumption.
      }
      destruct A as [? A].
      eexists. eapply stp2_or22. eapply A. eassumption.
    + SCase "or1". subst. eapply IHn. apply H2. omega. eexists. eassumption.
  - Case "or1". subst.
    eapply IHn in H2. destruct H2 as [? H2].
    eapply IHn in H3. destruct H3 as [? H3].
    eexists. eapply stp2_or1.
    eassumption. eassumption. omega. eexists. eassumption. omega. eexists. eassumption.
  - Case "wrapf". subst. eapply IHn. eapply H2. omega. eexists. eauto.
  - Case "transf". subst. eapply IHn. eapply H2. omega. eapply IHn. eapply H3. omega. eexists. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0.
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

Lemma dcs_has_type_shape: forall G f ds T,
  dcs_has_type G f ds T ->
  T = TTop \/
  ((exists l T1 T2, T = TAll l T1 T2) \/ (exists l T1, T = TMem l T1 T1)) \/
  (exists TA ds' T', T = TAnd TA T' /\
   dcs_has_type G f ds' T' /\
   ((exists l T1 T2, TA = TAll l T1 T2) \/ (exists l T1, TA = TMem l T1 T1))).
Proof.
  intros. induction H.
  - left. reflexivity.
  - destruct IHdcs_has_type; subst.
    + right. left. left. eexists. eexists. eexists.
      simpl. reflexivity.
    + right. destruct H4; repeat ev.
      * right. destruct H1; repeat ev.
        eexists. eexists. eexists.
        split. rewrite H1. simpl. reflexivity.
        split. eassumption.
        left. eexists. eexists. eexists. reflexivity.
        eexists. eexists. eexists.
        split. rewrite H1. simpl. reflexivity.
        split. eassumption.
        left. eexists. eexists. eexists. reflexivity.
      * right. destruct H3; repeat ev.
        eexists. eexists. eexists.
        split. rewrite H1. simpl. reflexivity.
        split. eassumption.
        left. eexists. eexists. eexists. reflexivity.
        eexists. eexists. eexists.
        split. rewrite H1. simpl. reflexivity.
        split. eassumption.
        left. eexists. eexists. eexists. reflexivity.
  - destruct IHdcs_has_type; subst.
    + right. left. right. eexists. eexists.
      simpl. reflexivity.
    + right. destruct H2; repeat ev.
      * right. destruct H0; repeat ev.
        eexists. eexists. eexists.
        split. rewrite H0. simpl. reflexivity.
        split. eassumption.
        right. eexists. eexists. reflexivity.
        eexists. eexists. eexists.
        split. rewrite H0. simpl. reflexivity.
        split. eassumption.
        right. eexists. eexists. reflexivity.
      * right. destruct H2; repeat ev.
        eexists. eexists. eexists.
        split. rewrite H0. simpl. reflexivity.
        split. eassumption.
        right. eexists. eexists. reflexivity.
        eexists. eexists. eexists.
        split. rewrite H0. simpl. reflexivity.
        split. eassumption.
        right. eexists. eexists. reflexivity.
Qed.

Lemma dcs_tbind_aux: forall n, forall G f ds venv1 T x venv0 T0 n0,
  n0 <= n ->
  dcs_has_type G f ds T ->
  stp2 0 true venv1 (open (varF x) T) venv0 (TBind T0) [] n0 ->
  False.
Proof.
  intros n. induction n.
  intros. inversion H1; omega.
  intros. eapply dcs_has_type_shape in H0.
  destruct H0. subst. inversion H1.
  destruct H0.
  destruct H0.
    repeat ev. subst. inversion H1.
    repeat ev. subst. inversion H1.
  destruct H0 as [TA [ds' [T' [A1 [A2 A3]]]]].
  destruct A3; repeat ev; subst.
  inversion H1. subst. inversion H4. subst. eapply IHn in A2. inversion A2.
  instantiate (1:=n1). omega. eassumption.
  inversion H1. subst. inversion H4. subst. eapply IHn in A2. inversion A2.
  instantiate (1:=n1). omega. eassumption.
Qed.

Lemma dcs_tbind: forall G f ds venv1 T x venv0 T0 n0,
  dcs_has_type G f ds T ->
  stp2 0 true venv1 (open (varF x) T) venv0 (TBind T0) [] n0 ->
  False.
Proof.
  intros. eapply dcs_tbind_aux. instantiate (1:=n0). eauto. eassumption. eassumption.
Qed.

Lemma dcs_mem_has_type_stp: forall G G1 G2 f ds T x T1 T2,
  dcs_has_type G f ds T ->
  sstpd2 true G1 (open (varF x) T) G2 (TMem (length ds) T1 T2) [] ->
  False.
Proof.
  intros. remember (length ds) as l. assert (l >= length ds) as A by omega. clear Heql.
  induction H. simpl in H0. destruct H0 as [? H0]. inversion H0.
  destruct (tand_shape (TAll m T0 T3) TS).
  rewrite H5 in H4. rewrite H4 in H0. simpl in H0. destruct H0 as [? H0]. inversion H0.
  subst. inversion H9.
  subst. eapply IHdcs_has_type. eexists. eapply H9. simpl in A. omega.
  rewrite H5 in H4. rewrite H4 in H0. destruct H0 as [? H0]. inversion H0.
  destruct (tand_shape (TMem m T0 T0) TS).
  rewrite H3 in H2. rewrite H2 in H0. simpl in H0. destruct H0 as [? H0]. inversion H0.
  subst. inversion H7. subst. simpl in A. omega.
  apply IHdcs_has_type. eexists. eassumption. simpl in A. omega.
  rewrite H3 in H2. rewrite H2 in H0. simpl in H0. destruct H0 as [? H0]. inversion H0.
  simpl in A. omega.
Qed.

Lemma invert_typ: forall venv vx l T1 T2 n,
  val_type venv vx (TMem l T1 T2) n ->
  exists GX ds TX,
    vx = (vobj GX (fresh GX) ds) /\
    index l ds = Some (dmem TX) /\
    sstpd2 false venv T1 (((fresh GX),vobj GX (fresh GX) ds)::GX) (open (varF (fresh GX)) TX) [] /\
    sstpd2 true (((fresh GX),vobj GX (fresh GX) ds)::GX) (open (varF (fresh GX)) TX) venv T2 [].
Proof.
  intros. inversion H; ev; try solve by inversion.
  subst.
  exists venv1. exists ds.
  assert (exists TX, index l ds = Some (dmem TX) /\ sstpd2 true ((fresh venv1, vobj venv1 (fresh venv1) ds) :: venv1) (TMem l (open (varF (fresh venv1)) TX) (open (varF (fresh venv1)) TX)) venv0 (TMem l T1 T2) []) as A. {
    clear H. clear H0.
    unfold id in H4.
    remember (((fresh venv1, vobj venv1 (fresh venv1) ds) :: venv1)) as venv.
    assert (sstpd2 true venv (open (varF (fresh venv1)) T) venv0 (TMem l T1 T2) []) as B. {
      eexists. eassumption.
    }
    clear Heqvenv.
    unfold id in H2.
    remember ((fresh venv1, open (varF (fresh venv1)) T) :: tenv0) as tenv.
    clear Heqtenv. clear H4.
    induction H2. destruct B as [? B]. inversion B.
    simpl.
    case_eq (le_lt_dec (fresh dcs) m); intros LE E1.
    case_eq (beq_nat l m); intros E2.
    destruct (tand_shape (TAll m T0 T3) TS).
    rewrite H4 in H3. rewrite H3 in B. destruct B as [? B]. inversion B. inversion H8.
    eapply dcs_mem_has_type_stp in H2. inversion H2. rewrite <- H1. eapply beq_nat_true in E2. rewrite <- E2. eexists. eassumption.
    rewrite H4 in H3. rewrite H3 in B. destruct B as [? B]. inversion B.
    eapply IHdcs_has_type.  destruct (tand_shape (TAll m T0 T3) TS).
    rewrite H4 in H3. rewrite H3 in B. destruct B as [? B]. inversion B. inversion H8. eexists. eassumption.
    rewrite H4 in H3. rewrite H3 in B. destruct B as [? B]. inversion B.
    inversion H2; subst. simpl in LE. omega. simpl in LE. omega. simpl in LE. omega.
    simpl.
    case_eq (le_lt_dec (fresh dcs) m); intros LE E1.
    case_eq (beq_nat l m); intros E2.
    exists T0.
    split. reflexivity.
    destruct (tand_shape (TMem m T0 T0) TS).
    rewrite H1 in H0. rewrite H0 in B. destruct B as [? B]. inversion B. eapply beq_nat_true in E2. rewrite E2. rewrite E2 in H6. eexists. eassumption.
    eapply dcs_mem_has_type_stp in H2. inversion H2. rewrite <- H. eapply beq_nat_true in E2. rewrite <- E2. eexists. unfold open. eassumption.
    rewrite H1 in H0. rewrite H0 in B. eapply beq_nat_true in E2. rewrite <- E2 in B. apply B.
    eapply IHdcs_has_type. destruct (tand_shape (TMem m T0 T0) TS).
    rewrite H1 in H0. rewrite H0 in B. destruct B as [? B]. inversion B. inversion H6. apply beq_nat_false in E2. omega. eexists. eassumption.
    rewrite H1 in H0. rewrite H0 in B. destruct B as [? B]. inversion B. apply beq_nat_false in E2. omega.
    inversion H2; subst. simpl in LE. omega. simpl in LE. omega. simpl in LE. omega.
  }
  destruct A as [TX [A1 A2]].
  exists TX.
  split. reflexivity.
  split. apply A1.
  split.
  destruct A2 as [? A2]. inversion A2. subst. eexists. eassumption.
  destruct A2 as [? A2]. inversion A2. subst. eexists. eassumption.
Qed.

Lemma inv_closed_open: forall j n V l T, closed j n (open_rec j V T) -> closed j n (TSel V l) -> closed (j+1) n T.
Proof.
  intros. generalize dependent j. induction T; try solve [
  intros; inversion H; subst; unfold closed; try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto].

  - Case "TSelB". intros. simpl.
    unfold open_rec in H.
    destruct v.
    eapply closed_upgrade. eauto. omega.
    eapply closed_upgrade. eauto. omega.

    case_eq (beq_nat j i0); intros E.

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


Lemma open_subst_commute: forall T2 V l (n:nat) x j,
closed j n (TSel V l) ->
(open_rec j (varH x) (subst V T2)) =
(subst V (open_rec j (varH (x+1)) T2)).
Proof.
  intros T2 V l n. induction T2; intros; eauto.
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
  -  simpl.
     destruct v; simpl; try reflexivity.
     + simpl. case_eq (beq_nat i0 0); intros E.
       destruct V; try reflexivity.
       inversion H. subst.
       assert (beq_nat j i1 = false) as A. apply false_beq_nat. omega.
       rewrite A. reflexivity.
       reflexivity.
     + simpl. case_eq (beq_nat j i0); intros E.
       assert (x+1<>0). omega. eapply beq_nat_false_iff in H0.
       assert (x=x+1-1) as A. unfold id. omega.
       rewrite <- A.  rewrite H0. reflexivity.
       reflexivity.
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eapply closed_upgrade. eauto. eauto. eauto.
  -  simpl. rewrite IHT2. eauto. eapply closed_upgrade. eauto. eauto.
  - simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
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
  subst. omega.
  subst. eapply closed_upgrade. eassumption. omega.
  subst. eapply closed_upgrade. eassumption. omega.
Qed.

Lemma closed_subst: forall j n V l T, closed j (n+1) T -> closed 0 n (TSel V l) -> closed j (n) (subst V T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H; unfold closed; try econstructor; try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - Case "TSelH". simpl.
    case_eq (beq_nat x 0); intros E. eapply closed_upgrade. eapply closed_upgrade_free. eapply closed_sel. eauto. omega. eauto. omega.
    econstructor. assert (x > 0). eapply beq_nat_false_iff in E. omega. omega.
Qed.


Lemma subst_open_commute_m: forall j n m V l T2, closed (j+1) (n+1) T2 -> closed 0 m (TSel V l) ->
    subst V (open_rec j (varH (n+1)) T2) = open_rec j (varH n) (subst V T2).
Proof.
  intros. generalize dependent j. generalize dependent n.
  induction T2; intros; inversion H; simpl; eauto;
          try rewrite IHT2_1; try rewrite IHT2_2; try rewrite IHT2; eauto.

  simpl. case_eq (beq_nat x 0); intros E.
  destruct V; try solve [simpl; reflexivity].
  unfold closed in H0. inversion H0. subst.
  case_eq (beq_nat  j i0); intros E2.
  apply beq_nat_true in E2. subst. omega.
  reflexivity. reflexivity.
  simpl. case_eq (beq_nat j i0); intros E.
  simpl. case_eq (beq_nat (n+1) 0); intros E2. eapply beq_nat_true_iff in E2. omega.
  assert (n+1-1 = n) as A. omega. rewrite A. eauto.
  eauto.
Qed.

Lemma subst_open_commute: forall j n V l T2, closed (j+1) (n+1) T2 -> closed 0 0 (TSel V l) ->
    subst V (open_rec j (varH (n+1)) T2) = open_rec j (varH n) (subst V T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_zero: forall j k TX T2, closed k 0 T2 ->
    subst TX (open_rec j (varH 0) T2) = open_rec j TX T2.
Proof.
  intros. generalize dependent k. generalize dependent j. induction T2; intros; inversion H; simpl; eauto; try rewrite (IHT2_1 _ k); try rewrite (IHT2_2 _ (S k)); try rewrite (IHT2_2 _ (S k)); try rewrite (IHT2 _ (S k)); try rewrite (IHT2 _ k); eauto.

  eapply closed_upgrade; eauto.

  case_eq (beq_nat x 0); intros E. omega. omega.

  case_eq (beq_nat j i0); intros E. eauto. eauto.

  eapply closed_upgrade; eauto.

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

Lemma nosubst_open: forall j V l T2, nosubst (TSel V l) -> nosubst T2 -> nosubst (open_rec j V T2).
Proof.
  intros. generalize dependent j. induction T2; intros; try inversion H0; simpl; eauto.

  destruct v; eauto.
  case_eq (beq_nat j i0); intros E. eauto. eauto.
Qed.

Lemma nosubst_open_rev: forall j V l T2, nosubst (open_rec j V T2) -> nosubst (TSel V l) -> nosubst T2.
Proof.
  intros. generalize dependent j. induction T2; intros; try inversion H; simpl in H; simpl; eauto.
  destruct v; eauto.
Qed.

Lemma nosubst_zero_closed: forall j T2, nosubst (open_rec j (varH 0) T2) -> closed_rec (j+1) 0 T2 -> closed_rec j 0 T2.
Proof.
  intros. generalize dependent j. induction T2; intros; simpl in H; try destruct H; inversion H0; eauto.

  destruct v. inversion H1. inversion H1. inversion H1. subst.
  case_eq (beq_nat j i1); intros E. rewrite E in H. destruct H. eauto.
  eapply beq_nat_false_iff in E.
  constructor. omega.
Qed.



(* ---- two-env substitution. first define what 'compatible' types mean. ---- *)

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


Definition compat (GX:venv) (TX: ty) (TX': var) (V: option vl) (G1:venv) (T1:ty) (T1':ty) :=
  (exists x1 v nv, index x1 G1 = Some v /\ V = Some v /\ GX = GX /\ val_type GX v (subst TX' TX) nv /\ T1' = (subst (varF x1) T1)) \/
  (closed_rec 0 0 T1 /\ T1' = T1) \/ (* this one is for convenience: redundant with next *)
  (nosubst T1 /\ T1' = subst (varF 0) T1).


Definition compat2 (GX:venv) (TX: ty) (TX': var) (V: option vl) (p1:id*(venv*ty)) (p2:id*(venv*ty)) :=
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
  Grab Existential Variables.
  apply 0. apply 0.
Qed.

Lemma closed_compat': forall GX TX TX' l V GXX TXX TXX' j k,
  compat GX TX TX' V GXX TXX TXX' ->
  closed 0 k (TSel TX' l) ->
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
  Grab Existential Variables.
  apply 0. apply 0.
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

Lemma compat_mem: forall GX TX TX' V G1 l T1 T2 T1',
    compat GX TX TX' V G1 (TMem l T1 T2) T1' ->
    closed 0 1 TX ->
    exists TA TB, T1' = TMem l TA TB /\
                  compat GX TX TX' V G1 T1 TA /\
                  compat GX TX TX' V G1 T2 TB.
Proof.
  intros ? ? ? ? ? ? ? ? ? CC CLX. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. + left. repeat eexists; eauto.
  - ev. repeat eexists; eauto. + right. left. inversion H. eauto. + right. left. inversion H. eauto.
  - ev. repeat eexists; eauto. + right. right. inversion H. eauto. + right. right. inversion H. eauto.
Qed.


Lemma compat_mem_fwd2: forall GX TX TX' V G1 l T2 T2',
    compat GX TX TX' V G1 T2 T2' ->
    compat GX TX TX' V G1 (TMem l TBot T2) (TMem l TBot T2').
Proof.
  intros. repeat destruct H as [|H].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. rewrite H3. eauto.
  - ev. repeat eexists; eauto. + right. left. subst. eauto.
  - ev. repeat eexists; eauto. + right. right. subst. simpl. eauto.
Qed.

Lemma compat_mem_fwd1: forall GX TX TX' V G1 l T2 T2',
    compat GX TX TX' V G1 T2 T2' ->
    compat GX TX TX' V G1 (TMem l T2 TTop) (TMem l T2' TTop).
Proof.
  intros. repeat destruct H as [|H].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. rewrite H3. eauto.
  - ev. repeat eexists; eauto. + right. left. subst. eauto.
  - ev. repeat eexists; eauto. + right. right. subst. simpl. eauto.
Qed.

Lemma compat_mem_fwdx: forall GX TX TX' V G1 l T2 T2',
    compat GX TX TX' V G1 T2 T2' ->
    compat GX TX TX' V G1 (TMem l T2 T2) (TMem l T2' T2').
Proof.
  intros. repeat destruct H as [|H].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. rewrite H3. eauto.
  - ev. repeat eexists; eauto. + right. left. subst. eauto.
  - ev. repeat eexists; eauto. + right. right. subst. simpl. eauto.
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

Lemma compat_or: forall GX TX TX' V G1 T1 T2 T1',
    compat GX TX TX' V G1 (TOr T1 T2) T1' ->
    closed_rec 0 1 TX ->
    exists TA TB, T1' = TOr TA TB /\
                  compat GX TX TX' V G1 T1 TA /\
                  compat GX TX TX' V G1 T2 TB.
Proof.
  intros ? ? ? ? ? ? ? ? CC CLX. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. + left. repeat eexists; eauto.
  - ev. repeat eexists; eauto. + right. left. inversion H. eauto. + right. left. inversion H. eauto.
  - ev. repeat eexists; eauto. + right. right. inversion H. eauto. + right. right. inversion H. eauto.
Qed.

Lemma compat_sel: forall GX TX TX' V G1 T1' (GXX:venv) (TXX:ty) x l v n,
    compat GX TX TX' V G1 (TSel (varF x) l) T1' ->
    closed 0 1 TX ->
    closed 0 0 TXX ->
    index x G1 = Some v ->
    val_type GXX v TXX n ->
    exists TXX', T1' = (TSel (varF x) l) /\ TXX' = TXX /\ compat GX TX TX' V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? CC CL CL1 IX. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto. + right. left. simpl in H0. eauto.
  - ev. repeat eexists; eauto. + right. left. simpl in H0. eauto.
  - ev. repeat eexists; eauto. + right. left. simpl in H0. eauto.
Qed.

Lemma compat_selb: forall GX TX TX' V G1 T1' (GXX:venv) (TXX:ty) x T0 v n,
    compat GX TX TX' V G1 (open (varF x) T0) T1' ->
    closed 0 1 TX ->
    closed 0 0 TXX ->
    closed 1 0 T0 ->
    (* index x G1 = Some v -> *)
    val_type GXX v TXX n ->
    exists TXX', T1' = (open (varF x) T0) /\ TXX' = TXX /\ compat GX TX TX' V GXX TXX TXX'
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
  Grab Existential Variables.
  apply 0. apply 0.
Qed.


Lemma compat_selh: forall GX TX TX' V G1 T1' GH0 GH0' (GXX:venv) (TXX:ty) x l,
    compat GX TX TX' V G1 (TSel (varH x) l) T1' ->
    closed 0 1 TX ->
    indexr x (GH0 ++ [(0, (GX, TX))]) = Some (GXX, TXX) ->
    Forall2 (compat2 GX TX TX' V) GH0 GH0' ->
    (x = 0 /\ GXX = GX /\ TXX = TX) \/
    exists TXX',
      x > 0 /\ T1' = TSel (varH (x-1)) l /\
      indexr (x-1) GH0' = Some (GXX, TXX') /\
      compat GX TX TX' V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? CC CL IX FA.
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


Lemma compat_all: forall GX TX TX' V G1 m T1 T2 T1' n,
    compat GX TX TX' V G1 (TAll m T1 T2) T1' ->
    closed 0 1 TX ->
    closed 1 (n+1) T2 ->
    exists TA TB, T1' = TAll m TA TB /\
                  closed 1 n TB /\
                  compat GX TX TX' V G1 T1 TA /\
                  compat GX TX TX' V G1 (open_rec 0 (varH (n+1)) T2) (open_rec 0 (varH n) TB).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? CC CLX CL2. repeat destruct CC as [|CC].

  - ev. simpl in H0. repeat eexists; eauto. eapply closed_subst; eauto.
    + unfold compat. left. repeat eexists; eauto.
    + unfold compat. left. repeat eexists; eauto. erewrite subst_open_commute; eauto.

  - ev. simpl in H0. inversion H. repeat eexists; eauto. eapply closed_upgrade_free; eauto. omega.
    + unfold compat. right. right. split. eapply nosubst_intro; eauto. symmetry. eapply closed_no_subst; eauto.
    + unfold compat. right. right. split.
      * eapply nosubst_open. simpl. omega. eapply nosubst_intro. eauto.
      * erewrite subst_open_commute.  assert (T2 = subst (varF 0) T2) as E. symmetry. eapply closed_no_subst; eauto. rewrite <-E. eauto. eauto. eauto.

  - ev. simpl in H0. destruct H. repeat eexists; eauto. eapply closed_subst; eauto. eauto.
    + unfold compat. right. right. eauto.
    + unfold compat. right. right. split.
      * eapply nosubst_open. simpl. omega. eauto.
      * erewrite subst_open_commute; eauto.
  Grab Existential Variables.
  apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


Lemma compat_bind: forall GX TX TX' V G1 T2 T1' n,
    compat GX TX TX' V G1 (TBind T2) T1' ->
    closed 0 1 TX ->
    closed 1 (n+1) T2 ->
    exists TB, T1' = TBind TB /\
                  closed 1 n TB /\
                  compat GX TX TX' V G1 (open_rec 0 (varH (n+1)) T2) (open_rec 0 (varH n) TB).
Proof.
  intros ? ? ? ? ? ? ? ? CC CLX CL2. repeat destruct CC as [|CC].

  - ev. simpl in H0. repeat eexists; eauto. eapply closed_subst; eauto.
    + unfold compat. left. repeat eexists; eauto. erewrite subst_open_commute; eauto.

  - ev. simpl in H0. inversion H. repeat eexists; eauto. eapply closed_upgrade_free; eauto. omega.
    + unfold compat. right. right. split.
      * eapply nosubst_open. simpl. omega. eapply nosubst_intro. eauto.
      * erewrite subst_open_commute.  assert (T2 = subst (varF 0) T2) as E. symmetry. eapply closed_no_subst; eauto. rewrite <-E. eauto. eauto. eauto.

  - ev. simpl in H0. simpl in H. repeat eexists; eauto. eapply closed_subst; eauto. eauto.
    + unfold compat. right. right. split.
      * eapply nosubst_open. simpl. omega. eauto.
      * erewrite subst_open_commute; eauto.
  Grab Existential Variables.
  apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


Lemma subst_open1_aux: forall j x T,
closed (j+1) 0 T ->
(subst (varF x) (open_rec j (varH 0) T)) = (open_rec j (varF x) T).
Proof.
  intros. generalize dependent j. induction T; intros; eauto.
  - simpl.
    rewrite <- IHT1.
    rewrite <- IHT2.
    reflexivity.
    inversion H. eauto.
    inversion H. eauto.
  - destruct v.
  + simpl. reflexivity.
  + simpl. inversion H. subst. omega.
  + simpl.
    case_eq (beq_nat j i0); intros E.
    * simpl. reflexivity.
    * reflexivity.
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
  - simpl.
    rewrite <- IHT1.
    rewrite <- IHT2.
    reflexivity.
    inversion H. eauto.
    inversion H. eauto.
Qed.

Lemma subst_open1: forall x T,
closed 1 0 T ->
(subst (varF x) (open (varH 0) T)) = (open (varF x) T).
Proof.
  intros. eapply subst_open1_aux. simpl. eassumption.
Qed.

Lemma closed_open_tselh: forall j x T,
                                closed j 0 (open_rec j (varH x) T) ->
                                closed j 0 T.
Proof.
  intros. generalize dependent j. induction T; intros; eauto.
  - simpl in H. inversion H. subst.
    apply cl_mem. apply IHT1. eassumption. apply IHT2. eassumption.
  - destruct v.
  + simpl. eauto.
  + simpl in H. assumption.
  + simpl in H.
    case_eq (beq_nat j i0); intros E.
    * rewrite E in H. inversion H. subst. omega.
    * rewrite E in H. assumption.
  - simpl in H. inversion H. subst.
    apply cl_all. apply IHT1. eassumption. apply IHT2. eassumption.
  - simpl in H. inversion H. subst.
    apply cl_bind. apply IHT. eassumption.
  - simpl in H. inversion H. subst.
    apply cl_and. apply IHT1. eassumption. apply IHT2. eassumption.
  - simpl in H. inversion H. subst.
    apply cl_or. apply IHT1. eassumption. apply IHT2. eassumption.
Qed.

Lemma open_noop : forall i j T1 T0,
                    closed i j T0 ->
                    open_rec i T1 T0 = T0.
Proof.
  intros. induction H; eauto.
  - simpl. rewrite IHclosed_rec1. rewrite IHclosed_rec2. reflexivity.
  - simpl. rewrite IHclosed_rec1. rewrite IHclosed_rec2. reflexivity.
  - simpl. rewrite IHclosed_rec. reflexivity.
  - simpl. rewrite IHclosed_rec1. rewrite IHclosed_rec2. reflexivity.
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
  - Case "mem".
    eapply IHn in H2. eapply sstpd2_untrans in H2. eu.
    eapply IHn in H3. eapply sstpd2_untrans in H3. eu.
    eexists. eapply stp2_mem. eauto. eauto. omega. omega.
  - Case "sel1".
    remember H3 as Hv. clear HeqHv.
    eapply IHn in H5. eapply sstpd2_untrans in H5. eapply valtp_widen with (2:=H5) in H3.
    eapply invert_typ in H3. ev. repeat eu. subst.
    assert (closed (0+1) (length ([]:aenv)) x2). eapply inv_closed_open. eapply stp2_closed2; eauto. eauto.
    eexists. eapply stp2_strong_sel1. eauto.
    eassumption. eapply stp2_wrapf. eassumption.
    eauto. eauto. eauto. omega.
  - Case "sel2".
    remember H3 as Hv. clear HeqHv.
    eapply IHn in H5. eapply sstpd2_untrans in H5. eapply valtp_widen with (2:=H5) in H3.
    eapply invert_typ in H3. ev. repeat eu. subst.
    assert (closed (0+1) (length ([]:aenv)) x2). eapply inv_closed_open. eapply stp2_closed2; eauto. eauto. eauto.
    eexists. eapply stp2_strong_sel2. eauto.
    eassumption. eapply stp2_wrapf. eassumption.
    eauto. eauto. eauto. omega.
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
  - Case "or21". subst. eapply IHn in H1. inversion H1. eapply IHn in H2. inversion H2.
    eexists. eapply stp2_or21; eauto. omega. omega.
  - Case "or22". subst. eapply IHn in H1. inversion H1. eapply IHn in H2. inversion H2.
    eexists. eapply stp2_or22; eauto. omega. omega.
  - Case "or1". subst. eapply IHn in H1. inversion H1. eapply IHn in H2. inversion H2.
    eexists. eapply stp2_or1; eauto. omega. omega.
  - Case "wrapf". eapply IHn in H1. eu. eexists. eapply stp2_wrapf. eauto. omega.
  - Case "transf". eapply IHn in H1. eapply IHn in H2. eu. eu. eexists.
    eapply stp2_transf. eauto. eauto. omega. omega.
    Grab Existential Variables.
    apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.


(* can be called on level >= 1 *)

Lemma stp2_substitute_aux: forall ni nj, forall m G1 G2 T1 T2 GH n1,
   stp2 1 m G1 T1 G2 T2 GH n1 -> n1 < nj -> 
   forall GH0 GH0' GX TX TX' l T1' T2' V,
     GH = (GH0 ++ [(0,(GX, TX))]) ->
     val_type GX V (subst TX' TX) ni ->
     (* When we're replacing binds from a pack/unpack sequence, the
        type in GH may refer to itself (contain TSelH 0).
        It should be safe for TX to refer to itself. *)
     closed 0 1 TX ->
     closed 0 0 (TSel TX' l) ->
     compat GX TX TX' (Some V) G1 T1 T1' ->
     compat GX TX TX' (Some V) G2 T2 T2' ->
     Forall2 (compat2 GX TX TX' (Some V)) GH0 GH0' ->
     compat GX TX TX' (Some V) GX TX (subst TX' TX) ->
     exists n1', stp2 1 m G1 T1' G2 T2' GH0' n1'.
Proof.
  intros ni. induction ni.
  intros. inversion H2. (* ni=0 case: can't happen, invert val_type *)
  intros n. induction n; intros m G1 G2 T1 T2 GH n1 H ?. inversion H0.
  inversion H; subst.
  - Case "topx".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_top in IX1.
    eapply compat_top in IX2.
    subst. eexists. eapply stp2_topx. eauto. eauto.

  - Case "botx".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_bot in IX1.
    eapply compat_bot in IX2.
    subst. eexists. eapply stp2_botx. eauto. eauto.

  - Case "top".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_top in IX2.
    subst.
    eapply IHn in H1. destruct H1.
    eexists. eapply stp2_top. eauto. omega. 
    eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.

  - Case "bot".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_bot in IX1.
    subst.
    eapply IHn in H1. destruct H1.
    eexists. eapply stp2_bot. eauto. omega. 
    eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.

  - Case "bool".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    eapply compat_bool in IX1.
    eapply compat_bool in IX2.
    subst. eexists. eapply stp2_bool; eauto.
    eauto. eauto.

  - Case "mem".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
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
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

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

  - Case "sel2".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

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

  - Case "selx".

    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (T1' = TSel (varF x1) l). destruct IX1. ev. eauto. destruct H6. ev. auto. ev. eauto.
    assert (T2' = TSel (varF x2) l). destruct IX2. ev. eauto. destruct H7. ev. auto. ev. eauto.

    subst.
    eexists.
    eapply stp2_selx. eauto. eauto.

  - Case "sela1".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX TXX' (Some V) G1 (TSel (varH x) l) T1') as IXX. eauto.

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
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length (GU ++ GL) = length GH0 + 1). rewrite H1. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX TXX' (Some V) G1 (TSel (varH x) l) T1') as IXX. eauto.

    eapply (compat_selh GXX TXX TXX' (Some V) G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    destruct IX1.
    + SCase "x = 0". ev. subst.
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H11. subst.


        assert (GL = [(0, (GXX, TXX))]) as EQGL. {
          eapply proj2. eapply concat_same_length'. eassumption.
          simpl. eassumption.
        }

        assert (exists nb, stp2 1 false GXX (subst TXX' TXX) G2 (TBind (TMem l TBot T0)) [] nb) as SBind. {
          eapply IHn. eauto. omega. rewrite app_nil_l. eauto. eauto. eapply CX. eauto. eauto.
          right. left. split. eassumption. reflexivity.
          eauto. eauto.
        }
        destruct SBind as [nb SBind].

        (* (todo: revise note)
           If the input level is 1, we cannot create a selb node.
           A potential avenue is to create a sel node directly.
           But this is not straightforward: we have an imprecise bind which we need to invert.
           Inversion requires transitivity, which increases the size.
           Then on the internal stp obtained from the inverted bind, we need to call
           subst again, but it need not be smaller than our own input.

           Fortunately, we know that we are unpacking a bind in the valtp,
           which becomes the new self object, so we can do an outer
           induction on the valtp depth.

           TODO: Can we use the same approach for selb, and get rid of the
           level 2 pushback altogether?  <--- YES!
         *)

        {

        assert (exists n1, stp2 0 true GXX (subst TXX' TXX) G2 (TBind (TMem l TBot T0)) [] n1) as SBind0. {
          eapply sstpd2_untrans. eapply stpd2_to_sstpd2_aux1. eauto. eauto.
          
        }
        destruct SBind0 as [n1 SBind0].

        assert (val_type G2 x0 (TBind (TMem l TBot T0)) (S ni)) as VSB. eapply valtp_widen. eapply VS. eexists. eapply SBind0.
        inversion VSB; subst; ev.
        inversion H14.
        eapply dcs_tbind in H17. inversion H17. eassumption.
        inversion H14.
        inversion H14. (* invert bind/bind *) subst.


        assert (closed 0 0 (open (varF x2) T2)) as CL. eapply closed_open. eauto. eauto.

        assert (compat venv0 (open (varH 0) T2) (varF x2)
                       (Some x0) venv0 (open (varH 0) T2)
                       (open (varF x2) T2)) as CP1. {
          left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        }
        assert (compat venv0 (open (varH 0) T2) (varF x2)
     (Some x0) G2 (open (varH 0) (TMem l TBot T0))
     (TMem l TBot T2')) as CP2. {
          destruct IX2 as [IX2 | [IX2 | IX2]].
        (*1*)repeat destruct IX2 as [|IX2]; ev. inversion H18; subst.
        rewrite subst_open1.
        left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        inversion H4. inversion H28. eauto. (* closed 1 0 T0 *)
        (*2*)destruct IX2 as [IX21 IX22]. right. left. split. econstructor; eauto. rewrite IX22. eauto.
        (*3*)destruct IX2 as [IX21 IX22]. right. right. split. econstructor; simpl; eauto. rewrite IX22. eauto.
        }
        assert (compat venv0 (open (varH 0) T2) (varF x2)
     (Some x0) venv0 (open (varH 0) T2)
     (subst (varF x2) (open (varH 0) T2))) as CPH. {
           left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        }



        assert (exists n7, stp2 1 false venv0 (open (varF x2) T2) G2 (TMem l TBot T2') [] n7) as ST1. {
          subst.
          eapply IHni in H24. destruct H24 as [? H24].
          eexists.
          eapply H24.
          eauto. eauto. rewrite app_nil_l. eauto.
          rewrite subst_open1. eauto. eauto.
          eapply closed_open. eapply closed_upgrade_free. eauto. eauto. eauto. eauto.
          eauto. eauto. eauto. eauto.
        }
        destruct ST1 as [n7 ST1].

        assert (stp2 1 false venv0 (open (varF x2) T2) G2 (TMem l TBot T2') GH0' n7) as ST1'.
        eapply stp2_extendH_mult in ST1. rewrite app_nil_r in ST1. eapply ST1.

        assert (exists n9, stp2 1 true G2 (TMem l TBot T2') G2 (TMem l TBot T2') GH0' n9) as REG1.
        eapply stp2_reg2. eauto.
        destruct REG1 as [n9 REG1].

        assert (exists n8, stp2 1 true G2 T2' G2 T2' GH0' n8) as REG1'.
        inversion REG1. subst.
        eapply stp2_reg2. eapply H36.
        destruct REG1' as [n8 REG1'].

        eexists. eapply stp2_sel1. eauto. eauto. eauto.
        eapply ST1'. eapply REG1'.
        }

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
      unfold open. erewrite subst_open_commute.
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
      unfold open. erewrite subst_open_commute.
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
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length (GU ++ GL) = length GH0 + 1). rewrite H1. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX TXX' (Some V) G2 (TSel (varH x) l) T2') as IXX. eauto.

    eapply (compat_selh GXX TXX TXX' (Some V) G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    destruct IX2.
    + SCase "x = 0". ev. subst.
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H11. subst.


        assert (GL = [(0, (GXX, TXX))]) as EQGL. {
          eapply proj2. eapply concat_same_length'. eassumption.
          simpl. eassumption.
        }

        assert (exists nb, stp2 1 false GXX (subst TXX' TXX) G1 (TBind (TMem l T0 TTop)) [] nb) as SBind. {
          eapply IHn. eauto. omega. eauto. rewrite app_nil_l. eauto. eauto. eapply CX. eauto. eauto.
          right. left. split. eassumption. reflexivity.
          eauto. eauto.
        }
        destruct SBind as [nb SBind].

        {

        assert (exists n1, stp2 0 true GXX (subst TXX' TXX) G1 (TBind (TMem l T0 TTop)) [] n1) as SBind0. {
          eapply sstpd2_untrans. eapply stpd2_to_sstpd2_aux1. eauto. eauto.
        }
        destruct SBind0 as [n1 SBind0].

        assert (val_type G1 x0 (TBind (TMem l T0 TTop)) (S ni)) as VSB. eapply valtp_widen. eapply VS. eexists. eapply SBind0.
        inversion VSB; subst; ev.
        inversion H14.
        eapply dcs_tbind in H17. inversion H17. eassumption.
        inversion H14.
        inversion H14. (* invert bind/bind *) subst.


        assert (closed 0 0 (open (varF x2) T2)) as CL. eapply closed_open. eauto. eauto.

        assert (compat venv0 (open (varH 0) T2) (varF x2)
                       (Some x0) venv0 (open (varH 0) T2)
                       (open (varF x2) T2)) as CP1. {
          left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        }
        assert (compat venv0 (open (varH 0) T2) (varF x2)
     (Some x0) G1 (open (varH 0) (TMem l T0 TTop))
     (TMem l T1' TTop)) as CP2. {
          destruct IX1 as [IX1 | [IX1 | IX1]].
        (*1*)repeat destruct IX2 as [|IX2]; ev. inversion H18; subst.
        rewrite subst_open1.
        left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        inversion H4. inversion H28. eauto. (* closed 1 0 T0 *)
        (*2*)destruct IX1 as [IX11 IX12]. right. left. split. econstructor; eauto. rewrite IX12. eauto.
        (*3*)destruct IX1 as [IX11 IX12]. right. right. split. econstructor; simpl; eauto. rewrite IX12. eauto.
        }
        assert (compat venv0 (open (varH 0) T2) (varF x2)
     (Some x0) venv0 (open (varH 0) T2)
     (subst (varF x2) (open (varH 0) T2))) as CPH. {
           left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto. split. rewrite subst_open1. eauto. eauto. rewrite subst_open1. eauto. eauto.
        }



        assert (exists n7, stp2 1 false venv0 (open (varF x2) T2) G1 (TMem l T1' TTop) [] n7) as ST1. {
          subst.
          eapply IHni in H24. destruct H24 as [? H24].
          eexists.
          eapply H24.
          eauto. eauto. rewrite app_nil_l. eauto.
          rewrite subst_open1. eauto. eauto.
          eapply closed_open. eapply closed_upgrade_free. eauto. eauto. eauto. eauto.
          eauto. eauto. eauto. eauto.
        }
        destruct ST1 as [n7 ST1].

        assert (stp2 1 false venv0 (open (varF x2) T2) G1 (TMem l T1' TTop) GH0' n7) as ST1'.
        eapply stp2_extendH_mult in ST1. rewrite app_nil_r in ST1. eapply ST1.

        assert (exists n9, stp2 1 true G1 (TMem l T1' TTop) G1 (TMem l T1' TTop) GH0' n9) as REG1.
        eapply stp2_reg2. eauto.
        destruct REG1 as [n9 REG1].

        assert (exists n8, stp2 1 true G1 T1' G1 T1' GH0' n8) as REG1'.
        inversion REG1.
        eapply stp2_reg2. eapply H34.
        destruct REG1' as [n8 REG1'].

        eexists. eapply stp2_sel2. eauto. eauto. eauto.
        eapply ST1'. eapply REG1'.
        }

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
      unfold open. erewrite subst_open_commute.
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
      unfold open. erewrite subst_open_commute.
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
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX TXX' (Some V) G2 (TSel (varH x) l) T2') as IXX by eauto.

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
        omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
        omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
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
      omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      omega. eauto. eauto. eauto. eauto. eauto. eauto. eapply compat_mem_fwd1. eauto. eauto. eauto.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.

  - Case "selax".

    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX TXX' (Some V) G1 (TSel (varH x) l) T1') as IXX1. eauto.
    assert (compat GXX TXX TXX' (Some V) G2 (TSel (varH x) l) T2') as IXX2. eauto.

    eapply (compat_selh GXX TXX TXX' (Some V) G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].
    eapply (compat_selh GXX TXX TXX' (Some V) G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].
    assert (not (nosubst (TSel (varH 0) l))). unfold not. intros. simpl in H1. eauto.
    assert (not (closed 0 0 (TSel (varH 0) l))). unfold not. intros. inversion H6. omega.

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
    intros GH0 GH0' GX TX TX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

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
    omega. eauto.
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
    intros GH0 GH0' GX TX TX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply compat_bind in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_bind in IX2. repeat destruct IX2 as [? IX2].

    subst.

    eapply IHn in H3. destruct H3.
    eapply IHn in H4. destruct H4.
    eexists.
    eapply stp2_bind.
    eauto.
    eauto.
    eauto.
    eauto.
    omega.
      instantiate (3:=(0, (G1,  open (varH (length (GH0 ++ [(0, (GX, TX))]))) T0))::GH0).
      reflexivity.
      eauto. eapply CX. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto. repeat split. rewrite app_length. simpl. rewrite EL. eapply IX1. eauto.
      eauto.
    omega.
      change
        ((0, (G2, open (varH (length (GH0 ++ [(0, (GX, TX))]))) T3))
           :: GH0 ++ [(0, (GX, TX))]) with
      (((0, (G2, open (varH (length (GH0 ++ [(0, (GX, TX))]))) T3))
          :: GH0) ++ [(0, (GX, TX))]).
      reflexivity.
      eauto. eapply CX. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto. repeat split. rewrite app_length. simpl. rewrite EL. eapply IX2. eauto.
      eauto.
    eauto.
    eauto. subst GH. fold id. rewrite <- EL.
    eapply closed_upgrade_free. eauto. unfold id in H4.
    rewrite app_length. simpl. omega.
    eauto.
    eauto. subst GH. fold id. rewrite <-EL.
      eapply closed_upgrade_free. eauto. unfold id in H4.
      rewrite app_length. simpl. omega.

  - Case "and11".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    subst. apply compat_and in IX1. repeat destruct IX1 as [? IX1].
    eapply IHn in H1. destruct H1.
    eapply IHn in H2. destruct H2.
    eexists.
    subst. eapply stp2_and11; eassumption.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.
  - Case "and12".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    subst. apply compat_and in IX1. repeat destruct IX1 as [? IX1].
    eapply IHn in H1. destruct H1.
    eapply IHn in H2. destruct H2.
    eexists.
    subst. eapply stp2_and12; eassumption.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.
  - Case "and2".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    subst. apply compat_and in IX2. repeat destruct IX2 as [? IX2].
    eapply IHn in H1. destruct H1.
    eapply IHn in H2. destruct H2.
    eexists.
    subst. eapply stp2_and2. eapply H1. eapply H2.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.

  - Case "or21".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    subst. apply compat_or in IX2. repeat destruct IX2 as [? IX2].
    eapply IHn in H1. destruct H1.
    eapply IHn in H2. destruct H2.
    eexists.
    subst. eapply stp2_or21; eassumption.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.
  - Case "or22".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    subst. apply compat_or in IX2. repeat destruct IX2 as [? IX2].
    eapply IHn in H1. destruct H1.
    eapply IHn in H2. destruct H2.
    eexists.
    subst. eapply stp2_or22; eassumption.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    eauto.
  - Case "or1".
    intros GH0 GH0' GXX TXX TXX' lX T1' T2' V ? VS CX ? IX1 IX2 FA IXH.
    subst. apply compat_or in IX1. repeat destruct IX1 as [? IX1].
    eapply IHn in H1. destruct H1.
    eapply IHn in H2. destruct H2.
    eexists.
    subst. eapply stp2_or1. eapply H1. eapply H2.
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

    assert (stp2 1 true G1 T1 ((fresh G3,V)::G3) T3 (GH0 ++ [(0, (GX, TX))]) n0) as S1.
    eapply stp2_extend2; eauto.
    assert (stp2 1 false ((fresh G3,V)::G3) T3 G2 T2 (GH0 ++ [(0, (GX, TX))]) n2) as S2.
    eapply stp2_extend1; eauto.

    eapply IHn in S1. destruct S1 as [? S1].
    eapply IHn in S2. destruct S2 as [? S2].
    eexists.
    eapply stp2_transf. eapply S1. eapply S2.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
    omega. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
apply 0. 
Qed.


Lemma stpd2_substitute: forall m G1 G2 T1 T2 GH,
   stpd2 m G1 T1 G2 T2 GH ->
   forall GH0 GH0' GX TX TX' l T1' T2' V n,
     GH = (GH0 ++ [(0,(GX, TX))]) ->
     val_type GX V (subst TX' TX) n ->
     closed 0 1 TX ->
     closed 0 0 (TSel TX' l) ->
     compat GX TX TX' (Some V) G1 T1 T1' ->
     compat GX TX TX' (Some V) G2 T2 T2' ->
     compat GX TX TX' (Some V) GX TX (subst TX' TX) ->
     Forall2 (compat2 GX TX TX' (Some V)) GH0 GH0' ->
     stpd2 m G1 T1' G2 T2' GH0'.
Proof. intros. repeat eu. eapply stp2_substitute_aux; eauto. Qed.

(* end substitute *)



Lemma stpd2_to_atpd2: forall G1 G2 T1 T2 GH m,
  stpd2 m G1 T1 G2 T2 GH ->
  atpd2 m G1 T1 G2 T2 GH.
Proof.
  intros. eauto.
Qed.

Lemma stpd2_to_sstpd2: forall G1 G2 T1 T2 m,
  stpd2 m G1 T1 G2 T2 nil ->
  sstpd2 m G1 T1 G2 T2 nil.
Proof.
  intros. eu.
  eapply stpd2_to_sstpd2_aux1; eauto. 
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
  - Case "or21".
    eapply stpd2_or21; eauto.
    eapply IHstp2_1; eauto. eexists. rewrite <- Heqm. eassumption.
    eapply IHstp2_2; eauto. eexists. rewrite <- Heqm. eassumption.
  - Case "or22".
    eapply stpd2_or22; eauto.
    eapply IHstp2_1; eauto. eexists. rewrite <- Heqm. eassumption.
    eapply IHstp2_2; eauto. eexists. rewrite <- Heqm. eassumption.
  - Case "or1".
    eapply stpd2_or1; eauto.
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


(* TODO: need to revisit if stp includes trans rule.
   if yes, probably need to return stpd2 false, and
   call untrans after recursive calls *)
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
    (* replace x: {z => ..U }  U < T2  by x: (.. U)  U < T *)
    (* previously, there was a separate stp2 level for this *)
    assert (exists (v : vl) n, index x GX = Some v /\ val_type GX v TX n) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? [? VT]]].
    assert (sstpd2 true GX TX GX (TBind (TMem m TBot T2)) []).
    eapply stpd2_to_sstpd2. eapply IHST1; eauto.
    assert (val_type GX x0 (TBind (TMem m TBot T2)) x1) as V2. eapply valtp_widen; eauto.
    inversion V2.
    subst. destruct H2. inversion H2.
    inversion H6. 
    subst. eapply dcs_tbind in H4. inversion H4. eassumption. (* 1 case left *)

    destruct H5. inversion H5. subst. 

    assert (exists n, stp2 1 false venv0 (open (varF x2) T0) GX
          (open (varF x) (TMem m TBot T2))
          [] n) as ST. {
      eapply stp2_substitute_aux with (GH0:=[]).
      eauto.
      eauto.
      simpl. reflexivity.
      erewrite subst_open1. eassumption. eauto. 
      eapply closed_open. simpl. eapply closed_upgrade. eauto. eapply closed_upgrade_free. eauto. simpl. eauto. eauto. eauto. eauto.
      left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto.
      split. rewrite subst_open1; eauto. simpl. rewrite subst_open1; eauto.
      left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto.
      split. rewrite subst_open1; eauto. rewrite subst_open1; eauto.
      eauto. (* forall *)
      left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto.
      split. rewrite subst_open1; eauto. rewrite subst_open1; eauto.
    }
    assert ((open (varF x) (TMem m TBot T2) = TMem m TBot (open (varF x) T2))) as Q.
    unfold open. unfold open. simpl. eauto.
    
    eapply stpd2_sel1. eauto. eauto. eapply valtp_closed; eauto.
    rewrite Q in ST.
    eapply stpd2_extendH_mult0. eapply atpd2_to_stpd2. apply ST.
    
    specialize (IHST2 GX GY WX WY).
    apply stpd2_reg2 in IHST2.
    apply IHST2.
  - Case "selb2".
    assert (exists (v : vl) n, index x GX = Some v /\ val_type GX v TX n) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? [? VT]]].
    assert (sstpd2 true GX TX GX (TBind (TMem m T1 TTop)) []).
    eapply stpd2_to_sstpd2. eapply IHST1; eauto.
    assert (val_type GX x0 (TBind (TMem m T1 TTop)) x1) as V2. eapply valtp_widen; eauto.
    inversion V2.
    subst. destruct H2. inversion H2.
    inversion H6. 
    subst. eapply dcs_tbind in H4. inversion H4. eassumption. (* 1 case left *)

    destruct H5. inversion H5. subst. 

    assert (exists n, stp2 1 false venv0 (open (varF x2) T2) GX
          (open (varF x) (TMem m T1 TTop))
          [] n) as ST. {
      eapply stp2_substitute_aux with (GH0:=[]).
      eauto.
      eauto.
      simpl. reflexivity.
      erewrite subst_open1. eassumption. eauto. 
      eapply closed_open. simpl. eapply closed_upgrade. eauto. eapply closed_upgrade_free. eauto. simpl. eauto. eauto. eauto. eauto.
      left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto.
      split. rewrite subst_open1; eauto. simpl. rewrite subst_open1; eauto.
      left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto.
      split. rewrite subst_open1; eauto. rewrite subst_open1; eauto.
      eauto. (* forall *)
      left. eexists. eexists. eexists. split. eauto. split. eauto. split. eauto.
      split. rewrite subst_open1; eauto. rewrite subst_open1; eauto.
    }
    assert ((open (varF x) (TMem m T1 TTop) = TMem m (open (varF x) T1) TTop)) as Q.
    unfold open. unfold open. simpl. eauto.
    
    eapply stpd2_sel2. eauto. eauto. eapply valtp_closed; eauto.
    rewrite Q in ST.
    eapply stpd2_extendH_mult0. eapply atpd2_to_stpd2. apply ST.
    
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
  - Case "or21".
    eapply stpd2_or21.
    eapply stpd2_wrapf. eapply IHST1; eauto.
    eapply IHST2; eauto.
  - Case "or22".
    eapply stpd2_or22.
    eapply stpd2_wrapf. eapply IHST1; eauto.
    eapply IHST2; eauto.
  - Case "or1".
    eapply stpd2_or1.
    eapply IHST1; eauto.
    eapply IHST2; eauto.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0.    
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
| wf_mem: forall G1 GH l T1 T2,
    wf_tp G1 GH T1 ->
    wf_tp G1 GH T2 ->
    wf_tp G1 GH (TMem l T1 T2)
| wf_sel: forall G1 GH TX x l,
    index x G1 = Some TX ->
    wf_tp G1 GH (TSel (varF x) l)
| wf_sela: forall G1 GH TX x l,
    indexr x GH = Some TX  ->
    wf_tp G1 GH (TSel (varH x) l)
| wf_all: forall G1 GH m T1 T2 x,
    wf_tp G1 GH T1 ->
    x = length GH ->
    closed 1 (length GH) T2 ->
    wf_tp G1 ((0,T1)::GH) (open (varH x) T2) ->
    wf_tp G1 GH (TAll m T1 T2)
| wf_bind: forall G1 GH T1 x,
    x = length GH ->
    closed 1 (length GH) T1 ->
    wf_tp G1 ((0,open (varH x) T1)::GH) (open (varH x) T1) ->
    wf_tp G1 GH (TBind T1)
| wf_and: forall G1 GH T1 T2,
    wf_tp G1 GH T1 ->
    wf_tp G1 GH T2 ->
    wf_tp G1 GH (TAnd T1 T2)
| wf_or: forall G1 GH T1 T2,
    wf_tp G1 GH T1 ->
    wf_tp G1 GH T2 ->
    wf_tp G1 GH (TOr T1 T2)
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

Lemma wf_tp_to_stp2_cycle_aux: forall T0 T v G GH,
  wf_tp ((fresh G, T0) :: G) GH T ->
  forall GX GY, wf_env GX G -> wf_envh ((fresh G, v)::GX) GY GH ->
  stpd2 true ((fresh G, v) :: GX) T
             ((fresh G, v) :: GX) T GY.
Proof.
  intros T0 T t G GH ST.
  dependent induction ST; intros GX GY WX WY.
  - Case "top". eapply stpd2_topx.
  - Case "bot". eapply stpd2_botx.
  - Case "bool". eapply stpd2_bool; eauto.
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
  - Case "or".
    eapply stpd2_or1.
    eapply stpd2_or21. eapply stpd2_wrapf. eapply IHST1; eauto. eapply IHST2; eauto.
    eapply stpd2_or22. eapply stpd2_wrapf. eapply IHST2; eauto. eapply IHST1; eauto.
Qed.

Lemma stp_to_stp2_cycle: forall venv env T0 T t,
  wf_env venv env ->
  stp ((fresh env, T0) :: env) [] T T->
  stpd2 false ((fresh env, vobj venv (fresh venv) t) :: venv) T
              ((fresh env, vobj venv (fresh venv) t) :: venv) T [].
Proof.
  intros. apply stpd2_wrapf.
  eapply stp_to_wf_tp in H0.
  eapply wf_tp_to_stp2_cycle_aux; eauto.
Qed.

Lemma dcs_has_type_stp: forall G G1 G2 f ds x T T1 T2,
  dcs_has_type G f ds T ->
  sstpd2 true G1 (open (varF x) T) G2 (TAll (length ds) T1 T2) [] ->
  False.
Proof.
  intros. remember (length ds) as l. assert (l >= length ds) as A by omega. clear Heql.
  induction H. simpl in H0. destruct H0 as [? H0]. inversion H0.
  destruct (tand_shape (TAll m T0 T3) TS).
  rewrite H5 in H4. rewrite H4 in H0. simpl in H0. destruct H0 as [? H0]. inversion H0.
  subst. inversion H9. subst. simpl in A. omega.
  apply IHdcs_has_type. eexists. eassumption. simpl in A. omega.
  rewrite H5 in H4. rewrite H4 in H0. simpl in H0. destruct H0 as [? H0]. inversion H0.
  simpl in A. omega.
  destruct (tand_shape (TMem m T0 T0) TS).
  rewrite H3 in H2. rewrite H2 in H0. simpl in H0. destruct H0 as [? H0]. inversion H0.
  subst. inversion H7.
  apply IHdcs_has_type. eexists. eassumption. simpl in A. omega.
  rewrite H3 in H2. rewrite H2 in H0. simpl in H0. destruct H0 as [? H0]. inversion H0.
Qed.

Lemma invert_obj: forall venv vf l T1 T2 n vx nx,
  val_type venv vf (TAll l T1 T2) n ->
  val_type venv vx T1 nx ->
  sstpd2 true venv T2 venv T2 [] ->
  exists env tenv TF ds x y T3 T4,
    vf = (vobj env (fresh env) ds) /\
    1 + (fresh env) = x /\
    index l ds = Some (dfun x y) /\
    wf_env env tenv /\
    dcs_has_type (((fresh env), (open (varF (fresh env)) TF))::tenv) (fresh env) ds TF /\
    sstpd2 true ((fresh env, vobj env (fresh env) ds) :: env) (open (varF (fresh env)) TF) ((fresh env, vobj env (fresh env) ds) :: env) (open (varF (fresh env)) TF) [] /\
    has_type ((x,(open (varF (fresh env)) T3))::((fresh env),(open (varF (fresh env)) TF))::tenv) y (open (varF x) (open_rec 1 (varF (fresh env)) T4)) /\
    sstpd2 true venv T1 (((fresh env), vobj env (fresh env) ds)::env) (open (varF (fresh env)) T3) [] /\
    sstpd2 true ((x, vx)::((fresh env), vobj env (fresh env) ds)::env) (open (varF x) (open_rec 1 (varF (fresh env)) T4)) venv T2 [].
Proof.
  intros. inversion H; repeat ev; try solve by inversion.
  subst.
  exists venv1. exists tenv0. exists T. exists ds.
  assert (exists y T3 T4, index l ds = Some (dfun (1 + (fresh venv1))  y) /\ has_type ((1+(fresh venv1), (open (varF (fresh venv1)) T3)) :: ((fresh venv1), (open (varF (fresh venv1)) T)) :: tenv0) y (open (varF (1 + (fresh venv1))) (open_rec 1 (varF (fresh venv1)) T4)) /\ sstpd2 true (((fresh venv1), vobj venv1 (fresh venv1) ds)::venv1) (open (varF (fresh venv1)) (TAll l T3 T4)) venv0 (TAll l T1 T2) []) as A. {
    clear H. clear H0.
    unfold id in H4.
    remember ((fresh venv1, (open (varF (fresh venv1)) T))::tenv0) as tenv.
    assert (fresh tenv = S (fresh venv1)) as A. { rewrite Heqtenv. simpl. reflexivity. }
    clear Heqtenv.
    unfold id in H6.
    remember ((fresh venv1, vobj venv1 (fresh venv1) ds) :: venv1) as venv.
    assert (sstpd2 true venv (open (varF (fresh venv1)) T) venv0 (TAll l T1 T2) []) as B. { eexists; eassumption. }
    clear H6. clear Heqvenv.
    induction H4. destruct B as [? B]. inversion B.
    simpl.
    case_eq (le_lt_dec (fresh dcs) m); intros LE E1.
    case_eq (beq_nat l m); intros E2.
    exists y. eexists. eexists.
    split. rewrite <- A. rewrite H0. reflexivity.
    split. rewrite <- A. rewrite H0. eapply H.
    destruct (tand_shape (TAll m T0 T3) TS).
    rewrite H6 in H5. rewrite H5 in B. destruct B as [? B]. unfold open in B. simpl in B. inversion B. eapply beq_nat_true in E2. rewrite <- E2 in H10. eexists. eassumption.
    eapply dcs_has_type_stp in H4. inversion H4. rewrite <- H3. eapply beq_nat_true in E2. rewrite <- E2. eexists. eassumption.
    rewrite H6 in H5. rewrite H5 in B. eapply beq_nat_true in E2. rewrite <- E2 in B. apply B.
    eapply IHdcs_has_type. apply A. destruct (tand_shape (TAll m T0 T3) TS).
    rewrite H6 in H5. rewrite H5 in B. destruct B as [? B]. inversion B. unfold open in H10. simpl in H10. inversion H10. apply beq_nat_false in E2. omega. eexists. eassumption.
    rewrite H6 in H5. rewrite H5 in B. destruct B as [? B]. inversion B. apply beq_nat_false in E2. omega.
    inversion H4; subst. simpl in LE. omega. simpl in LE. omega. simpl in LE. omega.
    simpl.
    case_eq (le_lt_dec (fresh dcs) m); intros LE E1.
    case_eq (beq_nat l m); intros E2.
    destruct (tand_shape (TMem m T0 T0) TS).
    rewrite H3 in H0. rewrite H0 in B. destruct B as [? B]. unfold open in B. simpl in B. inversion B. eapply beq_nat_true in E2. rewrite <- E2 in H8. inversion H8.
    eapply dcs_has_type_stp in H4. inversion H4. rewrite <- H. eapply beq_nat_true in E2. rewrite <- E2. eexists. eassumption.
    rewrite H3 in H0. rewrite H0 in B. eapply beq_nat_true in E2. rewrite <- E2 in B. inversion B.
    unfold open in H5. simpl in H5. inversion H5.
    eapply IHdcs_has_type. apply A. destruct (tand_shape (TMem m T0 T0) TS).
    rewrite H3 in H0. rewrite H0 in B. destruct B as [? B]. inversion B. unfold open in H8. simpl in H8. inversion H8. eexists. eassumption.
    rewrite H3 in H0. rewrite H0 in B. destruct B as [? B]. inversion B.
    inversion H4; subst. simpl in LE. omega. simpl in LE. omega. simpl in LE. omega.
  }
  destruct A as [y [T3 [T4 [A1 [A2 A3]]]]].
  exists (1 + (fresh venv1)). exists y. exists T3. exists T4.
  split. reflexivity. split. reflexivity.
  split. apply A1.
  split. assumption. split. assumption.
  split. eapply sstpd2_reg1. eexists. eassumption.
  split. apply A2.
  destruct A3 as [? A3]. inversion A3. subst. split.
  eapply stpd2_upgrade. eexists. eassumption.

  assert (stpd2 false venv0 T1
          ((fresh venv1, vobj venv1 (fresh venv1) ds) :: venv1)
          (open_rec 0 (varF (fresh venv1)) T3) []) as ARG. eauto.
  assert (stpd2 false ((fresh venv1, vobj venv1 (fresh venv1) ds) :: venv1)
          (open (varH 0) (open_rec 1 (varF (fresh venv1)) T4))
          venv0 (open (varH 0) T2) [(0, (venv0, T1))]) as KEY. eauto.

  eapply stpd2_upgrade in ARG.

  assert (stpd2 false venv0 T1 venv0 T1 []) as HR1. eapply stpd2_wrapf. eapply stpd2_reg1. eauto.
  assert (closed 0 0 T1). eapply stpd2_closed1 in HR1. simpl in HR1. apply HR1.

  assert (stpd2 false ((1 + fresh venv1, vx)::(fresh venv1, vobj venv1 (fresh venv1) ds)::venv1)
                (open_rec 0 (varF (1 + fresh venv1)) (open_rec 1 (varF (fresh venv1)) T4))
                venv0 T2 []) as HR2. {
    assert (closed 0 (length ([]:aenv)) T2). eapply sstpd2_closed1; eauto.
    assert (open (varH 0) T2 = T2) as OP2. symmetry. eapply closed_no_open; eauto.

    eapply stpd2_substitute with (GH0:=nil).
    eapply stpd2_extend1. eapply KEY.
    eauto. simpl. eauto.
    erewrite closed_no_subst. eassumption. eassumption.
    eapply closed_upgrade_free. eauto. omega. eauto.
    left. repeat eexists. eapply index_hit2. eauto. eauto. eauto.
    rewrite closed_no_subst with (j:=0). eauto. eauto.
    rewrite (subst_open_zero 0 1). eauto. eauto.
    right. left. split. rewrite OP2. eauto. eauto.
    right. left. split. eauto. rewrite closed_no_subst with (j:=0). eauto. eauto.
    eauto.
  }
  eapply stpd2_upgrade in HR2.
  subst. eauto.
Grab Existential Variables.
apply 0. apply 0.
Qed.

Lemma invert_obj_var: forall venv vf l T1 T2 n vx nx xarg,
  val_type venv vf (TAll l T1 T2) n ->
  val_type venv vx T1 nx ->
  index xarg venv = Some vx ->
  sstpd2 true venv (open (varF xarg) T2) venv (open (varF xarg) T2) [] ->
  exists env tenv TF ds x y T3 T4,
    vf = (vobj env (fresh env) ds) /\
    1 + (fresh env) = x /\
    index l ds = Some (dfun x y) /\
    wf_env env tenv /\
    dcs_has_type (((fresh env), (open (varF (fresh env)) TF))::tenv) (fresh env) ds TF /\
    sstpd2 true ((fresh env, vobj env (fresh env) ds) :: env) (open (varF (fresh env)) TF) ((fresh env, vobj env (fresh env) ds) :: env) (open (varF (fresh env)) TF) [] /\
    has_type ((x,(open (varF (fresh env)) T3))::((fresh env),(open (varF (fresh env)) TF))::tenv) y (open (varF x) (open_rec 1 (varF (fresh env)) T4)) /\
    sstpd2 true venv T1 (((fresh env), vobj env (fresh env) ds)::env) (open (varF (fresh env)) T3) [] /\
    sstpd2 true ((x, vx)::((fresh env), vobj env (fresh env) ds)::env) (open (varF x) (open_rec 1 (varF (fresh env)) T4)) venv (open (varF xarg) T2) [].
Proof.
  intros. inversion H; repeat ev; try solve by inversion.
  subst.
  exists venv1. exists tenv0. exists T. exists ds.
  assert (exists y T3 T4, index l ds = Some (dfun (1 + (fresh venv1))  y) /\ has_type ((1+(fresh venv1), (open (varF (fresh venv1)) T3)) :: ((fresh venv1), (open (varF (fresh venv1)) T)) :: tenv0) y (open (varF (1 + (fresh venv1))) (open_rec 1 (varF (fresh venv1)) T4)) /\ sstpd2 true (((fresh venv1), vobj venv1 (fresh venv1) ds)::venv1) (open (varF (fresh venv1)) (TAll l T3 T4)) venv0 (TAll l T1 T2) []) as A. {
    clear H. clear H0.
    unfold id in H5.
    remember ((fresh venv1, (open (varF (fresh venv1)) T))::tenv0) as tenv.
    assert (fresh tenv = S (fresh venv1)) as A. { rewrite Heqtenv. simpl. reflexivity. }
    clear Heqtenv.
    unfold id in H7.
    remember ((fresh venv1, vobj venv1 (fresh venv1) ds) :: venv1) as venv.
    assert (sstpd2 true venv (open (varF (fresh venv1)) T) venv0 (TAll l T1 T2) []) as B. { eexists; eassumption. }
    clear H7. clear Heqvenv.
    induction H5. destruct B as [? B]. inversion B.
    simpl.
    case_eq (le_lt_dec (fresh dcs) m); intros LE E1.
    case_eq (beq_nat l m); intros E2.
    exists y. eexists. eexists.
    split. rewrite <- A. rewrite H0. reflexivity.
    split. rewrite <- A. rewrite H0. eapply H.
    destruct (tand_shape (TAll m T0 T3) TS).
    rewrite H7 in H6. rewrite H6 in B. destruct B as [? B]. unfold open in B. simpl in B. inversion B. eapply beq_nat_true in E2. rewrite <- E2 in H11. eexists. eassumption.
    eapply dcs_has_type_stp in H5. inversion H5. rewrite <- H4. eapply beq_nat_true in E2. rewrite <- E2. eexists. eassumption.
    rewrite H7 in H6. rewrite H6 in B. eapply beq_nat_true in E2. rewrite <- E2 in B. apply B.
    eapply IHdcs_has_type. apply A. destruct (tand_shape (TAll m T0 T3) TS).
    rewrite H7 in H6. rewrite H6 in B. destruct B as [? B]. inversion B. unfold open in H11. simpl in H11. inversion H11. apply beq_nat_false in E2. omega. eexists. eassumption.
    rewrite H7 in H6. rewrite H6 in B. destruct B as [? B]. inversion B. apply beq_nat_false in E2. omega.
    inversion H5; subst. simpl in LE. omega. simpl in LE. omega. simpl in LE. omega.
    simpl.
    case_eq (le_lt_dec (fresh dcs) m); intros LE E1.
    case_eq (beq_nat l m); intros E2.
    destruct (tand_shape (TMem m T0 T0) TS).
    rewrite H4 in H0. rewrite H0 in B. destruct B as [? B]. unfold open in B. simpl in B. inversion B. eapply beq_nat_true in E2. rewrite <- E2 in H9. inversion H9.
    eapply dcs_has_type_stp in H5. inversion H5. rewrite <- H. eapply beq_nat_true in E2. rewrite <- E2. eexists. eassumption.
    rewrite H4 in H0. rewrite H0 in B. eapply beq_nat_true in E2. rewrite <- E2 in B. inversion B.
    unfold open in H6. simpl in H6. inversion H6.
    eapply IHdcs_has_type. apply A. destruct (tand_shape (TMem m T0 T0) TS).
    rewrite H4 in H0. rewrite H0 in B. destruct B as [? B]. inversion B. unfold open in H9. simpl in H9. inversion H9. eexists. eassumption.
    rewrite H4 in H0. rewrite H0 in B. destruct B as [? B]. inversion B.
    inversion H5; subst. simpl in LE. omega. simpl in LE. omega. simpl in LE. omega.
  }
  destruct A as [y [T3 [T4 [A1 [A2 A3]]]]].
  exists (1 + (fresh venv1)). exists y. exists T3. exists T4.
  split. reflexivity. split. reflexivity.
  split. apply A1.
  split. assumption. split. assumption.
  split. eapply sstpd2_reg1. eexists. eassumption.
  split. apply A2.
  destruct A3 as [? A3]. inversion A3. subst. split.
  eapply stpd2_upgrade. eexists. eassumption.

  assert (stpd2 false venv0 T1
          ((fresh venv1, vobj venv1 (fresh venv1) ds) :: venv1)
          (open_rec 0 (varF (fresh venv1)) T3) []) as ARG. eauto.
  assert (stpd2 false ((fresh venv1, vobj venv1 (fresh venv1) ds) :: venv1)
          (open (varH 0) (open_rec 1 (varF (fresh venv1)) T4))
          venv0 (open (varH 0) T2) [(0, (venv0, T1))]) as KEY. eauto.

  eapply stpd2_upgrade in ARG.

  assert (stpd2 false venv0 T1 venv0 T1 []) as HR1. eapply stpd2_wrapf. eapply stpd2_reg1. eauto.
  assert (closed 0 0 T1). eapply stpd2_closed1 in HR1. simpl in HR1. apply HR1.

  assert (stpd2 false ((1 + fresh venv1, vx)::(fresh venv1, vobj venv1 (fresh venv1) ds)::venv1)
                (open_rec 0 (varF (1 + fresh venv1)) (open_rec 1 (varF (fresh venv1)) T4))
                venv0 (open (varF xarg) T2) []) as HR2. {
    eapply stpd2_substitute with (GH0:=nil).
    eapply stpd2_extend1. eapply KEY.
    eauto. simpl. eauto.
    erewrite closed_no_subst. eassumption. eassumption.
    eapply closed_upgrade_free. eauto. omega. eauto.
    left. repeat eexists. eapply index_hit2. eauto. eauto. eauto.
    rewrite closed_no_subst with (j:=0). eauto. eauto.
    rewrite (subst_open_zero 0 1). eauto. eauto.
    left. repeat eexists. eassumption.
    rewrite closed_no_subst with (j:=0). eauto. eauto.
    rewrite (subst_open_zero 0 1). eauto. eauto.
    right. left. split. eauto. rewrite closed_no_subst with (j:=0). eauto. eauto.
    eauto.
  }
  eapply stpd2_upgrade in HR2.
  subst. eauto.
Grab Existential Variables.
apply 0. apply 0.
Qed.

Lemma valtp_reg: forall G v T n,
                   val_type G v T n ->
                   sstpd2 true G T G T [].
Proof. intros. induction H; eapply sstpd2_reg2; eauto. Qed.

Lemma has_type_wf:
  forall G t T, has_type G t T -> stp G [] T T.
Proof.
  intros. induction H; eauto.
  - eapply stp_reg. eassumption.

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
      assert (res_type venv0 (index i venv0) (open (varF i) T1)). eapply IHhas_type; eauto. eapply has_type_wf; eauto.
      inversion H3. subst.
      eapply not_stuck. eapply v_pack. eauto. eauto. eauto.
      eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

    + SCase "unpack".
      assert (res_type venv0 (index i venv0) (TBind T1)). eapply IHhas_type; eauto. eapply has_type_wf; eauto.
      inversion H3. subst.
      inversion H7; subst; ev; try solve by inversion.
      eapply dcs_tbind in H9. inversion H9. eassumption.
      eapply not_stuck. inversion H9. subst.

      assert (exists n, stp2 1 false venv1 (open (varF x) T2) venv0 (open (varF i) T1) [] n).
      eapply stp2_substitute_aux with (GH0:=nil).
      eapply H17. eauto. simpl. reflexivity.
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

(*
  - Case "Typ".
    remember (ttyp l) as e.
    induction H0; inversion Heqe; subst.
    + remember (fresh env) as i.
      remember (open (varF i) T) as TX.
      remember ((i,vty venv0 l)::venv0) as venv1.
      assert (index i venv1 = Some (vty venv0 l)). subst. eapply index_hit2. rewrite wf_fresh with (ts := env). eauto. eauto. eauto. eauto.
      assert ((open (varF (fresh venv0)) T) = TX). rewrite wf_fresh with (ts:=env). rewrite <-Heqi. eauto. eauto.
      assert (val_type venv1 (vty venv0 l) TX 1). eapply v_ty. eauto. eauto.
      eapply H4.

      (* we have everything as stp and 'just' need to convert to stp2. however we're
      working with an env that has a self binding, and the wf_env evidence needs
      the very val_tp what we're trying to construct *)

      eapply stpd2_upgrade. rewrite wf_fresh with (ts:=env). subst. eapply stp_to_stp2_cycle. eauto. eauto. eauto.

      eapply not_stuck. eapply v_pack. eapply H0. eapply H3. instantiate (1:=T). simpl. subst TX. eauto. subst venv1. eapply sstpd2_extend1. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. rewrite wf_fresh with (ts:=env). subst i. eauto. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

*)
  - Case "App".
    remember (tapp e1 i e2) as e. induction H0; inversion Heqe; subst.
    +
      remember (teval n venv0 e1) as tf.
      remember (teval n venv0 e2) as tx.


      destruct tx as [rx|]; try solve by inversion.
      assert (res_type venv0 rx T1) as HRX. SCase "HRX". subst. eapply IHn; eauto.
      inversion HRX as [? vx].

      destruct tf as [rf|]; subst rx; try solve by inversion.
      assert (res_type venv0 rf (TAll i T1 T2)) as HRF. SCase "HRF". subst. eapply IHn; eauto.
      inversion HRF as [? vf].

      destruct (invert_obj venv0 vf i T1 T2 n1 vx n0) as
          [env1 [tenv [TF [ds [x0 [y0 [T3 [T4 [EF [FRX [EQDS [WF [HDS [HTF [HTY [STX STY]]]]]]]]]]]]]]]]. eauto. eauto. eapply stpd2_upgrade. eapply stp_to_stp2. eassumption. eauto. eauto.
      (* now we know it's a closure, and we have has_type evidence *)

      assert (res_type ((x0,vx)::((fresh env1),vf)::env1) res (open (varF x0) (open_rec 1 (varF (fresh env1)) T4))) as HRY.
        SCase "HRY".
          subst. eapply IHn. rewrite EQDS in H3. eauto. eauto.
          (* wf_env f x *) econstructor. eapply valtp_widen; eauto. eapply sstpd2_extend2. eauto. eauto.
          (* wf_env f   *) econstructor. eapply v_obj; eauto.
          eauto.
      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto. rewrite EF. eauto.

    +
      remember (teval n venv0 e1) as tf.
      remember (teval n venv0 (tvar x)) as tx.


      destruct tx as [rx|]; try solve by inversion.
      assert (res_type venv0 rx T1) as HRX. SCase "HRX". subst. eapply IHn; eauto.
      inversion HRX as [? vx].

      destruct tf as [rf|]; subst rx; try solve by inversion.
      assert (res_type venv0 rf (TAll i T1 T2)) as HRF. SCase "HRF". subst. eapply IHn; eauto.
      inversion HRF as [? vf].

      destruct (invert_obj_var venv0 vf i T1 T2 n1 vx n0 x) as
          [env1 [tenv [TF [ds [x0 [y0 [T3 [T4 [EF [FRX [EQDS [WF [HDS [HTF [HTY [STX STY]]]]]]]]]]]]]]]]. eauto. eauto.
      destruct n. inversion Heqtx. simpl in Heqtx. inversion Heqtx. reflexivity.
      eapply stpd2_upgrade. eapply stp_to_stp2. eassumption. eauto. eauto.
      (* now we know it's a closure, and we have has_type evidence *)

      assert (res_type ((x0,vx)::((fresh env1),vf)::env1) res (open (varF x0) (open_rec 1 (varF (fresh env1)) T4))) as HRY.
        SCase "HRY".
          subst. eapply IHn. rewrite EQDS in H3. eauto. eauto.
          (* wf_env f x *) econstructor. eapply valtp_widen; eauto. eapply sstpd2_extend2. eauto. eauto.
          (* wf_env f   *) econstructor. eapply v_obj; eauto.
          eauto.
      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto. rewrite EF. eauto.


    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.


  - Case "Obj".
    remember (tobj i l) as xe. induction H0; inversion Heqxe; subst.
    + remember (open (varF i) T) as TX.
      remember ((i,vobj venv0 i l)::venv0) as venv1.
      assert (index i venv1 = Some (vobj venv0 i l)). subst. eapply index_hit2. rewrite wf_fresh with (ts := env). eauto. eauto. eauto. eauto.
      assert ((open (varF (fresh venv0)) T) = TX). rewrite wf_fresh with (ts:=env). rewrite H8. eauto. eauto.
      assert (val_type venv1 (vobj venv0 i l) TX 1). eapply v_obj. eauto. eauto.
      rewrite <- H8. eapply H4.

      rewrite wf_fresh with (ts:=env). assumption. eauto.

      (* we have everything as stp and 'just' need to convert to stp2. however we're
      working with an env that has a self binding, and the wf_env evidence needs
      the very val_tp what we're trying to construct *)

      eapply stpd2_upgrade. subst.
      rewrite <- wf_fresh with (ts:=env) (vs:=venv0).
      unfold id.
      rewrite wf_fresh with (ts:=env) (vs:=venv0) at 1.
      rewrite wf_fresh with (ts:=env) (vs:=venv0) at 3.
      eapply stp_to_stp2_cycle. eauto.
      rewrite wf_fresh with (ts:=env) (vs:=venv0).
      eauto. eauto. eauto. eauto. eauto.

      eapply not_stuck. eapply v_pack. eapply H0. eapply H3. instantiate (1:=T). simpl. subst TX. eauto. subst venv1. eapply sstpd2_extend1. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. rewrite wf_fresh with (ts:=env). subst i. eauto. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

  - Case "TLet".
    remember (tlet i e1 e2) as e. induction H0; inversion Heqe; subst.
    + remember (teval n venv0 e1) as tx.
      destruct tx as [rx|]; try solve by inversion.
      assert (res_type venv0 rx Tx) as HRX. SCase "HRX". subst. eapply IHn; eauto.
      inversion HRX as [? vx]. subst.
      assert (res_type ((i, vx) :: venv0) res T) as HR. SCase "HR". subst. eapply IHn; eauto. econstructor. eapply valtp_widen; eauto. eapply sstpd2_extend2. eapply stpd2_upgrade. eapply stp_to_stp2. eapply has_type_wf. eauto. eauto. eauto. rewrite wf_fresh with (ts:=env). eauto. eauto. eauto.
      inversion HR as [? v]. subst.
      eapply not_stuck. eapply valtp_widen. eauto. eapply sstpd2_extend1. eapply stpd2_upgrade. eapply stp_to_stp2. eauto. eauto. eauto. rewrite wf_fresh with (ts:=env). eauto. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto.

Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0.
Qed.

End FSUB.