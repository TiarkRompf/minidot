(* Full safety for DOT (WIP) *)

(* this version is based on fsub2.v *)
(* based on that, it adds self types *)

(*
TODO:
- intersection types

- stp2 trans + narrowing 
- stp/stp2 weakening and regularity
*)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Module FSUB.

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TBot   : ty           
  | TTop   : ty    
  | TFun   : ty -> ty -> ty
  | TMem   : ty -> ty -> ty
  | TSel   : id -> ty
  | TSelH  : id -> ty
  | TSelB  : id -> ty
  | TAll   : ty -> ty -> ty
  | TBind  : ty -> ty
.

Inductive tm : Type :=
  | ttrue  : tm
  | tfalse : tm
  | tvar   : id -> tm
  | ttyp   : ty -> tm
  | tapp   : tm -> tm -> tm (* f(x) *)
  | tabs   : id -> id -> tm -> tm (* \f x.y *)
  | ttapp  : tm -> tm -> tm (* f[X] *)
  | ttabs  : id -> ty -> tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
| vty   : list (id*vl) -> ty -> vl
| vbool : bool -> vl
| vabs  : list (id*vl) -> id -> id -> tm -> vl
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
| cl_fun: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TFun T1 T2)
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
    | TFun T1 T2  => TFun (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

(* sanity check *)
Example open_ex1: open (TSel 9) (TAll TBool (TFun (TSelB 1) (TSelB 0))) =
                      (TAll TBool (TFun (TSel 9) (TSelB 0))).
Proof. compute. eauto. Qed.


Fixpoint subst (U : ty) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TBool        => TBool
    | TMem T1 T2   => TMem (subst U T1) (subst U T2)
    | TFun T1 T2   => TFun (subst U T1) (subst U T2)
    | TSelB i      => TSelB i
    | TSel i       => TSel i
    | TSelH i      => if beq_nat i 0 then U else TSelH (i-1)
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TBind T2     => TBind (subst U T2)
  end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TBot         => True
    | TBool        => True
    | TMem T1 T2   => nosubst T1 /\ nosubst T2
    | TFun T1 T2   => nosubst T1 /\ nosubst T2
    | TSelB i      => True
    | TSel i       => True
    | TSelH i      => i <> 0
    | TAll T1 T2   => nosubst T1 /\ nosubst T2
    | TBind T2     => nosubst T2
  end.


Hint Unfold open.
Hint Unfold closed.


Inductive stp: tenv -> tenv -> option id -> ty -> ty -> Prop :=
| stp_topx: forall G1 GH S,
    stp G1 GH S TTop TTop
| stp_botx: forall G1 GH S,
    stp G1 GH S TBot TBot
| stp_top: forall G1 GH S T1,
    stp G1 GH S T1 T1 ->
    stp G1 GH S T1 TTop
| stp_bot: forall G1 GH S T2,
    stp G1 GH S T2 T2 ->
    stp G1 GH S TBot T2
| stp_bool: forall G1 GH S,
    stp G1 GH S TBool TBool
| stp_fun: forall G1 GH S T1 T2 T3 T4,
    stp G1 GH None T3 T1 ->
    stp G1 GH None T2 T4 ->
    stp G1 GH S (TFun T1 T2) (TFun T3 T4)             
| stp_mem: forall G1 GH S T1 T2 T3 T4,
    stp G1 GH None T3 T1 ->
    stp G1 GH None T2 T4 ->
    stp G1 GH S (TMem T1 T2) (TMem T3 T4)
| stp_sel1: forall G1 GH S TX T2 x,
    index x G1 = Some TX ->
    stp G1 GH (Some x) TX (TMem TBot T2) ->   
    stp G1 GH S (TSel x) T2
| stp_sel2: forall G1 GH S TX T1 x,
    index x G1 = Some TX ->
    stp G1 GH (Some x) TX (TMem T1 TTop) ->
    stp G1 GH S T1 (TSel x)
| stp_selx: forall G1 GH S TX x,
    index x G1 = Some TX ->
    stp G1 GH S (TSel x) (TSel x)
| stp_sela1: forall G1 GH S TX T2 x,
    indexr x GH = Some TX -> 
    stp G1 GH None TX (TMem TBot T2) ->   (* not using self name for now *)
    stp G1 GH S (TSelH x) T2
| stp_sela2: forall G1 GH S TX T1 x,
    indexr x GH = Some TX ->
    stp G1 GH None TX (TMem T1 TTop) ->   (* not using self name for now *)
    stp G1 GH S T1 (TSelH x)
| stp_selax: forall G1 GH S TX x,
    indexr x GH = Some TX  ->
    stp G1 GH S (TSelH x) (TSelH x)
| stp_all: forall G1 GH S T1 T2 T3 T4 x,
    stp G1 GH None T3 T1 ->
    x = length GH ->
    closed 1 (length GH) T2 -> (* must not accidentally bind x *)
    closed 1 (length GH) T4 -> 
    stp G1 ((0,T3)::GH) None (open (TSelH x) T2) (open (TSelH x) T4) ->
    stp G1 GH S (TAll T1 T2) (TAll T3 T4)
| stp_bindx: forall G1 GH S T1 T2 x,
    x = length GH ->
    closed 1 (length GH) T1 -> (* must not accidentally bind x *)
    closed 1 (length GH) T2 -> 
    stp G1 ((0,open (TSelH x) T1)::GH) S (open (TSelH x) T1) (open (TSelH x) T2) ->
    stp G1 GH S (TBind T1) (TBind T2)
| stp_bind1: forall G1 GH T1 T2 x,
    (* only TSel, not TSelH for now *)
    closed 1 (length GH) T2 -> 
    stp G1 GH (Some x) T1 (open (TSel x) T2) ->
    stp G1 GH (Some x) T1 (TBind T2)
| stp_bind2: forall G1 GH T1 T2 x,
    (* only TSel, not TSelH for now *)
    closed 1 (length GH) T1 -> (* must not accidentally bind x *)
    stp G1 GH (Some x) (open (TSel x) T1) T2 ->
    stp G1 GH (Some x) (TBind T1) T2
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

(* TODO *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           index x env = Some T1 ->
           stp env [] (Some x) T1 T1 ->
           has_type env (tvar x) T1
| t_typ: forall env T1,
           stp env [] None T1 T1 ->
           has_type env (ttyp T1) (TMem T1 T1)
| t_app: forall env f x T1 T2,
           has_type env f (TFun T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
| t_abs: forall env f x y T1 T2,
           has_type ((x,T1)::(f,TFun T1 T2)::env) y T2 ->
           stp env [] None (TFun T1 T2) (TFun T1 T2) ->
           fresh env <= f ->
           1+f <= x ->
           has_type env (tabs f x y) (TFun T1 T2)
| t_tapp: forall env f x T11 T12,
           has_type env f (TAll T11 T12) ->
           has_type env x T11 ->
           stp env [] None T12 T12 ->
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
           stp env [] None (TAll T1 T2) (TAll T1 T2) ->
           fresh env = x ->
           has_type env (ttabs x T1 y) (TAll T1 T2)

| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] None T1 T2 ->
           has_type env e T2
.


Definition base (v:vl): venv :=
  match v with
    | vty GX _ => GX
    | vbool _ => nil
    | vabs GX _ _ _ => GX
    | vtabs GX _ _ _ => GX
  end.

Inductive stp2: bool -> bool -> venv -> ty -> venv -> ty -> list (id*(venv*ty)) -> nat -> Prop :=
| stp2_topx: forall m G1 G2 GH n1,
    stp2 m true G1 TTop G2 TTop GH n1
| stp2_botx: forall m G1 G2 GH n1,
    stp2 m true G1 TBot G2 TBot GH n1
| stp2_top: forall m G1 G2 GH T n1,
    stp2 false  false G1 T G1 T GH n1 ->
    stp2 m true G1 T G2 TTop GH (S n1)
| stp2_bot: forall m G1 G2 GH T n1,
    stp2 false false G2 T G2 T GH n1 ->
    stp2 m true G1 TBot G2 T GH (S n1)
| stp2_bool: forall m G1 G2 GH n1,
    stp2 m true G1 TBool G2 TBool GH n1
| stp2_fun: forall m G1 G2 T1 T2 T3 T4 GH n1 n2,
    stp2 false false G2 T3 G1 T1 GH n1 ->
    stp2 false false G1 T2 G2 T4 GH n2 ->
    stp2 m true G1 (TFun T1 T2) G2 (TFun T3 T4) GH (S (n1+n2))
| stp2_mem: forall m G1 G2 T1 T2 T3 T4 GH n1 n2,
    stp2 false false G2 T3 G1 T1 GH n1 ->
    stp2 false false G1 T2 G2 T4 GH n2 ->
    stp2 m true G1 (TMem T1 T2) G2 (TMem T3 T4) GH (S (n1+n2))


(* strong version, with precise/invertible bounds *)
| stp2_strong_sel1: forall G1 G2 GX TX x T2 GH n1,
    index x G1 = Some (vty GX TX) ->
    closed 0 0 TX ->
    stp2 true true GX TX G2 T2 GH n1 ->
    stp2 true true G1 (TSel x) G2 T2 GH (S n1)

| stp2_strong_sel2: forall G1 G2 GX TX x T1 GH n1,
    index x G2 = Some (vty GX TX) ->
    closed 0 0 TX ->
    stp2 true false G1 T1 GX TX GH n1 ->
    stp2 true true G1 T1 G2 (TSel x) GH (S n1)

| stp2_strong_selx: forall G1 G2 v x1 x2 GH n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 true true G1 (TSel x1) G2 (TSel x2) GH n1
         
         
(* existing object, but imprecise type *)
| stp2_sel1: forall G1 G2 TX x T2 GH n1 v,
    index x G1 = Some v ->
    val_type (base v) v TX ->
    closed 0 0 TX ->
    stp2 false false (base v) TX G2 (TMem TBot T2) GH n1 ->
    stp2 false true G1 (TSel x) G2 T2 GH (S n1)

| stp2_sel2: forall G1 G2 TX x T1 GH n1 v,
    index x G2 = Some v ->
    val_type (base v) v TX ->           
    closed 0 0 TX ->
    stp2 false false (base v) TX G1 (TMem T1 TTop) GH n1 ->
    stp2 false true G1 T1 G2 (TSel x) GH (S n1)
         
| stp2_selx: forall G1 G2 v x1 x2 GH n1,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stp2 false true G1 (TSel x1) G2 (TSel x2) GH n1
         
(* hypothetical object *)
| stp2_sela1: forall G1 G2 GX TX x T2 GH n1,
    indexr x GH = Some (GX, TX) ->
    (* closed 0 x TX -> *)
    stp2 false false GX TX G2 (TMem TBot T2) GH n1 ->
    stp2 false true G1 (TSelH x) G2 T2 GH (S n1)

| stp2_sela2: forall G1 G2 GX TX x T1 GH n1,
    indexr x GH = Some (GX, TX) ->
    (* closed 0 x TX -> *)
    stp2 false false GX TX G2 (TMem T1 TTop) GH n1 ->
    stp2 false true G1 T1 G2 (TSelH x) GH (S n1)

         
| stp2_selax: forall G1 G2 GX TX x GH n1,
    indexr x GH = Some (GX, TX) ->
    indexr x GH = Some (GX, TX) ->
    stp2 false true G1 (TSelH x) G2 (TSelH x) GH n1


| stp2_all: forall m G1 G2 T1 T2 T3 T4 GH n1 n2, 
    stp2 false false G2 T3 G1 T1 GH n1 ->
    closed 1 (length GH) T2 -> (* must not accidentally bind x *)
    closed 1 (length GH) T4 -> 
    stp2 false false G1 (open (TSelH (length GH)) T2) G2 (open (TSelH (length GH)) T4) ((0,(G2, T3))::GH) n2 ->
    stp2 m true G1 (TAll T1 T2) G2 (TAll T3 T4) GH (S (n1+n2))

| stp2_bind: forall m G1 G2 T1 T2 GH n1, 
    closed 1 (length GH) T1 -> (* must not accidentally bind x *)
    closed 1 (length GH) T2 -> 
    stp2 false false G1 (open (TSelH (length GH)) T1) G2 (open (TSelH (length GH)) T2) ((0,(G1, open (TSelH (length GH)) T1))::GH) n1 ->
    stp2 m true G1 (TBind T1) G2 (TBind T2) GH (S n1)


| stp2_bind1: forall m G1 G2 GH T1 T2 n1,
    (* only TSel, not TSelH for now *)
    closed 1 (length GH) T1 -> (* must not accidentally bind x *)
    stp2 m true G1 (open (TSel 0) T1) G2 T2 GH n1 ->
    stp2 m true G1 (TBind T1) G2 T2 GH (S n1)
| stp2_bind2: forall m G1 G2 GH T1 T2 n1,  (* TODO: self name! fixed to 0 for now *)
    (* only TSel, not TSelH for now *)
    closed 1 (length GH) T2 -> 
    stp2 m false G1 T1 G2 (open (TSel 0) T2) GH n1 ->
    stp2 m true G1 T1 G2 (TBind T2) GH (S n1)

         
| stp2_wrapf: forall m G1 G2 T1 T2 GH n1,
    stp2 m true G1 T1 G2 T2 GH n1 ->
    stp2 m false G1 T1 G2 T2 GH (S n1)
| stp2_transf: forall m G1 G2 G3 T1 T2 T3 GH n1 n2,
    stp2 m true G1 T1 G2 T2 GH n1 ->
    stp2 m false G2 T2 G3 T3 GH n2 ->           
    stp2 m false G1 T1 G3 T3 GH (S (n1+n2))




with wf_env : venv -> tenv -> Prop := 
| wfe_nil : wf_env nil nil
| wfe_cons : forall n v t vs ts,
    val_type ((n,v)::vs) v t ->
    wf_env vs ts ->
    wf_env (cons (n,v) vs) (cons (n,t) ts)

with val_type : venv -> vl -> ty -> Prop :=
| v_ty: forall env venv tenv T1 TE,
    wf_env venv tenv -> (* T1 wf in tenv ? *)
    (exists n, stp2 true true venv (TMem T1 T1) env TE [] n)->
    val_type env (vty venv T1) TE
| v_bool: forall venv b TE,
    (exists n, stp2 true true [] TBool venv TE [] n) ->
    val_type venv (vbool b) TE
| v_abs: forall env venv tenv f x y T1 T2 TE,
    wf_env venv tenv ->
    has_type ((x,T1)::(f,TFun T1 T2)::tenv) y T2 ->
    fresh venv <= f ->
    1 + f <= x ->
    (exists n, stp2 true true venv (TFun T1 T2) env TE [] n)-> 
    val_type env (vabs venv f x y) TE
| v_tabs: forall env venv tenv x y T1 T2 TE,
    wf_env venv tenv ->
    has_type ((x,T1)::tenv) y (open (TSel x) T2) ->
    fresh venv = x ->
    (exists n, stp2 true true venv (TAll T1 T2) env TE [] n) ->
    val_type env (vtabs venv x T1 y) TE
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



Definition stpd2 b G1 T1 G2 T2 GH := exists n, stp2 false b G1 T1 G2 T2 GH n.
Definition sstpd2 b G1 T1 G2 T2 GH := exists n, stp2 true b G1 T1 G2 T2 GH n.






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
Proof. intros. exists 0. eauto. Qed.
Lemma stpd2_botx: forall G1 G2 GH,
    stpd2 true G1 TBot G2 TBot GH.
Proof. intros. exists 0. eauto. Qed.
Lemma stpd2_top: forall G1 G2 GH T,
    stpd2 false G1 T G1 T GH ->
    stpd2 true G1 T G2 TTop GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_bot: forall G1 G2 GH T,
    stpd2 false G2 T G2 T GH ->
    stpd2 true G1 TBot G2 T GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_bool: forall G1 G2 GH,
    stpd2 true G1 TBool G2 TBool GH.
Proof. intros. exists 0. eauto. Qed.
Lemma stpd2_fun: forall G1 G2 GH T11 T12 T21 T22,
    stpd2 false G2 T21 G1 T11 GH ->
    stpd2 false G1 T12 G2 T22 GH ->
    stpd2 true G1 (TFun T11 T12) G2 (TFun T21 T22) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_mem: forall G1 G2 GH T11 T12 T21 T22,
    stpd2 false G2 T21 G1 T11 GH ->
    stpd2 false G1 T12 G2 T22 GH ->
    stpd2 true G1 (TMem T11 T12) G2 (TMem T21 T22) GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_sel1: forall G1 G2 TX x T2 GH v,
    index x G1 = Some v ->
    val_type (base v) v TX ->                
    closed 0 0 TX ->
    stpd2 false (base v) TX G2 (TMem TBot T2) GH ->
    stpd2 true G1 (TSel x) G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_sel2: forall G1 G2 TX x T1 GH v,
    index x G2 = Some v ->
    val_type (base v) v TX ->                
    closed 0 0 TX ->
    stpd2 false (base v) TX G1 (TMem T1 TTop) GH ->
    stpd2 true G1 T1 G2 (TSel x) GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_selx: forall G1 G2 x1 x2 GH v,
    index x1 G1 = Some v ->
    index x2 G2 = Some v ->
    stpd2 true G1 (TSel x1) G2 (TSel x2) GH.
Proof. intros. exists 0. eauto. Qed.

Lemma stpd2_sela1: forall G1 G2 GX TX x T2 GH,
    indexr x GH = Some (GX, TX) ->
    (* closed 0 x TX -> *)
    stpd2 false GX TX G2 (TMem TBot T2) GH ->
    stpd2 true G1 (TSelH x) G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_sela2: forall G1 G2 GX TX x T1 GH,
    indexr x GH = Some (GX, TX) ->
    (* closed 0 x TX -> *)
    stpd2 false GX TX G2 (TMem T1 TTop) GH ->
    stpd2 true G1 T1 G2 (TSelH x) GH.
Proof. intros. repeat eu. eauto. Qed.

         
Lemma stpd2_selax: forall G1 G2 GX TX x GH,
    indexr x GH = Some (GX, TX) ->
    indexr x GH = Some (GX, TX) ->
    stpd2 true G1 (TSelH x) G2 (TSelH x) GH.
Proof. intros. exists 0. eauto. Qed.


Lemma stpd2_all: forall G1 G2 T1 T2 T3 T4 GH, 
    stpd2 false G2 T3 G1 T1 GH ->
    closed 1 (length GH) T2 -> 
    closed 1 (length GH) T4 -> 
    stpd2 false G1 (open (TSelH (length GH)) T2) G2 (open (TSelH (length GH)) T4) ((0,(G2, T3))::GH) ->
    stpd2 true G1 (TAll T1 T2) G2 (TAll T3 T4) GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_bind: forall G1 G2 T1 T2 GH, 
    closed 1 (length GH) T1 -> 
    closed 1 (length GH) T2 -> 
    stpd2 false G1 (open (TSelH (length GH)) T1) G2 (open (TSelH (length GH)) T2) ((0,(G1, open (TSelH (length GH)) T1))::GH) ->
    stpd2 true G1 (TBind T1) G2 (TBind T2) GH.
Proof. intros. repeat eu. eauto. Qed.

(* TODO: bind1, bind2 *)

Lemma stpd2_wrapf: forall G1 G2 T1 T2 GH,
    stpd2 true G1 T1 G2 T2 GH ->
    stpd2 false G1 T1 G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_transf: forall G1 G2 G3 T1 T2 T3 GH,
    stpd2 true G1 T1 G2 T2 GH ->
    stpd2 false G2 T2 G3 T3 GH ->           
    stpd2 false G1 T1 G3 T3 GH.
Proof. intros. repeat eu. eauto. Qed.





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
        | tabs f x y => Some (Some (vabs env f x y))
        | ttabs x T y  => Some (Some (vtabs env x T y))
        | ttyp T     => Some (Some (vty env T))
        | tapp ef ex   =>
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
                | Some (Some (vabs env2 f x ey)) =>
                  teval n ((x,vx)::(f,vabs env2 f x ey)::env2) ey
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
                | Some (Some (vabs _ _ _ _)) => Some None
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
Hint Constructors has_type.
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

Definition polyId := TAll (TMem TBot TTop) (TFun (TSelB 0) (TSelB 0)).

Example ex1: has_type [] (ttabs 0 (TMem TBot TTop) (tabs 1 2 (tvar 2))) polyId.
Proof.
  crush2.
Qed.


(* instantiate it to bool *)

Example ex2: has_type [(0,polyId)] (ttapp (tvar 0) (ttyp TBool)) (TFun TBool TBool).
Proof.
  eapply t_tapp. eapply t_sub. eapply t_var. simpl. eauto.
  eapply stp_all. eauto. eauto. crush_has_tp. crush_has_tp. crush_has_tp.
  compute.
  eapply stp_all. instantiate (1:= (TMem TBool TBool)).
    eapply stp_mem. crush2. crush2. crush2. crush2. crush2.
    eapply stp_fun. crush2. crush2.
  eapply t_sub. eapply t_typ. crush2. crush2.
  
  eapply stp_fun; crush2.
Qed.
       


(* define brand / unbrand client function *)

Definition brandUnbrand :=
  TAll (TMem TBot TTop)
       (TFun
          (TFun TBool (TSelB 0)) (* brand *)
          (TFun
             (TFun (TSelB 0) TBool) (* unbrand *)
             TBool)).

Example ex3:
  has_type []
           (ttabs 0 (TMem TBot TTop)
                  (tabs 1 2
                        (tabs 3 4
                              (tapp (tvar 4) (tapp (tvar 2) ttrue)))))
           brandUnbrand.
Proof.
  crush2.
Qed.


(* instantiating it at bool is admissible *)

Example ex4:
  has_type [(1,TFun TBool TBool);(0,brandUnbrand)]
           (tvar 0) (TAll (TMem TBool TBool) (TFun (TFun TBool TBool) (TFun (TFun TBool TBool) TBool))).
Proof.
  eapply t_sub. crush2. crush2.
Qed.

Hint Resolve ex4.

(* apply it to identity functions *)

Example ex5:
  has_type [(1,TFun TBool TBool);(0,brandUnbrand)]
           (tapp (tapp (ttapp (tvar 0) (ttyp TBool)) (tvar 1)) (tvar 1)) TBool.
Proof.
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
    | TFun T1 T2   => TFun (splice n T1) (splice n T2)
    | TSelB i      => TSelB i
    | TSel i       => TSel i
    | TSelH i      => if le_lt_dec n i  then TSelH (i+1) else TSelH i
    | TAll T1 T2   => TAll (splice n T1) (splice n T2)
    | TBind T2   => TBind (splice n T2)
  end.

Definition splicett n (V: (id*ty)) :=
  match V with
    | (x,T) => (x,(splice n T))
  end.

Lemma splice_open_permute: forall (G0:tenv) T2 n j,
(open_rec j (TSelH (n + S (length G0))) (splice (length G0) T2)) = 
(splice (length G0) (open_rec j (TSelH (n + length G0)) T2)).
Proof.
  intros G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto.
  
  case_eq (le_lt_dec (length G) i); intros E LE; simpl; eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  case_eq (le_lt_dec (length G) (n + length G)); intros EL LE.
  assert (n + S (length G) = n + length G + 1). omega.
  rewrite H. eauto.
  omega.
Qed.

Lemma indexr_splice_hi: forall G0 G2 x0 x v1 T,
    indexr x0 (G2 ++ G0) = Some T ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (splicett (length G0)) (G2 ++ (x, v1) :: G0)) = Some (splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. omega.
  - simpl in H. destruct a.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite map_length. rewrite app_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma indexr_splice_lo0: forall G0 G2 x0 (T:ty),
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 G0 = Some T.
Proof. admit. Qed.

Lemma indexr_splice_lo1: forall G0 x0 (T:ty) f,
    indexr x0 G0 = Some T ->
    map (splicett f) G0 = G0 ->
    indexr x0 G0 = Some (splice f T).
Proof. admit. Qed.

Lemma indexr_extend_mult: forall G0 G2 x0 (T:ty),
    indexr x0 G0 = Some T ->
    indexr x0 (G2++G0) = Some T.
Proof. admit. Qed.


Lemma indexr_splice_lo: forall G0 G2 x0 x v1 T f,
    indexr x0 (G2 ++ G0) = Some T ->
    map (splicett f) G0 = G0 ->
    x0 < length G0 ->
    indexr x0 (map (splicett f) (G2 ++ (x, v1) :: G0)) = Some (splice f T).
Proof.
  intros.
  assert (indexr x0 G0 = Some T). eapply indexr_splice_lo0; eauto.
  assert (indexr x0 (map (splicett f) G0) = Some (splice f T)).
  rewrite H0. eapply indexr_splice_lo1. eauto. eauto.
  rewrite map_app. simpl.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.  


Lemma stp_splice : forall GX G0 G1 T1 T2 S x v1,
   stp GX (G1++G0) S T1 T2 ->
   map (splicett (length G0)) G0 = G0 ->                  
   stp GX (map (splicett (length G0)) (G1++(x,v1)::G0)) S (splice (length G0) T1) (splice (length G0) T2).
Proof.
  intros GX G0 G1 T1 T2 S x v1 H. remember (G1++G0) as G. remember S as S'.
  revert G0 G1 HeqG S HeqS'.
  induction H; intros; subst GH; simpl; eauto.
  - admit.
  - admit.
  - Case "sela1".
    case_eq (le_lt_dec (length G0) x0); intros E LE.
    + eapply stp_sela1. eapply indexr_splice_hi with (T:=TX). eauto. eauto.
      eapply IHstp. eauto. eauto.
    + eapply stp_sela1. eapply indexr_splice_lo with (T:=TX). eauto. eauto. eauto.
      eapply IHstp. eauto. eauto.
  - Case "sela2". admit.
  - Case "selax".
    case_eq (le_lt_dec (length G0) x0); intros E LE.
    + eapply stp_selax. eapply indexr_splice_hi with (T:=TX). eauto. eauto.
    + eapply stp_selax. eapply indexr_splice_lo with (T:=TX). eauto. eauto. eauto.
  - Case "all".
    eapply stp_all.
    eapply IHstp1. eauto. eauto. eauto.
    admit. (* closed *) 
    admit. (* closed *)

    specialize IHstp2 with (G3:=G0) (G4:=(0, T3) :: G2).
    simpl in IHstp2. rewrite map_length. rewrite app_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x0.
    rewrite app_length in IHstp2. simpl in IHstp2.
    eapply IHstp2. eauto. eauto.
  - Case "bind". admit.
Qed.




Lemma stp_extend : forall G1 GH T1 T2 x v1,
                       stp G1 GH T1 T2 ->
                       stp G1 ((x,v1)::GH) T1 T2.
Proof.
  (* use stp_splice: we need to have that env and types are well-formed *)
  admit.
Qed.


Lemma stp2_extend2 : forall x v1 G1 G2 T1 T2 H s m n1,
                       stp2 s m G1 T1 G2 T2 H n1 ->
                       fresh G2 <= x ->
                       stp2 s m G1 T1 ((x,v1)::G2) T2 H n1.
Proof. admit. Qed.

Lemma stp2_extend1 : forall x v1 G1 G2 T1 T2 H s m n1,
                       stp2 s m G1 T1 G2 T2 H n1 ->
                       fresh G1 <= x ->
                       stp2 s m ((x,v1)::G1) T1 G2 T2 H n1.
Proof. admit. Qed.

Lemma stp2_extendH : forall x v1 G1 G2 T1 T2 H s m n1,
                       stp2 s m G1 T1 G2 T2 H n1 ->
                       stp2 s m G1 T1 G2 T2 ((x,v1)::H) n1.
Proof.
  admit. (* (NOT) TODO (NOW): use splice *)
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


Lemma stp2_reg2 : forall G1 G2 T1 T2 H s m n1,
                       stp2 s m G1 T1 G2 T2 H n1 ->
                       stp2 s m G2 T2 G2 T2 H n1.
Proof. admit. Qed.

Lemma stp2_reg1 : forall G1 G2 T1 T2 H s m n1,
                       stp2 s m G1 T1 G2 T2 H n1 ->
                       stp2 s m G1 T1 G1 T1 H n1.
Proof. admit. Qed.


Lemma stp2_closed2 : forall G1 G2 T1 T2 H s m n1,
                       stp2 s m G1 T1 G2 T2 H n1 ->
                       closed 0 (length H) T2.
Proof. admit. Qed.

Lemma stp2_closed1 : forall G1 G2 T1 T2 H s m n1,
                       stp2 s m G1 T1 G2 T2 H n1 ->
                       closed 0 (length H) T1.
Proof. admit. Qed.

(* stpd2 variants below *)

Lemma stpd2_extend2 : forall x v1 G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       fresh G2 <= x ->
                       stpd2 m G1 T1 ((x,v1)::G2) T2 H.
Proof. admit. Qed.

Lemma stpd2_extend1 : forall x v1 G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       fresh G1 <= x ->
                       stpd2 m ((x,v1)::G1) T1 G2 T2 H.
Proof. admit. Qed.

Lemma stpd2_extendH : forall x v1 G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       stpd2 m G1 T1 G2 T2 ((x,v1)::H).
Proof. admit. Qed.

Lemma stpd2_extendH_mult : forall G1 G2 T1 T2 H H2 m,
                       stpd2 m G1 T1 G2 T2 H->
                       stpd2 m G1 T1 G2 T2 (H2++H).
Proof. admit. Qed.

Lemma stpd2_extendH_mult0 : forall G1 G2 T1 T2 H2 m,
                       stpd2 m G1 T1 G2 T2 [] ->
                       stpd2 m G1 T1 G2 T2 H2.
Proof. admit. Qed.


Lemma stpd2_reg2 : forall G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       stpd2 m G2 T2 G2 T2 H.
Proof. admit. Qed.

Lemma stpd2_reg1 : forall G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       stpd2 m G1 T1 G1 T1 H.
Proof. admit. Qed.


Lemma stpd2_closed2 : forall G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       closed 0 (length H) T2.
Proof. admit. Qed.

Lemma stpd2_closed1 : forall G1 G2 T1 T2 H m,
                       stpd2 m G1 T1 G2 T2 H ->
                       closed 0 (length H) T1.
Proof. admit. Qed.


(* sstpd2 variants below *)

Lemma sstpd2_extend2 : forall x v1 G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       fresh G2 <= x ->
                       sstpd2 m G1 T1 ((x,v1)::G2) T2 H.
Proof. admit. Qed.

Lemma sstpd2_extend1 : forall x v1 G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       fresh G1 <= x ->
                       sstpd2 m ((x,v1)::G1) T1 G2 T2 H.
Proof. admit. Qed.

Lemma sstpd2_extendH : forall x v1 G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       sstpd2 m G1 T1 G2 T2 ((x,v1)::H).
Proof. admit. Qed.

Lemma sstpd2_extendH_mult : forall G1 G2 T1 T2 H H2 m,
                       sstpd2 m G1 T1 G2 T2 H->
                       sstpd2 m G1 T1 G2 T2 (H2++H).
Proof. admit. Qed.

Lemma sstpd2_extendH_mult0 : forall G1 G2 T1 T2 H2 m,
                       sstpd2 m G1 T1 G2 T2 [] ->
                       sstpd2 m G1 T1 G2 T2 H2.
Proof. admit. Qed.

Lemma sstpd2_reg2 : forall G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       sstpd2 m G2 T2 G2 T2 H.
Proof. admit. Qed.

Lemma sstpd2_reg1 : forall G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       sstpd2 m G1 T1 G1 T1 H.
Proof. admit. Qed.

Lemma sstpd2_closed2 : forall G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       closed 0 (length H) T2.
Proof. admit. Qed.

Lemma sstpd2_closed1 : forall G1 G2 T1 T2 H m,
                       sstpd2 m G1 T1 G2 T2 H ->
                       closed 0 (length H) T1.
Proof. admit. Qed.




Lemma valtp_extend : forall vs v x v1 T,
                       val_type vs v T ->
                       fresh vs <= x ->
                       val_type ((x,v1)::vs) v T.
Proof.
  intros. induction H; eauto; econstructor; eauto; eapply sstpd2_extend2; eauto.
Qed.


Lemma index_safe_ex: forall H1 G1 TF i,
             wf_env H1 G1 ->
             index i G1 = Some TF ->
             exists v, index i H1 = Some v /\ val_type H1 v TF.
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
         assert (exists v0, index i vs = Some v0 /\ val_type vs v0 TF) as HI. eapply IHwf_env. eauto.
         inversion HI as [v0 HI1]. inversion HI1.
         eexists. econstructor. eapply index_extend; eauto. eapply valtp_extend; eauto.
     + SSCase "bad".
       rewrite E1 in H3. inversion H3.
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

  
Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.



Lemma stpd2_trans_aux: forall n, forall G1 G2 G3 T1 T2 T3 H n1,
  stp2 false false G1 T1 G2 T2 H n1 -> n1 < n ->
  stpd2 false G2 T2 G3 T3 H ->
  stpd2 false G1 T1 G3 T3 H.
Proof.
  intros n. induction n; intros; try omega; repeat eu; subst; inversion H0.
  - Case "wrapf". eapply stpd2_transf; eauto.
  - Case "transf". eapply stpd2_transf. eauto. eapply IHn. eauto. omega. eauto.
Qed.

(*
Lemma sstpd2_trans_axiom: forall n, forall G1 G2 G3 T1 T2 T3 H n1,
  stp2 true false G1 T1 G2 T2 H n1 -> n1 < n ->
  sstpd2 false G2 T2 G3 T3 H ->
  sstpd2 false G1 T1 G3 T3 H.
Proof.
  intros n. induction n; intros; try omega; repeat eu; subst; inversion H0.
  - Case "wrapf". eexists. eapply stp2_transf; eauto.
  - Case "transf". admit. (*eexists. eapply stp2_transf. eauto. ep. eapply IHn. eauto. omega. eauto. eauto. *)
Qed.
*)


Lemma stpd2_trans: forall G1 G2 G3 T1 T2 T3 H,
  stpd2 false G1 T1 G2 T2 H ->
  stpd2 false G2 T2 G3 T3 H ->
  stpd2 false G1 T1 G3 T3 H.
Proof. intros. repeat eu. eapply stpd2_trans_aux; eauto. Qed.

(* used in trans -- need to generalize interface for induction *)

Lemma stpd2_narrow: forall x G1 G2 G3 G4 T1 T2 T3 T4 H,
  stpd2 false G1 T1 G2 T2 ((x,(G1,T1))::H) -> (* careful about H! *)
  stpd2 false G3 T3 G4 T4 ((x,(G2,T2))::H) ->
  stpd2 false G3 T3 G4 T4 ((x,(G1,T1))::H).
Proof. admit. Qed.


Lemma sstpd2_trans_aux: forall n, forall m G1 G2 G3 T1 T2 T3 n1,
  stp2 true m G1 T1 G2 T2 nil n1 -> n1 < n ->
  sstpd2 true G2 T2 G3 T3 nil ->
  sstpd2 true G1 T1 G3 T3 nil.
Proof.
  intros n. induction n; intros; try omega. eu.
  inversion H.
  - Case "topx". subst. inversion H1.
    + SCase "topx". eexists. eauto.
    + SCase "top". eexists. eauto.
    + SCase "sel2". eexists. eapply stp2_strong_sel2. eauto. eauto. eapply stp2_transf. eauto. eauto.
  - Case "botx". subst. inversion H1.
    + SCase "botx". eexists. eauto.
    + SCase "top". eexists. eauto.
    + SCase "?". eexists. eauto.
    + SCase "sel2". eexists. eapply stp2_strong_sel2. eauto. eauto. eapply stp2_transf. eauto. eauto.
  - Case "top". subst. inversion H1.
    + SCase "topx". eexists. eauto.
    + SCase "top". eexists. eauto.
    + SCase "sel2". eexists. eapply stp2_strong_sel2. eauto. eauto. eapply stp2_transf. eauto. eauto.
  - Case "bot". admit. 
  - Case "bool". subst. inversion H1.
    + SCase "top". eexists. eauto.
    + SCase "bool". eexists. eauto.
    + SCase "sel2". eexists. eapply stp2_strong_sel2. eauto. eauto. eapply stp2_transf. eauto. eauto.
  - Case "fun". subst. inversion H1.
    + SCase "top". eexists. eapply stp2_top. subst. eapply stp2_wrapf. eapply stp2_fun. eapply stp2_reg2. eauto. eapply stp2_reg1. eauto.
    + SCase "fun".
      admit.
      (* eexists. eapply stp2_fun. ep. eapply stpd2_trans. eauto. eauto. destruct EEX. eauto. *)
    + SCase "sel2". eexists. eapply stp2_strong_sel2. eauto. eauto. eapply stp2_transf. eauto. eauto.
  - Case "mem". subst. inversion H1.
    + SCase "top". admit.
    + SCase "mem". admit.
    + SCase "sel2". eexists. eapply stp2_strong_sel2. eauto. eauto. eapply stp2_transf. eauto. eauto.
  - Case "ssel1".
    assert (sstpd2 true GX TX G3 T3 []). eapply IHn. eauto. omega. eexists. eapply H1. 
    eu. eexists. eapply stp2_strong_sel1. eauto. eauto. eauto.
  - Case "ssel2". subst. inversion H1.
    + SCase "top". admit.
    + SCase "ssel1".  (* interesting one *)
      subst. rewrite H6 in H2. inversion H2. subst.
      eapply IHn. eapply H4. omega. eexists. eauto.
    + SCase "ssel2".
      eexists. eapply stp2_strong_sel2. eauto. eauto. eapply stp2_transf. eauto. eauto.
    + SCase "sselx".
      subst. rewrite H2 in H6. inversion H6. subst.
      eexists. eapply stp2_strong_sel2. eauto. eauto. eauto.
  - Case "sselx". subst. inversion H1.
    + SCase "top". admit.
    + SCase "ssel1".
      subst. rewrite H5 in H3. inversion H3. subst.
      eexists. eapply stp2_strong_sel1. eauto. eauto. eauto.
    + SCase "ssel2". eexists. eapply stp2_strong_sel2. eauto. eauto. eapply stp2_transf. eauto. eauto.
    + SCase "sselx".
      subst. rewrite H5 in H3. inversion H3. subst.
      eexists. eapply stp2_strong_selx. eauto. eauto.
  - Case "all". subst. inversion H1.
    + SCase "top". admit.
    + SCase "ssel2".
      eexists. eapply stp2_strong_sel2. eauto. eauto. eapply stp2_transf. eauto. eauto.
    + SCase "all".
      subst.
      assert (stpd2 false G3 T7 G1 T0 []). eapply stpd2_trans. eauto. eauto.
      assert (stpd2 false G1 (open (TSelH (length ([]:aenv))) T4)
                          G3 (open (TSelH (length ([]:aenv))) T8)
                          [(0, (G3, T7))]).
        eapply stpd2_trans. eapply stpd2_narrow. eapply stpd2_extendH. eexists. eapply H8. eauto. eauto. 
      repeat eu. eexists. eapply stp2_all. eauto. eauto. eauto. eauto.

  - Case "bind". subst. inversion H1.
    + SCase "top". admit.
    + SCase "ssel2".
      eexists. eapply stp2_strong_sel2. eauto. eauto. eapply stp2_transf. eauto. eauto.
    + SCase "bind".
      subst.
      assert (stpd2 false G1 (open (TSelH (length ([]:aenv))) T0)
                          G3 (open (TSelH (length ([]:aenv))) T2)
                          [(0, (G1, open (TSelH (length ([]:aenv))) T0))]).
        eapply stpd2_trans. eauto. eapply stpd2_narrow. eexists. eapply H4. eauto. 
      repeat eu. eexists. eapply stp2_bind. eauto. eauto. eauto. 

  - Case "wrapf". subst. eapply IHn. eapply H2. omega. eexists. eauto.
  - Case "transf". subst. eapply IHn. eapply H2. omega. eapply IHn. eapply H3. omega. eexists. eauto.
Grab Existential Variables.
apply 0. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma sstpd2_trans: forall G1 G2 G3 T1 T2 T3,
  sstpd2 true G1 T1 G2 T2 nil ->
  sstpd2 true G2 T2 G3 T3 nil ->
  sstpd2 true G1 T1 G3 T3 nil.
Proof. intros. repeat eu. eapply sstpd2_trans_aux; eauto. eexists. eauto. Qed.


Lemma sstpd2_untrans_aux: forall n, forall G1 G2 T1 T2 n1,
  stp2 true false G1 T1 G2 T2 nil n1 -> n1 < n ->
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



Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  sstpd2 true H1 T1 H2 T2 [] ->
  val_type H2 vf T2.
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

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.

Lemma invert_typ: forall venv vx T1 T2,
  val_type venv vx (TMem T1 T2) ->
  exists GX TX,
    vx = (vty GX TX) /\
    stpd2 false venv T1 GX TX [] /\
    stpd2 false GX TX venv T2 [].
Proof.
  intros. inversion H; ev; try solve by inversion. inversion H1.
  subst.
  assert (stpd2 false venv0 T1 venv1 T0 []) as E1. eauto.
  assert (stpd2 false venv1 T0 venv0 T2 []) as E2. eauto.
  repeat eu. repeat eexists; eauto. 
Qed.



Lemma stpd2_to_sstpd2_aux: forall n, forall G1 G2 T1 T2 m n1,
  stp2 false m G1 T1 G2 T2 nil n1 -> n1 < n ->
  sstpd2 m G1 T1 G2 T2 nil.
Proof.
  intros n. induction n; intros; try omega.
  inversion H.
  - Case "botx". eexists. eauto.
  - Case "topx". eexists. eauto.
  - Case "bot". eexists. eauto.
  - Case "top". eexists. eauto.
  - Case "bool". eexists. eauto.
  - Case "fun". eexists. eapply stp2_fun. eauto. eauto.
  - Case "mem". eexists. eapply stp2_mem. eauto. eauto.
  - Case "sel1".
    (* TODO: val_type should take size bound parameter (if we do it like this) *)
    (* alternative: sstp2_mem returns sstp2 *)
    eapply IHn in H4. eapply sstpd2_untrans in H4. eapply valtp_widen with (2:=H4) in H2.
    eapply invert_typ in H2. ev. eu. eu. subst.
    assert (x3 < n). admit. (* this is safe, because the val_tp was part of our argument *)
    assert (x2 < n). admit.
    assert (closed 0 (length ([]:aenv)) x1). eapply stp2_closed2; eauto.
    assert (sstpd2 true x0 x1 G2 T2 []). eapply sstpd2_untrans. eapply IHn. eauto. omega.
    eu. eexists. eapply stp2_strong_sel1. eauto. eauto. eauto. omega.
  - Case "sel2".
    eapply IHn in H4. eapply sstpd2_untrans in H4. eapply valtp_widen with (2:=H4) in H2.
    eapply invert_typ in H2. ev. eu. eu. subst.
    assert (x3 < n). admit. (* this is safe, because the val_tp was part of our argument *)
    assert (x2 < n). admit.
    assert (closed 0 (length ([]:aenv)) x1). eapply stp2_closed2; eauto.
    assert (sstpd2 false G1 T1 x0 x1 []). eapply IHn. eauto. omega.
    eu. eexists. eapply stp2_strong_sel2. eauto. eauto. eauto. omega.
  - Case "selx".
    eexists. eapply stp2_strong_selx. eauto. eauto. 
  - Case "selh1". inversion H1. 
  - Case "selh2". inversion H1. 
  - Case "selhx". inversion H1.
  - Case "all". eexists. eapply stp2_all. eauto. eauto. eauto. eauto.
  - Case "bind". eexists. eapply stp2_bind. eauto. eauto. eauto.
  - Case "wrapf". eapply IHn in H1. eu. eexists. eapply stp2_wrapf. eauto. omega.
  - Case "transf". eapply IHn in H1. eapply IHn in H2. eu. eu. eexists.
    eapply stp2_transf. eauto. eauto. omega. omega.
    Grab Existential Variables.
    apply 0. apply 0. apply 0. apply 0.
Qed.



Lemma stpd2_to_sstpd2: forall G1 G2 T1 T2 m,
  stpd2 m G1 T1 G2 T2 nil ->
  sstpd2 m G1 T1 G2 T2 nil.
Proof. intros. repeat eu. eapply stpd2_to_sstpd2_aux; eauto. Qed.


Lemma stpd2_upgrade: forall G1 G2 T1 T2,
  stpd2 false G1 T1 G2 T2 nil ->
  sstpd2 true G1 T1 G2 T2 nil.
Proof.
  intros.
  eapply sstpd2_untrans. eapply stpd2_to_sstpd2. eauto.
Qed.

(* not essential *)
Lemma sstpd2_downgrade: forall G1 G2 T1 T2 H,
  sstpd2 true G1 T1 G2 T2 H ->
  stpd2 false G1 T1 G2 T2 H.
Proof.
  admit.
Qed.




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
Lemma stp_substitute: forall T1 T2 GX GH,
   stp GX GH T1 T2 ->
   forall GH0 TX0,
     GH = (GH0 ++ [(0,TMem TBot TX0)]) ->
     closed 0 0 TX0 ->
     stp GX (map (substt TX0) GH0) TX0 TX0 ->
     stp GX (map (substt TX0) GH0)
         (subst TX0 T1)
         (subst TX0 T2).
Proof.
  intros T1 T2 GX GH H.
  induction H.
  - Case "top". eauto.
  - Case "bot". eauto.
  - Case "bool". eauto.
  - Case "fun". intros. simpl. eapply stp_fun. eauto. eauto.
  - Case "mem". intros. simpl. eapply stp_mem. eauto. eauto.
  - Case "sel1". admit.
  - Case "sel2". admit.
  - Case "selx". admit.
  - Case "sela1". intros GH0 TX1 ? ? ?. simpl.
    subst GH. specialize (indexr_subst _ x (TMem TBot TX1) _ H). intros. 
    destruct H1; destruct H1.
    + subst. simpl.
      specialize (IHstp GH0 TX1). 
      assert (subst TX1 TX1 = TX1). eapply closed_no_subst; eauto.
      (* rewrite H1 in IHstp. *)
      eapply IHstp. eauto. eauto. eauto.
    + subst. simpl.
      assert (beq_nat x 0 = false). eapply beq_nat_false_iff; omega. rewrite H5. simpl.
      eapply stp_sela1. eapply H4. eapply IHstp. eauto. eauto. eauto.
  - Case "sela2". admit. 
  - Case "selax". intros GH0 TX ? ? ?. simpl.
    subst GH. specialize (indexr_subst _ x TX TL TU H). intros.
    destruct H0; destruct H0.
    + subst. simpl. eauto.
    + subst. simpl. assert (beq_nat x 0 = false). eapply beq_nat_false_iff. omega. rewrite H4. eapply stp_selax. eauto.
  - Case "all".
    intros GH0 TX ? ? ?.
    simpl. eapply stp_all.
    + eapply IHstp1; eauto.
    + rewrite map_length. eauto.
    + rewrite map_length. eapply closed_subst. subst GH.
      rewrite app_length in H1. simpl in H1. eauto.
      eapply closed_upgrade_free; eauto. omega.
    + rewrite map_length. eapply closed_subst. subst GH.
      rewrite app_length in H2. simpl in H2. eauto.
      eapply closed_upgrade_free; eauto. omega.
    + specialize IHstp2 with (GH0:=(0, T3)::GH0) (TX:=TX).
      subst GH. simpl in IHstp2.
      unfold open. unfold open in IHstp2.
      subst x.
      rewrite open_subst_commute with (n:=0).
      rewrite open_subst_commute with (n:=0).
      rewrite app_length in IHstp2. simpl in IHstp2.
      eapply IHstp2; eauto. eapply stp_extend; eauto.
      eauto. eauto.
Qed.
*)

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


Definition compat (GX:venv) (TX: ty) (V: option vl) (G1:venv) (T1:ty) (T1':ty) :=
  (exists x1 v, index x1 G1 = Some v /\ V = Some v /\ GX = base v /\ val_type GX v TX /\ T1' = (subst (TSel x1) T1)) \/
  (*  (G1 = GX /\ T1' = (subst TX T1)) \/ *)   (* this is doesn't work for DOT *)
  (* ((forall TA TB, TX <> TMem TA TB) /\ T1' = subst TTop T1) \/ *)(* can remove all term-only bindings -- may not be necessary after all since it applies nosubst *)
  (closed_rec 0 0 T1 /\ T1' = T1) \/ (* this one is for convenience: redundant with next *)
  (nosubst T1 /\ T1' = subst TTop T1).


Definition compat2 (GX:venv) (TX: ty) (V: option vl) (p1:id*(venv*ty)) (p2:id*(venv*ty)) :=
  match p1, p2 with
      (n1,(G1,T1)), (n2,(G2,T2)) => n1=n2(*+1 disregarded*) /\ G1 = G2 /\ compat GX TX V G1 T1 T2
  end.



Lemma indexr_compat_miss0: forall GH GH' GX TX V (GXX:venv) (TXX:ty) n,
      Forall2 (compat2 GX TX V) GH GH' ->
      indexr (n+1) (GH ++ [(0,(GX, TX))]) = Some (GXX,TXX) ->
      exists TXX', indexr n GH' = Some (GXX,TXX') /\ compat GX TX V GXX TXX TXX'.
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



Lemma compat_top: forall GX TX V G1 T1',
  compat GX TX V G1 TTop T1' -> closed 0 0 TX -> T1' = TTop.
Proof.
  intros ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto. 
Qed.

Lemma compat_bot: forall GX TX V G1 T1',
  compat GX TX V G1 TBot T1' -> closed 0 0 TX -> T1' = TBot.
Proof.
  intros ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.


Lemma compat_bool: forall GX TX V G1 T1',
  compat GX TX V G1 TBool T1' -> closed 0 0 TX -> T1' = TBool.
Proof.
  intros ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.

Lemma compat_mem: forall GX TX V G1 T1 T2 T1',
    compat GX TX V G1 (TMem T1 T2) T1' ->
    closed 0 0 TX -> 
    exists TA TB, T1' = TMem TA TB /\
                  compat GX TX V G1 T1 TA /\
                  compat GX TX V G1 T2 TB.
Proof.
  intros ? ? ? ? ? ? ? CC CLX. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. + left. repeat eexists; eauto.
  - ev. repeat eexists; eauto. + right. left. inversion H. eauto. + right. left. inversion H. eauto.
  - ev. repeat eexists; eauto. + right. right. inversion H. eauto. + right. right. inversion H. eauto.
Qed.


Lemma compat_mem_fwd2: forall GX TX V G1 T2 T2',
    compat GX TX V G1 T2 T2' ->
    compat GX TX V G1 (TMem TBot T2) (TMem TBot T2').
Proof.
  intros. repeat destruct H as [|H].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. rewrite H3. eauto.
  - ev. repeat eexists; eauto. + right. left. subst. eauto. 
  - ev. repeat eexists; eauto. + right. right. subst. simpl. eauto.
Qed.

Lemma compat_mem_fwd1: forall GX TX V G1 T2 T2',
    compat GX TX V G1 T2 T2' ->
    compat GX TX V G1 (TMem T2 TTop) (TMem T2' TTop).
Proof.
  intros. repeat destruct H as [|H].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. rewrite H3. eauto.
  - ev. repeat eexists; eauto. + right. left. subst. eauto. 
  - ev. repeat eexists; eauto. + right. right. subst. simpl. eauto.
Qed.

Lemma compat_mem_fwdx: forall GX TX V G1 T2 T2',
    compat GX TX V G1 T2 T2' ->
    compat GX TX V G1 (TMem T2 T2) (TMem T2' T2').
Proof.
  intros. repeat destruct H as [|H].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. rewrite H3. eauto.
  - ev. repeat eexists; eauto. + right. left. subst. eauto. 
  - ev. repeat eexists; eauto. + right. right. subst. simpl. eauto.
Qed.


Lemma compat_fun: forall GX TX V G1 T1 T2 T1',
    compat GX TX V G1 (TFun T1 T2) T1' ->
    closed_rec 0 0 TX -> 
    exists TA TB, T1' = TFun TA TB /\
                  compat GX TX V G1 T1 TA /\
                  compat GX TX V G1 T2 TB.
Proof.
  intros ? ? ? ? ? ? ? CC CLX. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto. + left. repeat eexists; eauto. + left. repeat eexists; eauto.
  - ev. repeat eexists; eauto. + right. left. inversion H. eauto. + right. left. inversion H. eauto.
  - ev. repeat eexists; eauto. + right. right. inversion H. eauto. + right. right. inversion H. eauto.
Qed.


Lemma compat_sel: forall GX TX V G1 T1' (GXX:venv) (TXX:ty) x v,
    compat GX TX V G1 (TSel x) T1' ->
    closed 0 0 TX ->
    closed 0 0 TXX ->
    index x G1 = Some v ->
    val_type GXX v TXX ->
    exists TXX', T1' = (TSel x) /\ TXX' = TXX /\ compat GX TX V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? CC CL CL1 IX. repeat destruct CC as [|CC].
  - ev. repeat eexists; eauto. + right. left. simpl in H0. eauto.
  - ev. repeat eexists; eauto. + right. left. simpl in H0. eauto.
  - ev. repeat eexists; eauto. + right. left. simpl in H0. eauto.
Qed.



Lemma compat_selh: forall GX TX V G1 T1' GH0 GH0' (GXX:venv) (TXX:ty) x,
    compat GX TX V G1 (TSelH x) T1' ->
    closed 0 0 TX ->
    indexr x (GH0 ++ [(0, (GX, TX))]) = Some (GXX, TXX) ->
    Forall2 (compat2 GX TX V) GH0 GH0' ->
    (x = 0 /\ GXX = GX /\ TXX = TX) \/
    exists TXX',
      x > 0 /\ T1' = TSelH (x-1) /\
      indexr (x-1) GH0' = Some (GXX, TXX') /\
      compat GX TX V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? CC CL IX FA. 
  unfold id in x.
  case_eq (beq_nat x 0); intros E.
  - left. assert (x = 0). eapply beq_nat_true_iff. eauto. subst x. rewrite indexr_hit0 in IX. inversion IX. eauto.
  - right. assert (x <> 0). eapply beq_nat_false_iff. eauto.
    assert (x > 0). omega. remember (x-1) as y. assert (x = y+1) as Y. omega. subst x.
    eapply (indexr_compat_miss0 GH0 GH0' _ _ _ _ _ _ FA) in IX.
    repeat destruct CC as [|CC].
    + ev. simpl in H7. rewrite E in H7. rewrite <-Heqy in H7. eexists. eauto.
    + ev. inversion H1. omega. 
    + ev. simpl in H4. rewrite E in H4. rewrite <-Heqy in H4. eexists. eauto.
Qed.


Lemma compat_all: forall GX TX V G1 T1 T2 T1' n,
    compat GX TX V G1 (TAll T1 T2) T1' ->
    closed 0 0 TX ->
    closed 1 (n+1) T2 ->
    exists TA TB, T1' = TAll TA TB /\
                  closed 1 n TB /\
                  compat GX TX V G1 T1 TA /\
                  compat GX TX V G1 (open_rec 0 (TSelH (n+1)) T2) (open_rec 0 (TSelH n) TB).
Proof.
  intros ? ? ? ? ? ? ? ? CC CLX CL2. repeat destruct CC as [|CC].

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


Lemma compat_bind: forall GX TX V G1 T2 T1' n,
    compat GX TX V G1 (TBind T2) T1' ->
    closed 0 0 TX ->
    closed 1 (n+1) T2 ->
    exists TB, T1' = TBind TB /\
                  closed 1 n TB /\
                  compat GX TX V G1 (open_rec 0 (TSelH (n+1)) T2) (open_rec 0 (TSelH n) TB).
Proof.
  intros ? ? ? ? ? ? ? CC CLX CL2. repeat destruct CC as [|CC].

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


Lemma stp2_substitute: forall m G1 G2 T1 T2 GH n1,
   stp2 false m G1 T1 G2 T2 GH n1 ->
   forall GH0 GH0' GX TX T1' T2' V,
     GH = (GH0 ++ [(0,(GX, TX))]) ->
     closed 0 0 TX ->
     compat GX TX V G1 T1 T1' ->
     compat GX TX V G2 T2 T2' ->
     Forall2 (compat2 GX TX V) GH0 GH0' ->
     stpd2 m G1 T1' G2 T2' GH0'.
Proof.
  intros m G1 G2 T1 T2 GH n1 H. remember false as flag.
  induction H; inversion Heqflag.
  - Case "topx".
    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    eapply compat_top in IX1.
    eapply compat_top in IX2.
    subst. eapply stpd2_topx. eauto. eauto.
    
  - Case "botx".
    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    eapply compat_bot in IX1.
    eapply compat_bot in IX2.
    subst. eapply stpd2_botx. eauto. eauto.
    
  - Case "top".
    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    eapply compat_top in IX2.
    subst. eapply stpd2_top; eauto. eauto. 
    
  - Case "bot".
    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    eapply compat_bot in IX1.
    subst. eapply stpd2_bot; eauto. eauto.
    
  - Case "bool".
    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    eapply compat_bool in IX1.
    eapply compat_bool in IX2.
    subst. eapply stpd2_bool; eauto. eauto. eauto. 
    
  - Case "fun".
    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    eapply compat_fun in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_fun in IX2. repeat destruct IX2 as [? IX2].
    subst. eapply stpd2_fun; eauto. eauto. eauto. 

  - Case "mem".
    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    eapply compat_mem in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_mem in IX2. repeat destruct IX2 as [? IX2].
    subst. eapply stpd2_mem; eauto. eauto. eauto. 
                                
  - Case "sel1". 
    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX V G1 T1' (base v) TX) in IX1. repeat destruct IX1 as [? IX1].

    assert (compat GXX TXX V (base v) TX TX) as CPX. right. left. eauto.

    subst.
    eapply stpd2_sel1. eauto. eauto. eauto.
    eapply IHstp2. eauto. eauto. eauto. eauto.
    eauto. eapply compat_mem_fwd2. eauto.
    eauto. eauto. eauto. eauto. eauto.

  - Case "sel2". 
    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX V G2 T2' (base v) TX) in IX2. repeat destruct IX2 as [? IX2].

    assert (compat GXX TXX V (base v) TX TX) as CPX. right. left. eauto.

    subst.
    eapply stpd2_sel2. eauto. eauto. eauto.
    eapply IHstp2. eauto. eauto. eauto. eauto.
    eauto. eapply compat_mem_fwd1. eauto.
    eauto. eauto. eauto. eauto. eauto.

  - Case "selx". 

    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (T1' = TSel x1). destruct IX1. ev. eauto. destruct H3. ev. auto. ev. eauto.
    assert (T2' = TSel x2). destruct IX2. ev. eauto. destruct H4. ev. auto. ev. eauto.
    
    subst.
    eapply stpd2_selx. eauto. eauto. 

  - Case "sela1".
    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX V G1 (TSelH x) T1') as IXX. eauto.
    
    eapply (compat_selh GXX TXX V G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].
    
    destruct IX1. 
    + SCase "x = 0".
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl.
        eapply stpd2_sel1. eauto. eauto. eauto.
        eapply IHstp2. eauto. eauto. eauto. eauto. right. left. auto.
        eapply compat_mem_fwd2. eauto.
        eauto.
      * subst. inversion H4. omega.
      * subst. destruct H4. eauto.
    + SCase "x > 0".
      ev. subst.
      eapply stpd2_sela1. eauto. eapply IHstp2; eauto. eauto. eapply compat_mem_fwd2. eauto.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.
      
  - Case "sela2". admit.
    
  - Case "selax".

    intros GH0 GH0' GXX TXX T1' T2' V ? CX IX1 IX2 FA.
    
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX V G1 (TSelH x) T1') as IXX1. eauto.
    assert (compat GXX TXX V G2 (TSelH x) T2') as IXX2. eauto.
    
    eapply (compat_selh GXX TXX V G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].
    eapply (compat_selh GXX TXX V G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].
    assert (not (nosubst (TSelH 0))). unfold not. intros. simpl in H1. eauto.
    assert (not (closed 0 0 (TSelH 0))). unfold not. intros. inversion H4. omega.

    destruct x; destruct IX1; ev; try omega; destruct IX2; ev; try omega; subst.
    + SCase "x = 0".
      repeat destruct IXX1 as [IXX1|IXX1]; ev; try contradiction.
      repeat destruct IXX2 as [IXX2|IXX2]; ev; try contradiction. 
      * SSCase "sel-sel".
        subst. inversion H14. subst.
        simpl. eapply stpd2_selx. eauto. eauto.
    + SCase "x > 0".
      destruct IXX1; destruct IXX2; ev; subst; eapply stpd2_selax; eauto.
    (* leftovers *)
    + eauto. + subst. eauto. + eauto. + eauto. + subst. eauto. + eauto. 

  - Case "all".
    intros GH0 GH0' GX TX T1' T2' V ? CX IX1 IX2 FA.
    
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.
    
    eapply compat_all in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_all in IX2. repeat destruct IX2 as [? IX2].

    subst.
    
    eapply stpd2_all. 
    + eapply IHstp2_1. eauto. eauto. eauto. eauto. eauto. eauto. 
    + eauto.
    + eauto.
    + subst. 
      specialize (IHstp2_2 H3) with (GH1 := (0, (G2, T3))::GH0).
      eapply IHstp2_2. 
      reflexivity.
      eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.

  - Case "bind".
    intros GH0 GH0' GX TX T1' T2' V ? CX IX1 IX2 FA.
    
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.
    
    eapply compat_bind in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_bind in IX2. repeat destruct IX2 as [? IX2].

    subst. 
    
    eapply stpd2_bind. 
    + eauto.
    + eauto.
    + subst. 
      specialize (IHstp2 H2) with (GH1 := (0, (G1,  open (TSelH (length (GH0 ++ [(0, (GX, TX))]))) T1))::GH0).
      eapply IHstp2. 
      reflexivity.
      eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto. repeat split. rewrite app_length. simpl. rewrite EL. eapply IX1. eauto.
    + eauto.
    + eauto. subst GH. fold id. rewrite <- EL. eapply closed_upgrade_free. eauto. omega.
    + eauto.
    + eauto. subst GH. fold id. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
      (* TODO: rewrite match error. probably need to unfold something. *)
      
  - Case "wrapf".
    intros. subst. eapply stpd2_wrapf. eapply IHstp2; eauto.
  - Case "transf".

    (* TODO:  
       About the middle man in trans:
       We don't know that we can safely remove x.
       However, we can extend G2 without increasing
       the size of the derivations, and obtain the
       necessary compat evidence. For this, we'll need
       to do induction on the size n.
     *)
    admit. (*intros. subst. eapply stpd2_transf. eapply IHstp2_1. eappy IHstp2_2. *)
Qed.


Lemma stpd2_substitute: forall m G1 G2 T1 T2 GH,
   stpd2 m G1 T1 G2 T2 GH ->
   forall GH0 GH0' GX TX T1' T2' V,
     GH = (GH0 ++ [(0,(GX, TX))]) ->
     closed 0 0 TX ->
     compat GX TX V G1 T1 T1' ->
     compat GX TX V G2 T2 T2' ->
     Forall2 (compat2 GX TX V) GH0 GH0' ->
     stpd2 m G1 T1' G2 T2' GH0'.
Proof. intros. repeat eu. eapply stp2_substitute; eauto. Qed.




(*
(* not used right now, but could be a useful helper *)
Lemma stp2_concretize: forall G1 G2 T1X T2X TX,
   stp2 G1 (open (TSelH 0) T1X) G2 (open (TSelH 0) T2X) [(0,(G2, TX))] ->
   stp2 ((fresh G1, vty G2 TX)::G1) (open (TSel (fresh G1)) T1X)
     G2 (open TX T2X) [].
Proof.
  admit. (* call aux version above *)
Qed.
*)


(* --------------------------------- *)

(*
Lemma stp_wf_subst: forall G1 GH T11 T12 x,
  stp G1 GH T11 T11 ->
  stp G1 ((x, TMem T11) :: GH) (open (TSelH x) T12) (open (TSelH x) T12) ->
  stp G1 GH (open T11 T12) (open T11 T12).
Proof.
  admit.
Qed.


Lemma has_type_wf: forall G1 t T,
  has_type G1 t T ->
  stp G1 [] T T.
Proof.
  intros. induction H.
  - Case "true". eauto.
  - Case "false". eauto.
  - Case "var". eauto.
  - Case "app".
    assert (stp env [] (TFun T1 T2) (TFun T1 T2)) as WF. eauto.
    inversion WF. eauto.
  - Case "abs".
    eauto.
  - Case "tapp".
    assert (stp env [] (TAll T11 T12) (TAll T11 T12)) as WF. eauto.
    inversion WF. subst. eapply stp_wf_subst; eauto.
  - Case "tabs".
    eauto.
Qed.
*)


Lemma inv_vtp_half: forall G v T GH,
  val_type G v T ->
  exists T0, val_type (base v) v T0 /\ closed 0 0 T0 /\ stpd2 false (base v) T0 G T GH.
Proof. admit. Qed.
  
Lemma stp_to_stp2: forall G1 GH T1 T2,
  stp G1 GH T1 T2 ->
  forall GX GY, wf_env GX G1 -> wf_envh GX GY GH ->
  stpd2 false GX T1 GX T2 GY.
Proof with stpd2_wrapf.
  intros G1 G2 T1 T2 ST. induction ST; intros GX GY WX WY; eapply stpd2_wrapf.
  - Case "topx". eapply stpd2_topx.
  - Case "botx". eapply stpd2_botx.
  - Case "top". eapply stpd2_top; eauto.
  - Case "bot". eapply stpd2_bot; eauto.
  - Case "bool". eapply stpd2_bool; eauto.
  - Case "fun". eapply stpd2_fun; eauto.
  - Case "mem". eapply stpd2_mem; eauto.
  - Case "sel1". 
    assert (exists v : vl, index x GX = Some v /\ val_type GX v TX) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? VT]].
    eapply inv_vtp_half in VT. ev.
    eapply stpd2_sel1. eauto. eauto. eauto. eapply stpd2_trans. eauto. eauto.
  - Case "sel2". admit.
  - Case "selx". 
    assert (exists v : vl, index x GX = Some v /\ val_type GX v TX) as A.
    eapply index_safe_ex. eauto. eauto. ev.
    eapply stpd2_selx. eauto. eauto. 
  - Case "sela1". eauto.
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    inversion VT. subst. 
    eapply stpd2_sela1. eauto. eapply IHST. eauto. eauto.
  - Case "sela2". admit.
  - Case "selax". eauto.
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto. ev. destruct x0.
    eapply stpd2_selax. eauto. eauto. 
  - Case "all".
    subst x. assert (length GY = length GH). eapply wfh_length; eauto.
    eapply stpd2_all. eauto. rewrite H. eauto. rewrite H.  eauto.
    rewrite H.
    eapply IHST2. eauto. eapply wfeh_cons. eauto.
  - Case "bind".
    subst x. assert (length GY = length GH). eapply wfh_length; eauto. unfold id in H.
    eapply stpd2_bind. rewrite H. eauto. rewrite H. eauto.
    rewrite H.
    eapply IHST. eauto. eapply wfeh_cons. eauto.
Qed.




Lemma invert_abs: forall venv vf T1 T2,
  val_type venv vf (TFun T1 T2) ->
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





Lemma invert_tabs: forall venv vf vx T1 T2,
  val_type venv vf (TAll T1 T2) ->
  val_type venv vx T1 ->
  sstpd2 true venv T2 venv T2 [] ->
  exists env tenv x y T3 T4,
    vf = (vtabs env x T3 y) /\
    fresh env = x /\
    wf_env env tenv /\
    has_type ((x,T3)::tenv) y (open (TSel x) T4) /\
    sstpd2 true venv T1 env T3 [] /\
    sstpd2 true ((x,vx)::env) (open (TSel x) T4) venv T2 []. (* (open T1 T2) []. *)
Proof.
  intros venv0 vf vx T1 T2 VF VX STY. inversion VF; ev; try solve by inversion. inversion H2. subst.
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
  assert (stpd2 false venv0 T1 venv0 T1 []). eapply stpd2_reg1. eauto.
  assert (closed 0 0 T1). eapply stpd2_closed1 in H1. simpl in H1. eauto.
  
  (* now rename *)
  
  assert (stpd2 false ((fresh venv1,vx) :: venv1) (open_rec 0 (TSel (fresh venv1)) T3) venv0 (T2) []). { (* T2 was open T1 T2 *)

    (* now that sela1/sela2 can use subtyping, it is better to dispatch on the
       valtp evidence (instead of the type, as before) *)

    eapply inv_vtp_half in VX. ev.
    
    assert (closed 0 (length ([]:aenv)) T2). eapply sstpd2_closed1; eauto.
    assert (open (TSelH 0) T2 = T2) as OP2. symmetry. eapply closed_no_open; eauto.

    
    eapply stpd2_substitute with (GH0:=nil). 
    eapply stpd2_extend1. eapply stpd2_narrow. eapply stpd2_extendH. eapply H6. eapply KEY.
    eauto. simpl. eauto. eauto. 
    left. repeat eexists. eapply index_hit2. eauto. eauto. eauto. eauto.
    rewrite (subst_open_zero 0 1). eauto. eauto.
    right. left. split. rewrite OP2. eauto. eauto. eauto. 
  }
  eapply stpd2_upgrade in H4.

  (* done *)
  subst. eauto.
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
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.

  - Case "False".
    remember (tfalse) as e. induction H0; inversion Heqe; subst.
    + eapply not_stuck. eapply v_bool; eauto. 
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.
      
  - Case "Var".
    remember (tvar i) as e. induction H0; inversion Heqe; subst.
    + destruct (index_safe_ex venv0 env T1 i) as [v [I V]]; eauto. 
      rewrite I. eapply not_stuck. eapply V.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.

  - Case "Typ".
    remember (ttyp t) as e. induction H0; inversion Heqe; subst.
    + eapply not_stuck. eapply v_ty; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.
      
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

      destruct (invert_abs venv0 vf T1 T2) as
          [env1 [tenv [f0 [x0 [y0 [T3 [T4 [EF [FRF [FRX [WF [HTY [STX STY]]]]]]]]]]]]]. eauto.
      (* now we know it's a closure, and we have has_type evidence *)

      assert (res_type ((x0,vx)::(f0,vf)::env1) res T4) as HRY.
        SCase "HRY".
          subst. eapply IHn. eauto. eauto.
          (* wf_env f x *) econstructor. eapply valtp_widen; eauto. eapply sstpd2_extend2. eapply sstpd2_extend2. eauto. eauto. eauto. 
          (* wf_env f   *) econstructor. eapply v_abs; eauto. eapply sstpd2_extend2.
          eapply sstpd2_downgrade in STX. eapply sstpd2_downgrade in STY. repeat eu.
          eexists. eapply stp2_fun. eapply stp2_reg2. eapply STX. eapply stp2_reg1. eauto. eauto.
          eauto. (* TODO: sstpd2_fun constructor *)

      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen; eauto. eapply sstpd2_extend1. eapply sstpd2_extend1. eauto. eauto. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.
      
    
  - Case "Abs".
    remember (tabs i i0 e) as xe. induction H0; inversion Heqxe; subst.
    + eapply not_stuck. eapply v_abs; eauto. rewrite (wf_fresh venv0 env H1). eauto. eapply stpd2_upgrade. eapply stp_to_stp2. eauto. eauto. econstructor.
    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.

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

      destruct (invert_tabs venv0 vf vx T11 T12) as
          [env1 [tenv [x0 [y0 [T3 [T4 [EF [FRX [WF [HTY [STX STY]]]]]]]]]]].
      eauto. eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.
      (* now we know it's a closure, and we have has_type evidence *)

      assert (res_type ((x0,vx)::env1) res (open (TSel x0) T4)) as HRY.
        SCase "HRY".
          subst. eapply IHn. eauto. eauto.
          (* wf_env x *) econstructor. eapply valtp_widen; eauto. eapply sstpd2_extend2. eauto. eauto. eauto.
      inversion HRY as [? vy].

      eapply not_stuck. eapply valtp_widen. eauto. eauto.

    + eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.

  - Case "TAbs".
    remember (ttabs i t e) as xe. induction H0; inversion Heqxe; subst.
    + eapply not_stuck. eapply v_tabs; eauto. subst i. eauto. rewrite (wf_fresh venv0 env H1). eauto. eapply stpd2_upgrade. eapply stp_to_stp2. eauto. eauto. econstructor.
    +  eapply restp_widen. eapply IHhas_type; eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. econstructor.

       Grab Existential Variables. apply 0. apply 0.
Qed.

End FSUB.