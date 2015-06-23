(* Full safety for F-sub (WIP) *)
(* values well-typed with respect to runtime environment *)
(* inversion lemma structure *)

(*

TODO:
- stp / stp2
- vty will need ty and/or env. figure out what exactly.

- stp2 trans + narrowing 

*)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Module STLC.

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TTop   : ty           
  | TFun   : ty -> ty -> ty
  | TMem   : ty -> ty
  | TMemE  : ty -> ty (* exact *)
  | TSel   : id -> ty
  | TSelH  : id -> ty
  | TAll   : ty -> ty -> ty

  | TSelB  : id -> ty                           
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : id -> id -> tm -> tm (* \f x.y *)
  | ttapp : tm -> ty -> tm (* f[X] *)
  | ttabs : id -> ty -> tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
| vty   : list (id*vl) -> ty -> vl
| vtya  : list (id*vl) -> ty -> vl (* X<T, only used in stp2_all *)
| vbool : bool -> vl
| vabs  : list (id*vl) -> id -> id -> tm -> vl
| vtabs : list (id*vl) -> id -> ty -> tm -> vl
.

Definition venv := list (id*vl).
Definition tenv := list (id*ty).

Hint Unfold venv.
Hint Unfold tenv.
(*
Fixpoint length {X: Type} (l : list X): nat :=
  match l with
    | [] => 0
    | _::l' => 1 + length l'
  end.
*)
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

Inductive sub_env {X:Type}: list (id*X) -> list (id*X) -> Prop :=
| se_refl: forall G,
    sub_env G G
| se_ext:  forall G1 G2 x v,
    sub_env G1 G2 ->
    fresh G2 <= x ->
    sub_env G1 ((x,v)::G2)
.




(* LOCALLY NAMELESS *)

Inductive closed_rec: nat -> nat -> ty -> Prop :=
| cl_top: forall k l,
    closed_rec k l TTop
| cl_bool: forall k l,
    closed_rec k l TBool
| cl_fun: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec k l T2 ->
    closed_rec k l (TFun T1 T2)
| cl_mem: forall k l T1,
    closed_rec k l T1 ->
    closed_rec k l (TMem T1)
| cl_bind: forall k l T1 T2,
    closed_rec k l T1 ->
    closed_rec (S k) l T2 ->
    closed_rec k l (TAll T1 T2)
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
    | TTop => TTop
    | TBool       => TBool
    | TMem T1     => TMem (open_rec k u T1)
    | TMemE T1    => TMemE (open_rec k u T1)
    | TFun T1 T2  => TFun (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

(* sanity check *)
Example open_ex1: open (TSel 9) (TAll TBool (TFun (TSelB 1) (TSelB 0))) =
                      (TAll TBool (TFun (TSel 9) (TSelB 0))).
Proof. compute. eauto. Qed.


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
 Case "TBind". econstructor. eapply IHclosed_rec1. omega. eapply IHclosed_rec2. omega.
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


Fixpoint subst (U : ty) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBool        => TBool
    | TMem T1      => TMem (subst U T1)
    | TMemE T1     => TMemE (subst U T1)
    | TFun T1 T2   => TFun (subst U T1) (subst U T2)
    | TSelB i      => TSelB i
    | TSel i       => TSel i
    | TSelH i      => if beq_nat i 0 then U else TSelH (i-1)
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
  end.


Definition substt (UX: ty) (V: (id*ty)) :=
  match V with
    | (x,T) => (x-1,(subst UX T))
  end.


Definition substvb (UX: ty) (V: (id*(venv*ty))) :=
  match V with
    | (x,(G,T)) => (x-1,(G, (subst UX T)))
  end.

Definition substb (UX: ty) (UY: ty) (V: (id*(bool*ty))) :=
  match V with
    | (x,(b, T)) => (x-1,(b, (subst (if b then UX else UY) T)))
  end.


Definition substvbp (GX:venv) (UX: ty) (V: (id*vl)) (V2: (id*vl)) :=
  match V,V2 with
    | (x,vtya G T), V2 =>
      (G = GX /\ V2 = (x,vtya G (subst UX T))) \/
      (V2 = (x,vtya ((fresh G, vty GX UX)::G) (subst (TSel (fresh G)) T)))
    | _,_ => V = V2
  end.






Hint Unfold open.
Hint Unfold closed.


Inductive stp: tenv -> ty -> ty -> Prop :=
| stp_top: forall G1 T1,
    stp G1 T1 TTop
| stp_bool: forall G1,
    stp G1 TBool TBool
| stp_fun: forall G1 T1 T2 T3 T4,
    stp G1 T3 T1 ->
    stp G1 T2 T4 ->
    stp G1 (TFun T1 T2) (TFun T3 T4)             
| stp_mem: forall G1 T1 T2,
    stp G1 T1 T2 ->
    stp G1 (TMem T1) (TMem T2)         
| stp_sel1: forall G1 T T2 x,
    indexr x G1 = Some (TMem T) ->
    stp G1 T T2 ->   
    stp G1 (TSelH x) T2
| stp_selx: forall G1 T x,
    indexr x G1 = Some (TMem T) ->
    stp G1 (TSelH x) (TSelH x)
| stp_all: forall G1 T1 T2 T3 T4 x,
    stp G1 T3 T1 ->
    x = length G1 ->
    stp ((x,TMem T3)::G1) (open (TSelH x) T2) (open (TSelH x) T4) ->
    stp G1 (TAll T1 T2) (TAll T3 T4)
.

Hint Constructors stp.

(* TODO *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           index x env = Some T1 ->
           stp env T1 T1 ->
           has_type env (tvar x) T1
| t_app: forall env f x T1 T2,
           has_type env f (TFun T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
| t_abs: forall env f x y T1 T2,
           has_type ((x,T1)::(f,TFun T1 T2)::env) y T2 ->
           stp env (TFun T1 T2) (TFun T1 T2) ->
           fresh env <= f ->
           1+f <= x ->
           has_type env (tabs f x y) (TFun T1 T2)
| t_tapp: forall env f T11 T12 ,
           has_type env f (TAll T11 T12) ->
           has_type env (ttapp f T11) (open T11 T12)
(*
NOTE: both the POPLmark paper and Cardelli's paper use this rule:
Does it make a difference? It seems like we can always widen f?

| t_tapp: forall env f T2 T11 T12 ,
           has_type env f (TAll T11 T12) ->
           stp env T2 T11 ->
           has_type env (ttapp f T2) (open T2 T12)

*)                    
| t_tabs: forall env x y T1 T2,
           has_type ((x,TMem T1)::env) y (open (TSel x) T2) -> 
           stp env (TAll T1 T2) (TAll T1 T2) ->
           fresh env = x ->
           has_type env (ttabs x T1 y) (TAll T1 T2)
(* TODO: subsumption *)
.

Definition sel (b:bool) (G1:venv) (G2:venv) := if b then G1 else G2.

Definition swap (p:id*(bool*ty)) :=
  match p with
    | (x, (b, T)) => (x, (negb b, T))
  end.


Inductive stp2: venv -> ty -> venv -> ty -> list (id*(venv*ty))  -> Prop :=
| stp2_bool: forall G1 G2 GH,
    stp2 G1 TBool G2 TBool GH
| stp2_fun: forall G1 G2 T1 T2 T3 T4 GH,
    stp2 G2 T3 G1 T1 GH ->
    stp2 G1 T2 G2 T4 GH ->
    stp2 G1 (TFun T1 T2) G2 (TFun T3 T4) GH
| stp2_mem: forall G1 G2 T1 T2 GH,
    stp2 G1 T1 G2 T2 GH ->
    stp2 G1 (TMem T1) G2 (TMem T2) GH

(* atm not clear if these are needed *)
| stp2_sel1: forall G1 G2 GX TX x T2 GH,
    index x G1 = Some (vty GX TX) ->
    (* closed 0 0 TX -> *)
    stp2 GX TX G2 T2 GH ->
    stp2 G1 (TSel x) G2 T2 GH

| stp2_sel2: forall G1 G2 GX TX x T1 GH,
    index x G2 = Some (vty GX TX) ->
    (* closed 0 0 TX -> *)
    stp2 G1 T1 GX TX GH ->
    stp2 G1 T1 G2 (TSel x) GH

(* X<T, one sided *)
| stp2_sela1: forall G1 G2 GX TX x T2 GH,
    indexr x GH = Some (GX, TX) ->
    (* closed 0 x TX -> *)
    stp2 GX TX G2 T2 GH ->
    stp2 G1 (TSelH x) G2 T2 GH

         
| stp2_selx: forall G1 G2 GX TX x GH,
    indexr x GH = Some (GX, TX) ->
    indexr x GH = Some (GX, TX) ->
    (*closed 0 x TX ->*)
    stp2 G1 (TSelH x) G2 (TSelH x) GH


| stp2_all: forall G1 G2 T1 T2 T3 T4 GH,
    stp2 G2 T3 G1 T1 GH ->
    closed 1 (length GH) T2 -> (* must not accidentally bind x *)
    closed 1 (length GH) T4 -> 
    stp2 G1 (open (TSelH (length GH)) T2) G2 (open (TSelH (length GH)) T4) ((0,(G2, T3))::GH) ->
    stp2 G1 (TAll T1 T2) G2 (TAll T3 T4) GH
.






Inductive wf_env : venv -> tenv -> Prop := 
| wfe_nil : wf_env nil nil
| wfe_cons : forall n v t vs ts,
    val_type ((n,v)::vs) v t ->
    wf_env vs ts ->
    wf_env (cons (n,v) vs) (cons (n,t) ts)

with val_type : venv -> vl -> ty -> Prop :=
| v_ty: forall env venv tenv T1 TE,
    wf_env venv tenv -> (* T1 wf in tenv ? *)
    stp2 venv (TMem T1) env TE [] ->
    val_type env (vty venv T1) TE
| v_bool: forall venv b TE,
    stp2 [] TBool venv TE [] ->
    val_type venv (vbool b) TE
| v_abs: forall env venv tenv f x y T1 T2 TE,
    wf_env venv tenv ->
    has_type ((x,T1)::(f,TFun T1 T2)::tenv) y T2 ->
    fresh venv <= f ->
    1 + f <= x ->
    stp2 venv (TFun T1 T2) env TE [] -> 
    val_type env (vabs venv f x y) TE
| v_tabs: forall env venv tenv x y T1 T2 TE,
    wf_env venv tenv ->
    has_type ((x,TMem T1)::tenv) y (open (TSel x) T2) ->
    fresh venv = x ->
    stp2 venv (TAll T1 T2) env TE [] ->
    val_type env (vtabs venv x T1 y) TE
.

Inductive wf_envh : venv -> tenv -> Prop := 
| wfeh_nil : wf_envh nil nil
| wfeh_cons : forall n v t vs ts,
    valh_type ((n,v)::vs) v t ->
    wf_envh vs ts ->
    wf_envh (cons (n,v) vs) (cons (n,t) ts)

with valh_type : venv -> vl -> ty -> Prop :=
| v_tya: forall env venv tenv T1 TE,
    wf_envh venv tenv -> (* T1 wf in tenv ? *)
    stp2 venv (TMem T1) env TE [] ->
    valh_type env (vtya venv T1) TE
.




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
                | Some (Some (vtya _ _)) => Some None
                | Some (Some (vtabs _ _ _ _)) => Some None
                | Some (Some (vabs env2 f x ey)) =>
                  teval n ((x,vx)::(f,vabs env2 f x ey)::env2) ey
              end
          end
        | ttapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vty _ _)) => Some None
            | Some (Some (vtya _ _)) => Some None
            | Some (Some (vabs _ _ _ _)) => Some None
            | Some (Some (vtabs env2 x T ey)) =>
              teval n ((x,vty env ex)::env2) ey
          end
      end
  end.


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
Hint Constructors val_type.
Hint Constructors wf_env.
Hint Constructors stp.
Hint Constructors stp2.
Hint Constructors sub_env.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.

Lemma wf_fresh : forall vs ts,
                    wf_env vs ts ->
                    (fresh vs = fresh ts).
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

(*
Lemma index_extend_mult : forall X n vs vs2 (T: X),
                       index n vs = Some T ->
                       sub_env vs vs2 ->
                       index n vs2 = Some T.
Proof. admit. Qed.


Lemma sub_env_xx {X}: forall (G1:list(id*X)) G2 x v1,
  sub_env ((x,v1)::G1) G2 ->
  fresh G1 <= x ->                      
  sub_env G1 G2.
Proof.
  intros.
  remember ((x, v1) :: G1) as GX.
  induction H.
  - subst G. eapply se_ext; eauto. 
  - subst G0. eapply se_ext; eauto.
Qed.

Lemma stp_extend : forall G1 T1 T2,
                       stp G1 T1 T2 ->
                       forall x v1, fresh G1 <= x ->
                       stp ((x,v1)::G1) T1 T2.
Proof. intros G1 T1 T2 H. induction H; intros; eauto.
  - Case "sel". eapply stp_sel1. eapply index_extend; eauto.
  - Case "selx". eapply stp_selx. eapply index_extend; eauto.
  - Case "all". admit. (* eapply stp_all. eauto. intros. eapply H0. eapply sub_env_xx; eauto. eauto. *)
Qed.
*)

Lemma stp2_extend2 : forall x v1 G1 G2 T1 T2 H,
                       stp2 G1 T1 G2 T2 H ->
                       fresh G2 <= x ->
                       stp2 G1 T1 ((x,v1)::G2) T2 H.
Proof. admit. Qed.

Lemma stp2_extend1 : forall x v1 G1 G2 T1 T2 H,
                       stp2 G1 T1 G2 T2 H ->
                       fresh G1 <= x ->
                       stp2 ((x,v1)::G1) T1 G2 T2 H.
Proof. admit. Qed.

(*
Lemma stp2_extend2_mult : forall G1 G2 G2' T1 T2 H,
                       stp2 G1 T1 G2 T2 H ->
                       sub_env G2 G2' ->
                       stp2 G1 T1 G2' T2 H.
Proof. admit. Qed.

Lemma stp2_extend1_mult : forall G1 G1' G2 T1 T2 H,
                       stp2 G1 T1 G2 T2 H ->
                       sub_env G1 G1' ->    
                       stp2 G1' T1 G2 T2 H.
Proof. admit. Qed.
*)

Lemma stp2_reg2 : forall G1 G2 T1 T2 H ,
                       stp2 G1 T1 G2 T2 H ->
                       stp2 G2 T2 G2 T2 H.
Proof. admit. Qed.

Lemma stp2_reg1 : forall G1 G2 T1 T2 H,
                       stp2 G1 T1 G2 T2 H ->
                       stp2 G1 T1 G1 T1 H.
Proof. admit. Qed.



Lemma valtp_extend : forall vs v x v1 T,
                       val_type vs v T ->
                       fresh vs <= x ->
                       val_type ((x,v1)::vs) v T.
Proof.
  intros. induction H; eauto; econstructor; eauto; eapply stp2_extend2; eauto.
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


  
Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.


Hint Constructors stp2.


Lemma stp2_trans: forall G1 G2 G3 T1 T2 T3 H,
  stp2 G1 T1 G2 T2 H ->
  stp2 G2 T2 G3 T3 H ->
  stp2 G1 T1 G3 T3 H.
Proof. admit. Qed.

(* used in trans -- need to generalize interface for induction *)
(*
Lemma stp2_narrow: forall x G1 G2 G3 G4 T1 T2 T3 T4 H,
  stp2 G1 T1 G2 T2 H -> (* careful about H! *)
  stp2 G3 T3 G4 T4 ((x,vtya G2 T2)::H) ->
  stp2 G3 T3 G4 T4 ((x,vtya G1 T1)::H).
Proof. admit. Qed.
 *)

(* used in inversion *)

(* used in inversion *)

(*
Lemma open2stp: forall venv0 venv1 x j l v T1 T2 H,
  (index x venv0 = Some v) \/ (closed j l T1) ->
  (index x venv1 = Some v) \/ (closed j l T2) ->
  stp2 venv0 T1 venv1 T2 H ->
  stp2 venv0 (open_rec j (TSel x) T1) venv1 (open_rec j (TSel x) T2) H.
Proof. admit. Qed.
*)

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


(*
Lemma stp2_refl: forall G1 T1 GH,
  closed (length GH) (fresh G1) T1 ->
  stp2 G1 T1 G1 T1 GH.                 
Proof. admit. Qed.
*)  
     
Hint Unfold open.


Fixpoint openm_rec (k: nat) (v:nat) (T: ty) { struct T }: ty :=
  match T with
    | TSel x      => TSel x (* free var remains free. functional, so we can't check for conflict *)
    | TSelH i     => TSelH i
                           (* TODO: check k i <> 0 ? *)
    | TSelB i     => if le_lt_dec k i  then TSelH (v+k-i-1) else TSelB i
    | TAll T1 T2  => TAll (openm_rec k v T1) (openm_rec (S k) v T2) 
    | TTop => TTop
    | TBool       => TBool
    | TMem T1     => TMem (openm_rec k v T1)
    | TMemE T1    => TMemE (openm_rec k v T1)
    | TFun T1 T2  => TFun (openm_rec k v T1) (openm_rec k v T2)
  end.


Example openm_ex0: open_rec 0 (TSelH 9) (TAll TBool (TFun (TSelB 1) (TSelB 0))) =
                      (TAll TBool (TFun (TSelH 9) (TSelB 0))).
Proof. compute. eauto. Qed.


Example openm_ex1: openm_rec 0 9 (TAll TBool (TFun (TSelB 1) (TSelB 0))) =
                      (TAll TBool (TFun (TSelH 8) (TSelB 0))).
Proof. compute. eauto. Qed.


(*
openm (S i) n T1 T2 ->
openm (open_rec i (TSel (S n)) T1) T2

T0 = T1X2
T1 = (open_rec 1 (TSelH (length GH)-1) T0)
T2 = (open_rec 0 (TSelH (length GH)) T1)
*)     

Lemma open_more: forall T1X2 L i,
  open_rec i (TSelH (L)) (openm_rec (S i) L T1X2) = openm_rec i (S L) T1X2.
Proof.
  intros T.
  induction T; intros.
  - Case "bool". compute. eauto.
  - Case "top". compute. eauto.
  - Case "fun".
    unfold open, open_rec, openm_rec. fold openm_rec. fold open_rec.
    rewrite IHT1. rewrite IHT2. eauto.
  - unfold open, open_rec, openm_rec. fold openm_rec. fold open_rec.
    rewrite IHT. eauto.
  - unfold open, open_rec, openm_rec. fold openm_rec. fold open_rec.
    rewrite IHT. eauto.
  - eauto.
  - eauto.
  - unfold open, open_rec, openm_rec. fold openm_rec. fold open_rec.
    rewrite IHT1. rewrite IHT2. eauto.
  - unfold openm_rec. unfold open_rec.
    case_eq (le_lt_dec (S i0) (i)); intros E1 EV1;
    case_eq (le_lt_dec (i0) (i)); intros E3 EV3;
    (case_eq (beq_nat i0 i); intros E5; [ eapply beq_nat_true_iff in E5 |
                                          eapply beq_nat_false_iff in E5]) ; subst; try omega; try eauto.

    assert (L + S i0 - i = S L + i0 - i). omega. eauto.
    assert (L = S L + i - i - 1). unfold id. omega. eauto.
Qed.


Fixpoint open_env (GY:venv)(TY:ty) (G: venv): venv :=
  match G with
    | nil => nil
    | (x,v)::xs =>
      (x,match v with
         | vtya GX TX => vtya ((fresh GX,vty GY TY)::GX) (open_rec (length xs) (TSel (fresh GX)) TX)
         | _ => v
       end) :: (open_env GY TY xs)
  end.

Fixpoint openm_env (G: venv): venv :=
  match G with
    | nil => nil
    | (x,v)::xs =>
      (x,match v with
           | vtya GX TX => vtya GX (openm_rec 0 (length xs) TX) 
           | _ => v
         end) :: (openm_env xs)
  end.

Fixpoint closed_env (G: venv): Prop :=
  match G with
    | nil => True
    | (x,v)::xs =>
      (match v with
           | vtya GX TX => closed_rec (length xs) 0 TX
           | _ => True
      end) /\ closed_env xs
  end.



Lemma open_env_length: forall g t G,
   length (open_env g t G) = length G.
Proof. intros. induction G. eauto. destruct a. destruct v; eauto;
       unfold open_env; fold open_env; unfold length; unfold length in IHG;
       eauto.
Qed.

Lemma openm_env_length: forall G,
   length (openm_env G) = length G.
Proof. intros. induction G. eauto. destruct a. destruct v; eauto;
       unfold openm_env; fold openm_env; unfold length; unfold length in IHG;
       eauto.
Qed.

Lemma openm_env_cons: forall G2 GH0 T2X1,
   (0, vtya G2 (openm_rec 0 (length (GH0)) T2X1)) :: openm_env GH0
    = openm_env ((0,vtya G2 T2X1)::GH0).
Proof. intros. unfold openm_env. fold openm_env. eauto.
Qed.

Lemma closed_no_openm: forall T x l j,
  closed_rec j l T ->
  T = openm_rec j x T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed_rec; rewrite <-IHclosed_rec; auto];
  try solve [compute; compute in IHclosed_rec1; compute in IHclosed_rec2; rewrite <-IHclosed_rec1; rewrite <-IHclosed_rec2; auto].

  Case "TSelB".
    unfold openm_rec. destruct (le_yy k i). eauto. rewrite H0. eauto.
Qed.

Lemma closed_no_openm2: forall T l j,
  closed_rec j l T ->
  forall j2 x, j2 >= j -> T = openm_rec j2 x T.
Proof.
  intros T l j H. induction H; intros; eauto;
  try solve [compute; compute in IHclosed_rec; rewrite <-IHclosed_rec; auto];
  try solve [compute; compute in IHclosed_rec1; compute in IHclosed_rec2; rewrite <-IHclosed_rec1; rewrite <-IHclosed_rec2; auto].

  simpl. rewrite <-IHclosed_rec1. rewrite <-IHclosed_rec2. eauto. eauto. eauto.
  simpl. rewrite <-IHclosed_rec1. rewrite <-IHclosed_rec2. eauto. omega. eauto.

  Case "TSelB".
  simpl. destruct (le_yy j2 i). omega. rewrite H1. eauto.
Qed.




Hint Immediate open_env_length.
Hint Immediate openm_env_length.


(*

example:

A0 <: Int |- { X1 <: A0 => X1 -> X1 } < { Y1 <: A0 => A0 -> Y1 }
A0 <: Int, Y1 <: A0, Y1 -> Y1 < A0 -> Y1

-->

|- { X0 <: Int => X0 -> X0 } < { Y0 <: Int => Int -> Y0 }
Y0 <: Int |- Y0 -> Y0 < Int -> Y0

*)

Lemma xxf: forall A B C,
             A < C -> B < C -> C - A = C - B -> A = B.
Proof. intros. omega. Qed.


Lemma indexr_wtf1: forall GH GX TX n,
             indexr n (openm_env GH) = Some (vtya GX TX) ->
             exists TX', indexr n GH = Some (vtya GX TX') /\
                             TX = openm_rec 0 n TX'.
Proof.
  intros GH. induction GH.
  - intros. simpl in H. inversion H.
  - intros. case_eq (beq_nat n (length GH)); intros E.
    + assert (n = length GH). eapply beq_nat_true_iff; eauto.

      simpl. destruct a. rewrite E.
      simpl in H. rewrite openm_env_length in H. rewrite E in H.
      
      destruct v; simpl in H; inversion H.
      subst. eexists. split; eauto. 

    + assert (n <> length GH). eapply beq_nat_false_iff; eauto.

      simpl. destruct a. rewrite E.
      simpl in H. rewrite openm_env_length in H. rewrite E in H.
      
      eapply IHGH; eauto.
Qed.

(* Set Printing All. -- problem with length GH: id vs nat *)

Lemma indexr_wtf2: forall GH GX TX GX0 TX0 n,
      indexr (n+1) (openm_env (GH ++ [(0,vtya GX0 TX0)])) =
         Some (vtya GX TX) ->
      exists TXX, TX = (openm_rec 0 (n+1) TXX) /\
                  indexr n (openm_env (open_env GX0 TX0 GH)) =
                  Some
                    (vtya ((fresh GX, vty GX0 TX0) :: GX)
                          (openm_rec 0 (n) (open_rec (n) (TSel (fresh GX)) TXX))).
Proof.
  intros GH. induction GH.
  - intros. simpl in H.
    assert (n+1 <> 0). omega.
    eapply beq_nat_false_iff in H0. rewrite H0 in H. inversion H.
  - intros. case_eq (beq_nat n (length GH)); intros E.
    + assert (n = length GH). eapply beq_nat_true_iff; eauto.
      assert (n+1 = length GH + 1). eauto.
      assert (beq_nat (n+1) ((length GH) + 1) = true). eapply beq_nat_true_iff; eauto.
      simpl in H. destruct a.
      
      rewrite app_length in H. simpl in H. rewrite openm_env_length in H.
      rewrite app_length in H. simpl in H. simpl in H.
      rewrite H2 in H. destruct v; inversion H.
      simpl. rewrite openm_env_length. rewrite open_env_length. unfold id.
      rewrite E. rewrite H0. eauto.
    + assert (n <> length GH). eapply beq_nat_false_iff; eauto.
      assert (n+1 <> length GH + 1). omega.
      assert (beq_nat (n+1) ((length GH) + 1) = false). eapply beq_nat_false_iff; eauto.
      simpl in H. destruct a.

      rewrite app_length in H. simpl in H. rewrite openm_env_length in H.
      rewrite app_length in H. simpl in H. simpl in H.
      rewrite H2 in H.
      
      simpl. rewrite openm_env_length. rewrite open_env_length. unfold id. rewrite E.

      eapply IHGH; eauto.
Qed.


Lemma indexr_wtf3: forall GH GX TX GX0 TX0 n,
      closed_env (GH ++ [(0,vtya GX0 TX0)]) ->
      indexr (n+1) (openm_env (GH ++ [(0,vtya GX0 TX0)])) =
         Some (vtya GX TX) ->
      exists TXX,
        TX = (openm_rec 0 (n+1) TXX) /\
        closed_rec (n+1) 0 TXX /\
        indexr n (openm_env (open_env GX0 TX0 GH)) =
        Some
          (vtya ((fresh GX, vty GX0 TX0) :: GX)
                (openm_rec 0 (n) (open_rec (n) (TSel (fresh GX)) TXX))).
Proof.
  intros GH. induction GH.
  - intros. simpl in H0.
    assert (n+1 <> 0). omega.
    eapply beq_nat_false_iff in H1. rewrite H1 in H0. inversion H0.
  - intros. case_eq (beq_nat n (length GH)); intros E.
    + assert (n = length GH). eapply beq_nat_true_iff; eauto.
      assert (n+1 = length GH + 1). eauto.
      assert (beq_nat (n+1) ((length GH) + 1) = true). eapply beq_nat_true_iff; eauto.
      simpl in H0. destruct a.
      rewrite app_length in H0. simpl in H0. rewrite openm_env_length in H0.
      rewrite app_length in H0. simpl in H0. simpl in H0.
      rewrite H3 in H0. destruct v; inversion H0.
      simpl in H. destruct H. rewrite app_length in H. simpl in H.
      simpl. rewrite openm_env_length. rewrite open_env_length. unfold id.
      rewrite E. rewrite H1. eauto. 
    + assert (n <> length GH). eapply beq_nat_false_iff; eauto.
      assert (n+1 <> length GH + 1). omega.
      assert (beq_nat (n+1) ((length GH) + 1) = false). eapply beq_nat_false_iff; eauto.
      simpl in H0. destruct a.

      rewrite app_length in H0. simpl in H0. rewrite openm_env_length in H0.
      rewrite app_length in H0. simpl in H0. simpl in H0.
      rewrite H3 in H0.

      simpl in H. destruct H.
      simpl. rewrite openm_env_length. rewrite open_env_length. unfold id. rewrite E.

      eapply IHGH; eauto.
Qed.

(*
Lemma indexr_wtf4: forall GH GX TX GX0 TX0 n,
      closed_env (GH ++ [(0,vtya GX0 TX0)]) ->
      indexr (n+1) (openm_env (GH ++ [(0,vtya GX0 TX0)])) =
         Some (vtya GX TX) ->
      exists TXX,
        TX = (openm_rec 0 (length GH) TXX) /\
        closed_rec (length GH) 0 TXX /\
        indexr n (openm_env (open_env GX0 TX0 GH)) =
        Some
          (vtya ((fresh GX, vty GX0 TX0) :: GX)
                (openm_rec 0 (n) (open_rec (n) (TSel (fresh GX)) TXX))).
Proof.
*)




Lemma indexr_hit0: forall GH GX0 TX0,
      indexr 0 (openm_env (GH ++ [(0,vtya GX0 TX0)])) =
      Some (vtya GX0 (openm_rec 0 0 TX0)).
Proof.
  intros GH. induction GH.
  - intros. simpl. eauto. 
  - intros. simpl. destruct a. simpl. rewrite openm_env_length. rewrite app_length. simpl.
    assert (length GH + 1 = S (length GH)). omega. rewrite H.
    eauto.
Qed.

Lemma indexr_hit02: forall GH GX0 TX0,
      closed_env (GH ++ [(0,vtya GX0 TX0)]) ->
      indexr 0 (openm_env (GH ++ [(0,vtya GX0 TX0)])) =
      Some (vtya GX0 TX0) /\ closed_rec 0 0 TX0.
Proof.
  intros GH. induction GH.
  - intros. simpl. rewrite <- (closed_no_openm TX0 0 0 0). eauto. simpl in H. destruct H. eauto.  simpl in H. destruct H. eauto.
  - intros. simpl. destruct a. simpl. rewrite openm_env_length. rewrite app_length. simpl.
    assert (length GH + 1 = S (length GH)). omega. rewrite H0.
    simpl in H. destruct H.
    eauto.
Qed.


(* 
sketch: 





*)



Hint Resolve beq_nat_true_iff.
Hint Resolve beq_nat_false_iff.

Lemma open_subst_commute: forall T2 TX (n:nat) x j,
closed j n TX ->
(open_rec j (TSelH x) (subst TX T2)) =
(subst TX (open_rec j (TSelH (x+1)) T2)).
Proof.
  intros T2 TX n. induction T2; intros; eauto.
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto.
  -  simpl. rewrite IHT2. eauto. eauto.
  -  simpl. rewrite IHT2. eauto. eauto.
  -  simpl. case_eq (beq_nat i 0); intros E. symmetry. eapply closed_no_open. eauto. simpl. eauto.  
  -  simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eapply closed_upgrade. eauto. eauto. eauto.
  - simpl. case_eq (beq_nat j i); intros E. simpl.
    assert (x+1<>0). omega. eapply beq_nat_false_iff in H0.
    assert (x=x+1-1). unfold id. omega.
    rewrite H0. eauto.
    simpl. eauto.
Qed.


Lemma indexr_subst: forall GH0 x TX T,
   indexr x (GH0 ++ [(0, TMem TX)]) = Some (TMem T) ->
   x = 0 /\ TX = T \/
   x > 0 /\ indexr (x-1) (map (substt TX) GH0) = Some (TMem (subst TX T)).
Proof.
  intros GH0. induction GH0; intros.
  - simpl in H. case_eq (beq_nat x 0); intros E.
    + rewrite E in H. inversion H.
      left. split. eapply beq_nat_true_iff. eauto. eauto.
    + rewrite E in H. inversion H.
  -  destruct a. unfold id in H. remember ((length (GH0 ++ [(0, TMem TX)]))) as L.
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

Lemma indexr_subst2: forall GH0 x bx TX TX1 TX2 b T,
   indexr x (GH0 ++ [(0, (bx,TX))]) = Some (b,T) ->
   x = 0 /\ bx = b /\ TX = T \/
   x > 0 /\ indexr (x-1) (map (substb TX1 TX2) GH0) = Some (b, (subst (if b then TX1 else TX2) T)).
Proof.
  intros GH0. induction GH0; intros.
  - simpl in H. case_eq (beq_nat x 0); intros E.
    + rewrite E in H. inversion H.
      left. split. eapply beq_nat_true_iff. eauto. eauto.
    + rewrite E in H. inversion H.
  -  destruct a. unfold id in H. remember ((length (GH0 ++ [(0, (bx,TX))]))) as L.
     case_eq (beq_nat x L); intros E. 
     + assert (x = L). eapply beq_nat_true_iff. eauto.
       eapply indexr_hit in H.
       right. split. rewrite app_length in HeqL. simpl in HeqL. omega.
       assert ((x - 1) = (length (map (substb TX1 TX2) GH0))).
       rewrite map_length. rewrite app_length in HeqL. simpl in HeqL. unfold id. omega.
       simpl.
       eapply beq_nat_true_iff in H1. unfold id in H1. unfold id. rewrite H1. subst. destruct b; eauto. eauto. eauto. subst. eauto. 
     + assert (x <> L). eapply beq_nat_false_iff. eauto.
       eapply indexr_miss in H. eapply IHGH0 in H.
       inversion H. left. eapply H1.
       right. inversion H1. split. eauto.
       simpl.
       assert ((x - 1) <> (length (map (substb TX1 TX2) GH0))).
       rewrite app_length in HeqL. simpl in HeqL. rewrite map_length.
       unfold not. intros. subst L. unfold id in H0. unfold id in H2. unfold not in H0. eapply H0. unfold id in H4. rewrite <-H4. omega.
       eapply beq_nat_false_iff in H4. unfold id in H4. unfold id. rewrite H4.
       destruct p. eauto. subst. eauto. 
Qed.

Lemma closed_no_subst: forall T j TX,
   closed_rec j 0 T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
            try rewrite (IHT j TX); eauto; try rewrite (IHT2 (S j) TX); eauto; try rewrite (IHT1 j TX); eauto.

  eapply closed_upgrade. eauto. eauto.

  subst. omega. 
Qed.

(* stub -- we do not have proper wf evidence *)
(* FSub has an okt wf predicate on environments *)
Lemma stp_refl: forall T j n,
                  closed_rec j 0 T ->
                  forall G, length G = n ->
  stp G T T.
Proof.
  intros T j n H. remember 0 as z.
  induction H; intros; eauto; try subst l.
  - Case "all". subst. eapply stp_all. eauto. eauto. admit. (* need to open *)
  - Case "sel". admit. (* no rule for TSel in stp1 ! *)
  - Case "selH". admit. (* we know it's a valid index, but not (TMem T) *)
  - Case "selB". admit. (* no rule for TSelB *)
Qed.

Lemma stp_substitute: forall T1 T2 GH,
   stp GH T1 T2 ->
   forall GH0 TX,
     GH = (GH0 ++ [(0,TMem TX)]) ->
     closed 0 0 TX ->
     stp (map (substt TX) GH0)
         (subst TX T1)
         (subst TX T2).
Proof.
  intros T1 T2 GH H.
  induction H.
  - Case "top". eauto.
  - Case "bool". eauto.
  - Case "fun". intros. simpl. eapply stp_fun. eauto. eauto.
  - Case "mem". intros. simpl. eapply stp_mem. eauto.
  - Case "sel1". intros GH0 TX ? ?. simpl.
    subst G1. specialize (indexr_subst _ x TX T H). intros. 
    destruct H1; destruct H1.
    + subst. simpl.
      specialize (IHstp GH0 T). 
      assert (subst T T = T). eapply closed_no_subst; eauto.
      rewrite H1 in IHstp.
      eapply IHstp. eauto. eauto.
    + subst. simpl.
      assert (beq_nat x 0 = false). eapply beq_nat_false_iff; omega. rewrite H4. simpl.
      eapply stp_sel1. eapply H3. eapply IHstp. eauto. eauto.
  - Case "selx". intros GH0 TX ? ?. simpl.
    subst G1. specialize (indexr_subst _ x TX T H). intros.
    destruct H0; destruct H0.
    + subst. simpl. eapply stp_refl; eauto.
    + subst. simpl. assert (beq_nat x 0 = false). eapply beq_nat_false_iff. omega. rewrite H3. eapply stp_selx. eauto.
  - Case "all".
    intros GH0 TX ? ?.
    simpl. eapply stp_all.
    + eapply IHstp1; eauto.
    + rewrite map_length. eauto.
    + specialize IHstp2 with (GH0:=(x, TMem T3)::GH0) (TX:=TX).
      subst G1. simpl in IHstp2.
      unfold open. unfold open in IHstp2.
      subst x.
      rewrite open_subst_commute with (n:=0).
      rewrite open_subst_commute with (n:=0).
      rewrite app_length in IHstp2. simpl in IHstp2.
      assert (forall n, n+1-1=n) as E. intros. omega. rewrite E  in IHstp2.
      eapply IHstp2; eauto.
      eauto. eauto.
Qed.

(* SCRATCH SPACE *)

(*
when and how we can replace with multiple environments:

stp2 G1 T1 G2 T2 (GH0 ++ [(0,vtya GX TX)])

1) T1 closed

   stp2 G1 T1 G2' T2' (subst GH0)

2) G1 contains (GX TX) at some index x1

   index x1 G1 = (GX TX)
   stp2 G (subst (TSel x1) T1) G2' T2'

3) G1 = GX

   stp2 G1 (subst TX T1) G2' T2'

4) G1 and GX unrelated


   stp2 ((GX,TX) :: G1) (subst (TSel (length G1)) T1) G2' T2'

*)


Lemma swap_subst_comm: forall G TX TY,
   (map swap (map (substb TX TY) G)) = (map (substb TY TX) (map swap G)).
Proof.
  intros.
  induction G.
  simpl. eauto.
  simpl. rewrite IHG. remember (map (substb TX TY) (map swap G)) as TL.
  unfold swap. unfold substb. destruct a. simpl.
  destruct p; destruct b; eauto.
Qed.

Lemma swap_if: forall (b:bool) (G1: ty) (G2:ty),
   (if b then G1 else G2) = (if negb b then G2 else G1).
Proof.
  intros. simpl.
  destruct b. eauto. eauto.
Qed.






Lemma closed_subst: forall n x T, closed 1 (n+1) T -> closed 1 (n) (subst (TSel x) T).
Proof. admit. Qed.

Lemma closed_subst2: forall n TX T, closed 1 (n+1) T -> closed 0 0 TX -> closed 1 (n) (subst TX T).
Proof. admit. Qed.

    
Lemma subst_open_commute: forall n TX T2, closed 1 (n+1) T2 -> closed 0 0 TX ->
    subst TX (open (TSelH (n+1)) T2) = open (TSelH n) (subst TX T2).
Proof. admit. Qed.

(*
Lemma closed_open: forall n T, closed 0 0 (open_rec 0 (TSelH n) T).
Proof. admit. Qed.
*)

Lemma Forall2_length: forall A B f (G1:list A) (G2:list B), Forall2 f G1 G2 -> length G1 = length G2.
Proof. admit. Qed.



(* compat helpers --- possible results of substitution, with relation to venv *)

Definition compat (GX:venv) (TX: ty) (G1:venv) (T1:ty) (T1':ty) :=
  (exists x1, index x1 G1 = Some (vty GX TX) /\ T1' = (subst (TSel x1) T1)) \/ 
  (G1 = GX /\ T1' = (subst TX T1)) \/
  (closed 0 0 T1 /\ T1' = T1) \/
  (T1' = subst TTop T1). (* catchall case, this means env doesn't matter *)
                        
Definition check (GX:venv) (TX: ty) (G1:venv) (T1:ty) :=
  (exists x1, index x1 G1 = Some (vty GX TX)) \/ 
  (G1 = GX) \/
  (closed 0 0 T1).


Definition compat2 (GX:venv) (TX: ty) (p1:id*(venv*ty)) (p2:id*(venv*ty)) :=
  match p1, p2 with
      (n1,(G1,T1)), (n2,(G2,T2)) => n1=n2(*+1 disregarded*) /\ G1 = G2 /\ compat GX TX G1 T1 T2
  end.


Lemma compat_all: forall GX TX G1 T1 T2 T1' n,
    compat GX TX G1 (TAll T1 T2) T1' ->
    closed 0 0 TX -> closed 1 (n+1) T2 ->
    exists TA TB, T1' = TAll TA TB /\
                  closed 1 n TB /\
                  compat GX TX G1 T1 TA /\
                  compat GX TX G1 (open (TSelH (n+1)) T2) (open (TSelH n) TB).
Proof.
  intros ? ? ? ? ? ? ? CC CLX CL2. destruct CC.

    simpl in H. destruct H. destruct H. repeat eexists. eauto. eapply closed_subst2. eauto. eauto.  unfold compat. eauto. unfold compat. left. exists x. eauto. rewrite subst_open_commute. eauto. eauto. eauto.

    destruct H. destruct H. simpl in H0. repeat eexists. eauto. eapply closed_subst2. eauto. eauto. unfold compat. eauto. unfold compat. right. left. rewrite subst_open_commute. eauto. eauto. eauto.

    destruct H. destruct H. inversion H. repeat eexists. eauto. subst. eapply closed_upgrade_free. eauto. omega. unfold compat. eauto. unfold compat. eauto. right. right. right. rewrite subst_open_commute. rewrite (closed_no_subst T2 1). eauto. eauto. eauto. eauto.

    simpl in H. repeat eexists. eauto. eapply closed_subst2. eauto. eauto. unfold compat. eauto. unfold compat. eauto. right. right. right. rewrite subst_open_commute. eauto. eauto. eauto.
    Qed.












Lemma stp2_substitute: forall G1 G2 T1 T2 GH,
   stp2 G1 T1 G2 T2 GH ->
   forall GH0 GH0' GX TX T1' T2',
     GH = (GH0 ++ [(0,(GX, TX))]) ->
     closed 0 0 TX ->
     compat GX TX G1 T1 T1' ->
     compat GX TX G2 T2 T2' ->
     Forall2 (compat2 GX TX) GH0 GH0' ->
     stp2 G1 T1'
          G2 T2'
          GH0'.
Proof.
  intros G1 G2 T1 T2 GH H.
  induction H.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - Case "all".
    intros GH0 GH0' GX TX T1' T2' ? CX IX1 IX2 FA.
    
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.
    
    eapply compat_all in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_all in IX2. repeat destruct IX2 as [? IX2].

    subst.
    
    eapply stp2_all. 
    + eapply IHstp2_1. eauto. eauto. eauto. eauto. eauto.
    + eauto.
    + eauto.
    + subst. specialize IHstp2_2 with (GH1 := (0, (G2, T3))::GH0).
      eapply IHstp2_2.
      reflexivity.
      eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto.
    + eauto.
    + eapply closed_upgrade_free. eauto. omega.
    + eauto.
    + eapply closed_upgrade_free. eauto. omega.
Qed.



Lemma stp2_substitute: forall G1 G2 T1 T2 GH,
   stp2 G1 T1 G2 T2 GH ->
   forall GH0 TX x1,
     GH = (GH0 ++ [(0,(false, TX))]) ->
     closed 0 0 TX ->
     index x1 G1 = Some (vty G2 TX) \/ closed 0 0 T1 ->
     stp2 G1 (subst (TSel x1) T1)
          G2 (subst TX T2)
          (map (substb (TSel x1) TX) GH0).
Proof.
  intros G1 G2 T1 T2 GH H.
  induction H.
  - admit.
  - admit.
  - admit.      
  - admit.
  - admit.
  - Case "sela1".

    intros GH0 TXX x1 ? ? IX1.
    subst GH. specialize (indexr_subst2 _ x _ TXX (TSel x1) TXX _ _ H). intros. 
    destruct H1; destruct H1. 
    + destruct H3. subst. simpl. 
      
      specialize (IHstp2 GH0 TX x1).

      eapply stp2_sel1. destruct IX1. eauto. inversion H1. omega.
      simpl. simpl in IHstp2. 
      
      assert (subst (TSel x1) TX = TX). eapply closed_no_subst; eauto.
      rewrite H1 in IHstp2.
      eapply IHstp2. eauto. eauto. eauto.

    + subst. simpl.
      assert (beq_nat x 0 = false). eapply beq_nat_false_iff; omega. rewrite H4. 

      destruct b.
      eapply stp2_sela1. eapply H3. simpl. simpl in IHstp2.
      eapply IHstp2. eauto. eauto. 
      destruct IX1. eauto. inversion H5. omega. simpl. simpl in IX1.
       eapply stp2_sela1. eapply H3. simpl. eapply stp2_substitute_same.

      
      (* simpl. destruct b. *)
      * eapply stp2_sela1. instantiate (2 := true). instantiate (1:= snd (snd (substb (TSel x1) (TSel x2) (x-1,(true,TX))))).
         admit.
         simpl. eapply IHstp2. eauto. eauto. simpl. simpl. destruct bb. simpl. eauto. simpl.
      destruct IX1. eauto. inversion H5. omega. simpl. simpl in IX1.
      destruct IX1. eauto. inversion H5. omega.
      destruct IX2. eauto. eauto.
      * eapply stp2_sela1. instantiate (2 := false). instantiate (1:= snd (snd (substb (TSel x1) (TSel x2) (x-1,(true,TX))))).
        admit.
        simpl. eapply IHstp2. eauto. eauto. simpl. simpl. destruct bb. simpl. eauto. simpl.
      destruct IX1. eauto. inversion H5. omega. simpl. simpl in IX1.
      destruct IX1. eauto. inversion H5. omega.
      destruct IX2. eauto. eauto.
        eauto.


    
  - Case "selx".
    admit.
  - Case "all".
    intros GH0 TX x1 ? CX IX1.
    
    simpl. unfold id in x1. 

    (* lemmas *)
    assert (forall n x T, closed 1 (n+1) T -> closed 1 (n) (subst (TSel x) T)) as closed_subst. admit.

    assert (forall n TX T, closed 1 (n+1) T -> closed 0 0 TX -> closed 1 (n) (subst TX T)) as closed_subst2. admit.

    
    assert (forall n TX T2, closed 1 (n+1) T2 -> closed 0 0 TX ->
    subst TX (open (TSelH (n+1)) T2) = open (TSelH n) (subst TX T2)) as subst_open_commute. admit.

    assert (forall n T, closed 0 0 (open_rec 0 (TSelH n) T)) as
        closed_open. admit.

    
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    
    eapply stp2_all. 
    + (* rewrite swap_subst_comm. simpl in IHstp2_1.
      specialize (IHstp2_1 (map swap GH0) GX TX x2 x1 (negb b)). 
      assert ([(0, (negb b, TX))] = map swap [(0, (b, TX))]).
      eauto.
      
      eapply IHstp2_1. eauto. rewrite H5. rewrite <-map_app. rewrite H3. eauto.
      destruct IX2 as [?|IX2]. eauto. inversion IX2. eauto.
      destruct IX1 as [?|IX1]. eauto. inversion IX1. eauto. *)
      admit. (* contravariant *)
    + simpl. rewrite map_length. eapply closed_subst. unfold id. rewrite <-H4. eauto.
    + simpl. rewrite map_length. eapply closed_subst2. unfold id. rewrite <-H4. eauto. eauto.
    + specialize IHstp2_2 with (GH0:= (0, (false, T3))::GH0)
                                 (TX:= TX)
                                 (x1:=x1)
      .

      rewrite H4 in IHstp2_2. unfold id in IHstp2_2.
      rewrite subst_open_commute in IHstp2_2.
      rewrite subst_open_commute in IHstp2_2.      
      rewrite map_length.
      simpl in IHstp2_2.
      eapply IHstp2_2. subst GH. eauto. eauto.

      destruct IX1 as [IX1|IX1]. eauto. inversion IX1. eauto.
      subst GH. rewrite app_length in H1. simpl in H1. eauto. eauto.
      subst GH. rewrite app_length in H0. simpl in H0. eauto. eauto.
Qed.




    
Lemma stp2_substitute: forall G1 G2 T1 T2 GH,
   stp2 G1 T1 G2 T2 GH ->
   forall GH0 TX x1 x2 b,
     GH = (GH0 ++ [(0,(b, TX))]) ->
     closed 0 0 TX ->
     index x1 G1 = Some (vty (sel b G1 G2) TX) \/ closed 0 0 T1 ->
     index x2 G2 = Some (vty (sel b G1 G2) TX) \/ closed 0 0 T2 ->
     stp2 G1 (subst (TSel x1) T1)
          G2 (subst (TSel x2) T2)
          (map (if b then substb (TSel x1) (TSel x2) else substb (TSel x2) (TSel x1)) GH0).
(* TODO: cases for GX = G1 or GX = G2. asymetric, see below *)
Proof.
  intros G1 G2 T1 T2 GH H.
  induction H.
  - admit.
  - admit.
  - admit.      
  - admit.
  - admit.
  - Case "sela1".
    intros GH0 TXX x1 x2 bb ? ? IX1 IX2.
    destruct bb. admit.
    subst GH. specialize (indexr_subst2 _ x _ TXX (TSel x2) (TSel x1)_ _ H). intros. 
    destruct H1; destruct H1. 
    + destruct H3. subst. simpl. 
      
      specialize (IHstp2 GH0 TX x1 x2 false).

      (* destruct b. *)
      eapply stp2_sel1. destruct IX1. eauto. inversion H1. omega.
      simpl. simpl in IHstp2. 
      
      assert (subst (TSel x1) TX = TX). eapply closed_no_subst; eauto.
      rewrite H1 in IHstp2.
      eapply IHstp2. eauto. eauto. eauto. eauto.

      (*destruct b. eauto. eauto.*)

    + subst. simpl.
      assert (beq_nat x 0 = false). eapply beq_nat_false_iff; omega. rewrite H4. 

      destruct b.
      eapply stp2_sela1. eapply H3. simpl. simpl in IHstp2.
      specialize IHstp2 with (b := false).
      eapply IHstp2.

      
      (* simpl. destruct b. *)
      * eapply stp2_sela1. instantiate (2 := true). instantiate (1:= snd (snd (substb (TSel x1) (TSel x2) (x-1,(true,TX))))).
         admit.
         simpl. eapply IHstp2. eauto. eauto. simpl. simpl. destruct bb. simpl. eauto. simpl.
      destruct IX1. eauto. inversion H5. omega. simpl. simpl in IX1.
      destruct IX1. eauto. inversion H5. omega.
      destruct IX2. eauto. eauto.
      * eapply stp2_sela1. instantiate (2 := false). instantiate (1:= snd (snd (substb (TSel x1) (TSel x2) (x-1,(true,TX))))).
        admit.
        simpl. eapply IHstp2. eauto. eauto. simpl. simpl. destruct bb. simpl. eauto. simpl.
      destruct IX1. eauto. inversion H5. omega. simpl. simpl in IX1.
      destruct IX1. eauto. inversion H5. omega.
      destruct IX2. eauto. eauto.
        eauto.


    
  - admit.
  - Case "all".
    intros GH0 GX TX x1 x2 b ? IX1 IX2.
    
    simpl. unfold id in x1. unfold id in x2.

    (* lemmas *)
    assert (forall n x T, closed 1 (n+1) T -> closed 1 (n) (subst (TSel x) T)) as closed_subst. admit.

    assert (forall n x1 T2, closed 1 (n+1) T2 ->
    subst (TSel x1) (open (TSelH (n+1)) T2) = open (TSelH n) (subst (TSel x1) T2)) as subst_open_commute. admit.

    assert (forall n T, closed 0 0 (open_rec 0 (TSelH n) T)) as
        closed_open. admit.

    
    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    
    eapply stp2_all. 
    + rewrite swap_subst_comm. simpl in IHstp2_1.
      specialize (IHstp2_1 (map swap GH0) GX TX x2 x1 (negb b)). 
      assert ([(0, (negb b, TX))] = map swap [(0, (b, TX))]).
      eauto.
      
      eapply IHstp2_1. eauto. rewrite H5. rewrite <-map_app. rewrite H3. eauto.
      destruct IX2 as [?|IX2]. eauto. inversion IX2. eauto.
      destruct IX1 as [?|IX1]. eauto. inversion IX1. eauto.
    + simpl. rewrite map_length. eapply closed_subst. unfold id. rewrite <-H4. eauto.
    + simpl. rewrite map_length. eapply closed_subst. unfold id. rewrite <-H4. eauto.
    +
      specialize IHstp2_2 with (GH0:= (0, (false, T3))::GH0)
                                 (GX:=GX) (TX:= TX)
                                 (x1:=x1) (x2:=x2) (b:=b)
      .

      rewrite H4 in IHstp2_2. unfold id in IHstp2_2.
      rewrite subst_open_commute in IHstp2_2.
      rewrite subst_open_commute in IHstp2_2.
      rewrite map_length.
      simpl in IHstp2_2.
      eapply IHstp2_2. subst GH. eauto.

      destruct IX1 as [IX1|IX1]. eauto. inversion IX1. eauto.
      destruct IX2 as [IX2|IX2]. eauto. inversion IX2. eauto.
      subst GH. rewrite app_length in H1. simpl in H1. eauto.
      subst GH. rewrite app_length in H0. simpl in H0. eauto.
Qed.


  
Lemma stp2_substitute: forall G1 G2 T1 T2 GH,
   stp2 G1 T1 G2 T2 GH ->
   forall T1X T2X GH0 GH1 GX TX L x1 x2,
     GH1 = (GH0 ++ [(0,vtya GX TX)]) ->
     closed_env GH1 ->
     GH = openm_env GH1 -> 
     L = length GH0 ->
     T1 = openm_rec 0 (L+1) T1X ->
     T2 = openm_rec 0 (L+1) T2X ->
     closed_rec (L+1) 0 T1X ->
     closed_rec (L+1) 0 T2X ->
     index x1 G1 = Some (vty GX TX) \/ closed 0 0 T1X ->
     index x2 G2 = Some (vty GX TX) \/ closed 0 0 T2X ->
     stp2 G1 (openm_rec 0 L (open_rec L (TSel x1) T1X))
          G2 (openm_rec 0 L (open_rec L (TSel x2) T2X))
          (openm_env (open_env GX TX GH0)).
(* TODO: cases for GX = G1 or GX = G2. asymetric, see below *)
Proof.
  intros G1 G2 T1 T2 GH H.
  induction H.
  - admit.
  - admit.
  - admit.      
  - admit.
  - admit.
  - Case "selax".
    intros T1X T2X GH0 GH1 GXX TXX L x1 x2.
    intros EGH2 CGH1 EGH EL MO1 MO2 C1 C2 IX1 IX2.
    unfold id in x.
    
    destruct T1X; inversion MO1; inversion C1; try omega.

    case_eq (beq_nat x 0); intros E.
    + assert (x = 0). eapply beq_nat_true_iff. eauto.
      assert (L = i). omega.
      assert (beq_nat L i = true) as EI. eapply beq_nat_true_iff; eauto.
      
      simpl. simpl in MO1. rewrite EI.
      
      assert (GX = GXX /\ TX = TXX /\ closed_rec 0 0 TXX) as EQ. {
        subst. eapply indexr_hit02 in CGH1. destruct CGH1 as [A B]. rewrite A in H. inversion H. repeat split; eauto. eauto. subst TX. eauto.
      }
      destruct EQ as [EG [ET CT]]. subst GXX TXX.


      assert (TX = (openm_rec 0 L (open_rec L (TSel x1) TX))) as OTX. {
        rewrite <-(closed_no_open TX (TSel x1) 0 L).
        rewrite <-(closed_no_openm TX L 0).
        eauto. eauto. eapply closed_upgrade. eauto. omega.
      }
      idtac.
      destruct IX1 as [IX1|IX1].
      (* index *)
      simpl. eapply stp2_sel1. eapply IX1.
      rewrite OTX.
      eapply IHstp2; try rewrite <- OTX; eauto. rewrite <-(closed_no_openm TX (L+1) 0 0). eauto. eauto. eapply closed_upgrade. eauto. omega.
      (* closed *)
      inversion IX1. omega. (* contra *)
      
    + assert (x <> 0). eapply beq_nat_false_iff; eauto.
      assert (L <> i). unfold not. intros Q. rewrite Q in H2. destruct H6. unfold id. omega.
      assert (L > i). omega.
      assert (beq_nat L i = false) as EI. eapply beq_nat_false_iff; eauto.
      simpl. simpl in MO1. rewrite EI.

      remember (L+0-i-1) as y.
      assert (x=y+1) as EXY. omega.
      rewrite EXY in H. rewrite EGH in H. rewrite EGH2 in H.
      
      eapply indexr_wtf2 in H.
      destruct H as [TXI [? ?]].

      eapply stp2_sela1. subst y. eapply H9.

      eapply IHstp2; eauto.
      
  - Case "selx".
    intros T1X T2X GH0 GX1 TX1 D1 D2 ? MO1 MO2.

    assert (closed_rec (D1+2) 0 T1X) as C1. admit. (* TODO: pass this in *)
    assert (closed_rec (D2+2) 0 T2X) as C2. admit.
    
    destruct T1X; inversion MO1; inversion C1; try omega.
    destruct T2X; inversion MO2; inversion C2; try omega. 

    (* subst. *)

    case_eq (beq_nat x 0); intros E.
    + assert (x = 0). eapply beq_nat_true_iff. eauto.
      assert (D1 = i). omega.
      assert (D2 = i1). omega.
      assert (beq_nat D1 i = true) as E1. eapply beq_nat_true_iff; eauto.
      assert (beq_nat D2 i1 = true) as E2. eapply beq_nat_true_iff; eauto.
      subst.
      simpl. rewrite E1. rewrite E2. simpl. 
      eapply stp2_sel1. eapply index_hit2; eauto. admit. (* closed 0 0 TX1 *)
      eapply stp2_sel2. eapply index_hit2; eauto. admit.
      admit. (* reflexivity:  stp2 GX1 TX1 GX1 TX1 (openm_env (open_env GX1 TX1 GH0)) *)
    + assert (x <> 0). eapply beq_nat_false_iff; eauto.
      assert (x >= 0). omega.
      assert (forall n, n >= 0 -> n <> 0 -> n > 0). intros. omega.
      assert (x > 0). eapply H14; eauto. clear H14.
      assert (D1 > i). omega.
      assert (D2 > i1). omega.
      assert (beq_nat D1 i = false) as E1. eapply beq_nat_false_iff; eauto. omega.
      assert (beq_nat D2 i1 = false) as E2. eapply beq_nat_false_iff; eauto. omega.

      assert (x = (D1 +0 - i - 1) + 1) as E3. subst. admit. (* omega! *)
      assert (x = (D2 +0- i1 - 1) + 1) as E4. subst. admit. (* omega! *)

      rewrite E3 in H.
      rewrite E4 in H0.
      rewrite H1 in H. rewrite H1 in H0.
      eapply indexr_wtf2 with (n:= D1+0-i-1) in H.
      eapply indexr_wtf2 with (n:= D2+0-i1-1) in H0.

      (*      remember *)
      remember (D1+0-i-1) as y.
      assert (D2 + 0-i1-1 = y). subst. admit. (*omega.*)
      simpl. rewrite E1. rewrite E2. simpl. rewrite H17. rewrite <-Heqy.

      destruct H as [TXX [? ?]].
      
      eapply stp2_selx; eauto.
    
  - Case "all".
    intros T1X T2X GH0 GX TX D1 D2 ? MO1 MO2.

    assert (closed_rec (D1+2) 0 T1X) as C1. admit. (* TODO: pass this in *)
    assert (closed_rec (D2+2) 0 T2X) as C2. admit.

    destruct T1X; inversion MO1.
    destruct T2X; inversion MO2.
    
    eapply stp2_all.
    + repeat fold openm_rec. eapply IHstp2_1. eauto. eauto. eauto. 

    + repeat fold openm_rec. repeat fold open_rec. (* repeat rewrite open_more. *)

(*
    (0, vtya G2 T3) :: openm_env 0 (GH0 ++ [(0, vtya GX TX)]) = 
                       openm_env 0 (GH2 ++ [(0, vtya GX TX)])

    --->

    (0, vtya G2 openm_rec 0 0 (S (length GH0)) T2X1 :: openm_env 0 (GH0 ++ [(0, vtya GX TX)]) = 
    openm_env 0 ((0, vtya G2 T2X1)::GH0 ++ [(0, vtya GX TX)])

    --->

    GH2 = (0, vtya G2 T2X1)::GH0

*)
    remember (((0,vtya G2 T2X1)::GH0)) as GH2.
    assert (length GH = length GH0 + 1). { subst. rewrite openm_env_length. eapply app_length. }
    assert (length GH2 = S (length GH0)) as EL. { subst. eauto. }

    assert ((0, vtya G2 (openm_rec 0 (length GH) T2X1)) :: openm_env (GH0 ++ [(0, vtya GX TX)]) =
             openm_env (((0, vtya G2 T2X1) :: GH0) ++ [(0, vtya GX TX)])) as EV1. {
      subst. rewrite (openm_env_length). 
      rewrite openm_env_cons. eauto.
    }
    assert (openm_rec 0 (D2+1) T2X1 = openm_rec 0 (length GH) T2X1) as Q. admit. (* closed *)
    rewrite <-Q in EV1.
    
    specialize IHstp2_2 with (T1X:=T1X2) (T2X:=T2X2) (GH0:=GH2) (GX:=GX) (TX:=TX)
      (D1:= D1) (D2:=D2).
    assert (stp2
              ((fresh G1, vty GX TX) :: G1)
               (openm_rec 0 D1
                          (open_rec D1 (TSel (fresh G1)) T1X2))
               ((fresh G2, vty GX TX) :: G2)
               (openm_rec 0 D2
                          (open_rec D2 (TSel (fresh G2)) T2X2))
               (openm_env (open_env GX TX GH2))) as IH. {
      subst. eapply IHstp2_2. subst. eapply EV1.
      subst. eapply open_more.
      subst. eapply open_more.
    }
    rewrite openm_env_length. rewrite open_env_length. unfold open.
    rewrite open_more. rewrite open_more.

    assert ((openm_env (open_env GX TX GH2)) = ((0,
      vtya ((fresh G2, vty GX TX) :: G2)
        (openm_rec 0 (length GH0) (open_rec (length GH0) (TSel (fresh G2)) T2X1)))
                 :: openm_env (open_env GX TX GH0))) as EV2. {
      subst GH2. 
      unfold open_env. fold open_env. unfold openm_env. fold openm_env.
      rewrite open_env_length.
      eauto.
    }
    rewrite <-EV2. rewrite <- EL.
    eapply IH.
Qed.


Lemma stp2_concretize_aux: forall G1 G2 T1 T2 GH,
   stp2 G1 T1 G2 T2 GH ->
   forall T1X T2X GH0 TX,
   GH = openm_env (GH0 ++ [(0,vtya G2 TX)]) ->
   T1 = openm_rec 0 (length GH) T1X ->
   T2 = openm_rec 0 (length GH) T2X ->
stp2 ((fresh G1, vty G2 TX)::G1) (openm_rec 0 (length GH0) (open_rec (length GH0) (TSel (fresh G1)) T1X))
     G2 (openm_rec 0 (length GH0) (open_rec (length GH0) TX T2X))
     (openm_env (open_env G2 TX GH0)).
Proof.
  admit. (* asymmetric version -- abstract over this *)
Qed.




Lemma stp2_concretize: forall G1 G2 T1X T2X TX,
   stp2 G1 (open (TSelH 0) T1X) G2 (open (TSelH 0) T2X) [(0,vtya G2 TX)] ->
   stp2 ((fresh G1, vty G2 TX)::G1) (open (TSel (fresh G1)) T1X)
     G2 (open TX T2X) [].
Proof.
  admit. (* call aux version above *)
Qed.





(*

Lemma stp2_concretize: forall G1 G2 T1 T2 TX GX GH L,
  stp2 G1 T1 G2 T2 (GH ++ [(0,vtya GX TX)]) ->
  length GH = L ->                       
  closed 0 (fresh GX) TX ->
  (forall x, fresh G1 <= x -> GX = G2 ->
   stp2 ((x,vty GX TX) :: G1) (open_rec L (TSel x) T1) G2 (open_rec L TX T2) GH) /\
  (forall x, fresh G2 <= x -> GX = G1 ->
   stp2 G1 (open_rec L TX T1) ((x,vty GX TX) :: G2) (open_rec L (TSel x) T2) GH) /\
  (forall x, fresh G1 <= x -> closed L (fresh G2) T2 ->
   stp2 ((x,vty GX TX) :: G1) (open_rec L (TSel x) T1) G2 T2 GH) /\
  (forall x, fresh G2 <= x -> closed L (fresh G1) T1 ->
   stp2 G1 T1 ((x,vty GX TX) :: G2) (open_rec L (TSel x) T2) GH) /\
  (GX = G2 -> closed L (fresh G1) T1 ->
   stp2 G1 T1 G2 (open_rec L TX T2) GH) /\
  (GX = G1 -> closed L (fresh G2) T2 ->
   stp2 G1 (open_rec L TX T1) G2 T2 GH) /\
  (closed L (fresh G1) T1 -> closed L (fresh G2) T2 ->
   stp2 G1 T1 G2 T2 GH).
Proof.
  intros.
  remember (GH++[(0,vtya GX TX)]) as GH0.
  assert (forall n1 n2 T, closed 0 n2 T -> closed n1 n2 T). intros. eapply closed_upgrade. eauto. omega.
  subst L.
  generalize dependent GH.
  induction H; intros GH0 ?.
  - Case "1bool". repeat split; intros; eauto. 
  - Case "fun". repeat split; intros.
    eapply stp2_fun. eapply IHstp2_1; eauto. eapply IHstp2_2; eauto.
    eapply stp2_fun. eapply IHstp2_1; eauto. eapply IHstp2_2; eauto.
    inversion H4. subst. eapply stp2_fun. eapply IHstp2_1; eauto. eapply IHstp2_2; eauto.
    inversion H4. eapply stp2_fun. eapply IHstp2_1; eauto. eapply IHstp2_2; eauto.
    inversion H4. eapply stp2_fun. eapply IHstp2_1; eauto. eapply IHstp2_2; eauto.
    inversion H4. eapply stp2_fun. eapply IHstp2_1; eauto. eapply IHstp2_2; eauto.
    inversion H4. inversion H3. eapply stp2_fun. eapply IHstp2_1; eauto. eapply IHstp2_2; eauto.
  - Case "mem". repeat split; intros.
    eapply stp2_mem. eapply IHstp2; eauto.
    eapply stp2_mem. eapply IHstp2; eauto.
    inversion H3. eapply stp2_mem. eapply IHstp2; eauto.
    inversion H3. eapply stp2_mem. eapply IHstp2; eauto.
    inversion H3. eapply stp2_mem. eapply IHstp2; eauto.
    inversion H3. eapply stp2_mem. eapply IHstp2; eauto.
    inversion H3. inversion H0. eapply stp2_mem. eapply IHstp2; eauto.
  - Case "sel1". repeat split; intros.
    eapply stp2_sel1. eapply index_extend; eauto. eauto. eapply IHstp2; eauto. 
    eapply stp2_sel1. eauto. eauto. eapply IHstp2; eauto. 
    eapply stp2_sel1. eapply index_extend; eauto. eauto. eapply IHstp2; eauto.
    eapply stp2_sel1. eauto. eauto. eapply IHstp2; eauto.
    eapply stp2_sel1. eauto. eauto. eapply IHstp2; eauto.
    eapply stp2_sel1. eauto. eauto. eapply IHstp2; eauto.
    eapply stp2_sel1. eauto. eauto. eapply IHstp2; eauto.
  - Case "sel2". repeat split; intros.
    eapply stp2_sel2. eauto. eauto. eapply IHstp2; eauto.
    eapply stp2_sel2. eapply index_extend; eauto. eauto. eapply IHstp2; eauto.
    eapply stp2_sel2. eauto. eauto. eapply IHstp2; eauto.
    eapply stp2_sel2. eapply index_extend; eauto. eauto. eapply IHstp2; eauto.
    eapply stp2_sel2. eauto. eauto. eapply IHstp2; eauto.
    eapply stp2_sel2. eauto. eauto. eapply IHstp2; eauto.
    eapply stp2_sel2. eauto. eauto. eapply IHstp2; eauto.
  - Case "sela1".
    case_eq (beq_nat (length GH0) x); intros E.
    + SCase "hit".
      assert (length GH0 = x). eapply beq_nat_true_iff; eauto. subst x.
      assert (forall x, beq_nat x x = true) as EX. intros. eapply beq_nat_true_iff. eauto.
      assert (forall T, (open_rec (length GH0) T (TSelH (length GH0)) = T)) as OP. unfold open_rec. rewrite E. eauto.
      repeat split; intros.
      * eapply le_xx in H4. destruct H4 as [? LE].
        rewrite OP. 
        eapply stp2_sel1. unfold index. rewrite LE. rewrite EX. eauto. eauto.
        subst. eapply indexr_hit in H. inversion H. subst.
        eapply IHstp2. eauto. eauto. eauto. compute. eauto. 
      * subst. eapply indexr_hit in H. inversion H. subst. rewrite OP.
        eapply IHstp2. eauto. eauto. eauto. eauto.
      * subst. eapply indexr_hit in H. inversion H. subst. rewrite OP.
        eapply le_xx in H4. destruct H4 as [? LE].
        eapply stp2_sel1. unfold index. rewrite LE. rewrite EX. eauto. eauto.
        eapply IHstp2; eauto. eauto.
      * inversion H5. omega. (* contra *)
      * inversion H5. omega. (* contra *)
      * subst. eapply indexr_hit in H. inversion H. subst. rewrite OP.
        eapply IHstp2; eauto. eauto.
      * inversion H4. omega. (* contra *)
    + SCase "miss".
      assert (x < length GH). eapply indexr_max; eauto.
      assert (length GH = length GH0+1). subst GH. eapply app_length. 
      assert (x < length GH0). eapply beq_nat_false_iff in E. omega.
      assert (x <> length GH0). eapply beq_nat_false_iff in E. omega.
      assert (forall n2 T, closed x n2 T -> closed (length GH0) n2 T). intros. eapply closed_upgrade. eauto. omega.

      subst.
      assert (forall T, open_rec (length GH0) T (TSelH x) = (TSelH x)) as OP. unfold open. unfold open_rec. rewrite E. eauto.
      repeat split; intros.
      * try rewrite OP. eapply stp2_sela1; eauto. eapply indexr_miss; eauto. eapply IHstp2; eauto.
      * try rewrite OP. eapply stp2_sela1; eauto. eapply indexr_miss; eauto. eapply IHstp2; eauto.
      * try rewrite OP. eapply stp2_sela1; eauto. eapply indexr_miss; eauto. eapply IHstp2; eauto.
      * try rewrite OP. eapply stp2_sela1; eauto. eapply indexr_miss; eauto. eapply IHstp2; eauto.
      * try rewrite OP. eapply stp2_sela1; eauto. eapply indexr_miss; eauto. eapply IHstp2; eauto.
      * try rewrite OP. eapply stp2_sela1; eauto. eapply indexr_miss; eauto. eapply IHstp2; eauto.
      * try rewrite OP. eapply stp2_sela1; eauto. eapply indexr_miss; eauto. eapply IHstp2; eauto.
  - Case "selx".
    case_eq (beq_nat (length GH0) x); intros E.
    + SCase "hit".
      assert (length GH0 = x). eapply beq_nat_true_iff; eauto. subst x.
      assert (forall x, beq_nat x x = true) as EX. intros. eapply beq_nat_true_iff. eauto.
      assert (forall T, (open_rec (length GH0) T (TSelH (length GH0)) = T)) as OP. unfold open_rec. rewrite E. eauto.
      repeat split; intros.
      * subst. eapply indexr_hit in H. inversion H. subst.
        eapply le_xx in H4. destruct H4 as [? LE].
        repeat rewrite OP. 
        eapply stp2_sel1. unfold index. rewrite LE. rewrite EX. eauto. eauto.        
        eapply stp2_refl; eauto. eauto.
      * subst. eapply indexr_hit in H. inversion H. subst. 
        eapply le_xx in H4. destruct H4 as [? LE].
        repeat rewrite OP.
        eapply stp2_sel2. unfold index. rewrite LE. rewrite EX. eauto. eauto.
        eapply stp2_refl; eauto. eauto.
      * inversion H5. omega. (* contra *)
      * inversion H5. omega. (* contra *)
      * inversion H5. omega. (* contra *)
      * inversion H5. omega. (* contra *)
      * inversion H5. omega. (* contra *)
    + SCase "miss".
      assert (x < length GH). eapply indexr_max; eauto.
      assert (length GH = length GH0+1). subst GH. eapply app_length. 
      assert (x < length GH0). eapply beq_nat_false_iff in E. omega.
      assert (x <> length GH0). eapply beq_nat_false_iff in E. omega.
      assert (forall n2 T, closed x n2 T -> closed (length GH0) n2 T). intros. eapply closed_upgrade. eauto. omega.

      subst.
      assert (forall T, open_rec (length GH0) T (TSelH x) = (TSelH x)) as OP. unfold open. unfold open_rec. rewrite E. eauto.
      repeat split; intros.
      * repeat rewrite OP. eapply stp2_selx; eauto. eapply indexr_miss; eauto. eapply indexr_miss; eauto.
      * repeat rewrite OP. eapply stp2_selx; eauto. eapply indexr_miss; eauto. eapply indexr_miss; eauto.
      * repeat rewrite OP. eapply stp2_selx; eauto. eapply indexr_miss; eauto. eapply indexr_miss; eauto.
      * repeat rewrite OP. eapply stp2_selx; eauto. eapply indexr_miss; eauto. eapply indexr_miss; eauto.
      * repeat rewrite OP. eapply stp2_selx; eauto. eapply indexr_miss; eauto. eapply indexr_miss; eauto.
      * repeat rewrite OP. eapply stp2_selx; eauto. eapply indexr_miss; eauto. eapply indexr_miss; eauto.
      * repeat rewrite OP. eapply stp2_selx; eauto. eapply indexr_miss; eauto. eapply indexr_miss; eauto.
    
  - Case "all".
    assert (open_rec (length GH0) TX T3 = T3) as OP. admit.
    (* SHAKY!! opening with the smaller one may not be true*)
    
    assert (length ((0, vtya G2 T3) :: GH0) = S (length GH0)). eauto.
    
    repeat split; intros.
    + eapply stp2_all.
      repeat fold open_rec. eapply IHstp2_1; eauto. 
      (* repeat fold open_rec. rewrite OP. eauto. admit. (* todo induction *) *)
      eauto.

      repeat fold open_rec.

      remember ((0, vtya G2 T3) :: GH0) as GH1.
      assert ((0, vtya GX T3) :: GH = GH1 ++ [(0, vtya GX TX)]) as EQ.
      subst GH1. subst GH. subst G2. eauto. 
      
      assert ( stp2 ((x, vty GX TX) :: G1) (open_rec ((length GH1)) (TSel x) T2) G2
     (open_rec ((length GH1)) TX T4)  GH1) as IH.

      eapply (IHstp2_2 GH1). eauto. subst G2. eauto. eauto. eauto.
      subst GH1.

      rewrite H3 in IH.
      
      rewrite OP. eapply IH.

    + eapply stp2_all.
      repeat fold open_rec. eapply IHstp2_1; eauto.
      eauto.

      repeat fold open_rec.
    admit.
Qed.

*)


(* --------------------------------- *)


Lemma stp_wf_subst: forall G1 T11 T12 x,
  stp G1 T11 T11 ->
  stp ((x, TMem T11) :: G1) (open (TSel x) T12) (open (TSel x) T12) ->
  stp G1 (open T11 T12) (open T11 T12).
Proof.
  admit.
Qed.


Lemma has_type_wf: forall G1 t T,
  has_type G1 t T ->
  stp G1 T T.
Proof.
  intros. induction H.
  - Case "true". eauto.
  - Case "false". eauto.
  - Case "var". eauto.
  - Case "app".
    assert (stp env (TFun T1 T2) (TFun T1 T2)) as WF. eauto.
    inversion WF. eauto.
  - Case "abs".
    eauto.
  - Case "tapp".
    assert (stp env (TAll T11 T12) (TAll T11 T12)) as WF. eauto.
    inversion WF. subst. eapply stp_wf_subst; eauto.
  - Case "tabs".
    eauto.
Qed.


Lemma sub_env_fresh {X}: forall (G1: list(id*X)) G2,
  sub_env G1 G2 -> fresh G1 <= fresh G2.
Proof.
  intros. induction H. eauto.
  assert ((fresh ((x, v) :: G2)) = 1+x). eauto. rewrite H1. omega.
Qed.



Lemma stp_splice: forall x v G1 G2 G1' G2' T1 T2 GH,
  stp2 ((x,v)::G1) (open (TSel x) T1) ((x,v)::G2) (open (TSel x) T2) GH ->
  sub_env G1 G1' ->
  sub_env G2 G2' ->
  fresh G1' <= x ->
  fresh G2' <= x ->
  stp2 ((x,v)::G1') (open (TSel x) T1) ((x,v)::G2') (open (TSel x) T2) GH.
Proof.
  (* not clear if this is any easier to prove ... *)
  admit.
Qed.


(* TODO *)
Lemma stp_to_stp2: forall G1 T1 T2,
  stp G1 T1 T2 ->
  forall GX, wf_env GX G1 -> 
  stp2 GX T1 GX T2 [].
Proof. admit. Qed.

(*
Lemma stp_to_stp2: forall G1 G2 T1 T2,
  stp G2 T1 T2 ->
  sub_env G1 G2 ->                   
  forall GX GH, wf_env GX G1 -> wf_envh GH G2 ->
  stp2 GX T1 GX T2 GH.
Proof.
  intros G1 G2  T1 T2 ST SE. induction ST; intros GX GH WX WH.
  - Case "bool". eauto.
  - Case "fun". eauto.
  - Case "mem". eauto.
  - Case "sel1". 
    assert (exists v : vl, index x GX = Some v /\ val_type GX v (TMem T)) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? VT]].
    inversion VT; try solve by inversion; subst.
    eapply stp2_sel1; eauto. inversion H2. subst. eauto. 
    eapply stp2_sela1; eauto. inversion H2. subst. eauto. 
  - Case "selx". eauto.
    assert (exists v : vl, index x GX = Some v /\ val_type GX v (TMem T)) as A.
    eapply index_safe_ex. eauto. eauto.
    destruct A as [? [? VT]].
    inversion VT; try solve by inversion; subst.
    eapply stp2_sel2. eauto. eapply stp2_sel1. eauto. 
    inversion H2. subst.
    eapply stp2_reg1. eauto.
    eapply stp2_selx. eauto. eauto. 
  - Case "all".
    eapply stp2_all. eauto. intros.
    assert (fresh GX <= fresh G1'). eapply sub_env_fresh; eauto.
    assert (fresh GX = fresh G1). eauto.
    assert (forall x, fresh G1 <= x -> stp2 ((x, vtya GX T3)::GX) (open (TSel x) T2) ((x, vtya GX T3)::GX) (open (TSel x) T4)). intros. eapply H0. eauto. eauto.
    econstructor. econstructor. eapply W.
    eapply stp2_mem. eapply stp2_extend2. eapply stp2_reg1. eauto. omega. eauto.

    eapply stp_splice. eapply H8. omega. eauto. eauto. omega. omega.
Qed.
*)

Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stp2 H1 T1 H2 T2 [] ->
  val_type H2 vf T2.
Proof.
  intros. inversion H; econstructor; eauto; eapply stp2_trans; eauto.
Qed.


Lemma invert_abs: forall venv vf T1 T2,
  val_type venv vf (TFun T1 T2) ->
  exists env tenv f x y T3 T4,
    vf = (vabs env f x y) /\
    fresh env <= f /\
    1 + f <= x /\
    wf_env env tenv /\
    has_type ((x,T3)::(f,TFun T3 T4)::tenv) y T4 /\
    stp2 venv T1 env T3 [] /\
    stp2 env T4 venv T2 [].
Proof.
  intros. inversion H; try solve by inversion. inversion H4. subst. repeat eexists; repeat eauto.
Qed.

Lemma invert_tabs: forall venv vf T1 T2,
  val_type venv vf (TAll T1 T2) ->
  exists env tenv x y T3 T4,
    vf = (vtabs env x T3 y) /\
    fresh env = x /\
    wf_env env tenv /\
    has_type ((x,TMem T3)::tenv) y (open (TSel x) T4) /\
    stp2 venv T1 env T3 [] /\
    stp2 ((x,vty venv T1)::env) (open (TSel x) T4) venv (open T1 T2) [].
Proof.
  intros. inversion H; try solve by inversion. inversion H3. subst. repeat eexists; repeat eauto.
  remember (fresh venv1) as x.
  remember (x + fresh venv0) as xx.

  (* inversion of TAll < TAll *)
  assert (stp2 venv0 T1 venv1 T0 []). eauto.
  assert (stp2 venv1 (open (TSelH 0) T3) venv0 (open (TSelH 0) T2) [(0,vtya venv0 T1)]). {
    eapply H15.
  }
  
  (* now rename *)
  
  assert (stp2 ((fresh venv1,vty venv0 T1) :: venv1) (open_rec 0 (TSel (fresh venv1)) T3)
               venv0 (open T1 T2) []). {
    eapply stp2_concretize; eauto.
  }

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
  (* S n *) intros. destruct e; inversion H; inversion H0.
  
  Case "True".  eapply not_stuck. eapply v_bool; eauto.
  Case "False". eapply not_stuck. eapply v_bool; eauto.

  Case "Var".
    destruct (index_safe_ex venv0 tenv0 T i) as [v [I V]]; eauto. 

    rewrite I. eapply not_stuck. eapply V.

  Case "App".
    remember (teval n venv0 e1) as tf.
    remember (teval n venv0 e2) as tx. 
    subst T.
    
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
        (* wf_env f x *) econstructor. eapply valtp_widen; eauto. eapply stp2_extend2. eapply stp2_extend2. eauto. eauto. eauto. 
        (* wf_env f   *) econstructor. eapply v_abs; eauto. eapply stp2_extend2. eapply stp2_fun. eapply stp2_reg2. eauto. eapply stp2_reg1. eauto. eauto.
        eauto. 

    inversion HRY as [? vy].

    eapply not_stuck. eapply valtp_widen; eauto. eapply stp2_extend1. eapply stp2_extend1. eauto. eauto. eauto.
    
  Case "Abs". intros. inversion H. inversion H0.
    subst. inversion H19. subst.
    eapply not_stuck. eapply v_abs; eauto. rewrite (wf_fresh venv0 tenv0 H1). eauto. eapply stp_to_stp2. eauto. eauto. 

  Case "TApp".
    remember (teval n venv0 e) as tf.
    subst T.

    destruct tf as [rf|]; try solve by inversion.  
    assert (res_type venv0 rf (TAll T11 T12)) as HRF. SCase "HRF". subst. eapply IHn; eauto.
    inversion HRF as [? vf].

    subst t.
    destruct (invert_tabs venv0 vf T11 T12) as
        [env1 [tenv [x0 [y0 [T3 [T4 [EF [FRX [WF [HTY [STX STY]]]]]]]]]]]. eauto.
    (* now we know it's a closure, and we have has_type evidence *)

    assert (res_type ((x0,vty venv0 T11)::env1) res (open (TSel x0) T4)) as HRY.
      SCase "HRY".
        subst. eapply IHn. eauto. eauto.
        (* wf_env x *) econstructor. eapply v_ty. 
        (* wf_env   *) eauto.
    eapply stp2_extend2. eapply stp2_mem. eauto. eauto.
    eauto.
    inversion HRY as [? vy].

    eapply not_stuck. eapply valtp_widen; eauto.

  Case "TAbs". intros. inversion H. inversion H0.
    subst. inversion H17. subst.
    eapply not_stuck. eapply v_tabs; eauto. (* rewrite (wf_fresh venv0 tenv0 H1).*) eauto. eapply stp_to_stp2. eauto. eauto. 
    
Qed.

End STLC.