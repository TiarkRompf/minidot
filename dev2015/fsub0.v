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

Fixpoint length {X: Type} (l : list X): nat :=
  match l with
    | [] => 0
    | _::l' => 1 + length l'
  end.

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

(*
Fixpoint update {X : Type} (n : nat) (x: X)
               (l : list X) { struct l }: list X :=
  match l with
    | [] => []
    | a :: l'  => if beq_nat n (length l') then x::l' else a :: update n x l'
  end.
*)

Inductive sub_env: tenv -> tenv -> Prop :=
| se_refl: forall G,
    sub_env G G
| se_ext:  forall G1 G2 x,
    sub_env G1 G2 ->
    sub_env G1 (x::G2)
.




(* LOCALLY NAMELESS *)

Inductive closed_rec: nat -> ty -> Prop :=
| cl_top: forall k,
    closed_rec k TTop
| cl_bool: forall k,
    closed_rec k TBool
| cl_fun: forall k T1 T2,
    closed_rec k T1 ->
    closed_rec k T2 ->
    closed_rec k (TFun T1 T2)
| cl_mem: forall k T1,
    closed_rec k T1 ->
    closed_rec k (TMem T1)
| cl_meme: forall k T1,
    closed_rec k T1 ->
    closed_rec k (TMemE T1)
| cl_bind: forall k T1 T2,
    closed_rec k T1 ->
    closed_rec (S k) T2 ->
    closed_rec k (TAll T1 T2)
| cl_sel: forall k x,
    closed_rec k (TSel x)
| cl_selb: forall k i,
    k > i ->
    closed_rec k (TSelB i)
.

Hint Constructors closed_rec.

Definition closed j T := closed_rec j T.


Fixpoint open_rec (k: nat) (u: ty) (T: ty) { struct T }: ty :=
  match T with
    | TSel x      => TSel x (* free var remains free. functional, so we can't check for conflict *)
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


Lemma closed_no_open: forall T x j,
  closed_rec j T ->
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

Lemma closed_upgrade: forall i j T,
 closed_rec i T ->
 j >= i ->
 closed_rec j T.
Proof.
 intros. generalize dependent j. induction H; intros; eauto.
 Case "TBind". econstructor. eapply IHclosed_rec1. omega. eapply IHclosed_rec2. omega.
 Case "TSelB". econstructor. omega.
Qed.


Hint Unfold open.
Hint Unfold closed.


Inductive stp: tenv -> ty -> ty -> Prop :=
| stp_fun: forall G1 T1 T2 T3 T4,
    stp G1 T3 T1 ->
    stp G1 T2 T4 ->
    stp G1 (TFun T1 T2) (TFun T3 T4)             
| stp_mem: forall G1 T1 T2,
    stp G1 T1 T2 ->
    stp G1 (TMem T1) (TMem T2)         
| stp_sel1: forall G1 T x,
    index x G1 = Some (TMem T) ->
    stp G1 (TSel x) T
| stp_selx: forall G1 x,
    stp G1 (TSel x) (TSel x)
| stp_all: forall G1 T1 T2 T3 T4,
    stp G1 T3 T1 ->
    stp ((fresh G1,TMem T3)::G1) (open (TSel (fresh G1)) T2) (open (TSel (fresh G1)) T4) ->
    stp G1 (TAll T1 T2) (TAll T3 T4)
.
(* TODO *)

Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           index x env = Some T1 ->
           has_type env (tvar x) T1
| t_app: forall env f x T1 T2,
           has_type env f (TFun T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
| t_abs: forall env f x y T1 T2,
           has_type ((x,T1)::(f,TFun T1 T2)::env) y T2 ->
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
           fresh env <= x ->
           has_type env (ttabs x T1 y) (TAll T1 T2)
(* TODO: subsumption *)
.


Inductive stp2: venv -> ty -> venv -> ty -> Prop :=
| stp2_bool: forall G1 G2,
    stp2 G1 TBool G2 TBool
| stp2_fun: forall G1 G2 T1 T2 T3 T4,
    stp2 G2 T3 G1 T1 ->
    stp2 G1 T2 G2 T4 ->
    stp2 G1 (TFun T1 T2) G2 (TFun T3 T4)             
| stp2_mem: forall G1 G2 T1 T2,
    stp2 G1 T1 G2 T2 ->
    stp2 G1 (TMem T1) G2 (TMem T2)         

| stp2_sel1: forall G1 G2 GX TX x T2,
    index x G1 = Some (vty GX TX) ->
    stp2 GX TX G2 T2 ->
    stp2 G1 (TSel x) G2 T2

| stp2_sel2: forall G1 G2 GX TX x T1,
    index x G1 = Some (vty GX TX) ->
    stp2 G1 T1 GX TX ->
    stp2 G1 T1 G2 (TSel x)

(* X<T, one sided *)
| stp2_sela1: forall G1 G2 GX TX x T2,
    index x G1 = Some (vtya GX TX) ->
    stp2 GX TX G2 T2 ->
    stp2 G1 (TSel x) G2 T2

         
| stp2_selx: forall G1 G2 GX TX x y,
    index x G1 = Some (vtya GX TX) ->
    index y G2 = Some (vtya GX TX) ->
    stp2 G1 (TSel x) G2 (TSel y)


| stp2_all: forall G1 G2 T1 T2 T3 T4,
    stp2 G2 T3 G1 T1 ->
    (* watch out -- we put X<:T in the env, not X=T *)
    stp2 ((fresh G1,vtya G2 T3)::G1) (open (TSel (fresh G1)) T2)
         ((fresh G2,vtya G2 T3)::G2) (open (TSel (fresh G2)) T4) ->
    stp2 G1 (TAll T1 T2) G2 (TAll T3 T4)

(*         
| stp2_all: forall G1 G2 T1 T2 T3 T4 ok,
    stp2 G2 T3 G1 T1 ->
    (* watch out -- we put X<:T in the env, not X=T *)
    (forall (x:id), ok x ->
    stp2 ((vtya G2 T3)::G1) (open (TSel (length G1)) T2)
         ((vtya G2 T3)::G2) (open (TSel (length G2)) T4)) ->
    stp2 G1 (TAll T1 T2) G2 (TAll T3 T4)
 *)
(*
narrowing: need to prevent accidental bindings.
perhaps:
- add a name to vtya
- pick a fresh one (not used in either G1,G2)
*)
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
    stp2 venv (TMem T1) env TE ->
    val_type env (vty venv T1) TE
| v_bool: forall venv b TE,
    stp2 [] TBool venv TE ->
    val_type venv (vbool b) TE
| v_abs: forall env venv tenv f x y T1 T2 TE,
    wf_env venv tenv ->
    has_type ((x,T1)::(f,TFun T1 T2)::tenv) y T2 ->
    fresh venv <= f ->
    1 + f <= x ->
    stp2 venv (TFun T1 T2) env TE -> 
    val_type env (vabs venv f x y) TE
| v_tabs: forall env venv tenv x y T1 T2 TE,
    wf_env venv tenv ->
    has_type ((x,TMem T1)::tenv) y (open (TSel x) T2) ->
    fresh venv <= x ->
    stp2 venv (TAll T1 T2) env TE ->
    val_type env (vtabs venv x T1 y) TE
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

Lemma le_xx : forall a b,
                       a <= b ->
                       exists E, le_lt_dec a b = left E.
Proof. intros.
  case_eq (le_lt_dec a b). intros. eauto.
  intros. omega.     
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


Lemma stp_extend : forall x v1 G1 T1 T2,
                       stp G1 T1 T2 ->
                       fresh G1 <= x ->
                       stp ((x,v1)::G1) T1 T2.
Proof. intros. induction H; eauto.
       eapply stp_sel1. eapply index_extend; eauto.
admit. (* TAll *)
Qed.

Lemma stp2_extend2 : forall x v1 G1 G2 T1 T2,
                       stp2 G1 T1 G2 T2 ->
                       fresh G2 <= x ->
                       stp2 G1 T1 ((x,v1)::G2) T2.
Proof. admit. Qed.

Lemma stp2_extend1 : forall x v1 G1 G2 T1 T2,
                       stp2 G1 T1 G2 T2 ->
                       fresh G1 <= x ->
                       stp2 ((x,v1)::G1) T1 G2 T2.
Proof. admit. Qed.

Lemma stp2_reg2 : forall G1 G2 T1 T2,
                       stp2 G1 T1 G2 T2 ->
                       stp2 G2 T2 G2 T2.
Proof. admit. Qed.

Lemma stp2_reg1 : forall G1 G2 T1 T2,
                       stp2 G1 T1 G2 T2 ->
                       stp2 G1 T1 G1 T1.
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


Lemma stp2_trans: forall G1 G2 G3 T1 T2 T3,
  stp2 G1 T1 G2 T2 ->
  stp2 G2 T2 G3 T3 ->
  stp2 G1 T1 G3 T3.
Proof. admit. Qed.

(* used in trans -- need to generalize interface for induction *)
Lemma stp2_narrow: forall x G1 G2 G3 G4 T1 T2 T3 T4,
  stp2 G1 T1 G2 T2 ->
  stp2 ((x,vtya G2 T2)::G3) T3 ((x,vtya G2 T2)::G4) T4 ->
  stp2 ((x,vtya G1 T1)::G3) T3 ((x,vtya G1 T1)::G4) T4.
Proof. admit. Qed.

(* used in inversion *)
Lemma stp2_narrow_concrete: forall x G2 G3 G4 T2 T3 T4,
  stp2 ((x,vtya G2 T2)::G3) T3 ((x,vtya G2 T2)::G4) T4 ->
  stp2 ((x,vty G2 T2)::G3) T3 ((x,vty G2 T2)::G4) T4.
Proof.
  admit.
  (* selx becomes sel1/sel2 *)
Qed.

(* stp_subst *)
Lemma stp2_subst: forall x G1 T1 G2 T2 TX,
  stp2 G1 T1 ((x,vty G2 TX) :: G2) (open (TSel (length G2)) T2) ->
  stp2 G1 T1 ((x,vty G2 TX) :: G2) (open TX T2).
Proof.
  admit.
Qed.




Lemma stp_to_stp2: forall G H T1 T2,
  wf_env H G ->
  stp G T1 T2 ->
  stp2 H T1 H T2.
Proof.
  intros. inversion H1. eauto.
  - Case "fun". admit.
  - Case "mem". admit.
  - Case "sel1". 
  assert (exists v : vl, index x H = Some v /\ val_type H v (TMem T2)) as A.
    eapply index_safe_ex. eauto. eauto.
  destruct A as [? [? VT]].
  inversion VT; try solve by inversion.  subst.
    
  eapply stp2_sel1; eauto. inversion H8. subst. eauto.
  - Case "selx". admit.
  - Case "all". admit.
Qed.

Lemma valtp_widen: forall vf H1 H2 T1 T2,
  val_type H1 vf T1 ->
  stp2 H1 T1 H2 T2 ->
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
    stp2 venv T1 env T3 /\
    stp2 env T4 venv T2.
Proof.
  intros. inversion H; try solve by inversion. inversion H4. subst. repeat eexists; repeat eauto.
Qed.

Lemma invert_tabs: forall venv vf T1 T2,
  val_type venv vf (TAll T1 T2) ->
  exists env tenv x y T3 T4,
    vf = (vtabs env x T3 y) /\
    fresh env <= x /\
    wf_env env tenv /\
    has_type ((x,TMem T3)::tenv) y (open (TSel x) T4) /\
    stp2 venv T1 env T3 /\
    stp2 ((x,vty venv T1)::env) (open (TSel x) T4) venv (open T1 T2).
Proof.
  intros. inversion H; try solve by inversion. inversion H3. subst. repeat eexists; repeat eauto.
  admit.
  (*
  remember fresh
  (* inversion of TAll < TAll *)
  assert (stp2 venv0 T1 venv1 T0). eauto.
  assert (stp2 ((x,vtya venv0 T1) :: venv1) (open (TSel x) T3)
               ((x,vtya venv0 T1) :: venv0) (open (TSel x) T2)). eauto.

  (* narrow vtya to vty: X<T to X=T *)
  assert (stp2 ((x,vty venv0 T1) :: venv1) (open (TSel x) T3)
               ((x,vty venv0 T1) :: venv0) (open (TSel x) T2)). eapply stp2_narrow_concrete. eauto.

  (* substitute *)
  assert (stp2 ((x,vty venv0 T1) :: venv1) (open (TSel x) T3)
               ((x,vty venv0 T1) :: venv0) (open T1 T2)).
  eapply stp2_subst. eauto.
  
  (* smaller env -- ok because val_type venv vf (TAll T1 T2) *)
  assert (stp2 ((x,vty venv0 T1) :: venv1) (open (TSel x) T3)
               venv0 (open T1 T2)). admit.

  assert (fresh tenv0 = fresh venv1) as E. eapply wf_fresh.
  rewrite <- E. eauto.*)
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
    subst. inversion H12. subst.
    eapply not_stuck. eapply v_abs; eauto. rewrite (wf_fresh venv0 tenv0 H1). eauto. admit. (* has_type_ef *)

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
    subst. inversion H14. subst.
    eapply not_stuck. eapply v_tabs; eauto. rewrite (wf_fresh venv0 tenv0 H1). eauto. admit. (* has_type_wf *)
    
Qed.

End STLC.