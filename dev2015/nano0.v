(* Full safety for STLC *)


Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Module STLC.

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.y *)
.

Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty.

Hint Unfold venv.
Hint Unfold tenv.

Fixpoint length {X: Type} (l : list X): nat :=
  match l with
    | [] => 0
    | _::l' => 1 + length l'
  end.

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.


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
| t_abs: forall env y T1 T2,
           has_type (T1::(TFun T1 T2)::env) y T2 -> 
           has_type env (tabs y) (TFun T1 T2)
.

Inductive wf_env : venv -> tenv -> Prop := 
| wfe_nil : wf_env nil nil
| wfe_cons : forall v t vs ts,
    val_type v t ->
    wf_env vs ts ->
    wf_env (cons v vs) (cons t ts)

with val_type : vl -> ty -> Prop :=
| v_bool: forall b,
    val_type (vbool b) TBool
| v_abs: forall venv tenv y T1 T2,
    wf_env venv tenv ->
    has_type (T1::(TFun T1 T2)::tenv) y T2 ->
    val_type (vabs venv y) (TFun T1 T2)
.




(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)

Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (index x env)
        | tabs y     => Some (Some (vabs env y))
        | tapp ef ex   =>
          match teval n env ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 ey)) =>
              match teval n env ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n (vx::(vabs env2 ey)::env2) ey
              end
          end
      end
  end.

(* Here is a possible way to use DO notion for cleaner syntax: *)

Notation "'RES' x" := (Some x) (right associativity, at level 60).
Notation "'VAL' x" := (Some x) (right associativity, at level 60).

Definition STUCK: option (option vl) := Some (None).
Definition TIMEOUT: option (option vl) := None.

Notation "'DO1' x <== e1 ; e2" 
   := (match e1 with
         | Some x => e2
         | _ => None
       end)
   (right associativity, at level 60).

Notation "'DO' x <== e1 ; e2" 
   := (match e1 with
         | Some (Some x) => e2
         | Some _ => Some None
         | None => None
       end)
   (right associativity, at level 60).


Notation "'FUEL' n <== e1 ; e2" 
   := (match e1 with
         | 0 => TIMEOUT
         | S n => e2
       end)
   (right associativity, at level 60).

Notation "'DO' n <== 'FUEL' e1 ; e2"
   := (match e1 with
         | 0 => TIMEOUT
         | S n => e2
       end)
   (right associativity, at level 60).


Fixpoint eval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  DO n1 <== FUEL n; 
  match t with
    | ttrue      => RES VAL (vbool true)
    | tfalse     => RES VAL (vbool false)
    | tvar x     => RES (index x env)
    | tabs y     => RES VAL (vabs env y)
    | tapp ef ex =>
      DO vf <== eval n1 env ef;
        DO vx <==  eval n1 env ex;
        match vf with
          | (vabs env2 ey) =>
            eval n1 (vx::(vabs env2 ey)::env2) ey
          | _ => STUCK
        end
  end.

(* end notation *)


Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
Hint Constructors val_type.
Hint Constructors wf_env.

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.

Lemma wf_length : forall vs ts,
                    wf_env vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
  assert ((length (v::vs)) = 1 + length vs). constructor.
  assert ((length (t::ts)) = 1 + length ts). constructor.
  rewrite IHwf_env in H1. auto.
Qed.

Hint Immediate wf_length.

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


Lemma index_safe_ex: forall H1 G1 TF i,
             wf_env H1 G1 ->
             index i G1 = Some TF ->
             exists v, index i H1 = Some v /\ val_type v TF.
Proof. intros. induction H.
       Case "nil". inversion H0.
       Case "cons". inversion H0.
         case_eq (beq_nat i (length ts)).
           SCase "hit".
             intros E.
             rewrite E in H3. inversion H3. subst t.
             assert (beq_nat i (length vs) = true). eauto.
             assert (index i (v :: vs) = Some v). eauto.  unfold index. rewrite H2. eauto.
             eauto.
           SCase "miss".
             intros E.
             assert (beq_nat i (length vs) = false). eauto.
             rewrite E in H3.
             assert (exists v0, index i vs = Some v0 /\ val_type v0 TF) as HI. eapply IHwf_env. eauto.
           inversion HI as [v0 HI1]. inversion HI1. 
           eexists. econstructor. eapply index_extend; eauto.  eauto.
Qed.

  


(* if not a timeout, then result not stuck and well-typed *)

Theorem full_safety : forall n e tenv venv res T,
  teval n venv e = Some res -> has_type tenv e T -> wf_env venv tenv ->
  exists v, res = Some v /\ val_type v T.

Proof.
  intros n. induction n.
  (* 0   *) intros. inversion H.
  (* S n *) intros. destruct e; inversion H; inversion H0.
  
  Case "True".  eexists. split. eauto. eapply v_bool.
  Case "False". eexists. split. eauto. eapply v_bool.

  Case "Var".
    destruct (index_safe_ex venv0 tenv0 T i) as [v IV]. eauto. eauto. 
    inversion IV as [I V]. 

    rewrite I. eexists. split. eauto. eapply V.

  Case "App". 
    remember (teval n venv0 e1) as tf. (* not stuck *)
    remember (teval n venv0 e2) as tx. 
    subst T.
    
    destruct tf as [rf|]; destruct tx as [rx|]; try solve by inversion.

    assert (exists vf, rf = Some vf /\ val_type vf (TFun T1 T2)) as HRF. subst. eapply IHn; eauto.
    inversion HRF as [vf [EF HVF]].
    inversion HVF. (* now we know it's a closure, and we have has_type evidence *)
    
    assert (exists vx, rx = Some vx /\ val_type vx T1) as HRX. subst. eapply IHn; eauto.
    inversion HRX as [vx [EX HVX]].

    subst. eapply IHn; eauto. (* body *)
    
    (* other case: tx = None *)
    assert (exists vf, rf = Some vf /\ val_type vf (TFun T1 T2)) as HRF. subst. eapply IHn; eauto.

    inversion HRF as [vf [EF HVF]]. subst. inversion HVF. subst. inversion H3. (* contradiction *)

    
  Case "Abs". 
    eexists. split. eauto. eapply v_abs; eauto.
Qed.

End STLC.