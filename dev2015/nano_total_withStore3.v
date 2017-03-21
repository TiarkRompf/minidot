(* Full safety for STLC *)

(* copied from nano0.v *)

(* This version prohibits recursion, and we prove that   *)
(* evaluation always terminates with a well-typed value. *)
(* From this follows both type soundness and strong      *)
(* normalization for STLC.                               *)

Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.

Module STLC.

Definition id := nat.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tref : tm -> tm
  | tapp : tm -> tm -> tm (* f(x) *)
  | tabs : tm -> tm (* \f x.y *)
.


Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : list vl -> tm -> vl
| vref  : nat -> vl
.


Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> ty -> ty
  | TRef   : ty -> ty
.

Definition venv := list vl.
Definition tenv := list ty.
Definition store := list vl.
Definition Gamma := list ty.
Definition rho   := list nat.
Definition location := nat.


Hint Unfold store.
Hint Unfold Gamma.
Hint Unfold rho.


Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

(*
Fixpoint indexd {K : Type} (n : id) (l : rho) (M: list K) : option K :=
  match (index n l) with
    | None => None
    | Some (x) => index x M
  end.
*)

Inductive has_type : Gamma -> tm -> ty -> Prop :=
| t_true: forall env,
           has_type env ttrue TBool
| t_false: forall env,
           has_type env tfalse TBool
| t_var: forall x env T1,
           index x env = Some T1 ->
           has_type env (tvar x) T1
| t_ref: forall e env T1,
           has_type env e T1 ->
           has_type env (tref e) (TRef T1)
| t_app: forall env f x T1 T2,
           has_type env f (TFun T1 T2) ->
           has_type env x T1 ->
           has_type env (tapp f x) T2
| t_abs: forall env y T1 T2,
           has_type (T1::env) y T2 -> 
           has_type env (tabs y) (TFun T1 T2)
.


(*
None             means timeout
Some None        means stuck
Some (Some v))   means result v
*)


Fixpoint itype (k:nat) : Type := 
 match k with 
  | 0    => unit
  | S k' => prodT (itype k') ((list (itype k')) -> store -> vl -> Prop)
 end.


Definition imemtype k : Type := list (itype k).

Definition type  : Type := forall (k : nat), (itype k).


(* Definition : belong to a type *)
Definition beIn (j k:nat) : Type := (lt j k) -> (imemtype j * store * vl) -> (itype k) -> Prop .

Lemma xx: forall j, j < 0 -> False. intros. omega. Defined.
Lemma yy: forall j k, j < S k -> ~ j < k -> j = k. intros. omega. Qed.
Lemma zz k: k < (S k). Proof. auto. Defined.
Lemma ww: forall k, k < k -> False. intros. omega. Defined.

Lemma In j k : beIn j k.
Proof.
  intros. revert j. induction k.
  unfold beIn. intros. apply xx in H. contradiction.
  unfold beIn. intros. 
  unfold beIn in IHk. destruct (lt_dec j k). eapply IHk.
  eassumption. eassumption. eapply (fst X0).
  assert (j = k). apply yy; assumption. subst j.
  eapply (snd X0). eapply (fst X). eapply (fst X). eapply X.
Defined.


(*Definition 1 Approx*)
Definition itype_approx (j k : nat) : Type := lt j k -> itype k -> itype j.

Definition imemtype_approx (j k : nat) : Type := lt j k -> imemtype k -> imemtype j.

Lemma ApproxT j k: itype_approx j k.
Proof.
  intros. revert j. 
  induction k. 
  unfold itype_approx. intros. apply xx in H. contradiction.
  unfold itype_approx. intros. 
  unfold itype_approx in IHk.
  destruct (lt_dec j k). eapply IHk. auto. simpl in X.  eapply (fst X).
  assert (j = k). apply yy; assumption. subst j. eapply (fst X). 
Defined.


Definition ApproxMem j k : imemtype_approx j k :=
  fun (a : (lt j k)) (psi_k : imemtype k) => 
    map (ApproxT j k a) psi_k
.

(* Definition 2 Well-typed Memory *)
Definition imemtype_sat (k: nat) (psi: imemtype k) (M: store) : Prop :=
  length psi = length M /\ 
  (forall j l (a : lt j k), l < (length psi) -> 
    match index l psi, index l M  with
    | Some tau, Some v => In j k a (ApproxMem j k a psi, M, v) tau
    | _,_ => False
    end
  )
.



(* Definition 3 Memory Extension *)
Definition MemoryEx (k: nat)(psi1 : imemtype k)(M1 : store)(psi2: imemtype k) (M2 : store) : Prop :=
  imemtype_sat k psi1 M1 /\ imemtype_sat k psi2 M2 /\
  forall l, l < length psi1 -> index l psi1 = index l psi2 /\ index l M1 = index l M2
.

Definition MemoryExLt (k: nat)(psi1 : imemtype k)(M1 : store)(j: nat)(psi2: imemtype j) (M2 : store) : Prop :=
  forall (a: j < k),
  imemtype_sat j (ApproxMem j k a psi1) M1 /\ imemtype_sat j psi2 M2 /\
  forall l, l < length psi1 -> index l (ApproxMem j k a psi1) = index l psi2 /\ index l M1 = index l M2
.

(* Note: def from paper requires j <= k. Not sure if needed here. *)


Lemma MemoryEx_refl: forall k psi M, imemtype_sat k psi M -> 
                                     MemoryEx k psi M psi M.
Proof.
  intros. unfold MemoryEx. split. assumption. split. assumption.
  intros. split; reflexivity.
Qed.


(* Definition 4 Type *)

Definition typeP (k :nat)(tau : itype k) : Prop := 
forall j (psi: imemtype j) M v (a : lt j k), In j k a (psi, M, v) tau ->
  imemtype_sat j psi M /\ 
  forall (psi2: imemtype j) (M2 : store), 
    MemoryEx j psi M psi2 M2 -> In j k a (psi2, M2, v) tau 
.


Fixpoint teval(n: nat)(M: store)(env: venv)(t: tm){struct n}: (store * nat * (option (option vl))):=
  match n with
    | 0 => (M, 0, None)
    | S n =>
      match t with
        | ttrue        => (M, 1, Some (Some (vbool true)) )
        | tfalse       => (M, 1, Some (Some (vbool false)) ) 
        | tvar x       => (M, 1, Some (index x env))
        | tref ex      =>
          match teval n M env ex with
            | (M1, de, None)           => (M1,     1+de, None)
            | (M1, de, Some None)      => (M1,     1+de, Some None)
            | (M1, de, Some (Some vx)) => (vx::M1, 1+de, Some (Some (vref (length M1))))
          end
(*        | ttyp T       => (((vty env T) :: M), 1, Some (Some (length M)))*)
        | tabs y       => (M, 1, Some (Some (vabs env y)) )
        | tapp ef ex   =>
          match teval n M env ex with
            | (M1, df, None)           => (M1, 1+df, None)
            | (M1, df, Some None)      => (M1, 1+df, Some None)
            | (M1, df, Some (Some vx)) =>
              match teval (n - df) M1 env ef with
                | (M2, dx, None)                       => (M2, 1+df+dx, None)
                | (M2, dx, Some None)                  => (M2, 1+df+dx, Some None)
                | (M2, dx, Some (Some (vbool _)))      => (M2, 1+df+dx, Some None)
                | (M2, dx, Some (Some (vref _)))       => (M2, 1+df+dx, Some None)
                | (M2, dx, Some (Some (vabs env2 ey))) => 
                  match teval (n - df - dx) M2 (vx::env2) ey with
                    | (M3, dy,  res)                 => (M3, 1+df+dx+dy, res)
                  end
              end
          end
      end
  end
.

Definition tevaln M env e v (M1:store) k:= 
  exists n, teval n M env e = (M1, k, Some (Some v)).


(*
Fixpoint teval(n: nat)(env:venv)(t: tm){struct n}: (nat * option (option vl)) :=
  match n with
    | 0 => (0,None)
    | S n =>
      match t with
        | ttrue                                => (1, Some (Some (vbool true)))
        | tfalse                               => (1, Some (Some (vbool false)))
        | tvar x                               => (1, Some (index x env))
        | tabs y                               => (1, Some (Some (vabs env y)))
        | tapp ef ex                           =>
          match teval n env ef with
            | (df, None)                       => (1+df, None)
            | (df, Some None)                  => (1+df, Some None)
            | (df, Some (Some (vbool _)))      => (1+df, Some None)
            | (df, Some (Some (vabs env2 ey))) =>
              match teval (n-df) env ex with
                | (dx, None)                   => (1+df+dx, None)
                | (dx, Some None)              => (1+df+dx, Some None)
                | (dx, Some (Some vx))         =>
                  match teval (n-df-dx) (vx::env2) ey with
                    | (dy, res)                => (1+df+dx+dy, res)
                  end
              end
          end
      end
end.*)

(*
Lemma teval_redun: forall i n1 n2 env t k res,
n1 <= i -> teval n1 env t = (k, Some res) ->
n1 <= n2 -> teval n2 env t = (k, Some res).
Proof. intros i. induction i. 
  intros. assert (n1 = 0) by omega. subst n1. simpl in H0. inversion H0.
  (*i = S i *) 
  intros. destruct n1. simpl in H0. inversion H0. destruct n2. omega.
  destruct t.
  simpl in H0. inversion H0. subst. simpl. auto.
    simpl in H0. inversion H0. subst. simpl. auto.
  simpl in H0. inversion H0. subst. simpl. auto.  
  simpl in H0. 
  destruct ( teval n1 env t1) eqn : A1; try solve by inversion.
  destruct o; try solve by inversion.
  destruct o; try solve by inversion.
  destruct v; try solve by inversion.
  inversion H0. subst. simpl.
  assert (teval n2 env t1 =  (n, Some (Some (vbool b)))).
    apply IHi with n1. omega. auto. omega.
  rewrite H2. auto.
  destruct (teval (n1 - n) env t2) eqn : A2; try solve by inversion.
  destruct o; try solve by inversion.
  destruct o; try solve by inversion. 
  destruct (teval (n1 - n - n0) (v :: l) t) eqn :A3; try solve by inversion.
  inversion H0. subst. 
  simpl. 
  assert (teval n2 env t1 = (n, Some (Some (vabs l t)))).
    apply IHi with n1. omega. auto. omega.
  rewrite H2. assert (teval (n2 - n) env t2 = (n0, Some (Some v))).
  apply IHi with (n1-n). omega. auto. omega.
  rewrite H3. assert (teval (n2 - n - n0) (v :: l) t = (n3, Some res)).
  apply IHi with (n1 - n - n0). omega. auto. omega.
  rewrite H4. auto.
  inversion H0. subst. simpl.
  assert (teval n2 env t1 = (n, Some (Some (vabs l t)))).
  apply IHi with n1; try omega; auto.
  rewrite H2. assert (teval (n2 - n) env t2 = (n0, Some None)).
  apply IHi with (n1-n); try omega; auto.
  rewrite H3. auto.
  inversion H0. subst. simpl.
  assert (teval n2 env t1 = (n, Some None)). 
  apply IHi with n1; try omega; auto.
  rewrite H2. auto.
  simpl in H0. inversion H0. subst. simpl. auto.
Qed.
Lemma teval_red: forall n1 n2 env t k res,
teval n1 env t = (k, Some res) ->
n1 <= n2 -> teval n2 env t = (k, Some res).
Proof. intros.
  apply teval_redun with (i := S n1)( n1 := n1).
  omega. auto. auto.
Qed.
Lemma teval_use: forall i t n env k res, 
n <= i ->
teval n env t = (k, Some (res)) -> k > 0 /\ k <= n.
Proof. induction i. intros t n env k res Hle H. 
  assert (n = 0) by omega. subst. simpl in H. inversion H.
  destruct t; intros n env k res Hle H; destruct n; 
    try (simpl in H; inversion H; subst; split; omega).
  simpl in H. assert (n <= i) by omega.
  destruct (teval n env t1) eqn :A1 ; try solve by inversion.
  destruct o; try solve by inversion.
  destruct o; try solve by inversion.
  destruct v; try solve by inversion.
  inversion H. subst. 
  assert (n0 > 0 /\ n0 <= n).
   apply (IHi t1 n env (n0) (Some(vbool b)) H0 A1).
  destruct H1. split; omega.
  destruct (teval (n - n0) env t2) eqn : A2; try solve by inversion.
  destruct o; try solve by inversion.
  destruct o; try solve by inversion.
  destruct (teval (n - n0 - n1) (v :: l) t) eqn : A3; try solve by inversion.
  inversion H. subst. 
  assert ((n - n0 - n1)<= i) by omega.
  assert ( n2 > 0 /\  n2 <= (n - n0 - n1)).
    apply (IHi t (n - n0 - n1) (v::l) n2 res H1 A3).
  destruct H2.
  split; omega.
  inversion H. subst.
  assert ((n - n0) <= i) by omega.
  assert (n1 > 0 /\ n1 <= (n-n0)).
    apply (IHi t2 (n-n0) env n1 None H1 A2).
  destruct H2. split; omega.
  inversion H; subst.
  assert (n0 > 0 /\ n0 <= n).
    apply (IHi t1 n env n0 None H0 A1).
  destruct H1. split; omega.
Qed.
Lemma teval_fuel: forall t n env k res, 
teval n env t = (k, Some (res)) -> k > 0 /\ k <= n.
Proof. intros. apply (teval_use n t n env k res). omega. auto.
Qed.
Definition tevaln env e v := exists nm, 
forall n, n > nm -> exists k, teval n env e = (k, Some (Some v)).
*)


(* Defitition 5 : Expr :Type *)
Definition ExpT (k t:nat)(a : lt k t) (e: tm) (R: venv) (psi: imemtype k) (M : store) (tau: itype t): Prop := 
  exists j M' psi' l, tevaln M R e l M' j /\
                      MemoryEx k psi M psi' M' /\
                      In k t a (psi', M', l) tau
.


(*
Definition ExpT (k t: nat)(a : lt k t) (e :tm) (H : rho) (psi : imemtype k) (M : store)(T: itype t): Prop :=
  exists j M' loc, (tevaln M H e loc M' j) /\
          (exists psi' (c : le k k)(d : lt k t) value, 
           ME k k c (psi, M)(psi', M') /\
           index loc M' = Some value /\ In (k) (t) d (psi', M', value) T).
*)


(*
Fixpoint Bool k: itype k :=
  match k return itype k with
    | 0 => tt
    | S k' => (Bool k', fun P M v =>
                          (imemtype_sat k' P M) /\ (v = vbool true \/ v = vbool false)
              )
  end.
(imemtype_sat k X H) /\ 
    (index X0 H = Some (vbool true) \/ index X0 H = Some (vbool false)).
*)

Lemma Bool k : itype k.
Proof. induction k. apply tt.
  simpl. split. apply IHk.
  intros psi M v. apply ( 
    (imemtype_sat k psi M) /\ 
    (v = vbool true \/ v = vbool false)).
Defined.

Lemma Fun (T1 T2 : type) k : itype k.
Proof. induction k. apply tt.
  simpl. split. apply IHk.
  intros psi M v. apply (
    (imemtype_sat k psi M) /\ exists env2 e, 
             v = (vabs env2 e) /\
             (forall (psi' : imemtype k) (M' : store) (v : vl), 
                ((MemoryEx k psi M psi' M')) /\ (In k (S k) (zz k) (psi', M', v) (T1 (S k)))
             -> (ExpT k (S k) (zz k) e (v::env2) psi' M' (T2 (S k)) )) ).
Defined.

Lemma Ref (T : type) k : itype k.
Proof. induction k. apply tt.
  simpl. split. apply IHk.
  intros psi M v. apply (
    (imemtype_sat k psi M) /\ exists loc vv, 
             v = (vref loc) /\ index loc M = Some vv /\
             snd (T (S k)) psi M vv).
Defined. 
  

Fixpoint val_type (T:ty): type :=
 match T with
    | TBool => Bool
    | TFun T1 T2 => Fun (val_type T1) (val_type T2)
    | TRef T => Ref (val_type T) (* TODO *)
  end.

Ltac In_simpl k:= simpl; destruct (lt_dec k k); try omega;
                  unfold eq_rect_r; unfold eq_rect; unfold eq_sym;
                  match goal with
                      H: ~ k < k |- _ => remember (yy k k (zz k) H) as V
                  end;
                  match goal with
                      H: ?V = (yy k k (zz k) _) |- _ => clear H; destruct V
                  end; simpl.

Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X. induction vs; intros; try inversion H.
  case_eq (beq_nat n (length vs)); intros E; rewrite E in H1.
  eapply beq_nat_true in E. rewrite E. compute. eauto.  
  apply IHvs in H1. compute. eauto.  
Qed.


Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (G: n < length vs) by apply (index_max X vs n T H).
  assert (F: n <> length vs) by omega.
  assert (E: beq_nat n (length vs) = false) by (eapply beq_nat_false_iff; eauto).
  simpl. rewrite E. auto. 
Qed.

Lemma index_has : forall X (vs: list X) n,
             n < length vs ->
             exists T, index n vs = Some T.
Proof. induction vs. 
  intros. simpl in *. omega.
  intros. simpl in *. destruct (lt_dec n (length vs)).
  + specialize (IHvs n l). destruct IHvs. exists x.
    assert ( n <> length vs) by omega. rewrite <- beq_nat_false_iff in H1. rewrite H1.
    assumption.
  + assert ( n = length vs) by omega. rewrite <- beq_nat_true_iff in H0. rewrite H0.
    exists a. reflexivity.
Qed.

Lemma index_map : forall X Y (vs : list X) n a (f : X -> Y),
             index n vs = Some a ->
             index n (map f vs) = Some (f a).
Proof. induction vs. intros. simpl in H. inversion H.
  intros. case_eq (beq_nat n (length vs)); intros E.
  + simpl in *. rewrite E in H. inversion H. subst. rewrite map_length. rewrite E.
    reflexivity.
  + simpl in *. rewrite E in H. specialize (IHvs _ _ f H). 
    rewrite map_length. rewrite E. assumption.
Qed.

Lemma SAT_reduce: forall k (psi:imemtype (S k)) M,
   imemtype_sat (S k) psi M -> imemtype_sat k (map (fun a => fst a) psi) M.
Proof.
  intros. unfold imemtype_sat in *. destruct H. split. rewrite map_length. assumption.
  intros. rewrite map_length in H1. assert (j < S k) by omega.
    specialize (H0 j l H2 H1). 
    assert (exists tau, index l psi = Some tau). apply index_has. assumption.
    destruct H3. rewrite H3 in H0.
    assert (index l (map (fun a => fst a) psi) = Some (fst x)). apply index_map. assumption.
    unfold itype in *. rewrite H4.
    unfold ApproxMem in *. rewrite map_map.
    
    fold itype in *.
    rewrite H in H1. eapply index_has in H1. destruct H1. rewrite H1 in *.

    assert (((map
     (fun x1 : itype k * (list (itype k) -> store -> vl -> Prop) =>
      ApproxT j k a (fst x1)) psi) = (map (ApproxT j (S k) H2) psi))).
    
    admit. (* double approx*)
    rewrite H5.

    unfold In in *. unfold nat_rect in *. 
    assert (lt_dec j k = left a). admit. (* not sure *) 
    rewrite H6 in H0. assumption.
Qed.
    
Lemma ExtendME : forall k M psi M' psi' v T, 
  In k (S k) (zz k) (psi', M', v) (val_type T (S k)) ->
  MemoryEx k psi M psi' M' ->  
  MemoryEx k psi M (val_type T k :: psi') (v :: M').
Proof. 
  induction k. intros. unfold MemoryEx in *. destruct H0. destruct H1.
  split. assumption. split. unfold imemtype_sat in H1. unfold imemtype_sat.
  destruct H1. split. simpl. simpl in H1. omega.
  intros. omega. intros. specialize (H2 _ H3). destruct H2. split. rewrite H2.
  apply index_has in H3. destruct H3. rewrite H3 in H2. erewrite index_extend. symmetry. eassumption. auto.
  unfold imemtype_sat in H0. destruct H0. rewrite H0 in H3. 
  apply index_has in H3. destruct H3. rewrite H4. rewrite H3 in H4.
  erewrite index_extend. symmetry. eassumption. auto.

  (* induction case *)
  intros. (* PROGRESS TO HERE *)
  
  

(* generalize and pull this out as a proper lemma with induction on k *)
(* imemtype_sat for extended store *)
Lemma EnvExt: forall k M (psi:imemtype k), 
  imemtype_sat k psi M -> imemtype_sat k (Bool k::psi) ((vbool true)::M). 
Proof. 
    intros. induction k. intros. unfold imemtype_sat in *. destruct H. split. simpl. auto.
      intros. omega. (* induction base case *)

    assert (imemtype_sat k (Bool k :: (map (fun a => fst a) psi)) (vbool true :: M)) as IND.
    { apply SAT_reduce in H; try omega. fold itype in *. specialize (IHk (map
         (fun a : itype k * (list (itype k) -> store -> vl -> Prop) =>
          fst a) psi) H). assumption.
    } fold itype in *.
    intros. unfold imemtype_sat. unfold imemtype_sat in H. destruct H. split. simpl. eauto.
    intros. specialize (H0 j l a).
    case_eq (beq_nat l (length psi)); intros E.
    + eapply beq_nat_true_iff in E.
      assert (index l (Bool (S k) :: psi) = Some (Bool (S k))). simpl. rewrite <- beq_nat_true_iff in E.
        unfold itype in *. rewrite E. fold itype in *. reflexivity.
      rewrite H2. unfold ApproxMem. simpl. 
      
      destruct (lt_dec j k). (* goal In j k l0 -- get from IND *)
      * unfold imemtype_sat in IND. destruct IND as [? IND]. 
        specialize (IND j l l0). simpl in IND. rewrite map_length in IND. simpl in H2. specialize (IND H1).
        eapply beq_nat_true_iff in E.
      (* Set Printing All. rewriting is a bit tricky b/c types *)
        unfold itype in *. unfold id in *. unfold location in *. rewrite E in IND. 
        unfold itype. unfold location in *. unfold ApproxMem in IND.
        rewrite map_map in IND. eapply IND. 
      
      * unfold eq_rect_r. unfold eq_rect. unfold eq_sym. remember (yy j k a n) as V.
        destruct V. simpl.
        assert (beq_nat l (length M) = true). admit.
        rewrite H3. split. eapply IND. eauto.
    + eapply beq_nat_false_iff in E.
      assert (index l (Bool (S k) :: psi) = index l psi). admit.
      rewrite H2. simpl in H1. assert (l < length psi). admit. 
      specialize (H0 H3).
      destruct (index l psi); try assumption. simpl. simpl in H0. 

      destruct (lt_dec j k).
      * (* get again from IND *)
        unfold imemtype_sat in IND. destruct IND as [? IND]. 
        specialize (IND j l l0). simpl in IND. rewrite map_length in IND. simpl in H2. specialize (IND H1).
        eapply beq_nat_false_iff in E. unfold itype in *. rewrite E in IND. unfold itype in H2. rewrite E in H2.
        fold itype in *.
        assert (index l
          (map
             (fun
                a0 : itype k * (list (itype k) -> store -> vl -> Prop) =>
              fst a0) psi) = Some (fst i)). apply index_map. assumption.
        rewrite H5 in IND. unfold ApproxMem in *. rewrite map_map in IND. 
        assert (map
              (fun
                 x : itype k * (list (itype k) -> store -> vl -> Prop) =>
               ApproxT j k l0 (fst x)) psi =  map (ApproxT j (S k) a) psi). 
               admit. (* double approx *)
        rewrite H6 in IND. assumption.

      * assert (j = k). omega. unfold eq_rect_r in *. unfold eq_rect in *. unfold eq_sym in *.
        remember (yy j k a n) as V. destruct V. simpl in *.
 
        (* need another lemma: every itype works with an extended store *)

Lemma extStore: forall (j:nat)  (i : (itype (S j))) psi M l (a : lt j (S j)), 
snd i (ApproxMem j (S j) a psi) M l  ->
snd i (Bool j :: ApproxMem j (S j) a psi) (vbool true :: M) l.
Proof. intros. 
  destruct i. simpl in *. 


admit. (* not sure how *)

Qed.
  

       admit. (*apply extStore. assumption.*)

Qed.


Lemma ME_longer: forall k psi1 M1 psi2 M2,
   MemoryEx k psi1 M1 psi2 M2 -> length psi1 <= length psi2.
Proof. intros.
  unfold MemoryEx in H. destruct H. destruct H0. 
  assert (forall l, l < length psi1 -> index l psi1 = index l psi2).
    intros. specialize (H1 l H2). apply H1.
  clear H H0 H1 M1 M2.
  generalize dependent psi2. induction psi1.
  intros. simpl. omega.
  intros. simpl. specialize (H2 (length psi1)). simpl in H2. 
  assert (length psi1 < S (length psi1)) by omega. specialize (H2 H).
  assert (beq_nat (length psi1)(length psi1) = true). rewrite beq_nat_true_iff. reflexivity.
  rewrite H0 in H2. assert (index (length psi1) psi2 = Some a). rewrite H2. reflexivity.
  apply index_max in H1. omega.
Qed.


Lemma ME_trans: forall k psi1 M1 psi2 M2 psi3 M3,
   MemoryEx k psi1 M1 psi2 M2 -> 
   MemoryEx k psi2 M2 psi3 M3 ->
   MemoryEx k psi1 M1 psi3 M3.
Proof. intros. assert (length psi1 <= length psi2). (eapply ME_longer). eassumption.
  unfold MemoryEx in *. destruct H. destruct H2. destruct H0. destruct H4.
  split. assumption. split. assumption. intros.
  specialize (H3 _ H6). destruct H3. 
  assert (l < length psi2) by omega.
  specialize (H5 _ H8). destruct H5. split. rewrite H3. assumption. rewrite H7. assumption.
Qed.


(* Definition 4 TypeProp *)
Definition typeProp (k :nat)(tau : type) : Prop := 
forall (psi: imemtype k) M v, In k (S k) (zz k) (psi, M, v) (tau (S k))->
  imemtype_sat k psi M /\ 
  forall psi' M', MemoryEx k psi M psi' M' -> In k (S k) (zz k) (psi' , M', v)(tau (S k)).

Lemma BoolProp: forall k, typeProp k Bool.
Proof. intros.
  unfold typeProp. intros. unfold In in H. unfold nat_rect in H. destruct (lt_dec k k). assert False. 
    eapply ww. eassumption. inversion H0.
  unfold eq_rect_r in H. unfold eq_rect in H. unfold eq_sym in H. remember (yy k k (zz k) n) as V. clear HeqV; destruct V.
  simpl in H. destruct H.
  split. assumption.
  intros. In_simpl k. destruct (lt_dec k0 k0) ; try omega. remember (yy k0 k0 (zz k0) n1) as V. clear HeqV; destruct V.
  simpl. split. unfold MemoryEx in H1. destruct H1. destruct H2. assumption.
  assumption.
Qed.

Lemma FunProp: forall k T1 T2, (* typeProp k T1 -> typeProp k T2 ->*) typeProp k (Fun T1 T2).
Proof.
  intros.
  unfold typeProp.
  intros. unfold In in H. unfold nat_rect in H. destruct (lt_dec k k). assert False. eapply ww. eassumption. inversion H0.
  unfold eq_rect_r in H. unfold eq_rect in H. unfold eq_sym in H. remember (yy k k (zz k) n) as V. clear HeqV; destruct V.
  simpl in H. destruct H. destruct H0 as [env2 [e [? ?]]]. destruct (lt_dec k0 k0) in H1. assert False.
  eapply ww. eassumption. inversion H2. unfold eq_rect_r in H1. unfold eq_rect in H1. unfold eq_sym in H1. 
  remember (yy k0 k0 (zz k0) n0) as V. clear HeqV; destruct V. simpl in H1.
  
  split. assumption. intros. 
  unfold In. unfold nat_rect. destruct (lt_dec k1 k1). omega. unfold eq_rect_r. unfold eq_rect. unfold eq_sym.
  remember (yy k1 k1 (zz k1) n1) as V. clear HeqV; destruct V. simpl.
  split. unfold MemoryEx in H2. destruct H2. destruct H3. assumption.  
  exists env2. exists e. split. assumption. 
  destruct (lt_dec k2 k2). assert False. eapply ww. eassumption. inversion H3.
  unfold eq_rect_r. unfold eq_rect. unfold eq_sym. remember (yy k2 k2 (zz k2) n2) as V. clear HeqV; destruct V. simpl.
  
  intros. destruct H3. assert (MemoryEx k3 psi M psi'0 M'0). eapply ME_trans. eassumption. eassumption.
  eapply H1. split. assumption. assumption.
Qed.


Lemma RefProp : forall k T, typeProp k T -> typeProp k (Ref T).
Proof. intros ? ? A. unfold typeProp. intros. 
  unfold In in H. unfold nat_rect in H. destruct (lt_dec k k). assert False. eapply ww. eassumption. inversion H0.
  unfold eq_rect_r in H. unfold eq_rect in H. unfold eq_sym in H. remember (yy k k (zz k) n) as V. clear HeqV; destruct V.
  simpl in H. destruct H. split. assumption.
  intros. In_simpl k0. remember H1 as AA. clear HeqAA. 
  unfold MemoryEx in H1. destruct H1. destruct H2. split. assumption.
  destruct H0 as [loc [vv [? [? ?]]]]. exists loc. exists vv. split. assumption. split. 
  assert (loc < length M). apply index_max in H4. assumption.
  unfold imemtype_sat in H1. destruct H1. rewrite <- H1 in H6. specialize (H3 _ H6). destruct H3. rewrite <- H8. assumption.
  
  (* use the fact that T is closed under MemoryEx *)
  unfold typeProp in A. specialize (A psi M vv). assert (In k1 (S k1) (zz k1) (psi, M, vv) (T (S k1))).
  { In_simpl k. destruct (lt_dec k1 k1); try omega. remember (yy k1 k1 (zz k1) n2) as V. clear HeqV; destruct V.
    simpl. assumption. }
  specialize (A H6). destruct A. specialize (H8 _ _ AA). unfold In in H8. unfold nat_rect in H8.
  destruct (lt_dec k1 k1); try omega. unfold eq_rect_r in H8. unfold eq_rect in H8. unfold eq_sym in H8.
  remember (yy k1 k1 (zz k1) n1) as V. clear HeqV; destruct V. simpl in H8. assumption.
Qed.
  

Lemma typeAll : forall (T : ty) (k : nat), typeProp k (val_type T).
Proof. intros. induction T. apply BoolProp. apply FunProp.
  apply RefProp. assumption. Qed.


Definition wf_env (G: Gamma) (H: venv) : Prop :=
  forall x T, index x G = Some T ->
              exists v, index x H = Some v /\
                        forall k psi M,
                          imemtype_sat k psi M -> 
                          In k (S k) (zz k) (psi,M,v) (val_type T (S k)).


(* simplify a goal like:
     In k (S k) (zz k) (psi, M, vbool true) (val_type TBool (S k))
*)

(* invert_abs*)
Lemma invert_abs: forall k psif' MF' vf T1 T,
   In k (S k) (zz k) (psif', MF', vf) (val_type (TFun T1 T) (S k)) ->
   exists env e, vf = vabs env e /\ 
   (  forall psi M v, (snd (val_type T1 (S k)) psi M v /\ MemoryEx k psif' MF' psi M)  ->
                      ExpT k (S k) (zz k) e (v :: env) psi M (val_type T (S k))
   ).
Proof. intros.
   unfold In in H. unfold nat_rect in H. destruct (lt_dec k k) ; try omega. unfold eq_rect_r in H.
   unfold eq_rect in H. unfold eq_sym in H. remember (yy k k (zz k) n) as V. clear HeqV; destruct V.
   simpl in H. destruct H. destruct H0 as [env2 [e [? ?]]]. 
   exists env2. exists e. split. assumption.
   (* exists n to terminate *)
   destruct (lt_dec k0 k0). assert False. eapply ww. eassumption. inversion H2.
   unfold eq_rect_r in H1. unfold eq_rect in H1. unfold eq_sym in H1.
   remember (yy k0 k0 (zz k0) n0) as V. clear HeqV; destruct V. simpl in H1. fold itype.
   intros. apply H1. destruct H2. split; assumption.
Qed.






Theorem full_total_safety : forall e G T,
  has_type G e T -> forall H M, wf_env G H ->
                                forall k psi,
                                        imemtype_sat k psi M ->
                                        exists n n' M' v,
    teval n M H e = (M', n', Some (Some v)) /\
      exists psi', MemoryEx k psi M psi' M' /\ In k (S k) (zz k) (psi',M',v) (val_type T (S k)).
Proof.
  induction e; intros; inversion H; subst.
  - Case "true".
    exists 1. exists 1. exists M. exists (vbool true). split. reflexivity.
    intros. exists psi. split. eapply MemoryEx_refl. assumption.
    In_simpl k. eauto. 
  - Case "false".
    exists 1. exists 1. exists M. exists (vbool false). split. reflexivity.
    intros. exists psi. split. eapply MemoryEx_refl. assumption.
    In_simpl k. eauto. 
  - Case "var".
    specialize (H1 _ _ H5). destruct H1 as [v [? ?]]. 
    exists 1. exists 1. exists M. exists v. split. simpl. rewrite H1. reflexivity.
    intros. specialize (H3 k psi M H2). exists psi. split. eapply MemoryEx_refl. assumption. assumption.
  - Case "ref". 
    specialize (IHe _ _ H5 _ M H1 k psi H2).
    destruct IHe as [n [n' [M' [v [E F]]]]].
    exists (S n). exists (S n'). exists (v::M'). exists (vref (length M')).
    split. simpl. rewrite E. reflexivity.

    (* extend MemoryEx *)
    destruct F as [psi' [ME IN]].
    
    exists (val_type T1 k::psi'). split.
    { unfold MemoryEx. unfold MemoryEx in ME. destruct ME. split. assumption.
      destruct H4. split. unfold imemtype_sat. unfold imemtype_sat in H4. destruct H4.
      split. simpl. omega. intros. case_eq (beq_nat l (length psi')); intros F.
      - rewrite beq_nat_true_iff in F. subst. simpl. assert (beq_nat (length psi') (length psi') = true).
        rewrite beq_nat_true_iff. reflexivity. rewrite H9. 
        rewrite H4. assert (beq_nat (length M') (length M') = true). 
        rewrite beq_nat_true_iff. reflexivity. rewrite H10.

        unfold In in IN. unfold nat_rect in IN. destruct (lt_dec k k). omega.
        unfold eq_rect_r in IN. unfold eq_rect in IN. unfold eq_sym in IN. remember (yy k k (zz k) n0) as V.
        clear HeqV; destruct V. simpl in IN.

        unfold In. unfold nat_rect.

        admit. (* not sure how to get *)
      - rewrite beq_nat_false_iff in F. assert (l < length psi'). simpl in H8. omega.
        specialize (H7 _ _ a H9). replace (index l (val_type T1 k :: psi')) with (index l psi').
        replace (index l (v :: M')) with (index l M').
        destruct (index l psi'); try solve by inversion.
        destruct (index l M'); try solve by inversion.
        unfold In. unfold nat_rect. 

        admit. (* not sure how to get *)
        admit. admit. (* routine *)
      - admit. (* MemoryEx *)
    }

    (* In val_type TRef *)
    In_simpl k. split. unfold MemoryEx in ME. destruct ME. destruct H4.
    unfold imemtype_sat. unfold imemtype_sat in H4. destruct H4. split. simpl. omega.
    intros. simpl in *. case_eq (beq_nat l (length psi')) ; intros F.
    + rewrite <- H4. rewrite F. destruct (lt_dec k0 k0); try omega. unfold eq_rect_r in IN.
      unfold eq_rect in IN. unfold eq_sym in IN. remember (yy k0 k0 (zz k0) n1) as V.
      clear HeqV; destruct V. simpl in IN.
      unfold In. unfold nat_rect. admit. (* not sure *)
    + admit. (* NOT SURE *)
    +
    exists (length M'). exists v. split. reflexivity.
    assert (beq_nat (length M')(length M') = true). rewrite beq_nat_true_iff. reflexivity.
    rewrite H3. split. reflexivity. 
    unfold In in IN. unfold nat_rect in IN. destruct (lt_dec k0 k0); try omega.
    unfold eq_rect_r in IN. unfold eq_rect in IN. unfold eq_sym in IN. remember (yy k0 k0 (zz k0) n1) as V.
    clear HeqV; destruct V. simpl in IN.
    assert (MemoryEx k1 psi' M' (val_type T1 k1 :: psi') (v :: M')).
    { unfold MemoryEx. split. unfold MemoryEx in ME. destruct ME. destruct H6. assumption.
      split. unfold MemoryEx in ME. destruct ME. destruct H6. unfold imemtype_sat. unfold imemtype_sat in H6.
      destruct H6. split. simpl. omega. admit. (* not sure *)
      admit. (*routine*)
    }
    assert (typeProp k1 (val_type T1)). eapply typeAll.
    unfold typeProp in H6. admit. (* should be fine *)
    

  - Case "app".
    destruct (IHe2 G _ H8 H0 M H1 k psi H2) as [nx [nx' [Mx [vx [Ex [psix [MEx INx]]]]]]].
    assert (imemtype_sat k psix Mx). unfold MemoryEx in MEx. destruct MEx. destruct H4. assumption.
    destruct (IHe1 G _ H6 H0 Mx H1 k psix H3) as [nf [nf' [Mf [vf [Ef [psif [MEf INf]]]]]]].

    (* use invert_abs *)
    apply invert_abs in INf. destruct INf as [env [e [Vf TER]]]. fold itype in *. 
    specialize (TER psif Mf vx). assert (ExpT k (S k) (zz k) e (vx :: env) psif Mf (val_type T (S k))).
    apply TER. split.
    { unfold In in INx. unfold nat_rect in INx. destruct (lt_dec k k); try omega. unfold eq_rect_r in INx.
      unfold eq_rect in INx. unfold eq_sym in INx. remember (yy k k (zz k) n) as V. clear HeqV; destruct V.
      simpl in INx. 
      (* a level of extention is needed *)

      assert (typeProp k0 (val_type T1)). apply typeAll. unfold typeProp in H4. 
      specialize (H4 psix Mx vx). assert (In k0 (S k0) (zz k0) (psix, Mx, vx) (val_type T1 (S k0))).
      In_simpl k0. assumption. specialize (H4 H5). destruct H4. specialize (H7 psif Mf MEf).
      unfold In in H7. unfold nat_rect in H7. destruct (lt_dec k0 k0); try omega. unfold eq_rect_r in H7.
      unfold eq_rect in H7. unfold eq_sym in H7. remember (yy k0 k0 (zz k0) n0) as V. clear HeqV; destruct V.
      simpl in H7. assumption.
    }
    apply MemoryEx_refl. unfold MemoryEx in MEf. destruct MEf as [A [B ?]]. assumption.
    (* computation of function body *)
    unfold ExpT in H4. destruct H4 as [ne' [Me [psie [ve [Een [MEe INe]]]]]].
    unfold tevaln in Een. destruct Een as [ne Ee]. 
    exists (S (nf + nx + ne)). exists (S (nx' + nf' + ne')). exists Me. exists ve.
    split. simpl. assert (teval (nf + nx + ne) M H0 e2 = (Mx, nx', Some (Some vx))). admit. (*teval extend *)
    rewrite H4. assert (teval (nf + nx + ne - nx') Mx H0 e1 = (Mf, nf', Some (Some vf))). admit. (*teval extend *)
    rewrite H5. rewrite Vf. assert (teval (nf + nx + ne - nx' - nf') Mf (vx :: env) e = (Me, ne', Some (Some ve))).
    admit. (* teval extend *) rewrite H7. reflexivity.
    
    exists psie. split. eapply ME_trans. eassumption. eapply ME_trans. eassumption. eassumption.
    assumption.
  
  - Case "abs". 
    exists 2. exists 1. exists M. exists (vabs H0 e). split. simpl. reflexivity.
    exists psi. split. apply MemoryEx_refl. assumption.
    unfold In. unfold nat_rect. destruct (lt_dec k k); try omega. unfold eq_rect_r. unfold eq_rect. unfold eq_sym.
    remember (yy k k (zz k) n) as V. clear HeqV; destruct V. simpl. 
    split. assumption. exists H0. exists e. split. reflexivity. destruct (lt_dec k0 k0).
    assert False. eapply ww. eassumption. inversion H3. unfold eq_rect_r. unfold eq_rect. unfold eq_sym. 
    remember (yy k0 k0 (zz k0) n0) as V. clear HeqV; destruct V. simpl. intros.

    (* this is the intros of important stuff *)
       
    specialize (IHe _ _ H5). destruct H3.  
    assert (wf_env (T1 :: G) (v :: H0)). admit. (* wf_extend *)
    specialize (IHe _ M' H6). specialize (IHe k psi'). unfold MemoryEx in H3. destruct H3. destruct H7.
    specialize (IHe H7). destruct IHe as [nn [n' [M'0 [v0 [Ev [psi'0 [MEv INv]]]]]]].
    unfold ExpT. exists n'. exists M'0. exists psi'0. exists v0. split.
    exists (nn). assumption. split. assumption. assumption.
Qed.
    
(*
(* need to use Fixpoint because of positivity restriction *) 

Fixpoint val_type nm (v:vl) (T:ty) : Prop := match v, T with
| vbool b, TBool => True
| vabs env y, TFun T1 T2 =>
  (forall vx k, k <= nm /\ val_type k vx T1 ->
     exists v, tevaln (vx::env) y v /\ val_type k v T2) 
| _,_ => False
end
.*)
(*
Definition R nm H t T := 
  exists v, tevaln H t v /\ val_type nm v T.

Definition R_env nm venv tenv :=
  length venv = length tenv /\
 forall x T1, index x tenv = Some T1 ->
   R nm venv (tvar x) T1.

Lemma val_type_dec: forall n1 n2 v T,
val_type n1 v T -> n2 <= n1 ->
val_type n2 v T.
Proof. intros. 
  destruct v; destruct T; try solve by inversion. simpl. auto.
  simpl val_type in H. simpl val_type. intros vx k [Hle Hvt].
  assert (k <= n1) by omega. assert ((k<= n1)/\(val_type k vx T1)).
    split; auto.
  destruct (H vx k H2) as [v [Hev Hvt1]].
  exists v. split; auto.
Qed.

Lemma R_dec: forall n1 n2 H t T ,
R n1 H t T -> n2 <= n1 -> 
R n2 H t T.
Proof.  intros.
  unfold R in H0. unfold R.
  destruct H0 as [v[Hev Hvt]].
  exists v. split; auto. apply val_type_dec with (n1). auto. auto.
Qed. 

Lemma R_env_dec: forall n1 n2 venv tenv,
R_env n1 venv tenv -> n2 <= n1 ->
R_env n2 venv tenv.
Proof. unfold R_env. intros.
  destruct H. split; auto. intros.
  assert (R n1 venv0 (tvar x) T1) by apply (H1 x T1 H2).
  apply R_dec with n1. auto. auto.
Qed.



Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.


Hint Constructors has_type.
(* Hint Constructors val_type. *)
 (*Hint Constructors wf_env.*)

Hint Constructors option.
Hint Constructors list.

Hint Unfold index.
Hint Unfold length.

Hint Resolve ex_intro.

Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X. induction vs; intros; try inversion H.
  case_eq (beq_nat n (length vs)); intros E; rewrite E in H1.
  eapply beq_nat_true in E. rewrite E. compute. eauto.  
  apply IHvs in H1. compute. eauto.  
Qed.


Lemma index_extend : forall X vs n a (T: X),
                       index n vs = Some T ->
                       index n (a::vs) = Some T.

Proof.
  intros.
  assert (G: n < length vs) by apply (index_max X vs n T H).
  assert (F: n <> length vs) by omega.
  assert (E: beq_nat n (length vs) = false) by (eapply beq_nat_false_iff; eauto).
  simpl. rewrite E. auto. 
Qed.

Lemma R_cons_val: forall n venv tenv k vx T1,
R_env n (venv) (tenv) ->
k <= n /\ val_type k vx T1 ->
(R_env k (vx:: venv) (T1:: tenv)).
Proof. intros. destruct H0.
  unfold R_env. unfold R_env in H. destruct H. split. simpl. auto.
  intros. unfold index in H3. destruct (beq_nat x (length tenv0)) eqn : A.
  Case "hit". inversion H3. subst. clear H3. unfold R. 
    exists vx. split. exists 0. intros. destruct n0. omega. exists 1.
    simpl. assert (beq_nat x (length venv0) = true). rewrite H. auto.
    rewrite H4. auto. auto.
  Case "miss". assert (index x tenv0 = Some T0). auto.
    assert (R n venv0 (tvar x) T0). apply H2. auto.
    unfold R. unfold R in H5. 
    destruct H5 as [v [He Ht]].
    exists v. split. exists 0. intros. destruct n0. omega. exists 1.
    simpl. assert (beq_nat x (length venv0)= false). rewrite H. auto.
    rewrite H6. 
      destruct He as [nn Hev]. assert (S nn > nn) as Gn. omega.
      destruct (Hev (S nn) Gn) as [nk Heval]. simpl in Heval. inversion Heval. subst. clear Heval.
      rewrite H9. auto.
    apply val_type_dec with n. auto. auto.
Qed.


Theorem full_total_safety : forall e n tenv T,
  has_type tenv e T -> forall venv, R_env n venv tenv ->
  R n venv e T.
Proof. induction e; intros; inversion H; subst.
  Case "true". eexists. split. exists 0. intros. destruct n0.
    omega. exists 1. simpl. auto. simpl. auto.

  Case "false". eexists. split. exists 0. intros. destruct n0.
    omega. exists 1. simpl. auto. simpl. auto.
  
  Case "var". apply H0. auto.

  Case "app". 
    assert (R n venv0 e1 (TFun T1 T)) by apply (IHe1 n tenv0 (TFun T1 T) H4 venv0 H0).
    assert (R n venv0 e2 T1) by apply (IHe2 n tenv0 T1 H6 venv0 H0).
    destruct H1 as [vf [Fe Ft]]. 
    destruct H2 as [vx [Xe Xt]].
    destruct Fe as [kf FE]. assert (S kf > kf) as Gf by omega.
    destruct (FE (S kf) Gf) as [nf Fev].
    destruct Xe as [kx XE]. assert (S kx > kx) as Gx by omega.
    destruct (XE (S kx) Gx) as [nx Xev].
    simpl in Ft. destruct vf eqn: Vf; try solve by inversion.
    assert (n <= n /\ val_type n vx T1) as G. split; auto.
    destruct (Ft vx n G) as [vy [Ye Yt]].
    exists vy. split; auto.
    destruct Ye as [ky YE]. assert (S ky > ky) as Gy by omega.
    destruct (YE (S ky) Gy) as [ny Yev].
    exists (3+kf+kx+ky). intros.
    exists (1+nf+nx+ny). destruct n0. omega. simpl.
    assert (teval n0 venv0 e1 = (nf, Some (Some (vabs l t)))).
      apply teval_red with (S kf). auto. omega.
    rewrite H2.
    assert (teval (n0 - nf) venv0 e2 = (nx, Some (Some vx))).
      apply teval_red with (S kx). auto. 
      assert (nf > 0 /\ nf <= (S kf)). apply (teval_fuel e1 _ venv0 _ (Some (vabs l t))).
      auto. destruct H3. 
    omega.
    rewrite H3.
    assert (teval (n0 - nf - nx) (vx :: l) t = (ny, Some (Some vy))).
      apply teval_red with (S ky). auto. 
      assert (nf > 0 /\ nf <= (S kf)). apply (teval_fuel e1 _ venv0 _ (Some (vabs l t))).
      auto. destruct H5.
      assert (nx > 0 /\ nx <= (S kx)). apply (teval_fuel e2 _ venv0 _ (Some (vx))).
      auto. destruct H8. 
    omega.
    rewrite H5. auto.
  Case "abs".
    unfold R. eexists. split. exists 0. intros. destruct n0. omega. exists 1.
    simpl. eauto. 
    simpl. intros. destruct H1. 
    assert (R_env k (vx::venv0) (T1::tenv0)). apply R_cons_val with n.
      auto. split; auto.
    apply (IHe) with (T1::tenv0). auto. auto. 
Qed. 
*)
End STLC.