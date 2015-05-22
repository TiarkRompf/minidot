Require Export SfLib.

Require Export Arith.EqNat.

Require Export Arith.Le.

(* 
subtyping: 
  - looking at single-environment case again.
  - new pushback proof structure: transitivity axiom only 
    needed in contravariant positions
  - realizable type: precise expansion has good bounds

 TODO:
  - add bindx and/or bind2/bind1 rules
  - transitivity will only hold in realizable context

 QUESTIONS: 
  - exact statement of transitivity? 
  - what's the right notion of realizable types/contexts?
  - how can we do induction across realizability evidence?
*)


(* ############################################################ *)
(* Syntax *)
(* ############################################################ *)

Module DOT.

Definition id := nat.

Inductive ty : Type :=
  | TNoF   : ty (* marker for empty method list *)

  | TBot   : ty
  | TTop   : ty
  | TBool  : ty
  | TAnd   : ty -> ty -> ty
  | TFun   : id -> ty -> ty -> ty
  | TMem   : ty -> ty -> ty
  | TSel   : id -> ty

  | TSelB  : id -> ty
  | TBind  : ty -> ty
.
  
Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : id -> id -> tm -> tm (* a.f(x) *)
  | tabs : id -> ty -> list (id * dc) -> tm -> tm (* let f:T = x => y in z *)
  | tlet : id -> ty -> tm -> tm -> tm (* let x:T = y *)                                         
with dc: Type :=
  | dfun : ty -> ty -> id -> tm -> dc (* def m:T = x => y *)
.

Fixpoint dc_type_and (dcs: list(nat*dc)) :=
  match dcs with
    | nil => TNoF
    | (n, dfun T1 T2 _ _)::dcs =>
      TAnd (TFun (length dcs) T1 T2)  (dc_type_and dcs)
  end.


Definition TObj p dcs := TAnd (TMem p p) (dc_type_and dcs).
Definition TArrow p x y := TAnd (TMem p p) (TAnd (TFun 0 x y) TNoF).


Inductive vl : Type :=
| vbool : bool -> vl
| vabs  : list (id*vl) -> id -> ty -> list (id * dc) -> vl (* clos env f:T = x => y *)
| vmock : list (id*vl) -> ty -> id -> id -> vl
.

Definition env := list (nat*vl).
Definition tenv := list (nat*ty).

Fixpoint index {X : Type} (n : nat)
               (l : list (nat * X)) : option X :=
  match l with
    | [] => None
    (* for now, ignore binding value n' !!! *)
    | (n',a) :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

Fixpoint update {X : Type} (n : nat) (x: X)
               (l : list (nat * X)) { struct l }: list (nat * X) :=
  match l with
    | [] => []
    (* for now, ignore binding value n' !!! *)
    | (n',a) :: l'  => if beq_nat n (length l') then (n',x)::l' else (n',a) :: update n x l'
  end.



(* LOCALLY NAMELESS *)

Inductive closed_rec: nat -> ty -> Prop :=
| cl_nof: forall k,
    closed_rec k TNoF
| cl_top: forall k,
    closed_rec k TTop
| cl_bot: forall k,
    closed_rec k TBot
| cl_bool: forall k,
    closed_rec k TBool
| cl_fun: forall k m T1 T2,
    closed_rec k T1 ->
    closed_rec k T2 ->
    closed_rec k (TFun m T1 T2)
| cl_mem: forall k T1 T2,
    closed_rec k T1 ->
    closed_rec k T2 ->
    closed_rec k (TMem T1 T2)
| cl_and: forall k T1 T2,
    closed_rec k T1 ->
    closed_rec k T2 ->
    closed_rec k (TAnd T1 T2)
| cl_bind: forall k T1,
    closed_rec (S k) T1 ->
    closed_rec k (TBind T1)
| cl_sel: forall k x,
    closed_rec k (TSel x)
| cl_selb: forall k i,
    k > i ->
    closed_rec k (TSelB i)
.

Hint Constructors closed_rec.

Definition closed j T := closed_rec j T.


Fixpoint open_rec (k: nat) (u: id) (T: ty) { struct T }: ty :=
  match T with
    | TSel x      => TSel x (* free var remains free. functional, so we can't check for conflict *)
    | TSelB i     => if beq_nat k i then TSel u else TSelB i
    | TBind T1    => TBind (open_rec (S k) u T1)
    | TNoF        => TNoF
    | TBot => TBot
    | TTop => TTop
    | TBool       => TBool
    | TAnd T1 T2  => TAnd (open_rec k u T1) (open_rec k u T2)
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
    | TFun m T1 T2  => TFun m (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

(* sanity check *)
Example open_ex1: open 9 (TBind (TAnd (TMem TBot TTop) (TFun 0 (TSelB 1) (TSelB 0)))) =
                      (TBind (TAnd (TMem TBot TTop) (TFun 0 (TSel  9) (TSelB 0)))).
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
 Case "TBind". econstructor. eapply IHclosed_rec. omega.
 Case "TSelB". econstructor. omega.
Qed.


Hint Unfold open.
Hint Unfold closed.


(* ############################################################ *)
(* Static properties: type assignment, subtyping, ... *)
(* ############################################################ *)

(* TODO: wf is not up to date *)

(* static type expansion.
   needs to imply dynamic subtyping / value typing. *)
Inductive tresolve: id -> ty -> ty -> Prop :=
  | tr_self: forall x T,
             tresolve x T T
  | tr_and1: forall x T1 T2 T,
             tresolve x T1 T ->
             tresolve x (TAnd T1 T2) T
  | tr_and2: forall x T1 T2 T,
             tresolve x T2 T ->
             tresolve x (TAnd T1 T2) T
  | tr_unpack: forall x T2 T3 T,
             open x T2 = T3 ->
             tresolve x T3 T ->
             tresolve x (TBind T2) T
.

Tactic Notation "tresolve_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Self" |
    Case_aux c "And1" |
    Case_aux c "And2" |
    Case_aux c "Bind" ].


(* static type well-formedness.
   needs to imply dynamic subtyping. *)
Inductive wf_type : tenv -> ty -> Prop :=
| wf_top: forall env,
    wf_type env TNoF
| wf_bool: forall env,
    wf_type env TBool
| wf_and: forall env T1 T2,
             wf_type env T1 ->
             wf_type env T2 ->
             wf_type env (TAnd T1 T2)
| wf_mem: forall env TL TU,
             wf_type env TL ->
             wf_type env TU ->
             wf_type env (TMem TL TU)
| wf_fun: forall env f T1 T2,
             wf_type env T1 ->
             wf_type env T2 ->
             wf_type env (TFun f T1 T2)
                     
| wf_sel: forall envz x TE TL TU,
            index x envz = Some (TE) ->
            tresolve x TE (TMem TL TU) ->
            wf_type envz (TSel x)

| wf_selb: forall envz x, (* note: disregarding bind-scope *)
             wf_type envz (TSelB x)
| wf_bind: forall envz T,
             wf_type envz T ->
             wf_type envz (TBind T)

.

Tactic Notation "wf_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Top" |
    Case_aux c "Bool" |
    Case_aux c "And" |
    Case_aux c "MemA" |
    Case_aux c "Mem" |
    Case_aux c "Fun" |
    Case_aux c "Sel" |
    Case_aux x "SelB" |
    Case_aux c "Bind" ].


(* expansion / membership *)
(* this is the precise version! no slack in lookup *)
(* TODO: need the name for bind? *)
Inductive exp : tenv -> ty -> ty -> Prop :=
(*
| exp_bot: forall G1,
    exp G1 TBot (TMem TTop TBot)  (* causes trouble in inv_mem: need to build stp deriv with smaller n *)
*)
| exp_mem: forall G1 T1 T2,
    exp G1 (TMem T1 T2) (TMem T1 T2)
| exp_sel: forall G1 x T T2 T3 T4 T5,
    index x G1 = Some T ->
    exp G1 T (TMem T2 T3) ->
    exp G1 T3 (TMem T4 T5) ->
    exp G1 (TSel x) (TMem T4 T5) 
.


Inductive stp : bool -> tenv -> ty -> ty -> nat -> Prop := 

| stp_bot: forall G1 T n1,
    stp true G1 TBot T n1

| stp_top: forall G1 T n1,
    stp true G1 T TTop n1
             
| stp_bool: forall G1 n1,
    stp true G1 TBool TBool n1

| stp_fun: forall m G1 T11 T12 T21 T22 n1 n2,
    stp false G1 T21 T11 n1 ->
    stp true G1 T12 T22 n2 ->
    stp true G1 (TFun m T11 T12) (TFun m T21 T22) (S (n1+n2))

| stp_mem: forall G1 T11 T12 T21 T22 n1 n2,
    stp false G1 T21 T11 n1 ->
    stp true G1 T12 T22 n2 ->
    stp true G1 (TMem T11 T12) (TMem T21 T22) (S (n1+n2))
        
| stp_sel2: forall x T1 TX G1 n1,
    index x G1 = Some TX ->
    stp true G1 TX (TMem T1 TTop) n1 ->
    stp true G1 T1 (TSel x) (S n1)
| stp_sel1: forall x T2 TX G1 n1,
    index x G1 = Some TX ->
    stp true G1 TX (TMem TBot T2) n1 ->
    stp true G1 (TSel x) T2 (S n1)
| stp_selx: forall x G1 n1,
    stp true G1 (TSel x) (TSel x) (S n1)
                  
(* TODO!
| stp_bind2: forall f G1 T1 T2 TA2 n1,
    stp true ((f,T1)::G1) T1 T2 n1 ->
    open (length G1) TA2 = T2 ->                
    stp true G1 T1 (TBind TA2) (S n1)
| stp_bind1: forall f G1 T1 T2 TA1 n1,
    stp true ((f,T1)::G1) T1 T2 n1 ->
    open (length G1) TA1 = T1 ->                
    stp true G1 (TBind TA1) T2 (S n1)
... or at least...
*)
| stp_bindx: forall G1 T1 T2 TA1 TA2 n1 n2,
    stp true ((length G1,T1)::G1) T1 T2 n1 ->
    open (length G1) TA1 = T1 ->                
    open (length G1) TA2 = T2 ->
    (* we need exp T1 D here *)
    (* how will this interact with narrowing? *)
    (* exp G1 T1 (TMem TL TU) -> *)
    (* stp true G1 TL TU n2 -> *)
    itp G1 T1 n2 ->
    stp true G1 (TBind TA1) (TBind TA2) (S (n1+n2))

| stp_transf: forall G1 T1 T2 T3 n1 n2,
    stp true G1 T1 T2 n1 ->
    stp false G1 T2 T3 n2 ->           
    stp false G1 T1 T3 (S (n1+n2))

| stp_wrapf: forall G1 T1 T2 n1,
    stp true G1 T1 T2 n1 ->
    stp false G1 T1 T2 (S n1)       

with itp: tenv -> ty -> nat -> Prop :=

| itp_top: forall G1 n1,
    itp G1 TTop n1
| itp_bool: forall G1 n1,
    itp G1 TBool n1
(* TODO: we should have another mem case,
   if lower bound is bot, upper bound need
   not be realizable (?) *)
| itp_mem: forall G1 TL TU n1 n2,
    stp true G1 TL TU n1 ->
    itp G1 TU n2 -> 
    itp G1 (TMem TL TU) (n1+n2)
| itp_sel: forall G1 TX x n1,
    index x G1 = Some TX ->
    itp G1 TX n1 ->
    itp G1 (TSel x) n1
.






Tactic Notation "stp_cases" tactic(first) ident(c) :=
  first;
  [ 
    Case_aux c "Bot < ?" |
    Case_aux c "? < Top" |
    Case_aux c "Bool < Bool" |
    Case_aux c "Fun < Fun" |
    Case_aux c "Mem < Mem" |
    Case_aux c "? < Sel" |
    Case_aux c "Sel < ?" |
    Case_aux c "Sel < Sel" |
    Case_aux c "Bind < Bind" |
    Case_aux c "Trans" |
    Case_aux c "Wrap"
  ].


Hint Resolve ex_intro.

Hint Constructors stp.
Hint Constructors itp.

(* ############################################################ *)
(* Examples *)
(* ############################################################ *)


(*
THIS IS NOW FALSE: lhs must expand.

Example ex1: exists n, stp true nil (TBind TBot) (TBind TTop) n.
Proof.
 eexists. eapply stp_bindx. eapply stp_bot. eauto. (* false - bot doesn't exp! *).
Grab Existential Variables. apply 0.
Qed.
 *)

Example ex2: exists n, stp true nil
   (TBind (TMem TBool TBool))
   (TBind (TMem TBot TTop)) n.
Proof.
  eexists. eapply stp_bindx. eapply stp_mem. eapply stp_wrapf. eapply stp_bot.
  eapply stp_top. compute. eauto. compute. eauto. eauto. 
Grab Existential Variables. apply 0. apply 0. apply 0. apply 0.
Qed.

Example ex3: exists n, stp true nil
   (TBind (TMem TBool TBool))
   (TBind (TMem (TSelB 0) (TSelB 0))) n. (* can't do much with this *)
Proof.
  eexists. eapply stp_bindx.
  instantiate (3 := (TMem TBool TBool)).
  instantiate (2 := (TMem (TSel 0) (TSel 0))).

  eapply stp_mem. eapply stp_wrapf.
  eapply stp_sel1. compute. eauto. eapply stp_mem. eauto. eauto.
  eapply stp_sel2. compute. eauto. eauto.
  eauto. eauto. eauto.
Grab Existential Variables. apply 0. apply 0. apply 0. apply 0. apply 0. apply 0.
Qed.



(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)



Definition stpd b G1 T1 T2 := exists n, stp b G1 T1 T2 n.

Hint Unfold stpd.

Ltac ep := match goal with
             | [ |- stp ?M ?G1 ?T1 ?T2 ?N ] => assert (exists (x:nat), stp M G1 T1 T2 x) as EEX
           end.

Ltac eu := match goal with
             | H: stpd _ _ _ _ |- _ => destruct H
(*             | H: exists n: nat ,  _ |- _  =>
               destruct H as [e P] *)
           end.

Lemma stpd_bot: forall G1 T,
    stpd true G1 TBot T.
Proof. intros. exists 2. eauto. Qed.
Lemma stpd_top: forall G1 T,
    stpd true G1 T TTop.
Proof. intros. exists 0. eauto. Qed.
Lemma stpd_bool: forall G1,
    stpd true G1 TBool TBool.
Proof. intros. exists 0. eauto. Qed.
Lemma stpd_fun: forall m G1 T11 T12 T21 T22,
    stpd false G1 T21 T11 ->
    stpd true G1 T12 T22 ->
    stpd true G1 (TFun m T11 T12) (TFun m T21 T22).
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_mem: forall G1 T11 T12 T21 T22,
    stpd false G1 T21 T11 ->
    stpd true G1 T12 T22 ->
    stpd true G1 (TMem T11 T12) (TMem T21 T22).
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_sel2: forall x T1 TX G1,
    index x G1 = Some TX ->
    stpd true G1 TX (TMem T1 TTop) ->
    stpd true G1 T1 (TSel x).
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_sel1:  forall x T2 TX G1,
    index x G1 = Some TX ->
    stpd true G1 TX (TMem TBot T2) ->
    stpd true G1 (TSel x) T2.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_selx: forall x G1,
    stpd true G1 (TSel x) (TSel x).
Proof. intros. repeat eu. exists 1. eauto. Qed.
Lemma stpd_bindx: forall G1 T1 T2 TA1 TA2,
    stpd true ((length G1,T1)::G1) T1 T2 ->
    open (length G1) TA1 = T1 ->                
    open (length G1) TA2 = T2 ->
    (* exp G1 T1 (TMem TL TU) -> *)
    (* stpd true G1 TL TU -> *)
    (exists n, itp G1 T1 n) ->
    stpd true G1 (TBind TA1) (TBind TA2).
Proof. intros. repeat eu. destruct H2. eauto. Qed.
Lemma stpd_transf: forall G1 T1 T2 T3,
    stpd true G1 T1 T2 ->
    stpd false G1 T2 T3 ->           
    stpd false G1 T1 T3.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd_wrapf: forall G1 T1 T2,
    stpd true G1 T1 T2 ->
    stpd false G1 T1 T2. 
Proof. intros. repeat eu. eauto. Qed.





Ltac index_subst := match goal with
                 | H1: index ?x ?G = ?V1 , H2: index ?x ?G = ?V2 |- _ => rewrite H1 in H2; inversion H2; subst
                 | _ => idtac
               end.

Lemma stp0f_trans: forall n n1 n2 G1 T1 T2 T3,
    stp false G1 T1 T2 n1 ->
    stp false G1 T2 T3 n2 ->
    n1 <= n ->
    stpd false G1 T1 T3.
Proof.
  intros n. induction n.
  - Case "z".
    intros. assert (n1 = 0). omega. subst. inversion H.
  - Case "S n".
    intros. inversion H.
    + eapply stpd_transf. eexists. eapply H2. eapply IHn. eapply H3. eapply H0. omega.
    + eapply stpd_transf. eexists. eapply H2. eexists. eapply H0.
Qed.  



(* implementable type: expands and has good bounds *)
(* Definition itp G T (n:nat) := exists T1 T2 n1, exp G T (TMem T1 T2) /\ stp true G T1 T2 n1 /\ n1 <= n. *)

(*
Inductive itp: tenv -> ty -> nat -> Prop :=

| itp_top: forall G1 n1,
    itp G1 TTop n1
| itp_mem: forall G1 T T1 T2 n1 n,
    exp G1 T (TMem T1 T2) ->
    stp true G1 T1 T2 n1 ->
    n1 <= n ->
    itp G1 T n.
*)

(* TODO: now make it recurse into upper bounds *)

(* implementable context *)
Definition env_itp G n := forall x T, index x G = Some T -> itp G T n.




(* left:  may use axiom but has size. must shrink *)
(* right: no axiom but can grow *)

Definition trans_env_on G1 n2 :=
  forall m T1 T2 T3,
      stp m G1 T1 T2 n2 ->
      stpd true G1 T2 T3 ->
      stpd true G1 T1 T3.

Hint Unfold trans_env_on.

Definition trans_on n1 n2 := 
  forall G1,  
    env_itp G1 n1 ->
    trans_env_on G1 n2.
    
Hint Unfold trans_on.




Definition trans_up n := forall n1 n2, n1 + n2 <= n ->
                      trans_on n1 n2.
Hint Unfold trans_up.

Lemma trans_le: forall n n1 n2,
                      trans_up n ->
                      n1+n2 <= n ->
                      trans_on n1 n2
.
Proof. intros. unfold trans_up in H. eapply H. eauto. Qed.


Lemma upd_hit: forall {X} G G' x x' (T:X) T',
              index x G = Some T ->
              update x' T' G = G' ->
              beq_nat x x' = true ->
              index x G' = Some T'.
Proof. admit. Qed.
Lemma upd_miss: forall {X} G G' x x' (T:X) T',
              index x G = Some T ->
              update x' T' G = G' ->
              beq_nat x x' = false ->
              index x G' = Some T.
Proof. admit. Qed. 


Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  Case "nil". intros. inversion H.
  Case "cons".
  intros. inversion H. destruct a.
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
  unfold index. unfold index in H. rewrite H. rewrite E. destruct a. reflexivity.
Qed.

Lemma update_extend: forall X (TX1: X) G1 G1' x a, 
  update x TX1 G1 = G1' ->
  update x TX1 (a::G1) = (a::G1').
Proof. admit. Qed.

Lemma update_pres_len: forall X (TX1: X) G1 G1' x, 
  update x TX1 G1 = G1' ->
  length G1 = length G1'.
Proof. admit. Qed.

Lemma stp_extend : forall m G1 T1 T2 x v n,
                       stp m G1 T1 T2 n ->
                       stp m ((x,v)::G1) T1 T2 n.
Proof. admit. (*intros. destruct H. eexists. eapply stp_extend1. apply H.*) Qed.


Lemma itp_extend: forall G T n x v,
                         itp G T n ->
                         itp ((x,v)::G) T n.
Proof. admit. Qed.

Lemma env_itp_extend : forall G T n x v,
                       env_itp G n ->
                       itp ((x,v)::G) T n ->  
                       env_itp ((x,v)::G) n.
Proof. admit. (*intros. destruct H. eexists. eapply stp_extend1. apply H.*) Qed.



(*
NOT NEEDED (?)
Lemma exp_unique: forall G1 T1 TA1 TA2 TA1L TA2L, 
  exp G1 T1 (TMem TA1L TA1) ->
  exp G1 T1 (TMem TA2L TA2) ->
  TA1 = TA2.
Proof. admit. Qed.
*)


(* key lemma that relates exp and stp. result has bounded size. *)
Lemma stpd_inv_mem: forall n n1 G1, 

  forall TA1 TA2 TA1L TA2L T1,
  exp G1 T1 (TMem TA1L TA1) ->
  stp true G1 T1 (TMem TA2L TA2) n1 ->
  n1 <= n ->
  exists n3, stp true G1 (TMem TA1L TA1) (TMem TA2L TA2) n3 /\ n3 <= n1. (* should be semantic eq! *)
Proof.
  intros n1. induction n1.
  (*z*) intros. inversion H0; subst; inversion H1; subst; try omega. try inversion H.
  (* s n *)
  intros. inversion H.
(*  - Case "bot". subst. exists 0. split. eapply stp_mem. eauto. eauto. inversion H0.  subst. omega. *)
  - Case "mem". subst. exists n0. auto. (*inversion H0. subst. exists n3. split. eauto. omega. *)
  - Case "sel".
    subst.
    inversion H0.
    repeat index_subst. clear H4.
    
    assert (exists n0 : nat, stp true G1 (TMem T2 T3) (TMem TBot (TMem TA2L TA2)) n0 /\ n0 <= n2).
    eapply (IHn1 n2). apply H7. apply H5. omega.

    destruct H2. destruct H2. inversion H2. subst.

    assert (exists n0 : nat, stp true G1 (TMem TA1L TA1) (TMem TA2L TA2) n0 /\ n0 <= n3).
    eapply (IHn1 n3). apply H8. apply H15. omega.

    destruct H6. destruct H6.
    
    eexists. split. apply H6. omega.
Qed.


(* dual case *)
Lemma stpd_build_mem: forall n1 G1, 
  forall TA1 TA2 TA1L TA2L T1,
  exp G1 T1 (TMem TA1L TA1) ->
  stp true G1 (TMem TA1L TA1) (TMem TA2L TA2) n1 ->
  exists n3, stp true G1 T1 (TMem TA2L TA2) n3.
Proof.
  intros.
  generalize dependent n1.
  generalize dependent TA2.
  generalize dependent TA2L.
  induction H.
  - Case "mem".
    subst. eexists. eauto.
  - Case "sel".
    intros. subst.
    assert (exists n3, stp true G1 T3 (TMem TA2L TA2) n3) as IX2. {
      eapply IHexp2. eauto.
    }
    destruct IX2 as [n2 IX2].
    assert (exists n3, stp true G1 T (TMem TBot (TMem TA2L TA2)) n3) as IX. {
      eapply IHexp1. eapply stp_mem. eapply stp_wrapf. eapply stp_bot. apply IX2. 
    }
    destruct IX.
    subst. eexists. eapply stp_sel1. eauto. eauto.
    Grab Existential Variables. apply 0.
Qed.


Lemma stp_narrow: forall m G1 T1 T2 n1,
  stpd m G1 T1 T2 ->
                    
  forall x TX1 TX2 G1' nG,

    index x G1 = Some TX2 ->
    update x TX1 G1 = G1' ->
    stp true G1' TX1 TX2 n1 ->
    env_itp G1' nG ->
    itp G1' TX1 nG ->
    trans_on nG n1 ->

    stpd m G1' T1 T2.
Proof.
  intros m G1 T1 T2 n1 H. destruct H as [n2 H].
  induction H; intros.
  - Case "Bot".
    intros. eapply stpd_bot.
  - Case "Top".
    intros. eapply stpd_top.
  - Case "Bool". 
    intros. eapply stpd_bool.
  - Case "Fun". 
    intros. eapply stpd_fun. eapply IHstp1; eauto. eapply IHstp2; eauto.
  - Case "Mem". 
    intros. eapply stpd_mem. eapply IHstp1; eauto. eapply IHstp2; eauto.
  - Case "Sel2". intros.
    { case_eq (beq_nat x x0); intros E.
      assert (env_itp G1' nG). auto.
      (* hit updated binding *)
      + assert (x = x0) as EX. eapply beq_nat_true_iff; eauto. subst. index_subst. index_subst.
        eapply stpd_sel2. eapply upd_hit; eauto. eapply H6. eapply H7. eapply H3. eapply IHstp; eauto.
      (* other binding *)
      + assert (x <> x0) as EX. eapply beq_nat_false_iff; eauto.
        eapply stpd_sel2. eapply upd_miss; eauto. eapply IHstp. eapply H1. eauto. eauto. eauto. eauto. eauto.
    }
  - Case "Sel1". intros.
    { case_eq (beq_nat x x0); intros E.
      assert (env_itp G1' nG). auto.
      (* hit updated binding *)
      + assert (x = x0) as EX. eapply beq_nat_true_iff; eauto. subst. index_subst. index_subst. 
        eapply stpd_sel1. eapply upd_hit; eauto. eapply H6. eapply H7. eapply H3. eapply IHstp; eauto.
      (* other binding *)
      + assert (x <> x0) as EX. eapply beq_nat_false_iff; eauto.
        eapply stpd_sel1. eapply upd_miss; eauto. eapply IHstp. eapply H1. eauto. eauto. eauto. eauto. eauto.
    }
  - Case "Selx". eapply stpd_selx.
  - Case "Bindx".
    (* 
       Now considering only non-recursive bounds.
       All upper bounds must be realizable (deep, via itp).
    *)

    assert (length G1 = length G1'). { eapply update_pres_len; eauto. }
    remember (length G1) as L. clear HeqL. subst L.

    assert (itp G1 T1 n2). eauto. (* already have it! *)
    (* will do induction with extended env. need to prove T1 realizable in G1' *)
    assert (exists nx, itp G1' T1 nx) as IE. {
      clear IHstp. clear H. clear H0.
      induction H2.
      + SCase "top". exists 0. eauto.
      + SCase "bool". exists 0. eauto.
      + SCase "mem".
        assert (exists nx : nat, itp G1' TU nx) as IH. eapply IHitp; eauto.
        assert (exists nx : nat, stp true G1' TL TU nx) as IHS. admit. (* ind narrow! *)
        (* TODO: need to be able to do induction on stp_narrow *)
        destruct IH. destruct IHS.
        eexists. eapply itp_mem. eauto. eauto.
      + SCase "sel".
        assert (exists nx : nat, itp G1' TX nx) as IH. eauto.
        destruct IH.
        case_eq (beq_nat x0 x); intros E.
        * assert (x0 = x) as EX. eapply beq_nat_true_iff; eauto.
          subst. index_subst. index_subst.
          eexists. eapply itp_sel. eapply upd_hit. eauto. eauto. eauto. eauto.
        * assert (x0 <> x) as EX. eapply beq_nat_false_iff; eauto.
          subst.
          eexists. eapply itp_sel. eapply upd_miss. eauto. eauto. eauto. eauto.
    }

    eapply stpd_bindx. {
      eapply IHstp.
      eapply index_extend; eauto.
      eapply update_extend; eauto.
      eapply stp_extend; eauto.
    
      eapply env_itp_extend. eauto. 
      eapply itp_extend. eauto. eauto.
      eapply itp_extend. eauto. eauto.
    }
    eauto.
    eauto.
    eauto.

  - Case "Trans". eapply stpd_transf. eapply IHstp1; eauto. eapply IHstp2; eauto.
  - Case "Wrap". eapply stpd_wrapf. eapply IHstp; eauto.
Qed.


Lemma stpd_trans_lo: forall G1 T1 T2 TX TXL TXU,
  stpd true G1 T1 T2 ->                     
  stpd true G1 TX (TMem T2 TTop) ->
  exp G1 TX (TMem TXL TXU) ->
  stpd true G1 TX (TMem T1 TTop).
Proof.
  intros. repeat eu.
  assert (exists nx, stp true G1 (TMem TXL TXU) (TMem T2 TTop) nx /\ nx <= x) as E. eapply (stpd_inv_mem x). eauto. eauto. omega.
  destruct E as [nx [ST X]].
  inversion ST. subst.

  eapply stpd_build_mem. eauto. eapply stp_mem. eapply stp_transf. eauto. eauto. eauto.
Qed.


Lemma stpd_trans_hi: forall G1 T1 T2 TX n1 nG TXL TXU,
  stpd true G1 T1 T2 ->                     
  stp true G1 TX (TMem TBot T1) n1 ->
  exp G1 TX (TMem TXL TXU) ->
  env_itp G1 nG ->
  trans_up (nG + n1) ->
  stpd true G1 TX (TMem TBot T2).
Proof.
  intros. repeat eu.
  assert (exists nx, stp true G1 (TMem TXL TXU) (TMem TBot T1) nx /\ nx <= n1) as E. eapply (stpd_inv_mem n1). eauto. eauto. omega.
  destruct E as [nx [ST X]].
  inversion ST. subst.

  assert (trans_on nG n2) as IH. { eapply trans_le; eauto. omega. }
  assert (stpd true G1 TXU T2) as ST1. { eapply IH. eauto. eauto. eauto. }
  destruct ST1.
  eapply stpd_build_mem. eauto. eapply stp_mem. eauto. eauto.
Qed.


(* need to invert mem. requires proper realizability evidence *)
Lemma stpd_trans_cross: forall G1 TX T1 T2 TXL TXU n1 n2 nG,
                          (* trans_on *)
  stp true G1 TX (TMem T1 TTop) n1 ->
  stpd true G1 TX (TMem TBot T2) ->
  exp G1 TX (TMem TXL TXU) ->
  stp true G1 TXL TXU n2 ->
  env_itp G1 nG ->
  trans_up (n1+n2+nG) ->
  stpd true G1 T1 T2.
Proof.
  intros. eu.
  assert (exists n3, stp true G1 (TMem TXL TXU) (TMem T1 TTop) n3 /\ n3 <= n1) as SM1. eapply (stpd_inv_mem n1). eauto. eauto. omega.
  assert (exists n3, stp true G1 (TMem TXL TXU) (TMem TBot T2) n3 /\ n3 <= x) as SM2. eapply (stpd_inv_mem x). eauto. eauto. omega.
  destruct SM1 as [n3 [SM1 E3]].
  destruct SM2 as [n4 [SM2 E4]].
  inversion SM1. inversion SM2.
  subst. clear SM1 SM2.
  
  assert (trans_on nG n0) as IH0. { eapply trans_le; eauto. omega. }
  assert (trans_on nG n2) as IH1. { eapply trans_le; eauto. omega. }

  eapply IH0. eauto. eauto. eapply IH1. eauto. eauto. eauto.
Qed.


Lemma stp1_trans: forall n, trans_up n.
Proof.
  intros n. induction n.
  Case "z". admit.
  Case "S n".
  unfold trans_up. intros nG n1 NE G1 IMP  b T1 T2 T3 S12 S23.
  destruct S23 as [n2 S23].

(* TODO: pass in externally -- what about induction with bind?? *)
  (* assert (env_itp G1 n) as IMP. admit. *)

  stp_cases(inversion S12) SCase. 
  - SCase "Bot < ?". eapply stpd_bot.
  - SCase "? < Top". subst. inversion S23; subst.
    + SSCase "Top". eapply stpd_top.
    + SSCase "Sel2".
      assert (itp G1 TX nG) as E. { eapply IMP. eauto. }
      inversion E. subst. inversion H0.
      eapply stpd_sel2; eauto. eapply stpd_trans_lo; eauto.
  - SCase "Bool < Bool". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eauto.
    + SSCase "Bool". eapply stpd_bool; eauto.
    + SSCase "Sel2". eapply stpd_sel2. eauto.  eexists. eapply H5. 
  - SCase "Fun < Fun". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eapply stpd_top.
    + SSCase "Fun". inversion H10. subst.
      eapply stpd_fun.
      * eapply stp0f_trans; eauto.
      * assert (trans_on nG n3) as IH.
        { eapply trans_le; eauto. omega. }
        eapply IH; eauto.
    + SSCase "Sel2".
      assert (itp G1 TX nG) as E. { eapply IMP. eauto. }
      inversion E. subst. inversion H7.
      eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto.
  - SCase "Mem < Mem". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eapply stpd_top.
    + SSCase "Mem". inversion H10. subst.
      eapply stpd_mem.
      * eapply stp0f_trans; eauto.
      * assert (trans_on nG n3) as IH.
        { eapply trans_le; eauto. omega. }
        eapply IH; eauto.
    + SSCase "Sel2". 
      assert (itp G1 TX nG) as E. { eapply IMP. eauto. }
      inversion E. subst. inversion H7.
      eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto.
  - SCase "? < Sel". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eapply stpd_top.
    + SSCase "Sel2". 
      assert (itp G1 TX0 nG) as E. { eapply IMP. eauto. }
      inversion E. subst. inversion H7.
      eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto.
    + SSCase "Sel1". (* interesting case *)
      index_subst.
      assert (itp G1 TX0 nG) as E. { eapply IMP. eauto. }
      inversion E. subst. inversion H7.
      assert (trans_up (n0+n1+nG)) as IH.
      { unfold trans_up. intros. apply IHn. admit. (* FIXME n0+n1+nG <= n. *) }
      inversion H10. subst. index_subst. eapply stpd_trans_cross; eauto.
    + SSCase "Selx". inversion H8. index_subst. subst. index_subst. subst.
      eapply stpd_sel2. eauto. eauto.
  - SCase "Sel < ?".
      assert (trans_up (nG+n0)) as IH.
      { unfold trans_up. intros. eapply IHn. omega. }
      assert (itp G1 TX nG) as E. { eapply IMP. eauto. }
      inversion E. subst. inversion H0.
      eapply stpd_sel1. eauto. eapply stpd_trans_hi; eauto.
  - SCase "Sel < Sel". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eapply stpd_top.
    + SSCase "Sel2". 
       assert (itp G1 TX nG) as E. { eapply IMP. eauto. }
       inversion E. subst. inversion H5.
       eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto.
     + SSCase "Sel1". inversion H8. index_subst. subst. index_subst. subst.
       eapply stpd_sel1. eauto. eauto.
     + SSCase "Selx". inversion H6. subst. repeat index_subst.
       eapply stpd_selx; eauto.
  - SCase "Bind < Bind". inversion S23; subst; try solve by inversion.
    + SSCase "Top". eapply stpd_top.
    + SSCase "Sel2". 
      assert (itp G1 TX nG) as E. { eapply IMP. eauto. }
      inversion E. subst. inversion H10.
      eapply stpd_sel2. eauto. eapply stpd_trans_lo; eauto.
    + SSCase "Bind".
      inversion H16. subst.
      assert (trans_up (nG+n0)) as IH.
      { unfold trans_up. intros. eapply IHn. omega. }
      (* realizable in old env *) 
      assert (itp G1 (open (length G1) TA2) nG). { eapply itp_mem. eauto. eauto. admit. (* FIXME n5 <= nG *) }
      (* realizable in new env *)
      assert (itp G1 (open (length G1) TA1) nG). { eapply itp_mem.  eauto. eauto. admit. (* FIXME n3 <= nG *) }
      (* first narrow, then trans *)
      assert (stpd true ((length G1, open (length G1) TA1) :: G1)
                   (open (length G1) TA2) (open (length G1) TA3)) as NRW.
      { 
        assert (beq_nat (length G1) (length G1) = true) as E.
        { eapply beq_nat_true_iff. eauto. }
        inversion H16. subst.
        eapply stp_narrow. eauto.
        instantiate (2 := length G1). unfold index. rewrite E. eauto.
        instantiate (1 := open (length G1) TA1). unfold update. rewrite E. eauto.
        eauto.
        eapply env_itp_extend. eauto. eapply itp_extend. eauto. (* itp with TA2 in env *)
        eapply itp_extend. eauto. (* itp with TA1 in env *)
        eauto.
      }
      eapply stpd_bindx. eapply IH. eauto.
      eapply env_itp_extend. eauto. eapply itp_extend. eauto. eauto. eauto. eauto. eauto. eauto. eauto.  
  - SCase "Trans". subst.
    assert (trans_on nG n3) as IH2.
    { eapply trans_le; eauto. omega. }
    assert (trans_on nG n0) as IH1.
    { eapply trans_le; eauto. omega. }
    assert (stpd true G1 T4 T3) as S123.
    { eapply IH2; eauto. }
    destruct S123.
    eapply IH1; eauto.
  - SCase "Wrap". subst.
    assert (trans_on nG n0) as IH.
    { eapply trans_le; eauto. omega. }
    eapply IH; eauto.
Qed.


End DOT.

