(* Termination for D<> with intersection type and recursive type *)

(*
 DSub (D<:) + Bot + /\ + { z => ... }
 T ::= Top | Bot | x.Type | { Type: S..U } | (z: T) -> T^z | T1 /\ T2 | { z => T^z }
 t ::= x | { Type = T } | lambda x:T.t | t t 
 *)

(* NEGATIVE result:
    show that indexed vset types with precise indexes
    alone do not support t_var_unpack.

   NEW IDEA (to be tried):
    different approximation scheme
    t_var_unpack now works, is there anything else that breaks??
    (see total9 for more experiments based on total5)
*)



Require Export SfLib.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.

(* ### Syntax ### *)

Definition id := nat.

(* term variables occurring in types *)
Inductive var : Type :=
| varF : id -> var (* free, in concrete environment *)
| varH : id -> var (* free, in abstract environment  *)
| varB : id -> var (* locally-bound variable *)
.

Inductive ty : Type :=
| TTop : ty
| TBot : ty
(* (z: T) -> T^z *)
| TAll : ty -> ty -> ty
(* x.Type *)
| TSel : var -> ty
(* { Type: S..U } *)
| TMem : ty(*S*) -> ty(*U*) -> ty
| TBind  : ty -> ty (* Recursive binder: { z => T^z },
                         where z is locally bound in T *)
| TAnd : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *)
.

Inductive tm : Type :=
(* x -- free variable, matching concrete environment *)
| tvar : id -> tm
(* { Type = T } *)
| ttyp : ty -> tm
(* lambda x:T.t *)
| tabs : ty -> tm -> tm
(* t t *)
| tapp : tm -> tm -> tm
(* unpack(e) { x => ... } *)
| tunpack : tm -> tm -> tm                       
.

Inductive vl : Type :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> ty -> tm -> vl
(* a closure for a first-class type *)
| vty : list vl (*H*) -> ty -> vl
.

Definition tenv := list ty. (* Gamma environment: static *)
Definition venv := list vl. (* H environment: run-time *)


(* ### Representation of Bindings ### *)

(* An environment is a list of values, indexed by decrementing ids. *)

Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.

Inductive closed: nat(*B*) -> nat(*H*) -> nat(*F*) -> ty -> Prop :=
| cl_top: forall i j k,
    closed i j k TTop
| cl_bot: forall i j k,
    closed i j k TBot
| cl_all: forall i j k T1 T2,
    closed i j k T1 ->
    closed (S i) j k T2 ->
    closed i j k (TAll T1 T2)
| cl_sel: forall i j k x,
    k > x ->
    closed i j k (TSel (varF x))
| cl_selh: forall i j k x,
    j > x ->
    closed i j k (TSel (varH x))
| cl_selb: forall i j k x,
    i > x ->
    closed i j k (TSel (varB x))
| cl_mem: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TMem T1 T2)
| cl_bind: forall i j k T,
    closed (S i) j k T ->
    closed i j k (TBind T)
| cl_and: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TAnd T1 T2)
.

(* open define a locally-nameless encoding wrt to TVarB type variables. *)
(* substitute var u for all occurrences of (varB k) *)
Fixpoint open_rec (k: nat) (u: var) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
    | TSel (varF x) => TSel (varF x)
    | TSel (varH i) => TSel (varH i)
    | TSel (varB i) => if beq_nat k i then TSel u else TSel (varB i)
    | TMem T1 T2  => TMem (open_rec k u T1) (open_rec k u T2)
    | TBind T => TBind (open_rec (S k) u T)
    | TAnd T1 T2 => TAnd (open_rec k u T1) (open_rec k u T2)
  end.

Definition open u T := open_rec 0 u T.

(* Locally-nameless encoding with respect to varH variables. *)
Fixpoint subst (U : var) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TAll T1 T2   => TAll (subst U T1) (subst U T2)
    | TSel (varB i) => TSel (varB i)
    | TSel (varF i) => TSel (varF i)
    | TSel (varH i) => if beq_nat i 0 then TSel U else TSel (varH (i-1))
    | TMem T1 T2     => TMem (subst U T1) (subst U T2)
    | TBind T       => TBind (subst U T)
    | TAnd T1 T2    => TAnd (subst U T1)(subst U T2)
  end.

Fixpoint nosubst (T : ty) {struct T} : Prop :=
  match T with
    | TTop         => True
    | TBot         => True
    | TAll T1 T2   => nosubst T1 /\ nosubst T2
    | TSel (varB i) => True
    | TSel (varF i) => True
    | TSel (varH i) => i <> 0
    | TMem T1 T2    => nosubst T1 /\ nosubst T2
    | TBind T       => nosubst T
    | TAnd T1 T2    => nosubst T1 /\ nosubst T2
  end.

(* ### Static Subtyping ### *)
(*
The first env is for looking up varF variables.
The first env matches the concrete runtime environment, and is
extended during type assignment.
The second env is for looking up varH variables.
The second env matches the abstract runtime environment, and is
extended during subtyping.
*)
Inductive stp: tenv -> tenv -> ty -> ty -> Prop :=
| stp_top: forall G1 GH T1,
    closed 0 (length GH) (length G1) T1 ->
    stp G1 GH T1 TTop
| stp_bot: forall G1 GH T2,
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH TBot T2
| stp_mem: forall G1 GH S1 U1 S2 U2,
    stp G1 GH U1 U2 ->
    stp G1 GH S2 S1 ->
    stp G1 GH (TMem S1 U1) (TMem S2 U2)
| stp_sel1: forall G1 GH TX T2 x,
    indexr x G1 = Some TX ->
    closed 0 0 (length G1) TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH (TSel (varF x)) T2
| stp_sel2: forall G1 GH TX T1 x,
    indexr x G1 = Some TX ->
    closed 0 0 (length G1) TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 (TSel (varF x)) 
| stp_selx: forall G1 GH v x,
    indexr x G1 = Some v ->
    stp G1 GH (TSel (varF x)) (TSel (varF x))
| stp_sela1: forall G1 GH TX T2 x,
    indexr x GH = Some TX ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH (TSel (varH x)) T2
| stp_sela2: forall G1 GH TX T1 x,
    indexr x GH = Some TX ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 (TSel (varH x)) 
| stp_selax: forall G1 GH v x,
    indexr x GH = Some v  ->
    stp G1 GH (TSel (varH x)) (TSel (varH x))

(* stp for recursive type and inersection type *)
(*
| stp_bind1: forall GH G1 T1 T1' T2,
    stp G1 (T1'::GH) T1' T2 ->
    T1' = (open (varH (length GH)) T1) ->
    closed 1 (length GH) (length G1) T1 ->
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH (TBind T1) T2 

| stp_bind2: forall GH G1 T1 T1' T2,
    stp G1 (T1'::GH) T2 T1' ->
    T1' = (open (varH (length GH)) T1) ->
    closed 1 (length GH) (length G1) T1 ->
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH T2 (TBind T1) 
*)
| stp_bindx: forall GH G1 T1 T1' T2 T2',
    stp G1 (T1'::GH) T1' T2' ->
    T1' = (open (varH (length GH)) T1) ->
    T2' = (open (varH (length GH)) T2) ->
    closed 1 (length GH) (length G1) T1 ->
    closed 1 (length GH) (length G1) T2 ->
    stp G1 GH (TBind T1) (TBind T2)

| stp_and11: forall GH G1 T1 T2 T,
    stp G1 GH T1 T ->
    closed 0 (length GH) (length G1) T2 ->
    stp G1 GH (TAnd T1 T2) T

| stp_and12: forall GH G1 T1 T2 T,
    stp G1 GH T2 T ->
    closed 0 (length GH) (length G1) T1 ->
    stp G1 GH (TAnd T1 T2) T

| stp_and2: forall GH G1 T1 T2 T,
    stp G1 GH T T1 ->
    stp G1 GH T T2 ->
    stp G1 GH T (TAnd T1 T2)


| stp_all: forall G1 GH T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G1) T4 ->
    stp G1 (T3::GH) (open (varH x) T2) (open (varH x) T4) ->
    stp G1 GH (TAll T1 T2) (TAll T3 T4)
| stp_trans: forall G1 GH T1 T2 T3,
    stp G1 GH T1 T2 ->
    stp G1 GH T2 T3 ->
    stp G1 GH T1 T3
.

(* ### Type Assignment ### *)
Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           stp env [] T1 T1 ->
           has_type env (tvar x) T1
(* recursive typing  *)
| t_var_pack : forall G1 x T1 T1',
           (* has_type G1 (tvar x) T1' -> *)
      indexr x G1 = Some (open (varF x) T1) ->            
      T1' = (open (varF x) T1) ->
      closed 1 0 (length G1) T1 ->
      has_type G1 (tvar x) (TBind T1) 
| t_var_unpack : forall G1 x T1 T1',
      (* has_type G1 (tvar x) (TBind T1) -> *)
      indexr x G1 = Some (TBind T1) ->
      T1' = (open (varF x) T1) ->
      closed 0 0 (length G1) T1' ->
      has_type G1 (tvar x) T1'

(* unpack a recursive type: unpack(x:{z=>T^z}) { x:T^x => ... }  *)                    
| t_unpack: forall env x y T1 T1' T2,
           has_type env x (TBind T1) ->
           T1' = (open (varF (length env)) T1) ->
           has_type (T1'::env) y T2 ->
           closed 0 0 (length env) T2 ->
           has_type env (tunpack x y) T2

(* intersection typing *)
| t_and : forall env x T1 T2,
           has_type env (tvar x) T1 ->
           has_type env (tvar x) T2 ->
           has_type env (tvar x) (TAnd T1 T2)

               
| t_typ: forall env T1,
           closed 0 0 (length env) T1 ->
           has_type env (ttyp T1) (TMem T1 T1)
               
| t_app: forall env f x T1 T2,
           has_type env f (TAll T1 T2) ->
           has_type env x T1 ->
           closed 0 0 (length env) T2 ->
           has_type env (tapp f x) T2
| t_dapp:forall env f x T1 T2 T,
           has_type env f (TAll T1 T2) ->
           has_type env (tvar x) T1 ->
           T = open (varF x) T2 ->
           closed 0 0 (length env) T ->
           has_type env (tapp f (tvar x)) T
| t_abs: forall env y T1 T2,
           has_type (T1::env) y (open (varF (length env)) T2) ->
           closed 0 0 (length env) (TAll T1 T2) ->
           has_type env (tabs T1 y) (TAll T1 T2)
| t_sub: forall env e T1 T2,
           has_type env e T1 ->
           stp env [] T1 T2 ->
           has_type env e T2
.



(* ### Evaluation (Big-Step Semantics) ### *)

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
        | tvar x       => Some (indexr x env)
        | ttyp T       => Some (Some (vty env T))
        | tabs T y     => Some (Some (vabs env T y))
        | tapp ef ex   =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              match teval n env ef with
                | None => None
                | Some None => Some None
                | Some (Some (vty _ _)) => Some None
                | Some (Some (vabs env2 _ ey)) =>
                  teval n (vx::env2) ey
              end
          end
        | tunpack ex ey =>
          match teval n env ex with
            | None => None
            | Some None => Some None
            | Some (Some vx) =>
              teval n (vx::env) ey 
          end
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* ------------------------- NOTES -------------------------
Define value typing (val_type)
val_type0 cannot straightforwardly be defined as inductive
family, because the (forall vx, val_type0 env vx T1 -> ... )
occurrence violates the positivity restriction.
--------------------------------------------------------- *)


Fixpoint tsize_flat(T: ty) :=
  match T with
    | TTop => 1
    | TBot => 1
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSel _ => 1
    | TMem T1 T2 => S (tsize_flat T1 + tsize_flat T2)	
    | TBind T => S (tsize_flat T)
    | TAnd T1 T2 => S (tsize_flat T1 + tsize_flat T2)
  end. 

Lemma open_preserves_size: forall T x j,
  tsize_flat T = tsize_flat (open_rec j (varH x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  - destruct v; simpl; destruct (beq_nat j i); eauto.
Qed.


(* NEW DESIGN IDEA:
  
   The required invariants about runtime evaluation rely in crucial
   ways on transporting properties from the creation site of
   type objects to their use sites -- in particular the fact
   that only type aliased can be created (TMem T T), and that these
   cannot be recursive. 

   This suggests that in the proof, we should pair each (vty T) value
   with the semantic interpretation of the type member [[ T ]].

   So [[ T ]] in general is no longer a set of values, but a set of 
   (vl, vset) pairs. This leads to some complication as the type vset 
   is now recursive: 

      Definition vset := vset -> vl -> Prop.

   which Coq wouldn't let us do (for good reasons).

   It seems like the best we can do is an indexed variant such that

    vset (S n) := vset n -> vl -> Prop

   and quantify over n to denote all finite ones.

   As it turns out, we no longer need the previuos l/u bound selectors,
   and the TMem case can ensure that the *actual* type member of an
   object is inbetween the given bounds. This enables the case for
   intersection types.

   For TBind, there is still some uncertainty.
   
*)

Fixpoint vset n := match n with
                     | 0 => vl -> Prop
                     | S n => vset n -> vl -> Prop
                   end.

Definition vseta := forall n, vset n.


(* this is just a helper for pattern matching *)
Inductive vset_match : nat -> Type :=
| vsmatch: forall n, vset (S n) -> list (vset (S n)) -> list (vset (S n)) -> vset_match n
.                                





Require Coq.Program.Wf.

Lemma minus1 {k} : k < (S k). omega. Qed. 

Lemma approx {j k} (a: j < k): vset k -> vset j.
Proof. admit. Qed.

Lemma approx_env { j k } (a: j < k) :  list (vset k) ->  list (vset j).
Proof. admit. Qed. 

Program Fixpoint val_type n (env: list (vset (S n))) (GH:list (vset (S n))) (T:ty) (dd: vset (S n)) (v:vl) {measure (tsize_flat T)}: Prop :=
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall jj vx,
        (forall kx (a: (S kx < S n)),
           val_type kx (approx_env a env) (approx_env a GH) T1 (jj kx) vx) ->
        exists (jj2:vseta) v, tevaln (vx::env1) y v /\
          (forall k (a: (S k < S n)),
             val_type k (approx_env a env) (jj (k)::(approx_env a GH)) (open (varH (length GH)) T2) (jj2 (S k)) v)

    | vty env1 TX, TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      forall dy vy, val_type n env GH T1 dy vy -> dd (approx minus1 dy) vy /\ 
      match (vsmatch n dd env GH) with
        | vsmatch 0 _ _ _ => True
        | vsmatch (S n0) dd env GH  => forall dy vy, 
                      (val_type n0 (approx_env minus1 env) (approx_env minus1 GH) T1 dy vy -> dd dy vy) /\
                      (dd dy vy -> val_type n0 (approx_env minus1 env) (approx_env minus1 GH) T2 dy vy)
      end

    | _, TSel (varF x) =>
      match indexr x env with
        | Some jj => jj (approx minus1 dd) v
        | _ => False
      end
    | _, TSel (varH x) =>
      match indexr x GH with
        | Some jj => jj (approx minus1 dd) v
        | _ => False
      end

    | _, TAnd T1 T2 =>
      val_type n env GH T1 dd v /\ val_type n env GH T2 dd v
        
    | _, TBind T1 =>
       closed 1 (length GH) (length env) T1 /\
      (* NOTE: need to investigate this more. Ideally we would like to express:

          val_type env (dd::GH) (open (varH (length GH)) T1) n (dd n) v

         But this would require dd to be of type vseta instead of vset n. 
         If we change the signature to dd:vseta, however, then we run into 
         trouble with lemma valtp_to_vseta.

      *)
      
      val_type n env (dd::GH) (open (varH (length GH)) T1) dd v
    | _, TTop => 
      True
    | _,_ =>
      False
  end.

Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. unfold open. rewrite <-open_preserves_size. omega. Qed. (* TApp case: open *)
Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. omega. Qed. 

Next Obligation. simpl. unfold open. rewrite <-open_preserves_size. omega. Qed. (* TBind case: open *)

Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0; inversion H1. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0; inversion H1. Qed.


                                  
(* 
   The expansion of val_type, val_type_func is incomprehensible. 
   We cannot (easily) unfold and reason about it. Therefore, we prove unfolding of
   val_type to its body as a lemma.
   (Note that the unfold_sub tactic relies on 
   functional extensionality)
*)

Import Coq.Program.Wf.
Import WfExtensionality.

Lemma val_type_unfold: forall n env GH T dd v, val_type n env GH T dd v =
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall jj vx,
        (forall kx (a: (S kx < S n)),
           val_type kx (approx_env a env) (approx_env a GH) T1 (jj kx) vx) ->
        exists (jj2:vseta) v, tevaln (vx::env1) y v /\
          (forall k (a: (S k < S n)),
             val_type k (approx_env a env) (jj (k)::(approx_env a GH)) (open (varH (length GH)) T2) (jj2 (S k)) v)

    | vty env1 TX, TMem T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 0 (length GH) (length env) T2 /\
      match (vsmatch n dd env GH) with
        | vsmatch 0 _ _ _ => True
        | vsmatch (S n0) dd env GH  => forall dy vy, 
                      (val_type n0 (approx_env minus1 env) (approx_env minus1 GH) T1 dy vy -> dd dy vy) /\
                      (dd dy vy -> val_type n0 (approx_env minus1 env) (approx_env minus1 GH) T2 dy vy)
      end

    | _, TSel (varF x) =>
      match indexr x env with
        | Some jj => jj (approx minus1 dd) v
        | _ => False
      end
    | _, TSel (varH x) =>
      match indexr x GH with
        | Some jj => jj (approx minus1 dd) v
        | _ => False
      end

    | _, TAnd T1 T2 =>
      val_type n env GH T1 dd v /\ val_type n env GH T2 dd v
        
    | _, TBind T1 =>
       closed 1 (length GH) (length env) T1 /\
      (* NOTE: need to investigate this more. Ideally we would like to express:

          val_type env (dd::GH) (open (varH (length GH)) T1) n (dd n) v

         But this would require dd to be of type vseta instead of vset n. 
         If we change the signature to dd:vseta, however, then we run into 
         trouble with lemma valtp_to_vseta.

      *)
      
      val_type n env (dd::GH) (open (varH (length GH)) T1) dd v
    | _, TTop => 
      True
    | _,_ =>
      False
  end.

  

Proof. admit. 
Qed.


(* this is just to accelerate Coq -- val_type in the goal is slooow *)
Inductive vtp: forall n, list (vset (S n)) -> list (vset (S n)) -> ty -> vset (S n) -> vl -> Prop :=
| vv: forall n G H T dd v, val_type n G H T dd v -> vtp n G H T dd v.


Lemma unvv: forall n G H T dd v,
  vtp G H T n dd v -> val_type G H T n dd v.
Proof. admit. (*PERF

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

intros. inversion H0. apply inj_pair2_eq_dec in H2. subst. assumption.
apply eq_nat_dec. *)
Qed.



(* consistent environment *)
Definition R_env n venv genv tenv :=
  length venv = length tenv /\
  length genv = length tenv /\
  forall x TX, indexr x tenv = Some TX ->
    (exists jj vx,
       indexr x venv = Some vx /\
       indexr x genv = Some jj /\
       vtp n genv [] TX jj vx).


(* automation *)
Hint Unfold venv.
Hint Unfold tenv.

Hint Unfold open.
Hint Unfold indexr.
Hint Unfold length.

(* Hint Unfold R. *)
Hint Unfold R_env.

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Hint Constructors closed.
Hint Constructors has_type.
Hint Constructors stp.

Hint Constructors option.
Hint Constructors list.

Hint Resolve ex_intro.


(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)


Lemma invert_var : forall x tenv T,
  has_type tenv (tvar x) T -> forall n venv renv, R_env n venv renv tenv ->
  exists d v, tevaln venv (tvar x) v /\ indexr x venv = Some v /\ indexr x renv = Some d/\ val_type n renv [] T d v.
Proof.
  intros ? ? ? W. remember (tvar x) as e.
  induction W; intros ? ? ? WFE; inversion Heqe; try subst x0.

  - Case "Var". 
    unfold R_env in WFE. destruct WFE as [? [? F]].
    destruct (F _ _ H) as [d [v [I [D V]]]].
    
    exists d. exists v. split. exists 0. intros. destruct n0. omega. simpl. rewrite I. eauto. split. apply I. split. apply D. eapply unvv. eapply V.

  - Case "VarPack".
    unfold R_env in WFE. destruct WFE as [? [? F]].
    destruct (F _ _ H) as [d [v [I [D V]]]]. 
    exists d. exists v. split. exists 0. intros. destruct n0. omega. simpl. rewrite I. reflexivity.
    split. assumption. split. assumption.
    rewrite val_type_unfold.
    destruct v. split. rewrite H3. assumption.
    eapply unvv in V. admit. (* subst *)
    admit. (* vty like vabs *)

  - Case "VarUnpack".
    unfold R_env in WFE. destruct WFE as [? [? F]].
    destruct (F _ _ H) as [d [v [I [D V]]]]. 
    exists d. exists v. split. exists 0. intros. destruct n0. omega. simpl. rewrite I. reflexivity.
    split. assumption. split. assumption.
    eapply unvv in V. rewrite val_type_unfold in V. eapply unvv. 
    destruct v. destruct V as [? V].

    (* HAVE *)
    assert (val_type n renv [d] (open (varH 0) T1) d (vabs l t t0)). apply V. clear H5. 
    (* NEED *)
    assert (val_type n renv [d] (open (varH 0) T1) d (vabs l t t0)). apply V. clear H5.

    (* GOT IT !!! *)

    assert (val_type n renv [] (open (varF x) T1) d (vabs l t t0)). admit. (* subst *)

    subst T1'. eapply vv. eapply H5.

    admit. (* vty like vabs *)
    
  - Case "And".
    admit. 

  - Case "Sub".
    admit. 
Qed. 

