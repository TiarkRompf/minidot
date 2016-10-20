(* Termination for D<> *)
(* this version includes a proof of totality (like in nano0-total.v *)

(* copied from nano4-total.v *)
(* add TMem and TSel, complicated val_type0 wf definition *)
(* copied from nano4-total1-wip.v / dsubsup.v *)
(* scale up to full D<> *)

(* some proofs are commented out with a label PERF:
   this is just to make Coq go faster through the file *)

(*
TODO: 
 + add tty
 + add sel1, sel2
 + make TMem translucent
 - make TFun dependent (x)
 ------------
 - make TSel take a term instead of a nat
 - allow guarded recursion (x) 

TECHNICAL PROBLEMS:
 + circularity between stp2 and val_type
 - recursive types (once we add them)

A: scale up to D<>
   + sel1, sel2
     dependent functions
B: add interesting features:
     full paths 
     singleton types
     guarded recursion
     capabilities
*)


(*
 DSub (D<:) + Bot
 T ::= Top | Bot | x.Type | { Type: S..U } | (z: T) -> T^z
 t ::= x | { Type = T } | lambda x:T.t | t t
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
.

Inductive vl : Type :=
(* a closure for a lambda abstraction *)
| vabs : list vl (*H*) -> ty -> tm -> vl
(* a closure for a first-class type *)
| vty : list vl (*H*) -> ty -> vl
.

Definition tenv := list ty. (* Gamma environment: static *)
Definition venv := list vl. (* H environment: run-time *)
Definition aenv := list (venv*ty). (* J environment: abstract at run-time *)

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
    (* This is a bit looser than just being able to select on TMem vars. *)
    indexr x G1 = Some v ->
    stp G1 GH (TSel (varF x)) (TSel (varF x))
| stp_sela1: forall G1 GH TX T2 x,
    indexr x GH = Some TX ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem TBot T2) ->
    stp G1 GH (TSel (varH x)) T2
(* XXX complete proof for Fsub first *)
| stp_sela2: forall G1 GH TX T1 x,
    indexr x GH = Some TX ->
    closed 0 x (length G1) TX ->
    stp G1 GH TX (TMem T1 TTop) ->
    stp G1 GH T1 (TSel (varH x))
| stp_selax: forall G1 GH v x,
    (* This is a bit looser than just being able to select on TMem vars. *)
    indexr x GH = Some v  ->
    stp G1 GH (TSel (varH x)) (TSel (varH x))
| stp_all: forall G1 GH T1 T2 T3 T4 x,
    stp G1 GH T3 T1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G1) T4 ->
    stp G1 (T3::GH) (open (varH x) T2) (open (varH x) T4) ->
    stp G1 GH (TAll T1 T2) (TAll T3 T4)
.

(* ### Type Assignment ### *)
Inductive has_type : tenv -> tm -> ty -> Prop :=
| t_var: forall x env T1,
           indexr x env = Some T1 ->
           stp env [] T1 T1 ->
           has_type env (tvar x) T1
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



(* ### Runtime Subtyping ### *)
(* H1 T1 <: H2 T2 -| J *)
Inductive stp2: bool (* whether selections are precise *) ->
                bool (* whether the last rule may not be transitivity *) ->
                venv -> ty -> venv -> ty -> aenv  ->
                nat (* derivation size *) ->
                Prop :=
| stp2_top: forall G1 G2 GH T s n,
    closed 0 (length GH) (length G1) T ->
    stp2 s true G1 T G2 TTop GH (S n)
| stp2_bot: forall G1 G2 GH T s n,
    closed 0 (length GH) (length G2) T ->
    stp2 s true G1 TBot G2 T GH (S n)
| stp2_mem: forall G1 G2 S1 U1 S2 U2 GH s n1 n2,
    stp2 s s G1 U1 G2 U2 GH n1 ->
    stp2 s false G2 S2 G1 S1 GH n2 ->
    stp2 s true G1 (TMem S1 U1) G2 (TMem S2 U2) GH (S (n1+n2))

(* concrete type variables *)
(* precise/invertible bounds *)
(* vty already marks binding as type binding, so no need for additional TMem marker *)
| stp2_strong_sel1: forall G1 G2 GX TX x T2 GH n1,
    indexr x G1 = Some (vty GX TX) ->
    val_type_stub GX (vty GX TX) (TMem TX TX) -> (* for downgrade *)
    closed 0 0 (length GX) TX ->
    stp2 true true GX TX G2 T2 GH n1 ->
    stp2 true true G1 (TSel (varF x)) G2 T2 GH (S n1)
| stp2_strong_sel2: forall G1 G2 GX TX x T1 GH n1,
    indexr x G2 = Some (vty GX TX) ->
    val_type_stub GX (vty GX TX) (TMem TX TX) -> (* for downgrade *)
    closed 0 0 (length GX) TX ->
    stp2 true false G1 T1 GX TX GH n1 ->
    stp2 true true G1 T1 G2 (TSel (varF x)) GH (S n1)
(* imprecise type *)
| stp2_sel1: forall G1 G2 v GX TX x T2 GH n1,
    indexr x G1 = Some v ->
    val_type_stub GX v TX ->
    closed 0 0 (length GX) TX ->
    stp2 false false GX TX G2 (TMem TBot T2) GH n1 ->
    stp2 false true G1 (TSel (varF x)) G2 T2 GH (S n1)
| stp2_sel2: forall G1 G2 v GX TX x T1 GH n1,
    indexr x G2 = Some v ->
    val_type_stub GX v TX ->
    closed 0 0 (length GX) TX ->
    stp2 false false GX TX G1 (TMem T1 TTop) GH n1 ->
    stp2 false true G1 T1 G2 (TSel (varF x)) GH (S n1)
| stp2_selx: forall G1 G2 v x1 x2 GH s n,
    indexr x1 G1 = Some v ->
    indexr x2 G2 = Some v ->
    stp2 s true G1 (TSel (varF x1)) G2 (TSel (varF x2)) GH (S n)

(* abstract type variables *)
(*| stp2_strong_sela1: forall G1 G2 GX TX x T2 GH n1,
    indexr x GH = Some (GX, (TMem TX TX)) ->
    stp2 true true GX TX G2 T2 GH n1 ->
    stp2 true true G1 (TSel (varH x)) G2 T2 GH (S n1)
| stp2_strong_sela2: forall G1 G2 GX TX x T1 GH n1,
    indexr x GH = Some (GX, (TMem TX TX)) ->
    closed 0 0 (length GX) TX ->
    stp2 true false G1 T1 GX TX GH n1 ->
    stp2 true true G1 T1 G2 (TSel (varH x)) GH (S n1) *)
(* imprecise *)
| stp2_sela1: forall G1 G2 GX TX x T2 GH n1,
    indexr x GH = Some (GX, TX) ->
    closed 0 x (length GX) TX ->
    stp2 false false GX TX G2 (TMem TBot T2) GH n1 ->
    stp2 false true G1 (TSel (varH x)) G2 T2 GH (S n1)
| stp2_sela2: forall G1 G2 GX T1 TX x GH n1,
    indexr x GH = Some (GX, TX) ->
    closed 0 x (length GX) TX ->
    stp2 false false GX TX G1 (TMem T1 TTop) GH n1 ->
    stp2 false true G1 T1 G2 (TSel (varH x)) GH (S n1)
| stp2_selax: forall G1 G2 v x GH s n,
    indexr x GH = Some v ->
    stp2 s true G1 (TSel (varH x)) G2 (TSel (varH x)) GH (S n)

| stp2_all: forall G1 G2 T1 T2 T3 T4 x GH s n1 n2,
    stp2 false false G2 T3 G1 T1 GH n1 ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G2) T4 ->
    stp2 false false G1 (open (varH x) T2) G2 (open (varH x) T4) ((G2, T3)::GH) n2 ->
    stp2 s true G1 (TAll T1 T2) G2 (TAll T3 T4) GH (S (n1 + n2))

| stp2_wrapf: forall G1 G2 T1 T2 GH s n1,
    stp2 s true G1 T1 G2 T2 GH n1 ->
    stp2 s false G1 T1 G2 T2 GH (S n1)

| stp2_transf: forall G1 G2 G3 T1 T2 T3 GH s n1 n2,
    stp2 s true G1 T1 G2 T2 GH n1 ->
    stp2 s false G2 T2 G3 T3 GH n2 ->
    stp2 s false G1 T1 G3 T3 GH (S (n1+n2))


with val_type_stub : venv -> vl -> ty -> Prop :=
| v_ty: forall env venv T1 TE,
    (exists n, stp2 true true venv (TMem T1 T1) env TE [] n) ->
    val_type_stub env (vty venv T1) TE
| v_abs: forall env venv y GX TX T1 T2 TE,
    (exists n, stp2 true true GX (TAll T1 T2) env TE [] n) ->
    val_type_stub env (vabs venv TX y) TE
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
      end
  end.


Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).


(* ------------------------- NOTES -------------------------

Define value typing (val_type)

val_type0 cannot straightforwardly be defined as inductive
family, because the (forall vx, val_type0 env vx T1 -> ... )
occurrence violates the positivity restriction.

The definition as Fixpoint has some problems, too. In
particular we need to guarantee that it is well-founded.
The standard logical relations defintion recurses 
structurally on T. In this setting it is unclear how to
add the following desirable rules:

- v: x.T

    index y G1 = Some (vty TX) ->
    vtp G1 v TX ->
    vtp G1 v (TSel y)

- v: { z => T }

    vtp G1 v (open 0 (TVar true x) T2) ->
    closed 0 (length G1) T2 ->
    vtp G1 v (TBind T2)

- v: (x:T1) -> T2^x

    subst x in T2

Another concern is what to do if stp2 needs to use 
val_type internally (for T < x.L < U).

Ideas:

1) can we define a more complex size measure on types?
   (to exclude recursion through x.T)
2) can stp2 get away with a restricted version of vtp?
   (stp2 only needs type members, not functions)

Current development:

We follow (1) -- define a more complex size measure.

--------------------------------------------------------- *)


Fixpoint vsize (v : vl) : nat :=
  match v with
    | vabs _ _ _ => 0
    | vty G T  => 
      (fix tsize T := 
         match T with
           | TBot          => 1
           | TTop          => 1
           | TAll T1 T2    => S (tsize T1 + tsize T2)
           | TMem T1 T2    => S (tsize T1 + tsize T2)
           | TSel (varB x) => 1 (* ? *)
           | TSel (varH x) => 1 (* ? *)
           | TSel (varF x) => S
             ((fix idx x G :=
                match G with
                  | v::tl => if beq_nat x (length tl) then vsize v else idx x tl
                  | _ => 0
                end) x G)
         end) T
  end.

Fixpoint tsize (G:venv) (T:ty) {struct T} :=
  match T with
    | TBot           => 1
    | TTop           => 1
    | TAll T1 T2     => S (tsize G T1 + tsize G T2)  
    (* this becomes: ... + tsize G [T1] (open (varH 1) T2) *)
    | TMem T1 T2     => S (tsize G T1 + tsize G T2)
    | TSel (varB x)  => 1
    | TSel (varH x)  => 1
    | TSel (varF x)  => S
      match indexr x G with
        | Some v => vsize v
        | None => 0
      end
  end.


Lemma tsz_eq: forall TX GX,
  tsize GX TX = (vsize (vty GX TX)).
Proof.
  intros TX. simpl. induction TX; intros; eauto.
  - Case "fun". simpl. rewrite IHTX1. rewrite IHTX2. eauto.
  - Case "sel". simpl. destruct v; eauto. 
    induction GX.
    + simpl. eauto.
    + simpl. destruct (beq_nat i (length GX)). eauto. eauto.
  - Case "mem". simpl. rewrite IHTX1. rewrite IHTX2. eauto.
 Qed.
 
Lemma tsz_indir: forall GX TX,
  tsize GX TX < S (vsize (vty GX TX)).
Proof.
  intros. rewrite tsz_eq. eauto. 
Qed.


Lemma open_preserves_tsize: forall G T x j,
  tsize G T = tsize G (open_rec j (varH x) T).
Proof.
  intros G T. induction T; intros; simpl; eauto.
  - destruct v; simpl; destruct (beq_nat j i); eauto.
Qed.




Inductive val_type0 : venv -> vl -> ty -> Prop :=
| vs_ty: forall venv T1,
    val_type0 venv (vty venv T1) (TMem T1 T1)
| vs_abs: forall venv y TX,
    val_type0 venv (vabs venv TX y) (TAll TTop TBot)
.


(* NOTE: crucial to be a smaller type according to tsize! *)
(* TODO: needs selh case -- but not entirely clear how *)
Inductive bounds : venv -> ty -> (venv*ty) -> (venv*ty)  -> Prop :=
| bs_mem: forall G T1 T2,
    bounds G (TMem T1 T2) (G,T1) (G,T2)
| bs_sel: forall G GX TX GT1 GT2 x,
    indexr x G = Some (vty GX TX) ->
    bounds GX TX GT1 GT2 ->
    bounds G (TSel (varF x)) GT1 GT2 
.



Require Coq.Program.Wf.

Program Fixpoint val_type (env:venv) (GH:list (vl->Prop)) (v:vl) (T:ty) {measure (tsize env T)}: Prop :=
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall vx (jj:vl->Prop),
        val_type env GH vx T1 ->
        (forall vy, jj vy -> forall GL TL GU TU, bounds env T1 (GL,TL) (GU,TU) -> val_type GU GH vy TU) ->
        exists v, tevaln (vx::env1) y v /\ val_type env (jj::GH) v (open (varH (length GH)) T2)
    | vty env1 TX, TMem T1 T2 =>
      closed 0 0 (length env1) TX /\ (* required to convert to val_type_stub *)
      exists n1 n2,
        stp2 false false env1 TX env T2 [] n1 /\ (* FIXME: what about [] vs GH ?? *)
        stp2 false false env T1 env1 TX [] n2
    | _, TSel (varF x) =>
      match indexr x env with
        | Some (vty GX TX) => val_type GX GH v TX
        | _ => False
      end
    | _, TSel (varH x) =>
      match indexr x GH with
        | Some jj => jj v
        | _ => False
      end
    | vty env1 TX , TTop =>
      closed 0 0 (length env1) TX (* required to convert to val_type_stub *)
    | vabs _ _ _ , TTop =>
      True 
    | _,_ =>
      False
  end.

Next Obligation. simpl. omega. Qed.
Next Obligation. simpl. admit. (* TODO: prove a lemma that bounds are smaller *) Qed.

Next Obligation. simpl. unfold open. rewrite <-open_preserves_tsize. omega. Qed. (* TApp case: open *)
Next Obligation. (* TSel case *)
  simpl. rewrite <-Heq_anonymous. eapply tsz_indir. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.
Next Obligation. compute. repeat split; intros; destruct H; inversion H; inversion H0. Qed.


(* 
   ISSUE: 
   The expansion of val_type, val_type_func is incomprehensible. 
   We cannot (easily) unfold and reason about it. Therefore, we prove unfolding of
   val_type to its body as a lemma.

   (Note that the unfold_sub tactic relies on 
   functional extensionality)
*)

Import Coq.Program.Wf.
Import WfExtensionality.

Lemma val_type_unfold: forall env GH v T, val_type env GH v T =
  match v,T with
    | vabs env1 T0 y, TAll T1 T2 =>
      closed 0 (length GH) (length env) T1 /\ closed 1 (length GH) (length env) T2 /\
      forall vx (jj:vl->Prop),
        val_type env GH vx T1 ->
        (forall vy, jj vy -> forall GL TL GU TU, bounds env T1 (GL,TL) (GU,TU) -> val_type GU GH vy TU) ->
        exists v, tevaln (vx::env1) y v /\ val_type env (jj::GH) v (open (varH (length GH)) T2) 

    | vty env1 TX, TMem T1 T2 =>
      closed 0 0 (length env1) TX /\
      exists n1 n2, stp2 false false env1 TX env T2 [] n1 /\
                    stp2 false false env T1 env1 TX [] n2
    | _, TSel (varF x) =>
      match indexr x env with
        | Some (vty GX TX) => val_type GX GH v TX
        | _ => False
      end
    | _, TSel (varH x) =>
      match indexr x GH with
        | Some jj => jj v
        | _ => False
      end
    | vty env1 TX , TTop =>
      closed 0 0 (length env1) TX
    | vabs _ _ _ , TTop =>
      True 
    | _,_ =>
      False
  end.
Proof.
  intros. unfold val_type at 1. unfold val_type_func.
  unfold_sub val_type (val_type env GH v T).
  simpl.
  destruct v; simpl; try reflexivity.
  destruct T.
  - simpl; try reflexivity.
  - simpl; try reflexivity.
  - destruct T1; simpl; reflexivity. 
  - destruct v; simpl; try reflexivity.

  (* TSel case has another match *)
  destruct (indexr i env); simpl; try reflexivity;
  destruct v; simpl; try reflexivity.
  (* TSelH *)
  destruct (indexr i GH); simpl; try reflexivity.
  - eauto.
  -  destruct T; simpl; try reflexivity;
     destruct v; simpl; try reflexivity.
     (* TSel case has another match *)
     destruct (indexr i env); simpl; try reflexivity;
     destruct v; simpl; try reflexivity.
     (* TSelH *)
     destruct (indexr i GH); simpl; try reflexivity.
Qed.


(* make logical relation explicit *)
Definition R H t v T := tevaln H t v /\ val_type H [] v T.

(* consistent environment *)
Definition R_env venv tenv :=
  length venv = length tenv /\
 forall x T1, indexr x tenv = Some T1 ->
   exists v : vl, R venv (tvar x) v T1.

Definition R_envh (vvs:venv) (aenv:aenv) tenv :=
  length aenv = length tenv /\
 forall x T1, indexr x tenv = Some T1 ->
   indexr x aenv = Some (vvs, T1).


Inductive valh_type : venv -> aenv -> (venv*ty) -> ty -> Prop :=
| v_tya: forall aenv venv T1,
    valh_type venv aenv (venv, T1) T1
.



(* automation *)
Hint Unfold venv.
Hint Unfold tenv.

Hint Unfold open.
Hint Unfold indexr.
Hint Unfold length.

Hint Unfold R.
Hint Unfold R_env.
Hint Unfold R_envh.

Hint Constructors ty.
Hint Constructors tm.
Hint Constructors vl.

Hint Constructors closed.
Hint Constructors has_type.
Hint Constructors val_type_stub.
Hint Constructors stp.
Hint Constructors stp2.

Hint Constructors option.
Hint Constructors list.

Hint Resolve ex_intro.

(* ############################################################ *)
(* Examples *)
(* ############################################################ *)

Ltac crush :=
  try solve [eapply stp_selx; compute; eauto; crush];
  try solve [eapply stp_selax; compute; eauto; crush];
  try solve [econstructor; compute; eauto; crush];
  try solve [eapply t_sub; crush].

(* define polymorphic identity function *)

Definition polyId := TAll (TMem TBot TTop) (TAll (TSel (varB 0)) (TSel (varB 1))).

Example ex1: has_type [] (tabs (TMem TBot TTop) (tabs (TSel (varF 0)) (tvar 1))) polyId.
Proof.
  crush.
Qed.

(* instantiate it to TTop *)
Example ex2: has_type [polyId] (tapp (tvar 0) (ttyp TTop)) (TAll TTop TTop).
Proof.
  crush.
Qed.

(* ############################################################ *)
(* Proofs *)
(* ############################################################ *)

Fixpoint tsize_flat(T: ty) :=
  match T with
    | TTop => 1
    | TBot => 1
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSel _ => 1
    | TMem T1 T2 => S (tsize_flat T1 + tsize_flat T2)
  end.

Lemma open_preserves_size: forall T x j,
  tsize_flat T = tsize_flat (open_rec j (varH x) T).
Proof.
  intros T. induction T; intros; simpl; eauto.
  - destruct v; simpl; destruct (beq_nat j i); eauto.
Qed.

(* ## Extension, Regularity ## *)

Lemma wf_length : forall vs ts,
                    R_env vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
Qed.

Hint Immediate wf_length.

Lemma wfh_length : forall vvs vs ts,
                    R_envh vvs vs ts ->
                    (length vs = length ts).
Proof.
  intros. induction H. auto.
Qed.


Hint Immediate wfh_length.

Lemma indexr_max : forall X vs n (T: X),
                       indexr n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs.
  - Case "nil". intros. inversion H.
  - Case "cons".
    intros. inversion H.
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

Lemma indexr_extend : forall X vs n x (T: X),
                       indexr n vs = Some T ->
                       indexr n (x::vs) = Some T.

Proof.
  intros.
  assert (n < length vs). eapply indexr_max. eauto.
  assert (beq_nat n (length vs) = false) as E. eapply beq_nat_false_iff. omega.
  unfold indexr. unfold indexr in H. rewrite H. rewrite E. reflexivity.
Qed.

(* splicing -- for stp_extend. *)

Fixpoint splice n (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TAll T1 T2   => TAll (splice n T1) (splice n T2)
    | TSel (varF i) => TSel (varF i)
    | TSel (varB i) => TSel (varB i)
    | TSel (varH i) => if le_lt_dec n i then TSel (varH (i+1)) else TSel (varH i)
    | TMem T1 T2   => TMem (splice n T1) (splice n T2)
  end.

Definition spliceat n (V: (venv*ty)) :=
  match V with
    | (G,T) => (G,splice n T)
  end.

Lemma splice_open_permute: forall {X} (G0:list X) T2 n j,
(open_rec j (varH (n + S (length G0))) (splice (length G0) T2)) =
(splice (length G0) (open_rec j (varH (n + length G0)) T2)).
Proof.
  intros X G T. induction T; intros; simpl; eauto;
  try rewrite IHT1; try rewrite IHT2; try rewrite IHT; eauto;
  destruct v; eauto.

  case_eq (le_lt_dec (length G) i); intros E LE; simpl; eauto.
  rewrite LE. eauto.
  rewrite LE. eauto.
  case_eq (beq_nat j i); intros E; simpl; eauto.
  case_eq (le_lt_dec (length G) (n + length G)); intros EL LE.
  rewrite E.
  assert (n + S (length G) = n + length G + 1). omega.
  rewrite H. eauto.
  omega.
  rewrite E. eauto.
Qed.

Lemma indexr_splice_hi: forall G0 G2 x0 v1 T,
    indexr x0 (G2 ++ G0) = Some T ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (splice (length G0)) G2 ++ v1 :: G0) = Some (splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. omega.
  - simpl in H.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
Qed.

Lemma indexr_spliceat_hi: forall G0 G2 x0 v1 G T,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    length G0 <= x0 ->
    indexr (x0 + 1) (map (spliceat (length G0)) G2 ++ v1 :: G0) =
    Some (G, splice (length G0) T).
Proof.
  intros G0 G2. induction G2; intros.
  - eapply indexr_max in H. simpl in H. omega.
  - simpl in H. destruct a.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + rewrite E in H. inversion H. subst. simpl.
      rewrite app_length in E.
      rewrite app_length. rewrite map_length. simpl.
      assert (beq_nat (x0 + 1) (length G2 + S (length G0)) = true). {
        eapply beq_nat_true_iff. eapply beq_nat_true_iff in E. omega.
      }
      rewrite H1. eauto.
    + rewrite E in H.  eapply IHG2 in H. eapply indexr_extend. eapply H. eauto.
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
  - simpl in H.
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
  - simpl.
    case_eq (beq_nat x0 (length (G2 ++ G0))); intros E.
    + eapply beq_nat_true_iff in E.
      apply indexr_max in H. subst.
      rewrite app_length in H. apply plus_lt_contra in H. inversion H.
    + apply IHG2. assumption.
Qed.

Lemma indexr_splice_lo: forall G0 G2 x0 v1 T f,
    indexr x0 (G2 ++ G0) = Some T ->
    x0 < length G0 ->
    indexr x0 (map (splice f) G2 ++ v1 :: G0) = Some T.
Proof.
  intros.
  assert (indexr x0 G0 = Some T). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.

Lemma indexr_spliceat_lo: forall G0 G2 x0 v1 G T f,
    indexr x0 (G2 ++ G0) = Some (G, T) ->
    x0 < length G0 ->
    indexr x0 (map (spliceat f) G2 ++ v1 :: G0) = Some (G, T).
Proof.
  intros.
  assert (indexr x0 G0 = Some (G, T)). eapply indexr_splice_lo0; eauto.
  eapply indexr_extend_mult. eapply indexr_extend. eauto.
Qed.

Lemma closed_splice: forall i j k T n,
  closed i j k T ->
  closed i (S j) k (splice n T).
Proof.
  intros. induction H; simpl; eauto.
  case_eq (le_lt_dec n x); intros E LE.
  apply cl_selh. omega.
  apply cl_selh. omega.
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
  - apply cl_all. apply IHclosed1; omega. apply IHclosed2; omega.
Qed.

Lemma closed_inc: forall i j k T,
  closed i j k T ->
  closed i (S j) k T.
Proof.
  intros. apply (closed_inc_mult i j k T H i (S j) k); omega.
Qed.

Lemma closed_splice_idem: forall i j k T n,
                            closed i j k T ->
                            n >= j ->
                            splice n T = T.
Proof.
  intros. induction H; eauto.
  - (* TAll *) simpl.
    rewrite IHclosed1. rewrite IHclosed2.
    reflexivity.
    assumption. assumption.
  - (* TVarH *) simpl.
    case_eq (le_lt_dec n x); intros E LE. omega. reflexivity.
  - (* TMem *) simpl.
    rewrite IHclosed1. rewrite IHclosed2.
    reflexivity.
    assumption. assumption.
Qed.

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
           end.

Ltac inv_mem := match goal with
                  | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |-
                    closed 0 (length ?GH) (length ?G) ?T2 => inversion H; subst; eauto
                  | H: closed 0 (length ?GH) (length ?G) (TMem ?T1 ?T2) |-
                    closed 0 (length ?GH) (length ?G) ?T1 => inversion H; subst; eauto
                end.

Lemma stp_closed : forall G GH T1 T2,
                     stp G GH T1 T2 ->
                     closed 0 (length GH) (length G) T1 /\ closed 0 (length GH) (length G) T2.
Proof.
  intros. induction H;
    try solve [repeat ev; split; try inv_mem; eauto using indexr_max].
Qed.

Lemma stp_closed2 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) (length G1) T2.
Proof.
  intros. apply (proj2 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp_closed1 : forall G1 GH T1 T2,
                       stp G1 GH T1 T2 ->
                       closed 0 (length GH) (length G1) T1.
Proof.
  intros. apply (proj1 (stp_closed G1 GH T1 T2 H)).
Qed.

Lemma stp2_closed: forall G1 G2 T1 T2 GH s m n,
                     stp2 s m G1 T1 G2 T2 GH n ->
                     closed 0 (length GH) (length G1) T1 /\ closed 0 (length GH) (length G2) T2.
  intros. induction H;
    try solve [repeat ev; split; try inv_mem; eauto using indexr_max].
Qed.

Lemma stp2_closed2 : forall G1 G2 T1 T2 GH s m n,
                       stp2 s m G1 T1 G2 T2 GH n ->
                       closed 0 (length GH) (length G2) T2.
Proof.
  intros. apply (proj2 (stp2_closed G1 G2 T1 T2 GH s m n H)).
Qed.

Lemma stp2_closed1 : forall G1 G2 T1 T2 GH s m n,
                       stp2 s m G1 T1 G2 T2 GH n ->
                       closed 0 (length GH) (length G1) T1.
Proof.
  intros. apply (proj1 (stp2_closed G1 G2 T1 T2 GH s m n H)).
Qed.

Lemma closed_upgrade: forall i j k i' T,
 closed i j k T ->
 i' >= i ->
 closed i' j k T.
Proof.
 intros. apply (closed_inc_mult i j k T H i' j k); omega.
Qed.

Lemma closed_upgrade_free: forall i j k j' T,
 closed i j k T ->
 j' >= j ->
 closed i j' k T.
Proof.
 intros. apply (closed_inc_mult i j k T H i j' k); omega.
Qed.

Lemma closed_upgrade_freef: forall i j k k' T,
 closed i j k T ->
 k' >= k ->
 closed i j k' T.
Proof.
 intros. apply (closed_inc_mult i j k T H i j k'); omega.
Qed.

Lemma closed_open: forall i j k V T, closed (i+1) j k T -> closed i j k (TSel V) ->
  closed i j k (open_rec i V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.
  eapply closed_upgrade. eauto. eauto.
  - Case "TVarB". simpl.
    case_eq (beq_nat i x); intros E. eauto.
    econstructor. eapply beq_nat_false_iff in E. omega.
Qed.

Lemma indexr_has: forall X (G: list X) x,
  length G > x ->
  exists v, indexr x G = Some v.
Proof.
  intros. remember (length G) as n.
  generalize dependent x.
  generalize dependent G.
  induction n; intros; try omega.
  destruct G; simpl.
  - simpl in Heqn. inversion Heqn.
  - simpl in Heqn. inversion Heqn. subst.
    case_eq (beq_nat x (length G)); intros E.
    + eexists. reflexivity.
    + apply beq_nat_false in E. apply IHn; eauto.
      omega.
Qed.

Lemma stp_refl_aux: forall n T G GH,
  closed 0 (length GH) (length G) T ->
  tsize_flat T < n ->
  stp G GH T T.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst; eauto;
  try solve [omega];
  try solve [simpl in H0; constructor; apply IHn; eauto; try omega];
  try solve [apply indexr_has in H1; destruct H1; eauto].
  - simpl in H0.
    eapply stp_all.
    eapply IHn; eauto; try omega.
    reflexivity.
    assumption.
    assumption.
    apply IHn; eauto.
    simpl. apply closed_open; auto using closed_inc.
    unfold open. rewrite <- open_preserves_size. omega.
Qed.

Lemma stp_refl: forall T G GH,
  closed 0 (length GH) (length G) T ->
  stp G GH T T.
Proof.
  intros. apply stp_refl_aux with (n:=S (tsize_flat T)); eauto.
Qed.

Definition stpd2 s m G1 T1 G2 T2 GH := exists n, stp2 s m G1 T1 G2 T2 GH n.

Ltac ep := match goal with
             | [ |- stp2 ?S ?M ?G1 ?T1 ?G2 ?T2 ?GH ?N ] =>
               assert (exists (n:nat), stp2 S M G1 T1 G2 T2 GH n) as EEX
           end.

Ltac eu := match goal with
             | H: stpd2 _ _ _ _ _ _ _ |- _ =>
               destruct H as [? H]
           end.

Hint Unfold stpd2.

Lemma stp2_refl_aux: forall n T G GH s,
  closed 0 (length GH) (length G) T ->
  tsize_flat T < n ->
  stpd2 s true G T G T GH.
Proof.
  intros n. induction n; intros; try omega.
  inversion H; subst; eauto; try omega; try simpl in H0.
  - destruct (IHn T1 G GH false) as [n1 IH1]; eauto; try omega.
    destruct (IHn (open (varH (length GH)) T2) G ((G,T1)::GH) false); eauto; try omega.
    simpl. apply closed_open; auto using closed_inc.
    unfold open. rewrite <- open_preserves_size. omega.
    eexists; econstructor; try constructor; eauto.
  - eapply indexr_has in H1. destruct H1 as [v HI].
    eexists; eapply stp2_selx; eauto.
  - eapply indexr_has in H1. destruct H1 as [v HI].
    eexists; eapply stp2_selax; eauto.
  - destruct (IHn T1 G GH s) as [n1 IH1]; eauto; try omega.
    destruct (IHn T2 G GH s) as [n2 IH2]; eauto; try omega.
    destruct s; eexists; econstructor; try constructor; eauto.
Grab Existential Variables. apply 0. apply 0. apply 0. apply 0.
Qed.

Lemma stp2_refl: forall T G GH s,
  closed 0 (length GH) (length G) T ->
  stpd2 s true G T G T GH.
Proof.
  intros. apply stp2_refl_aux with (n:=S (tsize_flat T)); eauto.
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
  length GL = x0 ->
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
  length GL = x0 ->
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

Lemma stp_splice : forall GX G0 G1 T1 T2 v1,
   stp GX (G1++G0) T1 T2 ->
   stp GX ((map (splice (length G0)) G1) ++ v1::G0)
       (splice (length G0) T1) (splice (length G0) T2).
Proof. admit. (*PERF
  intros GX G0 G1 T1 T2 v1 H. remember (G1++G0) as G.
  revert G0 G1 HeqG.
  induction H; intros; subst GH; simpl; eauto.
  - Case "top".
    eapply stp_top.
    rewrite map_splice_length_inc.
    apply closed_splice.
    assumption.
  - Case "bot".
    eapply stp_bot.
    rewrite map_splice_length_inc.
    apply closed_splice.
    assumption.
  - Case "sel1".
    eapply stp_sel1. apply H. assumption.
    assert (splice (length G0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp. reflexivity.
  - Case "sel2".
    eapply stp_sel2. apply H. assumption.
    assert (splice (length G0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp. reflexivity.
  - Case "sela1".
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_sela1.
      apply indexr_splice_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x = x +1) as A by omega.
      rewrite <- A. eapply H0.
      eapply IHstp. eauto.
    + eapply stp_sela1. eapply indexr_splice_lo. eauto. eauto. eauto.
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp. eauto.
(*  - Case "sela2".
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_sela2.
      apply indexr_splice_hi. eauto. eauto.
      eapply closed_splice in H0. assert (S x = x +1) as A by omega.
      rewrite <- A. eapply H0.
      eapply IHstp. eauto.
    + eapply stp_sela2. eapply indexr_splice_lo. eauto. eauto. eauto.
      assert (splice (length G0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp. eauto. *)
  - Case "selax".
    case_eq (le_lt_dec (length G0) x); intros E LE.
    + eapply stp_selax.
      eapply indexr_splice_hi. eassumption. assumption.
    + eapply stp_selax. eapply indexr_splice_lo. eauto. eauto.
  - Case "all".
    eapply stp_all.
    eapply IHstp1. eauto. eauto. eauto.

    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.

    simpl. rewrite map_splice_length_inc. apply closed_splice. assumption.

    specialize IHstp2 with (G3:=G0) (G4:=T3 :: G2).
    simpl in IHstp2. rewrite app_length. rewrite map_length. simpl.
    repeat rewrite splice_open_permute with (j:=0). subst x.
    rewrite app_length in IHstp2. simpl in IHstp2.
    eapply IHstp2. eauto.*)
Qed.

Lemma stp2_splice : forall G1 T1 G2 T2 GH1 GH0 v1 s m n,
   stp2 s m G1 T1 G2 T2 (GH1++GH0) n ->
   stp2 s m G1 (splice (length GH0) T1) G2 (splice (length GH0) T2)
        ((map (spliceat (length GH0)) GH1) ++ v1::GH0) n.
Proof. admit. (*PERF
  intros G1 T1 G2 T2 GH1 GH0 v1 s m n H. remember (GH1++GH0) as GH.
  revert GH0 GH1 HeqGH.
  induction H; intros; subst GH; simpl; eauto.
  - Case "top".
    eapply stp2_top.
    rewrite map_spliceat_length_inc.
    apply closed_splice.
    assumption.
  - Case "bot".
    eapply stp2_bot.
    rewrite map_spliceat_length_inc.
    apply closed_splice.
    assumption.
  - Case "strong_sel1".
    eapply stp2_strong_sel1. apply H. assumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp2.
    reflexivity.
  - Case "strong_sel2".
    eapply stp2_strong_sel2. apply H. assumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp2.
    reflexivity.
  - Case "sel1".
    eapply stp2_sel1. apply H. eassumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp2. reflexivity.
  - Case "sel2".
    eapply stp2_sel2. apply H. eassumption. assumption.
    assert (splice (length GH0) TX=TX) as A. {
      eapply closed_splice_idem. eassumption. omega.
    }
    rewrite <- A. apply IHstp2. reflexivity.
  - Case "sela1".
    case_eq (le_lt_dec (length GH0) x); intros E LE.
    + eapply stp2_sela1.
      eapply indexr_spliceat_hi. apply H. eauto.
      eapply closed_splice in H0. assert (S x = x + 1) by omega. rewrite <- H2.
      eapply H0.
      eapply IHstp2. eauto.
    + eapply stp2_sela1. eapply indexr_spliceat_lo. apply H. eauto. eauto.
      assert (splice (length GH0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp2. eauto.
  (* - Case "sela2".
    case_eq (le_lt_dec (length GH0) x); intros E LE.
    + eapply stp2_sela2.
      eapply indexr_spliceat_hi. apply H. eauto.
      eapply closed_splice in H0. assert (S x = x + 1) by omega. rewrite <- H2.
      eapply H0.
      eapply IHstp2. eauto.
    + eapply stp2_sela2. eapply indexr_spliceat_lo. apply H. eauto. eauto.
      assert (splice (length GH0) TX=TX) as A. {
        eapply closed_splice_idem. eassumption. omega.
      }
      rewrite <- A. eapply IHstp2. eauto. *)
  - Case "selax".
    case_eq (le_lt_dec (length GH0) x); intros E LE.
    + destruct v. eapply stp2_selax.
      eapply indexr_spliceat_hi. apply H. eauto.
    + destruct v. eapply stp2_selax.
      eapply indexr_spliceat_lo. apply H. eauto.
  - Case "all".
    apply stp2_all with (x:= length GH1 + S (length GH0)).
    eapply IHstp2_1. reflexivity.

    simpl. rewrite map_spliceat_length_inc. rewrite app_length. omega.
    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.
    simpl. rewrite map_spliceat_length_inc. apply closed_splice. assumption.

    subst x.
    specialize IHstp2_2 with (GH2:=GH0) (GH3:=(G2, T3) :: GH1).
    simpl in IHstp2_2.
    repeat rewrite splice_open_permute with (j:=0).
    rewrite app_length in IHstp2_2.
    eapply IHstp2_2. reflexivity.*)
Qed.

Lemma stp_extend : forall G1 GH T1 T2 v1,
                       stp G1 GH T1 T2 ->
                       stp G1 (v1::GH) T1 T2.
Proof. admit. (*PERF
  intros. induction H; eauto using indexr_extend, closed_inc.
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. apply H1. omega.
  }
  assert (splice (length GH) T4 = T4) as A4. {
    eapply closed_splice_idem. apply H2. omega.
  }
  assert (closed 0 (length GH) (length G1) T3). eapply stp_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (splice (length GH)) [T3] ++ v1::GH =
          (T3::v1::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  apply stp_all with (x:=length (v1 :: GH)).
  apply IHstp1.
  reflexivity.
  apply closed_inc. apply H1.
  apply closed_inc. apply H2.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute. rewrite -> splice_open_permute.
  rewrite <- HGX3.
  apply stp_splice.
  simpl. unfold open in H3. rewrite <- H0. apply H3.*)
Qed.

Lemma stp_extend_mult : forall G T1 T2 GH GH2,
                       stp G GH T1 T2 ->
                       stp G (GH2++GH) T1 T2.
Proof.
  intros. induction GH2.
  - simpl. assumption.
  - simpl.
    apply stp_extend. assumption.
Qed.

Lemma indexr_at_index: forall {A} x0 GH0 GH1 (v:A),
  beq_nat x0 (length GH1) = true ->
  indexr x0 (GH0 ++ v :: GH1) = Some v.
Proof.
  intros. apply beq_nat_true in H. subst.
  induction GH0.
  - simpl. rewrite <- beq_nat_refl. reflexivity.
  - simpl.
    rewrite app_length. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m.
    rewrite false_beq_nat. assumption. omega.
Qed.

Lemma indexr_same: forall {A} x0 (v0:A) GH0 GH1 (v:A) (v':A),
  beq_nat x0 (length GH1) = false ->
  indexr x0 (GH0 ++ v :: GH1) = Some v0 ->
  indexr x0 (GH0 ++ v' :: GH1) = Some v0.
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

Inductive venv_ext : venv -> venv -> Prop :=
| venv_ext_refl : forall G, venv_ext G G
| venv_ext_cons : forall T G1 G2, venv_ext G1 G2 -> venv_ext (T::G1) G2.

Inductive aenv_ext : aenv -> aenv -> Prop :=
| aenv_ext_nil : aenv_ext nil nil
| aenv_ext_cons :
    forall T G' G A A',
      aenv_ext A' A -> venv_ext G' G ->
      aenv_ext ((G',T)::A') ((G,T)::A).

Lemma aenv_ext_refl: forall GH, aenv_ext GH GH.
Proof.
  intros. induction GH.
  - apply aenv_ext_nil.
  - destruct a. apply aenv_ext_cons.
    assumption.
    apply venv_ext_refl.
Qed.

Lemma venv_ext__ge_length:
  forall G G',
    venv_ext G' G ->
    length G' >= length G.
Proof.
  intros. induction H; simpl; omega.
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
    exists ((G', T)::GU'). exists GL'.
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

Lemma indexr_extend_venv : forall G G' x T,
                       indexr x G = Some T ->
                       venv_ext G' G ->
                       indexr x G' = Some T.
Proof.
  intros G G' x T H HV.
  induction HV.
  - assumption.
  - apply indexr_extend. apply IHHV. apply H.
Qed.

Lemma stp2_closure_extend_rec:
  forall G1 G2 T1 T2 GH s m n,
    stp2 s m G1 T1 G2 T2 GH n ->
    (forall G1' G2' GH',
       aenv_ext GH' GH ->
       venv_ext G1' G1 ->
       venv_ext G2' G2 ->
       stp2 s m G1' T1 G2' T2 GH' n).
Proof. admit. (*PERF
  intros G1 G2 T1 T2 GH s m n H.
  induction H; intros; eauto.
  - Case "top".
    eapply stp2_top.
    eapply closed_inc_mult; try eassumption; try omega.
    rewrite (@aenv_ext__same_length GH GH'). omega. assumption.
    apply venv_ext__ge_length. assumption.
  - Case "bot".
    eapply stp2_bot.
    eapply closed_inc_mult; try eassumption; try omega.
    rewrite (@aenv_ext__same_length GH GH'). omega. assumption.
    apply venv_ext__ge_length. assumption.
  - Case "strong_sel1".
    eapply stp2_strong_sel1. eapply indexr_extend_venv. apply H.
    assumption. assumption. assumption.
    apply IHstp2. assumption. apply venv_ext_refl. assumption.
  - Case "strong_sel2".
    eapply stp2_strong_sel2. eapply indexr_extend_venv. apply H.
    assumption. assumption. assumption.
    apply IHstp2. assumption. assumption. apply venv_ext_refl.
  - Case "sel1".
    eapply stp2_sel1. eapply indexr_extend_venv. apply H.
    assumption. eassumption. assumption.
    apply IHstp2. assumption. apply venv_ext_refl. assumption.
  - Case "sel2".
    eapply stp2_sel2. eapply indexr_extend_venv. apply H.
    assumption. eassumption. assumption.
    apply IHstp2. assumption. apply venv_ext_refl. assumption.
  - Case "selx".
    eapply stp2_selx.
    eapply indexr_extend_venv. apply H. assumption.
    eapply indexr_extend_venv. apply H0. assumption.
  - Case "sela1".
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_sela1 with (GX:=GX') (TX:=TX).
    assumption.
    eapply closed_inc_mult; try eassumption; try omega.
    apply venv_ext__ge_length. assumption.
    apply IHstp2; assumption.
 (* - Case "sela2".
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_sela2 with (GX:=GX') (TX:=TX).
    assumption.
    eapply closed_inc_mult; try eassumption; try omega.
    apply venv_ext__ge_length. assumption.
    apply IHstp2; assumption.*)
  - Case "selax".
    destruct v as [GX TX].
    assert (exists GX', indexr x GH' = Some (GX', TX) /\ venv_ext GX' GX) as A. {
      apply indexr_at_ext with (GH:=GH); assumption.
    }
    inversion A as [GX' [H' HX]].
    apply stp2_selax with (v:=(GX',TX)).
    assumption.
  - Case "all".
    eapply stp2_all with (x:=length GH').
    apply IHstp2_1; assumption.
    reflexivity.
    eapply closed_inc_mult; try eassumption; try omega.
    rewrite (@aenv_ext__same_length GH GH'). omega. assumption.
    apply venv_ext__ge_length. assumption.
    eapply closed_inc_mult; try eassumption; try omega.
    rewrite (@aenv_ext__same_length GH GH'). omega. assumption.
    apply venv_ext__ge_length. assumption.
    subst.  rewrite <- (@aenv_ext__same_length GH GH').
    apply IHstp2_2. apply aenv_ext_cons.
    assumption. assumption. assumption. assumption. assumption.
  - Case "trans".
    eapply stp2_transf.
    eapply IHstp2_1.
    assumption. assumption. apply venv_ext_refl.
    eapply IHstp2_2.
    assumption. apply venv_ext_refl. assumption.*)
Qed.

Lemma stp2_closure_extend : forall G1 T1 G2 T2 GH GX T v s m n,
                              stp2 s m G1 T1 G2 T2 ((GX,T)::GH) n ->
                              stp2 s m G1 T1 G2 T2 ((v::GX,T)::GH) n.
Proof.
  intros. eapply stp2_closure_extend_rec. apply H.
  apply aenv_ext_cons. apply aenv_ext_refl. apply venv_ext_cons.
  apply venv_ext_refl. apply venv_ext_refl. apply venv_ext_refl.
Qed.

Lemma stp2_extend : forall v1 G1 G2 T1 T2 H s m n,
                      stp2 s m G1 T1 G2 T2 H n ->
                       stp2 s m (v1::G1) T1 G2 T2 H n /\
                       stp2 s m G1 T1 (v1::G2) T2 H n /\
                       stp2 s m (v1::G1) T1 (v1::G2) T2 H n.
Proof. admit. (*PERF
  intros. induction H0;
    try solve [split; try split; intros; eauto using indexr_extend];
    try solve [split; try split; intros; constructor; simpl; eauto using indexr_extend, closed_upgrade_freef];
    try solve [split; try split; intros;
               inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]]; eauto];
    try solve [split; try split; intros; inversion IHstp2 as [? [? ?]]; eauto];
    try solve [split; try split; intros; inversion IHstp2 as [? [? ?]]; eauto using indexr_extend];
    try solve [split; try split; intros;
               inversion IHstp2_1 as [? [? ?]]; inversion IHstp2_2 as [? [? ?]];
               eauto; eapply stp2_all; simpl; eauto using stp2_closure_extend, closed_upgrade_freef]. *)
Qed.

Lemma stp2_extend2 : forall v1 G1 G2 T1 T2 H s m n,
                       stp2 s m G1 T1 G2 T2 H n ->
                       stp2 s m G1 T1 (v1::G2) T2 H n.
Proof.
  intros. apply (proj2 (stp2_extend v1 G1 G2 T1 T2 H s m n H0)).
Qed.

Lemma stp2_extend1 : forall v1 G1 G2 T1 T2 H s m n,
                       stp2 s m G1 T1 G2 T2 H n ->
                       stp2 s m (v1::G1) T1 G2 T2 H n.
Proof.
  intros. apply (proj1 (stp2_extend v1 G1 G2 T1 T2 H s m n H0)).
Qed.

Lemma stp2_extendH : forall v1 G1 G2 T1 T2 GH s m n,
                       stp2 s m G1 T1 G2 T2 GH n ->
                       stp2 s m G1 T1 G2 T2 (v1::GH) n.
Proof.
  intros.
  induction H;
    try solve [try constructor; simpl; eauto using indexr_extend, closed_upgrade_free];
    try solve [eapply stp2_transf; simpl; eauto].
  assert (splice (length GH) T2 = T2) as A2. {
    eapply closed_splice_idem. apply H1. omega.
  }
  assert (splice (length GH) T4 = T4) as A4. {
    eapply closed_splice_idem. apply H2. omega.
  }
  assert (closed 0 (length GH) (length G2) T3). eapply stp2_closed1. eauto.
  assert (splice (length GH) T3 = T3) as A3. {
    eapply closed_splice_idem. eauto. omega.
  }
  assert (map (spliceat (length GH)) [(G2, T3)] ++ v1::GH =
          ((G2, T3)::v1::GH)) as HGX3. {
    simpl. rewrite A3. eauto.
  }
  eapply stp2_all.
  apply IHstp2_1.
  reflexivity.
  apply closed_inc. apply H1.
  apply closed_inc. apply H2.
  simpl.
  rewrite <- A2. rewrite <- A4.
  unfold open.
  change (varH (S (length GH))) with (varH (0 + (S (length GH)))).
  rewrite -> splice_open_permute.
  rewrite -> splice_open_permute.
  rewrite <- HGX3.
  apply stp2_splice.
  subst x. simpl. unfold open in H3. apply H3.
Qed.

Lemma stp2_extendH_mult : forall G1 G2 T1 T2 H H2 s m n,
                       stp2 s m G1 T1 G2 T2 H n ->
                       stp2 s m G1 T1 G2 T2 (H2++H) n.
Proof.
  intros. induction H2.
  - simpl. assumption.
  - simpl.
    apply stp2_extendH. assumption.
Qed.

Lemma stp2_extendH_mult0 : forall G1 G2 T1 T2 H2 s m n,
                       stp2 s m G1 T1 G2 T2 [] n ->
                       stp2 s m G1 T1 G2 T2 H2 n.
Proof.
  intros.
  assert (H2 = H2++[]) as A by apply app_nil_end. rewrite A.
  apply stp2_extendH_mult. assumption.
Qed.

Lemma stp2_reg  : forall G1 G2 T1 T2 GH s m n,
                    stp2 s m G1 T1 G2 T2 GH n ->
                    stpd2 s true G1 T1 G1 T1 GH /\ stpd2 s true G2 T2 G2 T2 GH.
Proof.
  intros.
  apply stp2_closed in H. destruct H as [H1 H2].
  split; apply stp2_refl; assumption.
Qed.

Lemma stp2_reg2 : forall G1 G2 T1 T2 GH s m n,
                       stp2 s m G1 T1 G2 T2 GH n ->
                       stpd2 s true G2 T2 G2 T2 GH.
Proof.
  intros. apply (proj2 (stp2_reg G1 G2 T1 T2 GH s m n H)).
Qed.

Lemma stp2_reg1 : forall G1 G2 T1 T2 GH s m n,
                       stp2 s m G1 T1 G2 T2 GH n ->
                       stpd2 s true G1 T1 G1 T1 GH.
Proof.
  intros. apply (proj1 (stp2_reg G1 G2 T1 T2 GH s m n H)).
Qed.

Lemma stp_reg  : forall G GH T1 T2,
                    stp G GH T1 T2 ->
                    stp G GH T1 T1 /\ stp G GH T2 T2.
Proof.
  intros.
  apply stp_closed in H. destruct H as [H1 H2].
  split; apply stp_refl; assumption.
Qed.

Lemma stp_reg2 : forall G GH T1 T2,
                       stp G GH T1 T2 ->
                       stp G GH T2 T2.
Proof.
  intros. apply (proj2 (stp_reg G GH T1 T2 H)).
Qed.

Lemma stp_reg1 : forall G GH T1 T2,
                       stp G GH T1 T2 ->
                       stp G GH T1 T1.
Proof.
  intros. apply (proj1 (stp_reg G GH T1 T2 H)).
Qed.

Lemma stpd2_extend2 : forall v1 G1 G2 T1 T2 H s m,
                       stpd2 s m G1 T1 G2 T2 H ->
                       stpd2 s m G1 T1 (v1::G2) T2 H.
Proof.
  intros. destruct H0 as [n Hsub]. eexists n.
  apply stp2_extend2; eauto.
Qed.

Lemma stpd2_extend1 : forall v1 G1 G2 T1 T2 H s m,
                       stpd2 s m G1 T1 G2 T2 H ->
                       stpd2 s m (v1::G1) T1 G2 T2 H.
Proof.
  intros. destruct H0 as [n Hsub]. eexists n.
  apply stp2_extend1; eauto.
Qed.

Lemma stpd2_extendH : forall v1 G1 G2 T1 T2 GH s m,
                       stpd2 s m G1 T1 G2 T2 GH ->
                       stpd2 s m G1 T1 G2 T2 (v1::GH).
Proof.
  intros. destruct H as [n Hsub]. exists n.
  apply stp2_extendH; eauto.
Qed.

Lemma stpd2_extendH_mult : forall G1 G2 T1 T2 GH GH2 s m,
                       stpd2 s m G1 T1 G2 T2 GH ->
                       stpd2 s m G1 T1 G2 T2 (GH2++GH).
Proof.
  intros. destruct H as [n Hsub]. exists n.
  apply stp2_extendH_mult; eauto.
Qed.

Lemma stpd2_closed2 : forall G1 G2 T1 T2 GH s m,
                       stpd2 s m G1 T1 G2 T2 GH ->
                       closed 0 (length GH) (length G2) T2.
Proof.
  intros. destruct H as [n Hsub].
  eapply stp2_closed2; eauto.
Qed.

Lemma stpd2_closed1 : forall G1 G2 T1 T2 GH s m,
                       stpd2 s m G1 T1 G2 T2 GH ->
                       closed 0 (length GH) (length G1) T1.
Proof.
  intros. destruct H as [n Hsub].
  eapply stp2_closed1; eauto.
Qed.


Lemma valtp_stub_extend : forall vs v v1 T,
                       val_type_stub vs v T ->
                       val_type_stub (v1::vs) v T.
Proof.
  intros. induction H; eauto; econstructor; eauto; eapply stpd2_extend2; eauto.
Qed.



Lemma indexr_safe_ex: forall H1 G1 TF i,
             R_env H1 G1 ->
             indexr i G1 = Some TF ->
             exists v, indexr i H1 = Some v /\ val_type H1 [] v TF.
Proof.
  intros. destruct H. destruct (H2 i TF H0) as [v [E V]].
  exists v. split; eauto. destruct E as [n E].
  assert (S n > n) as N. omega. specialize (E (S n) N).
  simpl in E. inversion E. eauto.
Qed.

Lemma index_safeh_ex: forall H1 H2 G1 GH TF i,
             R_env H1 G1 -> R_envh H1 H2 GH ->
             indexr i GH = Some TF ->
             exists v, indexr i H2 = Some v /\ valh_type H1 H2 v TF.
Proof.
  intros. destruct H0. specialize (H4 i TF H3).
  exists (H1,TF). split. eauto. eapply v_tya.
Qed.



Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv [] v T ->
      res_type venv (Some v) T.

Hint Constructors res_type.
Hint Resolve not_stuck.

(* ### Transitivity ### *)

Lemma stpd2_top: forall G1 G2 GH T s,
    closed 0 (length GH) (length G1) T ->
    stpd2 s true G1 T G2 TTop GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_bot: forall G1 G2 GH T s,
    closed 0 (length GH) (length G2) T ->
    stpd2 s true G1 TBot G2 T GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_mem: forall G1 G2 S1 U1 S2 U2 GH s,
    stpd2 s s G1 U1 G2 U2 GH ->
    stpd2 s false G2 S2 G1 S1 GH ->
    stpd2 s true G1 (TMem S1 U1) G2 (TMem S2 U2) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_strong_sel1: forall G1 G2 GX TX x T2 GH,
    indexr x G1 = Some (vty GX TX) ->
    val_type_stub GX (vty GX TX) (TMem TX TX) -> (* for downgrade *)
    closed 0 0 (length GX) TX ->
    stpd2 true true GX TX G2 T2 GH ->
    stpd2 true true G1 (TSel (varF x)) G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_strong_sel2: forall G1 G2 GX TX x T1 GH,
    indexr x G2 = Some (vty GX TX) ->
    val_type_stub GX (vty GX TX) (TMem TX TX) -> (* for downgrade *)
    closed 0 0 (length GX) TX ->
    stpd2 true false G1 T1 GX TX GH ->
    stpd2 true true G1 T1 G2 (TSel (varF x)) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_sel1: forall G1 G2 v GX TX x T2 GH,
    indexr x G1 = Some v ->
    val_type_stub GX v TX ->
    closed 0 0 (length GX) TX ->
    stpd2 false false GX TX G2 (TMem TBot T2) GH ->
    stpd2 false true G1 (TSel (varF x)) G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_sel2: forall G1 G2 v GX TX x T1 GH,
    indexr x G2 = Some v ->
    val_type_stub GX v TX ->
    closed 0 0 (length GX) TX ->
    stpd2 false false GX TX G1 (TMem T1 TTop) GH ->
    stpd2 false true G1 T1 G2 (TSel (varF x)) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_selx: forall G1 G2 v x1 x2 GH s,
    indexr x1 G1 = Some v ->
    indexr x2 G2 = Some v ->
    stpd2 s true G1 (TSel (varF x1)) G2 (TSel (varF x2)) GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_sela1: forall G1 G2 GX TX x T2 GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 x (length GX) TX ->
    stpd2 false false GX TX G2 (TMem TBot T2) GH ->
    stpd2 false true G1 (TSel (varH x)) G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
(*Lemma stpd2_sela2: forall G1 G2 GX T1 TX x GH,
    indexr x GH = Some (GX, TX) ->
    closed 0 x (length GX) TX ->
    stpd2 false false GX TX G1 (TMem T1 TTop) GH ->
    stpd2 false true G1 T1 G2 (TSel (varH x)) GH.
Proof. intros. repeat eu. eauto. Qed. *)
Lemma stpd2_selax: forall G1 G2 v x GH s,
    indexr x GH = Some v ->
    stpd2 s true G1 (TSel (varH x)) G2 (TSel (varH x)) GH.
Proof. intros. exists (S 0). eauto. Qed.
Lemma stpd2_all: forall G1 G2 T1 T2 T3 T4 x GH s,
    stpd2 false false G2 T3 G1 T1 GH ->
    x = length GH ->
    closed 1 (length GH) (length G1) T2 ->
    closed 1 (length GH) (length G2) T4 ->
    stpd2 false false G1 (open (varH x) T2) G2 (open (varH x) T4) ((G2, T3)::GH) ->
    stpd2 s true G1 (TAll T1 T2) G2 (TAll T3 T4) GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_wrapf: forall G1 G2 T1 T2 GH s,
    stpd2 s true G1 T1 G2 T2 GH ->
    stpd2 s false G1 T1 G2 T2 GH.
Proof. intros. repeat eu. eauto. Qed.
Lemma stpd2_transf: forall G1 G2 G3 T1 T2 T3 GH s,
    stpd2 s true G1 T1 G2 T2 GH ->
    stpd2 s false G2 T2 G3 T3 GH ->
    stpd2 s false G1 T1 G3 T3 GH.
Proof. intros. repeat eu. eauto. Qed.

Lemma stpd2_trans_aux: forall n, forall G1 G2 G3 T1 T2 T3 H s n1,
  stp2 s false G1 T1 G2 T2 H n1 -> n1 < n ->
  stpd2 s false G2 T2 G3 T3 H ->
  stpd2 s false G1 T1 G3 T3 H.
Proof.
  intros n. induction n; intros; try omega; repeat eu; subst; inversion H0.
  - Case "wrapf". eapply stpd2_transf; eauto.
  - Case "transf". eapply stpd2_transf. eauto. eapply IHn. eauto. omega. eauto.
Qed.

Lemma stpd2_trans: forall G1 G2 G3 T1 T2 T3 H s,
  stpd2 s false G1 T1 G2 T2 H ->
  stpd2 s false G2 T2 G3 T3 H ->
  stpd2 s false G1 T1 G3 T3 H.
Proof. intros. repeat eu. eapply stpd2_trans_aux; eauto. Qed.

Lemma stp2_narrow_aux: forall n, forall m G1 T1 G2 T2 GH n0,
  stp2 false m G1 T1 G2 T2 GH n0 ->
  n0 <= n ->
  forall GH1 GH0 GH' GX1 TX1 GX2 TX2,
    GH=GH1++[(GX2,TX2)]++GH0 ->
    GH'=GH1++[(GX1,TX1)]++GH0 ->
    stpd2 false false GX1 TX1 GX2 TX2 GH0 ->
    stpd2 false m G1 T1 G2 T2 GH'.
Proof. admit. (*PERF
  intros n.
  induction n.
  - Case "z". intros. inversion H0. subst. inversion H; eauto.
  - Case "s n". intros m G1 T1 G2 T2 GH n0 H NE. inversion H; subst;
    intros GH1 GH0 GH' GX1 TX1 GX2 TX2 EGH EGH' HX; eauto.
    + SCase "top". eapply stpd2_top.
      subst. rewrite app_length. simpl. rewrite app_length in H0. simpl in H0. apply H0.
    + SCase "bot". eapply stpd2_bot.
      subst. rewrite app_length. simpl. rewrite app_length in H0. simpl in H0. apply H0.
    + SCase "mem_true". eapply stpd2_mem.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
    + SCase "sel1". eapply stpd2_sel1; try eassumption.
      eapply IHn; try eassumption. omega.
    + SCase "sel2". eapply stpd2_sel2; try eassumption.
      eapply IHn; try eassumption. omega.
    + SCase "sela1".
      unfold id,venv,aenv in *.
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(GX2, TX2)]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        unfold venv in A2'. rewrite A2' in H0. inversion H0. subst.
        inversion HX as [nx HX'].
        eapply stpd2_sela1.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        apply beq_nat_true in E. rewrite E. eapply stp2_closed1. eassumption.
        eapply stpd2_trans.
        eexists. eapply stp2_extendH_mult. eapply stp2_extendH_mult. eassumption.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_sela1. eapply A. assumption.
        eapply IHn; try eassumption. omega.
(*    + SCase "sela2".
      unfold id,venv,aenv in *.
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(GX2, TX2)]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        unfold venv in A2'. rewrite A2' in H0. inversion H0. subst.
        inversion HX as [nx HX'].
        eapply stpd2_sela2.
        eapply indexr_extend_mult. simpl. rewrite E. reflexivity.
        apply beq_nat_true in E. rewrite E. eapply stp2_closed1. eassumption.
        eapply stpd2_trans.
        eexists. eapply stp2_extendH_mult. eapply stp2_extendH_mult. eassumption.
        eapply IHn; try eassumption. omega.
        reflexivity. reflexivity.
      * assert (indexr x GH' = Some (GX, TX)) as A. {
          subst.
          eapply indexr_same. apply E. eassumption.
        }
        eapply stpd2_sela2. eapply A. assumption.
        eapply IHn; try eassumption. omega.*)
    + SCase "selax".
      unfold id,venv,aenv in *.
      case_eq (beq_nat x (length GH0)); intros E.
      * assert (indexr x ([(GX2, TX2)]++GH0) = Some (GX2, TX2)) as A2. {
          simpl. rewrite E. reflexivity.
        }
        assert (indexr x GH = Some (GX2, TX2)) as A2'. {
          rewrite EGH. eapply indexr_extend_mult. apply A2.
        }
        unfold venv in A2'. rewrite A2' in H0. inversion H0. subst.
        inversion HX as [nx HX'].
        eapply stpd2_selax.
        eapply indexr_extend_mult. simpl. unfold id,venv,aenv in *. rewrite E.
        reflexivity.
      * assert (indexr x GH' = Some v) as A. {
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
      rewrite <- A. reflexivity.
      rewrite <- A. assumption. rewrite <- A. assumption.
      subst.
      eapply IHn with (GH1:=(G2, T4) :: GH1); try eassumption. omega.
      simpl. reflexivity. simpl. reflexivity.
    + SCase "wrapf".
      eapply stpd2_wrapf.
      eapply IHn; try eassumption. omega.
    + SCase "transf".
      eapply stpd2_transf.
      eapply IHn; try eassumption. omega.
      eapply IHn; try eassumption. omega.
Grab Existential Variables. apply 0. *)
Qed.

Lemma stpd2_narrow: forall G1 G2 G3 G4 T1 T2 T3 T4 H,
  stpd2 false false G1 T1 G2 T2 H -> (* careful about H! *)
  stpd2 false false G3 T3 G4 T4 ((G2,T2)::H) ->
  stpd2 false false G3 T3 G4 T4 ((G1,T1)::H).
Proof.
  intros. inversion H1 as [n H'].
  eapply (stp2_narrow_aux n) with (GH1:=[]) (GH0:=H). eapply H'. omega.
  simpl. reflexivity. reflexivity.
  assumption.
Qed.

Ltac indexr_contra :=
  match goal with
    | H: indexr ?N [] = Some ?V |- _ => simpl in H; inversion H
  end.

Lemma stpd2_untrans_aux: forall n, forall m G1 G2 G3 T1 T2 T3 GH n1,
  stp2 true m G1 T1 G2 T2 GH n1 -> n1 < n ->
  stpd2 true true G2 T2 G3 T3 GH ->
  stpd2 true true G1 T1 G3 T3 GH.
Proof. admit. (*PERF
  intros n. induction n; intros; try omega. eu.
  inversion H; subst;
  try solve [inversion H1; eexists; eauto];
  try solve [eapply stpd2_bot; eauto using stp2_closed2];
  try solve [eapply stpd2_strong_sel1; eauto; eapply IHn; eauto; try omega];
  try solve [eapply IHn; [eapply H2 | omega | eauto]]; (* wrapf *)
  try solve [eapply IHn; [eapply H2 | omega | (eapply IHn; [ eapply H3 | omega | eauto ])]]; (* transf *)
  inversion H1; subst;
  try solve [eapply stpd2_top; eauto using stp2_closed1];
  try solve [eapply stpd2_strong_sel2; eauto];
  try solve [eapply stpd2_mem; [eapply IHn; eauto; try omega |
                                eapply stpd2_trans; eauto]];
  try solve [eapply stpd2_sela1; eauto; eapply stpd2_wrapf; eapply IHn; eauto; try omega];
  try solve [indexr_contra].
  - Case "sel2 - sel1".
    rewrite H7 in H2. inversion H2. subst.
    eapply IHn. eapply H5. omega. eauto.
  - Case "sel2 - selx".
    rewrite H7 in H2. inversion H2. subst.
    eapply stpd2_strong_sel2; eauto.
  - Case "selx - sel1".
    rewrite H5 in H3. inversion H3. subst.
    eapply stpd2_strong_sel1; eauto.
  - Case "selx - selx".
    rewrite H5 in H3. inversion H3. subst.
    eapply stpd2_selx; eauto.
  - Case "selax - selax".
    eapply stpd2_selax; eauto.
  - Case "all - all".
    eapply stpd2_all; eauto.
    eapply stpd2_trans; eauto.
    eapply stpd2_trans. eapply stpd2_narrow. eexists. eapply H8. eauto. eauto.
Grab Existential Variables. apply 0. *)
Qed.

(* We don't generally need to push back transitivity in non-empty abstract contexts. *)
Lemma stpd2_strong_trans: forall G1 G2 G3 T1 T2 T3,
  stpd2 true true G1 T1 G2 T2 [] ->
  stpd2 true true G2 T2 G3 T3 [] ->
  stpd2 true true G1 T1 G3 T3 [].
Proof. intros. repeat eu. eapply stpd2_untrans_aux; eauto. Qed.

Lemma stpd2_strong_untrans: forall G1 G2 T1 T2,
  stpd2 true false G1 T1 G2 T2 [] ->
  stpd2 true true G1 T1 G2 T2 [].
Proof.
  intros. destruct H as [n H].
  eapply stpd2_untrans_aux; eauto using stp2_reg2.
Qed.

Lemma stpd2_downgrade_aux: forall G1 G2 T1 T2 H m,
  stpd2 true m G1 T1 G2 T2 H ->
  stpd2 false m G1 T1 G2 T2 H.
Proof. admit. (*PERF
  intros. inversion H0. dependent induction H1; try solve [eexists; eauto].
  - Case "mem".
    eapply stpd2_mem. eapply stpd2_wrapf. eapply IHstp2_1. eexists. eassumption.
    eapply IHstp2_2. eexists. eassumption.
  - Case "sel1".
    eapply stpd2_sel1; eauto. simpl.
    eapply stpd2_wrapf. eapply stpd2_mem.
    eapply stpd2_wrapf. eapply IHstp2. eexists. eassumption.
    eapply stpd2_wrapf. eapply stpd2_bot.
    eapply closed_upgrade_free. eassumption. omega.
  - Case "sel2".
    eapply stpd2_sel2; eauto. simpl.
    eapply stpd2_wrapf. eapply stpd2_mem.
    eapply stpd2_wrapf. eapply stpd2_top.
    simpl. eapply closed_upgrade_free. eassumption. omega.
    eapply IHstp2. eexists. eassumption.
  - Case "wrap".
    eapply stpd2_wrapf. eapply IHstp2. eexists. eassumption.
  - Case "trans".
    eapply stpd2_transf.
    eapply IHstp2_1. eexists. eassumption.
    eapply IHstp2_2. eexists. eassumption.
  Grab Existential Variables.
  apply 0. apply 0. apply 0. apply 0. *)
Qed.

Lemma stpd2_downgrade: forall G1 G2 T1 T2 H,
  stpd2 true true G1 T1 G2 T2 H ->
  stpd2 false false G1 T1 G2 T2 H.
Proof.
  intros. eapply stpd2_downgrade_aux. eapply stpd2_wrapf. assumption.
Qed.

Lemma valtp_stub_widen: forall vf H1 H2 T1 T2,
  val_type_stub H1 vf T1 ->
  stpd2 true true H1 T1 H2 T2 [] ->
  val_type_stub H2 vf T2.
Proof.
  intros. inversion H; subst; econstructor; eauto; eapply stpd2_strong_trans; eauto.
Qed.






Lemma invert_typ: forall venv vx S U,
  val_type_stub venv vx (TMem S U) ->
  exists GX TX,
    vx = (vty GX TX) /\
    stpd2 true false venv S GX TX [] /\
    stpd2 true true GX TX venv U [].
Proof.
  intros. inversion H; ev; try solve by inversion; inversion H0; subst;
  repeat eexists; eauto.
Qed.

Lemma stpd2_to_strong_aux: forall n, forall G1 G2 T1 T2 m n1,
  stp2 false m G1 T1 G2 T2 [] n1 -> n1 < n ->
  stpd2 true m G1 T1 G2 T2 [].
Proof. admit. (*PERF
  intros n. induction n; intros; try omega.
  inversion H; subst; try solve [inversion H1].
  - Case "top".
    eapply stpd2_top; eauto.
  - Case "bot".
    eapply stpd2_bot; eauto.
  - Case "mem".
    eapply stpd2_mem; auto.
    eapply stpd2_strong_untrans. eapply IHn; eauto. omega.
    eapply IHn; eauto. omega.
  - Case "sel1".
    eapply IHn in H4. eapply stpd2_strong_untrans in H4.
    eapply valtp_stub_widen with (2:=H4) in H2.
    remember H2 as Hv. clear HeqHv.
    eapply invert_typ in H2. ev. subst.
    assert (closed 0 (length ([]:aenv)) (length x0) x1). eapply stpd2_closed1; eauto.
    eapply stpd2_strong_sel1. eauto. eauto.
    inversion Hv; subst.
    eapply v_ty. eapply stp2_refl. eauto. eauto.
    eassumption. omega.
  - Case "sel2".
    eapply IHn in H4. eapply stpd2_strong_untrans in H4.
    eapply valtp_stub_widen with (2:=H4) in H2.
    remember H2 as Hv. clear HeqHv.
    eapply invert_typ in H2. ev. subst.
    assert (closed 0 (length ([]:aenv)) (length x0) x1). eapply stpd2_closed1; eauto.
    eapply stpd2_strong_sel2. eauto. eauto.
    inversion Hv; subst.
    eapply v_ty. eapply stp2_refl. eauto. eauto.
    eassumption. omega.
  - Case "selx".
    eapply stpd2_selx; eauto.
  - Case "all".
    eapply stpd2_all; eauto.
  - Case "wrapf".
    eapply stpd2_wrapf; eauto.
    eapply IHn; eauto. omega.
  - Case "transf".
    eapply stpd2_transf.
    eapply IHn; eauto. omega.
    eapply IHn; eauto. omega. *)
Qed.

Lemma stpd2_to_strong: forall G1 G2 T1 T2 m,
  stpd2 false m G1 T1 G2 T2 [] ->
  stpd2 true m G1 T1 G2 T2 [].
Proof. intros. repeat eu. eapply stpd2_to_strong_aux; eauto. Qed.

Lemma stpd2_upgrade: forall G1 G2 T1 T2,
  stpd2 false false G1 T1 G2 T2 nil ->
  stpd2 true true G1 T1 G2 T2 nil.
Proof.
  intros.
  eapply stpd2_strong_untrans. eapply stpd2_to_strong. eauto.
Qed.


(* ### Substitution for relating static and dynamic semantics ### *)
Lemma indexr_hit2 {X}: forall x (B:X) A G,
  length G = x ->
  B = A ->
  indexr x (B::G) = Some A.
Proof.
  intros.
  unfold indexr.
  assert (beq_nat x (length G) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1. subst. reflexivity.
Qed.

Lemma indexr_miss {X}: forall x (B:X) A G,
  indexr x (B::G) = A ->
  x <> (length G)  ->
  indexr x G = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = false). eapply beq_nat_false_iff. eauto.
  rewrite H1 in H. eauto.
Qed.

Lemma indexr_hit {X}: forall x (B:X) A G,
  indexr x (B::G) = Some A ->
  x = length G ->
  B = A.
Proof.
  intros.
  unfold indexr in H.
  assert (beq_nat x (length G) = true). eapply beq_nat_true_iff. eauto.
  rewrite H1 in H. inversion H. eauto.
Qed.

Lemma indexr_hit0: forall GH (GX0:venv) (TX0:ty),
      indexr 0 (GH ++ [(GX0, TX0)]) =
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

Lemma closed_no_open: forall T x i j k,
  closed i j k T ->
  T = open_rec i x T.
Proof.
  intros. induction H; intros; eauto;
  try solve [compute; compute in IHclosed; rewrite <-IHclosed; auto];
  try solve [compute; compute in IHclosed1; compute in IHclosed2;
             rewrite <-IHclosed1; rewrite <-IHclosed2; auto].

  Case "TVarB".
    unfold open_rec. assert (i <> x0). omega.
    apply beq_nat_false_iff in H0.
    rewrite H0. auto.
Qed.

Lemma open_subst_commute: forall T2 V j k x i,
closed i j k (TSel V) ->
(open_rec i (varH x) (subst V T2)) =
(subst V (open_rec i (varH (x+1)) T2)).
Proof. admit. (*PERF
  intros T2 TX j k. induction T2; intros; eauto; try destruct v; eauto.
  - simpl. rewrite IHT2_1; eauto. rewrite IHT2_2; eauto.
    eapply closed_upgrade. eauto. eauto.
  - simpl.
    case_eq (beq_nat i 0); intros E.
    apply beq_nat_true in E. subst.
    case_eq (beq_nat i0 0); intros E0.
    apply beq_nat_true in E0. subst.
    destruct TX; eauto.
    simpl. destruct i; eauto.
    inversion H; subst. omega.
    simpl. reflexivity.
    case_eq (beq_nat i0 0); intros E0.
    apply beq_nat_true in E0. subst.
    simpl. destruct TX; eauto.
    case_eq (beq_nat i i0); intros E1.
    apply beq_nat_true in E1. subst.
    inversion H; subst. omega.
    reflexivity.
    simpl. reflexivity.
  - simpl.
    case_eq (beq_nat i i0); intros E.
    apply beq_nat_true in E; subst.
    simpl.
    assert (x+1 <> 0) as A by omega.
    eapply beq_nat_false_iff in A.
    rewrite A.
    assert (x = x + 1 - 1) as B. unfold id. omega.
    rewrite <- B. reflexivity.
    simpl. reflexivity.
  - simpl. rewrite IHT2_1. rewrite IHT2_2. eauto. eauto. eauto. *)
Qed.

Lemma closed_no_subst: forall T i k TX,
   closed i 0 k T ->
   subst TX T = T.
Proof.
  intros T. induction T; intros; inversion H; simpl; eauto;
  try solve [rewrite (IHT i k TX); eauto; try omega];
  try solve [rewrite (IHT1 i k TX); eauto; rewrite (IHT2 (S i) k TX); eauto; try omega];
  try solve [rewrite (IHT1 i k TX); eauto; rewrite (IHT2 i k TX); eauto; try omega];
  try omega.
Qed.

Lemma closed_subst: forall i j k V T, closed i (j+1) k T -> closed 0 j k (TSel V) -> closed i j k (subst V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto.

  - Case "TVarH". simpl.
    case_eq (beq_nat x 0); intros E.
    eapply closed_upgrade. eapply closed_upgrade_free.
    eauto. omega. eauto. omega.
    econstructor. assert (x > 0). eapply beq_nat_false_iff in E. omega. omega.
Qed.

Lemma closed_nosubst: forall i j k V T, closed i (j+1) k T -> nosubst T -> closed i j k (subst V T).
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H;
  try econstructor;
  try eapply IHT1; eauto; try eapply IHT2; eauto; try eapply IHT; eauto; subst;
  try inversion H0; eauto.

  - Case "TVarH". simpl. simpl in H0. unfold id in H0.
    assert (beq_nat x 0 = false) as E. apply beq_nat_false_iff. assumption.
    rewrite E.
    eapply cl_selh. omega.
Qed.

Lemma subst_open_commute_m: forall i j k k' j' V T2, closed (i+1) (j+1) k T2 -> closed 0 j' k' (TSel V) ->
    subst V (open_rec i (varH (j+1)) T2) = open_rec i (varH j) (subst V T2).
Proof.
  intros.
  generalize dependent i. generalize dependent j.
  induction T2; intros; inversion H; simpl; eauto; subst;
  try rewrite IHT2_1;
  try rewrite IHT2_2;
  try rewrite IHT2; eauto.
  - Case "TVarH". simpl. case_eq (beq_nat x 0); intros E.
    eapply closed_no_open. eapply closed_upgrade. eauto. omega.
    eauto.
  - Case "TVarB". simpl. case_eq (beq_nat i x); intros E.
    simpl. case_eq (beq_nat (j+1) 0); intros E2.
    eapply beq_nat_true_iff in E2. omega.
    subst. assert (j+1-1 = j) as A. omega. rewrite A. eauto.
    eauto.
Qed.

Lemma subst_open_commute: forall i j k k' V T2, closed (i+1) (j+1) k T2 -> closed 0 0 k' (TSel V) ->
    subst V (open_rec i (varH (j+1)) T2) = open_rec i (varH j) (subst V T2).
Proof.
  intros. eapply subst_open_commute_m; eauto.
Qed.

Lemma subst_open_zero: forall i i' k TX T2, closed i' 0 k T2 ->
    subst TX (open_rec i (varH 0) T2) = open_rec i TX T2.
Proof.
  intros. generalize dependent i'. generalize dependent i.
  induction T2; intros; inversion H; simpl; eauto;
  try solve [rewrite (IHT2_1 _ i'); eauto;
             rewrite (IHT2_2 _ (S i')); eauto;
             rewrite (IHT2_2 _ (S i')); eauto];
  try solve [rewrite (IHT2_1 _ i'); eauto;
             rewrite (IHT2_2 _ i'); eauto].
  subst.
  case_eq (beq_nat x 0); intros E. omega. omega.
  case_eq (beq_nat i x); intros E. eauto. eauto.
Qed.

Lemma Forall2_length: forall A B f (G1:list A) (G2:list B),
                        Forall2 f G1 G2 -> length G1 = length G2.
Proof.
  intros. induction H.
  eauto.
  simpl. eauto.
Qed.

Lemma nosubst_intro: forall i k T, closed i 0 k T -> nosubst T.
Proof.
  intros. generalize dependent i.
  induction T; intros; inversion H; simpl; eauto.
  omega.
Qed.

Lemma nosubst_open: forall i V T2, nosubst (TSel V) -> nosubst T2 -> nosubst (open_rec i V T2).
Proof.
  intros. generalize dependent i. induction T2; intros;
  try inversion H0; simpl; eauto; destruct v; eauto.
  case_eq (beq_nat i i0); intros E. eauto. eauto.
Qed.

(*
when and how we can replace with multiple environments:

stp2 G1 T1 G2 T2 (GH0 ++ [(vty GX TX)])

1) T1 closed

   stp2 G1 T1 G2' T2' (subst GH0)

2) G1 contains (GX TX) at some index x1

   index x1 G1 = (GX TX)
   stp2 G (subst (TVarF x1) T1) G2' T2'

3) G1 = GX

   stp2 G1 (subst TX T1) G2' T2'

4) G1 and GX unrelated

   stp2 ((GX,TX) :: G1) (subst (TVarF (length G1)) T1) G2' T2'

*)

(* ---- two-env substitution. first define what 'compatible' types mean. ---- *)

Definition compat (GX:venv) (TX: ty) (V: option vl) (G1:venv) (T1:ty) (T1':ty) :=
  (exists x1 v, indexr x1 G1 = Some v /\ V = Some v /\ GX = GX /\ val_type_stub GX v TX /\ T1' = (subst (varF x1) T1)) \/
  (closed 0 0 (length G1) T1 /\ T1' = T1) \/ (* this one is for convenience: redundant with next *)
  (nosubst T1 /\ T1' = subst (varF 0) T1).


Definition compat2 (GX:venv) (TX: ty) (V: option vl) (p1:(venv*ty)) (p2:(venv*ty)) :=
  match p1, p2 with
      (G1,T1), (G2,T2) => G1 = G2 /\ compat GX TX V G1 T1 T2
  end.

Lemma closed_compat: forall GX TX V GXX TXX TXX' i j,
  compat GX TX V GXX TXX TXX' ->
  closed 0 j (length GXX) TX ->
  closed i (j+1) (length GXX) TXX ->
  closed i j (length GXX) TXX'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2. destruct H2. destruct H2. destruct H3. destruct H4. destruct H4.
    destruct H5. rewrite H5.
    eapply closed_subst. eauto.
    eapply cl_sel. apply indexr_max in H2. omega.
  - destruct H2. rewrite H3.
    eapply closed_upgrade. eapply closed_upgrade_free. eauto. omega. omega.
  - subst. eapply closed_nosubst. eauto. eauto.
Qed.

Lemma indexr_compat_miss0: forall GH GH' GX TX V (GXX:venv) (TXX:ty) n,
      Forall2 (compat2 GX TX V) GH GH' ->
      indexr (n+1) (GH ++ [(GX, TX)]) = Some (GXX,TXX) ->
      exists TXX', indexr n GH' = Some (GXX,TXX') /\ compat GX TX V GXX TXX TXX'.
Proof.
  intros. revert n H0. induction H.
  - intros. simpl. eauto. simpl in H0. assert (n+1 <> 0). omega.
    eapply beq_nat_false_iff in H. rewrite H in H0. inversion H0.
  - intros. simpl. destruct y.
    case_eq (beq_nat n (length l')); intros E.
    + simpl in H1. rewrite app_length in H1. simpl in H1.
      assert (n = length l'). eapply beq_nat_true_iff. eauto.
      assert (beq_nat (n+1) (length l + 1) = true). eapply beq_nat_true_iff.
      rewrite (Forall2_length _ _ _ _ _ H0). omega.
      rewrite H3 in H1. destruct x. inversion H1. subst. simpl in H.
      destruct H. subst. eexists. eauto.
    + simpl in H1. destruct x.
      assert (n <> length l'). eapply beq_nat_false_iff. eauto.
      assert (beq_nat (n+1) (length l + 1) = false). eapply beq_nat_false_iff.
      rewrite (Forall2_length _ _ _ _ _ H0). omega.
      rewrite app_length in H1. simpl in H1.
      rewrite H3 in H1.
      eapply IHForall2. eapply H1.
Qed.

Lemma compat_top: forall GX TX V G1 T1',
  compat GX TX V G1 TTop T1' -> closed 0 0 (length GX) TX -> T1' = TTop.
Proof.
  intros ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.

Lemma compat_bot: forall GX TX V G1 T1',
  compat GX TX V G1 TBot T1' -> closed 0 0 (length GX) TX -> T1' = TBot.
Proof.
  intros ? ? ? ? ? CC CLX. repeat destruct CC as [|CC]; ev; eauto.
Qed.

Lemma compat_mem: forall GX TX V G1 S1 U1 T1',
    compat GX TX V G1 (TMem S1 U1) T1' ->
    closed 0 0 (length GX) TX ->
    exists SA UA, T1' = TMem SA UA /\
                  compat GX TX V G1 S1 SA /\
                  compat GX TX V G1 U1 UA.
Proof.
  intros ? ? ? ? ? ? ? CC CLX.
  destruct CC as [|CC]; ev; subst.
  repeat eexists; eauto; solve [unfold compat; left; repeat eexists; eassumption].

  destruct CC as [|CC]; ev; subst;
  inversion H; subst;
  repeat eexists; eauto; solve [unfold compat; eauto].
Qed.

Lemma compat_mem_fwd2: forall GX TX V G1 T2 T2',
    compat GX TX V G1 T2 T2' ->
    compat GX TX V G1 (TMem TBot T2) (TMem TBot T2').
Proof.
  intros. repeat destruct H as [|H]; ev; repeat eexists; eauto.
  - left. repeat eexists; eauto. rewrite H3. eauto.
  - right. left. subst. eauto.
  - right. right. subst. simpl. eauto.
Qed.

Lemma compat_mem_fwd1: forall GX TX V G1 T1 T1',
    compat GX TX V G1 T1 T1' ->
    compat GX TX V G1 (TMem T1 TTop) (TMem T1' TTop).
Proof.
  intros. repeat destruct H as [|H]; ev; repeat eexists; eauto.
  - left. repeat eexists; eauto. rewrite H3. eauto.
  - right. left. subst. eauto.
  - right. right. subst. simpl. eauto.
Qed.

Lemma compat_sel: forall GX TX V G1 T1' (GXX:venv) (TXX:ty) x v,
    compat GX TX V G1 (TSel (varF x)) T1' ->
    closed 0 0 (length GX) TX ->
    closed 0 0 (length GXX) TXX ->
    indexr x G1 = Some v ->
    val_type_stub GXX v TXX ->
    exists TXX', T1' = (TSel (varF x)) /\ compat GX TX V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? CC CL CL1 IX HV.

  destruct CC.
  destruct H. destruct H. destruct H. destruct H0. destruct H1. destruct H2.
  simpl in H3. eexists. split. eauto. right. left. eauto.
  destruct H. destruct H. simpl in H0. eexists. split. eauto. right. left. eauto.
  destruct H. destruct H. simpl in H0. eexists. split. eauto. right. left. eauto.
Qed.

Lemma compat_selh: forall GX TX V G1 T1' GH0 GH0' (GXX:venv) (TXX:ty) x,
    compat GX TX V G1 (TSel (varH x)) T1' ->
    closed 0 0 (length GX) TX ->
    indexr x (GH0 ++ [(GX, TX)]) = Some (GXX, TXX) ->
    Forall2 (compat2 GX TX V) GH0 GH0' ->
    (x = 0 /\ GXX = GX /\ TXX = TX) \/
    exists TXX',
      x > 0 /\ T1' = TSel (varH (x-1)) /\
      indexr (x-1) GH0' = Some (GXX, TXX') /\
      compat GX TX V GXX TXX TXX'
.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? CC CL IX FA.

  case_eq (beq_nat x 0); intros E.
  - left. assert (x = 0). eapply beq_nat_true_iff. eauto. subst x.
    rewrite indexr_hit0 in IX. inversion IX. eauto.
  - right. assert (x <> 0). eapply beq_nat_false_iff. eauto.
    assert (x > 0). unfold id. unfold id in H. omega.
    eapply (indexr_compat_miss0) in FA. destruct FA.
    destruct CC.

    destruct H2. destruct H2. destruct H2. destruct H3. destruct H4. destruct H5.
    simpl in H6.
    rewrite E in H6.
    eexists. split. omega. split; eauto.

    simpl in H2. destruct H2. destruct H2.
    inversion H2; subst. omega.

    destruct H2. rewrite E in H3.
    eexists. eauto.

    assert (x-1+1=x) as A. omega. rewrite A. eauto.
Qed.

Lemma compat_all: forall GX TX V G1 T1 T2 T1' n,
    compat GX TX V G1 (TAll T1 T2) T1' ->
    closed 0 0 (length GX) TX -> closed 1 (n+1) (length G1) T2 ->
    exists TA TB, T1' = TAll TA TB /\
                  closed 1 n (length G1) TB /\
                  compat GX TX V G1 T1 TA /\
                  compat GX TX V G1 (open_rec 0 (varH (n+1)) T2) (open_rec 0 (varH n) TB).
Proof.
  intros ? ? ? ? ? ? ? ? CC CLX CL2. destruct CC.

  ev. simpl in H0. repeat eexists; eauto. eapply closed_subst; eauto using indexr_max.
  unfold compat. left. repeat eexists; eauto.
  unfold compat. left. repeat eexists; eauto. erewrite subst_open_commute; eauto.

  destruct H. destruct H. inversion H. repeat eexists. eauto. subst.
  eapply closed_upgrade_free. eauto. omega. unfold compat. eauto.
  unfold compat. eauto. right. right. subst.
  split. eapply nosubst_open. simpl. omega. eapply nosubst_intro. eauto. symmetry.
  assert (T2 = subst (varF 0) T2) as A. symmetry. eapply closed_no_subst. eauto.
  remember (open_rec 0 (varH n) T2) as XX. rewrite A in HeqXX. subst XX.
  eapply subst_open_commute. eauto. eauto.

  simpl in H. destruct H. destruct H. repeat eexists. eauto. eapply closed_nosubst. eauto. eauto.
  unfold compat. right. right. eauto.
  unfold compat. right. right. split. eapply nosubst_open. simpl. omega. eauto.
  erewrite subst_open_commute. eauto. eauto. eauto.
Qed.

Lemma compat_closed: forall GX TX V G T T' j,
  compat GX TX V G T T' ->
  closed 0 (j + 1) (length G) T ->
  closed 0 0 (length GX) TX ->
  closed 0 j (length G) T'.
Proof.
  intros. inversion H;[|destruct H2;[|destruct H2]].
  - destruct H2 as [x1 [v [Hindex [HeqV [HGX [Hv Heq]]]]]]. subst.
    apply closed_subst. eassumption.
    apply indexr_max in Hindex. apply cl_sel. omega.
  - destruct H2. subst.
    eapply closed_upgrade_free. eapply H2. omega.
  - subst.
    apply closed_nosubst. assumption. eauto.
Qed.

Lemma stp2_substitute_aux: forall n, forall G1 G2 T1 T2 GH m n1,
   stp2 false m G1 T1 G2 T2 GH n1 ->
   n1 <= n ->
   forall GH0 GH0' GX TX T1' T2' V,
     GX = GX ->
     GH = (GH0 ++ [(GX, TX)]) ->
     val_type_stub GX V TX ->
     closed 0 0 (length GX) TX ->
     compat GX TX (Some V) G1 T1 T1' ->
     compat GX TX (Some V) G2 T2 T2' ->
     Forall2 (compat2 GX TX (Some V)) GH0 GH0' ->
     stpd2 false m G1 T1' G2 T2' GH0'.
Proof. admit. (*PERF
  intros n. induction n.
  Case "z". intros. inversion H0. subst. inversion H; eauto.
  intros G1 G2 T1 T2 GH m n1 H NE. remember false as s.
  induction H; inversion Heqs.

   - Case "top".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    eapply compat_top in IX2.
    subst. eapply stpd2_top.
    eapply compat_closed. eassumption.
    rewrite app_length in H. simpl in H.
    erewrite <- Forall2_length. eapply H. eassumption.
    eassumption. assumption.

  - Case "bot".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    eapply compat_bot in IX1.
    subst. eapply stpd2_bot.
    eapply compat_closed. eassumption.
    rewrite app_length in H. simpl in H.
    erewrite <- Forall2_length. eapply H. eassumption.
    eassumption. assumption.

  - Case "mem".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.
    eapply compat_mem in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_mem in IX2. repeat destruct IX2 as [? IX2].
    subst. eapply stpd2_mem.
    eapply IHn; eauto; try omega.
    eapply IHn; eauto; try omega.
    eauto. eauto.

  - Case "sel1".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX (Some V) G1 T1' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    assert (compat GXX TXX (Some V) GX TX TX) as CPX. right. left. eauto.

    subst.
    eapply stpd2_sel1. eauto. eauto. eauto.
    eapply IHn; eauto; try omega.
    eapply compat_mem_fwd2. eauto.
    eauto. eauto. eauto. eauto.

  - Case "sel2".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply (compat_sel GXX TXX (Some V) G2 T2' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    assert (compat GXX TXX (Some V) GX TX TX) as CPX. right. left. eauto.

    subst.
    eapply stpd2_sel2. eauto. eauto. eauto.
    eapply IHn; eauto; try omega.
    eapply compat_mem_fwd1. eauto.
    eauto. eauto. eauto. eauto.

  - Case "selx".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (T1' = TSel (varF x1)). {
      destruct IX1. ev. eauto.
      destruct H6. ev. auto.
      destruct H6. ev. eauto.
    }
    assert (T2' = TSel (varF x2)). {
      destruct IX2. ev. eauto.
      destruct H7. ev. auto.
      destruct H7. ev. eauto.
    }
    subst.
    eapply stpd2_selx. eauto. eauto.

  - Case "sela1".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX (Some V) G1 (TSel (varH x)) T1') as IXX. eauto.

    eapply (compat_selh GXX TXX (Some V) G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].

    destruct IX1.
    + SCase "x = 0".
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H8; subst.
        eapply stpd2_sel1. eauto. eauto. eauto.
        eapply IHn; eauto; try omega. right. left. auto.
        eapply compat_mem_fwd2. eauto.
      * subst. inversion H7. subst. omega.
      * subst. destruct H7. eauto.
    + SCase "x > 0".
      ev. subst.
      eapply stpd2_sela1. eauto.
      assert (x-1+1=x) as A by omega.
      remember (x-1) as x1. rewrite <- A in H0.
      eapply compat_closed. eauto. eauto. eauto.
      eapply IHn; eauto; try omega.
      eapply compat_mem_fwd2. eauto.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.

(*  - Case "sela2".
    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX (Some V) G2 (TSel (varH x)) T2') as IXX. eauto.

    eapply (compat_selh GXX TXX (Some V) G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    destruct IX2.
    + SCase "x = 0".
      repeat destruct IXX as [|IXX]; ev.
      * subst. simpl. inversion H8; subst.
        eapply stpd2_sel2. eauto. eauto. eauto.
        eapply IHn; eauto; try omega. right. left. auto.
        eapply compat_mem_fwd1. eauto.
      * subst. inversion H7. subst. omega.
      * subst. destruct H7. eauto.
    + SCase "x > 0".
      ev. subst.
      eapply stpd2_sela2. eauto.
      assert (x-1+1=x) as A by omega.
      remember (x-1) as x1. rewrite <- A in H0.
      eapply compat_closed. eauto. eauto. eauto.
      eapply IHn; eauto; try omega.
      eapply compat_mem_fwd1. eauto.
    (* remaining obligations *)
    + eauto. + subst GH. eauto. + eauto.*)

  - Case "selax".

    intros GH0 GH0' GXX TXX T1' T2' V ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    assert (compat GXX TXX (Some V) G1 (TSel (varH x)) T1') as IXX1. eauto.
    assert (compat GXX TXX (Some V) G2 (TSel (varH x)) T2') as IXX2. eauto.

    destruct v as [GX TX].
    eapply (compat_selh GXX TXX (Some V) G1 T1' GH0 GH0' GX TX) in IX1. repeat destruct IX1 as [? IX1].
    eapply (compat_selh GXX TXX (Some V) G2 T2' GH0 GH0' GX TX) in IX2. repeat destruct IX2 as [? IX2].

    assert (not (nosubst (TSel (varH 0)))). unfold not. intros. simpl in H1. eauto.
    assert (not (closed 0 0 (length G1) (TSel (varH 0)))). unfold not. intros. inversion H6. omega.
    assert (not (closed 0 0 (length G2) (TSel (varH 0)))). unfold not. intros. inversion H7. omega.

    destruct x; destruct IX1; ev; try omega; destruct IX2; ev; try omega; subst.
    + SCase "x = 0".
      repeat destruct IXX1 as [IXX1|IXX1]; ev; try contradiction.
      repeat destruct IXX2 as [IXX2|IXX2]; ev; try contradiction.
      * SSCase "sel-sel".
        subst. simpl. inversion H17; subst. inversion H9; subst.
        eapply stpd2_selx. eauto. eauto.
    + SCase "x > 0".
      destruct IXX1; destruct IXX2; ev; subst; eapply stpd2_selax; eauto.
    (* leftovers *)
    + eauto. + subst. eauto. + eauto. + eauto. + subst. eauto. + eauto.

  - Case "all".
    intros GH0 GH0' GX TX T1' T2' V ? ? ? CX IX1 IX2 FA.

    assert (length GH = length GH0 + 1). subst GH. eapply app_length.
    assert (length GH0 = length GH0') as EL. eapply Forall2_length. eauto.

    eapply compat_all in IX1. repeat destruct IX1 as [? IX1].
    eapply compat_all in IX2. repeat destruct IX2 as [? IX2].

    subst.

    eapply stpd2_all.
    + eapply IHn; eauto; try omega.
    + eauto.
    + eauto.
    + eauto.
    + subst.
      eapply IHn. eauto. omega. simpl. eauto.
      change ((G2, T3) :: GH0 ++ [(GX, TX)]) with (((G2, T3) :: GH0) ++ [(GX, TX)]).
      reflexivity.
      eauto. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      rewrite app_length. simpl. rewrite EL. eauto.
      eapply Forall2_cons. simpl. eauto. eauto.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
    + eauto.
    + eauto. subst GH. rewrite <-EL. eapply closed_upgrade_free. eauto. omega.
  - Case "wrapf".
    intros. subst. eapply stpd2_wrapf. eapply IHn; eauto; try omega.
  - Case "transf".
    intros. subst.
    apply stp2_extend2 with (v1:=V) in H.
    apply stp2_extend1 with (v1:=V) in H0.
    eapply stpd2_transf.

    eapply IHn; eauto; try omega.
    unfold compat. simpl. left. exists (length G2). exists V.
    rewrite <- beq_nat_refl. split; eauto.

    eapply IHn; eauto; try omega.
    unfold compat. simpl. left. exists (length G2). exists V.
    rewrite <- beq_nat_refl. split; eauto. *)
Qed.

Lemma stp2_substitute: forall G1 G2 T1 T2 GH m,
   stpd2 false m G1 T1 G2 T2 GH ->
   forall GH0 GH0' GX TX T1' T2' V,
     GX = GX ->
     GH = (GH0 ++ [(GX, TX)]) ->
     val_type_stub GX V TX ->
     closed 0 0 (length GX) TX ->
     compat GX TX (Some V) G1 T1 T1' ->
     compat GX TX (Some V) G2 T2 T2' ->
     Forall2 (compat2 GX TX (Some V)) GH0 GH0' ->
     stpd2 false m G1 T1' G2 T2' GH0'.
Proof.
  intros. repeat eu. eapply stp2_substitute_aux; eauto.
Qed.


(* ### Value Typing / Logical Relation for Values ### *)

Lemma valtp_inv_ty: forall n, forall H1 T1 GX TX,
  val_type H1 [] (vty GX TX) T1 ->
  tsize H1 T1 < n ->                    
  closed 0 0 (length GX) TX.
Proof.
  intros n. induction n; intros. omega.
  rewrite val_type_unfold in H. destruct T1; eauto; try contradiction.
  destruct v; remember (indexr i H1) as L; try destruct L; try destruct v; try contradiction.
  ev. eapply IHn. eauto. simpl in H0. rewrite <-HeqL in H0. rewrite tsz_eq. omega. admit.
  (*FIXME*)
(*  ev. eapply stp2_closed1 in H. eauto. *)
Qed.

Lemma valtp_closed: forall vf GH H1 T1,
  val_type H1 GH vf T1 ->
  closed 0 (length GH) (length H1) T1.
Proof.
  intros. destruct T1; destruct vf;
  rewrite val_type_unfold in H; try eauto; try contradiction.
  - (* fun *) ev. econstructor. eauto. eauto.
  - (* sel *) destruct v; try remember (indexr i H1) as L; destruct L as [[?|?]|]; try contradiction.
              econstructor. eapply indexr_max. eauto.
              admit. admit. admit. (* selH *)
  - (* sel *) destruct v; try remember (indexr i H1) as L; destruct L as [[?|?]|]; try contradiction.
              econstructor. eapply indexr_max. eauto.
              admit. admit. admit. (* selH *)
  - (* mem *) ev. econstructor. admit. (*eapply stp2_closed1 in H0. eauto. eapply stp2_closed2 in H. eauto.*)

              admit.  (* temp GH = [] *)
Qed.


Lemma vtp_to_stub: forall n, forall G v T,
  val_type G [] v T ->
  tsize G T < n ->
  val_type_stub G v T.
Proof. admit. (*
  intros n. induction n; intros. omega.
  destruct v.
  - (* abs *)
    destruct T; rewrite val_type_unfold in H; try contradiction.
    + (* top *) repeat econstructor. 
    + (* all *)
      ev. econstructor. eapply stp2_refl. econstructor. eauto. eauto. 
    + (* sel *)
      destruct v; try remember (indexr i G) as L; try  destruct L; try destruct v; try inversion H; try contradiction.
      assert (closed 0 (length ([]:aenv)) (length l0) t1). admit. (* temp eapply valtp_closed. eauto.*)
      eapply IHn in H. inversion H. subst.
      eapply v_abs. eapply stpd2_to_strong. eapply stpd2_sel2. eauto. eapply v_ty. eapply stp2_refl. eauto. eauto. eapply stpd2_downgrade. eapply stpd2_mem. eapply stpd2_top. eauto. eapply stpd2_wrapf. eauto.
      (* size *)
      simpl in H0. rewrite <-HeqL in H0. rewrite tsz_eq. omega. 
  - (* vty *)
    destruct T; rewrite val_type_unfold in H; try contradiction. 
    + (* top *) econstructor; eauto. 
    + (* sel *)
      destruct v; try remember (indexr i G) as L; try  destruct L; try destruct v; try inversion H; try contradiction.
      assert (closed 0 (length ([]:aenv)) (length l0) t0). admit. (* temp eapply valtp_closed. eauto. *)
      eapply IHn in H. inversion H. subst.
      eapply v_ty. eapply stpd2_to_strong. eapply stpd2_sel2. eauto. eapply v_ty. eapply stp2_refl. eauto. eauto. eapply stpd2_downgrade. eapply stpd2_mem. eapply stpd2_top. eauto. eapply stpd2_wrapf. eauto.
      (* size *)
      simpl in H0. rewrite <-HeqL in H0. rewrite tsz_eq. omega.
    + (* mem *) ev. eapply v_ty. eapply stpd2_mem. eapply stpd2_upgrade; eauto. admit. admit. (* eapply stpd2_to_strong; eauto. *)
Grab Existential Variables.
    apply 0. apply 0. apply nil. *)
Qed.




(* this is just to accelerate Coq -- val_type in the goal is slooow *)
Inductive vtp: venv -> (list (vl->Prop)) -> vl -> ty -> Prop :=
| vv: forall G H v T, val_type G H v T -> vtp G H v T.


Lemma unvv: forall G H v T,
  vtp G H v T -> val_type G H v T.
Proof.
  intros. inversion H0. subst. apply H2.
Qed.


(* TODO: bounds will likley need GH environment, i.e. have to treat selh cases here *)
Lemma inv_bounds: forall n m b H1 H2 T0 T4 GH vx GL1 TL1 GU1 TU1 n0 GH1,
    val_type H2 GH vx T4 -> 
    stp2 m b H2 T4 H1 T0 GH1 n0 -> n0 < n ->
    bounds H1 T0 (GL1, TL1) (GU1, TU1) ->
    exists GL TL GU TU n, bounds H2 T4 (GL, TL) (GU, TU) /\
                        stp2 false false GU TU GU1 TU1 GH1 n /\ n <= n0.
    Proof.
      intros n. induction n. intros. omega.
      intros. 
      inversion H4; subst.
      - (* mem *)
        inversion H0; subst.
        + (* bot *)
          rewrite val_type_unfold in H. destruct vx; contradiction.
        + (* mem *)
          repeat eexists. constructor. 
          assert (m = false). admit. (* FIXME: downgrade/convert m to false *)
          subst m. eapply H11. omega. 
        + (* sel1 *) 
          assert (val_type GX GH vx TX) as VT. rewrite val_type_unfold in H.
          destruct vx. rewrite H1 in H. eapply H. rewrite H1 in H. eapply H.
          
          assert (exists (GL : venv) (TL : ty) (GU : venv) (TU : ty) (n : nat),
                    bounds GX TX (GL, TL) (GU, TU) /\
                    stp2 false false GU TU GU1 TU1 GH1 n /\ n <= n1).
          eapply IHn. eapply VT. eapply H7. omega. constructor.
          
          ev. 
          repeat eexists. econstructor. eapply H1. eapply H8. eapply H9. omega.
        + (* sel1 weak *)
          assert (exists GX0 TX0, v = vty GX0 TX0 /\ val_type GX0 GH vx TX0). 
          rewrite val_type_unfold in H.
          rewrite H1 in H. destruct v. destruct vx; contradiction.
          repeat eexists. destruct vx; eapply H. 
          destruct H8 as [GX0 [TX0 [? ?]]]. subst v.

          (* FIXME: size of H5: val_type_stub not accounted for in stp *)
          (* extract stp2 out of val_type_stub and put it directly into stp2 sel1/sel2 *)
          inversion H5. ev. subst. 
          (* FIXME: inconsistency with [] vs GH1 *)
          assert (stp2 false false GX0 (TMem TX0 TX0) GU1 (TMem TBot (TMem TL1 TU1)) GH1 n1) as ST.
          admit.

          assert (val_type GX0 GH (vty GX0 TX0) (TMem TX0 TX0)).
          rewrite val_type_unfold. admit. (* closed + stp2_refl *)
          
          assert (exists (GL : venv) (TL : ty) (GU : venv) (TU : ty) (n : nat),
                    bounds GX0 (TMem TX0 TX0) (GL, TL) (GU, TU) /\
                    stp2 false false GU TU GU1 (TMem TL1 TU1) GH1 n /\ n <= n1).
          eapply IHn. eapply H8. eapply ST. omega. econstructor. 

          ev. inversion H10. subst x1 x2 x3 x4 G T1 T2.
          
          assert (exists (GL : venv) (TL : ty) (GU : venv) (TU : ty) (n : nat),
                    bounds GX0 TX0 (GL, TL) (GU, TU) /\
                    stp2 false false GU TU GU1 TU1 GH1 n /\ n <= x5).
          eapply IHn. eapply H9. eapply H11. omega. econstructor. 

          ev. 
          repeat eexists. econstructor. eapply H1. eapply H14. eapply H15. omega. 
        + (* sela1 *)
          (* FIXME: no case for selH *)
          admit.
        + (* wrap *)
          admit.
        + (* trans *)
          admit. (* TRICKY? -- need capability to widen H with H0? or can we do without? *)
     - (* sel2 *)
       inversion H0. subst.
       + (* bot *)
         rewrite val_type_unfold in H. destruct vx; contradiction.
       + (* sel1 *)
         subst. admit.
       + (* sel2 *)
         subst. admit. 
       + (* sel1 weak *)
         subst. admit.
       + (* sel2 weak *)
         subst. admit. 
       + (* selx *)
         subst. admit.
       + (* selh1 *)
         subst. admit. 
       + (* wrap *)
         subst. admit. 
       + (* trans *)
         subst. admit. 
    Qed.




Lemma valtp_widen_aux: forall n, forall n1 m b vf H1 H2 GH GH1 T1 T2,
  val_type H1 GH vf T1 -> 
  stp2 m b H1 T1 H2 T2 GH1 n1 ->
  n1 < n ->
  length GH1 = length GH ->
  (forall min, min <= n1 ->
               forall x HX TX, indexr x GH1 = Some (HX,TX) ->
                   exists v jj max,
                     indexr x GH = Some jj /\
                     val_type HX GH v TX /\
                     min < max /\
                     (forall vy, jj vy ->
                                 forall m b G2 T2 ns,
                                   stp2 m b HX TX G2 (TMem TBot T2) GH1 ns -> ns < max ->
                                   vtp G2 GH vy T2
                     )) ->
  vtp H2 GH vf T2.
Proof.
  intros n. induction n. intros. omega.
  intros. 
  inversion H0.

  - Case "Top".
    subst. admit. 
  - Case "Bot".
    subst. rewrite val_type_unfold in H. destruct vf; contradiction.
  - Case "mem".
    subst. admit. 
  - Case "Sel1".
    subst. admit.
  - Case "Sel2". 
    subst. admit.
  - Case "Sel1W".
    subst. admit.
  - Case "Sel2W".
    subst. admit.     
  - Case "selx".
    subst. admit. (* rewrite val_type_unfold in H. eapply vv. rewrite val_type_unfold.
    subst. rewrite <-H8 in H9. rewrite H9. eauto. *)

  - Case "sela1".
    subst. 
    rewrite val_type_unfold in H.
    specialize (H5 _ (le_refl _) _ _ _ H6). ev.
    rewrite H5 in H.
    assert (x1 vf). destruct vf; eauto. clear H.

    eapply H11. eapply H12. eapply H8. omega. 

  - Case "sela2".
    subst. admit. 
  - Case "selax".
    subst. admit.

  - Case "Fun".
    subst.
    rewrite val_type_unfold in H.
    assert (val_type H2 GH vf (TAll T4 T5)). rewrite val_type_unfold.
    subst. destruct vf; try solve [inversion H].
    destruct H as [? [? LR]].
    assert (closed 0 (length GH) (length H2) T4). admit. (* temp eapply stpd2_closed1. eauto. *)
    assert (closed 1 (length GH) (length H2) T5). admit.
    split. eauto. split. eauto. 
    intros vx jj VST0 STJ. 

    assert (val_type H2 GH vx T4) as VX0. { eapply VST0. }
    assert (vtp H1 GH vx T0) as VX1. {
      eapply IHn. eapply VST0. eapply H6. omega. omega. eauto. eauto. eauto.
      intros min MN. eapply H5. omega. 
    }


    
    assert (forall (vy : vl),
             jj vy ->
             forall (GL : venv) (TL : ty) (GU : venv) (TU : ty),
               bounds H1 T0 (GL, TL) (GU, TU) ->
               val_type GU GH vy TU) as STJ1.
    { intros vy jjvy ? ? ? ? BB. specialize (STJ vy jjvy).
      
      (* downgrade bounds from H1 T0 to H2 T4, get size < n0 *)
      assert (exists GL2 TL2 GU2 TU2 n,
                bounds H2 T4 (GL2, TL2) (GU2, TU2) /\
                stp2 false false GU2 TU2 GU TU GH1 n /\ n <= n0). {
        eapply inv_bounds. eapply VX0. eapply H6. info_eauto. eapply BB. }
      ev.
      eapply unvv. eapply IHn. eapply STJ. eapply H13. eapply H14. omega. eapply H4.
      intros min MN. eapply H5. omega. 
    }
    eapply unvv in VX1. 
    destruct (LR vx jj VX1 STJ1) as [v [TE VT]]. 

    
    exists v. split. eapply TE. eapply unvv.

    (* now deal with function result! *)

    rewrite H4 in H10. (* length stp result *)
    
    eapply IHn. eapply VT. eapply H10. 

    omega. 
    simpl. rewrite H4. reflexivity. (* length *) 

    (* now custom env predicate *)
    (* intros min N.
    assert (min < (S n2)). omega. remember (S n2) as nn. clear N. revert min H13.
    assert (nn <= S n2). omega. clear Heqnn. 
    induction nn.
    intros min NN. inversion NN. *)

    (* XXXXXXXX use n, not n2 !!! *)
    
    simpl. rewrite H4.
    intros.
    unfold id,venv,aenv in *.    
    { case_eq (beq_nat x (length GH)); intros E.
    + rewrite E in H14. inversion H14. subst HX TX. 
      exists vx. exists jj. exists (S n2). 
      split. reflexivity.
      assert (val_type H2 (jj :: GH) vx T4) as VXE. admit. (* TODO: lemma to extend VX0 *)
      split. eapply VXE.
      split. omega.
      intros.
      assert (val_type G2 (jj :: GH) vx (TMem TBot T2)) as VXEM. 
      eapply unvv. eapply IHn. eapply VXE. eapply H16. omega. 
      simpl. rewrite H4. reflexivity.
      intros min' NN'. eapply IHnn. omega. omega. 
      
      admit. (* OUCH !!!  FIXME: circularity with wf-env *)

      rewrite val_type_unfold in VXEM. destruct vx. contradiction. ev.
      specialize (STJ vy ny H15). 
      (* compute bounds of T4, given (TMem TBot T2) *)
      (* derive TU <: T2 *)
      (* get vy:TU from STJ1 *)
      (* widen *)
      admit. 
    + admit. (* extend H6 *)
    }
    eapply VT. 
    eapply vv. eapply H8.
      
  - Case "wrapf".
    admit. (* eapply IHn. eauto. eapply H4. omega. *)
  - Case "transf".
    admit. (*
    assert (val_type G2 GH vf T3). eapply IHn; eauto. omega.
    eapply IHn; eauto. omega. *)
Qed.

Lemma valtp_widen: forall vf GH H1 H2 T1 T2,
  val_type H1 GH vf T1 ->
  stpd2 true true H1 T1 H2 T2 GH ->
  val_type H2 GH vf T2.
Proof.
  intros. destruct H0. eapply valtp_widen_aux; eauto.
Qed.




Lemma valtp_reg: forall vf GH H1 T1,
  val_type H1 GH vf T1 ->
  stpd2 true true H1 T1 H1 T1 GH.
Proof.
  intros. eapply stp2_refl. eapply valtp_closed. eapply H.
Qed.

Lemma valtp_extend: forall vx vf GH H1 T1,
  val_type H1 GH vf T1 ->
  val_type (vx::H1) GH vf T1.
Proof.
  intros. eapply valtp_widen. eauto. eapply stpd2_extend2. eapply valtp_reg. eauto. 
Qed.


Lemma wf_env_extend: forall vx G1 H1 T1,
  R_env H1 G1 ->
  val_type (vx::H1) [] vx T1 ->               
  R_env (vx::H1) (T1::G1).
Proof.
  intros. unfold R_env. unfold R_env in H. destruct H as [L U].
  split. simpl. eauto.
  intros. simpl in H. case_eq(beq_nat x (length G1)); intros E; rewrite E in H.
  - inversion H. subst. exists vx. unfold R. split.
    exists 0. intros. destruct n. omega. simpl. rewrite <-L in E. rewrite E. eauto.
    eauto.
  - destruct (U x T0 H) as [vy [EV VY]]. exists vy. split.
    destruct EV as [n EV]. assert (S n > n) as N. omega. specialize (EV (S n) N). simpl in EV.
    exists n. intros. destruct n0. omega. simpl.  rewrite <-L in E. rewrite E. eauto.
    eapply valtp_extend. eauto. 
Qed.


Lemma restp_widen: forall vf H1 H2 T1 T2,
  res_type H1 vf T1 ->
  stpd2 true true H1 T1 H2 T2 [] ->
  res_type H2 vf T2.
Proof.
  intros. inversion H. eapply not_stuck. eapply valtp_widen; eauto.
Qed.




(* ### Relating Static and Dynamic Subtyping ### *)

Lemma inv_vtp_stub_half: forall G v T GH,
  val_type_stub G v T ->
  exists G0 T0, val_type_stub G0 v T0 /\ closed 0 0 (length G0) T0 /\
             stpd2 false false G0 T0 G T GH.
Proof.
  intros. inversion H; subst.
  - eexists. eexists. split; try split.
    + simpl. econstructor. ev. eapply stp2_reg1 in H0. apply H0.
    + ev. eapply stp2_closed1 in H0. simpl in H0. apply H0.
    + eapply stpd2_downgrade. ev. eexists. simpl.
      eapply stp2_extendH_mult0. eassumption.
  - eexists. eexists. split; try split.
    + simpl. econstructor; try eassumption. 
    + ev. eapply stp2_closed2 in H0. simpl in H0. apply H0.
    + eapply stpd2_downgrade. ev.  eapply stp2_reg2 in H0.
      eu. eexists. eapply stp2_extendH_mult0. eassumption.
Qed.


  
Lemma inv_vtp_half: forall G v T GH,
  val_type G [] v T ->
  exists G0 T0, val_type_stub G0 v T0 /\ closed 0 0 (length G0) T0 /\
             stpd2 false false G0 T0 G T GH.
Proof.
  intros. eapply inv_vtp_stub_half. eapply vtp_to_stub. eauto. eauto.
Qed.



Lemma wf_envh_extend: forall GX GY GH T3,
  R_envh GX GY GH ->
  R_envh GX ((GX, T3) :: GY) (T3 :: GH).
Proof.
  intros. destruct H. 
  unfold R_envh. split. simpl. eauto.
  intros. case_eq (beq_nat x (length GY)); intros E.
  + simpl. rewrite E. simpl in H1. rewrite H in E. rewrite E in H1. inversion H1. eauto. 
  + eapply indexr_extend. eapply H0. eapply indexr_miss. eauto. rewrite H in E. eapply beq_nat_false_iff. eapply E. 
Qed.

Lemma stp_to_stp2: forall G1 GH T1 T2,
  stp G1 GH T1 T2 ->
  forall GX GY, R_env GX G1 -> R_envh GX GY GH ->
  stpd2 false false GX T1 GX T2 GY.
Proof.
  intros G1 G2 T1 T2 ST. induction ST; intros GX GY WX WY; eapply stpd2_wrapf.
  - Case "top".
    eapply stpd2_top. erewrite wfh_length; eauto. erewrite wf_length; eauto.
  - Case "bot".
    eapply stpd2_bot. erewrite wfh_length; eauto. erewrite wf_length; eauto.
  - Case "mem". eapply stpd2_mem; eauto.
  - Case "sel1".
    assert (exists v : vl, indexr x GX = Some v /\ val_type GX [] v TX) as A.
    eapply indexr_safe_ex. eauto. eauto.
    destruct A as [? [? VT]].
    eapply inv_vtp_half in VT. ev.
    eapply stpd2_sel1. eauto. eauto. eauto. eapply stpd2_trans. eauto. eauto.
  - Case "sel2".
    assert (exists v : vl, indexr x GX = Some v /\ val_type GX [] v TX) as A.
    eapply indexr_safe_ex. eauto. eauto.
    destruct A as [? [? VT]].
    eapply inv_vtp_half in VT. ev.
    eapply stpd2_sel2. eauto. eauto. eauto. eapply stpd2_trans. eauto. eauto.
  - Case "selx". eauto.
    assert (exists v0 : vl, indexr x GX = Some v0 /\ val_type GX [] v0 v) as A.
    eapply indexr_safe_ex. eauto. eauto. eauto.
    destruct A as [? [? ?]].
    eapply stpd2_selx; eauto.
  - Case "sela1".
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    inversion VT. subst.
    eapply stpd2_sela1. eauto. erewrite wf_length; eauto. eauto.
  - Case "sela2".
    assert (exists v, indexr x GY = Some v /\ valh_type GX GY v TX) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    inversion VT. subst.
    eapply stpd2_sela2. eauto. erewrite wf_length; eauto. eauto.
  - Case "selax".
    assert (exists v0, indexr x GY = Some v0 /\ valh_type GX GY v0 v) as A.
    eapply index_safeh_ex. eauto. eauto. eauto.
    destruct A as [? [? VT]]. destruct x0.
    destruct VT. subst.
    eapply stpd2_selax. eauto.
  - Case "all".
    subst x.
    assert (length GY = length GH) as A. eapply wfh_length; eauto.
    assert (length GX = length G1) as B. eapply wf_length; eauto.
    eapply stpd2_all. eauto. eauto.
    rewrite A. rewrite B. eauto.
    rewrite A. rewrite B. eauto.
    rewrite A.
    eapply IHST2. eauto. eapply wf_envh_extend. eauto. 
Qed.





(* ### Inversion Lemmas ### *)

Lemma invert_abs: forall venv vf T1 T2,
  val_type venv [] vf (TAll T1 T2) ->
  exists env TX y,
    vf = (vabs env TX y) /\ 
    (closed 0 0 (length venv) T2 -> forall vx : vl,
       val_type venv [] vx T1 ->
       exists v : vl, tevaln (vx::env) y v /\ val_type venv [] v T2).
Proof.
  intros. 
  rewrite val_type_unfold in H.   
  destruct vf; try solve [inversion H].
  ev. exists l. exists t. exists t0. split. eauto.
  intros C. simpl in H1.
  (* TODO: substitute *)
  admit.
  (* assert unfold open in H1. rewrite <-closed_no_open in H1. eauto. *)
Qed.


(* final type safety + termination proof *)

Theorem full_total_safety : forall e tenv T,
  has_type tenv e T -> forall venv, R_env venv tenv ->
  exists v, tevaln venv e v /\ val_type venv [] v T.
Proof.
  intros ? ? ? W.
  induction W; intros ? WFE.

  - Case "Var". 
    destruct (indexr_safe_ex venv0 env T1 x) as [v IV]. eauto. eauto. 
    inversion IV as [I V]. 

    exists v. split. exists 0. intros. destruct n. omega. simpl. rewrite I. eauto. eapply V.

  - Case "Typ".
    repeat eexists. intros. destruct n. inversion H0. simpl. eauto.
    assert (stpd2 false false venv0 T1 venv0 T1 []). eapply stpd2_wrapf. eapply stp2_refl. rewrite <-(wf_length venv0) in H. eauto. eauto.
    rewrite val_type_unfold. eu. eauto. 
    
  - Case "App".
    rewrite <-(wf_length venv0 _ WFE) in H. 
    destruct (IHW1 venv0 WFE) as [vf [IW1 HVF]].
    destruct (IHW2 venv0 WFE) as [vx [IW2 HVX]].
    
    eapply invert_abs in HVF.
    destruct HVF as [venv1 [TX [y [HF IHF]]]].

    destruct (IHF H vx HVX) as [vy [IW3 HVY]].

    exists vy. split. {
      (* pick large enough n. nf+nx+ny will do. *)
      destruct IW1 as [nf IWF].
      destruct IW2 as [nx IWX].
      destruct IW3 as [ny IWY].
      exists (S (nf+nx+ny)). intros. destruct n. omega. simpl.
      rewrite IWF. subst vf. rewrite IWX. rewrite IWY. eauto.
      omega. omega. omega.
    }
    eapply HVY.

  - Case "DApp". admit. 
    
  - Case "Abs".
    erewrite <-(wf_length venv0 env WFE) in H. inversion H; subst. 
    eexists. split. exists 0. intros. destruct n. omega. simpl. eauto.
    rewrite val_type_unfold. repeat split; eauto.
    intros. 
    assert (stpd2 true true venv0 T1 (vx::venv0) T1 []). eapply stpd2_extend2. eapply stp2_refl; eauto. eu.
    assert (stpd2 true true (vx::venv0) T2 venv0 T2 []). eapply stpd2_extend1. eapply stp2_refl; eauto. eu.
    assert (val_type (vx::venv0) vx T1). eapply valtp_extend. eauto. 
    assert (R_env (vx::venv0) (T1::env)). eapply wf_env_extend. eauto. eauto. 
    specialize (IHW (vx::venv0) H7). ev.
    assert ((open (varF (length env)) T2) = T2) as R. unfold open. symmetry. eapply closed_no_open. eauto. 
    assert (val_type venv0 x1 T2). eapply valtp_widen. eauto. rewrite R. eauto.
    (* we have all pieces ... *)
    eexists. split; eauto.
  - Case "Sub".
    specialize (IHW venv0 WFE). ev. eexists. split. eauto.
    eapply valtp_widen. eauto. eapply stpd2_upgrade. eapply stp_to_stp2; eauto. unfold R_envh. split. eauto. intros. inversion H2. 
Grab Existential Variables.
    apply 0. 
Qed.



