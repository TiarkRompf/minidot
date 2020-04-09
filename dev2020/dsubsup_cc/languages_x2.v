(* Source language (currently missing: T ::=  T1 /\ T2 | { z => T^z }):

  DSubSup (D<:>)
  T ::= Top | Bot | t.Type | { Type: S..U } | (z: T) -> T^z
  t ::= x | { Type = T } | lambda x:T.t | t t *)
Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

(* ### Syntax ### *)

Definition id := nat.

(* We do NOT distinguish between constructor and term variables but 
   use kinds to identify *)
Inductive var : Type :=
| varF : id -> var (* free, in concrete environment *)
| varB : id -> var (* locally-bound variable *)
.

(* An environment is a list of values, indexed by decrementing ids. *)

Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.

(* Target language (inspired by https://docs.racket-lang.org/pie/index.html):

 t ::= x | Unit | Type
     | (z: T) -> T^z  | lambda x:T.t | t t
     | Sigma z:T. T^z | (t, t)  | fst t | snd t *)

(* Declare Scope cc_scope. *)

Require Import FunInd.
Require Import Recdef.

(* Adapt the convention of dev2017/dsub-total3.v *)
(* Module CC2. *)

(*   Inductive kd : Type := *)
(*   (* ⋆ *) *)
(*   | KStar : kd *)
(*   (* rule (⋆, box, box) *) *)
(*   | KAll1 : ty -> kd -> kd *)
(*   (* rule (box, box, box) *) *)
(*   | KAll2 : kd -> kd -> kd *)
                        
(*   with ty : Type := *)
(*        | TTop : ty *)
(*        | TBot : ty *)
(*        (* (x: A) -> B *) *)
(*        (* rule (⋆, ⋆, ⋆) *) *)
(*        | TAll1 : ty -> ty -> ty *)
(*        (* rule (box, ⋆, ⋆) *) *)
(*        | TAll2 : kd -> ty -> ty *)
(*        (* x.Type *) *)
(*        | TSel : var -> ty. *)


(*   Inductive tm : Type := *)
(*   (* x -- free variable, matching concrete environment *) *)
(*   | tvar : var -> tm *)
(*   (* lambda x:T.t *) *)
(*   | tabs : ty -> tm -> tm *)
(*   (* t t *) *)
(*   | tapp : tm -> tm -> tm *)
(*   . *)

(*   Inductive vl : Type := *)
(*   (* a closure for a lambda abstraction *) *)
(*   | vabs : list vl (*H*) -> ty -> tm -> vl *)
(*   (* a closure for a first-class type *) *)
(*   | vty : list vl (*H*) -> ty -> vl *)
(*   . *)

(*   Definition tenv := list ty. (* Gamma environment: static *) *)
(*   Definition venv := list vl. (* H environment: run-time *) *)

  

(* End CC2. *)
(*
  CC
  t :≔ s | x | lambda x:T.t | t t 

  Sort = {⋆, ◻}; Axioms = {(⋆, ◻)}; 
  Rules = {(⋆, ⋆, ⋆), (◻, ⋆, ⋆), (◻, ◻, ◻), (⋆, ◻, ◻)}
*)

(* Calculus of Construction as a PTS *)
Module CC.

Inductive sort : Type :=
| Star : sort (* Universe of CC types *)
| Box :  sort (* Universe of CC kinds  *)
.

Definition sort_max (s s' : sort): sort :=
  match s, s' with
  | Box, _ | _, Box => Box
  | _, _ => Star
  end.

(* Collapse terms, types, and kinds into one grammar *)
Inductive tm : Type := (* TODO what about equality types? *)
(* Sort Constants *)
| CSort : sort -> tm

(* PI types (kinds) *)
| TAll : tm -> tm -> tm
(* TODO: Add weak sigma type back afterwards *)
(* | TSig : tm -> tm -> tm *)

(* Basic types *)
(* | TTop : tm *)
(* | TBot : tm *)

(* variables *)
(* Unlike DOT where TSel is used to identify term var and type var *)
| tvar : var -> tm
(* λ-terms*)
| tabs : tm -> tm -> tm
(* application *)
| tapp : tm -> tm -> tm
(* | tsig : tm -> tm -> tm *)
(* | tfst : tm -> tm *)
(* | tsnd : tm -> tm *)
.

Inductive vl : Type :=
(* a closure for simple types *)
| vty : list vl (*H*) -> tm -> vl
(* a closure for function types *)
| vabs : list vl (*H*) -> tm -> tm -> vl
(* Weak sigma type*)
(* | vsig : vl -> vl -> vl *)
.

(* Γ *)
Definition tenv := list tm.
(* ρ in the notation of Chris Casinghino's survey paper 2010 *)
Definition venv := list vl.

Module Notations.

  (* \square *)
  Notation "◻" := (CSort Box) : cc_scope.
  (* \star *)
  Notation "⋆" := (CSort Star) : cc_scope.

End Notations.

Import Notations.
Open Scope cc_scope.


Fixpoint open_rec (k: nat) (u: tm) (T: tm) { struct T }: tm :=
  match T with
  | ⋆           => ⋆
  | ◻           => ◻
  (* | TTop        => TTop *)
  (* | TBot        => TBot *)
  | TAll T1 T2  => TAll (open_rec k u T1) (open_rec (S k) u T2)
  (* | TSig T1 T2  => TSig (open_rec k u T1) (open_rec (S k) u T2) *)
  | tvar (varF x) => tvar (varF x)
  | tvar (varB x) =>
    if beq_nat k x then u else (tvar (varB x))
  | tabs ty tm => tabs (open_rec k u ty) (open_rec (S k) u tm)
  | tapp tm1 tm2 => tapp (open_rec k u tm1) (open_rec k u tm2)
  (* | tsig tm1 tm2 => tsig (open_rec k u tm1) (open_rec (S k) u tm2) *)
  (* | tfst tm => tfst (open_rec k u tm) *)
  (* | tsnd tm => tsnd (open_rec k u tm) *)
  end.

Definition open_var x T := open_rec 0 (tvar x) T.
Definition open t T := open_rec 0 t T.

Fixpoint subst (x: nat) (u: tm) (t: tm) : tm :=
  match t with
  | CSort _ => t
  (* | TTop => TTop *)
  (* | TBot => TBot *)
  | TAll t1 t2 => TAll (subst x u t1) (subst x u t2)
  (* | TSig t1 t2 => TSig (subst x u t1) (subst x u t2) *)
  | tvar (varF y) =>
    if beq_nat x y then u else (tvar (varF y))
  | tvar (varB y) => tvar (varB y)
  | tabs t1 t2 => tabs (subst x u t1) (subst x u t2)
  | tapp t1 t2 => tapp (subst x u t1) (subst x u t2)
  (* | tsig t1 t2 => tsig (subst x u t1) (subst x u t2) *)
  (* | tfst t => tfst (subst x u t) *)
  (* | tsnd t => tsnd (subst x u t) *)
  end.

(* TODO: state and prove that (T^e) = (T^x){e/x} *)

Inductive closed: nat(*B*) -> nat(*F*) -> tm -> Prop :=
| cl_sort: forall i j U,
    closed i j (CSort U)
(* | cl_top: forall i j, *)
(*     closed i j TTop *)
(* | cl_bot: forall i j, *)
(*     closed i j TBot *)
| cl_all: forall i j T1 T2,
    closed i j T1 ->
    closed (S i) j T2 ->
    closed i j (TAll T1 T2)
(* | cl_sig: forall i j T1 T2, *)
(*     closed i j T1 -> *)
(*     closed (S i) j T2 -> *)
(*     closed i j (TSig T1 T2) *)
| cl_tvarb: forall i j x,
    i > x ->
    closed i j (tvar (varB x))
| cl_tvarf: forall i j x,
    j > x ->
    closed i j (tvar (varF x))
| cl_tabs:  forall i j ty tm,
    closed i j ty ->
    closed (S i) j tm ->
    closed i j (tabs ty tm)
| cl_tapp:  forall i j tm1 tm2,
    closed i j tm1 ->
    closed i j tm2 ->
    closed i j (tapp tm1 tm2)
(* | cl_tsig:  forall i j tm1 tm2, *)
(*     closed i j tm1 -> *)
(*     closed i j tm2 -> *)
(*     closed i j (tsig tm1 tm2) *)
(* | cl_tfst:  forall i j tm, *)
(*     closed i j tm -> *)
(*     closed i j (tfst tm) *)
(* | cl_tsnd:  forall i j tm, *)
(*     closed i j tm -> *)
(*     closed i j (tsnd tm) *)
.

Inductive ctx_wf: tenv -> Type :=
(* CNil *)
| wf_empty:
    ctx_wf []
(* CCons *)           
| wf_sort: forall Gamma A s,
    has_type Gamma A (CSort s) ->
    ctx_wf Gamma ->
    ctx_wf (A :: Gamma)
with has_type : tenv -> tm -> tm -> Type :=
(* Sorts *)
(* TBox; ◻ : ◻ *)
| t_box: forall Gamma,
    has_type Gamma ◻ ◻
(* TStar; ⋆ : ◻ *)
| t_star: forall Gamma,
    has_type Gamma ⋆ ◻

(* Variables *)             
(* 
  TVar; x : T : s
  x is a term variable when s is ⋆
  x is a type variable when s is ◻
 *)
(* term variables *)
| t_var_tm: forall Gamma x A,
    ctx_wf Gamma ->
    indexr x Gamma = Some A ->
    has_type Gamma A ⋆ ->
    has_type Gamma (tvar (varF x)) A
(* constructor variables *)
| t_var_cons: forall Gamma x A,
    ctx_wf Gamma ->
    indexr x Gamma = Some A ->
    has_type Gamma A ◻ ->
    has_type Gamma (tvar (varF x)) A

(* TLambda; λx:A.b : (x:A) -> B *)
(* Term language *)
(* λ-terms: where A and B are proper types *)
| t_abs_star_star: forall Gamma b A B,
    has_type Gamma A ⋆ ->
    has_type Gamma (TAll A B) ⋆ ->
    has_type (A :: Gamma) b (open_var (varF (length Gamma)) B) ->
    has_type Gamma (tabs A b) (TAll A B)
(* polymorphism: where A is kinds and B is proper types*)
| t_abs_box_star: forall Gamma b A B,
    has_type Gamma A ◻ ->
    has_type Gamma (TAll A B) ⋆ ->
    has_type (A :: Gamma) b (open_var (varF (length Gamma)) B) ->
    has_type Gamma (tabs A b) (TAll A B)
(* Type language *)
(* dependent type functions: where A is proper types and B is kinds *)
| t_abs_star_box: forall Gamma b A B,
    has_type Gamma A ⋆ ->
    has_type Gamma (TAll A B) ◻ ->
    has_type (A :: Gamma) b (open_var (varF (length Gamma)) B) ->
    has_type Gamma (tabs A b) (TAll A B)
(* type constructors: where A and B are both kinds *)
| t_abs_box_box: forall Gamma b A B,
    has_type Gamma A ◻ ->
    has_type Gamma (TAll A B) ◻ ->
    has_type (A :: Gamma) b (open_var (varF (length Gamma)) B) ->
    has_type Gamma (tabs A b) (TAll A B)

(* Applications *)
(* TApp; a b : [b/x]B *)
| t_app: forall Gamma f a A B,
    has_type Gamma f (TAll A B) ->
    has_type Gamma a A ->
    has_type Gamma (tapp f a) (open a B)

(* Pi types; (x:A) -> B; the definition follows Rules *)
(* Term language *)
(* Function types *)
(* (x: A) -> B where A and B are proper types *)
| t_allt_star_star: forall Gamma A B,    
    has_type Gamma A ⋆ ->    
    has_type (A :: Gamma) (open_var (varF (length Gamma)) B) ⋆ ->
    has_type Gamma (TAll A B) ⋆
(* Polymorphism types *)
| t_allt_box_star: forall Gamma A B,    
    has_type Gamma A ◻ ->    
    has_type (A :: Gamma) (open_var (varF (length Gamma)) B) ⋆ ->
    has_type Gamma (TAll A B) ⋆
(* Type language *)
(* Dependent function types *)
| t_allt_star_box: forall Gamma A B,    
    has_type Gamma A ⋆ ->    
    has_type (A :: Gamma) (open_var (varF (length Gamma)) B) ◻ ->
    has_type Gamma (TAll A B) ◻
(* Kinds; the type of type constructors *)
| t_allt_box_box: forall Gamma A B,
    has_type Gamma A ◻ ->    
    has_type (A :: Gamma) (open_var (varF (length Gamma)) B) ◻ ->
    has_type Gamma (TAll A B) ◻


(* Enable consistent strong Sigma-types, (cf. Definition 5.1 in [Geuvers '94]),
   forbidding (◻, ⋆, ⋆), (⋆, ◻, ⋆), (◻, ◻, ⋆), (⋆, ⋆, ◻) in the formation rule.*)
(* | t_sigt: forall Gamma T1 T2 s1 s2 s3, *)
(*     s3 = sort_max s1 s2 -> *)
(*     has_type Gamma T1 (CSort s1) -> *)
(*     has_type (T1 :: Gamma) (open (varF (length Gamma)) T2) (CSort s2) -> *)
(*     has_type Gamma (TSig T1 T2) (CSort s3) *)

(* | t_topt: forall Gamma, *)
(*     has_type Gamma TTop ⋆ *)

(* | t_bott: forall Gamma, *)
(*     has_type Gamma TBot ⋆ *)

(* | t_sig: forall Gamma e1 e2 T1 T2, *)
(*     has_type Gamma e1 T1 -> *)
(*     has_type Gamma e2 (open' e1 T2) -> *)
(*     has_type Gamma (tsig e1 e2) (TSig T1 T2) *)

(* | t_fst: forall Gamma e T1 T2, *)
(*     has_type Gamma e (TSig T1 T2) -> *)
(*     has_type Gamma (tfst e) T1 *)

(* | t_snd: forall Gamma e T1 T2 T, *)
(*     has_type Gamma e (TSig T1 T2) -> *)
(*     T = (open' (tfst e) T2) -> *)
(*     has_type Gamma (tsnd e) T *)

(* TODO equality/tconv? We omit it for now. *)
.

(* The definition of [.]_ρ *)
Fixpoint teval(n: nat)(env: venv)(t: tm){struct n}: option (option vl) :=
  match n with
  | 0 => None
  | S n =>
    match t with
    | tvar (varF x) => Some (indexr x env)
    | tvar (varB x) => Some None
    | tabs T y     =>  Some (Some (vabs env T y))
    | tapp ef ex   =>
      match teval n env ex with
      | None => None
      | Some None => Some None
      | Some (Some vx) =>
        match teval n env ef with
        | Some None => Some None
        | Some (Some (vabs env2 _ ey)) => teval n (vx::env2) ey
        | _ => None
        end
      end
    (* | tsig t1 t2 => *)
    (*   match teval n env t1 with *)
    (*   | None => None *)
    (*   | Some None => Some None *)
    (*   | Some (Some v1) => *)
    (*     match teval n env t2 with *)
    (*     | None => None *)
    (*     | Some None => Some None *)
    (*     | Some (Some v2) => Some (Some (vsig v1 v2)) *)
    (*     end *)
    (*   end *)
    | _ => None
    end
  end.

Definition tevaln env e v := exists nm, forall n, n > nm -> teval n env e = Some (Some v).

Fixpoint tsize_flat(T: tm) :=
  match T with
  (* | TTop => 1 *)
  (* | TBot => 1 *)
  | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
  (* | TSig T1 T2 => S (tsize_flat T1 + tsize_flat T2) *)
  | _ => 0
  end.
Lemma open_preserves_size: forall T x j,
    tsize_flat T = tsize_flat (open_rec j (tvar (varF x)) T).
Proof.
  intros T. induction T; intros; simpl; eauto. simpl.
  - destruct s; auto.
  - destruct v; eauto.  simpl; destruct (beq_nat j i); eauto.
Qed.

(* *********************** *)
(* Semantic Interpretation *)
(* *********************** *)

(* The definition of value sets *)
Definition vset := vl -> Prop.

(* TODO: The definition of SN set *)
Fixpoint SN e := forall env, exists v, tevaln env e v.

(* Set inclusion "subset" a ⊂ b *)
Definition vtsub (a: vset) (b: vset) :=
  forall v, a v -> b v.

(* set-interpretations for kinds V(K) *)
(* Perhaps we need to remove "has_type", or embed this kind relation into
   type interpretation *)
(* Fixpoint interp_kinds Gamma A (proof: has_type Gamma A _): Type := *)
(*   match proof with *)
(*   (* Interpretaiton of kinds *) *)
(*   (* V(◻) = SAT *) *)
(*   | t_box _ => (* ◻ *) *)
(*     vset *)
(*   (* V(⋆) = SAT *) *)
(*   | t_star _ => (* ⋆ *) *)
(*     vset *)
(*   (* V((x:A)->B) where A and B are both kinds *) *)
(*   | t_allt Gamma T1 T2 Box Box p1 p2 =>  (* Πα:T1.T2, T1:◻ *) *)
(*     let V1 := (interp_kinds Gamma T1 p1) in *)
(*     let V2 := (interp_kinds (T1 :: Gamma) (open (varF (length Gamma)) T2) p2) in *)
(*     V1 -> V2 *)
(*   (* V((x:A)->B) where A is a Γ-type and B is a kind *) *)
(*   | t_allt Gamma T1 T2 Star Box p1 p2 => (* Πα:T1.T2, T1:⋆ *) *)
(*     (interp_kinds (T1 :: Gamma) (open (varF (length Gamma)) T2) p2) *)
(*   | _ => False *)
(*   end. *)

(* Lemma wf_renv : forall Gamma x K, *)
(*     has_type Gamma x K -> *)
(*     has_type Gamma K ◻ -> *)
(*     [[x]]ᵨ ∈ V(K).  *)

  

(* Design idea:
   terms and types are separate GADTs indexed by their sort, classifying their universe.
   Might yield more concise and readable definitions (such as kind_set).
Inductive ty: sort -> Type :=
| TAll : forall s s',
    ty s -> ty s' -> ty s'
| TSig : forall s s',
    ty s -> ty s' -> ty s'
| TTm: forall s,
    tm s -> ty s
with tm: sort -> Type :=
| tvar : forall s,
    var -> tm s (* TODO: might make sense to index variables with their sort *)
| tabs : forall s s',
    ty s -> tm s' -> tm s'
| tapp : forall s s',
    tm s -> tm s' -> tm s (* TODO: correct? *)
| tsig : forall s s',
    ty s -> tm s' -> tm s'
| tfst : forall s, tm s -> tm s
| tsnd : forall s, tm s -> tm s
| tty: forall s, ty s -> tm s
.

Potentially interesting, since we could define
a sort-indexed evaluator, that describes evaluation/normalization
at runtime and at type level.
*)


(* σ in the notation of Chris Casinghino's survey paper 2010 *)  
Definition cenv := list vset.

Require Coq.Program.Wf.
(* Also, need to take kinds into consideration. With kind_set?  *)
(* TODO adapt the definitions in Geuvers '94, starting at p. 20 to sets of values *)
(* [t]_ρ = v ∈ [[ A ]]_σ *)
Program Fixpoint val_type (σ: cenv) (A:tm) (v:vl) {measure (tsize_flat A)}: Prop :=
  match v, A with
  (* Let's start from simple cases *)
  | vty env1 T, ⋆ => True
                      
  (* TODO: Shall we allow subtyping? *)
  | vabs env1 T0 y, TAll T1 T2 =>
    closed 0 (length σ) T1 /\ closed 0 (length σ) T2 /\
    forall vx, val_type σ T1 vx ->
          exists v S_T1, tevaln (vx :: env1) y v /\
                    (* T1 : ◻ *)
                    ((val_type (S_T1 :: σ) (open_var (varF (length σ)) T2) v) \/
                     (* T1 : * *)                     
                     (val_type σ T2 v))
  (* *)
  | _, _ => False
  end.


Next Obligation. Admit Obligations.

Import Coq.Program.Wf.
Import WfExtensionality.
   
Lemma val_type_unfold: forall σ A v, val_type σ A v =
  match v, A with
  (* Let's start from simple cases *)
  | vty env1 T, ⋆ => True
                      
  (* TODO: Shall we allow subtyping? *)
  | vabs env1 T0 y, TAll T1 T2 =>
    closed 0 (length σ) T1 /\ closed 0 (length σ) T2 /\
    forall vx, val_type σ T1 vx ->
          exists v S_T1, tevaln (vx :: env1) y v /\
                    (* T1 : ◻ *)
                    ((val_type (S_T1 :: σ) (open_var (varF (length σ)) T2) v) \/
                     (* T1 : * *)                     
                     (val_type σ T2 v))
  (* *)
  | _, _ => False
  end.
Proof.
Admitted.


(* this is just to accelerate Coq -- val_type in the goal is slooow *)
Inductive vtp: list vset -> tm -> vl -> Prop :=
| vv: forall σ A v, val_type σ A v -> vtp σ A v.


(* σ |= ρ : Γ *)
Definition R_env (Gamma: tenv) (ρ: venv) (σ: cenv) :=
  length Gamma = length ρ /\
  length ρ = length σ /\
  (* (x:A) ∈ Γ *)
  forall x A, indexr x Gamma = Some A ->
          (* ρ(x) ∈ [[ A ]]_σ *)
          (exists (vsx:vset) vx,
              indexr x ρ = Some vx /\
              indexr x σ = Some vsx /\
              vtp σ A vx).

Definition strong_normalization := forall e Gamma T,
      has_type Gamma e T ->
      forall ρ σ, R_env Gamma ρ σ ->
              exists v, tevaln ρ e v /\ val_type σ T v.

(* TODO: prove strong normalization *)
Theorem full_total_safty : strong_normalization.
Proof. 
  unfold strong_normalization.
  intros ? ? ? W.
  induction W; intros ? ? WFE.

  (* TODO: note that we haven't defined interpretation for sorts *)
  (* TODO: Will need to feed "has_type" proof into val_type *)
  (* Check F_ω proof in detail *)
  - (* Case "◻" *) admit.
  - (* Case "⋆" *) admit.
  - (* Case "Term variables" *) admit. 
  - (* Case "Constructor variables" *) admit.
  - (* Case "λ abstractions" *) admit.
  - (* Case "polymorphism" *) admit.
  - (* Case "dependent functions" *) admit.
  - (* Case "type constructors" *) admit.
  - (* Case "applications" *) admit.
  - (* Case "function types" *) admit.
  - (* Case "polymorphism types" *) admit.
  - (* Case "Pi types (dependent function types)" *) admit.
  - (* Case "Kinds" *) admit.

Grab Existential Variables.

Admitted.

End CC.
