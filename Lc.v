
Require Export SfLib.
Require Import Coq.Lists.ListSet.
Require Import List. Open Scope list_scope.

(* We're using functions as type environments, so this is needed
 * to prove equality of environments *)
Require Import FunctionalExtensionality.

Inductive tm :=
| tnat : nat -> tm
| tvar : id -> tm
| tabs : id -> tm -> tm
| tapp : tm -> tm -> tm
| tfix : id -> id -> tm -> tm
| tbox : tm -> tm
| tunbox : tm -> tm
| trun : tm -> tm.

(* TODO: maybe add lift *)


Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tnat" | Case_aux c "tvar"
  | Case_aux c "tabs" | Case_aux c "tapp"
  | Case_aux c "tfix" | Case_aux c "tbox"
  | Case_aux c "tunbox" | Case_aux c "trun" ].


Inductive value : nat -> tm -> Prop :=
(* nats are values in all stages *)
| vnat : forall n l, value l (tnat n)

(* stage 0 values *)
| vabs_0 : forall v t, value 0 (tabs v t)
| vfix_0 : forall i1 i2 t, value 0 (tfix i1 i2 t)
| vbox_0 : forall v, value 1 v -> value 0 (tbox v)

(* stage n > 0 values *)
| vvar_n : forall n i,
    n > 0 -> value n (tvar i)
| vabs_n : forall n v i,
    n > 0 -> value n v -> value n (tabs i v)
| vapp_n : forall n t1 t2,
    n > 0 -> value n t1 -> value n t2 -> value n (tapp t1 t2)
| vfix_n : forall f x v n,
    n > 0 -> value n v -> value n (tfix f x v)
| vbox_n : forall n v,
    n > 0 -> value n v -> value (n+1) (tbox v)
| vunbox_n : forall n v,
    n > 1 -> value (n-1) v -> value n (tunbox v)
| vrun_n : forall n v,
    n > 0 -> value n v -> value n (trun v).

Hint Constructors value.


Tactic Notation "value_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "vnat" | Case_aux c "vabs_0"
  | Case_aux c "vfix_0" | Case_aux c "vbox_0"
  | Case_aux c "vvar_n" | Case_aux c "vabs_n"
  | Case_aux c "vapp_n" | Case_aux c "vfix_n"
  | Case_aux c "vbox_n" | Case_aux c "vunbox_n"
  | Case_aux c "vrun_n" ].


Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : id) (s : tm) (t : tm) : tm :=
  match t with
  | tnat _ => t
  | tvar v => if eq_id_dec v x then s else t
  | tabs v t' => if eq_id_dec v x
                 then t
                 else tabs v ([x:=s] t')
  | tapp t1 t2 => tapp ([x:=s] t1) ([x:=s] t2)
  | tfix f v t' =>
      if eq_id_dec f x
      then t
      else if eq_id_dec v x
           then t
           else tfix f v ([x:=s] t')
  | tbox t' => tbox ([x:=s] t')
  | tunbox t' => tunbox ([x:=s] t')
  | trun t' => trun ([x:=s] t')
  end

where "'[' x ':=' s ']' t" := (subst x s t).


Fixpoint fvs (n : nat) (t : tm) : set id :=
  match n with
  | 0 =>
      match t with
      | tnat _ => nil
      | tvar i => i :: nil
      | tabs i t' => set_remove eq_id_dec i (fvs n t')
      | tapp t1 t2 => set_union eq_id_dec (fvs n t1) (fvs n t2)
      | tfix i1 i2 t' => set_remove eq_id_dec i1 (set_remove eq_id_dec i2 (fvs n t'))
      | tbox t' => fvs (n + 1) t'
      | tunbox t' => fvs n t' (* I think this case should not happen *)
      | trun t' => fvs n t'
      end
  | n =>
      match t with
      | tunbox t' => fvs (n-1) t'
      | _ => nil
      end
  end.


Fixpoint closed (n : nat) (t : tm) : bool :=
  beq_nat (length (fvs n t)) 0.


Inductive step : tm -> nat -> tm -> Prop :=
| s_app1 : forall e1 e1' e2 n,
    step e1 n e1' ->
    step (tapp e1 e2) n (tapp e1' e2)
| s_app2 : forall v e e' n,
    value n v  ->
    step e n e' ->
    step (tapp v e) n (tapp v e')
| s_appabs : forall x e v,
    value 0 v ->
    step (tapp (tabs x e) v) 0 ([x:=v] e)
| s_appfix : forall f x e v,
    value 0 v ->
    step (tapp (tfix f x e) v) 0 ([x:=v] ([f:=tfix f x e] e))
| s_box : forall e n e',
    step e (n + 1) e' ->
    step (tbox e) n (tbox e')
| s_run1 : forall e n e',
    step e n e' ->
    step (trun e) n (trun e')
| s_run : forall v,
    value 1 v ->
    closed 0 v = true ->
    step (trun (tbox v)) 0 v
| s_unb1 : forall e n e',
    step e n e' ->
    step (tunbox e) (n + 1) (tunbox e')
| s_unb : forall v,
    value 1 v ->
    step (tunbox (tbox v)) 1 v
| s_abs : forall x e n e',
    step e (n + 1) e' ->
    step (tabs x e) (n + 1) (tabs x e')
| s_fix : forall f x e n e',
    step e (n + 1) e' ->
    step (tfix f x e) (n + 1) (tfix f x e').

Hint Constructors step.


Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "s_app1" | Case_aux c "s_app2"
  | Case_aux c "s_appabs" | Case_aux c "s_appfix"
  | Case_aux c "s_box" | Case_aux c "s_run1"
  | Case_aux c "s_run" | Case_aux c "s_unb1"
  | Case_aux c "s_unb" | Case_aux c "s_abs"
  | Case_aux c "s_fix" ].


Definition example1 := tapp (tabs (Id 0) (tvar (Id 0))) (tnat 42).

Example example1_evaluation :
  step example1 0 (tnat 42).
Proof.
  unfold example1. constructor. constructor.
Qed.


Definition example2 := tunbox (tbox (tnat 42)).

Example example2_evaluation :
  step example2 1 (tnat 42).
Proof.
  unfold example2. auto.
Qed.


Definition example3 := trun (tbox (tnat 42)).

Example example3_evaluation :
  step example3 0 (tnat 42).
Proof.
  unfold example3.
  remember (tunbox (tbox (tnat 42))) as rhs.
  assert (step rhs 1 (tnat 42)).
  Case "proof of assertion". rewrite Heqrhs. apply example2_evaluation.
  constructor; auto.
Qed.

(* types ***********************************************************)

Inductive ty :=
| tynat : ty
| tyfun : ty -> ty -> ty
| tybox : (id -> option ty) -> ty -> ty.

Definition tyenv := id -> option ty.

Definition empty_tyenv : tyenv := fun _ => None.

Definition extend_tyenv : id -> ty -> tyenv -> tyenv :=
  fun i t e => fun i' => if eq_id_dec i i'
                         then Some t
                         else e i.

Definition singleton_env : id -> ty -> tyenv :=
  fun i t => extend_tyenv i t empty_tyenv.


Inductive has_ty : list tyenv -> tm -> ty -> Prop :=
| ty_con : forall envs n,
    has_ty envs (tnat n) tynat
| ty_var : forall env envs i t,
    env i = Some t ->
    has_ty (env :: envs) (tvar i) t
| ty_abs : forall env envs i t1 t2 body,
    has_ty (extend_tyenv i t1 env :: envs) body t2 ->
    has_ty (env :: envs) (tabs i body) (tyfun t1 t2)
| ty_fix : forall env envs x f t1 t2 body,
    has_ty (extend_tyenv x t1 (extend_tyenv f (tyfun t1 t2) env) :: envs) body t2 ->
    has_ty envs (tfix f x body) (tyfun t1 t2)
| ty_app : forall envs tm1 tm2 t1 t2,
    has_ty envs tm1 (tyfun t1 t2) ->
    has_ty envs tm2 t1 ->
    has_ty envs (tapp tm1 tm2) t2
| ty_box : forall box_env envs body t,
    has_ty (box_env :: envs) body t ->
    has_ty envs (tbox body) (tybox box_env t)
| ty_unbox : forall box_env envs e t,
    has_ty envs e (tybox box_env t) ->
    has_ty (box_env :: envs) (tunbox e) t
| ty_run : forall envs e t,
    has_ty envs e (tybox empty_tyenv t) ->
    has_ty envs (trun e) t.


Definition stuck : tm -> Prop :=
  fun t => forall t', not (step t 0 t').

Example example_stuck1 : stuck (tapp (tnat 1) (tnat 2)).
Proof.
  unfold stuck. unfold not. intros t'.
  remember (tnat 1) as t1. remember (tnat 2) as t2. remember (tapp t1 t2) as tapp.
  intros eval. 
  step_cases (induction eval) Case; inversion Heqtapp; clear Heqtapp; subst.
  Case "s_app1".
    apply IHeval. reflexivity. reflexivity. inversion eval.
  Case "s_app2".
    apply IHeval. reflexivity. reflexivity. inversion eval.
  Case "s_appabs".
    inversion H1.
  Case "s_appfix".
    inversion H1.
Qed.

