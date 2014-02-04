
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


Fixpoint closed (n : nat) (t : tm) : Prop :=
  fvs n t = empty_set id.


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
    closed 0 v ->
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
  constructor. auto.
  unfold closed. simpl. reflexivity.
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


Tactic Notation "ty_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ty_con" | Case_aux c "ty_var"
  | Case_aux c "ty_abs" | Case_aux c "ty_fix"
  | Case_aux c "ty_app" | Case_aux c "ty_box"
  | Case_aux c "ty_unbox" | Case_aux c "ty_run" ].


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


Inductive tm_lvl : tm -> nat -> Prop :=
| l_nat : (* nats are terms at all levels *)
    forall n l,
    tm_lvl (tnat n) l
| l_var : (* variables are terms at all levels *)
    forall i l,
    tm_lvl (tvar i) l
| l_abs :
    forall i body l,
    tm_lvl body l -> tm_lvl (tabs i body) l
| l_app :
    forall t1 t2 l,
    tm_lvl t1 l -> tm_lvl t2 l -> tm_lvl (tapp t1 t2) l
| l_fix :
    forall i1 i2 body l,
    tm_lvl body l -> tm_lvl (tfix i1 i2 body) l
| l_box :
    forall body l,
    tm_lvl body (l + 1) -> tm_lvl (tbox body) l
| l_unbox :
    forall body l,
    tm_lvl body l -> tm_lvl (tunbox body) (l + 1)
| l_run :
    forall body l,
    tm_lvl body l -> tm_lvl (trun body) l

(* a term at level l is also a term at level l + 1 *)
| l_inc :
    forall t l,
    tm_lvl t l -> tm_lvl t (l + 1).


Theorem progress : forall term type,
  has_ty [empty_tyenv] term type ->
  value 0 term \/ exists term', step term 0 term'.
Proof.
  intros term type td. remember [empty_tyenv] as envs.
  ty_cases (induction td) Case; inversion Heqenvs; clear Heqenvs; subst.
  Case "ty_con". auto.
  Case "ty_var". right. inversion H.
  Case "ty_abs". auto.
  Case "ty_fix". auto.
  Case "ty_app". right.
    destruct IHtd1. reflexivity.
    SCase "tm1 is value".
      destruct IHtd2. reflexivity.
      SSCase "tm2 is value".
        value_cases (inversion H; subst) SSSCase.
          inversion td1.
          eauto.
          eauto.
          inversion td1.
          inversion H; subst. inversion H4.
          eauto.
          inversion H; subst. inversion H6.
          eauto.
          inversion td1.
          inversion H1.
          inversion H1.
      SSCase "tm2 can take a step".
        inversion H0. exists (tapp tm1 x). auto.
    SCase "tm1 can take a step".
      destruct IHtd2. reflexivity.
      SSCase "tm2 is value". inversion H. eexists (tapp x tm2). auto.
      SSCase "tm2 can take a step". inversion H. eexists (tapp x tm2). auto.
  Case "ty_box".
    (* proving this case is not possible since we're defining well-typedness
     * as having a type when type environments is [empty_env].
     * so inductive case of typing rule of ty_box says body of ty_box
     * should be well-typed in empty type environment, which is not
     * true, instead we need to type check body of ty_box with an extra
     * type environment
     *
     * I think we need to formulate this theorem in different way ..
     *)
    admit.
  Case "ty_unbox".
    (* this is also impossible to prove because of similar reasons .. *)
    admit.
  Case "ty_run". right.
    destruct IHtd. reflexivity.
    SCase "e is value". inversion td; subst.
      SSCase "e is tvar".
        (* this is not possible, since we're at level 0,
         * and variables are not values at level 0 *)
        inversion H; subst. inversion H2.
      SSCase "e is tapp".
        (* not possible since tapps are not values at level 0 *)
        inversion H; subst. inversion H4.
      SSCase "e is tbox".
        inversion H; subst. exists body. apply s_run. assumption.
        (* TODO: how to show argument of trun is closed??? *) admit.
        admit.
      SSCase "e is tunbox".
        (* unbox is not value at level 0 *)
        inversion H; subst. inversion H1.
      SSCase "e is trun".
        (* run is not a value at level 0 *)
        exists (trun e0). constructor. inversion H; subst. inversion H2.
    SCase "e can take a step".
      inversion H. exists (trun x). auto.
Qed.
