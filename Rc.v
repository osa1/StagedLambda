
Require Export SfLib.
Require Import Coq.Lists.ListSet.
Require Import List. Open Scope list_scope.
Require Import FunctionalExtensionality.


Inductive var_kind :=
| holevar : var_kind
| recvar : var_kind
| ordvar : var_kind.


Inductive tm :=
| tnat : nat -> tm
| tvar : id -> tm
| tabs : id -> tm -> tm
| tapp : tm -> tm -> tm
| tfix : id -> id -> tm -> tm
| trec : rec -> tm
| trec_select : rec -> id -> tm
| tlet : id -> tm -> tm -> tm

with rec :=
| rempty : rec
| rvar : id -> rec
| rextend1 : rec -> id -> id -> rec
| rextend2 : rec -> id -> tm -> rec.


Inductive value : tm -> Prop :=
| vnat : forall n, value (tnat n)
| vabs : forall i1 t, value (tabs i1 t)
| vfix : forall i1 i2 t, value (tfix i1 i2 t)
| vrec : forall t, recordval t -> value (trec t)

with recordval : rec -> Prop :=
| emptyrec : recordval rempty
| recordext : forall r i t,
    value t ->
    recordval r ->
    recordval (rextend2 r i t).

Inductive substx :=
| substx_var : id -> tm -> substx
| substx_record : id -> rec -> substx.


Inductive subst : substx -> tm -> tm -> Prop :=
| snat : forall x n, subst x (tnat n) (tnat n)
| svar : forall i t, subst (substx_var i t) (tvar i) t
| svar1 : forall a b r, subst (substx_record a r) (tvar b) (tvar b)
| svar2 : forall a b t, a <> b -> subst (substx_var a t) (tvar b) (tvar b)
| sabs : forall x i t b b',
    x <> i ->
    subst (substx_var x t) b b' ->
    subst (substx_var x t) (tabs i b) (tabs i b')
| sabs' : forall x i r b b',
    subst (substx_record x r) b b' ->
    subst (substx_record x r) (tabs i b) (tabs i b')
| sabs1 : forall x t b,
    subst (substx_var x t) (tabs x b) (tabs x b)
| sapp : forall x t1 t2 t1' t2',
    subst x t1 t1' ->
    subst x t2 t2' ->
    subst x (tapp t1 t2) (tapp t1' t2')
| srec : forall x r r',
    subst_rec x r r' ->
    subst x (trec r) (trec r')
| srec_select : forall x i r r',
    subst_rec x r r' ->
    subst x (trec_select r i) (trec_select r' i)
| slet : forall i x t t1 t2 t1' t2',
    i <> x ->
    subst (substx_var x t) t1 t1' ->
    subst (substx_var x t) t2 t2' ->
    subst (substx_var x t) (tlet i t1 t2) (tlet i t1' t2')
| slet' : forall x r i t1 t2 t1' t2',
    subst (substx_record x r) t1 t1' ->
    subst (substx_record x r) t2 t2' ->
    subst (substx_record x r) (tlet i t1 t2) (tlet i t1' t2')
| slet1 : forall i t t1 t2 t1',
    subst (substx_var i t) t1 t1' ->
    subst (substx_var i t) (tlet i t1 t2) (tlet i t1' t2)

with subst_rec : substx -> rec -> rec -> Prop :=
| srec_empty : forall x, subst_rec x rempty rempty
| srec_var : forall i r,
    subst_rec (substx_record i r) (rvar i) r
| srec_var' : forall a b t,
    subst_rec (substx_var a t) (rvar b) (rvar b)
| srec_var'' : forall a b r,
    a <> b ->
    subst_rec (substx_record a r) (rvar b) (rvar b)
| srec_extend : forall r i t x t',
    subst x t t' ->
    subst_rec x (rextend2 r i t) (rextend2 r i t').


Inductive access : rec -> id -> tm -> Prop :=
| access1 : forall r i t i' t',
    access r i t ->
    access (rextend2 r i' t') i t
| access2 : forall r i t,
    access (rextend2 r i t) i t.


Inductive step : tm -> tm -> Prop :=
|  step_app1 : forall t1 t2 t1',
    step t1 t1' ->
    step (tapp t1 t2) (tapp t1' t2)
| step_app2 : forall t1 t2 t2',
    value t1 ->
    step t2 t2' ->
    step (tapp t1 t2) (tapp t1 t2')
| step_appabs : forall i x t t',
    subst (substx_var i x) t t' ->
    step (tapp (tabs i t) x) t'
| step_let1 : forall i t1 t2 t1',
    step t1 t1' ->
    step (tlet i t1 t2) (tlet i t1' t2)
| step_let : forall i x t t',
    value x ->
    subst (substx_var i x) t t' ->
    step (tlet i x t) t'
| step_acc : forall r x t,
    recordval r ->
    access r x t ->
    step (trec_select r x) t.

Hint Constructors step.


Inductive ty :=
| tynat : ty
| tyarr : ty -> ty -> ty
| tyrec : (id -> option ty) -> ty.


Definition tyenv := id -> option ty.

Definition empty_tyenv : tyenv := fun i => None.

Definition extend_tyenv env i (t : ty) :=
    fun i' => if eq_id_dec i' i then Some t else env i'.

Definition recty := tyenv.


Inductive has_ty : tyenv -> tm -> ty -> Prop :=
| typenat : forall env n,
    has_ty env (tnat n) tynat
| typevar : forall env i ty,
    env i = Some ty ->
    has_ty env (tvar i) ty
| typeabs : forall env x t ty1 ty2,
    has_ty (extend_tyenv env x ty1) t ty2 ->
    has_ty env (tabs x t) (tyarr ty1 ty2)
| tyfix : forall env f x t ty1 ty2,
    has_ty (extend_tyenv (extend_tyenv env x ty1) f (tyarr ty1 ty2)) t ty2 ->
    has_ty env (tfix f x t) (tyarr ty1 ty2)
| tyapp : forall env t1 t2 ty1 ty2,
    has_ty env t1 (tyarr ty1 ty2) ->
    has_ty env t2 ty1 ->
    has_ty env (tapp t1 t2) ty2
| tylet : forall env i x body ty1 ty2,
    has_ty env x ty1 ->
    has_ty (extend_tyenv env i ty1) body ty2 ->
    has_ty env (tlet i x body) ty2
| tyempty_rec : forall env,
    has_ty env (trec rempty) (tyrec empty_tyenv)
| tyupate_rec : forall env i ext ty r recty,
    has_ty env ext ty ->
    has_ty_rec env r recty ->
    has_ty env (trec (rextend2 r i ext)) (tyrec (extend_tyenv recty i ty))
| tyacc_rec : forall env rec recty i ty,
    has_ty_rec env rec recty ->
    recty i = Some ty ->
    has_ty env (trec_select rec i) ty

with has_ty_rec : tyenv -> rec -> recty -> Prop :=
| has_ty_rec_empty : forall env,
    has_ty_rec env rempty empty_tyenv
| has_ty_rec_extend1 : forall env i var extty rec recty,
    has_ty env (tvar var) extty ->
    has_ty_rec env rec recty ->
    has_ty_rec env (rextend1 rec i var) (extend_tyenv recty i extty)
| has_ty_rec_extend2 : forall env i ext extty rec recty,
    has_ty env ext extty ->
    has_ty_rec env rec recty ->
    has_ty_rec env (rextend2 rec i ext) (extend_tyenv recty i extty).


Theorem progress : forall tm ty,
    has_ty empty_tyenv tm ty ->
    value tm \/ exists tm', step tm tm'.
Proof.
    intros tm. induction tm.
    Case "tnat". intros. left. apply vnat.
    Case "tnat". intros. inversion H. inversion H2.
    Case "tabs". admit.
    Case "tapp". intros. inversion H; subst. destruct IHtm1 with (ty := tyarr ty1 ty0); auto.
      SCase "tm1 is value". destruct IHtm2 with (ty := ty1); auto.
        SSCase "tm2 is value". (* tm1 should be a lambda or fix *) inversion H3; subst.
          inversion H3. inversion H7.
          (* show substitution *) admit.
          (* same as appabs *) admit.
          inversion H0.
          inversion H0.
          inversion H0.
        SSCase "tm2 can take a step".
          right. inversion H1. exists (tapp tm1 x); auto.
      SCase "tm1 can take a step".
        right. inversion H0. exists (tapp x tm2); auto.
    Case "tfix". admit.
    Case "trec". admit.
    Case "trec_select". admit.
    Case "tlet". intros. right. inversion H; subst. destruct IHtm1 with (ty := ty1); auto.
      SCase "tm1 is value". (* again, need to show substitution *) admit.
      SCase "tm1 can take a step". inversion H0. exists (tlet i x tm2). auto.
Qed.
