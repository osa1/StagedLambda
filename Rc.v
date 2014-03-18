
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
