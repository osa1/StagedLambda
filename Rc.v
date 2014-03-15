
Require Export SfLib.
Require Import Coq.Lists.ListSet.
Require Import List. Open Scope list_scope.
Require Import FunctionalExtensionality.




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
