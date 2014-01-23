
Require Export SfLib.


Inductive tm :=
| tnat : nat -> tm
| tvar : id -> tm
| tabs : id -> tm -> tm
| tapp : tm -> tm -> tm
| tfix : id -> id -> tm -> tm
| tbox : tm -> tm
| tunbox : tm -> tm
| trun : tm -> tm.


Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tnat" | Case_aux c "tvar"
  | Case_aux c "tabs" | Case_aux c "tapp"
  | Case_aux c "tfix" | Case_aux c "tbox"
  | Case_aux c "tunbox" | Case_aux c "trun" ].


Inductive value : nat -> tm -> Prop :=
| vvvv : forall n, value 10 (tnat n). (* TODO: implement this *)


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


Inductive closed : nat -> tm -> Prop :=
| c_nat : forall n, closed 0 (tnat n). (* TODO: implement this *)


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
