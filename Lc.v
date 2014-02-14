
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


Inductive tm_lvl : tm -> nat -> Prop :=
| l_nat : (* nats are terms at all levels *)
    forall n l,
    tm_lvl (tnat n) l
| l_var : (* variables are terms at all levels *)
    forall i l,
    tm_lvl (tvar i) l
| l_abs : forall i body l,
    tm_lvl body l -> tm_lvl (tabs i body) l
| l_app : forall t1 t2 l,
    tm_lvl t1 l -> tm_lvl t2 l -> tm_lvl (tapp t1 t2) l
| l_fix : forall i1 i2 body l,
    tm_lvl body l -> tm_lvl (tfix i1 i2 body) l
| l_box : forall body l,
    tm_lvl body (1 + l) -> tm_lvl (tbox body) l
| l_unbox : forall body l,
    tm_lvl body l -> tm_lvl (tunbox body) (1 + l)
| l_run : forall body l,
    tm_lvl body l -> tm_lvl (trun body) l.

Hint Constructors tm_lvl.


Lemma tm_lvl_inc :
  forall term lvl, tm_lvl term lvl -> tm_lvl term (1 + lvl).
Proof.
  intros term.
  tm_cases (induction term) Case; intros lvl td; inversion td; subst; auto.
Qed.


Inductive value : nat -> tm -> Prop :=
(* nats are values in all stages *)
| vnat : forall n l, value l (tnat n)

(* stage 0 values *)
| vabs_0 : forall v t, tm_lvl t 0 -> value 0 (tabs v t)
| vfix_0 : forall i1 i2 t, tm_lvl t 0 -> value 0 (tfix i1 i2 t)
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
    n > 0 -> value (1+n) v -> value n (tbox v)
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


Lemma values_are_terms :
  forall term lvl, value lvl term -> tm_lvl term lvl.
Proof.
  intros term. tm_cases (induction term) Case; auto.
  Case "tabs". intros lvl vd.
    destruct lvl.
    SCase "lvl = 0". apply l_abs. inversion vd; subst; auto.
    SCase "lvl = n + 1". apply l_abs. inversion vd; subst; auto.
  Case "tapp". intros. inversion H; subst; auto.
  Case "tfix". intros lvl vd.
    destruct lvl.
    SCase "lvl = 0". apply l_fix. inversion vd; subst; auto.
    SCase "lvl = n + 1". apply l_fix. inversion vd; subst; auto.
  Case "tbox". intros. apply l_box. inversion H; subst; auto.
  Case "tunbox". intros.
    destruct lvl.
    inversion H; subst. inversion H1.
    apply l_unbox. apply IHterm. inversion H; subst. simpl in H3. rewrite <- minus_n_O in H3. auto.
  Case "trun".
    intros. inversion H; subst; auto.
Qed.


Lemma values_are_terms' :
  forall term lvl, value (1+lvl) term -> tm_lvl term lvl.
Proof.
  intros term. tm_cases (induction term) Case; auto.
  Case "tabs". intros lvl vd.
    destruct lvl.
    SCase "lvl = 0". apply l_abs. inversion vd; subst; auto.
    SCase "lvl = n + 1". apply l_abs. inversion vd; subst; auto.
  Case "tapp". intros. inversion H; subst; auto.
  Case "tfix". intros lvl vd.
    destruct lvl.
    SCase "lvl = 0". apply l_fix. inversion vd; subst; auto.
    SCase "lvl = n + 1". apply l_fix. inversion vd; subst; auto.
  Case "tbox". intros. apply l_box. inversion H; subst; auto.
  Case "tunbox". intros. destruct lvl.
    SCase "lvl = 0". inversion H; subst. inversion H1. inversion H2.
    SCase "lvl = n + 1". apply l_unbox. inversion H; subst. apply IHterm. auto.
  Case "trun".
    intros. inversion H; subst; auto.
Qed.


Fixpoint subst (x : id) (s : tm) (n : nat) (t : tm) : tm :=
  match n with
  | 0 =>
      match t with
      | tnat _ => t
      | tvar v => if eq_id_dec v x then s else t
      | tabs v t' =>
          if eq_id_dec v x
          then t
          else tabs v (subst x s n t') (* TODO: FIXME *)
      | tfix f v t' =>
          if eq_id_dec f x
          then t
          else if eq_id_dec v x
               then t
               else tfix f v (subst x s n t') (* TODO: FIXME *)
      | tapp t1 t2 => tapp (subst x s n t1) (subst x s n t2)
      | tbox t' => tbox (subst x s (1+n) t')
      | tunbox _ => t (* unreachable case *)
      | trun t' => trun (subst x s n t')
      end
  | n =>
      match t with
      | tnat _
      | tvar _ => t
      | tabs v t' => tabs v (subst x s n t')
      | tfix f v t' => tfix f v (subst x s n t')
      | tapp t1 t2 => tapp (subst x s n t1) (subst x s n t2)
      | tbox t' => tbox (subst x s (1+n) t')
      | tunbox t' => tunbox (subst x s (n-1) t')
      | trun t' => trun (subst x s n t')
      end
  end.


Fixpoint fvs (n : nat) (t : tm) : set id :=
  match n with
  | 0 =>
      match t with
      | tnat _ => nil
      | tvar i => i :: nil
      | tabs i t' => set_remove eq_id_dec i (fvs n t')
      | tfix i1 i2 t' => set_remove eq_id_dec i1 (set_remove eq_id_dec i2 (fvs n t'))
      | tapp t1 t2 => set_union eq_id_dec (fvs n t1) (fvs n t2)
      | tbox t' => fvs (1 + n) t'
      | tunbox t' => fvs n t'
      | trun t' => fvs n t'
      end
  | n =>
      match t with
      | tnat _ => nil
      | tvar _ => nil
      | tabs _ t'
      | tfix _ _ t' => fvs n t'
      | tapp t1 t2 => set_union eq_id_dec (fvs n t1) (fvs n t2)
      | tbox t' => fvs (1 + n) t'
      | tunbox t' => fvs (n - 1) t'
      | trun t' => fvs n t'
      end
  end.


Definition closed (n : nat) (t : tm) : Prop :=
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
    step (tapp (tabs x e) v) 0 (subst x v 0 e)
| s_appfix : forall f x e v,
    value 0 v ->
    step (tapp (tfix f x e) v) 0 (subst x v 0 (subst f (tfix f x e) 0 e))
| s_box : forall e n e',
    step e (1 + n) e' ->
    step (tbox e) n (tbox e')
| s_run1 : forall e n e',
    step e n e' ->
    step (trun e) n (trun e')
| s_run : forall v,
    value 1 v ->
    step (trun (tbox v)) 0 v
| s_unb1 : forall e n e',
    step e n e' ->
    step (tunbox e) (1 + n) (tunbox e')
| s_unb : forall v,
    value 1 v ->
    step (tunbox (tbox v)) 1 v
| s_abs : forall x e n e',
    step e (1 + n) e' ->
    step (tabs x e) (1 + n) (tabs x e')
| s_fix : forall f x e n e',
    step e (1 + n) e' ->
    step (tfix f x e) (1 + n) (tfix f x e').

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

(*
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
*)

Lemma empty_union : forall set1 set2,
  set_union eq_id_dec set1 set2 = nil <-> set1 = nil /\ set2 = nil.
Proof.
  intro set1. destruct set1 as [|h1 t1].
  Case "set1 = nil". intros. destruct set2 as [|h2 t2].
    SCase "set2 = nil". split; auto.
    SCase "set2 = h2 :: t2". split; intros.
      split. reflexivity. simpl in H. apply set_add_not_empty in H. inversion H.
      inversion H. inversion H1.
  Case "set1 = h1 :: t1". intros. destruct set2 as [|h2 t2].
    SCase "set2 = nil". split; intros; auto. inversion H. inversion H0.
    SCase "set2 = h2 :: t2". split; intros.
      simpl in H. apply set_add_not_empty in H. inversion H.
      inversion H. inversion H0.
Qed.



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
    has_ty ((extend_tyenv x t1 (extend_tyenv f (tyfun t1 t2) env)) :: envs) body t2 ->
    has_ty (env :: envs) (tfix f x body) (tyfun t1 t2)
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


Theorem progress : forall term tau n envs,
  tm_lvl term n ->
  has_ty (envs ++ [empty_tyenv]) term tau ->
  length envs = n ->
  value n term \/ exists term', step term n term'.
Proof.
  intros term. 
  tm_cases (induction term) Case.

  Case "tnat". auto.

  Case "tvar". intros tau n envs tlvld td ld. destruct n as [|n'].
    SCase "n = 0". destruct envs as [|h t]. 
       rewrite app_nil_l in td. inversion td. inversion H3. simpl in ld. inversion ld.
    SCase "n = n' + 1". left. apply vvar_n. omega.

  Case "tabs". intros tau n envs tlvld td ld. destruct n as [|n'].
    SCase "n = 0". left. apply vabs_0. inversion tlvld; subst. auto.
    SCase "n = n' + 1". inversion td; subst.
      destruct envs as [|head tail].
        inversion ld.        
      destruct (IHterm t2 (S n') ((extend_tyenv i t1 head) :: tail)). 
      inversion tlvld; subst. auto.
      simpl in H. inversion H. rewrite H1, H2 in H3. auto.
      apply ld.
      left. apply vabs_n. omega. apply H0. 
      right. inversion H0. exists (tabs i x). apply s_abs. apply H1.

  Case "tapp". intros tau n envs tlvld td ld. destruct n as [|n'].
    SCase "n = 0". admit.
    SCase "n = S n'".
      inversion td; subst.
      destruct (IHterm1 (tyfun t1 tau) (S n') envs).
        inversion tlvld; subst. apply H1. apply H2. apply ld.
      destruct (IHterm2 t1 (S n') envs).
        inversion tlvld; subst. apply H6. apply H4. apply ld.
      SSCase "term1 and term2 are values".
        left. apply vapp_n. omega. apply H. apply H0.
      SSCase "term1 is a value, term2 takes a step".
        right. inversion H0. exists (tapp term1 x). apply s_app2. apply H. apply H1.
      SSCase "term1 takes a step".
        right. inversion H. exists (tapp x term2). apply s_app1. apply H0. 

  Case "tfix". intros tau n envs tlvld td ld. destruct n as [|n'].
    SCase "n = 0". left. apply vfix_0. inversion tlvld; subst. apply H3.
    SCase "n = n' + 1". inversion td; subst.
      destruct envs as [|head tail].
        inversion ld.
      destruct (IHterm t2 (S n') (extend_tyenv i0 t1 (extend_tyenv i (tyfun t1 t2) head) :: tail)). 
      inversion tlvld; subst. auto.
      simpl in H. inversion H. rewrite H1, H2 in H4. auto.
      apply ld.
      left. apply vfix_n. omega. apply H0.
      right. inversion H0. exists (tfix i i0 x). apply s_fix. apply H1.

  Case "tbox". intros tau n envs tlvld td ld. 
    inversion td.
    destruct (IHterm t (1+n) (box_env :: envs)).
    inversion tlvld. apply H4. 
    apply H1. admit. (* TODO: length tl = n -> length (h::tl) = 1+n *)
    SCase "body is a value".
      left. destruct n as [|n'].
        apply vbox_0. apply H3.
        apply vbox_n. omega. apply H3.
    SCase "body takes a step". 
    right. inversion H3. exists (tbox x). apply s_box. apply H4.

  Case "tunbox". intros tau n envs tlvld td ld.
    destruct n as [|n'].
    SCase "n = 0". inversion tlvld.
    SCase "n = n' + 1".
      inversion td; subst.
      destruct envs as [|hdenvs tlenvs]. inversion ld. 
      destruct (IHterm (tybox box_env tau) n' (tlenvs)).
      inversion tlvld. apply H3.
      inversion H. rewrite <- H3, <- H2. apply H1.
      admit. (* TODO: length (h::tl) = S n  -> length tl = n. *) 
      SSCase "body is a value". 
        destruct n' as [|n''].
        SSSCase "n = 1 | n' = 0".
          right. 
          inversion H0; subst. (* Now find out that term is a tbox *)
          SSSSCase "tnat". inversion H1.
          SSSSCase "tabs". inversion H1.
          SSSSCase "tfix". inversion H1.
          SSSSCase "tbox". 
            exists v. apply s_unb. apply H2.
          inversion H2. inversion H2. inversion H2. inversion H2.
          inversion H2. inversion H2. inversion H2.
        SSSCase "n = S(S n'')".
          left. apply vunbox_n. omega. simpl. apply H0.
      SSCase "body takes a step".
        right. inversion H0. exists (tunbox x). apply s_unb1. apply H2.

  Case "trun". intros tau n envs tlvld td ld. 
    destruct (IHterm (tybox empty_tyenv tau) n (envs)). 
    inversion tlvld. apply H0.
    inversion td. apply H1.
    apply ld.

    destruct n as [|n'].
    SCase "n = 0". inversion td; subst. 
        right. inversion H2; subst. 
        SSSCase "tvar". inversion H. inversion H5.
        SSSCase "tapp". inversion H. inversion H5.
        SSSCase "tbox". exists body. apply s_run. inversion H. apply H1. apply H5. 
        SSSCase "tunbox". inversion H. inversion H4.
        SSSCase "trun". inversion H. inversion H3.
    SCase "n = n' + 1". inversion td; subst.
      SSCase "term is a value". 
        left. apply vrun_n. omega. apply H.
      SSCase "term takes a step".
        right. inversion H. exists (trun x). apply s_run1. apply H0.
Qed.

(* Local Variables: *)
(* coq-prog-name: "/usr/local/bin/coqtop" *)
(* coq-load-path: nil *)
(* End: *)
