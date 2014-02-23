
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

Hint Resolve tm_lvl_inc.


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

Hint Resolve values_are_terms.


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

Hint Resolve values_are_terms'.


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

Hint Resolve subst.


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

Hint Resolve fvs.


Definition closed (n : nat) (t : tm) : Prop :=
  fvs n t = empty_set id.

Hint Unfold closed.


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

Example example3_evaluation :
  step example3 0 (tnat 42).
Proof.
  unfold example3.
  remember (tunbox (tbox (tnat 42))) as rhs.
  assert (step rhs 1 (tnat 42)).
  Case "proof of assertion". rewrite Heqrhs. apply example2_evaluation.
  constructor. auto.
Qed.


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
                         else e i'.

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

Hint Constructors has_ty.

Tactic Notation "ty_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ty_con" | Case_aux c "ty_var"
  | Case_aux c "ty_abs" | Case_aux c "ty_fix"
  | Case_aux c "ty_app" | Case_aux c "ty_box"
  | Case_aux c "ty_unbox" | Case_aux c "ty_run" ].


Definition stuck : tm -> Prop :=
  fun t => forall t', not (step t 0 t').

Hint Unfold stuck.


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

  Case "tapp". intros tau n envs tlvld td ld.
    inversion td.
    destruct (IHterm1 (tyfun t1 tau) n envs).
      inversion tlvld; subst. apply H7. apply H2. apply ld.
    destruct (IHterm2 t1 n envs).
      inversion tlvld; subst. apply H10. apply H4. apply ld.
    SCase "term1 and term2 are values".
      destruct n as [|n'].
      SSCase "n = 0".
        inversion H5; subst. (* Find out the shape of the rator. Can be either lambda or fix. *)
        SSSCase "tnat". inversion H2.
        SSSCase "tabs". right. exists (subst v term2 0 t). apply s_appabs. apply H6.
        SSSCase "tfix". right. exists (subst i2 term2 0 (subst i1 (tfix i1 i2 t) 0 t)).
                        apply s_appfix. apply H6.
        SSSCase "tbox". inversion H2.
        inversion H7. inversion H7. inversion H7. inversion H7.
        inversion H7. inversion H7. inversion H7.
      SSCase "n = S n'".
        left. apply vapp_n. omega. apply H5. apply H6.
    SCase "term1 is a value, term2 takes a step".
      right. inversion H6. exists (tapp term1 x). apply s_app2. apply H5. apply H7.
    SCase "term1 takes a step".
      right. inversion H5. exists (tapp x term2). apply s_app1. apply H6.

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
      inversion tlvld.  apply H4.
      apply H1.
      simpl. rewrite ld. reflexivity.
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
        simpl in ld. inversion ld. rewrite H2. reflexivity.
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


Lemma env_elimination : forall v n envn envs env0 tau,
  value (1+n) v ->
  length envs = n ->
  has_ty ((envn :: envs) ++ [env0]) v tau ->
  has_ty (envn :: envs) v tau.
Proof.
  intro v. tm_cases (induction v) Case; intros.
  
  Case "tnat". inversion H1. apply ty_con.

  Case "tvar". inversion H1. subst. auto.

  Case "tabs". inversion H1.
    apply IHv with (n := n) in H7. auto. subst. inversion H; auto. auto.

  Case "tapp". inversion H1.
    apply IHv1 with (n := n) in H5.
    apply IHv2 with (n := n) in H7.
    apply ty_app with (t1 := t1).
    subst. apply H5. apply H7.
    inversion H. apply H13. apply H0.
    inversion H. apply H12. apply H0.

  Case "tfix". inversion H1.
    apply IHv with (n := n) in H8. auto. subst. inversion H; auto. auto.

  Case "tbox". inversion H1.
    apply IHv with (n:= 1+n) in H4.
    apply (ty_box box_env (envn::envs) v t).
    apply H4. inversion H; subst. apply H9. simpl. rewrite H0. reflexivity.
    
  Case "tunbox". inversion H1.
    destruct envs as [|hdenvs tlenvs].
    SCase "envs is []". inversion H. simpl in H0. rewrite <- H0 in H8. omega.
    SCase "envs is hd::tl".
      destruct n as [|n']. inversion H. omega.
      apply IHv with (n := n') (envn := hdenvs) (envs := tlenvs) (tau := (tybox envn tau)) in H6.
      apply (ty_unbox envn (hdenvs::tlenvs) v tau).
      apply H6. inversion H; subst. simpl. apply H10.
      auto.
  
  Case "trun". inversion H1.
    apply IHv with (n := n) in H4.
    apply (ty_run (envn::envs) v tau).
    apply H4. inversion H. apply H9. apply H0.
Qed.

Hint Resolve env_elimination.


Lemma env_addition : forall term n envn envs env0 tau,
  tm_lvl term n ->
  length envs = n ->
  has_ty (envn :: envs) term tau ->
  has_ty ((envn :: envs) ++ [env0]) term tau.
Proof.
  intro v. tm_cases (induction v) Case; intros; inversion H1; auto.

  Case "tvar". apply ty_var. apply H6.

  Case "tabs". subst.
    apply ty_abs. apply IHv with (n := length envs) (env0 := env0) in H7; auto.
    inversion H; auto.

  Case "tapp". subst. inversion H; subst.
    apply IHv1 with (n := length envs) (env0 := env0) in H5; auto.
    apply IHv2 with (n := length envs) (env0 := env0) in H7; auto.
    apply ty_app with (t1 := t1); auto.

  Case "tfix". subst.
    apply ty_fix. apply IHv with (n := length envs) (env0 := env0) in H8; auto.
    inversion H; auto.

  Case "tbox". apply IHv with (n := 1 + n) (env0 := env0) in H4; auto.
    inversion H; auto. inversion H0; auto.

  Case "tunbox". destruct envs as [|hd tl].
    SCase "envs = []". inversion H. rewrite <- H9 in H0. inversion H0.
    SCase "envs = hd :: tl". apply IHv with (n := n-1) (env0 := env0) in H6.
      apply ty_unbox; auto. inversion H; subst. simpl. rewrite <- minus_n_O. auto. simpl in H0.
        destruct n as [|n']. inversion H0. rewrite <- H0. simpl. omega.

  Case "trun". apply IHv with (n := n) (env0 := env0) in H4; auto.
    inversion H; auto.
Qed.

Hint Resolve env_addition.


Definition extension := fun (e1 e2 : tyenv) => forall i tau,
  e2 i = Some tau -> e1 i = Some tau.

Hint Unfold extension.

Lemma any_env_extends_empty_env : forall env,
  extension env empty_tyenv.
Proof.
  intros. unfold extension. intros. unfold empty_tyenv in H. inversion H.
Qed.

Hint Resolve any_env_extends_empty_env.


Lemma extension_preservation : forall env env' x tau,
  extension env env' ->
  extension (extend_tyenv x tau env) (extend_tyenv x tau env').
Proof.
  intros. unfold extension in H.
  unfold extend_tyenv. intros i.
  destruct (eq_id_dec x i); auto.
Qed.

Hint Resolve extension_preservation.


Lemma env_shadowing : forall env x tau tau',
  extend_tyenv x tau (extend_tyenv x tau' env) = extend_tyenv x tau env.
Proof.
  intros. apply functional_extensionality. intro. destruct (eq_id_dec x0 x).
  Case "x0 = x". rewrite e. unfold extend_tyenv. rewrite eq_id. rewrite eq_id. reflexivity.
  Case "x0 <> x". unfold extend_tyenv. rewrite neq_id; auto. rewrite neq_id; auto. rewrite neq_id; auto.
Qed.

Hint Resolve env_shadowing.


Lemma env_permutability : forall env x y tau tau',
  x <> y ->
  extend_tyenv x tau (extend_tyenv y tau' env) = extend_tyenv y tau' (extend_tyenv x tau env).
Proof.
  admit.
Qed.


Lemma weakening : forall term envs env0 env0' tau n,
  has_ty (envs ++ [env0]) term tau ->
  extension env0' env0 ->
  tm_lvl term n ->
  length envs = n ->
  has_ty (envs ++ [env0']) term tau.
Proof.
  intro term. tm_cases (induction term) Case.

  Case "tnat". intros. inversion H; auto.

  Case "tvar". destruct envs as [|h t].
    SCase "envs = []". intros. unfold extension in H0.
      simpl. apply ty_var. apply H0. simpl in H. inversion H. auto.
    SCase "envs = h :: t". intros. unfold extension in H0.
      inversion H; subst. apply ty_var. apply H7.

  Case "tabs". intros. inversion H. destruct envs as [|hdenvs tlenvs].
    SCase "envs is []".
      simpl. simpl in H. simpl in H3. subst. inversion H3. rewrite H5 in H7, H3.
      rewrite H4 in H7, H3.
      apply IHterm with (envs := []) (env0 := extend_tyenv i t1 env0) (env0' := extend_tyenv i t1 env0') (n := 0) in H7. simpl in H7; auto.
      apply extension_preservation with (env := env0') (env' := env0) (x := i) (tau := t1); auto.
      simpl in H1. inversion H1; auto. auto.
    SCase "envs is hdenvs :: tlenvs".
      inversion H3. rewrite H10 in H7.
      apply IHterm with (envs := extend_tyenv i t1 env :: tlenvs) (env0' := env0') (n := n) in H7; auto.
      simpl. simpl in H7. rewrite H9 in H7. apply ty_abs. assumption.
      inversion H1. assumption.

  Case "tapp". intros. inversion H.
      apply IHterm1 with (env0' := env0') (n := n) in H6; auto.
      apply IHterm2 with (env0' := env0') (n := n) in H8; auto.
      apply (ty_app (envs ++ [env0']) term1 term2 t1 tau); auto.
      inversion H1; auto.
      inversion H1; auto.

  Case "tfix". intros. destruct envs as [|hdenvs tlenvs].
    SCase "envs is []". inversion H. apply ty_fix.
      remember (extend_tyenv i0 t1 (extend_tyenv i (tyfun t1 t2) env0)) as extended_env.
      assert ([extended_env] = [] ++ [extended_env]); auto. rewrite H10 in H9.
      apply IHterm with (env0' := extend_tyenv i0 t1 (extend_tyenv i (tyfun t1 t2) env0')) (n := 0) in H9; auto.
      rewrite Heqextended_env; auto.
      inversion H1; subst; auto.
    SCase "envs is hdenvs :: tlenvs". inversion H; subst.
      rewrite app_comm_cons in H9. apply IHterm with (env0' := env0') (n := length (hdenvs :: tlenvs)) in H9; simpl; auto.
        inversion H1; auto.

  Case "tbox". intros. inversion H.
    apply IHterm with (env0' := env0') (envs := (box_env :: envs)) (n := 1+n) in H5; auto.
    inversion H1; auto. simpl. rewrite H2. reflexivity.

  Case "tunbox". intros. 
    destruct envs as [|h t]. 
    SCase "envs = []".
      simpl in H2. rewrite <- H2 in H1. inversion H1.
    SCase "envs = h :: t".
      simpl in H. simpl. inversion H.
      apply IHterm with (env0' := env0') (envs := t) (n := n - 1) in H7; subst; auto.
      inversion H1. simpl. rewrite <- H3 in H4. rewrite <- H3.
      destruct l as [|l']; auto. simpl. apply minus_n_O.

  Case "trun". intros. inversion H.
    apply IHterm with (env0' := env0') (n:= n) in H5; auto.
    inversion H1; auto.
Qed.

Hint Resolve weakening.


Lemma substitutability : forall e n x xsubst taux tau envs env0, 
  tm_lvl e n ->
  tm_lvl xsubst 0 ->
  closed 0 xsubst ->
  length envs = n ->
  has_ty (envs ++ [extend_tyenv x taux env0]) e tau ->
  has_ty [empty_tyenv] xsubst taux ->
  has_ty (envs ++ [env0]) (subst x xsubst n e) tau.
Proof.
  intro e. tm_cases (induction e) Case.

  Case "tnat". intros. simpl. destruct n0 as [|n']; inversion H3; apply ty_con.

  Case "tvar". intros. simpl. destruct n as [|n'].
    SCase "n = 0". destruct (eq_id_dec i x).
      SSCase "i = x". subst. destruct envs as [|hdenvs tlenvs].
        SSSCase "envs = []". simpl in H3. simpl.
          inversion H3. unfold extend_tyenv in H9.
          destruct (eq_id_dec x x).
          SSSSCase "x = x". inversion H9; subst.
            apply weakening with (term := xsubst) (envs := []) (env0 := empty_tyenv) (env0' := env0) (tau := tau) (n := 0).
            simpl. assumption.
            apply (any_env_extends_empty_env env0).
            assumption. auto.
          SSSSCase "x <> x". tauto.
        SSSCase "envs = hdenvs :: tlenvs". simpl in H2. inversion H2.
      SSCase "i <> x". destruct envs as [|hdenvs tlenvs].
        SSSCase "envs  = []".
          simpl. simpl in H3. inversion H3. subst.
          unfold extend_tyenv in H9. destruct (eq_id_dec x i).
          SSSSCase "i = x". rewrite e in n. tauto.
          SSSSCase "i <> x". apply ty_var. assumption.
        SSSCase "envs = hdenvs :: tlenvs".
          simpl in H2. inversion H2.
    SCase "n = S n'". destruct envs as [|hdenvs tlenvs].
      SSCase "envs = []". simpl in H2. inversion H2.
      SSCase "envs = hdenvs :: tlenvs".
        inversion H3. simpl. apply ty_var. assumption.

  Case "tabs". intros. inversion H3. inversion H.
    destruct n as [|n'].
    SCase "n = 0". destruct envs as [|hdenvs tlenvs].
      SSCase "envs = []". simpl in *. destruct (eq_id_dec i x).
        SSSCase "i = x". inversion H5. subst.
          rewrite env_shadowing in H9.
          apply ty_abs. assumption.
        SSSCase "i <> x". inversion H5. subst.
          rewrite env_permutability in H9.
          apply ty_abs.
          apply IHe with (n := 0) (x := x) (xsubst := xsubst) (taux := taux) (tau := t2) (envs := []) (env0 := (extend_tyenv i t1 env0)) in H9; auto.
          auto.
      SSCase "envs = hdenvs :: tlenvs". inversion H2.
    SCase "n = S n'". destruct envs as [|hdenvs tlenvs].
      SSCase "envs = []". simpl in H2. inversion H2.
      SSCase "envs = hdenvs :: tlenvs". inversion H5. subst.
        simpl in *. apply ty_abs.
        apply IHe with (n := S n') (x := x) (xsubst := xsubst) (taux := taux) (tau := t2) (envs := extend_tyenv i t1 hdenvs :: tlenvs) (env0 := env0) in H9; auto.

  Case "tapp". intros. inversion H3. inversion H. subst.
    apply IHe1 with (n := length envs) (x := x) (env0 := env0) (envs := envs) (xsubst := xsubst) (tau := tyfun t1 tau) in H8; auto.
    apply IHe2 with (n := length envs) (x := x) (env0 := env0) (envs := envs) (xsubst := xsubst) (tau := t1) in H10; auto.
    simpl. destruct (length envs) as [|n'].
    apply ty_app with (t1 := t1) (t2 := tau) (tm1 := (subst x xsubst 0 e1)) (tm2 := (subst x xsubst 0 e2)); auto.
    apply ty_app with (t1 := t1) (t2 := tau) (tm1 := (subst x xsubst (S n') e1)) (tm2 := (subst x xsubst (S n') e2)); auto.

  Case "tfix". admit.

  Case "tbox". intros. inversion H3. inversion H. subst.
    apply IHe with (n := 1 + length envs) (x := x) (env0 := env0) (envs := (box_env :: envs)) (xsubst := xsubst) (tau := t) in H7; auto.
    simpl. destruct (length envs) as [|n'].
    simpl in H7. apply ty_box in H7; auto.
    simpl in H7. apply ty_box in H7; auto.

  Case "tunbox". intros. inversion H3. inversion H. subst.
    destruct envs as [|hdenvs tlenvs].
    SCase "envs = []". simpl in H11. omega.
    SCase "envs = hdenvs :: tlenvs".
      inversion H5. rewrite H8 in H7.
      apply IHe with (n := l) (x := x) (env0 := env0) (envs := tlenvs) (xsubst := xsubst) (tau := (tybox box_env tau)) in H7; auto.
      simpl. apply ty_unbox. rewrite <- minus_n_O. rewrite <- H6.
      assumption.
      simpl in H11. inversion H11. reflexivity.

  Case "trun". intros. inversion H3. inversion H. subst.
    apply IHe with (n := length envs) (x := x) (env0 := env0) (envs := envs) (xsubst := xsubst) (tau := (tybox empty_tyenv tau)) in H7; auto.
    apply ty_run in H7; auto.
    simpl. destruct (length envs) as [|n']; auto.
Qed.

Hint Resolve substitutability.


Theorem preservation : forall term n envs tau term',
  tm_lvl term n ->
  length envs = 1 + n ->
  has_ty envs term tau ->
  step term n term' ->
  has_ty envs term' tau.
Proof.
  intro term. tm_cases (induction term) Case; intros.

  Case "tnat". inversion H2.

  Case "tvar". inversion H2.

  Case "tabs". destruct n as [|n'].
    SCase "n = 0". inversion H2.
    SCase "n = n' + 1".
      inversion H2; subst. inversion H1; subst.
      apply (IHterm (S n') (extend_tyenv i t1 env :: envs0) t2 e') in H8; auto.
        inversion H; auto.

  Case "tapp". intros. inversion H2; subst.
    SCase "e1 can take a step". inversion H1; subst. apply (IHterm1 n envs (tyfun t1 tau) e1') in H6; auto.
      apply (ty_app envs e1' term2 t1 tau); auto. inversion H; auto.
    SCase "e2 can take a step". inversion H1; subst. apply (IHterm2 n envs t1 e') in H10; auto.
      apply (ty_app envs term1 e' t1 tau); auto.
      inversion H; auto.
    SCase "application".
      inversion H1. inversion H6. subst.
      admit.

    SCase "fix". admit.

  Case "tfix". intros. destruct n as [|n'].
    SCase "n = 0". inversion H2.
    SCase "n = n' + 1". inversion H2; subst. inversion H1; subst.
      apply IHterm with (envs := extend_tyenv i0 t1 (extend_tyenv i (tyfun t1 t2) env) :: envs0) (tau := t2) in H8; auto.
        inversion H; auto.

  Case "tbox". intros. inversion H2; subst.
    inversion H1. apply (IHterm (1 + n) (box_env :: envs) t e') in H4; auto.
    inversion H; auto. simpl. rewrite H0. reflexivity.

  Case "tunbox". intros. destruct n as [|n'].
    SCase "n = 0". inversion H2.
    SCase "n = n' + 1". inversion H2; subst.
      SSCase "s_unb1". inversion H1. apply IHterm with (n := n') (term' := e') in H6; auto.
        inversion H; auto. subst. auto.
      SSCase "s_unb". inversion H1. inversion H6. apply H11.

  Case "trun". intros. inversion H2; subst.
    SCase "s_run1". inversion H1; subst. apply IHterm with (n := n) (term' := e') in H6; auto.
      inversion H; auto.
    SCase "s_run". inversion H1. inversion H6. subst.
      destruct envs as [|hdenvs tlenvs].
      SSCase "envs is []". inversion H0.
      SSCase "envs is hdenvs::tlenvs".
        inversion H0.
        destruct tlenvs as [|htlenvs ttlenvs].
        SSSCase "tlenvs is []".
          apply (env_elimination term' 0 empty_tyenv [] hdenvs tau) in H11; auto.
          admit. (* TODO: apply weakening here. *)
        SSSCase "tlenvs is not []".
          inversion H5.
Qed.


(* Local Variables: *)
(* coq-prog-name: "/usr/local/bin/coqtop" *)
(* coq-load-path: nil *)
(* End: *)
