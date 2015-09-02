Require Export Types_J.
Module STLC.
  Inductive ty: Type :=
| ty_Bool: ty
| ty_arrow: ty -> ty -> ty.

  Inductive tm: Type :=
  | tm_var: id -> tm
  | tm_app: tm -> tm -> tm
  | tm_abs: id -> ty -> tm -> tm
  | tm_true: tm
  | tm_false: tm
  | tm_if: tm -> tm -> tm -> tm.

  Tactic Notation "tm_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "tm_var" | Case_aux c "tm_app"
      | Case_aux c "tm_abs" | Case_aux c "tm_true"
      | Case_aux c "tm_false" | Case_aux c "tm_if"].

  Notation a := (Id 0).
  Notation b := (Id 1).
  Notation c := (Id 2).

  Notation idB := (tm_abs a ty_Bool (tm_var a)).
  Notation idBB := (tm_abs a (ty_arrow ty_Bool ty_Bool) (tm_var a)).
  Notation idBBBB := (tm_abs a (ty_arrow (ty_arrow ty_Bool ty_Bool)
                                         (ty_arrow ty_Bool ty_Bool))
                             (tm_var a)).

  Notation k := (tm_abs a ty_Bool (tm_abs b ty_Bool (tm_var a))).

  Inductive value : tm -> Prop :=
  | v_abs: forall x T t,
             value (tm_abs x T t)
  | v_true: value tm_true
  | t_false: value tm_false.

  Hint Constructors value.

  Fixpoint subst (s:tm) (x:id) (t:tm): tm :=
    match t with
      | tm_var x' => if beq_id x x' then s else t
      | tm_abs x' T t1 => tm_abs x' T (if beq_id x x' then t1 else (subst s x t1))
      | tm_app t1 t2 => tm_app (subst s x t1) (subst s x t2)
      | tm_true => tm_true
      | tm_false => tm_false
      | tm_if t1 t2 t3 => tm_if (subst s x t1) (subst s x t2) (subst s x t3)
    end.

  Reserved Notation "t1 '==>' t2" (at level 40).

  Inductive step: tm -> tm -> Prop :=
  | ST_AppAbs: forall x T t12 v2,
                 value v2 ->
                 (tm_app (tm_abs x T t12) v2) ==> (subst v2 x t12)
  | ST_App1: forall t1 t1' t2,
               t1 ==> t1' ->
               tm_app t1 t2 ==> tm_app t1' t2
  | ST_App2: forall v1 t2 t2',
               value v1 ->
               t2 ==> t2' ->
               tm_app v1 t2 ==> tm_app v1 t2'
  | ST_IfTrue: forall t1 t2,
                 (tm_if tm_true t1 t2) ==> t1
  | ST_IfFalse: forall t1 t2,
                  (tm_if tm_false t1 t2) ==> t2
  | ST_If: forall t1 t1' t2 t3,
             t1 ==> t1' ->
             (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
  where "t1 '==>' t2" := (step t1 t2).


  Tactic Notation "step_cases" tactic(first) ident(c) :=
    first;
    [Case_aux c "ST_AppAbs" | Case_aux c "ST_App1"
     | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue"
     | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"].

  Notation stepmany := (refl_step_closure step).
  Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

  Hint Constructors step.

  Lemma step_example1:
    (tm_app idBB idB) ==>* idB.
    eapply rsc_step.
    apply ST_AppAbs.
    apply v_abs.
    simpl.
    apply rsc_refl.
  Qed.

  Lemma step_example2:
    (tm_app idBB (tm_app idBB idB)) ==>* idB.
  Proof.
    eapply rsc_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
    eapply rsc_step.
    apply ST_AppAbs. simpl. auto.
    simpl. apply rsc_refl.
  Qed.

  Lemma step_example3:
    (tm_app (tm_app idBBBB idBB) idB) ==>* idB.
  Proof.
    eapply rsc_step with (tm_app idBB idB).
    apply ST_App1.
    apply ST_AppAbs.
    auto.
    eapply rsc_step.
    apply ST_AppAbs.
    auto.
    apply rsc_refl.
  Qed.

  Definition context := partial_map ty.
  Module Context.
    Definition partial_map (A:Type) := id -> option A.
    Definition empty {A:Type} : partial_map A := (fun _ => None).
    Definition extend {A:Type} (Gamma:partial_map A) (x: id) (T: A) :=
      fun x' => if beq_id x x' then Some T else Gamma x'.

    Lemma extend_eq: forall A (ctxt: partial_map A) x T,
                       (extend ctxt x T) x = Some T.
    Proof.
      intros. unfold extend. rewrite <- beq_id_refl. auto.
    Qed.

    Lemma extend_neq: forall A (ctxt: partial_map A) x1 T x2,
                        beq_id x2 x1 = false ->
                        (extend ctxt x2 T) x1 = ctxt x1.
    Proof.
      intros. unfold extend. rewrite H. auto.
    Qed.

  End Context.

  Inductive has_type: context -> tm -> ty -> Prop :=
  | T_Var: forall Gamma x T,
             Gamma x = Some T ->
             has_type Gamma (tm_var x) T
  | T_Abs: forall Gamma x T11 T12 t12,
             has_type (extend Gamma x T11) t12 T12 ->
             has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App: forall T11 T12 Gamma t1 t2,
             has_type Gamma t1 (ty_arrow T11 T12) ->
             has_type Gamma t2 T11 ->
             has_type Gamma (tm_app t1 t2) T12
  | T_True: forall Gamma,
              has_type Gamma tm_true ty_Bool
  | T_False: forall Gamma,
               has_type Gamma tm_false ty_Bool
  | T_If: forall t1 t2 t3 T Gamma,
            has_type Gamma t1 ty_Bool ->
            has_type Gamma t2 T ->
            has_type Gamma t3 T ->
            has_type Gamma (tm_if t1 t2 t3) T.

  Tactic Notation "has_type_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "T_Var" | Case_aux c "T_Abs"
      | Case_aux c "T_App" | Case_aux c "T_True"
      | Case_aux c "T_False" | Case_aux c "T_If"].

  Hint Constructors has_type.

  Example typing_example_1:
    has_type empty (tm_abs a ty_Bool (tm_var a)) (ty_arrow ty_Bool ty_Bool).
  Proof.
    apply T_Abs.
    apply T_Var.
    reflexivity.
  Qed.

  Example typing_example_1':
    has_type empty (tm_abs a ty_Bool (tm_var a)) (ty_arrow ty_Bool ty_Bool).
  Proof.
    auto.
  Qed.

  Hint Unfold beq_id beq_nat extend.

  Example typing_example_2:
    has_type empty
             (tm_abs a ty_Bool
                     (tm_abs b (ty_arrow ty_Bool ty_Bool)
                             (tm_app (tm_var b) (tm_app (tm_var b) (tm_var a)))))
             (ty_arrow ty_Bool (ty_arrow (ty_arrow ty_Bool ty_Bool) ty_Bool)).
  Proof with auto using extend_eq.
    apply T_Abs.
    apply T_Abs.
    eapply T_App. apply T_Var...
    eapply T_App. apply T_Var...
    apply T_Var...
  Qed.


  Example typing_nonexample_1:
    ~ exists T,
         has_type empty
                  (tm_abs a ty_Bool
                          (tm_abs b ty_Bool
                                  (tm_app (tm_var a) (tm_var b))))
                  T.
  Proof.
    intros C. destruct C.
    inversion H. subst. clear H.
    inversion H5. subst. clear H5.
    inversion H4. subst. clear H4.
    inversion H2. subst. clear H2.
    inversion H5. subst. clear H5.
    inversion H1.
  Qed.

  Inductive appears_free_in: id -> tm -> Prop :=
  | afi_var: forall x,
               appears_free_in x (tm_var x)
  | afi_app1: forall x t1 t2,
                appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
  | afi_app2: forall x t1 t2,
                appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
  |  afi_abs: forall x y T11 t12,
                y <> x ->
                appears_free_in x t12 ->
                appears_free_in x (tm_abs y T11 t12)
  | afi_if1: forall x t1 t2 t3,
               appears_free_in x t1 ->
               appears_free_in x (tm_if t1 t2 t3)
  | afi_if2: forall x t1 t2 t3,
               appears_free_in x t2 ->
               appears_free_in x (tm_if t1 t2 t3)
  | afi_if3: forall x t1 t2 t3,
               appears_free_in x t3 ->
               appears_free_in x (tm_if t1 t2 t3).

  Tactic Notation "afi_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "afi_var"
    | Case_aux c "afi_app1" | Case_aux c "afi_app2"
    | Case_aux c "afi_abs"
    | Case_aux c "afi_if1" | Case_aux c "afi_if2"
    | Case_aux c "afi_if3"].

  Hint Constructors appears_free_in.

  Definition closed (t: tm) :=
    forall x, ~ appears_free_in x t.

  Lemma free_in_context: forall x t T Gamma,
                           appears_free_in x t ->
                           has_type Gamma t T ->
                           exists T', Gamma x = Some T'.
  Proof.
    intros. generalize dependent Gamma. generalize dependent T.
    afi_cases(induction H) Case;
      intros; try solve [inversion H0; eauto].
    Case "afi_abs".
    inversion H1; subst.
    apply  IHappears_free_in in H7.
    apply not_eq_beq_id_false in H.
    rewrite extend_neq in H7. assumption.
    assumption.
  Qed.

  Corollary typable_empty_closed: forall t T,
                                  has_type empty t T ->
                                  closed t.
  Proof.
    intros. unfold closed.
    intros. intros contra.
    apply free_in_context with x t T empty in contra; auto.
    inversion contra. inversion H0.
  Qed.

  Lemma context_invariance: forall Gamma Gamma' t S,
                              has_type Gamma t S ->
                              (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
                              has_type Gamma' t S.
  Proof with eauto.
    intros.
    generalize dependent Gamma'.
    has_type_cases (induction H) Case; intros; auto.
    Case "T_Var".
    apply T_Var. rewrite <- H0...
    Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x0 Hafi.
    unfold  extend. remember (beq_id x x0) as e. destruct e...
    Case "T_App".
    apply T_App with T11...
  Qed.

  Lemma substitution_preserves_typing: forall Gamma x U v t T,
                                         has_type (extend Gamma x U) t T ->
                                         has_type empty v U ->
                                         has_type Gamma (subst v x t) T.
  Proof with eauto.
    intros Gamma x U v t T Ht Hv.
    generalize dependent Gamma.
    generalize dependent T.
    tm_cases(induction t) Case; intros T Gamma H;
    inversion H; subst; simpl...
    Case "tm_var".
    rename i into y. remember (beq_id x y) as e. destruct e.
    SCase "x = y".
    apply beq_id_eq in Heqe. subst.
    rewrite extend_eq in H2. inversion H2; subst. clear H2.
    eapply context_invariance...
    intros x Hcontra.
    destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
    inversion HT'.
    SCase "x <> y".
    apply T_Var. rewrite extend_neq in H2...
    Case "tm_abs".
    rename i into y. apply T_Abs.
    remember (beq_id x y) as e. destruct e.
    SCase "x = y".
    eapply context_invariance...
    apply beq_id_eq in Heqe. subst.
    intros x Hafi. unfold extend.
    destruct (beq_id y x)...
    SCase "x <> y".
    apply IHt. eapply context_invariance...
    intros z Hafi. unfold extend.
    remember (beq_id y z) as e0. destruct e0...
    apply beq_id_eq in Heqe0. subst.
    rewrite <- Heqe...
  Qed.


  Theorem preservation: forall t t' T,
                          has_type empty t T ->
                          t ==> t' ->
                          has_type empty t' T.
  Proof with eauto.
    remember (@empty ty) as Gamma.
    intros t t' T HT.
    generalize dependent t'.
    has_type_cases(induction HT) Case;
      intros t' HE; subst Gamma; subst;
      try solve [inversion HE; subst; auto].
    Case "T_App".
    inversion HE. subst...
    SCase "ST_AppAbs".
    apply substitution_preserves_typing with T11...
    inversion HT1...
    subst. apply T_App with T11.
    apply IHHT1... assumption.
    subst.
    apply T_App with T11.
    assumption.
    apply IHHT2.
    reflexivity.
    assumption.
  Qed.

  Theorem progress: forall t T,
                      has_type empty t T ->
                      value t \/ exists t', t ==> t'.
  Proof with eauto.
    intros t T Ht.
    remember (@empty ty) as Gamma.
    has_type_cases (induction Ht) Case; subst Gamma...
    Case "T_Var".
    inversion H.
    Case "T_App".
    right. destruct IHHt1...
    SCase "t1 is a value".
    destruct IHHt2...
    SSCase "t2 is also a value".
    inversion H; subst. exists (subst t2 x t)...
    solve by inversion. solve by inversion.
    SSCase "t2 steps".
    destruct H0 as [t2' Hstep]. exists (tm_app t1 t2')...
    SCase "t1 steps".
    destruct H as [t1' Hstep]. exists (tm_app t1' t2)...
    Case "T_If".
    right. destruct IHHt1...
    SCase "t1 is a value".
    inversion H; subst. solve by inversion.
    SSCase "t1 = true". eauto.
    SSCase "t1 = false". eauto.
    SCase "t1 also steps".
    destruct H as [t1' Hstep]. exists (tm_if t1' t2 t3)...
  Qed.



  Theorem types_unique: forall Gamma t T1 T2,
                          has_type Gamma t T1 ->
                          has_type Gamma t T2 ->
                          T1 = T2.
  Proof with eauto.
    intros Gamma t.
    generalize dependent Gamma.
    tm_cases(induction t) Case; intros.
    Case "tm_var".
    inversion H. inversion H0. subst.
    remember (Gamma i).
    destruct Heqo.
    destruct o. inversion H3. inversion H7. subst. auto.
    inversion H3.
    Case "tm_app".
    inversion H. inversion H0. subst.
    assert (T11 = T0).
    apply IHt2 with Gamma...
    assert ((ty_arrow T11 T1) = (ty_arrow T0 T2)).
    apply IHt1 with Gamma...
    inversion H2. reflexivity.
    Case "tm_abs".
    inversion H. inversion H0. subst.
    assert (T12 = T3).
    apply IHt with (extend Gamma i t)...
    rewrite H1. reflexivity.
    Case "tm_true".
    inversion H. inversion H0. reflexivity.
    Case "tm_false".
    inversion H. inversion H0. reflexivity.
    inversion H. inversion H0. subst.
    eauto.
  Qed.


  End STLC.