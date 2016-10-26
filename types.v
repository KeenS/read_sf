Require Export Smallstep_J.

Lemma auto_example_1: forall P Q R S T U: Prop,
                        (P -> Q) ->
                        (P -> R) ->
                        (T -> R) ->
                        (S -> T -> U) ->
                        ((P -> Q) -> (P -> S)) ->
                        T ->
                        P ->
                        U.
Proof.
  auto.
Qed.

Hint Constructors refl_step_closure.
Hint Resolve beq_id_eq beq_id_false_not_eq.

Definition astep_many st := refl_step_closure (astep st).
Notation "t '/' st '==>a*' t'" := (astep_many st t t')
                                    (at level 40, st at level 39).

Example astep_example1:
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state ==>a* (ANum 15).
Proof.
  apply rsc_step with (APlus (ANum 3) (ANum 12)).
  apply AS_Plus2.
  apply av_num.
  apply AS_Mult.
  apply rsc_step with (ANum 15).
  apply AS_Plus.
  apply rsc_refl.
Qed.

Hint Constructors astep aval.
Example astep_example1':
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state ==>a* (ANum 15).
Proof.
  eapply rsc_step. auto. simpl.
  eapply rsc_step. auto. simpl.
  apply rsc_refl.
Qed.

Tactic Notation "print_goal" := match goal with |- ?x => idtac x
                                end.
Tactic Notation "normalize" :=
  repeat (print_goal; eapply rsc_step;
          [(eauto 10; fail) | (instantiate; simpl)]);
  apply rsc_refl.

Example astep_example1'':
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state ==>a* (ANum 15).
Proof.
  normalize.
Qed.

Example astep_example1''': exists e',
                             (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
                                                                        ==>a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

Inductive tm : Type :=
| tm_true : tm
| tm_false : tm
| tm_if : tm -> tm -> tm -> tm
| tm_zero : tm
| tm_succ : tm -> tm
| tm_pred : tm -> tm
| tm_iszero : tm -> tm.

Inductive bvalue: tm -> Prop :=
  | bv_true : bvalue tm_true
  | bv_false : bvalue tm_false.

Inductive nvalue : tm -> Prop :=
| nv_zero : nvalue tm_zero
| nv_succ : forall t, nvalue t -> nvalue (tm_succ t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_IFTrue: forall t1 t2,
               (tm_if tm_true t1 t2) ==> t1
| ST_IfFalse : forall t1 t2,
                 (tm_if tm_false t1 t2) ==> t2
| ST_If : forall t1 t1' t2 t3,
            t1 ==> t1' ->
            (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
| ST_Succ: forall t1 t1',
             t1 ==> t1' ->
             (tm_succ t1) ==> (tm_succ t1')
| ST_PredZero :
    (tm_pred tm_zero) ==> tm_zero
| ST_PredSucc : forall t1,
                  nvalue t1 ->
                  (tm_pred (tm_succ t1)) ==> t1
| ST_Pred : forall t1 t1',
              t1 ==> t1' ->
              (tm_pred t1) ==> (tm_pred t1')
| ST_IszeroZero :
    (tm_iszero tm_zero) ==> tm_true
| ST_IszeroSucc : forall t1,
                    nvalue t1 ->
                    (tm_iszero (tm_succ t1)) ==> tm_false
| ST_Iszero : forall t1 t1',
                t1 ==> t1' ->
                (tm_iszero t1) ==> (tm_iszero t1')
where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"
   | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
   | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred"
   | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
   | Case_aux c "ST_Iszero"].

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Definition stuck(t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

Example some_tm_is_stuck:
  exists t, stuck t.
Proof.
  exists (tm_succ tm_true).
  unfold stuck.
  split. 
  unfold normal_form.
  intros contra.
  inversion contra.
  inversion H.
  inversion H1.
  intros contra.
  inversion contra.
  inversion H.
  inversion H.
  inversion H1.
Qed.

Lemma value_is_nf: forall t,
                     value t -> step_normal_form t.
Proof.
  intros t H.
  unfold normal_form.
  intros H1.
  destruct H.
  destruct H.
  inversion H1.
  inversion H.
  inversion H1.
  inversion H.
  induction H.
  inversion H1.
  inversion H.
  apply IHnvalue.
  inversion H1.
  inversion H0.
  exists t1'.
  assumption.
Qed.

Theorem step_deterministic:
  partial_function step.
Proof with eauto.
  unfold partial_function.
  intros x y1 y2 H1.
  generalize dependent y2.
  step_cases(induction H1) Case;intros y2 H2.
  Case "ST_IfTrue".
  inversion H2. reflexivity. inversion H4.
  Case "ST_IfFalse".
  inversion H2. reflexivity. inversion H4.
  Case "ST_If".
  inversion H2.
  subst. inversion H1.
  subst. inversion H1.
  subst. apply IHstep in H5. subst. reflexivity.
  Case "ST_Succ".
  inversion H2. subst. apply IHstep in H0. subst. reflexivity.
  Case "ST_PredZero".
  inversion H2. reflexivity.
  inversion H0.
  Case "ST_PredSucc".
  inversion H2.
  reflexivity.
  inversion H; subst.
  inversion H1. inversion H3.
  inversion H1. inversion H3. subst.
  assert (value t).
  unfold value.
  right.
  apply H4.
  apply value_is_nf in H0.
  unfold normal_form in H0.
  destruct H0.
  exists t1'1.
  apply H7.
  Case "ST_Pred".
  inversion H2; subst.  inversion H1.
  inversion H1.
  assert (value y2).
  unfold value. right. apply H0.
  apply value_is_nf in H5.
  unfold normal_form in H5.
  destruct H5.
  exists t1'0.
  apply H3. apply IHstep in H0. subst. reflexivity.
  Case "ST_IszeroZero".
  inversion H2. reflexivity.
  inversion H0.
  Case "ST_IszeroSucc".
  inversion H2; subst.
  reflexivity.
  inversion H1.
  assert (value t1). unfold value. right. apply H.
  apply value_is_nf in H5.
  unfold normal_form in H5.
  destruct H5.
  exists t1'0. apply H3.
  Case "ST_Iszero".
  inversion H2; subst.
  inversion H1.
  inversion H1.
  assert (value t0). right. apply H0.
  apply value_is_nf in H5.
  unfold normal_form in H5.
  destruct H5.
  exists t1'0.
  apply H3.
  apply IHstep in H0. subst.
  reflexivity.
Qed.

Inductive ty: Type :=
| ty_Bool: ty
| ty_Nat: ty.

Inductive has_type: tm -> ty -> Prop :=
| T_True:
    has_type tm_true ty_Bool
| T_False:
    has_type tm_false ty_Bool
| T_If: forall t1 t2 t3 T,
          has_type t1 ty_Bool ->
          has_type t2 T ->
          has_type t3 T ->
          has_type (tm_if t1 t2 t3) T
| T_Zero:
    has_type tm_zero ty_Nat
| T_Succ: forall t1,
            has_type t1 ty_Nat ->
            has_type (tm_succ t1) ty_Nat
| T_Pred: forall t1,
            has_type t1 ty_Nat ->
            has_type (tm_pred t1) ty_Nat
| T_Iszero: forall t1,
              has_type t1 ty_Nat ->
              has_type (tm_iszero t1) ty_Bool.


Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
    | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
    | Case_aux c "T_Iszero"].

Hint Constructors has_type.


Example has_type_1:
  has_type (tm_if tm_false tm_zero (tm_succ tm_zero)) ty_Nat.
Proof.
  apply T_If.
  apply T_False.
  apply T_Zero.
  apply T_Succ.
  apply T_Zero.
Qed.

Example has_type_not:
  ~ has_type (tm_if tm_false tm_zero tm_true) ty_Bool.
Proof.
  intros Contra. solve by inversion 2.
Qed.

Example succ_hastype_nat_hastype_nat: forall t,
    has_type (tm_succ t) ty_Nat ->
    has_type t ty_Nat.
Proof.
  intros t H.
  inversion H.
  apply H1.
Qed.

Theorem progress: forall t T,
    has_type t T ->
    value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  Case "T_If".
  right. destruct IHHT1.
  SCase "t1 is a value". destruct H.
  SSCase "t1 is a bvalue". destruct H.
  SSSCase "t1 is tm_true".
  exists t2...
  SSSCase "t1 is tm_false".
  exists t3...
  SSCase "t1 is an nvalue".
  solve by inversion 2.
  SCase "t1 can take a step".
  destruct H as [t1' H1].
  exists (tm_if t1' t2 t3)...
  Case "T_Succ".
  destruct IHHT.
  SCase "t1 is a value".
  left.
  unfold value. right.
  unfold value in H.
  destruct H.
  SSCase "t1 is a bvalue".
  inversion H; subst; inversion HT.
  SSCase "t1 is an nvalue".
  apply nv_succ. apply H.
  SCase "t1 can take a step".
  right. destruct H.
  exists (tm_succ x)...
  Case "T_Pred".
  right. destruct IHHT.
  SCase "t1 is a value".
  unfold value in H.
  destruct H.
  SSCase "t1 is a bvalue".
  inversion H; subst; inversion HT.
  SSCase "t1 is a nvalue".
  inversion H. subst.
  exists tm_zero...
  exists t...
  SCase "t1 take a step".
  destruct H.
  exists (tm_pred x)...
  Case "T_Iszero".
  right. destruct IHHT.
  SCase "t1 is a value".
  destruct H.
  SSCase "t1 is a bvalue".
  inversion H; subst; inversion HT.
  SSCase "t1 is a nvalue".
  inversion H.
  exists tm_true...
  exists tm_false...
  SCase "t1 take a step".
  destruct H.
  exists (tm_iszero x)...
Qed.

Theorem preservation: forall t t' T,
    has_type t T ->
    t ==> t' ->
    has_type t' T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case;
    intros t' HE;
    try (solve by inversion).
  Case "T_If"; inversion HE; subst.
  SCase "ST_IFTrue". assumption.
  SCase "ST_IFFalse". assumption.
  SCase "ST_If". apply T_If; try assumption.
  apply IHHT1; assumption.
  Case "T_Succ".
  inversion HE; subst.
  apply IHHT in H0.
  apply T_Succ. apply H0.
  Case "T_Pred".
  inversion HE; subst.
  SCase "t1 is tm_zero".
  apply T_Zero.
  inversion HT.
  SCase "t1 is (tm_succ t')".
  assumption.
  SCase "t1 take a step".
  apply IHHT in H0.
  inversion HE; subst. inversion H1.
  apply T_Pred. assumption.
  Case "T_Iszero".
  inversion HE; subst.
  SCase "t1 is tm_true".
  apply T_True.
  SCase "t1 is tm_false".
  apply T_False.
  SCase "t1 take a step".
  apply IHHT in H0.
  inversion HE; subst.
  apply T_Iszero. assumption.
Qed.

Definition stepmany := (refl_step_closure step).
Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

Corollary soundness : forall t t' T,
    has_type t T ->
    t ==>* t' ->
    ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP. apply (preservation x y T HT H).
  unfold stuck. split; auto.
Qed.

