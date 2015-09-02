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
  subst.
Admitted.

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


