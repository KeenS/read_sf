Require Export Imp_J.
Require Import Relations.

Inductive tm: Type :=
| tm_const: nat -> tm
| tm_plus: tm -> tm -> tm.


Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "tm_const" | Case_aux c "tm_plus"].

Module SimpleArith0.
  Fixpoint eval (t: tm) : nat :=
    match t with
      | tm_const n => n
      | tm_plus a1 a2 => eval a1 + eval a2
    end.

End SimpleArith0.

Module SimpleArith1.

  Reserved Notation " t '||' n " (at level 50, left associativity).

  Inductive eval: tm -> nat -> Prop :=
  | E_Const: forall n,
               tm_const n || n
  | E_Plus: forall t1 t2 n1 n2,
              t1 || n1 ->
              t2 || n2 ->
              tm_plus t1 t2 || plus n1 n2
  where " t '||' n " := (eval t n).

End SimpleArith1.

Reserved Notation " t '||' t' " (at level 50, left associativity).
Inductive eval: tm -> tm -> Prop :=
| E_Const: forall n1,
             tm_const n1 || tm_const n1
| E_Plus: forall t1 n1 t2 n2,
            t1 || tm_const n1 ->
            t2 || tm_const n2 ->
            tm_plus t1 t2 || tm_const (plus n1 n2)
where " t '||' t' " := (eval t t').

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "E_Const" | Case_aux c "E_Plus"].

Module SimpleArith2.

  Reserved Notation " t '==>' t' " (at level 40).
  Inductive step: tm -> tm -> Prop :=
  | ST_PlusConstConst: forall n1 n2,
                         tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1: forall t1 t1' t2,
                t1 ==> t1' ->
                tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2: forall n1 t2 t2',
                t2 ==> t2' ->
                tm_plus (tm_const n1) t2 ==> tm_plus (tm_const n1) t2'
  where " t '==>' t' " := (step t t').

  Tactic Notation "step_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ST_PlusConstConst"
    | Case_aux c "ST_Plus1"
    | Case_aux c "ST_Plus2"
    ].

  Example test_step_1:
    tm_plus
      (tm_plus (tm_const 0) (tm_const 3))
      (tm_plus (tm_const 2) (tm_const 4))
      ==>
      tm_plus
      (tm_const (plus 0 3))
      (tm_plus (tm_const 2) (tm_const 4)).
  Proof.
    apply ST_Plus1. apply ST_PlusConstConst.
  Qed.

  Example test_step_2:
    tm_plus
      (tm_const 0)
      (tm_plus
         (tm_const 2)
         (tm_plus (tm_const 0) (tm_const 3)))
      ==>
      tm_plus
      (tm_const 0)
      (tm_plus
         (tm_const 2)
         (tm_const (plus 0 3))).
  Proof.
    apply ST_Plus2.
    apply ST_Plus2.
    apply ST_PlusConstConst.
  Qed.

  Theorem step_deterministic:
    partial_function step.
  Proof.
    unfold partial_function. intros x y1 y2 Hy1 Hy2.
    generalize dependent y2.
    step_cases (induction Hy1) Case; intros y2 Hy2.
    Case "ST_PlusConstConst". step_cases (inversion Hy2) SCase.
    SCase "ST_PlusConstConst". reflexivity.
    SCase "ST_Plus1". inversion H2.
    SCase "ST_Plus2". inversion H2.
    Case "ST_Plus1". step_cases (inversion Hy2) SCase.
    SCase "ST_PlusConstConst". rewrite <- H0 in Hy1. inversion Hy1.
    SCase "ST_Plus1". rewrite <- (IHHy1 t1'0). reflexivity. assumption.
    SCase "ST_Plus2". rewrite <- H in Hy1. inversion Hy1.
    Case "ST_Plus2". step_cases (inversion Hy2) SCase.
    SCase "ST_PlusConstConst". rewrite <- H1 in Hy1. inversion Hy1.
    SCase "ST_Plus1". inversion H2.
    SCase "ST_Plus2". rewrite <- (IHHy1 t2'0). reflexivity. assumption.
  Qed.
End SimpleArith2.

Inductive value: tm -> Prop :=
  v_const : forall n, value (tm_const n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst: forall n1 n2,
                        tm_plus (tm_const n1) (tm_const n2)
                                ==> tm_const (plus n1 n2)
| ST_Plus1: forall t1 t1' t2,
              t1 ==> t1' ->
              tm_plus t1 t2 ==> tm_plus t1' t2
| ST_Plus2: forall v1 t2 t2',
              value v1 ->
              t2 ==> t2' ->
              tm_plus v1 t2 ==> tm_plus v1 t2'
where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2"].

Theorem step_deterministic:
  partial_function step.
Proof.
  unfold partial_function.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  step_cases (induction Hy1) Case; intros y2 Hy2.
  Case "ST_PlusConstConst". step_cases (inversion Hy2) SCase.
  SCase "ST_PlusConstConst". reflexivity.
  SCase "ST_Plus1". inversion H2.
  SCase "ST_Plus2". inversion H3.
  Case "ST_Plus1". step_cases (inversion Hy2) SCase.
  SCase "ST_PlusConstConst". rewrite <- H0 in Hy1. inversion Hy1.
  SCase "ST_Plus1".  rewrite <- (IHHy1 t1'0). reflexivity. assumption.
  SCase "ST_Plus2". inversion H1. rewrite <- H4 in Hy1. inversion Hy1.
  Case "ST_Plus2". step_cases (inversion Hy2) SCase.
  SCase "ST_PlusConstConst". rewrite <- H2 in Hy1. inversion Hy1.
  SCase "ST_Plus1". inversion H. rewrite <- H4 in H3. inversion H3.
  SCase "ST_Plus2". rewrite (IHHy1 t2'0). reflexivity. assumption.
Qed.

Theorem strong_progress: forall t, 
                           value t \/ (exists t', t ==> t').
Proof.
  tm_cases (induction t) Case.
  Case "tm_const". left. apply v_const.
  Case "tm_plus". right. inversion IHt1.
  SCase "l". inversion IHt2.
  SSCase "l". inversion H. inversion H0.
  exists (tm_const (plus n n0)). apply ST_PlusConstConst.
  SSCase "r". inversion H0 as [t' H1].
  exists (tm_plus t1 t').
  apply ST_Plus2. apply H. apply H1.
  SCase "r". inversion H as [t' H0].
  exists (tm_plus t' t2).
  apply ST_Plus1. apply H0.
Qed.

Definition normal_form {X:Type} (R: relation X) (t: X): Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf: forall t,
                     value t -> normal_form step t.
Proof.
  unfold normal_form. intros t H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value: forall t,
                     normal_form step t -> value t.
Proof.
  unfold normal_form. intros t H.
  assert (G: value t \/ exists t', t ==> t').
  SCase "Proof of assertion". apply strong_progress.
  inversion G.
  SCase "l". assumption.
  SCase "r". apply ex_falso_quodlibet. apply H. assumption.
Qed.

Corollary nf_same_as_value: forall t,
                              normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

Definition stepmany := refl_step_closure step.

Notation " t '==>*' t'" := (stepmany t t') (at level 40).

Lemma test_stepmany_1:
  tm_plus
    (tm_plus (tm_const 0) (tm_const 3))
    (tm_plus (tm_const 2) (tm_const 4))
    ==>*
    tm_const (plus (plus 0 3) (plus 2 4)).
Proof.
  apply rsc_step with
  (tm_plus
     (tm_const (plus 0 3))
     (tm_plus (tm_const 2) (tm_const 4))).
  apply ST_Plus1. apply ST_PlusConstConst.
  apply rsc_step with
  (tm_plus (tm_const (plus 0 3))
           (tm_const (plus 2 4))).
  apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  apply rsc_R.
  apply ST_PlusConstConst.
Qed.

Lemma test_stepmany_2:
  tm_const 3 ==>* tm_const 3.
Proof.
  apply rsc_refl.
Qed.

Lemma test_stepmany_3:
  tm_plus (tm_const 0) (tm_const 3)
          ==>*
          tm_plus (tm_const 0) (tm_const 3).
Proof.
  apply rsc_refl.
Qed.

Lemma test_stepmany_4:
  tm_plus
    (tm_const 0)
    (tm_plus
       (tm_const 2)
       (tm_plus (tm_const 0)
                (tm_const 3)))
    ==>*
    tm_plus
    (tm_const 0)
    (tm_const (plus 2 (plus 0 3))).
Proof.
  eapply rsc_step.
  apply ST_Plus2. apply v_const.
  apply ST_Plus2. apply v_const. apply ST_PlusConstConst.
  eapply rsc_step. apply ST_Plus2. apply v_const. apply ST_PlusConstConst.
  apply rsc_refl.
Qed.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t': tm) :=
  (t ==>* t' /\ step_normal_form t').

Theorem normal_forms_unique:
  partial_function normal_form_of.
Proof.
  unfold partial_function. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12]. destruct P2 as [P21 P22].
  generalize dependent y2.
  induction P11. intros y2 H1 H2.
  inversion H1. reflexivity.
  unfold step_normal_form in P12.
  unfold normal_form in P12. case P12.
  exists y. assumption.
  intros y2 H1 H2.
  inversion H1. subst. case H2.
  exists y. assumption.
  subst. apply IHP11. assumption.
  destruct x. inversion H.
