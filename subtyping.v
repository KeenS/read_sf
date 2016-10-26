Require Export MoreStlc_J.

Inductive ty: Type :=
| ty_Top: ty
| ty_Bool: ty
| ty_base: id -> ty
| ty_arrow: ty -> ty -> ty
| ty_Unit: ty
.

Tactic Notation "ty_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "ty_Top" | Case_aux c "ty_Bool"
   | Case_aux c "ty_base" | Case_aux c "ty_arrow"
   | Case_aux c "ty_Unit" |
  ].

Inductive tm: Type :=
| tm_var: id -> tm
| tm_app: tm -> tm -> tm
| tm_abs: id -> ty -> tm -> tm
| tm_true: tm
| tm_false: tm
| tm_if: tm -> tm -> tm -> tm
| tm_unit: tm
.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_var" | Case_aux c "tm_app"
    | Case_aux c "tm_abs" | Case_aux c "tm_true"
    | Case_aux c "tm_false" | Case_aux c "tm_if"
    | Case_aux c "tm_unit"
  ].

Fixpoint subst (s: tm) (x: id) (t: tm): tm :=
  match t with
  | tm_var y =>
    if beq_id x y then s else t
  | tm_abs y T t1 =>
    tm_abs y T (if beq_id x y then t1 else (subst s x t1))
  | tm_app t1 t2 =>
    tm_app (subst s x t1) (subst s x t2)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst s x t1) (subst s x t2) (subst s x t3)

  | tm_unit => tm_unit
  end.


Inductive value: tm -> Prop :=
| v_abs: forall x T t,
    value (tm_abs x T t)
| t_true:
    value tm_true
| t_false_:
    value tm_false
| v_unit:
    value tm_unit
.

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step: tm -> tm -> Prop :=
| ST_AppAbs: forall x T t12 v2,
    value v2 ->
    (tm_app (tm_abs x T t12) v2) ==> (subst v2 x t12)
| ST_App1: forall t1 t1' t2,
    t1 ==> t1' ->
    (tm_app t1 t2) ==> (tm_app t1' t2)
| ST_App2: forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    (tm_app v1 t2) ==> (tm_app v1 t2')
| ST_IfTrue: forall t1 t2,
    (tm_if tm_true t1 t2) ==> t2
| ST_IfFalse: forall t1 t2,
    (tm_if tm_false t1 t2) ==> t2
| ST_If: forall t1 t1' t2 t3,
    t1 ==> t1' ->
    (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
where "t1 '==>' t2" := (step t1 t2).


Tactic Notation "step_cases" tactic(first) ident(c):=
  first;
  [Case_aux c "ST_AppAbs" | Case_aux c "ST_App1"
   | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue"
   | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"]
.

Hint Constructors step.

Inductive subtype: ty -> ty -> Prop :=
| S_Refl: forall T,
    subtype T T
| S_Trans: forall S U T,
    subtype S U ->
    subtype U T ->
    subtype S T
| S_Top: forall S,
    subtype S ty_Top
| S_Arrow: forall S1 S2 T1 T2,
    subtype T1 S1 ->
    subtype S2 T2 ->
    subtype (ty_arrow S1 S2) (ty_arrow T1 T2)
.

Hint Constructors subtype.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "S_Refl" | Case_aux c "S_Trans"
   | Case_aux c "S_Top" | Case_aux c "S_Arrow"]
.

Module Examples.
  Notation x := (Id 0).
  Notation y := (Id 1).
  Notation z := (Id 2).

  Notation A := (ty_base (Id 6)).
  Notation B := (ty_base (Id 7)).
  Notation C := (ty_base (Id 8)).

  Notation String := (ty_base (Id 9)).
  Notation Float := (ty_base (Id 10)).
  Notation Integer := (ty_base (Id 11)).

End Examples.


Definition context := id -> (option ty).
Definition empty: context := (fun _ => None).
Definition extend (Gamma: context) (x: id) (T: ty) := fun x' => if beq_id x x' then Some T else Gamma x'.

Inductive has_type: context -> tm -> ty -> Prop :=
| T_Var: forall Gamma x T,
    Gamma x = Some T ->
    has_type Gamma (tm_var x) T
| T_Abs: forall Gamma x T11 T12 t12,
    has_type (extend Gamma x T11) t12 T12 ->
    has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
| T_App: forall T1 T2 Gamma t1 t2,
    has_type Gamma t1 (ty_arrow T1 T2) ->
    has_type Gamma t2 T1 ->
    has_type Gamma (tm_app t1 t2) T2
| T_True: forall Gamma,
    has_type Gamma tm_true ty_Bool
| T_False: forall Gamma,
    has_type Gamma tm_false ty_Bool
| T_If: forall t1 t2 t3 T Gamma,
    has_type Gamma t1 ty_Bool ->
    has_type Gamma t2 T ->
    has_type Gamma t3 T ->
    has_type Gamma (tm_if t1 t2 t3) T
| T_Unit: forall Gamma,
    has_type Gamma tm_unit ty_Unit
| T_Sub: forall Gamma t S T,
    has_type Gamma t S ->
    subtype S T ->
    has_type Gamma t T.

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs"
    | Case_aux c "T_App" | Case_aux c "T_True"
    | Case_aux c "T_False" | Case_aux c "T_If"
    | Case_aux c "T_Unit"
    | Case_aux c "T_Sub"].


Lemma sub_inversion_Bool: forall U,
    subtype U ty_Bool ->
    U = ty_Bool.
Proof with auto.
  intros U Hs.
  remember ty_Bool as V.
  subtype_cases(induction Hs) Case.
  Case "S_Refl".
  reflexivity.
  Case "S_Trans".
  subst.
  assert (U = ty_Bool).
  apply IHHs2. reflexivity. subst.
  apply IHHs1. reflexivity.
  Case "S_Top".
  inversion HeqV.
  Case "S_Arrow".
  inversion HeqV.
Qed.

Lemma sub_inversion_arrow: forall U V1 V2,
    subtype U (ty_arrow V1 V2) ->
    exists U1, exists U2,
        U = (ty_arrow U1 U2) /\ (subtype V1 U1) /\ (subtype U2 V2).
Proof with eauto.
  intros U V1 V2 Hs.
  remember (ty_arrow V1 V2) as V.
  generalize dependent V2.
  generalize dependent V1.
  subtype_cases(induction Hs) Case; intros V1 V2 Hs.
  Case "S_Refl".
  exists V1. exists V2.
  split.
  assumption.
  split.
  apply S_Refl.
  apply S_Refl.
  Case "S_Trans".
  apply IHHs2 in Hs.
  destruct Hs as [U1 Hs].
  destruct Hs as [U2 Hs].
  destruct Hs as [Harr Hs].
  destruct Hs as [Hs3 Hs4].
  apply IHHs1 in Harr.
  destruct Harr as [U0 Harr].
  destruct Harr as [U3 Harr].
  destruct Harr.
  destruct H0.
  exists U0.
  exists U3.
  split.
  assumption.
  split.
  apply S_Trans with U1...
  apply S_Trans with U2...
  Case "S_Top".
  inversion Hs.
  Case "S_Arrow".
  inversion Hs.
  subst.
  exists S1.
  exists S2.
  split...
Qed.

Lemma canonical_forms_of_arrow_types: forall Gamma s T1 T2,
    has_type Gamma s (ty_arrow T1 T2) ->
    value s ->
    exists x, exists S1, exists s2,
          s = tm_abs x S1 s2.
Proof with eauto.
  intros Gamma s T1 T2 H Hv.
  remember (ty_arrow T1 T2).
  generalize dependent T1.
  generalize dependent T2.
  has_type_cases(induction H) Case; intros T2' T1' Hty; try (solve by inversion)...
  Case "T_Sub".
  subst.
  apply sub_inversion_arrow in H0.
  destruct H0. destruct H0. destruct H0. destruct H1.
  apply IHhas_type with (T2 := x0) (T1 := x)...
Qed.

Lemma canonical_forms_of_Bool: forall Gamma s,
    has_type Gamma s ty_Bool ->
    value s ->
    (s = tm_true \/ s = tm_false).
Proof with eauto.
  intros Gamma s Hty Hv.
  remember ty_Bool as T.
  has_type_cases (induction Hty) Case; try solve by inversion...
  Case "T_Sub".
  subst.
  apply sub_inversion_Bool in H.
  subst...
Qed.

Theorem progress: forall t T,
    has_type empty t T ->
    value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  has_type_cases (induction Ht) Case;
    intros HeqGamma; subst...
  Case "T_Var".
  inversion H.
  Case "T_App".
  right.
  destruct IHHt1; subst...
  SCase "t1 is a value".
  destruct IHHt2; subst...
  SSCase "t2 is a value".
  destruct (canonical_forms_of_arrow_types empty t1 T1 T2) as [x [S1 [t12 Heqt1]]]...
  subst. exists (subst t2 x t12)...
  SSCase "t2 steps".
  destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...
  SCase "t1 steps".
  destruct H as [t1' Hstp]. exists (tm_app t1' t2)...
  Case "T_If".
  right.
  destruct IHHt1...
  SCase "t1 is a value".
  assert (t1 = tm_true \/ t1 = tm_false) by (eapply canonical_forms_of_Bool; eauto).
  inversion H0; subst...
  SCase "t1 steps".
  destruct H. rename x into t1'. eauto.
Qed.

Lemma typing_inversion_abs: forall Gamma x S1 t2 T,
    has_type Gamma (tm_abs x S1 t2) T ->
    (exists S2, subtype (ty_arrow S1 S2) T /\ has_type (extend Gamma x S1) t2 S2).
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember (tm_abs x S1 t2) as t.
  has_type_cases (induction H) Case; inversion Heqt; subst; intros; try solve by inversion.
  Case "T_Abs".
  exists T12 ...
  Case "T_Sub".
  destruct IHhas_type as [S2 [Hsub Hty]]...
Qed.

Lemma typing_inversion_var: forall Gamma x T,
    has_type Gamma (tm_var x) T ->
    exists S, Gamma x = Some S /\ subtype S T.
Proof with eauto.
  intros Gamma x T Hty.
  remember (tm_var x) as t.
  has_type_cases (induction Hty) Case; inversion Heqt; subst; intros; try solve by inversion.
  Case "T_Var".
  exists T ...
  Case "T_Sub".
  destruct IHHty as [S2 [Hctxt HsubU]]...
Qed.


Lemma typing_inversion_app: forall Gamma t1 t2 T2,
    has_type Gamma (tm_app t1 t2) T2 ->
    exists T1,
      has_type Gamma t1 (ty_arrow T1 T2) /\
      has_type Gamma t2 T1.
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember (tm_app t1 t2) as t.
  has_type_cases (induction Hty) Case; inversion Heqt; subst; intros; try solve by inversion.
  Case "T_App".
  exists T1 ...
  Case "T_Sub".
  destruct IHHty as [S2 [Hty1 Hty2]]...
Qed.

Lemma typing_inversion_true: forall Gamma T,
    has_type Gamma tm_true T ->
    subtype ty_Bool T.
Proof with eauto.
  intros Gamma T Htyp.
  remember tm_true as tu.
  has_type_cases (induction Htyp) Case; inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_false: forall Gamma T,
    has_type Gamma tm_false T ->
    subtype ty_Bool T.
Proof with eauto.
  intros Gamma T Htyp.
  remember tm_false as tu.
  has_type_cases (induction Htyp) Case; inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_if: forall Gamma t1 t2 t3 T,
    has_type Gamma (tm_if t1 t2 t3) T ->
    has_type Gamma t1 ty_Bool
    /\ has_type Gamma t2 T
    /\ has_type Gamma t3 T.
Proof with eauto.
  intros Gamma t1 t2 t3 T Hty.
  remember (tm_if t1 t2 t3) as t.
  has_type_cases (induction Hty) Case; intros;
    inversion Heqt; subst; try solve by inversion.
  Case "T_If"...
  Case "T_Sub".
  destruct (IHHty H0) as [H1 [H2 H3]]...
Qed.

Lemma typing_inversion_unit: forall Gamma T,
    has_type Gamma tm_unit T ->
    subtype ty_Unit T.
Proof with eauto.
  intros Gamma T Htyp. remember tm_unit as tu.
  has_type_cases (induction Htyp) Case;
    inversion Heqtu; subst; intros...
Qed.

Lemma abs_arrow: forall x S1 s2 T1 T2,
    has_type empty (tm_abs x S1 s2) (ty_arrow T1 T2) ->
    subtype T1 S1
    /\ has_type (extend empty x S1) s2 T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst...
Qed.

Inductive appears_free_in: id -> tm -> Prop :=
| afi_var: forall x,
    appears_free_in x (tm_var x)
| afi_app1: forall x t1 t2,
    appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
| afi_app2: forall x t1 t2,
    appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
| afi_abs: forall x y T11 t12,
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
    appears_free_in x (tm_if t1 t2 t3)
.

Hint Constructors appears_free_in.


Lemma context_invariance: forall Gamma Gamma' t S,
    has_type Gamma t S ->
    (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
    has_type Gamma' t S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  has_type_cases (induction H) Case;
    intros Gamma' Heqv...
  Case "T_Var".
  apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
  apply T_Abs... apply IHhas_type. intros x0 Hafi.
  unfold extend. remember (beq_id x x0) as e.
  destruct e...
  Case "T_App".
  apply T_App with T1...
  Case "T_If".
  apply T_If...
Qed.

Lemma free_in_context: forall x t T Gamma,
    appears_free_in x t ->
    has_type Gamma t T ->
    exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case;
    subst; inversion Hafi; subst...
  Case "T_Abs".
  destruct (IHHtyp H4) as [T Hctx]. exists T.
  unfold extend in Hctx. apply not_eq_beq_id_false in H2.
  rewrite H2 in Hctx...
Qed.

Lemma substitution_preserves_typing: forall Gamma x U v t S,
    has_type (extend Gamma x U) t S ->
    has_type empty v U ->
    has_type Gamma (subst v x t) S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S.
  generalize dependent Gamma.
  tm_cases (induction t) Case; intros; simpl.
  Case "tm_var".
  rename i into y.
  destruct (typing_inversion_var _ _ _ Htypt)
           as [T [Hctx Hsub]].
  unfold extend in Hctx.
  remember (beq_id x y) as e. destruct e...
  SCase "x = y".
  apply beq_id_eq in Heqe. subst.
  inversion Hctx; subst. clear Hctx.
  apply context_invariance with empty...
  intros x Hcontra.
  destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
  inversion HT'.
  Case "tm_app".
  destruct (typing_inversion_app _ _ _ _ Htypt) as [T1 [Htypt1 Htypt2]].
  eapply T_App...
  Case "tm_abs".
  rename i into y. rename t into T1.
  destruct (typing_inversion_abs _ _ _ _ _ Htypt) as [T2 [Hsub Htypt2]].
  apply T_Sub with (ty_arrow T1 T2)... apply T_Abs...
  remember (beq_id x y) as e. destruct e.
  SCase "x=y".
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
  Case "tm_true".
  assert (subtype ty_Bool S)
    by apply (typing_inversion_true _ _ Htypt)...
  Case "tm_false".
  assert (subtype ty_Bool S)
    by apply (typing_inversion_false _ _ Htypt)...
  case "tm_if".
  assert (has_type (extend Gamma x U) t1 ty_Bool
          /\ has_type (extend Gamma x U) t2 S
          /\ has_type (extend Gamma x U) t3 S)
    by apply (typing_inversion_if _ _ _ _ _ Htypt).
  destruct H as [H1 [H2 H3]].
  apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
  auto.
  Case "tm_unit".
  assert (subtype ty_Unit S)
    by apply (typing_inversion_unit _ _ Htypt)...
Qed.


Theorem preservation: forall t t' T,
    has_type empty t T ->
    t ==> t' ->
    has_type empty t' T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  generalize dependent t'.
  has_type_cases (induction HT) Case;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
  inversion HE; subst...
  SCase "ST_AppAbs".
  destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
  apply substitution_preserves_typing with T...
Qed.