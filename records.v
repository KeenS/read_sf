Require Export Stlc_J.
Require Import Relations.

Module STLCExtendedRecords.

  Module FirstTry.
    Definition alist (X: Type) := list (id * X).

    Inductive ty: Type :=
    | ty_base: id -> ty
    | ty_arrow: ty -> ty -> ty
    | ty_rcd: (alist ty) -> ty.

  End FirstTry.



  Inductive ty: Type :=
  | ty_base: id -> ty
  | ty_arrow: ty -> ty -> ty
  | ty_rnil: ty
  | ty_rcons: id -> ty -> ty -> ty.

  Tactic Notation "ty_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ty_base" | Case_aux c "ty_arrow"
      | Case_aux c "ty_rnil" | Case_aux c "ty_rcons" ].


  Inductive tm: Type :=
  | tm_var: id -> tm
  | tm_app: tm -> tm -> tm
  | tm_abs: id -> ty -> tm -> tm
  | tm_proj: tm -> id -> tm
  | tm_rnil: tm
  | tm_rcons: id -> tm -> tm -> tm.

  Tactic Notation "tm_cases" tactic(first) ident(c) :=
    first;
    [Case_aux c "tm_var" | Case_aux c "tm_app" | Case_aux c "tm_abs"
     | Case_aux c "tm_proj" | Case_aux c "tm_rnil" | Case_aux c "tm_rcons"].


  Notation a := (Id 0).
  Notation f := (Id 1).
  Notation g := (Id 2).
  Notation l := (Id 3).
  Notation A := (ty_base (Id 4)).
  Notation B := (ty_base (Id 5)).
  Notation k := (Id 6).
  Notation i1 := (Id 7).
  Notation i2 := (Id 8).

  Check (ty_rcons i1 A ty_rnil).

  Definition weird_type := ty_rcons X A B.


  Inductive record_ty: ty -> Prop :=
  | rty_nil:
      record_ty ty_rnil
  | rty_cons: forall i T1 T2,
      record_ty (ty_rcons i T1 T2).


  Inductive record_tm: tm -> Prop :=
  | rtm_nil:
      record_tm tm_rnil
  | rtm_cons: forall i t1 t2,
      record_tm (tm_rcons i t1 t2).

  Inductive well_formed_ty: ty -> Prop :=
  | wfty_base: forall i,
      well_formed_ty (ty_base i)
  | wfty_arrow: forall T1 T2,
      well_formed_ty T1 ->
      well_formed_ty T2 ->
      well_formed_ty (ty_arrow T1 T2)
  | wfty_rnil:
      well_formed_ty ty_rnil
  | wfty_rcons: forall i T1 T2,
      well_formed_ty T1 ->
      well_formed_ty T2 ->
      record_ty T2 ->
      well_formed_ty (ty_rcons i T1 T2).

  Hint Constructors record_ty record_tm well_formed_ty.

  Fixpoint subst (x:id) (s:tm) (t:tm): tm :=
    match t with
    | tm_var y => if beq_id x y then s else t
    | tm_abs y T t1 => tm_abs y T (if beq_id x y then t1 else (subst x s t1))
    | tm_app t1 t2 => tm_app (subst x s t1) (subst x s t2)
    | tm_proj t1 i => tm_proj (subst x s t1) i
    | tm_rnil => tm_rnil
    | tm_rcons i t1 tr1 => tm_rcons i (subst x s t1) (subst x s tr1)
    end.

  Inductive value: tm -> Prop :=
  | v_abs: forall x T11 t12,
      value (tm_abs x T11 t12)
  | v_rnil: value tm_rnil
  | v_rcons: forall i v1 vr,
      value v1 ->
      value vr ->
      value (tm_rcons i v1 vr).

  Hint Constructors value.

  Fixpoint ty_lookup (i: id) (Tr:ty): option ty :=
    match Tr with
    | ty_rcons i' T Tr' => if beq_id i i' then Some T else ty_lookup i Tr'
    | _ => None
    end.

  Fixpoint tm_lookup (i: id) (tr: tm): option tm :=
    match tr with
    | tm_rcons i' t tr' => if beq_id i i' then Some t else tm_lookup i tr'
    | _ => None
    end.

  Reserved Notation "t1 '==>' t2" (at level 40).

  Inductive step: tm -> tm -> Prop :=
  | ST_AppAbs: forall x T11 t12 v2,
      value v2 ->
      (tm_app (tm_abs x T11 t12) v2) ==> (subst x v2 t12)
  | ST_App1: forall t1 t1' t2,
      t1 ==> t1' ->
      (tm_app t1 t2) ==> (tm_app t1' t2)
  | ST_App2: forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      (tm_app v1 t2) ==> (tm_app v1 t2')
  | ST_Proj1: forall t1 t1' i,
      t1 ==> t1' ->
      (tm_proj t1 i) ==> (tm_proj t1' i)
  | ST_ProjRcd: forall tr i vi,
      value tr ->
      tm_lookup i tr = Some vi ->
      (tm_proj tr i) ==>vi
  | ST_Rcd_Head: forall i t1 t1' tr2,
      t1 ==> t1' ->
      (tm_rcons i t1 tr2) ==> (tm_rcons i t1' tr2)
  | ST_Rcd_Tail: forall i v1 tr2 tr2',
      value v1 ->
      tr2 ==> tr2' ->
      (tm_rcons i v1 tr2) ==> (tm_rcons i v1 tr2')
  where "t1 '==>' t2" := (step t1 t2).


  Tactic Notation "step_cases" tactic(first) ident(c) :=
    first;
    [Case_aux c "ST_AppAbs"; Case_aux c "ST_App1" | Case_aux c "ST_App2"
     | Case_aux c "ST_Proj1" | Case_aux c "ST_ProjRcd"
     | Case_aux c "ST_Rcd_Head" | Case_aux c "ST_Rcd_Tail"].

  Notation stepmany := (refl_step_closure step).
  Notation "t1 '==>*' t2" :=(stepmany t1 t2) (at level 40).

  Hint Constructors step.


  Definition context := partial_map ty.

  
  Inductive has_type: context -> tm -> ty -> Prop :=
  | T_Var: forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      has_type Gamma (tm_var x) T
  | T_Abs: forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      has_type (extend Gamma x T11) t12 T12 ->
      has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App: forall T1 T2 Gamma t1 t2,
      has_type Gamma t1 (ty_arrow T1 T2) ->
      has_type Gamma t2 T1 ->
      has_type Gamma (tm_app t1 t2) T2
  | T_Proj: forall Gamma i t Ti Tr,
      has_type Gamma t Tr ->
      ty_lookup i Tr = Some Ti ->
      has_type Gamma (tm_proj t i) Ti
  | T_RNil: forall Gamma,
      has_type Gamma tm_rnil ty_rnil
  | T_RCons: forall Gamma i t T tr Tr,
      has_type Gamma t T ->
      has_type Gamma tr Tr ->
      record_ty Tr ->
      record_tm tr ->
      has_type Gamma (tm_rcons i t tr) (ty_rcons i T Tr).

  Hint Constructors has_type.
  Tactic Notation "has_type_cases" tactic(first) ident(c) :=
    first;
    [Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
     | Case_aux c "T_Proj" | Case_aux c "T_RNil" | Case_aux c "T_RCons"].

  Lemma typing_example_2:
    has_type empty
             (tm_app (tm_abs a (ty_rcons i1 (ty_arrow A A)
                                         (ty_rcons i2 (ty_arrow B B)
                                                   ty_rnil))
                             (tm_proj (tm_var a) i2))
                     (tm_rcons i1 (tm_abs a A (tm_var a))
                               (tm_rcons i2 (tm_abs a B (tm_var a))
                                         tm_rnil)))
             (ty_arrow B B).
  Proof.
    apply T_App with (ty_rcons i1 (ty_arrow A A)
                               (ty_rcons i2 (ty_arrow B B)
                                         ty_rnil))
    ;auto.
    apply T_Abs; auto.
    apply T_Proj with (ty_rcons i1 (ty_arrow A A)
                                (ty_rcons i2 (ty_arrow B B)
                                          ty_rnil))
    ;auto.
  Qed.

  Example typing_nonexample:
    ~ exists T,
        has_type (extend empty a (ty_rcons i2 (ty_arrow A A)
                                           ty_rnil))
                 (tm_rcons i1 (tm_abs a B (tm_var a)) (tm_var a))
                 T.
  Proof.
    intro contra.
    destruct contra.
    inversion H.
    subst.
    clear H.
    inversion H3.
    subst. clear H3.
    inversion H5.
    subst.
    inversion H8.
  Qed.

  Example typing_nonexample_2: forall y,
      ~ exists T,
          has_type (extend empty y A)
                   (tm_app (tm_abs a (ty_rcons i1 A ty_rnil)
                                   (tm_proj (tm_var a) i1))
                           (tm_rcons i1 (tm_var y) (tm_rcons i2 (tm_var y) tm_rnil)))
                   T.
  Proof.
    intros y contra.
    destruct contra.
    inversion H. subst. clear H.
    inversion H5. subst. clear H5.
    inversion H3. subst. clear H3.
    inversion H6.
  Qed.


  Lemma wf_rcd_lookup: forall i T Ti,
      well_formed_ty T ->
      ty_lookup i T = Some Ti ->
      well_formed_ty Ti.
  Proof with eauto.
    intros i T.
    ty_cases (induction T) Case; intros; try solve by inversion.
    Case "ty_rcons".
    inversion H. subst. unfold ty_lookup in H0.
    remember (beq_id i i0) as b. destruct b; subst...
    inversion H0. subst...
  Qed.


  Lemma step_preserves_record_tm: forall tr tr',
      record_tm tr ->
      tr ==> tr' ->
      record_tm tr'.
  Proof.
    intros tr tr' Htr Hstp.
    inversion Htr; subst; inversion Hstp; subst; auto.
  Qed.


  Lemma has_type__wf: forall Gamma t T,
      has_type Gamma t T -> well_formed_ty T.
  Proof with eauto.
    intros Gamma t T Htyp.
    has_type_cases (induction Htyp) Case...
    Case "T_App".
      inversion IHHtyp1...
    Case "T_Proj".
      eapply wf_rcd_lookup...
  Qed.


  Lemma lookup_field_in_value: forall v T i Ti,
      value v ->
      has_type empty v T ->
      ty_lookup i T = Some Ti ->
      exists ti, tm_lookup i v = Some ti /\ has_type empty ti Ti.
  Proof with eauto.
    intros v T i Ti Hval Htyp Hget.
    remember (@empty ty) as Gamma.
    has_type_cases (induction Htyp) Case; subst; try solve by inversion...
    Case "T_RCons".
      simpl in Hget. simpl. destruct (beq_id i i0).
      SCase "i is first".
        simpl. inversion Hget. subst.
        exists t...
      SCase "get tail".
        destruct IHHtyp2 as [vi [Hgeti Htypi]]...
        inversion Hval...
  Qed.


  Theorem progress: forall t T,
      has_type empty t T ->
      value t \/ exists t', t ==> t'.
  Proof with eauto.
    intros t T Ht.
    remember (@empty ty) as Gamma.
    generalize dependent HeqGamma.
    has_type_cases (induction Ht) Case; intros HeqGamma; subst.
    Case "T_Var".
      inversion H.
    Case "T_Abs".
      left...
    Case "T_App".
      right.
      destruct IHHt1; subst...
      SCase "t1 is a value".
        destruct IHHt2; subst...
        SSCase "t2 is a value".
          inversion H; subst; try (solve by inversion).
          exists (subst x t2 t12)...
        SSCase "t2 steps".
          destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...
      SCase "t1 steps".
        destruct H as [t1' Tstp]. exists (tm_app t1' t2)...
    Case "T_Proj".
      right. destruct IHHt...
      SCase "rcd is value".
        destruct (lookup_field_in_value _ _ _ _ H0 Ht H) as [ti [Hlkup _]].
        exists ti...
      SCase "rcd_steps".
        destruct H0 as [t' Hstp]. exists (tm_proj t' i)...
    Case "T_RNil".
      left...
    Case "T_RCons".
      destruct IHHt1...
      SCase "head is a value".
        destruct IHHt2; try reflexivity.
        SSCase "tail is a value".
          left...
        SSCase "tail steps".
          right. destruct H2 as [tr' Hstp].
          exists (tm_rcons i t tr')...
      SCase "head steps".
        right. destruct H1 as [t' Hstp].
        exists (tm_rcons i t' tr)...
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
  | afi_proj: forall x t i,
      appears_free_in x t ->
      appears_free_in x (tm_proj t i)
  | afi_rhead: forall x i ti tr,
      appears_free_in x ti ->
      appears_free_in x (tm_rcons i ti tr)
  | afi_rtail: forall x i ti tr,
      appears_free_in x tr ->
      appears_free_in x (tm_rcons i ti tr).

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
      apply T_Abs... apply IHhas_type. intros y Hafi.
      unfold extend. remember (beq_id x y) as e.
      destruct e...
    Case "T_App".
      apply T_App with T1...
    Case "T_RCons".
      apply T_RCons...
  Qed.


  Lemma free_in_context: forall x t T Gamma,
      appears_free_in x t ->
      has_type Gamma t T ->
      exists T', Gamma x = Some T'.
  Proof with eauto.
    intros x t T Gamma Hafi Htyp.
    has_type_cases (induction Htyp) Case; inversion Hafi; subst...
    Case "T_Abs".
      destruct IHHtyp as [T' Hctx]... exists T'.
      unfold extend in Hctx.
      apply not_eq_beq_id_false in H3. rewrite H3 in Hctx...
  Qed.


  Lemma substitution_preserves_typing: forall Gamma x U v t S,
      has_type (extend Gamma x U) t S ->
      has_type empty v U ->
      has_type Gamma (subst x v t) S.
  Proof with eauto.
    intros Gamma x U v t S Htypt Htypv.
    generalize dependent Gamma. generalize dependent S.
    tm_cases (induction t) Case;
      intros S Gamma Htypt; simpl; inversion Htypt; subst...
    Case "tm_var".
      simpl. rename i into y.
      remember (beq_id x y) as e. destruct e.
      SCase "x = y".
        apply beq_id_eq in Heqe. subst.
        unfold extend in H0. rewrite <- beq_id_refl in H0.
        inversion H0; subst. clear H0.
        eapply context_invariance...
        intros x Hcontra.
        destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
        inversion HT'.
      SCase "x <> y".
        apply T_Var... unfold extend in H0. rewrite <- Heqe in H0...
    Case "tm_abs".
      rename i into y. rename t into T11.
      apply T_Abs...
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
    Case "tm_rcons".
      apply T_RCons... inversion H7; subst; simpl...
  Qed.

  Theorem preservation: forall t t' T,
      has_type empty t T ->
      t ==> t' ->
      has_type empty t' T.
  Proof with eauto.
    intros t t' T HT.
    remember (@empty ty) as Gamma. generalize dependent HeqGamma.
    generalize dependent t'.
    has_type_cases (induction HT) Case;
      intros t' HeqGamma HE; subst; inversion HE; subst...
    Case "T_App".
      inversion HE; subst...
      SCase "ST_AppAbs".
      apply substitution_preserves_typing with T1...
      inversion HT1...
    Case "T_Proj".
      destruct (lookup_field_in_value _ _ _ _ H2 HT H) as [vi [Hget Htyp]].
      rewrite H4 in Hget. inversion Hget. subst...
    Case "T_RCons".
      apply T_RCons... eapply step_preserves_record_tm...
  Qed.

End STLCExtendedRecords.