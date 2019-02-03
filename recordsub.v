Require Export MoreStlc_J.

Inductive ty: Type :=
| ty_Top: ty
| ty_base: id -> ty
| ty_arrow: ty -> ty -> ty
| ty_rnil: ty
| ty_rcons: id -> ty -> ty -> ty.

Tactic Notation "ty_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "ty_Top" | Case_aux c "ty_base" | Case_aux c "ty_arrow"
   | Case_aux c "ty_rnil" | Case_aux c "ty_rcons"].

Inductive tm: Type :=
| tm_var: id -> tm
| tm_app: tm -> tm -> tm
| tm_abs: id -> ty -> tm -> tm
| tm_proj: tm -> id -> tm
| tm_rnil: tm
| tm_rcons: id -> tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "tm_var" | Case_aux c "tm_app" | Case_aux c "tm_abs" | Case_aux c "tm_proj" | Case_aux c "tm_rnil" | Case_aux c "tm_rcons"].

Inductive record_ty: ty -> Prop :=
| rty_nil:
    record_ty ty_rnil
| rty_cons: forall i T1 T2,
    record_ty (ty_rcons i T1 T2).

Inductive record_tm: tm -> Prop :=
| rtm_nil: record_tm tm_rnil
| rtm_cons: forall i t1 t2,
    record_tm (tm_rcons i t1 t2).

Inductive well_formed_ty: ty -> Prop :=
| wfty_Top:
    well_formed_ty ty_Top
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
  | tm_rcons i t1 tr2 => tm_rcons i (subst x s t1) (subst x s tr2)
  end.


Inductive value: tm -> Prop :=
| v_abs: forall x T t,
    value (tm_abs x T t)
| v_rnil: value tm_rnil
| v_rcons: forall i v vr,
    value v ->
    value vr ->
    value (tm_rcons i v vr).

Hint Constructors value.

Fixpoint ty_lookup (i:id) (Tr:ty): option ty :=
  match Tr with
  | ty_rcons i' T Tr' => if beq_id i i' then Some T else ty_lookup i Tr'
  | _ => None
  end.

Fixpoint tm_lookup (i:id) (tr:tm): option tm :=
  match tr with
  | tm_rcons i' t tr' => if beq_id i i' then Some t else tm_lookup i tr'
  | _ => None
  end.


Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step: tm -> tm -> Prop :=
| ST_AppAbs: forall x T t12 v2,
    value v2 ->
    (tm_app (tm_abs x T t12) v2) ==> (subst x v2 t12)
| ST_App1: forall t1 t1' t2,
    t1 ==> t1' ->
    (tm_app t1 t2) ==> (tm_app t1' t2)
| ST_App2: forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    (tm_app v1 t2) ==> (tm_app v1 t2')
| ST_Proj1: forall tr tr' i,
    tr ==> tr' ->
    (tm_proj tr i) ==> (tm_proj tr' i)
| ST_ProjRcd: forall tr i vi,
    value tr ->
    tm_lookup i tr = Some vi ->
    (tm_proj tr i) ==> vi
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
  [Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2" | Case_aux c "ST_Proj1" | Case_aux c "ST_ProjRcd" | Case_aux c "ST_Rcd" | Case_aux c "ST_Rcd_Head" | Case_aux c "ST_Rcd_Tail"].

Hint Constructors step.

Inductive subtype: ty -> ty -> Prop :=
| S_Refl: forall T,
    well_formed_ty T ->
    subtype T T
| S_Trans: forall S U T,
    subtype S U ->
    subtype U T ->
    subtype S T
| S_Top: forall S,
    well_formed_ty S ->
    subtype S ty_Top
| S_Arrow: forall S1 S2 T1 T2,
    subtype T1 S1 ->
    subtype S2 T2 ->
    subtype (ty_arrow S1 S2) (ty_arrow T1 T2)
| S_RcdWidth: forall i T1 T2,
    well_formed_ty (ty_rcons i T1 T2) ->
    subtype (ty_rcons i T1 T2) ty_rnil
| S_RcdDepth: forall i S1 T1 Sr2 Tr2,
    subtype S1 T1 ->
    subtype Sr2 Tr2 ->
    record_ty Sr2 ->
    record_ty Tr2 ->
    subtype (ty_rcons i S1 Sr2) (ty_rcons i T1 Tr2)
| S_RcdPerm: forall i1 i2 T1 T2 Tr3,
    well_formed_ty (ty_rcons i1 T1 (ty_rcons i2 T2 Tr3)) ->
    i1 <> i2 ->
    subtype (ty_rcons i1 T1 (ty_rcons i2 T2 Tr3))
            (ty_rcons i2 T2 (ty_rcons i1 T1 Tr3)).

Hint Constructors subtype.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "S_Refl" | Case_aux c "S_Trans" | Case_aux c "S_Top"
    | Case_aux c "S_Arrow" | Case_aux c "S_RcdWidth" | Case_aux c "S_RcdDepth" | Case_aux c "S_RcdPerm"].


Module Examples.
  Notation x := (Id 0).
  Notation y := (Id 1).
  Notation z := (Id 2).
  Notation j := (Id 3).
  Notation k := (Id 4).
  Notation i := (Id 5).
  Notation A := (ty_base (Id 6)).
  Notation B := (ty_base (Id 7)).
  Notation C := (ty_base (Id 8)).

  Definition ty_rcd_j :=
    (ty_rcons j (ty_arrow B B) ty_rnil).
  Definition ty_rcd_kj :=
    ty_rcons k (ty_arrow A A) ty_rcd_j.

  Example subtyping_example_0:
    subtype (ty_arrow C ty_rcd_kj)
            (ty_arrow C ty_rnil).
  Proof.
    apply S_Arrow.
    + apply S_Refl. auto.
    + unfold ty_rcd_kj, ty_rcd_j.
      apply S_RcdWidth; auto.
  Qed.

  Example subtyping_example_1:
    subtype ty_rcd_kj ty_rcd_j.
  Proof with eauto.
    unfold ty_rcd_kj, ty_rcd_j.
    apply S_Trans with (U := (ty_rcons j (ty_arrow B B) (ty_rcons k (ty_arrow A A) ty_rnil))).
    + apply S_RcdPerm...
    + apply S_RcdDepth...
  Qed.

  Example subtyping_example_3:
    subtype (ty_arrow ty_rnil (ty_rcons j A ty_rnil))
            (ty_arrow (ty_rcons k B ty_rnil) ty_rnil).
  Proof with eauto.
    apply S_Arrow...
  Qed.

  Example subtyping_example_4:
    subtype (ty_rcons x A (ty_rcons y B (ty_rcons z C ty_rnil)))
            (ty_rcons z C (ty_rcons y B (ty_rcons x A ty_rnil))).
  Proof with eauto.
    apply S_Trans with (U := (ty_rcons x A (ty_rcons z C (ty_rcons y B ty_rnil)))).
    + apply S_RcdDepth...
    + apply S_Trans with (U := (ty_rcons z C (ty_rcons x A (ty_rcons y B ty_rnil)))).
      * apply S_RcdPerm...
      * apply S_RcdDepth...
  Qed.

  Definition tm_rcd_kj :=
    (tm_rcons k (tm_abs z A (tm_var z))
              (tm_rcons j (tm_abs z B (tm_var z))
                        tm_rnil)).

End Examples.

Lemma subtype_wf: forall S T,
    subtype S T ->
    well_formed_ty T /\ well_formed_ty S.
Proof with eauto.
  intros S T Hsub.
  subtype_cases (induction Hsub) Case;
    intros; try (destruct IHHsub1; destruct IHHsub2)...
  Case "S_RcdPerm".
  split... inversion H.
  subst. inversion H5...
Qed.

Lemma wf_rcd_lookup: forall i T Ti,
    well_formed_ty T ->
    ty_lookup i T = Some Ti ->
    well_formed_ty Ti.
Proof with eauto.
  intros I T.
  ty_cases (induction T) Case; intros; try solve by inversion.
  Case "ty_rcons".
  inversion H. subst. unfold ty_lookup in H0.
  remember (beq_id I i) as b.
  destruct b; subst...
  inversion H0. subst...
Qed.

Lemma rcd_types_match: forall S T i Ti,
    subtype S T ->
    ty_lookup i T = Some Ti ->
    exists Si, ty_lookup i S = Some Si /\ subtype Si Ti.
Proof with (eauto using wf_rcd_lookup).
  intros S T i Ti Hsub Hget.
  generalize dependent Ti.
  subtype_cases (induction Hsub) Case; intros Ti Hget;
    try solve by inversion.
  Case "S_Refl".
  exists Ti...
  Case "S_Trans".
  destruct (IHHsub2 Ti) as [Ui Hui]... destruct Hui.
  destruct (IHHsub1 Ui) as [Si Hsi]... destruct Hsi.
  exists Si...
  Case "S_RcdDepth".
  rename i0 into k.
  unfold ty_lookup. unfold ty_lookup in Hget.
  remember (beq_id i k) as b. destruct b...
  SCase "i = k -- we're looking up the first field".
  inversion Hget. subst. exists S1...
  Case "S_RcdPerm".
  exists Ti. split.
  SCase "lookup".
  unfold ty_lookup. unfold ty_lookup in Hget.
  remember (beq_id i i1) as b. destruct b...
  SSCase "i = i1 -- we're looking up the first field".
  remember (beq_id i i2) as b. destruct b...
  SSSCase "i = i2 -- contradictory".
  destruct H0.
  apply beq_id_eq in Heqb. apply beq_id_eq in Heqb0.
  subst...
  Case "S_RcdPerm".
  inversion H. subst.
  inversion H5.
  subst ...
Qed.


Lemma sub_inversion_arrow: forall U V1 V2,
    subtype U (ty_arrow V1 V2) ->
    exists U1, exists U2,
        (U=(ty_arrow U1 U2)) /\ (subtype V1 U1) /\ (subtype U2 V2).
Proof with eauto.
  intros U V1 V2 Hs.
  remember (ty_arrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  subtype_cases (induction Hs) Case; intros V1 V2 Heq;
    try solve by inversion.
  Case "S_Refl".
  exists V1. exists V2.
  split; try (split; eauto); eauto.
  apply S_Refl. subst. inversion H. apply H2.
  apply S_Refl. subst. inversion H. apply H3.
  Case "S_Trans".
  apply IHHs2 in Heq.
  destruct Heq.
  destruct H.
  destruct IHHs1 with (V1 := x) (V2 := x0)...
  destruct H as (H1 & (H2 & H3))...
  destruct H as (H1 & (H2 & H3))...
  exists x1. destruct H0. exists x2... destruct H as (H'1 & (H'2 & H'3)).
  split...
  Case "S_Arrow".
  inversion Heq. subst. clear Heq.
  exists S1. exists S2...
Qed.

Definition context := id -> (option ty).
Definition empty: context := (fun _ => None).
Definition extend (Gamma: context) (x: id) (T: ty) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

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
| T_Proj: forall Gamma i t T Ti,
    has_type Gamma t T ->
    ty_lookup i T = Some Ti ->
    has_type Gamma (tm_proj t i) Ti
| T_Sub: forall Gamma t S T,
    has_type Gamma t S ->
    subtype S T ->
    has_type Gamma t T
| T_RNil: forall Gamma,
    has_type Gamma tm_rnil ty_rnil
| T_Rcons: forall Gamma i t T tr Tr,
    has_type Gamma t T ->
    has_type Gamma tr Tr ->
    record_ty Tr ->
    record_tm tr ->
    has_type Gamma (tm_rcons i t tr) (ty_rcons i T Tr).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
   | Case_aux c "T_Proj" | Case_aux c "T_Sub"
   | Case_aux c "T_RNil" | Case_aux c "T_Rcons"].

Module Examples2.
  Import Examples.

  Example typing_example_0:
    has_type empty
             (tm_rcons k (tm_abs z A (tm_var z))
                       (tm_rcons j (tm_abs z B (tm_var z))
                                 tm_rnil))
             ty_rcd_kj.
  Proof.
    apply T_Rcons.
    apply T_Abs.
    apply wfty_base.
    apply T_Var.
    compute. auto. auto.
    apply T_Rcons.
    apply T_Abs.
    apply wfty_base.
    apply T_Var.
    compute. auto. auto.
    apply T_RNil. auto. auto.
    compute. apply rty_cons. apply rtm_cons.
  Qed.

  Example typing_example_1:
    has_type empty
             (tm_app (tm_abs x ty_rcd_j (tm_proj (tm_var x) j))
                     (tm_rcd_kj))
             (ty_arrow B B).
  Proof with eauto.
    apply T_App with (T1 := ty_rcd_kj)...
    apply T_Sub with (S := (ty_arrow ty_rcd_j (ty_arrow B B)))...
    apply T_Abs...
    compute...
    apply S_Arrow.
    apply subtyping_example_1.
    auto.
    compute. auto.
  Qed.

  Example typing_example_2:
    has_type empty
             (tm_app (tm_abs z (ty_arrow (ty_arrow C C) ty_rcd_j)
                             (tm_proj (tm_app (tm_var z)
                                              (tm_abs x C (tm_var x )))
                                      j))
                     (tm_abs z (ty_arrow C C) tm_rcd_kj))
             (ty_arrow B B).
  Proof with eauto.
    apply T_App with (T1 := (ty_arrow (ty_arrow C C) ty_rcd_kj)).

    apply T_Sub with (S := (ty_arrow (ty_arrow(ty_arrow C C) ty_rcd_j) (ty_arrow B B))).
    apply T_Abs.
    compute...
    apply T_Proj with (T := ty_rcd_j).
    apply T_App with (T1 := (ty_arrow C C)).
    apply T_Var. compute...
    apply wfty_arrow... compute...
    apply T_Abs... compute...
    apply S_Arrow... apply S_Arrow...
    apply subtyping_example_1.
    apply T_Abs... 
    unfold tm_rcd_kj, ty_rcd_kj.
    unfold ty_rcd_j.
    apply T_Rcons...
  Qed.

End Examples2.

Lemma has_type__wf : forall Gamma t T,
    has_type Gamma t T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  has_type_cases (induction Htyp) Case...
  Case "T_App".
  inversion IHHtyp1...
  Case "T_Proj".
  eapply wf_rcd_lookup...
  Case "T_Sub".
  apply subtype_wf in H.
  destruct H...
Qed.


Lemma step_preserves_record_tm: forall tr tr',
    record_tm tr ->
    tr ==> tr' ->
    record_tm tr'.
Proof.
  intros tr tr' Htr Hstp.
  inversion Htr; subst; inversion Hstp; subst; eauto.
Qed.


Lemma lookup_field_in_value: forall v T i Ti,
    value v ->
    has_type empty v T ->
    ty_lookup i T = Some Ti ->
    exists vi, tm_lookup i v = Some vi /\ has_type empty vi Ti.
Proof with eauto.
  remember empty as Gamma.
  intros t T i Ti Hval Htyp. revert Ti HeqGamma Hval.
  has_type_cases (induction Htyp) Case; intros; subst; try solve by inversion.
  Case "T_Sub".
  apply (rcd_types_match S) in H0... destruct H0 as [Si [HgetSi Hsub]].
  destruct (IHHtyp Si) as [vi [Hget Htyvi]]...
  Case "T_Rcons".
  simpl in H0. simpl. simpl in H1.
  remember (beq_id i i0) as b. destruct b.
  SCase "i is first".
  inversion H1. subst. exists t...
  SCase "i in tail".
  destruct (IHHtyp2 Ti) as [vi [get Htyvi]]...
  inversion Hval...
Qed.


Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
    has_type Gamma s (ty_arrow T1 T2) ->
    value s ->
    exists x, exists S1, exists s2,
          s = tm_abs x S1 s2.
Proof with eauto.
  intros Gamma s T1 T2 Htyp Hval.
  remember (ty_arrow T1 T2) as T.
  generalize dependent T2. generalize dependent T1.
  has_type_cases (induction Htyp) Case; intros T'1 T'2 Ht; subst; try solve by inversion...
  Case "T_Sub".
  apply sub_inversion_arrow in H.
  destruct H. destruct H. destruct H.
  destruct (IHHtyp Hval x x0)...
Qed.

Theorem progress : forall t T,
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
  destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
    as [x [S1 [t12 Heqt]]]...
  subst. exists (subst x t2 t12)...
  SSCase "t2 steps".
  destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...
  SCase "t1 steps".
  destruct H as [t1' Hstp]. exists (tm_app t1' t2)...
  Case "T_Proj".
  right. destruct IHHt...
  SCase "rcd is value".
  destruct (lookup_field_in_value t T i Ti) as [t' [Hget Ht']]...
  SCase "rcd steps".
  destruct H0 as [t' Hstp]. exists (tm_proj t' i)...
  Case "T_Rcons".
  destruct IHHt1...
  SCase "head is a value"...
  destruct IHHt2...
  SSCase "tail steps".
  right. destruct H2 as [tr' Hstp].
  exists (tm_rcons i t tr')...
  SCase "head steps".
  right. destruct H1 as [t' Hstp].
  exists (tm_rcons i t' tr)...
Qed.


Lemma typing_inversion_var: forall Gamma x T,
    has_type Gamma (tm_var x) T ->
    exists S,
      Gamma x = Some S /\ subtype S T.
Proof with eauto.
  intros Gamma x T Hty.
  remember (tm_var x) as t.
  has_type_cases (induction Hty) Case; intros;
    inversion Heqt; subst; try solve by inversion.
  Case "T_Var".
  exists T...
  Case "T_Sub".
  destruct IHHty as [U [Hctx HsubU]]...
Qed.


Lemma typing_inversion_app: forall Gamma t1 t2 T2,
    has_type Gamma (tm_app t1 t2) T2 ->
    exists T1,
      has_type Gamma t1 (ty_arrow T1 T2) /\
      has_type Gamma t2 T1.
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember (tm_app t1 t2) as t.
  has_type_cases (induction Hty) Case; intros;
    inversion Heqt; subst; try solve by inversion.
  Case "T_App".
  exists T1...
  Case "T_Sub".
  destruct IHHty as [U1 [Hty1 Hty2]]...
  assert (Hwf := has_type__wf _ _ _ Hty2).
  exists U1...
Qed.

Lemma typing_inversion_abs: forall Gamma x S1 t2 T,
    has_type Gamma (tm_abs x S1 t2) T ->
    (exists S2, subtype (ty_arrow S1 S2) T
            /\ has_type (extend Gamma x S1) t2 S2).
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember (tm_abs x S1 t2) as t.
  has_type_cases (induction H) Case;
    inversion Heqt; subst; intros; try solve by inversion.
  Case "T_Abs".
  assert (Hwf := has_type__wf _ _ _ H0).
  exists T12...
  Case "T_Sub".
  destruct IHhas_type as [S2 [Hsub Hty]]...
Qed.

Lemma typing_inversion_proj: forall Gamma i t1 Ti,
    has_type Gamma (tm_proj t1 i) Ti ->
    exists T, exists Si,
        ty_lookup i T = Some Si /\ subtype Si Ti /\ has_type Gamma t1 T.
Proof with eauto.
  intros Gamma i t1 Ti H.
  remember (tm_proj t1 i) as t.
  has_type_cases (induction H) Case;
    inversion Heqt; subst; intros; try solve by inversion.
  Case "T_Proj".
  assert (well_formed_ty Ti) as Hwf.
  SCase "pf of assersion".
  apply (wf_rcd_lookup i T Ti)...
  apply has_type__wf in H...
  exists T. exists Ti...
  Case "T_Sub".
  destruct IHhas_type as [U [Ui [Ghet [Hsub Hty]]]]...
  exists U. exists Ui...
Qed.

Lemma typing_inversion_rcons: forall Gamma i ti tr T,
    has_type Gamma (tm_rcons i ti tr) T ->
    exists Si, exists Sr,
        subtype (ty_rcons i Si Sr) T /\ has_type Gamma ti Si /\
        record_tm tr /\ has_type Gamma tr Sr.
Proof with eauto.
  intros Gamma i ti tr T Hty.
  remember (tm_rcons i ti tr) as t.
  has_type_cases (induction Hty) Case;
    inversion Heqt; subst...
  Case "T_Sub".
  apply IHHty in H0.
  destruct H0 as [Ri [Rr [HsubRS [HtyRi HtypRr]]]].
  exists Ri. exists Rr...
  Case "T_Rcons".
  assert (well_formed_ty (ty_rcons i T Tr)) as Hwf.
  SCase "pf of assersion".
  apply has_type__wf in Hty1.
  apply has_type__wf in Hty2...
  exists T. exists Tr...
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
    appears_free_in x t1 ->  appears_free_in x (tm_app t1 t2)
| afi_app2: forall x t1 t2,
    appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
| afi_abs: forall x y T11 t12,
    y <> x ->
    appears_free_in x t12 ->
    appears_free_in x (tm_abs y T11 t12)
| afi_proj: forall x t i,
    appears_free_in x t ->
    appears_free_in x (tm_proj t i)
| afi_rhead: forall x i t tr,
    appears_free_in x t ->
    appears_free_in x (tm_rcons i t tr)
| afi_trail: forall x i t tr,
    appears_free_in x tr ->
    appears_free_in x (tm_rcons i t tr).


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
  Case "T_Rcons".
  apply T_Rcons...
Qed.

Lemma free_in_context : forall x t T Gamma,
    appears_free_in x t ->
    has_type Gamma t T ->
    exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; subst; inversion Hafi; subst...
  Case "T_Abs".
  destruct (IHHtyp H5) as [T Hctx]. exists T.
  unfold extend in Hctx.  apply not_eq_beq_id_false in H3.
  rewrite H3 in Hctx...
Qed.


Lemma substitution_preserves_typing: forall Gamma x U v t S,
    has_type (extend Gamma x U) t S ->
    has_type empty v U ->
    has_type Gamma (subst x v t) S.
Proof with eauto.
  intros Gamma x U v t S Htypt  Htypv.
  generalize dependent S. generalize dependent Gamma.
  tm_cases (induction t) Case; intros; simpl.
  Case "tm_var".
  rename i into y.
  destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].
  unfold extend in Hctx.
  remember (beq_id x y) as e. destruct e...
  SCase "x = y".
  apply beq_id_eq in Heqe. subst.
  inversion Hctx; subst. clear Hctx.
  apply context_invariance with empty...
  intros x Hcontra.
  destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
  inversion HT'.
  SCase "x<>y".
  destruct (subtype_wf _ _ Hsub)...
  Case "tm_app".
  destruct (typing_inversion_app _ _ _ _ Htypt) as [T1 [Htypt1 Htypt2]].
  eapply T_App...
  Case "tm_abs".
  rename i into y. rename t into T1.
  destruct (typing_inversion_abs _ _ _ _ _ Htypt)
    as [T2 [Hsub Htypt2]].
  destruct (subtype_wf _ _ Hsub) as [Hwf1 Hwf2].
  inversion Hwf2. subst.
  apply T_Sub with (ty_arrow T1 T2)... apply T_Abs...
  remember (beq_id x y) as e. destruct e.
  SCase "x = y".
  eapply context_invariance...
  apply beq_id_eq in Heqe. subst.
  intros x Hafi. unfold extend.
  destruct (beq_id y x)...
  SCase "x<>y".
  apply IHt. eapply context_invariance...
  intros z Hafi. unfold extend.
  remember (beq_id y z) as e0. destruct e0...
  apply beq_id_eq in Heqe0. subst.
  rewrite <- Heqe...
  Case "tm_proj".
  destruct (typing_inversion_proj _ _ _ _ Htypt)
    as [T [Ti [Hget [Hsub Htypt1]]]]...
  Case "tm_rnil".
  eapply context_invariance...
  intros y Hcontra. inversion Hcontra.
  Case "tm_rcons".
  destruct (typing_inversion_rcons _ _ _ _ _ Htypt) as
      [Ti [Tr [Hsub [HtypTi [Hrcdt2 HtypTr]]]]].
  apply T_Sub with (ty_rcons i Ti Tr)...
  apply T_Rcons...
  SCase "record_ty Tr".
  apply subtype_wf in Hsub. destruct Hsub. inversion H0...
  SCase "record tm (subst x v t2)".
  inversion Hrcdt2; subst; simpl...
Qed.


Theorem preservation: forall t t' T,
    has_type empty t T ->
    t ==> t' ->
    has_type empty t' T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  has_type_cases (induction HT) Case;
    intros t' HeqGamma HE; inversion HE; subst...
  Case "T_App".
  inversion HE; subst...
  SCase "ST_AppAbs".
  destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
  apply substitution_preserves_typing with T...
  Case "T_Proj".
  destruct (lookup_field_in_value _ _ _ _ H2 HT H)
    as [vi [Hget Hty]].
  rewrite H4 in Hget. inversion Hget. subst...
  Case "T_Rcons".
  eauto using step_preserves_record_tm.
Qed.

