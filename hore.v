Require Export ImpList_J.

Definition Assertion := state -> Prop.


Definition hoare_triple (P: Assertion) (c: com) (Q: Assertion): Prop :=
  forall st st',
    c / st || st' ->
    P st ->
    Q st'.

Notation "{{ P }} c" := (hoare_triple P c (fun st => True)) (at level 90): hoare_spec_scope.
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level): hoare_spec_scope.

Open Scope hoare_spec_scope.

Theorem hoare_post_true: forall (P Q: Assertion) c,
                           (forall st, Q st) ->
                           {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval Hp.
  apply H.
Qed.

Theorem hoare_pre_false: forall (P Q: Assertion) c,
                           (forall st, ~(P st)) ->
                           {{P}} c {{Q}}.
Proof.
  intros P Q c H.
  unfold hoare_triple.
  intros st st' Heval Hpre.
  apply H in Hpre.
  inversion Hpre.
Qed.

Definition assn_sub V a Q: Assertion :=
  fun (st: state) =>
    Q (update st V (aeval st a)).

Theorem hoare_asgn: forall Q V a,
                      {{assn_sub V a Q}} (V ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q V a st st' HE HQ.
  unfold assn_sub in HQ.
  inversion HE.
  subst.
  assumption.
Qed.

Example assn_sub_example :
  {{fun st => 3 = 3}}
    (X ::= (ANum 3))
    {{fun st => asnat (st X) = 3}}.
Proof.
  assert ((fun st => 3 = 3) = (assn_sub X (ANum 3) (fun st => asnat (st X) = 3))).
  unfold assn_sub. reflexivity.
  rewrite -> H.
  apply hoare_asgn.
Qed.

Theorem hoare_asgn_eq: forall Q Q' V a,
                         Q' = assn_sub V a Q ->
                         {{Q'}} (V ::= a) {{Q}}.
Proof.
  intros Q Q' V a H.
  rewrite H. apply hoare_asgn.
Qed.

Example assn_sub_example':
  {{fun st => 3 = 3}}
    (X ::= (ANum 3))
    {{fun st => asnat (st X) = 3}}.
Proof.
  apply hoare_asgn_eq. reflexivity.
Qed.

Theorem hoare_asgn_weakest: forall P V a Q,
                              {{P}} (V ::= a) {{Q}} ->
                              forall st, P st -> assn_sub V a Q st.
Proof.
  intros P V a Q Has st HE.
  unfold hoare_triple in Has.
  unfold assn_sub.
  apply Has with (st := st).
  apply E_Asgn.
  reflexivity.
  assumption.
Qed.


Theorem hoare_consequence: forall (P P' Q Q': Assertion) c,
                             {{P'}} c {{Q'}} ->
                             (forall st, P st -> P' st) ->
                             (forall st, Q' st -> Q st) ->
                             {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c H HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q. apply (H st st'). assumption.
  apply HPP'. assumption.
Qed.

Theorem hoare_consequence_pre: forall (P P' Q: Assertion) c,
                                 {{P'}} c {{Q}} ->
                                 (forall st, P st -> P' st) ->
                                 {{P}} c {{Q}}.
Proof.
  intros P P' Q c H HPP'.
  apply hoare_consequence with (P' := P') (Q' := Q); try assumption.
  intros st H'. apply H'.
Qed.

Theorem hoare_consequence_post: forall (P Q' Q: Assertion) c,
                                  {{P}} c {{Q'}} ->
                                  (forall st, Q' st -> Q st) ->
                                  {{P}} c {{Q}}.
Proof.
  intros P Q' Q c H HQQ'.
  apply hoare_consequence with (P' := P) (Q' := Q'); try assumption.
  + intros st H'. apply H'.
Qed.

Example hoare_asgn_example1:
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => asnat (st X) = 1}}.
Proof.
  apply hoare_consequence_pre with (P' := (fun st => 1 = 1)).
  apply hoare_asgn_eq. reflexivity.
  intros st H. reflexivity.
Qed.

Example hoare_asgn_example1' :
  {{fun st => True}}
    (X ::= (ANum 1))
    {{fun st => asnat (st X) = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn_eq. reflexivity.
  intros st H. reflexivity.
Qed.

Theorem hoare_skip: forall P,
                      {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP.
  inversion H.
  subst. assumption.
Qed.

Theorem hoare_seq: forall P Q R c1 c2,
                     {{Q}} c2 {{R}} ->
                     {{P}} c1 {{Q}} ->
                     {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 HQR HPQ.
  intros st st' H Hp.
  inversion H. subst. clear H.
  apply (HQR st'0 st'); try assumption.
  apply (HPQ st st'0); try assumption.
Qed.

Example hoare_asgn_example3: forall a n,
                               {{fun st => aeval st a = n}}
                                 (X ::= a; SKIP)
                                 {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  + apply hoare_skip.
  + eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity.
Qed.

Example hoare_asgn_example4:
  {{fun st => True}} (X ::= (ANum 1); Y ::= (ANum 2))
               {{fun st => asnat (st X) = 1 /\ asnat (st Y) = 2}}.
Proof.
  eapply hoare_seq.
  apply hoare_asgn.
  unfold assn_sub.
  unfold update.
  simpl.
  intros st st' H H'.
  inversion H. subst. simpl.
  omega.
Qed.

Definition bassn b: Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true: forall b st,
                        beval st b = true -> (bassn b) st.
Proof.
  intros b st H.
  unfold bassn. assumption.
Qed.

Lemma bexp_eval_false: forall b st,
                         beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st H contra.
  unfold bassn in contra.
  rewrite contra in H. inversion H.
Qed.

Theorem hoare_if: forall P Q b c1 c2,
                    {{fun st => P st /\ bassn b st}} c1 {{Q}}  ->
                    {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
                    {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  + apply (HTrue st st'). assumption.
    split. assumption. apply bexp_eval_true. assumption.
  + apply (HFalse st st'). assumption.
    split. assumption. apply bexp_eval_false. assumption.
Qed.

Example if_example:
  {{fun st => True}}
    IFB (BEq (AId X) (ANum 0))
    THEN (Y ::= (ANum 2))
    ELSE (Y ::= (APlus (AId X) (ANum 1)))
    FI
    {{fun st => asnat (st X) <= asnat (st Y)}}.
Proof.
  apply hoare_if.
  + eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, update.  simpl. intros.
    inversion H. symmetry in H1; apply beq_nat_eq in H1.
    rewrite H1. omega.
  +
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, update; simpl; intros. omega.
Qed.

Lemma hoare_while: forall P b c,
                     {{fun st => P st /\ bassn b st}} c {{P}} ->
                     {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wocm.
  ceval_cases (induction He) Case; try (inversion Heqwocm); subst.
  Case "E_WhileEnd".
  split. assumption. apply bexp_eval_false. assumption.
  Case "E_WhileLoop".
  apply IHHe2. reflexivity.
  apply (Hhoare st st'); try assumption.
  split. assumption. apply bexp_eval_true. assumption.
Qed.

Example while_example:
  {{fun st => asnat (st X) <= 3}}
    WHILE (BLe (AId X) (ANum 2))
    DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => asnat (st X) = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub. intros. rewrite update_eq. simpl.
  inversion H as [_ H0].simpl in H0. apply ble_nat_true in H0.
  omega.
  unfold bassn. intros. inversion H as [Hle Hb]. simpl in Hb.
  remember (ble_nat (asnat (st X)) 2) as le. destruct le.
  apply ex_falso_quodlibet. apply Hb. reflexivity.
  symmetry in Heqle. apply ble_nat_false in Heqle. omega.
Qed.

Theorem always_loop_hoare: forall P Q,
                             {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
  apply hoare_post_true. intros st. apply I.
  Case "Loop invariant and negated guard imply postcondition".
  simpl. intros st [Hinv Hguard].
  apply ex_falso_quodlibet. apply Hguard. reflexivity.
  Case "Precondition implies invariant".
  intros st H. constructor.
Qed.

Theorem always_loop_hoare': forall P Q,
                              {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  unfold hoare_triple. intros P Q st st' contra.
  apply loop_never_stops in contra. inversion contra.
Qed.