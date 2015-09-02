Require Export "Prop_J".

Inductive and (P Q: Prop) :Prop :=
  conj: P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q): type_scope.

Check conj.

Theorem and_example:
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
  apply ev_0.
  apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Print and_example.

Theorem and_example':
  (ev 0) /\ (ev 4).
Proof.
  split.
  - apply ev_0.
  - apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Theorem proj1: forall P Q: Prop,
                 P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H.
  apply H0.
Qed.

Theorem proj2: forall P Q: Prop,
                 P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [ Hp Hq].
  apply Hq.
Qed.

Theorem and_commut: forall P Q: Prop,
                      P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [Hp Hq].
  split.
  - apply Hq.
  - apply Hp.
Qed.

Print and_commut.

Theorem and_assoc: forall P Q R: Prop,
                     P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [Hp Hqr].
  inversion Hqr as [Hq Hr].
  split.
  split.
  apply Hp.
  apply Hq.
  apply Hr.
Qed.

Theorem even_ev: forall n: nat,
                   (even n -> ev n)  /\ (even (S n) -> ev (S n)).
Proof.
  induction n.
  + split.
    intros H.
    apply ev_0.
    intros H.
    inversion H.
  + split.
    apply IHn.
    intros H.
    apply ev_SS.
    inversion IHn.
    apply H0.
    apply H.
Qed.

Definition conj_fact: forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  (fun (P Q R: Prop) =>
    (fun (H0: and P Q) =>
       (fun (H1: and Q R) =>
       conj P R (proj1 P Q H0) (proj2 Q R H1)))
  ).

Definition iff (P Q: Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                        (at level 95, no associativity): type_scope.

Theorem iff_implies: forall P Q: Prop,
                       (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H.
  apply H0.
Qed.

Theorem iff_sym: forall P Q: Prop,
                   (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H.
  split.
  apply H1.
  apply H0.
Qed.

Theorem iff_refl: forall P: Prop,
                    P <-> P.
Proof.
  intros P.
  split.
  intros H.
  apply H.
  intros H.
  apply H.
Qed.

Theorem iff_trans: forall P Q R: Prop,
                     (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2.
  inversion H1.
  inversion H2.
  split.
  intros Hp.
  apply H3.
  apply H.
  apply Hp.
  intros Hr.
  apply H0.
  apply H4.
  apply Hr.
Qed.

Definition MyProp_iff_ev: forall n, MyProp n <-> ev n :=
  (fun (n: nat) => conj (MyProp n -> ev n) (ev n -> MyProp n) (ev_MyProp n) (MyProp_ev n)).

Inductive or (P Q: Prop): Prop :=
| or_introl: P -> or P Q
| or_intror: Q -> or P Q.

Notation "P \/ Q" := (or P Q): type_scope.

Check or_introl.
Check or_intror.

Theorem or_commut: forall P Q: Prop,
                     P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H.
  + apply or_intror.
    apply H0.
  + apply or_introl.
    apply H0.
Qed.

Theorem or_commut': forall P Q: Prop,
                      P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
  + right. apply HP.
  + left. apply HQ.
Qed.

Print or_commut.

Theorem or_distributes_over_and_1: forall P Q R: Prop,
                                     P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
  + split.
    left. apply HP.
    left. apply HP.
  + split.
    right. apply HQ.
    right. apply HR.
Qed.

Theorem or_distributes_over_and_2: forall P Q R: Prop,
                                     (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R. intros H. inversion H.
  inversion H0. inversion H1.
  left. apply H3.
  left. apply H2.
  inversion H1.
  left. apply H3.
  right. split. apply H2. apply H3.
Qed.

Theorem or_distributes_over_and: forall P Q R: Prop,
                                   P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  + apply or_distributes_over_and_1.
  + apply or_distributes_over_and_2.
Qed.

Theorem andb_true__and: forall b c,
                          andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
  + destruct c.
    - apply conj. reflexivity. reflexivity.
    - inversion H.
      + inversion H.
Qed.

Theorem and__andb_true: forall b c,
                          b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity.
Qed.

Theorem andb_false: forall b c,
                      andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct H.
  destruct b.
  right.  reflexivity.
  left. reflexivity.
Qed.

Theorem orb_true: forall b c,
                    orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b.
  + left. reflexivity.
  + simpl in H. right. apply H.
Qed.

Theorem orb_false: forall b c,
                     orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b.
  + simpl in H. inversion H.
  +  apply conj. reflexivity. simpl in H. apply H.
Qed.

Inductive False: Prop :=.


Theorem False_implies_nonsense:
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem nonsense_implies_False:
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem ex_falso_quodlibet: forall (P:Prop),
                              False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.


Definition not (P: Prop) := P -> False.

Notation "~ x" := (not x): type_scope.
Check not.

Theorem not_False:
  ~ False.
Proof.
  unfold not. intros H. inversion H.
Qed.

Theorem contradiction_implies_anything: forall P Q: Prop,
                                          (P /\ ~P) -> Q.
Proof.
  intros P Q H. inversion H as [HP HNP].
  unfold not in HNP.
  apply HNP in HP.
  inversion HP.
Qed.

Theorem double_neg: forall P: Prop,
                      P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros I.
  apply I in H.
  inversion H.
Qed.

Theorem contrapositive: forall P Q: Prop,
                          (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  unfold not.
  intros I.
  intros J.
  apply H in J.
  apply I in J.
  inversion J.
Qed.

Theorem not_both_true_and_false: forall P: Prop,
                                   ~ (P /\ ~ P).
Proof.
  intros P.
  unfold not.
  intros H.
  inversion H.
  apply H1 in H0.
  inversion H0.
Qed.

Theorem five_not_even:
  ~ ev 5.
Proof.
  unfold not. intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem ev_not_ev_S: forall n,
                       ev n -> ~ ev (S n).
Proof.
  unfold not.
  intros n H.
  induction H.
  + intros I. inversion I.
  + intros I.
    inversion I.
    apply IHev in H1.
    inversion H1.
Qed.

Notation "x <> y" := (~ (x = y)): type_scope.

Theorem not_false_then_true: forall b: bool,
                               b <> false -> b = true.
Proof.
  intros b H.
  destruct b.
  + reflexivity.
  + unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
Qed.

Theorem not_eq_beq_false: forall n n': nat,
                            n <> n' -> beq_nat n n' = false.
Proof.
  intros n.
  induction n.
  + intros n'.
    induction n'.
  - simpl. intros H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - intros H. simpl. reflexivity.
    + intros n'. induction n'.
  - intros H. reflexivity.
  - intros H. simpl.
    apply IHn.
    unfold not in H.
    unfold not.
    replace (S n = S n') with (n = n') in H.
    apply H.
Admitted.


Inductive ex (X: Type) (P: X -> Prop): Prop :=
  ex_intro: forall(witness: X), P witness -> ex X P.

Definition some_nat_is_even: Prop :=
  ex nat ev.

Definition snie: some_nat_is_even :=
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Notation "'exists' x , p" := (ex _ (fun x => p))
                               (at level 200, x ident, right associativity): type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
                                   (at level 200, x ident, right associativity): type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness := 2).
  reflexivity.
Qed.

Example exists_example_1': exists n,
                             n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2: forall n,
                            (exists m, n = 4 + m) ->
                            (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H.
  exists (2 + witness).
  apply H0.
Qed.

Definition p: ex nat (fun n => ev (S n)) :=
  ex_intro _ (fun n =>  ev (S n)) 1 (ev_SS 0 ev_0).

Theorem dist_not_exists: forall (X: Type) (P: X -> Prop),
                           (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P. intros H.
  unfold not.
  intros I.
  inversion I.
  apply H0.
  apply H.
Qed.

Definition peirce := forall P Q: Prop,
  ((P -> Q)->P)->P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

Theorem dist_exists_or: forall (X: Type) (P Q: X -> Prop),
                          (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
  intros X P Q.
  split.
  + intros H.
    inversion H.
    inversion H0.
    left.  exists witness. apply H1.
    right. exists witness. apply H1.
  + intros H.
    inversion H.
    inversion H0.
    exists witness. left. apply H1.
    inversion H0.
    exists witness. right. apply H1.
Qed.

Module MyEquality.
  Inductive eq (X: Type): X -> X -> Prop :=
    refl_equal: forall x, eq X x x.
  Notation "x = y" := (eq _ x y)
                        (at level 70, no associativity): type_scope.

  Inductive eq' (X: Type) (x: X): X -> Prop :=
    refl_equal' : eq' X x x.

  Notation "x =' y" := (eq' _ x y)
                         (at level 70, no associativity): type_scope.
  Theorem two_defs_of_equal_concide: forall (X: Type) (x y: X),
                                       x = y <-> x =' y.
  Proof.
    intros X x y.
    split.
    intros H.
    inversion H.
    reflexivity.
    intros H.
    inversion H.
    apply refl_equal.
  Qed.

  Definition four: 2 + 2 = 1 + 3 :=
    refl_equal nat 4.
  Definition singleton: forall (X: Set) (x: X), []++[x] = x::[] :=
    fun (X: Set) (x: X) => refl_equal (list X) [x].
End MyEquality.

Module LeFirstTry.
  Inductive le: nat -> nat -> Prop :=
| le_n: forall n, le n n
| le_S: forall n m, (le n m) -> (le n (S m)).
End LeFirstTry.


Inductive le(n: nat): nat -> Prop :=
| le_n: le n n
| le_S: forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.

Theorem test_le1:
  3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2:
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S.
  apply le_n.
Qed.

Theorem test_le3:
  ~(2 <= 1).
Proof.
  intros H.
  inversion H.
  inversion H1.
Qed.

Definition lt (n m: nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of: nat -> nat -> Prop :=
  sq: forall n: nat, square_of n (n * n).

Inductive next_nat (n: nat): nat -> Prop :=
| nn: next_nat n (S n).

Inductive next_even (n: nat): nat -> Prop :=
| ne_1: ev (S n) -> next_even n (S n)
| ne_2: ev (S (S n)) -> next_even n (S (S n)).

Module R.
  Inductive R: nat -> nat -> nat -> Prop :=
| c1: R 0 0 0
| c2: forall m n o, R m n o -> R (S m) n (S o)
| c3: forall m n o, R m n o -> R m (S n) (S o)
| c4: forall m n o, R (S m) (S n) (S (S o)) -> R m n o
| c5: forall m n o, R m n o -> R n m o.

End R.

(*
Theorem not_exists_dist:
  excluded_middle ->
  forall (X: Type) (P: X -> Prop),
    ~(exists x, ~ P x) -> (forall x, P x).
Proof.
  intros Ex X P H x.
  unfold not in H.
  unfold excluded_middle in Ex.
  apply Ex with (P x)
*)