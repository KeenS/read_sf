Require Export Logic_J.

Definition relation (X: Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2: X, R x y1 -> R x y2 -> y1 = y2.

Theorem next_nat_partial_function:
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 P Q.
  inversion P.
  inversion Q.
  reflexivity.
Qed.

Theorem le_not_a_partial_function:
  ~(partial_function le).
Proof.
  unfold not. unfold partial_function.
  intros H.
  assert (0 = 1) as Nonsense.
  apply H with 0.
  apply le_n.
  apply le_S. apply le_n.
  inversion Nonsense.
Qed.

(* Theorem total_relation_not_a_partial_function: *)
(*   ~(partial_function total_relation). *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a: X, R a a.

Theorem le_reflexive:
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.
Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c: X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans: transitive le.
Proof.
  unfold transitive.
  intros n m o Hmn Hmo.
  induction Hmo.
  apply Hmn.
  apply le_S. apply IHHmo.
Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo.
Qed.

Theorem lt_trans':
  transitive lt.
Proof.
  unfold lt.
  unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  + apply lt_S.
    inversion Hnm.
    apply le_n.
    rewrite H0.
    apply Hnm.
  + apply le_S.
    apply IHHm'o.
Qed.

Theorem lt_trans'':
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros m n o Hnm Hmo.
  induction o as [| o'].
  + inversion Hmo.
  + apply le_S.
    inversion Hmo.
    rewrite <- H0.
    apply Hnm.
    apply IHo'.
    apply H0.
Qed.

Theorem le_Sn_le: forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  apply le_S. apply le_n.
  apply H.
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b: X, (R a b) -> (R b a).

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b: X, (R a b) -> (R b a) -> a = b.


Definition equivalence {X: Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X: Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
| rt_step : forall x y, R x y -> clos_refl_trans R x y
| rt_refl : forall x, clos_refl_trans R x x
| rt_trans: forall x y z, clos_refl_trans R x y -> clos_refl_trans R y z -> clos_refl_trans R x z.

