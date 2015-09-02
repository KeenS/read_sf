Module Dictionary.
  Inductive dictionary: Type :=
| empty: dictionary
| record: nat -> nat -> dictionary -> dictionary.

  Definition insert (key value: nat) (d: dictionary): dictionary :=
    (record key value d).

  Fixpoint beq_nat (n m: nat): bool :=
    match n, m with
      | O, O => true
      | S n', S m' => beq_nat n' m'
      | _, _ => false
    end.

  Theorem beq_refl: forall n: nat, beq_nat n n = true.
  Proof.
    intros n.
    induction n.
    + reflexivity.
    + simpl. apply IHn.
  Qed.

  Fixpoint find (key: nat) (d: dictionary): option nat :=
    match d with
      | empty => None
      | record k v d' => if (beq_nat key k) then (Some v) else (find key d')
    end.

  Theorem dictionary_invariant1: forall (d: dictionary) (k v: nat),
                                   (find k (insert k v d)) = Some v.
  Proof.
    intros d. induction d as [| k v d'].
    + intros k v.
      simpl.
      rewrite beq_refl. reflexivity.
    + intros k0 v0.
      simpl. rewrite beq_refl. reflexivity.
  Qed.

  Theorem dictionary_invariant2: forall (d: dictionary) (m n o: nat),
                                   (beq_nat m n ) = false -> (find m d)  = (find m (insert n o d)).
  Proof.
    intros d m n o H.
    induction d.
    + simpl. rewrite H. reflexivity.
    + simpl. rewrite H. reflexivity.
  Qed.
End Dictionary.