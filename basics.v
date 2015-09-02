Lemma mult_0_r : forall n: nat,
                   n * 0 = 0.
Proof.
  intros n.
  induction n.
  + simpl.
    reflexivity.
  + simpl.
    apply IHn.
Qed.


Lemma add_swap: forall l n m:nat, l + (n + m) = n + (l + m).
- intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  assert(I: forall m n: nat, S(m + n) = m + S n).
  * intros m1 m2.
    induction m1.
    simpl.
    reflexivity.
    simpl.
    rewrite IHm1.
    reflexivity.
  * rewrite I.
    reflexivity.
Qed.


Lemma add_remove_l: forall j k l m n:nat,
                      j + k = l + m ->
                      n + j + k = n + l + m.
Proof.
  intros j k l m n.
  intros H.
  induction n.
  + simpl.
    apply H.
  + simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma mult_succ : forall m n:nat,
                    n * S m = n + n * m.
Proof.
  intros m n.
  induction n.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHn.
    - assert(H: (m + (n + n*m)) = (n + (m + n * m))).
      rewrite add_swap.
      reflexivity.
      rewrite H.
      reflexivity.
Qed.


Theorem mult_plus_distr_r : forall m n p: nat,
                              (n + m) * p = n * p + m * p.
Proof.
  intros m n p.
  induction p.
  + rewrite mult_0_r.
    rewrite mult_0_r.
    rewrite mult_0_r.
    reflexivity.
  + rewrite mult_succ.
    rewrite mult_succ.
    rewrite mult_succ.
    rewrite IHp.
    assert (H: m + (n * p + m *p) = n * p + (m + m * p)).
    - rewrite add_swap.
      reflexivity.
    - apply add_remove_l.
      apply add_swap.
Qed.

Theorem mult_plus_distr_l : forall m n p: nat,
                              p * (n + m) = p *n + p * m.
Proof.
  intros m n p.
  induction p.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHp.
    assert(H: m + (p * n + p * m) = p * n + (m + p * m)).
    - rewrite add_swap.
      reflexivity.
    - apply add_remove_l.
      apply add_swap.
Qed.

Theorem mult_assoc : forall n m p: nat,
                       n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction m.
  + simpl.
    rewrite mult_0_r.
    simpl.
    reflexivity.
  + simpl.
    rewrite mult_succ.
    rewrite mult_plus_distr_r.
    rewrite mult_plus_distr_l.
    rewrite IHm.
    reflexivity.
Qed.

Lemma add_succ : forall n m: nat,
                   n + S m = S (n + m).
Proof.
  intros n m.
  induction n.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHn.
    reflexivity.
Qed.


Theorem plus_swap' : forall n m p: nat,
                       n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  induction n.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHn.
    rewrite add_succ.
    reflexivity.
Qed.

Inductive bin: Type :=
| O  : bin
| B  : bin -> bin
| BPlus : bin -> bin.

Fixpoint incb(b: bin) : bin :=
  match b with
    | O => BPlus O
    | B b' => BPlus b'
    | BPlus b' => B (incb b')
  end.


Fixpoint to_nat (b: bin) : nat :=
  match b with
    | O => 0
    | B b' => (to_nat b') * 2
    | BPlus b' => (to_nat b') * 2 + 1
  end.

Lemma add_0_r: forall n: nat,
                 n + 0 = n.
Proof.  
  intros n.
  induction n.
  + reflexivity.
  + simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem to_nat_comm: forall b: bin,
         to_nat (incb b) = S (to_nat b).
Proof.
  intros b.
  induction b.
  + simpl.
    reflexivity.
  + simpl.
    rewrite add_succ.
    rewrite add_0_r.
    reflexivity.
  + simpl.
    rewrite add_succ.
    rewrite add_0_r.
    rewrite IHb.
    simpl.
    reflexivity.
Qed.

Fixpoint to_bin (n :nat) :bin :=
  match n with
    | 0 => O
    | S n => incb (to_bin n)
  end.

Theorem nat_bin_nat: forall n: nat,
                       to_nat (to_bin n) = n.
Proof.
  intros n.
  induction n.
  + simpl. reflexivity.
  + simpl.
    rewrite to_nat_comm.
    rewrite IHn.
    reflexivity.
Qed.

Definition id_bin (b: bin): bin :=
  to_bin (to_nat b).

Theorem bin_nat_bin: forall b: bin,
                       to_bin (to_nat b) = b.
Proof.
  intros b.
  induction b.
  + simpl.
    reflexivity.
  + simpl.
    