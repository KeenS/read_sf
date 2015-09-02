Require Import Bool Peano Peano_dec Compare_dec Plus Mult Minus Le Lt EqNat Div2
        Wf_nat NAxioms NProperties.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.



Definition even (n: nat): Prop :=
  even n = true.

Check even.
Check (even 4).
Check (even 3).

Definition even_n__even_SSn (n: nat): Prop :=
  (even n ) -> (even (S (S n))).

Definition true_for_zero (P:nat -> Prop): Prop :=
  P 0.
Definition preserved_by_S (P: nat -> Prop): Prop :=
  forall n', P n' -> P (S n').
Definition true_for_all_numbers (P: nat -> Prop): Prop :=
  forall n, P n.

Definition our_nat_induction (P: nat -> Prop): Prop :=
  (true_for_zero P) ->
  (preserved_by_S P) ->
  (true_for_all_numbers P).

Inductive good_day: day -> Prop :=
| gd_sat: good_day saturday
| gd_sun: good_day sunday.

Theorem gds: good_day sunday.
Proof. apply gd_sun. Qed.


Inductive day_before: day -> day -> Prop :=
| db_tue: day_before tuesday monday
| db_wed: day_before wednesday tuesday
| db_thu: day_before thursday wednesday
| db_fri: day_before friday thursday
| db_sat: day_before saturday friday
| db_sun: day_before sunday saturday
| db_mon: day_before monday sunday.

Inductive fine_day_for_singing: day -> Prop :=
| fdfs_any: forall d:day, fine_day_for_singing d.

Theorem fdfs_wed: fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

Definition fdfs_wed': fine_day_for_singing wednesday :=
  fdfs_any wednesday.

Check fdfs_wed.
Check fdfs_wed'.

Inductive ok_day: day -> Prop :=
| okd_gd: forall d, good_day d -> ok_day d
| okd_before: forall d1 d2, ok_day d2 -> day_before d2 d1 -> ok_day d1.

Definition okdw: ok_day wednesday :=
  okd_before wednesday thursday
             (okd_before thursday friday
                         (okd_before friday saturday
                                     (okd_gd saturday gd_sat)
                                     db_sat)
                         db_fri)
             db_thu.

Theorem okdw': ok_day wednesday.
Proof.
  apply okd_before with (d2 := thursday).
  apply okd_before with (d2 := friday).
  apply okd_before with (d2 := saturday).
  apply okd_gd. apply gd_sat.
  apply db_sat. apply db_fri. apply db_thu.
Qed.

Print okdw'.

Definition okd_before2 := forall d1 d2 d3,
                            ok_day d3 ->
                            day_before d2 d1 ->
                            day_before d3 d2 ->
                            ok_day d1.

Theorem okd_before2_valid: okd_before2.
Proof.
  unfold okd_before2.
  intros d1 d2 d3 H I J.
  apply okd_before with (d2 := d2).
  apply okd_before with (d2 := d3).
  apply H.
  apply J.
  apply I.
Qed.

Definition okd_before2_valid': okd_before2 :=
  fun (d1 d2 d3: day) =>
    fun (H: ok_day d3) =>
      fun (H0: day_before d2 d1) =>
        fun (H1: day_before d3 d2) =>
          okd_before d1 d2 (okd_before d2 d3 H H1) H0.
Print okd_before2_valid.


Check nat_ind.

Theorem mult_0_r': forall n:nat,
                     n * 0 = 0.
Proof.
  apply nat_ind.
  + reflexivity.
  + simpl.
    intros n IHn.
    rewrite IHn.
    reflexivity.
Qed.

Theorem plus_one_r': forall n: nat,
                       n + 1 = S n.
Proof.
  apply nat_ind.
  + reflexivity.
  + intros n IHn.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Inductive yesno: Type :=
| yes: yesno
| no : yesno.

Check yesno_ind.

Inductive rgb: Type :=
| red: rgb
| green: rgb
| blue: rgb.
Check rgb_ind.

Inductive natlist: Type :=
| nnil: natlist
| ncons: nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1: Type :=
| nnil1: natlist1
| nsnoc1: natlist1 -> nat -> natlist1.

Check natlist1_ind.

Inductive ExSet: Type :=
| con1: bool -> ExSet
| con2: nat -> ExSet -> ExSet.

Check ExSet_ind.

Inductive tree (X:Type): Type :=
| leaf: X -> tree X
| node: tree X -> tree X -> tree X.

Inductive mytype (X: Type) :=
| constr1: X   -> mytype X
| constr2: nat -> mytype X
| constr3: mytype X-> nat -> mytype X.

Check mytype_ind.

Inductive foo (X Y: Type) :=
| bar: X -> foo X Y
| baz: Y -> foo X Y
| quux: (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Inductive foo' (X:Type) :Type :=
| C1 : list X -> foo' X -> foo' X
| C2 : foo' X.

Check foo'_ind.

Definition P_m0r (n:nat): Prop :=
  n * 0 = 0.

Theorem mult_0_r'': forall n: nat,
                      P_m0r n.
Proof.
  apply nat_ind.
  + reflexivity.
  + unfold P_m0r.
    simpl.
    intros n IHn.
    apply IHn.
Qed.

Inductive ev: nat -> Prop :=
| ev_0: ev 0
| ev_SS: forall n: nat, ev n -> ev (S (S n)).

Theorem four_ev':
  ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition four_ev: ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Definition ev_plus4: forall n, ev n -> ev (4 + n) :=
  (fun (n: nat )(H: ev n) => ev_SS (S (S n)) (ev_SS n H)).

Theorem ev_plus4': forall n,
                     ev n -> ev (4 + n).
Proof.
  intros n H.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition double (n: nat): nat := n + n.

Theorem double_even: forall n,
                       ev (double n).
Proof.
  intros n.
  unfold double.
  induction n.
  + simpl. apply ev_0.
  +  simpl.
     Lemma plus_succ: forall n m: nat, n + S m = S (n + m).
     Proof.
       induction n.
       + reflexivity.
       + Lemma eq_S: forall n m: nat, n = m -> S n = S m.
         Proof.
           intros n.
           induction n.
           + intros m H.
             rewrite H.
             reflexivity.
           + intros m H.
             rewrite H.
             reflexivity.
         Qed.
         generalize dependent n.
         simpl.
         intros n H m.         
         apply eq_S.
         apply H.
     Qed.
     rewrite plus_succ.
     apply ev_SS.
     apply IHn.
Qed.

Theorem ev_minus2: forall n,
                     ev n -> ev (pred (pred n)).
Proof.
  intros n H.
  destruct H as [| n' E].
  + simpl. apply ev_0.
  + simpl. apply E.
Qed.

Theorem ev_even: forall n,
                   ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  + unfold even. reflexivity.
  + unfold even. apply IHE'.
Qed.

Theorem ev_sum: forall n m,
                  ev n -> ev m -> ev (n + m).
Proof.
  intros n m H I.
  induction H.
  + simpl. apply I.
  + simpl.
    apply ev_SS.
    apply IHev.
Qed.

Theorem SSev_even: forall n,
                     ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E. apply H0.
Qed.

Theorem SSSSev_even: forall n,
                       ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense: ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem ev_minus2': forall n,
                      ev n -> ev (pred (pred n)).
Proof.
  intros n E. inversion E as [| n' E'].
  simpl. apply ev_0.
  simpl. apply E'.
Qed.

Theorem ev_ev_even: forall n m,
                      ev (n + m) -> ev n -> ev m.
Proof.
  intros n m H I.
  induction I.
  simpl in H.
  apply H.
  apply IHI.
  inversion H.
  apply H1.
Qed.

Inductive MyProp: nat -> Prop :=
| MyProp1: MyProp 4
| MyProp2: forall n: nat, MyProp n -> MyProp (4 + n)
| MyProp3: forall n: nat, MyProp (2 + n) -> MyProp n.

Theorem MyProp_ten: MyProp 10.
Proof.
  apply MyProp3. simpl.
  assert (12 = 4 + 8) as H12.
  reflexivity.
  rewrite H12.
  apply MyProp2.
  assert (8 = 4 + 4).
  reflexivity.
  rewrite H.
  apply MyProp2.
  apply MyProp1.
Qed.

Theorem MyProp0: MyProp 0.
Proof.
  apply MyProp3.
  apply MyProp3.
  simpl.
  apply MyProp1.
Qed.

Theorem MyProp_plustwo: forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  intros n H.
  apply MyProp3.
  simpl.
  apply MyProp2.
  apply H.
Qed.

Theorem MyProp_ev: forall n:nat,
                     ev n -> MyProp n.
Proof.
  intros n E.
  induction E.
  + apply MyProp0.
  + apply MyProp_plustwo.
    apply IHE.
Qed.

Theorem ev_MyProp: forall n: nat,
                     MyProp n -> ev n.
Proof.
  intros n H.
  induction H.
  + apply ev_SS.
    apply ev_SS.
    apply ev_0.
  + apply ev_SS.
    apply ev_SS.
    apply IHMyProp.
  + inversion IHMyProp.
    apply H1.
Qed.