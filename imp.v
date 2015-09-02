Require Export SfLib_J.

Module AExp.
  Inductive aexp: Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.


  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

  Fixpoint aeval (e: aexp) : nat :=
    match e with
      | ANum n => n
      | APlus a1  a2 => (aeval a1) + (aeval a2)
      | AMinus a1 a2 => (aeval a1) - (aeval a2)
      | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Example test_aeval1: aeval(APlus (ANum 2) (ANum 2)) = 4.
  Proof. reflexivity. Qed.

  Fixpoint beval (e: bexp): bool :=
    match e with
      | BTrue => true
      | BFalse => false
      | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
      | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
      | BNot b1 => negb (beval b1)
      | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (e:aexp) : aexp :=
    match e with
      | ANum n => ANum n
      | APlus (ANum 0) e2 => optimize_0plus e2
      | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 => AMult (optimize_0plus e1)  (optimize_0plus e2)
    end.
                                           
  Example test_optimize_0plus:
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0)
                                        (ANum 1))))
    = APlus (ANum 2) (ANum 1).
  Proof. reflexivity. Qed.

  Theorem optimize_0plus_sound: forall e,
                                  aeval (optimize_0plus e) = aeval e.
    Proof.
      intros e. induction e.
      + reflexivity.
      + destruct e1.
      - destruct n.
        apply IHe2.
        simpl. rewrite IHe2. reflexivity.
      - simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
      - simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
      - simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
        + simpl. rewrite IHe1. rewrite IHe2. reflexivity.
        + simpl. rewrite IHe1. rewrite IHe2. reflexivity.
    Qed.

    Lemma foo: forall n, ble_nat 0 n = true.
    Proof.
      intros. destruct n.
      + simpl. reflexivity.
      + simpl. reflexivity.
    Qed.

    Lemma foo': forall n, ble_nat 0 n = true.
    Proof.
      intros.
      destruct n; simpl; reflexivity.
    Qed.

    Theorem optimize_0plus_sound': forall e,
                                     aeval (optimize_0plus e) = aeval e.
    Proof.
      intros e.
      induction e;
        try (simpl; rewrite IHe1; rewrite IHe2; reflexivity).
      Case "ANum". reflexivity.
      Case "APlus".
      destruct e1; try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
      SCase "e1 = ANum n". destruct n; simpl; rewrite IHe2; reflexivity. Qed.

    Theorem optimize_0plus_sound'': forall e,
                                      aeval (optimize_0plus e) = aeval e.
    Proof.
      intros e.
      induction e;
        try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
        try reflexivity.
      Case "APlus".
      destruct e1; try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
      SCase "e1 = ANum n". destruct n; simpl; rewrite IHe2; reflexivity. Qed.

    Tactic Notation "simpl_and_try" tactic(c) := simpl; try c.

    Tactic Notation "aexp_cases" tactic(first) ident(c) :=
      first;
      [Case_aux c "ANum" | Case_aux c "APlus"
       | Case_aux c "AMinus" | Case_aux c "AMult"].

    Theorem optimize_0plus_sound''': forall e,
                                       aeval (optimize_0plus e) = aeval e.
    Proof.
      intros e.
      aexp_cases (induction e) Case;
        try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
        try reflexivity.
      Case "APlus".
      aexp_cases (destruct e1) SCase;
        try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
      SCase "ANum". destruct n;
        simpl; rewrite IHe2; reflexivity. Qed.

    Fixpoint optimize_0plus_b (e: bexp) : bexp :=
      match e with
        | BTrue => BTrue
        | BFalse => BFalse
        | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
        | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
        | BNot b1 => BNot (optimize_0plus_b b1)
        | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
      end.

    Theorem optimize_0plus_b_sound: forall e, beval (optimize_0plus_b e) = beval e.
    Proof.
      intros e.
      induction e;
        simpl;
        try (rewrite optimize_0plus_sound;
                     rewrite optimize_0plus_sound;
                     reflexivity);
        try reflexivity.
      rewrite IHe. reflexivity.
      rewrite IHe1. rewrite IHe2. reflexivity.
    Qed.

    Example silly_presburger_example: forall n m o p,
                                        m + n <= n + o /\ o + 3 = p + 3 -> m <= p.
    Proof.
      intros. omega.
    Qed.

    Module aevalR_first_try.
      Inductive aevalR: aexp -> nat -> Prop :=
    | E_ANum: forall (n: nat),
                aevalR (ANum n) n
    | E_APlus: forall (e1 e2: aexp) (n1 n2: nat),
                 aevalR e1 n1 ->
                 aevalR e2 n2 ->
                 aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
                  aevalR e1 n1 ->
                  aevalR e2 n2 ->
                  aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult: forall (e1 e2: aexp) (n1 n2: nat),
                 aevalR e1 n1 ->
                 aevalR e2 n2 ->
                 aevalR (AMult e1 e2) (n1 * n2).

      Notation "e '||' n" := (aevalR e n) : type_scope.
    End aevalR_first_try.

    Reserved Notation "e '||' n" (at level 50, left associativity).

    Inductive aevalR: aexp -> nat -> Prop :=
    | E_ANum: forall (n: nat),
                (ANum n) || n
    | E_APlus: forall (e1 e2: aexp) (n1 n2: nat),
                 (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
    | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
                  (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
    | E_AMult: forall (e1 e2: aexp) (n1 n2: nat),
                 (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)
    where "e '||' n" := (aevalR e n) : type_scope.

    Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "E_ANum" | Case_aux c "E_APlus" | Case_aux c "E_AMinus" | Case_aux c "E_AMult"].

    Theorem aeval_iff_aevalR: forall a n,
                                (a || n) <-> aeval a = n.
    Proof.
      split.
      Case "->".
      intros H; induction H; subst; reflexivity.
      Case "<-".
      generalize dependent n.
      induction a; simpl; intros; subst; constructor;
      try apply IHa1; try apply IHa2; reflexivity.
    Qed.

End AExp.

Theorem beq_id_refl: forall X,
                       true = beq_id X X.
Proof.
  intros. destruct X.
  apply beq_nat_refl.
Qed.

Theorem beq_id_eq: forall i1 i2,
                     true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros i1 i2.
  destruct i1.
  destruct i2.
  unfold beq_id.
  intros H.
  apply beq_nat_eq in H.
  subst.
  reflexivity.
Qed.

Definition state := id -> nat.
Definition empty_state: state :=
  fun _ => 0.
Definition update (st: state) (X: id) (n: nat) : state :=
  fun X' => if beq_id X X' then n else st X'.

Theorem update_eq: forall n X st,
                     (update st X n) X = n.
Proof.
  intros n X st.
  unfold update. replace (beq_id X X) with true.
  reflexivity.
  apply beq_id_refl.
Qed.

Theorem update_neq:forall V2 V1 n st,
                     beq_id V2 V1 = false ->
                     (update st V2 n) V1 = (st V1).
Proof.
  intros V2 V1 n st H.
  unfold update.
  rewrite H.
  reflexivity.
Qed.

Theorem update_example: forall (n: nat),
                          (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros n.
  unfold update. simpl. unfold empty_state. reflexivity.
Qed.

Theorem update_shadow: forall x1 x2 k1 k2 (f: state),
                         (update (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  intros x1 x2 k1 k2 f.
  unfold update.
  case (beq_id k2 k1).
  + reflexivity.
  + reflexivity.
Qed.

Theorem update_some: forall x1 k1 k2 (f: state),
                       f k1 = x1 -> (update f k1 x1) k2 = f k2.
Proof.
  intros x1 k1 k2 f H.
  unfold update.
  subst.
  remember (beq_id k1 k2) as H.
  destruct H.
  replace k1 with k2. reflexivity.
  apply beq_id_eq. rewrite beq_id_sym.
  apply HeqH. reflexivity.
Qed.

Theorem update_permute: forall x1 x2 k1 k2 k3 f,
                          beq_id k2 k1 = false ->
                          (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  intros x1 x2 k1 k2 k3 f H.
  unfold update.
  remember (beq_id k1 k3) as A.
  remember (beq_id k2 k3) as B.
  destruct A.
  replace k3 with k1 in HeqB.
  rewrite H in HeqB.
  subst. reflexivity.
  apply beq_id_eq. apply HeqA.
  reflexivity.
Qed.


Inductive aexp: Type :=
| ANum: nat -> aexp
| AId: id -> aexp
| APlus: aexp -> aexp -> aexp
| AMinus: aexp -> aexp -> aexp
| AMult: aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
   |Case_aux c "AMinus" | Case_aux c "AMult"].

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Inductive bexp: Type :=
| BTrue  : bexp
| BFalse : bexp
| BEq    : aexp -> aexp -> bexp
| BLe    : aexp -> aexp -> bexp
| BNot   : bexp -> bexp
| BAnd   : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
    | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

Fixpoint aeval (st: state) (e: aexp): nat :=
  match e with
    | ANum n => n
    | AId X => st X
    | APlus a1 a2 => (aeval st a1) + (aeval st a2)
    | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
    | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st:state)  (e: bexp) : bool :=
  match e with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
    | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
    | BNot b1 => negb (beval st b1)
    | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1:
  aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
        = 13.
Proof. reflexivity. Qed.

Example bexp1: beval (update empty_state X 5)
                     (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
               = true.
Proof. reflexivity. Qed.

Inductive com: Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
   | Case_aux c "IFB" | Case_aux c "WHILE"].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).

Definition fact_in_coq: com :=
  Z ::= AId X;
  Y ::= ANum 1;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
        Y ::= AMult (AId Y) (AId Z);
        Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2: com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ: com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition substract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1);
  X ::= AMinus (AId X) (ANum 1).

Definition substract_slowly: com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
        substract_slowly_body
  END.

Definition substract_3_from_5_slowly: com :=
  X ::= ANum 3;
  Z ::= ANum 5;
  substract_slowly.

Definition loop : com :=
  WHILE BTrue DO
        SKIP
  END.

Definition fact_body: com :=
  Y ::= AMult (AId Y) (AId Z);
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop: com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
        fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X;
  Y ::= ANum 1;
  fact_loop.

Fixpoint ceval_step1 (st: state) (c: com) : state :=
  match c with
    | SKIP =>
      st
    | l ::= a1 =>
      update st l (aeval st a1)
    | c1 ; c2 =>
      let st' := ceval_step1 st c1 in
      ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI =>
      if (beval st b)
      then ceval_step1 st c1
      else ceval_step1 st c2
    | WHILE b1 DO c1 END =>
      st
  end.

Fixpoint ceval_step2 (st: state) (c: com) (i: nat) : state :=
  match i with
    | O => empty_state
    | S i' =>
      match c with
        | SKIP =>
          st
        | l ::= a1 =>
          update st l (aeval st a1)
        | c1 ; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step1 st' c2
        | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
          then ceval_step2 st c1 i'
          else ceval_step2 st c2 i'
        | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
      end
  end.


Fixpoint ceval_step3 (st: state) (c: com) (i: nat)
: option state :=
  match i with
    | O => None
    | S i' =>
      match c with
        | SKIP =>
          Some st
        | l ::= a1 =>
          Some (update st l (aeval st a1))
        | c1 ; c2 =>
          match (ceval_step3 st c1 i') with
            | Some st' => ceval_step3 st' c2 i'
            | None => None
          end
        | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
          then ceval_step3 st c1 i'
          else ceval_step3 st c2 i'
        | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
                 | Some st' => ceval_step3 st' c i'
                 | None => None
               end
          else Some st
      end
  end.

Notation "'LETOPT' x <== e1 'IN' e2"
  := (match e1 with
        | Some x => e2
        | None => None
      end)
       (right associativity, at level 60).

Fixpoint ceval_step (st: state) (c: com) (i: nat)
: option state :=
  match i with
    | O => None
    | S i' =>
      match c with
        | SKIP =>
          Some st
        | l ::= a1 =>
          Some (update st l (aeval st a1))
        | c1 ; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
                 ceval_step st' c2 i'
        | IFB b THEN c1 ELSE c2 FI =>
              if (beval st b)
              then ceval_step st c1 i'
              else ceval_step st c2 i'
        | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
                      ceval_step st' c i'
          else Some st
      end
  end.

Definition test_ceval (st: state) (c: com) :=
  match ceval_step st c 500 with
    | None => None
    | Some st => Some (st X, st Y, st Z)
  end.

Definition pup_to_n: com :=
  WHILE BNot (BEq (AId X)  (ANum 0)) DO
        Y ::= APlus (AId X) (AId Y);
        X ::= AMinus (AId X) (ANum 1)
  END.

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st || (update st l n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st || st' ->
      c2 / st' || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st || st' ->
      (WHILE b1 DO c1 END) / st' || st'' ->
      (WHILE b1 DO c1 END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').


Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_SKip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
    | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
    | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

Example ceval_example1:
  (X ::= ANum 2;
   IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
    FI)
    / empty_state
    || (update (update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (update empty_state X 2).
  apply E_Ass. reflexivity.
  apply E_IfFalse. reflexivity.
  apply E_Ass. reflexivity.
Qed.

Theorem ceval_step__ceval: forall c st st',
                             (exists i, ceval_step st c i = Some st') ->
                             c / st || st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i'].

  Case "i = 0 -- contradictory".
  intros c st st' H. inversion H. 
  Case "i = S i'".
  intros c st st' H.
  com_cases (destruct c) SCase;
    simpl in H; inversion H; subst; clear H.
  SCase "SKIP". apply E_Skip.
  SCase "::=". apply E_Ass. reflexivity.
  SCase ";".
  remember (ceval_step st c1 i') as r1. destruct r1.
  SSCase "Evaluation of r1 terminates normally".
  apply E_Seq with s.
  apply IHi'. rewrite Heqr1. reflexivity.
  apply IHi'. assumption.
  SSCase "Othervise --contradiction".
  inversion H1.
  SCase "IFB".
  remember (beval st b) as r. destruct r.
  SSCase "r = true".
  apply E_IfTrue. rewrite Heqr. reflexivity.
  apply IHi'. assumption.
  SSCase "r = false".
  apply E_IfFalse. rewrite Heqr. reflexivity.
  apply IHi'. assumption.
  SCase "WHILE". remember (beval st b) as r. destruct r.
  SSCase "r = true".
  remember (ceval_step st c i') as r1. destruct r1.
  SSSCase "r1 = Some s".
  apply E_WhileLoop with s. rewrite Heqr. reflexivity.
  apply IHi'. rewrite Heqr1. reflexivity.
  apply IHi'. assumption.
  SSSCase "r1 = None".
  inversion H1.
  SSCase "r = false".
  inversion H1.
  apply E_WhileEnd. rewrite Heqr. subst.
  reflexivity.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
                               c / st || st1 ->
                               c / st || st2 ->
                               st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case; intros st2 E2; inversion E2; subst.
  Case "E_SKip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq". assert (st' = st'0) as EQ1.
  SCase "Proof of assertion". apply IHE1_1; assumption.
  subst st'0. apply IHE1_2. assumption.
  Case "E_IfTrue".
  SCase "b1 evaluates to true".
  apply IHE1. assumption.
  SCase "b1 evaluates to false (contradiction)".
  rewrite H in H5. inversion H5.
  Case "E_IfFalse".
  SCase "b1 evaluates to true (contradiction)".
  rewrite H in H5. inversion H5.
  SCase "b1 evaluates to false".
  apply IHE1. assumption.
  Case "E_WhileEnd".
  SCase "b1 evaluates to true".
  reflexivity.
  SCase "b1 evaluates to false (contradiction)".
  rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
  SCase "b1 evaluates to true (contradiction)".
  rewrite H4 in H. inversion H.
  SCase "b1 evaluates to false".
  assert (st' = st'0) as EQ1.
  SSCase "Proof of assertion". apply IHE1_1; assumption.
  subst st'0. apply IHE1_2. assumption.
Qed.

Theorem plus2_spec: forall st n st',
                      st X = n ->
                      plus2 / st || st' ->
                      st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst.
  apply update_eq.
Qed.

Theorem loop_never_stops: forall st st',
                            ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  rewrite Heqloopdef in contra. inversion contra.
  subst. inversion H3.
  subst. inversion H2. subst.
Admitted.

Fixpoint no_whiles (c: com): bool :=
  match c with
    | SKIP => true
    | _ ::= _ => true
    | c1 ; c2 => andb (no_whiles c1) (no_whiles c2)
    | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
    | WHILE _ DO _ END => false
  end.
Theorem no_whiles_termnating: forall com st,
                                no_whiles com = true ->  exists st', com / st || st'.
Proof.
  intros com st H.
  generalize dependent st.
  induction com; intros st.
  + exists st. apply E_Skip.
  + exists (update st i (aeval st a)).
    apply E_Ass. reflexivity.
  + inversion H. remember (no_whiles com1) as r.
    destruct r. simpl in H1. rewrite H1 in IHcom2.
    destruct IHcom1 with st. reflexivity.
    destruct IHcom2 with x. reflexivity.
    exists x0.
    apply E_Seq with x.
    assumption. assumption. inversion H1.
  + destruct b.
    destruct IHcom1 with st. inversion H.
    rewrite H1. unfold andb in H1. remember (no_whiles com1) as r.
    destruct r. reflexivity. inversion H1.
    exists x. apply E_IfTrue. reflexivity. assumption.
    destruct IHcom2 with st. inversion H.
    rewrite H1. unfold andb in H1. remember (no_whiles com1) as r.
    destruct r. assumption. inversion H1.
    exists x. apply E_IfFalse. reflexivity. assumption.
    remember (BEq a a0). destruct b.
Admitted.

Print fact_body.
Print fact_loop.
Print fact_com.

Fixpoint real_fact (n: nat): nat :=
  match n with
    | O => 1
    | S n' => n * (real_fact n')
  end.

Definition fact_invariant (x: nat) (st: state) :=
  (st Y) * (real_fact (st Z)) = real_fact x.

Theorem fact_body_preserves_invariant: forall st st' x,
                                         fact_invariant x st ->
                                         st Z <> 0 ->
                                         fact_body / st || st' ->
                                         fact_invariant x st'.
Proof.
  unfold fact_invariant, fact_body.
  intros st st' x Hm HZnz He.
  inversion He; subst; clear He.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  unfold update. simpl.
  destruct (st Z) as [| z'].
  apply ex_falso_quodlibet. apply HZnz. reflexivity.
  rewrite <- Hm. rewrite <- mult_assoc.
  replace (S z' - 1) with z' by omega.
  reflexivity.
Qed.

Theorem fact_loop_preserves_invariant: forall st st' x,
                                         fact_invariant x st ->
                                         fact_loop / st || st' ->
                                         fact_invariant x st'.
Proof.
  intros st st' x H Hce.
  remember fact_loop as c.
  ceval_cases (induction Hce) Case;
    inversion Heqc; subst; clear Heqc.
  Case "E_WhileEnd".
  assumption.
  Case "E_WhileLoop".
  apply IHHce2.
  apply fact_body_preserves_invariant with st;
    try assumption.
  intros contra. simpl in H0; subst.
  rewrite contra in H0. inversion H0.
  reflexivity.
Qed.

Theorem guard_false_after_loop: forall b c st st',
                                  (WHILE b DO c END) / st || st' ->
                                  beval st' b = false.
Proof.
  intros b c st st' Hce.
  remember (WHILE b DO c END) as cloop.
  ceval_cases(induction Hce) Case;
    inversion Heqcloop; subst; clear Heqcloop.
  Case "E_WhileEnd".
  assumption.
  Case "E_WhileLoop".
  apply IHHce2. reflexivity.
Qed.

Theorem fact_com_correct: forall st st' x,
                            st X = x ->
                            fact_com / st || st' ->
                            st' Y = real_fact x.
Proof.
  intros st st' x HX Hce.
  inversion Hce; subst; clear Hce.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  inversion H1; subst; clear H1.
  rename st' into st''. simpl in H5.
  remember (update (update st Z (st X)) Y 1) as st'.
  assert (fact_invariant (st X) st').
  subst. unfold fact_invariant, update. simpl. omega.
  assert (fact_invariant (st X) st'').
  apply fact_loop_preserves_invariant with st'; assumption.
  unfold fact_invariant in H0.
  apply guard_false_after_loop in H5. simpl in H5.
  destruct (st'' Z).
  Case "st'' Z = 0". simpl in H0. omega.
  Case "st'' Z > 0 (impossible)". inversion H5.
Qed.

