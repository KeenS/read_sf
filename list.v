Module NatList.
  Inductive natprod : Type :=
    pair : nat -> nat -> natprod.

  Definition fst (p : natprod) : nat :=
    match p with
      | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
      | pair x y => y
    end.

  Notation "( x , y )" := (pair x y).

  Definition swap_pair (p : natprod) : natprod :=
    match p with
      | (x,y) => (y,x)
    end.

  Theorem surjective_paring' : forall (n m : nat),
                                 (n, m) = (fst (n,m), snd(n,m)).
  Proof.
    reflexivity.
  Qed.

  Theorem surjective_pairing_stuck : forall (p : natprod),
                                       p = (fst p, snd p).
  Proof.
    intros p.
    destruct p.
    simpl.
    reflexivity.
  Qed.

  Theorem snd_fst_is_swap : forall (p :natprod),
                              (snd p, fst p) = swap_pair p.
  Proof.
    intros p.
    destruct p. simpl.
    reflexivity.
  Qed.

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
      | O => nil
      | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l: natlist) : nat :=
    match l with
      | nil => 0
      | l :: t => S (length t)
    end.

  Fixpoint app (l1 l2: natlist) : natlist :=
    match l1 with
      | nil => l2
      | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y) (right associativity, at level 60).

  Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
  Proof. reflexivity. Qed.
  Example test_app2: nil ++ [4,5] =[4,5].
  Proof. reflexivity. Qed.
  Example test_app3: [1,2,3] ++ nil = [1,2,3].
  Proof. reflexivity. Qed.

  Definition hd (default:nat) (l:natlist) : nat :=
    match l with
      | nil => default
      | h :: t => h
    end.

  Definition tail (l: natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t => t
    end.

  Fixpoint nonzeros (l: natlist) : natlist :=
    match l with
      | nil => nil
      | 0 :: tl => nonzeros tl
      | hd :: tl => hd :: nonzeros tl
    end.
  Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
  Proof. reflexivity. Qed.

  Fixpoint even (n : nat) : bool :=
    match n with
      | O => true
      | S n' => negb (even n')
    end.

  Fixpoint odd (n : nat) : bool :=
    negb (even n).

  Fixpoint oddmembers (l: natlist) : natlist :=
    match l with
      | nil => nil
      | hd :: tl => match odd hd with
                      | false => oddmembers tl
                      | true => hd :: oddmembers tl
                    end
    end.

  Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
  Proof. reflexivity. Qed.

  Fixpoint countoddmembers (l:natlist) : nat :=
    match l with
      | nil => O
      | hd :: tl => match odd hd with
                      | false => countoddmembers tl
                      | true  => 1 + (countoddmembers tl)
                    end
    end.

  Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
  Proof. reflexivity. Qed.
  Example test_countoddmembers2: countoddmembers [0,2,4] = 0.
  Proof. reflexivity. Qed.
  Example test_countoddmembers3: countoddmembers nil = 0.
  Proof. reflexivity. Qed.

  Fixpoint alternate (l1 l2: natlist) :natlist :=
    match l1, l2 with
      | nil, l2' => l2'
      | l1', nil => l1'
      | hd1 :: tl1, hd2 :: tl2  => hd1 :: hd2 :: (alternate tl1 tl2)
    end.

  Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
  Proof. reflexivity. Qed.
  Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
  Proof. reflexivity. Qed.
  Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
  Proof. reflexivity. Qed.
  Example test_alternate4: alternate [] [20,30] = [20,30].
  Proof. reflexivity. Qed.

  Definition bag := natlist.

  Fixpoint neq (n m: nat): bool :=
    match n, m with
      | O, O      => true
      | O, _      => false
      | _, O      => false
      | S n', S m' => neq n' m'
    end.

  Fixpoint count (v: nat) (s: bag) : nat :=
    match s with
      | nil => 0
      | hd :: tl => match neq hd v with
                      | true  => 1 + (count v tl)
                      | false => (count v tl)
                    end
    end.

  Example test_count1: count 1 [1,2,3,1,4,1] = 3.
  Proof. reflexivity. Qed.
  Example test_count2: count 6 [1,2,3,1,4,1] = 0.
  Proof. reflexivity. Qed.

  Definition sum : bag -> bag -> bag := app.

  Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
  Proof. reflexivity. Qed.

  Definition add (v: nat) (s: bag): bag := v :: s.

  Example test_add1: count 1 (add 1 [1,4,1]) = 3.
  Proof. reflexivity. Qed.
  Example test_add2: count 5 (add 1 [1,4,1]) = 0.
  Proof. reflexivity. Qed.

  Fixpoint nge (n m: nat) :=
    match n, m with
      | O, O => true
      | S _, O => true
      | O, S _ => false
      | S n', S m' => nge n' m'
    end.
  

  Definition member (v: nat) (s: bag) : bool := nge (count v s) 1.

  Example test_member1: member 1 [1,4,1] = true.
  Proof. reflexivity. Qed.
  Example test_member2: member 2 [1,4,1] = false.
  Proof. reflexivity. Qed.

  Fixpoint remove_one (v: nat) (s: bag) : bag :=
    match s with
      | nil => nil
      | hd :: tl => match neq v hd with
                      | true  => tl
                      | false => hd :: remove_one v tl
                    end
    end.

  Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_one4:
    count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
  Proof. reflexivity. Qed.

  Fixpoint remove_all (v: nat) (s: bag) :bag :=
    match s with
      | nil => nil
      | hd :: tl => match neq v hd with
                      | true  => remove_all v tl
                      | false => hd :: remove_all v tl
                    end
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
  Proof. reflexivity. Qed.

  Fixpoint subset (s1: bag) (s2: bag) :bool :=
    match  s1, s2 with
      | nil, _  => true
      | _ , nil => false
      | s1', hd :: tl => subset (remove_one hd s1') tl
    end.

  Example test_subset1: subset [1,2] [2,1,4,1] = true.
  Proof. reflexivity. Qed.
  Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
  Proof. reflexivity. Qed.

  Theorem nil_app : forall l:natlist,
                      [] ++ l = l.
  Proof. reflexivity. Qed.

  Theorem tl_length_pred : forall l: natlist,
                             pred (length l) = length (tail l).
  Proof.
    intros l. destruct l as [| n l'].
    reflexivity.
    reflexivity.
  Qed.

  Theorem app_ass: forall l1 l2 l3 : natlist,
                     (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. induction l1 as [| n l1'].
    + reflexivity.
    + simpl. rewrite IHl1'. reflexivity.
  Qed.

  Theorem app_length : forall l1 l2: natlist,
                         length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2.
    induction l1 as [| n l1'].
    + reflexivity.
    + simpl. rewrite IHl1'. reflexivity.
  Qed.

  Fixpoint snoc (l: natlist) (v: nat) :natlist :=
    match l with
      | nil => [v]
      | h :: t => h :: (snoc t v)
    end.

  Fixpoint rev (l: natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t => snoc (rev t) h
    end.

  Example test_rev1: rev [1,2,3] = [3,2,1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem length_snoc: forall n : nat, forall l: natlist,
                         length (snoc l n) = S (length l).
  Proof.
    intros n l.
    induction l as [| m l'].
    + reflexivity.
    + simpl. rewrite IHl'. reflexivity.
  Qed.      

  Theorem rev_length_first: forall l :natlist,
                              length (rev l) = length l.
  Proof.
    intros l. induction l as [| n l'].
    + simpl. reflexivity.
    + simpl. rewrite length_snoc. rewrite IHl'. reflexivity.
  Qed.

  Theorem app_nil_end: forall l : natlist,
                         l ++ [] = l.
  Proof.
    intros l.
    induction l.
    + reflexivity.
    + simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma snoc_rev: forall l: natlist, forall n: nat, rev (snoc l n) = n :: (rev l).
  Proof.
    intros l n.
    induction l.
    + reflexivity.
    + simpl.
      rewrite IHl.
      reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
                             rev (rev l) = l.
  Proof.
    intros l.
    induction l.
    + reflexivity.
    + simpl.
      rewrite snoc_rev.
      rewrite IHl.
      reflexivity.
  Qed.

  Theorem rev_snoc: forall l: natlist, forall n: nat,
                      snoc (rev l) n = rev (n :: l).
  Proof.
    intros l n.
    induction l.
    + reflexivity.
    + reflexivity.
  Qed.

  Lemma snoc_app: forall n: nat, forall l1 l2: natlist,
                    l1 ++ snoc l2 n = snoc (l1 ++ l2) n.
  Proof.
    intros n l1 l2.
    induction l1.
    + reflexivity.
    + simpl. rewrite IHl1. reflexivity.
  Qed.

  Theorem distr_rev: forall l1 l2: natlist,
                       rev (l1 ++ l2) = (rev l2) ++ (rev l1).
  Proof.
    intros l1 l2.
    induction l1.
    + induction l2.
    - reflexivity.
    - simpl. rewrite app_nil_end. reflexivity.
      + simpl.
        rewrite IHl1.
        rewrite snoc_app.
        reflexivity.
  Qed.

  Theorem app_ass4: forall l1 l2 l3 l4: natlist,
                      l1 ++ (l2 ++ l3 ++ l4) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite app_ass.
    rewrite app_ass.
    reflexivity.

    Theorem snoc_append: forall (l: natlist) (n: nat),
                           snoc l n = l ++ [n].
    Proof.
      intros l n.
      induction l.
      + reflexivity.
      + simpl. rewrite IHl. reflexivity.
    Qed.

    Lemma nonzeros_length: forall l1 l2: natlist,
                             nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
    Proof.
      intros l1 l2.
      induction l1.
      + reflexivity.
      + simpl. rewrite IHl1.
        induction l2.
      - simpl. rewrite app_nil_end.
        destruct n.
        * rewrite app_nil_end. reflexivity.
        * rewrite app_nil_end. reflexivity.
      - simpl. destruct n.
        *  reflexivity.
        * simpl. reflexivity.
    Qed.

    Theorem nil_rev: rev [] = [].
    Proof.
      reflexivity.
    Qed.

    Inductive natoption: Type :=
    | Some : nat -> natoption
    | None : natoption.

    Fixpoint index (n: nat) (l:natlist): natoption :=
      match l with
        | nil => None
        | a :: l' => match neq n 0 with
                       | true => Some a
                       | false => index (pred n) l'
                     end
      end.

    Example test_index1 : index 0 [4,5,6,7] = Some 4.
    Proof. reflexivity. Qed.
    Example test_index2 : index 3 [4,5,6,7] = Some 7.
    Proof. reflexivity. Qed.
    Example test_index3 : index 10 [4,5,6,7] = None.
    Proof. reflexivity. Qed.

    Definition option_elim (o : natoption) (d: nat): nat :=
      match o with
        | Some n' => n'
        | None => d
      end.

    Definition hd_opt (l: natlist): natoption :=
      match l with
        | nil => None
        | a :: _ => Some a
      end.

    Example test_hd_opt1 : hd_opt [] = None.
    Proof. reflexivity. Qed.
    Example test_hd_opt2 : hd_opt [1] = Some 1.
    Proof. reflexivity. Qed.
    Example test_hd_opt3 : hd_opt [5,6] = Some 5.
    Proof. reflexivity. Qed.

    Theorem option_elim_hd: forall (l: natlist) (default: nat),
                              hd default l = option_elim (hd_opt l) default.
    Proof.
      intros l default.
      destruct l.
      + simpl. reflexivity.
      + simpl. reflexivity.
    Qed.

    Fixpoint beq (n m: nat): bool:=
      match n, m with
        | O, O => true
        | S n', S m' => beq n' m'
        | _ ,_ => false
      end.

    Fixpoint beq_natlist (l1 l2: natlist): bool :=
      match l1, l2 with
        | nil, nil => true
        | a::l1', b::l2' => match beq a b with
                              | true => beq_natlist l1' l2'
                              | false => false
                            end
        |  _, _ => false
      end.

    Example test_beq_natlist1 : (beq_natlist nil nil = true).
    Proof. reflexivity. Qed.
    Example test_beq_natlist2 : beq_natlist [1,2,3] [1,2,3] = true.
    Proof. reflexivity. Qed.
    Example test_beq_natlist3 : beq_natlist [1,2,3] [1,2,4] = false.
    Proof. reflexivity. Qed.

    Theorem beq_natlist_refl: forall l: natlist,
                                true = beq_natlist l l.
    Proof.
      intros l.
      induction l.
      + reflexivity.
      + simpl. rewrite IHl.
        induction n.
      - simpl. reflexivity.
      - simpl. rewrite <- IHn. reflexivity.
    Qed.

    Theorem silly1: forall (n m o p: nat),
                      n = m ->
                      [n, o] = [n, p] ->
                      [n, o] = [m, p].
    Proof.
      intros n m o p eq1 eq2.
      rewrite <- eq1.
      apply eq2.
    Qed.

    Theorem silly2: forall (n m o p:nat),
                      n = m ->
                      (forall (q r: nat), q = r -> [q, o] = [r, p]) ->
                      [n, o] = [m, p].
    Proof.
      intros n m o p eq1 eq2.
      apply eq2. apply eq1.
    Qed.

    Theorem silly_ex:
      (forall n, even n = true -> odd (S n) = true) ->
      even 3 = true ->
      odd 4 = true.
    Proof.
      intros.
      apply H.
      apply H0.
    Qed.

    Theorem silly3: forall (n: nat),
                      true = neq n 5 ->
                      neq (S (S n)) 7 = true.
    Proof.
      intros n H.
      symmetry.
      apply H.
    Qed.

    Theorem rev_exercise1: forall (l l': natlist),
                             l = rev l' ->
                             l' = rev l.
    Proof.
      intros l l' H.
      symmetry.
      rewrite H.
      apply rev_involutive.
    Qed.

    Theorem rev_ass': forall l1 l2 l3: natlist,
                        (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
      intros l1.
      induction l1.
      + reflexivity.
      + intros l2 l3.
        simpl.
        assert(H: (l1++l2)++l3 = l1++l2++l3).
        apply IHl1.
        rewrite H.
        reflexivity.
    Qed.

    Definition beq_nat (n m: nat): bool := neq n m.

    Theorem beq_nat_sym: forall (n m: nat),
                           beq_nat n m = beq_nat m n.
    Proof.
      intros n. induction n as [| n'].
      + destruct m. reflexivity.
        simpl. reflexivity.
      +  destruct m.
      - simpl. reflexivity.
      - simpl. apply IHn'.
    Qed.
  Qed.
End NatList.