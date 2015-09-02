Inductive list (X: Type): Type :=
| nil: list X
| cons: X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X: Type) (l: list X): nat :=
  match l with
    | nil => 0
    | cons h t => S (length X t)
  end.

Example test_length1:
  length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.
Example test_length2:
  length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X: Type) (l1 l2: list X): (list X) :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X: Type) (l:list X) (v:X): list X :=
  match l with
    | nil => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X): list X :=
  match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
  end.

Example test_rev1: rev nat (cons nat 1 (cons nat 2 (nil nat)))
                   = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.
Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Fixpoint app' X l1 l2: list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
  end.

Check app'.
Check app.

Fixpoint length' (X:Type) (l:list X): nat :=
  match l with
    | nil => 0
    | cons h t => S (length' _ t)
  end.

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Check (length list123'').

Fixpoint length'' {X:Type} (l:list X): nat :=
  match l with
    | nil => 0
    | cons h t => S (length'' t)
  end.

Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Definition list123''' := [1, 2, 3].

Fixpoint repeat (X: Type) (n: X) (count: nat): list X :=
  match count with
    | O        => nil
    | S count' => cons n (repeat X n count')
  end.

Example test_repeat1:
  repeat bool true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app: forall X: Type, forall l:list X,
                   app [] l = l.
Proof. reflexivity. Qed.

Theorem rev_snoc: forall X: Type,
                  forall v: X,
                  forall s: list X,
                    rev (snoc s v) = v :: (rev s).
Proof.
  intros X v s.
  induction s.
  + reflexivity.
  + simpl. rewrite IHs. reflexivity.
Qed.

Theorem snoc_with_append: forall X: Type,
                          forall l1 l2: list X,
                          forall v: X,
                            snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X l1 l2 v.
  induction l1.
  + simpl. reflexivity.
  + simpl. rewrite IHl1. reflexivity.
Qed.

Inductive prod (X Y: Type): Type :=
  pair: X -> Y -> prod X Y.
Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y): type_scope.

Definition fst {X Y: Type} (p : X * Y): X :=
  match p with (x, y) => x end.
Definition snd {X Y: Type} (p : X * Y): Y :=
  match p with (x, y) => y end.

Fixpoint combine {X Y: Type} (lx: list X) (ly: list Y): list (X*Y) :=
  match (lx, ly) with
    | ([], _) => []
    | (_, []) => []
    | (x::tx, y::ty) => (x, y) :: (combine tx ty)
  end.

Check @combine.
Eval simpl in (combine [1,2] [false,false,true,true]).

Inductive option (X:Type) :Type :=
| Some: X -> option X
| None: option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O => match m with
             | O => true
             | S m' => false
           end
    | S n' => match m with
                | O => false
                | S m' => beq_nat n' m'
              end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' => match m with
                | O => false
                | S m' => ble_nat n' m'
              end
  end.


Fixpoint index {X: Type} (n: nat)
         (l: list X): option X :=
  match l with
    | [] => None
    | a :: l' => if beq_nat n 0 then Some a else index (pred n) l'
  end.

Example test_index1: index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2: index 1 [[1],[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3: index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X: Type} (l: list X): option X :=
  match l with
    | [] => None
    | a::_ => Some a
  end.

Check @hd_opt.

Example test_hd_opt1: hd_opt [1,2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2: hd_opt [[1],[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X: Type} (f:X->X) (n:X): X :=
  f (f (f n)).

Check @doit3times.

Definition minustwo (n: nat): nat := pred (pred n).

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Check plus.
Definition plus3 := plus 3.
Check plus3.
Example test_plus3: plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3': doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'': doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z: Type}
           (f: X * Y -> Z) (x: X) (y: Y): Z := f (x, y).
Definition prod_uncurry {X Y Z: Type}
           (f: X -> Y -> Z) (p: X * Y): Z :=
  f (fst p) (snd p).

Theorem uncurry_curry: forall (X Y Z: Type) (f: X -> Y -> Z) x y,
                         prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.

Theorem curry_uncurry: forall (X Y Z: Type) (f: (X * Y) -> Z) (p: X * Y),
                         prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  destruct p.
  reflexivity.
Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l: list X): (list X) :=
  match l with
    | [] => []
    | h :: t => if test h then h :: (filter test t)
                else filter test t
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition length_is_1 {X: Type} (l: list X): bool :=
  beq_nat (length l) 1.

Example test_filter2:
  filter length_is_1
         [[1, 2],[3],[4],[5,6,7],[],[8]]
  = [[3],[4],[8]].
Proof. reflexivity. Qed.

Definition countoddmembers' (l: list nat): nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2': filter (fun l => beq_nat (length l) 1)
                              [[1, 2],[3],[4],[5,6,7],[],[8]]
                       = [[3],[4],[8]].
Proof. reflexivity. Qed.

Definition partition  {X: Type} (f: X -> bool) (l: list X): list X * list X :=
  (filter f l, filter (fun x => negb (f x))  l).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f: X -> Y) (l: list X): (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (plus 3) [2, 0, 2] = [5, 3, 5].
Proof. reflexivity. Qed.

Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity. Qed.
Example test_map3:
  map (fun n => [evenb n, oddb n]) [2,1,2,5]
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity. Qed.

Theorem map_rev: forall (X Y: Type) (f: X -> Y) (l: list X),
                   map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l.
  + reflexivity.
  + Lemma snoc_map: forall (X Y: Type) (f: X -> Y) (l: list X) (x: X),
                      map f (snoc l x) = snoc (map f l) (f x).
    Proof.
      intros X Y f l x.
      induction l.
      + reflexivity.
      + simpl. rewrite IHl. reflexivity.
    Qed.
    simpl.
    rewrite snoc_map.
    rewrite IHl.
    reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f:X -> list Y) (l:list X): (list Y) :=
  match l with
    | nil   => nil
    | a::l' => (f a) ++ (flat_map f l')
  end.

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4] = [1,1,1,5,5,5,4,4,4].
Proof. reflexivity. Qed.

Definition option_map {X Y: Type} (f: X -> Y) (xo: option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y): Y :=
  match l with
    | nil => b
    | h :: t => f h (fold f t b)
  end.

Definition constfun {X: Type} (x: X): nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.
Example constfun_example1: ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example: (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X: Type} (f: nat -> X) (k: nat) (x:X): nat -> X :=
  fun (k': nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1: fmostlytrue 0 = true.
Proof. reflexivity. Qed.
Example override_example2: fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Theorem override_example: forall (b: bool),
                            (override (constfun b) 3 true) 2 = b.
Proof. reflexivity. Qed.

Theorem unfold_examle_bad: forall m n,
                             3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite H.
  reflexivity.
Qed.

Theorem override_eq: forall {X: Type} x k (f:nat -> X),
                       (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  Lemma beq_nat_refl: forall (n: nat), beq_nat n n = true.
  Proof. intros n. induction n.
         + reflexivity.
         + simpl. apply IHn.
  Qed.
  simpl.
  rewrite beq_nat_refl.
  reflexivity.
Qed.

Theorem override_neq: forall {X: Type} x1 x2 k1 k2 (f: nat -> X),
                        f k1 = x1 ->
                        beq_nat k2 k1 = false ->
                        (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f.
  intros H.
  unfold override.
  intros I.
  rewrite I.
  rewrite H.
  reflexivity.
Qed.

Theorem eq_add_S: forall (n m : nat),
                    S n = S m -> n = m.
Proof.
  intros n m eq.
  inversion eq.
  reflexivity.
Qed.

Theorem silly4: forall (n m: nat),
                  [n] = [m] -> n = m.
Proof. intros n m eq. inversion eq. reflexivity. Qed.

Theorem silly5: forall (n m o: nat),
                  [n, m] = [o, o] ->
                  [n] = [m].
Proof.
  intros n m o eq.
  inversion eq.
  reflexivity.
Qed.

Example sillyex1: forall (X: Type) (x y z: X) (l j: list X),
                    x :: y :: l  = z :: j ->
                    y :: l = x :: j ->
                    x = y.
Proof.
  intros X x y z l j.
  intros eq1.
  intros eq2.
  inversion eq2.
  reflexivity.
Qed.

Theorem silly6: forall(n: nat),
                  S n = 0 ->
                  2 + 2 = 0.
Proof.
  intros n  contra. inversion contra. Qed.


Lemma eq_remove_S: forall n m,
                     n = m -> S n = S m.
Proof.
  intros n m.
  intros eq.
  inversion eq.
  reflexivity.
Qed.

Theorem beq_nat_eq: forall n m,
                      true = beq_nat n m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  + intros m. destruct m as [| m'].
  - reflexivity.
  - simpl. intros contra. inversion contra.
    + intros m. destruct m as [| m'].
  - simpl. intros contra. inversion contra.
  - simpl. intros H. apply eq_remove_S. apply IHn'. apply H.
Qed.

Theorem beq_nat_eq': forall n m,
                       beq_nat n m = true -> n = m.
Proof.
  intros m. induction m.
  + intros n.
    induction n. simpl. reflexivity.
    simpl. intros contra. inversion contra.
  + intros n. 
    destruct n. simpl. intros contra. inversion contra.
    simpl. intros H. apply eq_remove_S. apply IHm. apply H.
Qed.

Theorem length_snoc': forall (X: Type) (v: X)
                             (l: list X) (n: nat),
                        length l = n ->
                        length (snoc l v) = S n.
Proof.
  intros X v l. induction l.
  + intros n eq. rewrite <- eq. reflexivity.
  + intros n eq. simpl. destruct n.
  - inversion eq.
  - apply eq_remove_S. apply IHl. inversion eq. reflexivity.
Qed.

Theorem beq_nat_0_l: forall n,
                       true = beq_nat 0 n -> 0 = n.
Proof.
  intros n H. induction n.
  + reflexivity.
  + inversion H.
Qed.

Theorem beq_nat_0_r: forall n,
                       true = beq_nat n 0 -> 0 = n.
Proof.
  intros n H. induction n.
  + reflexivity.
  + inversion H.
Qed.

Theorem S_inj: forall (n m: nat) (b: bool),
                 beq_nat (S n) (S m) = b ->
                 beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3': forall (n: nat),
                   (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
                   true = beq_nat n 5 -> true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. apply H.
Qed.

Definition sillyfun (n: nat): bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false: forall (n: nat),
                          sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
  + reflexivity.
  + destruct (beq_nat n 5).
    reflexivity.
    reflexivity.
Qed.

Theorem override_shadow: forall {X:Type} x1 x2 k1 k2 (f: nat -> X),
                           (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
  + reflexivity.
  + reflexivity.
Qed.

Example trans_eq_example: forall (a b c d e f: nat),
                            [a,b] = [c,d] ->
                            [c,d] = [e,f] ->
                            [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

Definition fold_length {X: Type} (l: list X): nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1: fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct: forall X (l: list X),
                               fold_length l = length l.
Proof.
  intros X l.
  induction l.
  + simpl. unfold fold_length. simpl. reflexivity.
  + simpl. unfold fold_length. simpl. unfold fold_length in IHl.
    apply eq_remove_S. apply IHl.
Qed.


Theorem plus_n_n_injective: forall n m,
                              n + n = m + m -> n = m.
Proof.
  intros n. induction n.
  + simpl. intros m. induction m.
  -reflexivity.
  - intros H. inversion H.
    + intros m. induction m.
  -  intros H. simpl in H. inversion H.
  - intros H.
    apply eq_remove_S. apply IHn.
    simpl in H. apply eq_add_S in H.
    

    Lemma plus_succ: forall (n m: nat),
                       n + S m = S (n + m).
    Proof.
      intros n. induction n.
      + intros m. simpl.  reflexivity.
      + intros m. simpl.
        apply eq_remove_S.
        apply IHn.
    Qed.
    Lemma plus_succ2: forall (n m: nat),
                        n + S n = m + S m -> n + n = m + m.
    Proof.
      intros n. induction n.
      + intros m H. simpl.
        simpl in H.
        rewrite plus_succ in H.
        apply eq_add_S.
        apply H.
      + intros m H.
        rewrite plus_succ in H.
        rewrite plus_succ in H.
        rewrite plus_succ in H.
        apply eq_add_S in H.
        simpl.
        rewrite plus_succ.
        apply H.
    Qed.
    simpl.
    rewrite plus_succ in H.
    rewrite plus_succ in H.
    apply eq_add_S in H.
    apply H.
Qed.

Theorem plus_n_n_injective_take2: forall n m,
                                    n + n = m + m ->
                                    n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  + intros n H. induction n.
  - reflexivity.
  - simpl in H. simpl in IHn. inversion H.
    + intros n H. induction n.
  - inversion H.
  - simpl in H.
    apply eq_add_S in H.
    rewrite plus_succ in H.
    rewrite plus_succ in H.
    apply eq_add_S in H.
    apply IHm in H.
    rewrite H. reflexivity.
Qed.

Theorem index_afetr_last: forall (n: nat) (X: Type) (l: list X),
                            length l = n -> index (S n) l = None.
Proof.
  intros n X l.
  generalize dependent n.
  generalize dependent X.
  induction l.
  +  reflexivity.
  +  intros n H. 
     simpl. destruct l.
     - unfold length in H. rewrite <- H.
     unfold index.
     reflexivity.
     - destruct n.
       inversion H.
       apply IHl.
       inversion H.
       induction l.
       simpl. reflexivity.
       simpl. reflexivity.
Qed.

Theorem length_snoc_''': forall (n: nat) (X: Type) (v: X) (l: list X),
                           length l = n -> length (snoc l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  generalize dependent v.
  induction l.
  + intros v n H.
    simpl.
    simpl in H.
    rewrite H.
    reflexivity.
  + intros v n H.
    simpl.
    destruct n.
  - inversion H.
  - apply eq_remove_S.
    apply IHl.
    inversion H.
    reflexivity.
Qed.


Theorem app_length_cons: forall(X: Type) (l1 l2: list X) (x: X) (n: nat),
                           length (l1 ++ (x :: l2)) = n ->
                           S (length (l1 ++ l2)) = n.
Proof.
  intros X l1. induction l1.
  + simpl. intros l2 x n H.
    apply H.
  + simpl. intros l2 x' n H.
    destruct n.
  - inversion H.
  - apply eq_add_S in H.
    apply IHl1 in H.
    apply eq_remove_S.
    apply H.
Qed.

