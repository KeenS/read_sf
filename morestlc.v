Require Export Stlc_J.
Require Import Relations.

Module STLCExtended.

  Inductive ty: Type :=
| ty_arrow: ty -> ty -> ty
| ty_prod: ty -> ty -> ty
| ty_sum: ty -> ty -> ty
| ty_List: ty -> ty
| ty_Nat: ty.

  Tactic Notation "ty_cases" tactic(first) ident(c) :=
    first;
    [Case_aux c "ty_arrow"
    | Case_aux c "ty_prod"
    | Case_aux c "ty_sum"
    | Case_aux c "ty_List"
    | Case_aux c "ty_Nat"].

  Inductive tm: Type :=
  | tm_var: id -> tm
  | tm_app: tm -> tm -> tm
  | tm_abs: id -> ty -> tm -> tm
  | tm_pair: tm -> tm -> tm
  | tm_fst: tm -> tm
  | tm_snd: tm -> tm
  | tm_inl: ty -> tm -> tm
  | tm_inr: ty -> tm -> tm
  | tm_case: tm -> id -> tm -> id -> tm -> tm
  | tm_nil: ty -> tm
  | tm_cons: tm -> tm -> tm
  | tm_lcase: tm -> tm -> id -> id -> tm -> tm
  | tm_nat: nat -> tm
  | tm_succ: tm -> tm
  | tm_pred: tm -> tm
  | tm_mult: tm -> tm -> tm
  | tm_if0: tm -> tm -> tm -> tm
  | tm_let: id -> tm -> tm -> tm
  | tm_fix: tm -> tm.

  Tactic Notation "tm_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "tm_var" | Case_aux c "tm_app" | Case_aux c "tm_abs"
      | Case_aux c "tm_pair" | Case_aux c "tm_fst" | Case_aux c "tm_snd"
      | Case_aux c "tm_inl" | Case_aux c "tm_inr" | Case_aux c "tm_case"
      | Case_aux c "tm_nil" | Case_aux c "tm_cons" | Case_aux c "tm_lcase"
      | Case_aux c "tm_nat" | Case_aux c "tm_succ" | Case_aux c "tm_pred"
      | Case_aux c "tm_mult" | Case_aux c "tm_if0"
      | Case_aux c "tm_let" | Case_aux c "tm_fix" ].

  Fixpoint subst (x:id) (s:tm) (t:tm) :tm :=
    match t with
      | tm_var y =>
        if beq_id x y then s else t
      | tm_abs y T t1 =>
        tm_abs y T (if beq_id x y then t1 else (subst x s t1))
      | tm_app t1 t2 =>
        tm_app (subst x s t1) (subst x s t2)
      | tm_pair t1 t2 =>
        tm_pair (subst x s t1) (subst x s t2)
      | tm_fst t1 =>
        tm_fst (subst x s t1)
      | tm_snd t1 =>
        tm_snd (subst x s t1)
      | tm_inl T t1 =>
        tm_inl T (subst x s t1)
      | tm_inr T t1 =>
        tm_inr T (subst x s t1)
      | tm_case t' yl tl yr tr =>
        tm_case (subst x s t')
                yl (if beq_id x yl then tl else (subst x s tl))
                yr (if beq_id x yr then tr else (subst x s tr))
      | tm_nil T =>
        t
      | tm_cons t1 t2 =>
        tm_cons (subst x s t1) (subst x s t2)
      | tm_lcase t' tnil yhd ytl tcons =>
        tm_lcase (subst x s t') (subst x s tnil) yhd ytl 
                 (if orb (beq_id ytl x) (beq_id yhd x)
                  then tcons
                  else (subst x s tcons))
      | tm_nat n =>
        t
      | tm_succ t1 =>
        tm_succ (subst x s t1)
      | tm_pred t1 =>
        tm_pred (subst x s t1)
      | tm_mult t1 t2 =>
        tm_mult (subst x s t1) (subst x s t2)
      | tm_if0 t1 t2 t3 =>
        tm_if0 (subst x s t1) (subst x s t2) (subst x s t3)
      | tm_let y t1 t2 =>
        tm_let y (subst x s t1) (if beq_id x y then t2 else (subst x s t2))
      | tm_fix t1 =>
        tm_fix (subst x s t1)
    end.


  Inductive value: tm -> Prop :=
  | v_abs: forall x T11 t12,
             value (tm_abs x T11 t12)
  | v_pair: forall t1 t2,
                     value t1 -> value t2 -> value (tm_pair t1 t2)
  | v_suml: forall t1 T,
              value t1 -> value (tm_inl T t1)
  | v_sumr: forall t1 T,
              value t1 -> value (tm_inr T t1)
  | v_nil: forall T,
             value (tm_nil T)
  | v_cons: forall t1 t2,
              value t1 -> value t2 -> value (tm_cons t1 t2)
  | v_nat: forall n,
             value (tm_nat n).

  Hint Constructors value.

  Reserved Notation "t1 '==>' t2" (at level 40).
  Inductive step: tm -> tm -> Prop :=
  | ST_AppAbs: forall x T11 t12 v2,
                 value v2 ->
                 (tm_app (tm_abs x T11 t12) v2) ==> (subst x v2 t12)
  | ST_App1: forall t1 t1' t2,
               t1 ==> t1' ->
               (tm_app t1 t2) ==> (tm_app t1' t2)
  | ST_App2: forall v1 t2 t2',
               value v1 ->
               t2 ==> t2' ->
               (tm_app v1 t2) ==> (tm_app v1 t2')
  | ST_Pair1: forall t1 t1' t2,
                t1 ==> t1' ->
                (tm_pair t1 t2) ==> (tm_pair t1' t2)
  | ST_Pair2: forall v1 t2 t2',
                value v1 ->
                t2 ==> t2' ->
                (tm_pair v1 t2) ==> (tm_pair v1 t2')
  | ST_Fst1: forall t1 t1',
               t1 ==> t1' ->
               (tm_fst t1) ==> (tm_fst t1')
  | ST_FstPair: forall t1 t2,
               value (tm_pair t1 t2) ->
               tm_fst (tm_pair t1 t2) ==> t1
  | ST_Snd1: forall t1 t1',
               t1 ==> t1' ->
               (tm_snd t1) ==> (tm_snd t1')
  | ST_SndPair: forall t1 t2,
               value (tm_pair t1 t2) ->
               tm_snd (tm_pair t1 t2) ==> t2
  | ST_Inl: forall T t1 t1',
               t1 ==> t1' ->
               (tm_inl T t1) ==> (tm_inl T t1')
  | ST_Inr: forall T t1 t1',
               t1 ==> t1' ->
               (tm_inr T t1) ==> (tm_inr T t1')
  | ST_Case: forall t t' x1 t1 x2 t2,
                t ==> t' ->
                (tm_case t x1 t1 x2 t2) ==> (tm_case t' x1 t1 x2 t2)
  | ST_CaseInl: forall T t x1 t1 x2 t2,
                value (tm_inl T t) ->
                (tm_case (tm_inl T t) x1 t1 x2 t2) ==> (subst x1 t t1)
  | ST_CaseInr: forall T t x1 t1 x2 t2,
                value (tm_inr T t) ->
                (tm_case (tm_inr T t) x1 t1 x2 t2) ==> (subst x2 t t2)
  | ST_Cons1: forall t1 t1' t2,
               t1 ==> t1' ->
               (tm_cons t1 t2) ==> (tm_cons t1' t2)
  | ST_Cons2: forall v1 t2 t2',
                value v1 ->
                t2 ==> t2' ->
                (tm_cons v1 t2) ==> (tm_cons v1 t2')
  | ST_LCase1: forall t t' tnil xcons1 xcons2 tcons,
                t ==> t' ->
                (tm_lcase t tnil xcons1 xcons2 tcons) ==> (tm_lcase t' tnil xcons1 xcons2 tcons)
  | ST_LCaseNil: forall T tnil xcons1 xcons2 tcons,
                (tm_lcase (tm_nil T) tnil xcons1 xcons2 tcons) ==> tnil
  | ST_LCaseCons: forall t1 t2 tnil xcons1 xcons2 tcons,
                value (tm_cons t1 t2) ->
                (tm_lcase (tm_cons t1 t2) tnil xcons1 xcons2 tcons) ==> (subst xcons1 t1 (subst xcons2 t2 tcons))
  | ST_Succ1: forall t t',
                t ==> t' ->
                (tm_succ t) ==> (tm_succ t')
  | ST_Succ2: forall n,
                (tm_succ (tm_nat n)) ==> tm_nat (1 + n)
  | ST_Pred1: forall t t',
                t ==> t' ->
                (tm_pred t) ==> (tm_pred t')
  | ST_Pred2: forall n,
                (tm_pred (tm_nat (S n))) ==> tm_nat n
  | ST_PredZero: (tm_pred (tm_nat 0)) ==> (tm_nat 0)
  | ST_Mult1: forall t1 t1' t2,
                t1 ==> t1' ->
                (tm_mult t1 t2) ==> (tm_mult t1' t2)
  | ST_Mult2: forall v1 t2 t2',
                value v1 ->
                t2 ==> t2' ->
                (tm_mult v1 t2) ==> (tm_mult v1 t2')
  | ST_Mult3: forall n1 n2,
                (tm_mult (tm_nat n1) (tm_nat n2)) ==> (tm_nat (n1 * n2))
  | ST_If01: forall t1 t1' t2 t3,
                  t1 ==> t1' ->
                  (tm_if0 t1 t2 t3) ==> (tm_if0 t1' t2 t3)
  | ST_If0Zero: forall t2 t3,
                  (tm_if0 (tm_nat 0) t2 t3) ==> t2
  | ST_If0NonZero: forall n t2 t3,
                     n <> 0 ->
                     (tm_if0 (tm_nat n) t2 t3) ==> t3
  | ST_Let1: forall x t1 t1' t2,
               t1 ==> t1' ->
               (tm_let x t1 t2) ==> (tm_let x t1' t2)
  | ST_LetValue: forall x t1 t2,
               value t1 ->
               (tm_let x t1 t2) ==> (subst x t1 t2)
  | ST_Fix1: forall t t',
              t ==> t' ->
              (tm_fix t) ==> (tm_fix t')
  | ST_FixAbs: forall x T t,
      (tm_fix (tm_abs x T t)) ==> (subst x (tm_fix (tm_abs x T t)) t)
  where "t1 ==> t2" := (step t1 t2).

  Tactic Notation "step_cases" tactic(first) ident(c) :=
         first;
    [
      Case_aux c "ST_AppAbs"
    | Case_aux c "ST_App1"
    | Case_aux c "ST_App2"
    | Case_aux c "ST_Pair1"
    | Case_aux c "ST_Pair2"
    | Case_aux c "ST_Fst1"
    | Case_aux c "ST_FstPair"
    | Case_aux c "ST_Snd1"
    | Case_aux c "ST_SndPair"
    | Case_aux c "ST_Inl"
    | Case_aux c "ST_Inr"
    | Case_aux c "ST_Case"
    | Case_aux c "ST_CaseInl"
    | Case_aux c "ST_CaseInr"
    | Case_aux c "ST_Cons1"
    | Case_aux c "ST_Cons2"
    | Case_aux c "ST_LCase1"
    | Case_aux c "ST_LCaseNil"
    | Case_aux c "ST_LCaseCons"
    | Case_aux c "ST_Succ1"
    | Case_aux c "ST_Succ2"
    | Case_aux c "ST_Pred1"
    | Case_aux c "ST_Pred2"
    | Case_aux c "ST_PredZero"
    | Case_aux c "ST_Mult1"
    | Case_aux c "ST_Mult2"
    | Case_aux c "ST_Mult3"
    | Case_aux c "ST_If01"
    | Case_aux c "ST_If0Zero"
    | Case_aux c "ST_If0NonZero"
    | Case_aux c "ST_Let1"
    | Case_aux c "ST_LetValue"
    | Case_aux c "ST_Fix1"
    | Case_aux c "ST_FixAbs"
    ].

  Notation stepmany := (refl_step_closure step).
  Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

  Hint Constructors step.

  Definition context := partial_map ty.

  Inductive has_type: context -> tm -> ty -> Prop :=
  | T_Var: forall Gamma x T,
             Gamma x = Some T ->
             has_type Gamma (tm_var x) T
  | T_Abs: forall Gamma x T11 T12 t12,
             has_type (extend Gamma x T11) t12 T12 ->
             has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App: forall Gamma T1 T2 t1 t2,
             has_type Gamma t1 (ty_arrow T1 T2) ->
             has_type Gamma t2 T1 ->
             has_type Gamma (tm_app t1 t2) T2
  | T_Pair: forall Gamma T1 T2 t1 t2,
              has_type Gamma t1 T1 ->
              has_type Gamma t2 T2 ->
              has_type Gamma (tm_pair t1 t2) (ty_prod T1 T2)
  | T_Fst: forall Gamma T1 T2 t1,
             has_type Gamma t1 (ty_prod T1 T2) ->
             has_type Gamma (tm_fst t1) T1
  | T_Snd: forall Gamma T1 T2 t1,
             has_type Gamma t1 (ty_prod T1 T2) ->
             has_type Gamma (tm_snd t1) T2
  | T_Inl: forall Gamma T1 T2 t,
             has_type Gamma t T1 ->
             has_type Gamma (tm_inl T2 t) (ty_sum T1 T2)
  | T_Inr: forall Gamma T1 T2 t,
             has_type Gamma t T2 ->
             has_type Gamma (tm_inr T1 t) (ty_sum T1 T2)
  | T_Case: forall Gamma T1 T2 T t v1 t1 v2 t2,
              has_type Gamma t (ty_sum T1 T2) ->
              has_type (extend Gamma v1 T1) t1 T ->
              has_type (extend Gamma v2 T2) t2 T ->
              has_type Gamma (tm_case t v1 t1 v2 t2) T
  | T_Nil: forall Gamma T,
             has_type Gamma (tm_nil T) (ty_List T)
  | T_Cons: forall Gamma T t1 t2,
              has_type Gamma t1 T ->
              has_type Gamma t2 (ty_List T) ->
              has_type Gamma (tm_cons t1 t2) (ty_List T)
  | T_Lcase: forall Gamma t1 T1 t2 T vh vt t3,
               has_type Gamma t1 (ty_List T1) ->
               has_type Gamma t2 T ->
               has_type (extend (extend Gamma vh T1) vt (ty_List T1)) t3 T ->
               has_type Gamma (tm_lcase t1 t2 vh vt t3) T
  | T_Nat: forall Gamma n,
             has_type Gamma (tm_nat n) ty_Nat
  | T_Succ: forall Gamma n,
              has_type Gamma n ty_Nat ->
              has_type Gamma (tm_succ n) ty_Nat
  | T_Pred: forall Gamma n,
              has_type Gamma n ty_Nat ->
              has_type Gamma (tm_pred n) ty_Nat
  | T_Mult: forall Gamma n m,
              has_type Gamma n ty_Nat ->
              has_type Gamma m ty_Nat ->
              has_type Gamma (tm_mult n m) ty_Nat
  | T_If0: forall Gamma T tc tt te,
            has_type Gamma tc ty_Nat ->
            has_type Gamma tt T ->
            has_type Gamma te T ->
            has_type Gamma (tm_if0 tc tt te) T
  | T_Let: forall Gamma T1 T v t1 t,
             has_type Gamma t1 T1 ->
             has_type (extend Gamma v T1) t T ->
             has_type Gamma (tm_let v t1 t) T
  | T_Fix: forall Gamma t T,
             has_type Gamma t (ty_arrow T T) ->
             has_type Gamma (tm_fix t) T.


  Hint Constructors has_type.
  Tactic Notation "has_type_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "T_Var"
    | Case_aux c "T_Abs"
    | Case_aux c "T_App"
    | Case_aux c "T_Pair"
    | Case_aux c "T_Fst"
    | Case_aux c "T_Snd"
    | Case_aux c "T_Inl"
    | Case_aux c "T_Inr"
    | Case_aux c "T_Case"
    | Case_aux c "T_Nil"
    | Case_aux c "T_Cons"
    | Case_aux c "T_Lcase"
    | Case_aux c "T_Nat"
    | Case_aux c "T_Succ"
    | Case_aux c "T_Pred"
    | Case_aux c "T_Mult"
    | Case_aux c "T_If0"
    | Case_aux c "T_Let"
    | Case_aux c "T_Fix"
    ].


  Module Examples.
    Notation a := (Id 0).
    Notation f := (Id 1).
    Notation g := (Id 2).
    Notation l := (Id 3).
    Notation k := (Id 6).
    Notation i1 := (Id 7).
    Notation i2 := (Id 8).
    Notation x := (Id 9).
    Notation y := (Id 10).
    Notation processSum := (Id 11).
    Notation n := (Id 12).
    Notation eq := (Id 13).
    Notation m := (Id 14).
    Notation evenodd := (Id 15).
    Notation even := (Id 16).
    Notation odd := (Id 17).
    Notation eo := (Id 18).

    Hint Extern 2 (has_type _ (tm_app _ _) _) =>
    eapply T_App; auto.

    Hint Extern 2 (has_type _ (tm_lcase _ _ _ _ _) _) =>
    eapply T_Lcase; auto.


    Hint Extern 2 (_ = _) => compute; reflexivity.

    Module Numtest.
      Definition test :=
        tm_if0
          (tm_pred
             (tm_succ
                (tm_pred
                   (tm_mult
                      (tm_nat 2)
                      (tm_nat 0)))))
          (tm_nat 5)
          (tm_nat 6).

      Example typechecks: has_type (@empty ty) test ty_Nat.
      Proof.
        unfold test.
        auto 10.
      Qed.

      Example numtest_reduces:
        test ==>* tm_nat 5.
      Proof.
        unfold test.
        normalize.
      Qed.

    End Numtest.

    Module Prodtest.
      Definition test :=
        tm_snd
          (tm_fst
             (tm_pair
                (tm_pair
                   (tm_nat 5)
                   (tm_nat 6))
                (tm_nat 7))).
      Example typechecks:
        has_type (@empty ty) test ty_Nat.
      Proof.
        unfold test.
        eauto 15.
      Qed.

      Example reduces:
        test ==>* tm_nat 6.
      Proof.
        unfold test.
        normalize.
      Qed.


    End Prodtest.

    Module LetTest.
      Definition test :=
        tm_let
          x
          (tm_pred (tm_nat 6))
          (tm_succ (tm_var x)).

      Example typechecks:
        has_type (@empty ty) test ty_Nat.
      Proof.
        unfold test.
        eauto 15.
      Qed.

      Example reduces:
        test ==>* tm_nat 6.
      Proof.
        unfold test.
        normalize.
      Qed.

    End LetTest.


    Module Sumtest1.
      Definition test :=
        tm_case (tm_inl ty_Nat (tm_nat 5))
                x (tm_var x)
                y (tm_var y).

      Example typechecks:
        has_type (@empty ty) test ty_Nat.
      Proof.
        unfold test.
        eauto 15.
      Qed.

      Example reduces:
        test ==>* (tm_nat 5).
      Proof.
        unfold test.
        normalize.
      Qed.
    End Sumtest1.

    Module Sumtest2.
      Definition test :=
        tm_let
          processSum
          (tm_abs x (ty_sum ty_Nat ty_Nat)
                  (tm_case (tm_var x)
                           n (tm_var n)
                           n (tm_if0 (tm_var n) (tm_nat 1) (tm_nat 0))))
          (tm_pair
             (tm_app (tm_var processSum) (tm_inl ty_Nat (tm_nat 5)))
             (tm_app (tm_var processSum) (tm_inr ty_Nat (tm_nat 5)))).

      Example typechecks:
        has_type (@empty ty) test (ty_prod ty_Nat ty_Nat).
      Proof.
        unfold test.
        eauto 15.
      Qed.

      Example reduces: test ==>*(tm_pair (tm_nat 5) (tm_nat 0)).
      Proof.
        unfold test.
        normalize.
      Qed.
    End Sumtest2.

    Module ListTest.
      Definition test :=
        tm_let l
               (tm_cons (tm_nat 5) (tm_cons (tm_nat 6) (tm_nil ty_Nat)))
               (tm_lcase (tm_var l)
                         (tm_nat 0)
                         x y (tm_mult (tm_var x) (tm_var x))).
      Example typechecks:
        has_type (@empty ty) test ty_Nat.
      Proof.
        unfold test.
        eauto 20.
      Qed.

      Example reduces:
        test ==>* (tm_nat 25).
      Proof.
        unfold test.
        normalize.
      Qed.
    End ListTest.

    Module FixTest1.

      Definition fact :=
        tm_fix
          (tm_abs f (ty_arrow ty_Nat ty_Nat)
                  (tm_abs a ty_Nat
                          (tm_if0
                             (tm_var a)
                             (tm_nat 1)
                             (tm_mult
                                (tm_var a)
                                (tm_app (tm_var f) (tm_pred (tm_var a))))))).

      Example fact_typechecks:
        has_type (@empty ty) fact (ty_arrow ty_Nat ty_Nat).
      Proof.
        unfold fact.
        auto 10.
      Qed.

      Example fact_example:
        (tm_app fact (tm_nat 4)) ==>* (tm_nat 24).
      Proof.
        unfold fact.
        normalize.
      Qed.
    End FixTest1.

    Module FixTest2.
      Definition map :=
        tm_abs g (ty_arrow ty_Nat ty_Nat)
               (tm_fix
                  (tm_abs f (ty_arrow (ty_List ty_Nat) (ty_List ty_Nat))
                          (tm_abs l (ty_List ty_Nat)
                                  (tm_lcase (tm_var l)
                                            (tm_nil ty_Nat)
                                            a l (tm_cons (tm_app (tm_var g) (tm_var a))
                                                         (tm_app (tm_var f) (tm_var l))))))).
      Example map_typechecks:
        has_type empty map
                 (ty_arrow (ty_arrow ty_Nat ty_Nat)
                           (ty_arrow (ty_List ty_Nat)
                                     (ty_List ty_Nat))).
      Proof.
        unfold map.
        auto 10.
      Qed.
      Example map_example:
        tm_app (tm_app map (tm_abs a ty_Nat (tm_succ (tm_var a))))
               (tm_cons (tm_nat 1) (tm_cons (tm_nat 2) (tm_nil ty_Nat)))
               ==>*
               (tm_cons (tm_nat 2) (tm_cons (tm_nat 3) (tm_nil ty_Nat))).
      Proof.
        unfold map.
        normalize.
      Qed.

    End FixTest2.

    Module FixTest3.
      Definition equal :=
        tm_fix
          (tm_abs eq (ty_arrow ty_Nat (ty_arrow ty_Nat ty_Nat))
                  (tm_abs m ty_Nat
                          (tm_abs n ty_Nat
                                  (tm_if0 (tm_var m)
                                          (tm_if0 (tm_var n) (tm_nat 1) (tm_nat 0))
                                          (tm_if0 (tm_var n)
                                                  (tm_nat 0)
                                                  (tm_app (tm_app (tm_var eq)
                                                                  (tm_pred (tm_var m)))
                                                          (tm_pred (tm_var n)))))))).
      Example equal_typechecks :
        has_type (@empty ty) equal (ty_arrow ty_Nat (ty_arrow ty_Nat ty_Nat)).
      Proof.
        unfold equal.
        auto 10.
      Qed.


      Example equal_example1:
        (tm_app (tm_app equal (tm_nat 4)) (tm_nat 4)) ==>* (tm_nat 1).
      Proof.
        unfold equal.
        normalize.
      Qed.


      Example equal_example2:
  (tm_app (tm_app equal (tm_nat 4)) (tm_nat 5)) ==>* (tm_nat 0).
      Proof.
        unfold equal.
        normalize.
      Qed.
    End FixTest3.

    Module FixTest4.
      
      Definition eotest :=
        tm_let evenodd
               (tm_fix
                  (tm_abs eo (ty_prod (ty_arrow ty_Nat ty_Nat) (ty_arrow ty_Nat ty_Nat))
                          (tm_pair
                             (tm_abs n ty_Nat
                                     (tm_if0 (tm_var n)
                                             (tm_nat 1)
                                             (tm_app (tm_snd (tm_var eo)) (tm_pred (tm_var n)))))
                             (tm_abs n ty_Nat
                                     (tm_if0 (tm_var n)
                                             (tm_nat 0)
                                             (tm_app (tm_fst (tm_var eo)) (tm_pred (tm_var n))))))))
               (tm_let even (tm_fst (tm_var evenodd))
                       (tm_let odd (tm_snd (tm_var evenodd))
                               (tm_pair
                                  (tm_app (tm_var even) (tm_nat 3))
                                  (tm_app (tm_var even) (tm_nat 4))))).

      Example eotest_typechecks :
  has_type (@empty ty) eotest (ty_prod ty_Nat ty_Nat).
      Proof.
        unfold eotest.
        eauto 30.
      Qed.

      Example eotest_example1:
        eotest ==>* (tm_pair (tm_nat 0) (tm_nat 1)).
      Proof.
        unfold eotest.
        normalize.
      Qed.
    End FixTest4.
  End Examples.

  Theorem progress: forall t T,
      has_type empty t T ->
      value t \/ exists t', t ==> t'.
  Proof with eauto.
    intros t T Ht.
    remember (@empty ty) as Gamma.
    generalize dependent HeqGamma.
    has_type_cases (induction Ht) Case; intros HeqGamma; subst.
    Case "T_Var".
     inversion H.
    Case "T_Abs".
      left...
    Case "T_App".
      right.
      destruct IHHt1; subst...
      SCase "t1 is a value".
        destruct IHHt2; subst...
        SSCase "t2 is a value".
          inversion H; subst; try (solve by inversion).
          exists (subst x t2 t12)...
        SSCase "t2 steps".
          destruct H0 as [t2' Hstp].
          exists (tm_app t1 t2')...
      SCase "t1 steps".
        destruct H as [t1' Hstp].
        exists (tm_app t1' t2)...
    Case "T_Pair".
      destruct IHHt1; subst...
      SCase "t1 is a value".
        destruct IHHt2; subst...
        SSCase "t2 steps".
          right.
          destruct H0 as [t2' Hstp].
          exists (tm_pair t1 t2')...
      SCase "t1 steps".
        destruct H as [t1' Hstp].
        right...
    Case "T_Fst".
      right.
      destruct IHHt; subst...
      SCase "t1 is a value".
        inversion H; subst; try (solve by inversion).
        exists t0...
      SCase "t1 steps".
        destruct H as [t1' Hstp].
        exists (tm_fst t1')...
    Case "T_Snd".
      right.
      destruct IHHt; subst...
      SCase "t1 is a value".
        inversion H; subst; try (solve by inversion).
        exists t2...
      SCase "t1 steps".
        destruct H as [t1' Hstp].
        exists (tm_snd t1')...
    Case "T_Inl".
      destruct IHHt; subst...
      SCase "t1 steps".
        destruct H as [t1' Hstp].
        right.
        exists (tm_inl T2 t1')...
    Case "T_Inr".
      destruct IHHt; subst...
      SCase "t1 steps".
        destruct H as [t1' Hstp].
        right.
        exists (tm_inr T1 t1')...
    Case "T_Case".
      right.
      destruct IHHt1; subst...
      SCase "t is a value".
        inversion H; subst; try (solve by inversion).
        SSCase "t is inl".
          exists (subst v1 t0 t1)...
        SSCase "t is inr".
          exists (subst v2 t0 t2)...
      SCase "t steps".
        destruct H as [t1' Hstp].
        exists (tm_case t1' v1 t1 v2 t2)...
    Case "T_Nil".
      left...
    Case "T_Cons".
      destruct IHHt1; subst...
      SCase "t1 is a value".
        destruct IHHt2; subst...
        SSCase "t2 steps".
          right.
          destruct H0 as [t2' Hstp].
          exists (tm_cons t1 t2')...
      SCase "t1 steps".
        right.
        destruct H as [t1' Hstp].
        exists (tm_cons t1' t2)...
    Case "T_Lcase".
      right.
      destruct IHHt1; subst...
      SCase "t1 is a value".
        inversion H; subst; try (solve by inversion).
        SSCase "t1 is nil".
          exists t2...
        SSCase "t1 is a cons".
          exists (subst vh t0 (subst vt t4 t3))...
      SCase "t1 steps".
        destruct H as [t1' Hstp].
        exists (tm_lcase t1' t2 vh vt t3)...
     Case "T_Nat".
       left...
     Case "T_Succ".
       right.
       destruct IHHt; subst...
       SCase "n is a value".
         inversion H; subst; try (solve by inversion).
         exists (tm_nat (1 + n0))...
       SCase "n steps".
         destruct H as [t' Hstp].
         exists (tm_succ t')...
     Case "T_Pred".
       right.
       destruct IHHt; subst...
       SCase "n is a value".
         inversion H; subst; try (solve by inversion).
         remember (beq_nat n0  0) as Heq0.
         case n0.
         SSCase "n is 0".
           exists (tm_nat 0)...
         SSCase "n > 0".
           intros n.
           exists (tm_nat n)...
       SCase "n steps".
         destruct H as [n' Hstp].
         exists (tm_pred n')...
     Case "T_Mult".
       right.
       destruct IHHt1; subst...
       SCase "n is a value".
         destruct IHHt2; subst...
         SSCase "m is a value".
           inversion H; subst; try (solve by inversion).
           inversion H0; subst; try (solve by inversion).
           exists (tm_nat(n0 * n))...
         SSCase "m steps".
           destruct H0 as [m' Hstp].
           exists (tm_mult n m')...
       SCase "n steps".
         destruct H as [n' Hstp].
         exists (tm_mult n' m)...
     Case "T_If0".
       right.
       destruct IHHt1; subst...
       SCase "tc is a value".
         inversion H; subst; try (solve by inversion).
         case n.
         SSCase "n is 0".
           exists tt...
         SSCase "n is not 0".
           exists te...
       SCase "tc stepts".
         destruct H as [tc' Hstp].
         exists (tm_if0 tc' tt te)...
    Case "T_Let".
      right.
      destruct IHHt1; subst...
      SCase "t1 steps".
        destruct H as [t1' Hstp].
        exists (tm_let v t1' t)...
    Case "T_Fix".
      right.
      destruct IHHt; subst...
      SCase "t is a value".
        inversion H; subst; try (solve by inversion).
        exists (subst x (tm_fix (tm_abs x T11 t12)) t12)...
      SCase "t steps".
        destruct H as [t' Hstp].
        exists (tm_fix t')...
  Qed.

  Inductive appears_free_in: id -> tm -> Prop :=
  | afi_var: forall x,
      appears_free_in x (tm_var x)
  | afi_app1: forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
  | afi_app2: forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
  | afi_abs: forall x y T11 t12,
      y <> x ->
      appears_free_in x t12 ->
      appears_free_in x (tm_abs y T11 t12)
  | afi_pair1: forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tm_pair t1 t2)
  | afi_pair2: forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tm_pair t1 t2)
  | afi_fst: forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (tm_fst t1)
  | afi_snd: forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (tm_snd t1)
  | afi_inl: forall x t1 T1,
      appears_free_in x t1 ->
      appears_free_in x (tm_inl T1 t1)
  | afi_inr: forall x t1 T1,
      appears_free_in x t1 ->
      appears_free_in x (tm_inr T1 t1)
  | afi_case1: forall x t x1 t1 x2 t2,
      appears_free_in x t ->
      appears_free_in x (tm_case t x1 t1 x2 t2)
  | afi_case2: forall x t x1 t1 x2 t2,
      x1 <> x ->
      appears_free_in x t1 ->
      appears_free_in x (tm_case t x1 t1 x2 t2)
  | afi_case3: forall x t x1 t1 x2 t2,
      x2 <> x ->
      appears_free_in x t2 ->
      appears_free_in x (tm_case t x1 t1 x2 t2)
  | afi_cons1: forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tm_cons t1 t2)
  | afi_cons2: forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tm_cons t1 t2)
  | afi_lcase1: forall x t t1 xh xt t2,
      appears_free_in x t ->
      appears_free_in x (tm_lcase t t1 xh xt t2)
  | afi_lcase2: forall x t t1 xh xt t2,
      appears_free_in x t1 ->
      appears_free_in x (tm_lcase t t1 xh xt t2)
  | afi_lcase3: forall x t t1 xh xt t2,
      xt <> x ->
      xh <> x ->
      appears_free_in x t2 ->
      appears_free_in x (tm_lcase t t1 xh xt t2)
  | afi_succ: forall x n,
      appears_free_in x n ->
      appears_free_in x (tm_succ n)
  | afi_pred: forall x n,
      appears_free_in x n ->
      appears_free_in x (tm_pred n)
  | afi_mult1: forall x n m,
      appears_free_in x n ->
      appears_free_in x (tm_mult n m)
  | afi_mult2: forall x n m,
      appears_free_in x m ->
      appears_free_in x (tm_mult n m)
  | afi_if01: forall x tc tt te,
      appears_free_in x tc ->
      appears_free_in x (tm_if0 tc tt te)
  | afi_if02: forall x tc tt te,
      appears_free_in x tt ->
      appears_free_in x (tm_if0 tc tt te)
  | afi_if03: forall x tc tt te,
      appears_free_in x te ->
      appears_free_in x (tm_if0 tc tt te)
  | afi_let1: forall x x1 t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tm_let x1 t1 t2)
  | afi_let2: forall x x1 t1 t2,
      x1 <> x ->
      appears_free_in x t2 ->
      appears_free_in x (tm_let x1 t1 t2)
  | afi_fix: forall x t,
      appears_free_in x t ->
      appears_free_in x (tm_fix t)
  .

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
      apply T_Var...
      rewrite <- Heqv...
    Case "T_Abs".
      apply T_Abs...
      apply IHhas_type.
      intros y Hafi.
      unfold extend.
      remember (beq_id x y) as e.
      destruct e...
    Case "T_Pair".
      apply T_Pair...
    Case "T_Case".
      eapply T_Case...
      SCase "t1".
        apply IHhas_type2.
        intros y Hafi.
        unfold extend.
        remember (beq_id v1 y) as e.
        destruct e...
      SCase "t2".
        apply IHhas_type3.
        intros y Hafi.
        unfold extend.
        remember (beq_id v2 y) as e.
        destruct e...
    Case "T_Cons".
      apply T_Cons...
    Case "T_Lcase".
      eapply T_Lcase...
      SCase "t3".
        apply IHhas_type3.
        intros y Hafi.
        unfold extend.
        remember (beq_id vt y) as e1.
        remember (beq_id vh y) as e2.
        destruct e1...
        SSCase "vt <> y".
        symmetry in Heqe1.
        apply beq_id_false_not_eq in Heqe1.
        destruct e2...
    Case "T_Mult".
      apply T_Mult...
    Case "T_If0".
      apply T_If0...
    Case "T_Let".
      eapply T_Let...
      apply IHhas_type2.
      intros y Hafi.
      unfold extend.
      remember (beq_id v y) as e.
      destruct e...
  Qed.

  Lemma free_in_context: forall x t T Gamma,
      appears_free_in x t ->
      has_type Gamma t T ->
      exists T', Gamma x = Some T'.
  Proof with eauto.
    intros x t T Gamma Hafi Htyp.
    has_type_cases (induction Htyp) Case; inversion Hafi; subst...
    Case "T_Abs".
      destruct IHHtyp as [T' Hctx]...
      exists T'.
      unfold extend in Hctx.
      apply not_eq_beq_id_false in H2.
      rewrite H2 in Hctx...
    Case "T_Case".
      SCase "t1".
        destruct IHHtyp2 as [T' Hctx]...
        exists T'.
        unfold extend in Hctx.
        apply not_eq_beq_id_false in H2.
        rewrite H2 in Hctx...
      SCase "t2".
        destruct IHHtyp3 as [T' Hctx]...
        exists T'.
        unfold extend in Hctx.
        apply not_eq_beq_id_false in H2.
        rewrite H2 in Hctx...
    Case "T_Lcase".
      SCase "t3".
        destruct IHHtyp3 as [T' Hctx]...
        exists T'.
        unfold extend in Hctx.
        apply not_eq_beq_id_false in H3.
        apply not_eq_beq_id_false in H6.
        rewrite H3 in Hctx.
        rewrite H6 in Hctx...
    Case "T_Let".
      destruct IHHtyp2 as [T' Hctx]...
      exists T'.
      unfold extend in Hctx.
      apply not_eq_beq_id_false in H2.
      rewrite H2 in Hctx...
  Qed.


  Lemma substitution_preserves_typing: forall Gamma x U v t S,
      has_type (extend Gamma x U) t S ->
      has_type empty v U ->
      has_type Gamma (subst x v t) S.
  Proof with eauto.
    intros Gamma x U v t S Htypt Htypv.
    generalize dependent Gamma.
    generalize dependent S.

    tm_cases(induction t) Case;
      intros S Gamma Htypt; simpl; inversion Htypt; subst...
    Case "tm_var".
      remember (beq_id x i) as e. destruct e.
      SCase "x = y".
        apply beq_id_eq in Heqe. subst.
        unfold extend in H1.
        rewrite <- beq_id_refl in H1.
        inversion H1; subst. clear H1.
        eapply context_invariance...
        intros x Hcontra.
        destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
        inversion HT'.
      SCase "x <> y".
        apply T_Var...
        unfold extend in H1.
        rewrite <- Heqe in H1...
    Case "tm_abs".
      rename i into y.
      rename t into T11.
      apply T_Abs...
      remember (beq_id x y) as e. destruct e.
      SCase "x = y".
        eapply context_invariance...
        apply beq_id_eq in Heqe. subst.
        intros x Hafi.
        unfold extend.
        destruct (beq_id y x)...
      SCase "x <> y".
        apply IHt.
        eapply context_invariance...
        intros z Hafi.
        unfold extend.
        remember (beq_id y z) as e0. destruct e0...
        apply beq_id_eq in Heqe0.
        subst.
        rewrite <- Heqe...
   Case "tm_case".
     eapply T_Case...
     SCase "t2".
       remember (beq_id x i) as e. destruct e.
       SSCase "x = i".
         apply beq_id_eq in Heqe. subst.
         eapply context_invariance...
         intros x Hafi.
         unfold extend.
         remember (beq_id i x) as e.
         destruct e...
       SSCase  "x <> i".
         apply IHt2.
         eapply context_invariance...
         intros z Hafi.
         unfold extend. 
         remember (beq_id i z) as e. destruct e...
         apply beq_id_eq in Heqe0.
         subst.
         rewrite <- Heqe...
     SCase "t3".
       remember (beq_id x i0) as e. destruct e.
       SSCase "x = i0".
         apply beq_id_eq in Heqe. subst.
         eapply context_invariance...
         intros x Hafi.
         unfold extend.
         remember (beq_id i0 x) as e.
         destruct e...
       SSCase "x <> i0".
         apply IHt3.
         eapply context_invariance...
         intros z Hafi.
         unfold extend.
         remember (beq_id i0 z) as e. destruct e...
         apply beq_id_eq in Heqe0.
         subst.
         rewrite <- Heqe...
    Case "tm_lcase".
      eapply T_Lcase...
      SCase "t3".
        remember (beq_id i0 x) as e1.
        destruct e1.
        SSCase "i = x".
          apply beq_id_eq in Heqe1. subst. simpl.        
          eapply context_invariance...
          intros x0 Hafi.
          unfold extend.
          remember (beq_id x x0) as e. destruct e...
        SSCase "i <> x".
          simpl.
          remember (beq_id i x) as e.
          destruct e...
          SSSCase  "i0 = x".
            apply beq_id_eq in Heqe.
            symmetry in Heqe1.
            apply beq_id_false_not_eq in Heqe1.
            subst.
            eapply context_invariance...
            intros x0 Hafi.
            unfold extend.
            remember (beq_id x x0) as e. destruct e...
          SSSCase "i0 <> x".
            apply IHt3.
            eapply context_invariance...
            intros x0 Hafi.
            unfold extend.
            remember (beq_id i0 x0) as e. destruct e...
            remember (beq_id x x0) as e. destruct e...
            apply beq_id_eq in Heqe0. subst.
            rewrite <- beq_id_sym in Heqe.
            rewrite beq_id_sym in Heqe2.
            rewrite  <- Heqe1 in Heqe2.
            inversion Heqe2.
            remember (beq_id i x0) as e. destruct e...
            remember (beq_id x x0) as e. destruct e...
            apply beq_id_eq in Heqe2. subst.
            rewrite beq_id_sym in Heqe3.
            rewrite <- Heqe in Heqe3.
            inversion Heqe3.
    Case "tm_let"  .
      eapply T_Let.
      SCase "x = i".
        apply  IHt1...
      SCase "t2".
        remember (beq_id x i) as e. destruct e...
        SSCase "x = i".
          eapply context_invariance...
          intros x0 Hafi.
          unfold extend.
          remember (beq_id i x0) as e. destruct e...
          remember (beq_id x x0) as e. destruct e...
          apply beq_id_eq in Heqe.
          apply beq_id_eq in Heqe1.
          subst.
          symmetry in Heqe0.
          subst.
          rewrite <- beq_id_refl in Heqe0.
          inversion Heqe0.
        SSCase "x <> i".
          eapply IHt2.
          eapply context_invariance...
          intros x0 Hafi.
          unfold extend.
          remember (beq_id x i) as e. destruct e...
          inversion Heqe.
          remember (beq_id i x0) as e. destruct e...
          apply beq_id_eq in Heqe1. subst.
          rewrite <- Heqe0...
  Qed.

  Theorem preservation: forall t t' T,
      has_type empty t T ->
      t ==> t' ->
      has_type empty t' T.
  Proof with eauto.
    intros t t' T HT.
    remember (@empty ty) as Gamma.
    generalize dependent HeqGamma.
    generalize dependent t'.
    has_type_cases (induction HT) Case;
      intros t' HeqGamma HE; subst; inversion HE; subst...
    Case "T_App".
      SCase "ST_AppAbs".
       apply substitution_preserves_typing with T1...
       inversion HT1...
    Case "T_Fst".
      inversion HT...
    Case "T_Snd".
      inversion HT...
    Case "T_Case".
      SCase "ST_CaseInl".
        apply substitution_preserves_typing with T1...
        inversion HT1...
      SCase "ST_CaseInr".
        apply substitution_preserves_typing with T2...
        inversion HT1...
    Case "T_Lcase".
      apply substitution_preserves_typing with T1...
      apply substitution_preserves_typing with (ty_List T1)...
      inversion HT1...
      eapply context_invariance...
      inversion HT1...
    Case "T_Let".
      apply substitution_preserves_typing with T1...
      inversion HT...
    Case "T_Fix".
      apply substitution_preserves_typing with T...
  Qed.

End STLCExtended.
  