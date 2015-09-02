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
                 (if orb (beq_id yhd x) (beq_id ytl x)
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
  | v_nil: forall T,
             value (tm_nil T)
  | v_cons: forall t1 t2,
              value t1 -> value t2 -> value (tm_cons t1 t2)
  | v_nat: forall n,
             value (tm_nat n)
  | v_fix: forall t,
             value t ->
             value (tm_fix t).

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
               tm_snd (tm_pair t1 t2) ==> t1
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
                (tm_case t x1 t1 x2 t2) ==> (subst x1 t t1)
  | ST_CaseInr: forall T t x1 t1 x2 t2,
                value (tm_inr T t) ->
                (tm_case t x1 t1 x2 t2) ==> (subst x2 t t2)
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
                (tm_lcase (tm_cons t1 t2) tnil xcons1 xcons2 tcons) ==> (subst xcons2 t2 (subst xcons1 t1 tcons))
  | ST_Succ1: forall t t',
                t ==> t' ->
                (tm_succ t) ==> (tm_succ t')
  | ST_Succ2: forall n,
                (tm_succ (tm_nat n)) ==> tm_nat (1 + n)
  | ST_Pred1: forall t t',
                t ==> t' ->
                (tm_pred t) ==> (tm_pred t')
  | ST_Pred2: forall n,
                n <> 0 ->
                (tm_pred (tm_nat n)) ==> tm_nat (1 + n)
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

  