Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.
From Coq Require Import EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Strings.String.
From TL Require Import Maps.
Set Default Goal Selector "!".



(* ===================== expression with variables ======================== *)
Definition state := total_map nat.

Inductive aexp : Type :=
 | ANum (n : nat)
 | AId (x : string)
 | APlus (a1 a2 : aexp)
 | AMinus (a1 a2 : aexp)
 | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.

Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).



Open Scope com_scope.
Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Inductive com : Type :=
  | CSkip
  | CAsgn (x: string) (a: aexp)
  | CSeq (c1 c2 : com)
  | CIf (b: bexp) (c1 c2: com)
  | CWhile (b: bexp) (c: com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

Inductive bval : bexp -> Prop :=
  | bv_true : bval BTrue
  | bv_false : bval BFalse.

Inductive astep (st: state) : aexp -> aexp -> Prop :=
  | AS_Id : forall x,
      astep st (AId x) (ANum (st x))
  | AS_Plus1 : forall a1 a1' a2,
      astep st a1 a1' ->
      astep st (APlus a1 a2) (APlus a1' a2)
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      astep st a2 a2' ->
      astep st (APlus v1 a2) (APlus v1 a2')
  | AS_Plus : forall (n1 n2 : nat),
      astep st (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))
  | AS_Minus1 : forall a1 a1' a2,
      astep st a1 a1' ->
      astep st (AMinus a1 a2) (AMinus a1' a2)
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      astep st a2 a2' ->
      astep st (AMinus v1 a2) (AMinus v1 a2')
  | AS_Minus : forall (n1 n2 : nat),
      astep st (AMinus (ANum n1) (ANum n2)) (ANum (n1 - n2))
  | AS_Mult1 : forall a1 a1' a2,
      astep st a1 a1' ->
      astep st (AMult a1 a2) (AMult a1' a2)
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      astep st a2 a2' ->
      astep st (AMult v1 a2) (AMult v1 a2')
  | AS_Mult : forall (n1 n2 : nat),
      astep st (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2))
.

Inductive bstep (st: state) : bexp -> bexp -> Prop :=
  | BS_Eq1 : forall a1 a1' a2,
      astep st a1 a1' ->
      bstep st (BEq a1 a2) (BEq a1' a2)
  | BS_Eq2 : forall v1 a2 a2',
      aval v1 ->
      astep st a2 a2' ->
      bstep st (BEq v1 a2) (BEq v1 a2')
  | BS_Eq : forall (n1 n2 : nat),
      bstep st (BEq (ANum n1) (ANum n2))
               (if beq_nat n1 n2 then BTrue else BFalse)
  | BS_Neq1 : forall a1 a1' a2,
      astep st a1 a1' ->
      bstep st (BNeq a1 a2) (BNeq a1' a2)
  | BS_Neq2 : forall v1 a2 a2',
      aval v1 ->
      astep st a2 a2' ->
      bstep st (BNeq v1 a2) (BNeq v1 a2')
  | BS_Neq : forall (n1 n2 : nat),
      bstep st (BNeq (ANum n1) (ANum n2))
               (if beq_nat n1 n2 then BFalse else BTrue)
  | BS_Le1 : forall a1 a1' a2,
      astep st a1 a1' ->
      bstep st (BLe a1 a2) (BLe a1' a2)
  | BS_Le2 : forall v1 a2 a2',
      aval v1 ->
      astep st a2 a2' ->
      bstep st (BLe v1 a2) (BLe v1 a2')
  | BS_Le : forall (n1 n2 : nat),
      bstep st (BLe (ANum n1) (ANum n2))
               (if n1 <=? n2 then BTrue else BFalse)
  | BS_Gt1 : forall a1 a1' a2,
      astep st a1 a1' ->
      bstep st (BGt a1 a2) (BGt a1' a2)
  | BS_Gt2 : forall v1 a2 a2',
      aval v1 ->
      astep st a2 a2' ->
      bstep st (BGt v1 a2) (BGt v1 a2')
  | BS_Gt : forall (n1 n2 : nat),
      bstep st (BGt (ANum n1) (ANum n2))
               (if n2 <=? n1 then BTrue else BFalse)
  | BS_Not1 : forall a1 a1',
      bstep st a1 a1' ->
      bstep st (BNot a1) (BNot a1')
  | BS_NotTrue : 
      bstep st (BNot BTrue) BFalse
  | BS_NotFalse : 
      bstep st (BNot BFalse) BTrue
  | BS_AndStep : forall b1 b1' b2,
      bstep st b1 b1' ->
      bstep st (BAnd b1 b2) (BAnd b1' b2)
  | BS_AndTrueStep : forall b2 b2',
      bstep st b2 b2' ->
      bstep st (BAnd BTrue b2) (BAnd BTrue b2')
  | BS_AndFalse : forall b2 b2',
      bstep st b2 b2' ->
      bstep st (BAnd BFalse b2) BFalse
  | BS_AndTrueTrue : 
      bstep st (BAnd BTrue BTrue) BTrue
  | BS_AndTrueFalse : 
      bstep st (BAnd BTrue BFalse) BFalse
.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssignStep : forall st x a a',
      astep st a a' ->
      cstep (CAsgn x a, st) (CAsgn x a', st)
  | CS_Assign : forall st x n,
      cstep (CAsgn x (ANum n), st) (CSkip, (x !-> n ; st))
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep (CSeq c1 c2, st) (CSeq c1' c2, st')
  | CS_SeqFinish : forall st c2,
      cstep (CSeq CSkip c2, st) (c2, st)
  | CS_IfStep : forall st b1 b1' c1 c2,
      bstep st b1 b1' ->
      cstep (CIf b1 c1 c2, st) (CIf b1' c1 c2, st)
  | CS_IfTrue : forall st c1 c2,
      cstep (CIf BTrue c1 c2, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep (CIf BFalse c1 c2, st) (c2, st)
  | CS_While : forall st b c,
      cstep (CWhile b c, st)
            (CIf b (CSeq c (CWhile b c)) CSkip, st)
.

Inductive ty : Type :=
  | L : ty
  | H : ty.

Definition join (t1 t2 : ty) : ty :=
  match t1, t2 with
  | L, L => L
  | _, _ => H
  end.

Definition leq_ty (t1 t2 : ty) : Prop :=
  match t1, t2 with
  | L, L => True
  | L, H => True
  | H, H => True
  | H, L => False
  end.

Definition context := total_map ty.

Inductive has_type_aexp : context -> aexp -> ty -> Prop :=
  | T_ANum : forall Gamma n,
      has_type_aexp Gamma (ANum n) L
  | T_AId : forall Gamma x,
      has_type_aexp Gamma (AId x) (Gamma x)
  | T_APlus : forall Gamma a1 a2 t1 t2,
      has_type_aexp Gamma a1 t1 ->
      has_type_aexp Gamma a2 t2 ->
      has_type_aexp Gamma (APlus a1 a2) (join t1 t2)
  | T_AMinus : forall Gamma a1 a2 t1 t2,
      has_type_aexp Gamma a1 t1 ->
      has_type_aexp Gamma a2 t2 ->
      has_type_aexp Gamma (AMinus a1 a2) (join t1 t2)
  | T_AMult : forall Gamma a1 a2 t1 t2,
      has_type_aexp Gamma a1 t1 ->
      has_type_aexp Gamma a2 t2 ->
      has_type_aexp Gamma (AMult a1 a2) (join t1 t2)
.

Inductive has_type_bexp : context -> bexp -> ty -> Prop :=
  | T_BTrue : forall Gamma, has_type_bexp Gamma BTrue L
  | T_BFalse : forall Gamma, has_type_bexp Gamma BFalse L
  | T_BEq : forall Gamma a1 a2 t1 t2,
      has_type_aexp Gamma a1 t1 ->
      has_type_aexp Gamma a2 t2 ->
      has_type_bexp Gamma (BEq a1 a2) (join t1 t2)
  | T_BNeq : forall Gamma a1 a2 t1 t2,
      has_type_aexp Gamma a1 t1 ->
      has_type_aexp Gamma a2 t2 ->
      has_type_bexp Gamma (BNeq a1 a2) (join t1 t2)
  | T_BLe : forall Gamma a1 a2 t1 t2,
      has_type_aexp Gamma a1 t1 ->
      has_type_aexp Gamma a2 t2 ->
      has_type_bexp Gamma (BLe a1 a2) (join t1 t2)
  | T_BGt : forall Gamma a1 a2 t1 t2,
      has_type_aexp Gamma a1 t1 ->
      has_type_aexp Gamma a2 t2 ->
      has_type_bexp Gamma (BGt a1 a2) (join t1 t2)
  | T_BNot : forall Gamma b t,
      has_type_bexp Gamma b t ->
      has_type_bexp Gamma (BNot b) t
  | T_BAnd : forall Gamma b1 b2 t1 t2,
      has_type_bexp Gamma b1 t1 ->
      has_type_bexp Gamma b2 t2 ->
      has_type_bexp Gamma (BAnd b1 b2) (join t1 t2)
.

Inductive secure_com : context -> ty -> com -> Prop :=
  | S_Skip : forall Gamma pc,
      secure_com Gamma pc CSkip
  | S_Asgn : forall Gamma pc x a t_a,
      has_type_aexp Gamma a t_a ->
      leq_ty (join pc t_a) (Gamma x) ->  
      secure_com Gamma pc (CAsgn x a)
  | S_Seq : forall Gamma pc c1 c2,
      secure_com Gamma pc c1 ->
      secure_com Gamma pc c2 ->
      secure_com Gamma pc (CSeq c1 c2)
  | S_If : forall Gamma pc b c1 c2 t_b,
      has_type_bexp Gamma b t_b ->
      secure_com Gamma (join pc t_b) c1 ->
      secure_com Gamma (join pc t_b) c2 ->
      secure_com Gamma pc (CIf b c1 c2)
  | S_While : forall Gamma pc b c t_b,
      has_type_bexp Gamma b t_b ->
      secure_com Gamma (join pc t_b) c ->
      secure_com Gamma pc (CWhile b c)
.

Fixpoint aeval (st: state) (a: aexp) : nat :=
  match a with
  | ANum n       => n
  | AId x        => st x
  | APlus a1 a2  => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2  => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st: state) (b: bexp): bool :=
  match b with
  | BTrue        => true
  | BFalse       => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BNeq a1 a2  => negb ((aeval st a1) =? (aeval st a2))
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BGt a1 a2   => negb ((aeval st a1) <=? (aeval st a2))
  | BNot b      => negb (beval st b)
  | BAnd b1 b2  => (beval st b1) && (beval st b2)
  end.

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st, ceval CSkip st st  
  | E_Asgn : forall st a n x, aeval st a = n ->
              ceval (CAsgn x a) st (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
              ceval c1 st st' ->
              ceval c2 st' st'' ->
              ceval (CSeq c1 c2) st st''
  | E_IfTrue : forall st st' b c1 c2,
                 beval st b = true ->
                 ceval c1 st st' ->
                 ceval (CIf b c1 c2) st st'
  | E_IfFalse : forall st st' b c1 c2,
                 beval st b = false ->
                 ceval c2 st st' ->
                 ceval (CIf b c1 c2) st st'
  | E_WhileFalse : forall b c st,
                     beval st b = false ->
                     ceval (CWhile b c) st st
  | E_WhileTrue : forall st st' st'' b c,
                    beval st b = true ->
                    ceval c st st' ->
                    ceval (CWhile b c) st' st'' ->
                    ceval (CWhile b c) st st''.   


Definition low_eq (Gamma : context) (st1 st2 : state) : Prop :=
  forall x, Gamma x = L -> st1 x = st2 x.

Theorem noninterference_soundness :
  forall Gamma pc c st1 st2 st1' st2',
    (* if the syntatic judgment \Gamma\vdash_{pc} c secure is derivable *)
    secure_com Gamma pc c ->
    (* then non-interference holds, i.e. *)
    low_eq Gamma st1 st2 ->
    ceval c st1 st1' ->
    ceval c st2 st2' ->
    low_eq Gamma st1' st2'.
  Proof.
  intros Gamma pc c st1 st2 st1' st2' Hsec Hloweq He1 He2.
  induction Hsec.
  - (* S_Skip *) inversion He1. inversion He2. subst. auto.
  - (* S_Asgn *) inversion He1. inversion He2. 
    intros xx HxL.
  - (* S_Seq *) inversion He1. inversion He2. subst. auto.
  - (* S_If *) inversion He1. inversion He2. subst. auto.
  - (* S_While *) inversion He1. inversion He2. subst. auto.
