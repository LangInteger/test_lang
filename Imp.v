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



Module AExp.

Inductive aexp : Type :=
 | ANum (n : nat)
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

Fixpoint aeval (a: aexp) : nat :=
  match a with
  | ANum n       => n
  | APlus a1 a2  => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2  => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 3)) = 5.
Proof. reflexivity. Qed.

Fixpoint beval (b: bexp): bool :=
  match b with
  | BTrue        => true
  | BFalse       => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BNeq a1 a2  => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BGt a1 a2   => negb ((aeval a1) <=? (aeval a2))
  | BNot b      => negb (beval b)
  | BAnd b1 b2  => (beval b1) && (beval b2)
  end.

Fixpoint optimize_0plus (a: aexp): aexp :=
  match a with
  | ANum n       => ANum n
  | APlus (ANum 0) a2 => optimize_0plus a2
  | APlus a1 a2  => APlus (optimize_0plus a1) (optimize_0plus a2)
  | AMinus a1 a2 => AMinus (optimize_0plus a1) (optimize_0plus a2)
  | AMult a1 a2  => AMult (optimize_0plus a1) (optimize_0plus a2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 0) (APlus (ANum 3) (ANum 0)))
  = APlus (ANum 3) (ANum 0).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound:
  forall a, aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* a = ANum n *) reflexivity.
  - (* a = APlus a1 a2 *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *) simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *) simpl. simpl in IHa1. rewrite IHa1.  rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *) simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* a = AMinus a1 a2 *) simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* a = AMult a1 a2 *) simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

(* ===================== try and ; tactical ======================== *)
Theorem optimize_0plus_sound':
  forall a, aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. 
  induction a; 
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - (* a = ANum n *) reflexivity.
  - (* a = APlus a1 a2 *) 
    destruct a1 eqn:Ea1;
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      try (simpl; rewrite IHa2; reflexivity).
Qed.

Theorem optimize_0plus_sound'':
  forall a, aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. 
  induction a; 
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  - (* a = APlus a1 a2 *) 
    destruct a1 eqn:Ea1;
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      try (simpl; rewrite IHa2; reflexivity).
Qed.

(* ===================== repeat tactical ======================== *)
Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.
  (* rewrite Nat.add_comm. *)
Admitted.

(* ===================== lia ======================== *)
Example add_comm__lia: forall m n : nat,
  m + n = n + m.
Proof.
  intros m n. lia.
Qed.



End AExp.



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

Fixpoint aeval (st: state) (a: aexp) : nat :=
  match a with
  | ANum n       => n
  | AId x        => st x
  | APlus a1 a2  => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2  => (aeval st a1) * (aeval st a2)
  end.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Example test_aeval1:
  aeval (X !-> 5) (APlus (ANum 2) (ANum 3)) = 5.
Proof. reflexivity. Qed.

Example aexp1 :
    aeval (X !-> 5) <{ 3 + (X * 2) }>
  = 13.
Proof. reflexivity. Qed.

Example aexp2 :
    aeval (t_update (t_update empty_st X 5) Y 4) <{ Z + (X * Y) }>
  = 20.
Proof. reflexivity. Qed.  

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

(* ===================== commands ======================== *)
Inductive com : Type :=
  | CSkip
  | CAsgn (x: string) (a: aexp)
  | CSeq (c1 c2 : com)
  | CIf (b: bexp) (c1 c2: com)
  | CWhile (b: bexp) (c: com).

(* ===================== operational semantics ======================== 
   define the operational semantics of the Imp language as a function fails:

*)

Fixpoint ceval_fun_no_while (st: state) (c: com) : state :=
  match c with 
  | CSkip => st
  | CAsgn x a => (t_update st x (aeval st a))
  | CSeq c1 c2 => let st' := ceval_fun_no_while st c1 in
                  ceval_fun_no_while st' c2
  | CIf b c1 c2 => if beval st b then ceval_fun_no_while st c1
                  else ceval_fun_no_while st c2
  | CWhile b c1 => st (* not allowed *)
  end.

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
  
(* The following definition does not work
    It complains: Cannot guess decreasing argument of fix.
    because Coq does not accept such a definition that is not guaranteed to terminate.
 *)
(* Fixpoint ceval_fun_no_while' (st: state) (c: com) : state :=
  match c with 
  | CSkip => st
  | CAsgn x a => (t_update st x (aeval st a))
  | CSeq c1 c2 => let st' := ceval_fun_no_while' st c1 in
                  ceval_fun_no_while' st' c2
  | CIf b c1 c2 => if beval st b then ceval_fun_no_while' st c1
                  else ceval_fun_no_while' st c2
  | CWhile b c1 => if (beval st b) then ceval_fun_no_while' st (CSeq c1 (CWhile b c1))
                  else st
  end. *)

  (* A better way is to definition evaluation as a relation *)
  (** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Asgn)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
*)
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

Example ceval_example1:
  ceval <{
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  }> empty_st (t_update (t_update empty_st X 2) Z 4).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_IfFalse. 
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

Example ceval_example2:
  ceval <{
    X := 0;
    Y := 1;
    Z := 2
  }> empty_st (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Asgn. reflexivity.
  - apply E_Seq with (Y !-> 1 ; X !-> 0).
    + apply E_Asgn. reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

Definition plus2 : com :=
  <{ X := X + 2 }>.

Theorem plus2_spec : forall st n st',
  st X = n ->
  ceval plus2 st st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Hceval.
  inversion Hceval. subst. simpl. apply t_update_eq. Qed.