
From TL Require Import Identifier Environment.

Inductive exp : Type :=
  | ENum : nat -> exp
  | EId : id -> exp
  | EPlus : exp -> exp -> exp.

(* eq_exp_dec *)

Definition state := @Env nat.
Definition update_st := @update_env nat.
Definition empty_state := @empty_env nat.

(* empty state *)
Inductive eval : exp -> state -> nat -> Prop :=
    | eval_const : forall n st, eval (ENum n) st n
    | eval_var: forall x st u,
        st x = Some u -> eval (EId x) st u
    | eval_plus: forall e1 e2 st u v z,
        eval e1 st u ->
        eval e2 st v ->
        z = u + v ->
        eval (EPlus e1 e2) st z.

Inductive cmd : Type :=
  | CStop : cmd
  | CSkip : cmd
  | CAss  : id  -> exp -> cmd
  | CSeq  : cmd -> cmd -> cmd
  | CIf   : exp -> cmd -> cmd -> cmd
  | CWhile: exp -> cmd -> cmd.

Notation "'STOP'" := CStop.
Notation "'SKIP'" := CSkip.
Notation "x '::=' a" :=(CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Inductive config : Type :=
  | Config : cmd -> state -> config.

Notation "'〈' c ',' st '〉'" := (Config c st) (at level 0).

Reserved Notation "cfg '⇒' cfg'" (at level 40).

Inductive step : config -> config -> Prop :=
  | step_skip : forall st,
      〈 SKIP, st 〉 ⇒ 〈 STOP, st 〉
  | step_assign: forall x e v st st',
       eval e st v ->
       st' = update_st st x v ->
      〈 x ::= e, st 〉 ⇒  〈 STOP, st'〉
  | step_seq1 : forall c1 c1' c2 st st',
      〈 c1, st 〉⇒ 〈 c1', st' 〉->
      c1' <> STOP ->
      〈 c1 ;; c2, st 〉⇒ 〈 c1' ;; c2, st' 〉
  | step_seq2 : forall c1 c2 st st',
      〈 c1, st 〉⇒ 〈 STOP, st' 〉->
      〈 c1 ;; c2, st 〉⇒ 〈 c2, st' 〉
  | step_if1 : forall e u c1 c2 st,
       eval e st u -> u <> 0 ->
      〈 IFB e THEN c1 ELSE c2 FI, st 〉⇒〈 c1, st 〉
  | step_if2 : forall e c1 c2 st,
       eval e st 0 ->
      〈 IFB e THEN c1 ELSE c2 FI, st 〉⇒〈 c2, st 〉
  | step_while : forall e c st,
      〈 WHILE e DO c END, st 〉⇒
          〈 IFB e THEN c;; WHILE e DO c END ELSE SKIP FI, st 〉
where "cfg '⇒' cfg' " := (step cfg cfg').
