
From TL Require Import Identifier Environment.
From Coq Require Import Relations.
From Coq Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.

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

Lemma assign_neq_stop : forall x e, x ::= e <> STOP.
Proof.
  intros x e H. discriminate.
Qed.

Lemma seq_neq_stop : forall c1 c2, (c1 ;; c2) <> STOP.
Proof.
  intros c1 c2 H. discriminate.
Qed.

Lemma if_neq_stop : forall e c1 c2, (IFB e THEN c1 ELSE c2 FI) <> STOP.
Proof.
  intros e c1 c2 H. discriminate.
Qed.

Lemma while_neq_stop : forall e c, (WHILE e DO c END) <> STOP.
Proof.
  intros e c H. discriminate.
Qed.

Lemma eq_cmd_stop_dec: forall c1 : cmd, {c1 = STOP} + { c1 <> STOP }.
Proof.
  induction c1.
  - left. reflexivity.
  - right. intro H. discriminate H.
  - right. intro H. discriminate H.
  - right. intro H. discriminate H.
  - right. intro H. discriminate H.
  - right. intro H. discriminate H.
Qed.

Inductive config : Type :=
  | Config : cmd -> state -> config.

Definition is_stop cfg := 
  match cfg with
  | Config c m => c = STOP
  end.

Definition is_not_stop cfg := 
  match cfg with
  | Config c m => c <> STOP
  end.

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
  (* you cannot use while ==> if else here
     or the proof fo the preservation of well-formedness will fail
   *)
  | step_while1 : forall e c st u,
       eval e st u -> u <> 0 ->
      〈 WHILE e DO c END, st 〉⇒
          〈 c;; WHILE e DO c END, st 〉
  | step_while2 : forall e c st,
       eval e st 0 ->
      〈 WHILE e DO c END, st 〉⇒
          〈 SKIP, st 〉
where "cfg '⇒' cfg' " := (step cfg cfg').


Inductive multi {X:Type} (R: relation X): relation X :=
   | multi_refl : forall (x : X), multi R x x
   | multi_step : forall (x y z : X),
         R x y ->
         multi R y z ->
         multi R x z.

Lemma multi_is_refl : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl. Qed.

Lemma multi_is_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
   intros.
   induction H.
   - assumption.
   - apply multi_step with (y:=y).
      + assumption.
      + apply IHmulti. assumption.
Qed.


(* Multi-step transitions *)
(* reflexive transitive closure of -> *)
Definition multistep := multi step.
Notation " t '⇒*' t' " := (multistep t t') (at level 40).

(* indexed multi-step *)
Definition relation_idx := fun X : Type => X -> X -> nat -> Prop.
Inductive multi_idx {X:Type} (R: relation X) :relation_idx X :=
   | multi_refl_zero : forall (x : X), multi_idx R x x 0
   | multi_step_more : forall (x y z : X) n,
                         R x y ->
                         multi_idx R y z n ->
                         multi_idx R x z (S n).

Lemma multi_idx_is_refl : forall (X:Type) (R:relation X) (x y : X),
        R x y -> (multi_idx R) x y 1.
Proof.
  intros X R x y H.
  apply multi_step_more with y. apply H. apply multi_refl_zero.
Qed.

(* late intro for a stronger I.H. *)
Lemma multi_idx_is_trans : 
  forall n (X: Type) (R: relation X) ( x y z: X ) m,
    multi_idx R x y n ->
    multi_idx R y z m ->
    multi_idx R x z (n + m).
Proof.
  intros n X R.
  induction n; intros.
  - inversion H; subst.
    + simpl. assumption.
  - rewrite Nat.add_succ_l.
    inversion H; subst.
    apply multi_step_more with (y:=y0).
    + assumption.
    + specialize (IHn y0 y z m H5 H0).
      assumption.
Qed.
Definition multistep_idx := multi_idx step.

(* relationship of multi-step and multistep_idx *)
Lemma multi_implies_multi_idx:
  forall (X: Type) (R: relation X) (x y: X),
    multi R x y ->
    exists n, multi_idx R x y n.
Proof.
  intros X R x y H.
  induction H.
  - exists 0. apply multi_refl_zero.
  - destruct IHmulti as [n IH].
    exists (S n).
    apply multi_step_more with (y:=y); assumption.
Qed.

Lemma multi_idx_start_with_stop_states_unchanged:
  forall n c st1 st2,
    multistep_idx 〈STOP, st1〉 〈c, st2〉 n ->
    c = STOP /\ st1 = st2.
Proof.
  intros n c st1 st2 H.
  dependent induction H.
  - auto.
  - apply IHmulti_idx; auto. inversion H.
Qed. 