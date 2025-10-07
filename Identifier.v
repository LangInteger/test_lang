Require Import Arith.

Inductive id : Type := 
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  intros id1 id2.
  destruct id1 as [n1].
  destruct id2 as [n2].
  destruct (Nat.eq_dec n1 n2) as [Heq | Hneq].
  - left. rewrite Heq. reflexivity.
  - right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.

Lemma eq_id : forall (T : Type) x (p q : T),
  (if eq_id_dec x x then p else q) = p.
Proof.
  intros.
  destruct (eq_id_dec x x).
  - reflexivity.
  - contradiction n; reflexivity.
Qed.

