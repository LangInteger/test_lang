Require Import TL.Identifier.

Definition Env {X : Type} := id -> option X.

Definition empty_env {X : Type} : @Env X :=
  fun _ => None.

Lemma env_is_det: forall {X: Type} (st: @Env X) x u v,
  st x = Some u ->
  st x = Some v ->
  u = v.
Proof.
  intros.
  rewrite H in H0.
  inversion H0.
  reflexivity.
Qed.

Definition update_env {X : Type} (st : @Env X) (x : id) (n : X) : @Env X :=
  fun x' => if eq_id_dec x x' then (Some n) else st x'.

(* update x with n, then query result for x is n *)
Theorem update_eq {X : Type}: forall (n : X) x st,
  (update_env st x n) x = Some n.
Proof.
  intros.
  unfold update_env.
  destruct eq_id_dec.
  - reflexivity.
  - contradiction n0. reflexivity.
Qed.

Theorem update_neq {X : Type}: forall (n : X) x y st,
  x <> y ->
  (update_env st x n) y = st y.
Proof.
  intros.
  unfold update_env.
  destruct eq_id_dec.
  - contradiction H.
  - reflexivity.
Qed.

(* update x1 with the same value, then query result for any key does not change *)
Theorem update_same {X: Type}: forall (n1:X) x1 x2 (st: Env),
  st x1 = Some n1 -> (update_env st x1 n1) x2 = st x2.
Proof.
  intros.
  unfold update_env.
  destruct eq_id_dec.
  - rewrite <- H. rewrite e. reflexivity.
  - reflexivity.
Qed.

(* first update to x2 is shadowed by the second update *)
Theorem update_shadow {X: Type}: forall (n1:X) (n2:X) x1 x2 (st: Env),
  (update_env (update_env st x2 n1) x2 n2) x1 = (update_env st x2 n2) x1.
Proof.
  intros.
  unfold update_env.
  destruct eq_id_dec.
  - reflexivity.
  - reflexivity.
Qed.

(* the order how x1 x2 are updated does not matter *)
Theorem update_permute {X: Type} : forall (n1:X) (n2:X) x1 x2 x3 (st:Env),
  x2 <> x1 -> 
  (update_env (update_env st x2 n1) x1 n2) x3 = (update_env (update_env st x1 n2) x2 n1) x3.
Proof.
  intros.
  unfold update_env.
  destruct eq_id_dec.
    - destruct eq_id_dec. rewrite e0 in H. rewrite e in H. contradiction H. reflexivity. reflexivity.
    - destruct eq_id_dec. reflexivity. reflexivity.
Qed.
