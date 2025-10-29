From TL Require Import Identifier Environment Imperative WellFormedness Types.

(* val low-eq *)

Inductive val_low_eq : level -> nat -> nat -> Prop :=
  | VLEqH : forall u v, val_low_eq High u v
  | VLEqL : forall u v, u = v -> val_low_eq Low u v.

Lemma val_low_eq_flowsto : forall l l' u v,
  l ⊑ l' -> 
  val_low_eq l u v -> 
  val_low_eq l' u v.
Proof. 
  intros. inversion H.  
  - rewrite <- H2. apply H0.
  - apply VLEqH.
Qed.

Lemma val_low_eq_sym : forall l u v,
  val_low_eq l u v 
  -> val_low_eq l v u.
Proof.
  intros. inversion H. 
  - apply VLEqH.
  - apply VLEqL. auto.
Qed.

Lemma val_low_eq_trans : forall l u v w,
  val_low_eq l u v ->
  val_low_eq l v w ->
  val_low_eq l u w.
Proof.
  intros.
  destruct l.
  {
    inversion H.
    inversion H0.
    apply VLEqL.
    rewrite <- H2. apply H1.
  }
  {
    apply VLEqH.
  }
Qed.

Lemma val_low_eq_refl : forall l v,
  val_low_eq l v v.
Proof.
  intros. destruct l.
  {
    apply VLEqL. auto.
  }
  {
    apply VLEqH.
  }
Qed.

(* var low-eq *)
Inductive var_low_eq : typenv -> state -> state -> id -> Prop :=
  | VarLEq : forall Γ l u v m1 m2 x,
      Γ x = Some l ->
      m1 x = Some u -> 
      m2 x = Some v -> 
      val_low_eq l u v -> 
      var_low_eq Γ m1 m2 x.

(* build upon wellformedness *)
Lemma var_low_eq_wf_refl : forall Γ m x l,
  wf_mem m Γ ->
  Γ x = Some l -> 
  var_low_eq Γ m m x.
Proof.
  intros. 
  unfold wf_mem in H.
  destruct H.
  specialize (H1 x l H0) as H1.
  destruct H1.
  apply VarLEq with (l:=l) (u:=x0) (v:=x0); auto.
  apply val_low_eq_refl.
Qed.

Lemma var_low_eq_sym : forall Γ m1 m2 x,
  var_low_eq Γ m1 m2 x
  -> var_low_eq Γ m2 m1 x.
Proof.
  intros. 
  inversion H.
  apply VarLEq with (l:=l) (u:=v) (v:=u); auto.
  apply val_low_eq_sym. auto.
Qed.

Lemma var_low_eq_trans : forall Γ m1 m2 m3 x,
  var_low_eq Γ m1 m2 x
  -> var_low_eq Γ m2 m3 x
  -> var_low_eq Γ m1 m3 x.
Proof.
  intros. 
  inversion H.
  inversion H0.
  apply VarLEq with (l:=l) (u:=u) (v:=v0); auto.
  specialize (env_is_det Γ x l l0 H1 H9) as H_level_eq.
  specialize (env_is_det m2 x v u0 H3 H10) as H_mid_val_eq.
  rewrite <- H_level_eq in H12.
  rewrite <- H_mid_val_eq in H12.
  apply val_low_eq_trans with (v:=v);auto.
Qed.


