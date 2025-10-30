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

(* relation between var low eq and val low eq *)
Lemma var_low_eq_means_val_low_eq : forall Γ m1 m2 v1 v2 x l,
  var_low_eq Γ m1 m2 x ->
  Γ x = Some l ->
  m1 x = Some v1 ->
  m2 x = Some v2 ->
  val_low_eq l v1 v2.
Proof. 
  intros Γ m1 m2 v1 v2 x l H_var_leq H_env H_m1 H_m2.
  inversion H_var_leq. subst.
  specialize (env_is_det Γ x l l0 H_env H) as H_level_eq.
  specialize (env_is_det m1 x v1 u H_m1 H0) as H_val1_eq.
  specialize (env_is_det m2 x v2 v H_m2 H1) as H_val2_eq.
  subst.
  assumption.
Qed.

(* state low-eq *)
Inductive state_low_eq : typenv -> state -> state -> Prop :=
  | StateLEq : forall Γ m1 m2,
      wf_mem m1 Γ ->
      wf_mem m2 Γ ->
      (forall x l, Γ x = Some l -> var_low_eq Γ m1 m2 x) ->
      state_low_eq Γ m1 m2.

Lemma state_low_eq_sym : forall Γ m1 m2,
  state_low_eq Γ m1 m2 ->
  state_low_eq Γ m2 m1.
Proof. 
  intros Γ m1 m2 H.
  inversion H.
  apply StateLEq; auto.
  intros x l.
  specialize (H2 x l).
  intros H_env.
  apply var_low_eq_sym.
  apply H2 in H_env.
  assumption.
Qed.

Lemma state_low_eq_wf_refl : forall Γ m,
  wf_mem m Γ ->
  state_low_eq Γ m m.
Proof.
  intros.
  apply StateLEq; auto.
  intros x l.
  apply var_low_eq_wf_refl.
  assumption.
Qed.

Lemma state_low_eq_trans : forall Γ m1 m2 m3,
  state_low_eq Γ m1 m2 ->
  state_low_eq Γ m2 m3 ->
  state_low_eq Γ m1 m3.
Proof.
  intros Γ m1 m2 m3 H12 H23.
  inversion H12.
  inversion H23.
  apply StateLEq; auto.
  intros x l.
  specialize (H1 x l).
  specialize (H7 x l).
  intros H_env.
  specialize (H1 H_env).
  specialize (H7 H_env).
  apply var_low_eq_trans with (m2:=m2); auto.
Qed.


(* relation between states low eq and vars low eq *)
Lemma states_low_eq_means_vars_low_eq : forall Γ m1 m2,
  state_low_eq Γ m1 m2 ->
  forall x l,
    Γ x = Some l ->
    var_low_eq Γ m1 m2 x.
Proof. 
  intros Γ m1 m2 H_state_leq x l H_env.
  inversion H_state_leq.
  specialize (H1 x l).
  apply H1 in H_env.
  assumption.
Qed.

Definition config_low_eq (Γ : typenv) (cfg1 cfg2 : config) : Prop :=
  match cfg1, cfg2 with
  | Config c1 m1, Config c2 m2 =>
      c1 = c2 /\ state_low_eq Γ m1 m2
  end.
