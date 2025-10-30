From TL Require Import Identifier Environment Imperative WellFormedness LowEq Types.
From Coq Require Import Lia.

Theorem non_interference_exp: forall Γ m1 m2 v1 v2 e l,
  state_low_eq Γ m1 m2 ->
  {{ Γ ⊢ e : l }} ->
  eval e m1 v1 ->
  eval e m2 v2 ->
  val_low_eq l v1 v2.
Proof. 
  intros.

  revert v2 H2.
  revert v1 H1.
  
  induction H0; intros; inversion H1; inversion H2; subst; clear H1 H2.

  {
    apply val_low_eq_refl.
  }
  {
    specialize (states_low_eq_means_vars_low_eq Γ m1 m2 H x l H0) as H_var_eq.
    apply var_low_eq_means_val_low_eq with (Γ:=Γ) (m1:=m1) (m2:=m2) (x:=x); auto.
  }
  {
    specialize (IHexp_has_level1 H u H5 u0 H12) as H_leq1.
    specialize (IHexp_has_level2 H v H6 v0 H13) as H_leq2.

    induction H_leq1; induction H_leq2; try (apply VLEqH); try (apply VLEqL; lia).

    (* induction H_leq1.
    - apply VLEqH.
    - induction H_leq2.
      + apply VLEqH.
      + apply VLEqL. lia. *)
  }
Qed.