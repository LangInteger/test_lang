From TL Require Import Identifier Environment Imperative.

Inductive level :=
  | Low : level
  | High : level.

Inductive flowsto : level -> level -> Prop :=
  | flowsto_sym: forall l, flowsto l l
  | flowsto_ord: flowsto Low High.

Notation "l '⊑' l'" := (flowsto l l') (at level 35).

Definition join (l1 l2 : level) : level :=
  match l1, l2 with
  | Low, Low => Low
  | _, _     => High
  end.
Notation "l '⊔' l'" := (join l l') (at level 34).

Lemma level_flowsto_join: forall l1 l2 l3,
    l1 ⊔ l2 ⊑ l3 ->  l1 ⊑ l3 /\ l2 ⊑ l3.
Proof.
  intros l1 l2 l3 H.
  destruct l1; destruct l2; destruct l3; simpl in *; split; try ( inversion H; apply flowsto_ord); try(apply flowsto_sym).
Qed.

Lemma level_equal_join: forall l1 l2 l3,
    l1 ⊔ l2 = l3 ->  l1 ⊑ l3 /\ l2 ⊑ l3.
Proof.
  intros l1 l2 l3 H.
  destruct l1; destruct l2; destruct l3; simpl in *; split; try ( inversion H; apply flowsto_ord); try(apply flowsto_sym).
Qed.

Lemma join_twice_eq : forall l1 l2,
    (l1 ⊔ l2) ⊔ l2 = l1 ⊔ l2.
Proof. 
  intros l1 l2.
  destruct l1; destruct l2; simpl; auto. 
Qed.

Lemma join_twice_not_bigger : forall l1 l2,
    (l1 ⊔ l2) ⊔ l2 ⊑ l1 ⊔ l2.
Proof. 
  intros l1 l2.
  destruct l1; destruct l2; simpl; apply flowsto_sym.
Qed.

Lemma join_smaller_result_smaller_right: forall l1 l2 l3,
    l1 ⊑ l3 ->
    l2 ⊔ l1 ⊑ l2 ⊔ l3.
Proof.
  intros l1 l2 l3 H.
  destruct l1; destruct l2; destruct l3; simpl in *; try (apply flowsto_ord); try (apply flowsto_sym); auto.
Qed.

Lemma join_smaller_result_smaller_left: forall l1 l2 l3,
    l1 ⊑ l3 ->
    l1 ⊔ l2 ⊑ l3 ⊔ l2.
Proof.
  intros l1 l2 l3 H.
  destruct l1; destruct l2; destruct l3; simpl in *; try (apply flowsto_ord); try (apply flowsto_sym); auto.
Qed.


Lemma level_transitive: forall l1 l2 l3,
    l1 ⊑ l2 ->
    l2 ⊑ l3 ->
    l1 ⊑ l3.
Proof.
  intros l1 l2 l3 H12 H23.
  destruct l1; destruct l2; destruct l3; simpl in *; try (apply flowsto_ord); try (apply flowsto_sym); auto.
Qed.

Definition typenv := @Env level.
Reserved Notation "'{{' Γ '⊢' e ':' l '}}'" (at level 0, Γ at level 50, e at level 99).
(* no subtyping *)
Inductive exp_has_level : typenv -> exp -> level -> Prop :=
  | T_Const : forall Γ n,
      {{ Γ ⊢ (ENum n) : Low }}
  | T_Id : forall Γ x l,
      Γ x = Some l ->
      {{ Γ ⊢ (EId x) : l }}
  | T_Plus : forall Γ e1 e2 l1 l2 l,
      {{ Γ ⊢ e1 : l1 }} ->
      {{ Γ ⊢ e2 : l2 }} ->
      l1 ⊔ l2 = l ->
      {{ Γ ⊢ (EPlus e1 e2) : l }}
where "'{{' Γ '⊢' e ':' l '}}' " := (exp_has_level Γ e l).

Reserved Notation  "'-{' Γ ',' pc '⊢' c '}-'" (at level 0, Γ at level 55, pc at level 35).
Inductive cmd_has_type : typenv -> level -> cmd -> Prop :=
  | T_Skip : forall Γ pc,
      -{ Γ, pc ⊢ CSkip }-
  | T_Assign : forall Γ pc x e le lx,
      {{ Γ ⊢ e : le}} ->
      Γ x = Some lx ->
      le ⊔ pc ⊑ lx ->
      -{ Γ, pc ⊢ (x ::= e) }-
  | T_Seq : forall Γ pc c1 c2,
      -{ Γ, pc ⊢ c1 }- ->
      -{ Γ, pc ⊢ c2 }- ->
      -{ Γ, pc ⊢ (c1 ;; c2) }-
  | T_If : forall Γ pc e l pc' c1 c2,
      {{ Γ ⊢ e : l }} ->
      pc ⊔ l ⊑ pc' ->
      -{ Γ, pc' ⊢ c1 }- ->
      -{ Γ, pc' ⊢ c2 }- ->
      -{ Γ, pc ⊢ (IFB e THEN c1 ELSE c2 FI) }-
  | T_While : forall Γ pc e l pc' c,
      {{ Γ ⊢ e : l }} ->
      pc ⊔ l ⊑ pc' ->
      -{ Γ, pc' ⊢ c }- ->
      -{ Γ, pc ⊢ (WHILE e DO c END) }-
where "'-{' Γ ',' pc '⊢' c '}-'" := (cmd_has_type Γ pc c).