From TL Require Import Identifier Environment Imperative Types Augmented.

Inductive low_event : typeenv -> level -> event -> Prop :=
  | LEvent_Assign_Low : forall Γ l l' x v,
      l' ⊑ l ->
      low_event Γ l (AssignmentEvent l' x v).

