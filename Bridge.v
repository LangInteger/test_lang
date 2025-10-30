From TL Require Import Identifier Environment Imperative Types Augmented.

Inductive low_event : typenv -> level -> event -> Prop :=
  | LEvent_Assign_Low : forall Γ l l' x v,
      l' ⊑ l ->
      low_event Γ l (AssignmentEvent l' x v).

(* including both empty and high *)
Definition high_event Γ l e :=
  ~ low_event Γ l e.

Definition low_event_step Γ l evt cfg cfg' :=
  event_step Γ evt cfg cfg' /\ low_event Γ l evt.

Definition high_event_step Γ l evt cfg cfg' :=
  event_step Γ evt cfg cfg' /\ high_event Γ l evt.



Inductive bridge_step_num: typenv -> level -> config -> config -> event -> nat -> Prop :=
  (* ends with either a low event or stop *)
  | bridge_low_num: forall Γ l evt cfg cfg',
      low_event_step Γ l evt cfg cfg' ->
      bridge_step_num Γ l cfg cfg' evt 0
  | bridge_stop_num: forall Γ l evt cfg cfg',
      high_event_step Γ l evt cfg cfg' ->
      is_stop cfg' ->
      bridge_step_num Γ l cfg cfg' evt 0
  | bridge_trans_num: forall Γ l evt' evt'' cfg cfg' cfg'' n,
      high_event_step Γ l evt' cfg cfg' ->
      is_not_stop cfg' ->
      bridge_step_num Γ l cfg' cfg'' evt'' n ->
      bridge_step_num Γ l cfg cfg'' evt'' (S n).

Notation " t '↷' '(' Γ ',' obs ',' n ')'  t' " :=
  (bridge_step_num Γ Low t t' obs n) (at level 40).
