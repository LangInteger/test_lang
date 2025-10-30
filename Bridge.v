From TL Require Import Identifier Environment Imperative Types Augmented WellFormedness.
From Coq Require Import Program.Equality.

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


Lemma preservation_wf_bridge:
  forall Γ pc c c' m m' ev n,
    -{ Γ , pc ⊢ c }- ->
    (〈c, m 〉 ↷ (Γ, ev, n) 〈c', m' 〉) ->
    wf_mem m Γ ->
    (wf_mem m' Γ  /\ (c' <> STOP -> -{ Γ , pc ⊢ c' }- )) .

Proof.
  intros.
  dependent induction H0.

  - inversion H0. apply preservation_wf_event_step with (e:=evt) (c:=c) (m:=m); auto.
  - inversion H1. apply preservation_wf_event_step with (e:=evt) (c:=c) (m:=m); auto.
  - inversion H2. destruct cfg' as [c'' m'']. 
    apply IHbridge_step_num with (c:=c'') (m:=m'');    
    auto.
    + specialize (preservation_wf_event_step Γ evt' c m c'' m'' pc H H3 H4 ) as [H_ret1 H_ret2].
      apply H_ret2. apply H0.
    + specialize (preservation_wf_event_step Γ evt' c m c'' m'' pc H H3 H4 ) as [H_ret1 H_ret2]. auto.
Qed.