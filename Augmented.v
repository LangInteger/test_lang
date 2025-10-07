From TL Require Import Identifier Environment Imperative Types.

Inductive event :=
  | EmptyEvent : event
  | AssignmentEvent : level -> id -> nat -> event.


Inductive event_step : typenv -> event -> config -> config -> Prop :=
  | event_step_assign:
      forall Γ l x e v st st',
        〈 x ::= e,  st〉 ⇒ 〈STOP, st' 〉->
        Γ (x) = Some l ->
        eval e st v ->
        event_step Γ (AssignmentEvent l x v) 〈 x ::= e,  st〉 〈STOP, st' 〉
  | event_skip: forall Γ st,
        〈 SKIP, st 〉 ⇒ 〈 STOP, st 〉 ->
        event_step Γ EmptyEvent 〈 SKIP, st 〉 〈 STOP, st 〉
  | event_empty_branch: 

