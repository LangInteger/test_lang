From TL Require Import Identifier Environment Imperative Types.

Inductive event :=
  | EmptyEvent : event
  | AssignmentEvent : level -> id -> nat -> event.


Inductive event_step : typenv -> event -> config -> config -> Prop :=
  | event_skip: forall Γ st,
        〈 SKIP, st 〉 ⇒ 〈 STOP, st 〉 ->
        event_step Γ EmptyEvent 〈 SKIP, st 〉 〈 STOP, st 〉
  | event_assign: forall Γ l x e v st st',
        〈 x ::= e,  st〉 ⇒ 〈STOP, st' 〉->
        Γ (x) = Some l ->
        eval e st v ->
        event_step Γ (AssignmentEvent l x v) 〈 x ::= e,  st〉 〈STOP, st' 〉
  | event_empty_branch: forall Γ e c1 c2 c' st,
        〈 IFB e THEN c1 ELSE c2 FI, st 〉 ⇒ 〈 c', st 〉 ->
        event_step Γ EmptyEvent 〈 IFB e THEN c1 ELSE c2 FI, st 〉 〈 c', st 〉
  | event_empty_loop: forall Γ e c c' st,
        〈 WHILE e DO c END, st 〉 ⇒ 〈 c', st 〉 ->
        event_step Γ EmptyEvent 〈 WHILE e DO c END, st 〉 〈 c', st 〉
  | event_seq1: forall Γ ev c1 c1' c2 st st',
        event_step Γ ev 〈 c1, st 〉 〈 c1', st' 〉 ->
        c1' <> STOP ->
        event_step Γ ev 〈 c1 ;; c2, st 〉 〈 c1' ;; c2, st' 〉
  | event_seq2: forall Γ ev c1 c2 st st', 
        event_step Γ ev 〈 c1, st 〉 〈 STOP, st' 〉 ->
        event_step Γ ev 〈 c1 ;; c2, st 〉 〈 c2, st' 〉.
