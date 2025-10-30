From TL Require Import Identifier Environment Imperative Types Augmented Bridge.
From TL Require Import WellFormedness LowEq NIexp.

Theorem ni_bridge_num:
  forall Γ pc c,
    -{ Γ, pc ⊢ c }- ->
    forall d e st1 st2 evt1 evt2 st1' st2' n1 n2,
    state_low_eq Γ st1 st2 ->
    ( 〈 c, st1 〉 ↷ (Γ, evt1, n1) 〈 d, st1' 〉 ) ->
    ( 〈 c, st2 〉 ↷ (Γ, evt2, n2) 〈 e, st2' 〉 ) ->
    state_low_eq Γ st1' st2'
    /\ d = e 
    /\ (low_event Γ Low evt1 <-> low_event Γ Low evt2)
    /\  (low_event Γ Low evt1 -> evt1 = evt2).
Proof.
Admitted.
