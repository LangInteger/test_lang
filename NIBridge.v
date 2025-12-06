From TL Require Import Identifier Environment Imperative Types Augmented Bridge.
From TL Require Import WellFormedness LowEq NIexp.
From TL.lib Require Import InductionPrinciple.

Lemma skip_bridge_properties:
  forall Γ n m ev c_end m_end,
    bridge_step_num Γ Low 〈SKIP, m 〉 〈c_end, m_end 〉 ev n ->
    m_end = m /\ c_end = STOP /\ n = 0 /\ ev = EmptyEvent.
Proof.
Admitted.
  (* intros.
  inversion H.
  - inversion H0.
    inversion H7.
    auto.
  - inversion H0.
    inversion H8.
    auto.
  - inversion H0.
    inversion H9.
    
    exfalso.
    eauto.
Qed. *)

Definition NI_idx (n1: nat): Prop :=
  forall Γ pc c,
    -{ Γ, pc ⊢ c }- ->
    forall d e st1 st2 evt1 evt2 st1' st2' n2,
    state_low_eq Γ st1 st2 ->
    ( 〈 c, st1 〉 ↷ (Γ, evt1, n1) 〈 d, st1' 〉 ) ->
    ( 〈 c, st2 〉 ↷ (Γ, evt2, n2) 〈 e, st2' 〉 ) ->
    state_low_eq Γ st1' st2'
    /\ d = e 
    /\ (low_event Γ Low evt1 <-> low_event Γ Low evt2)
    /\  (low_event Γ Low evt1 -> evt1 = evt2).

Theorem ni_bridge_num:
  forall n, NI_idx (n).
Proof.
Admitted.
  (* apply strongind;
  unfold NI_idx.
  (* Base case *)
  {
    intros Γ pc c  H; subst.
    induction H; intros.
    {
      
    }
  } *)
