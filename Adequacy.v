From TL Require Import Identifier Environment Imperative Types Augmented WellFormedness Bridge.

Lemma adequacy_of_event_steps:
  forall Γ pc c m cfg',
    wf_mem m Γ ->
    -{ Γ, pc ⊢ c }- ->
    〈c, m 〉 ⇒ cfg' ->
    exists ev, event_step Γ ev 〈c, m 〉 cfg'.
Proof.
Admitted.

Theorem bridge_adequacy:
  forall n c m m_end,
    multistep_idx 〈c, m 〉 〈STOP, m_end 〉 n ->
    forall Γ pc, 
      -{ Γ, pc ⊢ c }-  ->
      wf_mem m Γ  ->
      (c = STOP \/
        exists ev n' cfg' k,
          (〈 c, m 〉 ↷ (Γ, ev, n') cfg') /\
          multistep_idx cfg' 〈STOP, m_end 〉 k /\ k < n).

Proof.
Admitted.