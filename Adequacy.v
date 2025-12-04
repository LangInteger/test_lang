From TL Require Import Identifier Environment Imperative Types Augmented WellFormedness Bridge.
Require Import Coq.Program.Equality.

Lemma adequacy_of_event_steps:
  forall Γ pc c m cfg',
    wf_mem m Γ ->
    -{ Γ, pc ⊢ c }- ->
    〈c, m 〉 ⇒ cfg' ->
    exists ev, event_step Γ ev 〈c, m 〉 cfg'.
Proof.
  intros Γ pc c m [c' m']; intros.
  dependent induction c.
  - (* STOP *)
    inversion H1.
  - (* SKIP *)
    exists EmptyEvent.
    assert (c' = STOP).
    {
      inversion H1.
      auto.
    }
    assert (m' = m).
    {
      inversion H1.
      auto.
    }
    subst.
    constructor; assumption.
  - (* Assignment *)
    inversion H1; subst.
    inversion H0.
    exists (AssignmentEvent lx i v).
    constructor; assumption.
  - (* Sequence *)
    inversion H0.
    inversion H1.
    {
      subst.
      specialize (IHc1 m c1' m' H H6 H10).
      destruct IHc1 as [ev].
      exists ev.
      constructor; auto.   
    }
    {
      subst.
      specialize (IHc1 m STOP m' H H6 H9).
      destruct IHc1 as [ev].
      exists ev.
      constructor; auto.
    }
  - (* If *)
    exists EmptyEvent.
    inversion H1; subst.
    + constructor. assumption.
    + constructor. assumption.
  - (* While *)
    exists EmptyEvent.
    inversion H1; subst; constructor; assumption.
Qed.

Theorem bridge_adequacy:
  forall Γ n c m m_end,
    multistep_idx 〈c, m 〉 〈STOP, m_end 〉 n ->
    forall pc, 
      -{ Γ, pc ⊢ c }-  ->
      wf_mem m Γ  ->
      (c = STOP \/
        exists ev n' cfg' k,
          (〈 c, m 〉 ↷ (Γ, ev, n') cfg') /\
          multistep_idx cfg' 〈STOP, m_end 〉 k /\ k < n).

Proof.
  (* intros Γ n.
  induction n.
  (* n = 0 *)
  {
    left.
    inversion H.
    reflexivity.
  }
  (* Inductive case, P(n-1) => P(n) *)
  {
    right.
    inversion H.
     
  } *)
Admitted.