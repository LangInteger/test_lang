From TL Require Import Identifier Environment Imperative Types Augmented Bridge.
From TL Require Import WellFormedness LowEq. 
From TL Require Import NIBridge.
From TL Require Import Adequacy.
From TL.lib Require Import InductionPrinciple.
From Coq Require Import Lia.
Require Import Coq.Program.Equality.

Definition TINI_idx (n1: nat): Prop :=
  forall Γ c st1 st1_end st2 st2_end pc n2,
    -{ Γ, pc ⊢ c }- ->
    state_low_eq Γ st1 st2 ->
    multistep_idx 〈c, st1 〉 〈STOP, st1_end 〉 n1 ->
    multistep_idx 〈c, st2 〉 〈STOP, st2_end 〉 n2 ->
    state_low_eq Γ st1_end st2_end.

Lemma tini_idx: forall n1, TINI_idx n1.
Proof.
  apply strongind.
  {
    unfold TINI_idx. intros. 
    inversion H1; subst; inversion H2; subst; 
    auto; inversion H3.
  }
  {
    unfold TINI_idx.
    intros.
    inversion H1.
    specialize (bridge_adequacy (S n) c st1 st1_end H2 Γ pc H0 H4) as [H_adeq_st11 | H_adeq_st12]; inversion H2; subst.
    + inversion H11.
    + specialize (bridge_adequacy n2 c st2 st2_end H3 Γ pc H0 H5) as [H_adeq_st21 | H_adeq_st22]. subst.
      * inversion H11.
      * destruct H_adeq_st12 as [ev1 [n1' [cfg1' [k1 [H_bridge1 [H_multistep1 H_index1]]]]]].
        destruct H_adeq_st22 as [ev2 [n2' [cfg2' [k2 [H_bridge2 [H_multistep2 H_index2]]]]]].

        destruct cfg1' as [c1 st1'].
        destruct cfg2' as [c2 st2'].

        specialize (ni_bridge_num Γ pc c H0 c1 c2 st1 st2 ev1 ev2 st1' st2' n1' n2' H1 H_bridge1 H_bridge2) as [H_leq' [H_c_eq [H_low_event_eq H_event_eq]]].
        subst.

        assert (k1 <= n) as H_k1 by lia.
        (* specialize (H k1 H_k1 Γ c2 st1' st1_end st2' st2_end pc k2 H0 H_leq' H_index1 H_index2) as H_ret. *)

        specialize (preservation_wf_bridge Γ pc c c2 st2 st2' ev2 n2' H0 H_bridge2 H5) as [H_wf_mem' H_wf_cmd'].

         destruct (eq_cmd_stop_dec c2) as [Heq | Hneq].
         {
            subst. 
            assert (st1' = st1_end). 
            {
              apply multi_idx_start_with_stop_states_unchanged with (n:=k1) (c:=STOP) in H_multistep1 as [_ H_st1_eq].
              assumption.
            }
            assert (st2' = st2_end). 
            {
              apply multi_idx_start_with_stop_states_unchanged with (n:=k2) (c:=STOP) in H_multistep2 as [_ H_st2_eq].
              assumption.
            }
            subst. assumption.
         }
         {
            apply H with (m:=k1) (c:=c2) (st1:=st1') (st2:=st2') (pc:=pc) (n2:=k2);auto.
         }
  }
Qed.
   
Theorem TINI:
  forall Γ c st1 st2 st1_end st2_end pc,
    -{ Γ, pc ⊢ c }- ->
    state_low_eq Γ st1 st2 ->
    〈 c, st1 〉 ⇒* 〈 STOP, st1_end 〉 ->
    〈 c, st2 〉 ⇒* 〈 STOP, st2_end 〉 ->
    state_low_eq Γ st1_end st2_end.
Proof.
  intros Γ c st1 st2 st1_end st2_end pc H_wt H_leq H_st1 H_st2.
  apply multi_implies_multi_idx in H_st1.
  apply multi_implies_multi_idx in H_st2.
  destruct H_st1 as [n1 Hst1'].
  destruct H_st2 as [n2 Hst2'].
  apply tini_idx with (c:=c) (n1:=n1) (n2:=n2) (st1:=st1) (st2:=st2) (pc:=pc); assumption.
Qed.
  
