From TL Require Import Identifier Environment Imperative Types Augmented Bridge.
From TL Require Import WellFormedness LowEq. 
From TL Require Import NIBridge.
From TL Require Import InductionPrinciple.

Lemma TINI_idx:
  forall Γ c st1 st2 st1_end st2_end n1 n2 pc,
    -{ Γ, pc ⊢ c }- ->
    state_low_eq Γ st1 st2 ->
    multistep_idx 〈 c, st1 〉 〈 STOP, st1_end 〉 n1 ->
    multistep_idx 〈 c, st2 〉 〈 STOP, st2_end 〉 n2 ->
    state_low_eq Γ st1_end st2_end.
Proof.
  intros Γ c st1 st2 st1_end st2_end n1 n2 pc H_wt H_leq H_st1 H_st2.
  
  revert Γ c st1 st2 H_wt H_leq H_st1 H_st2.

  apply strongind.
  - intros. inversion H_st1. inversion H_st2.
    + subst. apply H_leq.
    + subst. inversion H0.
  - intros.
    inversion H_st1; subst.  
    inversion H_st2.
    + subst. inversion H0.
    + subst.
      destruct y as [c1 st1'].
      destruct y0 as [c2 st2'].
   
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
  apply TINI_idx with (c:=c) (n1:=n1) (n2:=n2) (st1:=st1) (st2:=st2) (pc:=pc); assumption.
Qed.
  
