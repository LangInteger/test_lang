From TL Require Import Identifier Environment Imperative Types Augmented.

Definition wf_mem (m : state) (Γ : typenv) : Prop :=
  (forall x u, m x = Some u -> exists l, Γ x = Some l)
  /\
  (forall x l, Γ x = Some l -> exists u, m x = Some u).

Lemma update_preserves_wf_mem: forall m Γ x l v,
    wf_mem m Γ ->
    Γ x = Some l ->
    wf_mem (update_env m x v) Γ.
Proof.
Admitted.

(* - m is well-formed w.r.t. Γ
   - c is well-typed under Γ and pc (if c is not stop)
 *)
Definition wf_cfg (cfg : config) (Γ : typenv) (pc: level): Prop :=
  match cfg with
  | Config c m => wf_mem m Γ /\ (c <> STOP -> -{ Γ, pc ⊢ c }-)
  end.

Notation  "'={' Γ ',' pc '⊢' cfg '}='" := 
  (wf_cfg cfg Γ pc ) (at level 40).

Lemma pc_lowering_assign:
        forall Γ pc x e (le:level) (lx:level) pc',
          -{ Γ, pc' ⊢ (x ::= e)}- -> pc ⊑ pc' -> -{ Γ, pc ⊢ (x ::= e)}-.
Proof.
  intros Γ pc x e le lx pc' H_wf_c H_flow.
  inversion H_wf_c.
  apply T_Assign with (le:=le0) (lx:=lx0); auto.
  specialize (join_smaller_result_smaller_right pc le0 pc' H_flow) as H_join.
  specialize (level_transitive (le0 ⊔ pc) (le0 ⊔ pc') lx0 H_join H5) as H_le.
  assumption.
Qed.


Theorem preservation_wf_cfg: forall Γ pc cfg cfg',
    ={ Γ, pc ⊢ cfg }= ->
    cfg ⇒ cfg' ->
    ={ Γ, pc ⊢ cfg'}= .
Proof.

  intros Γ pc [c m] [c' m'].
  intros [H_wf_mem H_wf_cmd] H_step.

  remember (Config c m) as cfg0 eqn:Heq0.
  remember (Config c' m') as cfg1 eqn:Heq1.

  (* to make the I.H. stronger, we need to *)
  revert c m c' m' Heq0 Heq1 H_wf_mem H_wf_cmd.

  induction H_step;
  intros cc mm cc' mm' Heq0 Heq1 H_wf_mem H_wf_cmd;
  inversion Heq0; inversion Heq1; subst; simpl in *.

  (* step_skip *)
  - unfold wf_cfg. split.
    + apply H_wf_mem.
    + contradiction.
  (* step_assign *)
  - unfold wf_cfg. split.
    + assert (H_assign_neq_stop : x ::= e <> STOP) 
        by apply assign_neq_stop.
      specialize (H_wf_cmd H_assign_neq_stop) as H_wf_cmd'.
      inversion H_wf_cmd'.
      apply update_preserves_wf_mem with (l:=lx).
      assumption.
      assumption.
    + contradiction.
  (* step_seq1 *)
  - assert (H_seq_neq_stop : (c1 ;; c2) <> STOP) by apply seq_neq_stop.
    (* build C1_well_typed *)
    specialize (H_wf_cmd H_seq_neq_stop) as H_wf_cmd'.
    inversion H_wf_cmd'.
    assert (C1_well_typed : c1 <> STOP -> -{ Γ, pc ⊢ c1 }-).
      { 
        destruct (eq_cmd_stop_dec c1) as [Heq | Hneq].
        { contradiction. }
        { intro. apply H4. }
      }
    (* use I.H. *)
    assert (config_eq_1 : 〈 c1, mm 〉 = 〈 c1, mm 〉) by reflexivity.
    assert (config_eq_2 : 〈 c1', mm' 〉 = 〈 c1', mm' 〉) by reflexivity.
    specialize IHH_step with (c:=c1) (m:=mm) (c':=c1') (m':=mm').
    specialize (IHH_step config_eq_1 config_eq_2 H_wf_mem C1_well_typed) as [IH1 IH2].
    (* use IH1 IH2 *)
    split.
    + apply IH1.
    + intro. apply T_Seq. apply IH2 in H. assumption. assumption.
  (* step_seq2 *)
  - assert (H_seq_neq_stop : (c1 ;; cc') <> STOP) by apply seq_neq_stop.
    (* build C1_well_typed *)
    specialize (H_wf_cmd H_seq_neq_stop) as H_wf_cmd'.
    inversion H_wf_cmd'.
    assert (C1_well_typed : c1 <> STOP -> -{ Γ, pc ⊢ c1 }-).
      { 
        destruct (eq_cmd_stop_dec c1) as [Heq | Hneq].
        { contradiction. }
        { intro. apply H3. }
      }
    (* use I.H. *)
    assert (config_eq_1 : 〈 c1, mm 〉 = 〈 c1, mm 〉) by reflexivity.
    assert (config_eq_2 : 〈 STOP, mm' 〉 = 〈 STOP, mm' 〉) by reflexivity.
    specialize IHH_step with (c:=c1) (m:=mm) (c':=STOP) (m':=mm').
    specialize (IHH_step config_eq_1 config_eq_2 H_wf_mem C1_well_typed) as [IH1 IH2].
    (* use IH1 IH2 *)
    split.
    + apply IH1.
    + destruct (eq_cmd_stop_dec cc') as [Heq | Hneq].
        { contradiction. }
        { intro. apply H4. }
  (* step_if1 *)
  - split.
    + apply H_wf_mem.
    + intro. 
      assert (H_if_neq_stop : (IFB e THEN cc' ELSE c2 FI) <> STOP) 
        by apply if_neq_stop.
      specialize (H_wf_cmd H_if_neq_stop) as H_wf_cmd'.
      inversion H_wf_cmd'.
      apply level_equal_join in H8 as [H81 H82].
      apply pc_lowering with (pc:=pc) in H9.
      apply H9.
      apply H81.
  (* step_if2 *)
  - split.
    + apply H_wf_mem.
    + intro.
      assert (H_if_neq_stop : (IFB e THEN c1 ELSE cc' FI) <> STOP) 
        by apply if_neq_stop.
      specialize (H_wf_cmd H_if_neq_stop) as H_wf_cmd'.
      inversion H_wf_cmd'.
      apply level_flowsto_join in H7 as [H81 H82].
      apply pc_lowering with (pc:=pc) in H9.
      apply H9.
      apply H81.
  (* while *)
  - split.
    + apply H_wf_mem.
    + intro.
      assert (H_while_neq_stop : (WHILE e DO c END) <> STOP) 
        by apply while_neq_stop.
      specialize (H_wf_cmd H_while_neq_stop) as H_wf_cmd'.
      inversion H_wf_cmd'.
      assert (Hwhile_join : -{ Γ, pc ⊔ l ⊢ WHILE e DO c END }-).
        { apply T_While with (l := l) (pc' := pc ⊔ l).
            -- apply H2.
            -- apply join_twice_not_bigger.
            -- apply pc_lowering with (pc':=pc');auto.
        }
      apply T_If with (pc:=pc) (l:=l) (pc':=pc').
      * apply H2.
      * apply H5.
      * apply T_Seq. 
        -- apply H6.
        -- rewrite <- H5. apply Hwhile_join.
      * apply T_Skip. 
Qed.