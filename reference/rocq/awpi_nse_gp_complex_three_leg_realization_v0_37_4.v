
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_perspective_action_v0_11_2.
Require Import awpi_nse_gp_closed_action_envelope_v0_19_2.
Require Import awpi_nse_gp_finite_cutoff_envelope_v0_20_0.
Require Import awpi_nse_gp_leray_modal_triad_adapter_v0_13_3.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_gp_source_class_ownership_v0_25_4.
Require Import awpi_nse_gp_parent_degree_reproduction_v0_26_0.
Require Import awpi_nse_gp_to_m7_route_v0_28_3.
Require Import awpi_nse_gp_gk_cohomology_realization_v0_35_3.
Require Import awpi_nse_gp_three_leg_route_realization_v0_36_4.

Import ListNotations.
Open Scope R_scope.

Module NSE_GP_COMPLEX_THREE_LEG_REALIZATION.

Module PA := NSE_GP_PERSPECTIVE_ACTION.
Module CE := NSE_GP_CLOSED_ACTION_ENVELOPE.
Module CU := NSE_GP_FINITE_CUTOFF_ENVELOPE.
Module LM := NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.
Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module SO := NSE_GP_SOURCE_CLASS_OWNERSHIP.
Module PR := NSE_GP_PARENT_DEGREE_REPRODUCTION.
Module MR := NSE_GP_TO_M7_ROUTE.
Module GK := NSE_GP_GK_COHOMOLOGY_REALIZATION.
Module TL := NSE_GP_THREE_LEG_ROUTE_REALIZATION.

(* ===================================================================== *)
(* Closed action envelopes for ACTUAL signed source legs                  *)
(* ===================================================================== *)

Definition singleton_source_class
  (r d M : R)
  (Henv : CE.ActionEnvelope (LM.pos r) d M)
  : SO.PhysicalSourceClass.
Proof.
  assert (Hd : 0 <= d).
  {
    unfold CE.ActionEnvelope in Henv.
    tauto.
  }
  assert (HM : 0 <= M).
  {
    unfold CE.ActionEnvelope in Henv.
    tauto.
  }
  refine {|
    SO.psc_atoms := [r];
    SO.psc_capacity := d;
    SO.psc_budget := M;
    SO.psc_capacity_nonnegative := Hd;
    SO.psc_budget_nonnegative := HM
  |}.
  simpl.
  replace (r + 0) with r by ring.
  exact Henv.
Defined.

Theorem CTL00_SINGLETON_SIGNED_WORK :
  forall r d M : R,
  forall Henv : CE.ActionEnvelope (LM.pos r) d M,
    SO.class_signed_work
      (singleton_source_class r d M Henv)
    = r.
Proof.
  intros.
  unfold SO.class_signed_work, singleton_source_class.
  simpl.
  ring.
Qed.

Theorem CTL01_SINGLETON_POSITIVE_WORK :
  forall r d M : R,
  forall Henv : CE.ActionEnvelope (LM.pos r) d M,
    SO.class_positive_work
      (singleton_source_class r d M Henv)
    = LM.pos r.
Proof.
  intros.
  unfold SO.class_positive_work.
  rewrite CTL00_SINGLETON_SIGNED_WORK.
  reflexivity.
Qed.

(* Three signed source legs may be grouped physically BEFORE action.
   Individual positive-source envelopes imply a closed envelope for the
   positive part of their signed sum. *)
Theorem CTL02_THREE_SIGNED_SOURCE_GROUP_ENVELOPE :
  forall r1 r2 r3 d1 d2 d3 M1 M2 M3 : R,
    CE.ActionEnvelope (LM.pos r1) d1 M1 ->
    CE.ActionEnvelope (LM.pos r2) d2 M2 ->
    CE.ActionEnvelope (LM.pos r3) d3 M3 ->
    CE.ActionEnvelope
      (LM.pos (r1 + r2 + r3))
      ((d1 + d2) + d3)
      ((M1 + M2) + M3).
Proof.
  intros r1 r2 r3 d1 d2 d3 M1 M2 M3 H1 H2 H3.
  pose proof
    (CU.GPCU20_THREE_ATOM_FUSION_PRESERVES_ENVELOPE
      (LM.pos r1) d1 M1
      (LM.pos r2) d2 M2
      (LM.pos r3) d3 M3
      H1 H2 H3) as Hfuse.
  unfold CE.ActionEnvelope in Hfuse |- *.
  destruct Hfuse as [Hd [HM Hpoly]].
  split.
  - exact Hd.
  - split.
    + exact HM.
    + pose proof (LM.GPLM02_POS_THREE_SUBADDITIVE r1 r2 r3) as Hdom.
      pose proof (LM.GPLM00_POS_NONNEG (r1 + r2 + r3)) as Hr.
      pose proof (LM.GPLM00_POS_NONNEG r1) as H1p.
      pose proof (LM.GPLM00_POS_NONNEG r2) as H2p.
      pose proof (LM.GPLM00_POS_NONNEG r3) as H3p.
      nra.
Qed.

Definition three_source_parent_class
  (r1 r2 r3 d1 d2 d3 M1 M2 M3 : R)
  (H1 : CE.ActionEnvelope (LM.pos r1) d1 M1)
  (H2 : CE.ActionEnvelope (LM.pos r2) d2 M2)
  (H3 : CE.ActionEnvelope (LM.pos r3) d3 M3)
  : SO.PhysicalSourceClass.
Proof.
  pose proof
    (CTL02_THREE_SIGNED_SOURCE_GROUP_ENVELOPE
      r1 r2 r3 d1 d2 d3 M1 M2 M3 H1 H2 H3) as Hgroup.
  assert (Hd : 0 <= (d1 + d2) + d3).
  {
    unfold CE.ActionEnvelope in Hgroup.
    tauto.
  }
  assert (HM : 0 <= (M1 + M2) + M3).
  {
    unfold CE.ActionEnvelope in Hgroup.
    tauto.
  }
  refine {|
    SO.psc_atoms := [r1; r2; r3];
    SO.psc_capacity := (d1 + d2) + d3;
    SO.psc_budget := (M1 + M2) + M3;
    SO.psc_capacity_nonnegative := Hd;
    SO.psc_budget_nonnegative := HM
  |}.
  simpl.
  replace (r1 + (r2 + (r3 + 0))) with (r1 + r2 + r3) by ring.
  exact Hgroup.
Defined.

Theorem CTL03_THREE_SOURCE_PARENT_SIGNED_WORK :
  forall r1 r2 r3 d1 d2 d3 M1 M2 M3 : R,
  forall H1 : CE.ActionEnvelope (LM.pos r1) d1 M1,
  forall H2 : CE.ActionEnvelope (LM.pos r2) d2 M2,
  forall H3 : CE.ActionEnvelope (LM.pos r3) d3 M3,
    SO.class_signed_work
      (three_source_parent_class
        r1 r2 r3 d1 d2 d3 M1 M2 M3 H1 H2 H3)
    =
    r1 + r2 + r3.
Proof.
  intros.
  unfold SO.class_signed_work, three_source_parent_class.
  simpl.
  ring.
Qed.

(* ===================================================================== *)
(* Actual complex/helical triad + three source-leg action envelopes       *)
(* ===================================================================== *)

Record ComplexThreeLegPhysicalCertificate : Type := {
  ctl_C : CH.C2;
  ctl_uk : CH.C2;
  ctl_up : CH.C2;
  ctl_uq : CH.C2;

  ctl_duk : CH.C2;
  ctl_dup : CH.C2;
  ctl_duq : CH.C2;

  ctl_Nk : CH.C2;
  ctl_Np : CH.C2;
  ctl_Nq : CH.C2;

  ctl_nu : R;
  ctl_lk : R;
  ctl_lp : R;
  ctl_lq : R;
  ctl_dc : R;

  ctl_modal :
    CH.ComplexTriadCertificate
      ctl_C ctl_uk ctl_up ctl_uq
      ctl_duk ctl_dup ctl_duq
      ctl_Nk ctl_Np ctl_Nq
      ctl_nu ctl_lk ctl_lp ctl_lq ctl_dc;

  ctl_dk : R;
  ctl_dp : R;
  ctl_dq : R;

  ctl_Mk : R;
  ctl_Mp : R;
  ctl_Mq : R;

  ctl_env_k :
    CE.ActionEnvelope
      (LM.pos (CH.csource1 ctl_C ctl_Nk ctl_up ctl_uq))
      ctl_dk ctl_Mk;

  ctl_env_p :
    CE.ActionEnvelope
      (LM.pos (CH.csource2 ctl_C ctl_uk ctl_Np ctl_uq))
      ctl_dp ctl_Mp;

  ctl_env_q :
    CE.ActionEnvelope
      (LM.pos (CH.csource3 ctl_C ctl_uk ctl_up ctl_Nq))
      ctl_dq ctl_Mq
}.

Definition ctl_rk (T : ComplexThreeLegPhysicalCertificate) : R :=
  CH.csource1
    (ctl_C T) (ctl_Nk T) (ctl_up T) (ctl_uq T).

Definition ctl_rp (T : ComplexThreeLegPhysicalCertificate) : R :=
  CH.csource2
    (ctl_C T) (ctl_uk T) (ctl_Np T) (ctl_uq T).

Definition ctl_rq (T : ComplexThreeLegPhysicalCertificate) : R :=
  CH.csource3
    (ctl_C T) (ctl_uk T) (ctl_up T) (ctl_Nq T).

Definition ctl_class_k (T : ComplexThreeLegPhysicalCertificate)
  : SO.PhysicalSourceClass :=
  singleton_source_class
    (ctl_rk T) (ctl_dk T) (ctl_Mk T) (ctl_env_k T).

Definition ctl_class_p (T : ComplexThreeLegPhysicalCertificate)
  : SO.PhysicalSourceClass :=
  singleton_source_class
    (ctl_rp T) (ctl_dp T) (ctl_Mp T) (ctl_env_p T).

Definition ctl_class_q (T : ComplexThreeLegPhysicalCertificate)
  : SO.PhysicalSourceClass :=
  singleton_source_class
    (ctl_rq T) (ctl_dq T) (ctl_Mq T) (ctl_env_q T).

Definition ctl_parent_class (T : ComplexThreeLegPhysicalCertificate)
  : SO.PhysicalSourceClass :=
  three_source_parent_class
    (ctl_rk T) (ctl_rp T) (ctl_rq T)
    (ctl_dk T) (ctl_dp T) (ctl_dq T)
    (ctl_Mk T) (ctl_Mp T) (ctl_Mq T)
    (ctl_env_k T) (ctl_env_p T) (ctl_env_q T).

Definition ctl_child_k_action
  (T : ComplexThreeLegPhysicalCertificate) : R :=
  TL.canonical_parent_action (ctl_class_k T).

Definition ctl_child_p_action
  (T : ComplexThreeLegPhysicalCertificate) : R :=
  TL.canonical_parent_action (ctl_class_p T).

Definition ctl_child_q_action
  (T : ComplexThreeLegPhysicalCertificate) : R :=
  TL.canonical_parent_action (ctl_class_q T).

(* No outgoing-capacity premise: the sum of the actual three child actions
   is chosen canonically and therefore dominates each child. *)
Definition ctl_outgoing_capacity
  (T : ComplexThreeLegPhysicalCertificate) : R :=
  ctl_child_k_action T
  + ctl_child_p_action T
  + ctl_child_q_action T.

Theorem CTL10_ACTUAL_COMPLEX_SOURCE_SPLIT :
  forall T : ComplexThreeLegPhysicalCertificate,
    ctl_dc T
    + ctl_nu T * (ctl_lk T + ctl_lp T + ctl_lq T)
        * CH.ctriad (ctl_C T) (ctl_uk T) (ctl_up T) (ctl_uq T)
    =
    ctl_rk T + ctl_rp T + ctl_rq T.
Proof.
  intro T.
  unfold ctl_rk, ctl_rp, ctl_rq.
  exact
    (CH.GPCH40_CERTIFICATE_GIVES_COMPLEX_THREE_SOURCE
      (ctl_C T) (ctl_uk T) (ctl_up T) (ctl_uq T)
      (ctl_duk T) (ctl_dup T) (ctl_duq T)
      (ctl_Nk T) (ctl_Np T) (ctl_Nq T)
      (ctl_nu T) (ctl_lk T) (ctl_lp T) (ctl_lq T) (ctl_dc T)
      (ctl_modal T)).
Qed.

Theorem CTL11_PARENT_CLASS_IS_ACTUAL_DAMPED_TRIAD_SOURCE :
  forall T : ComplexThreeLegPhysicalCertificate,
    SO.class_signed_work (ctl_parent_class T)
    =
    ctl_dc T
    + ctl_nu T * (ctl_lk T + ctl_lp T + ctl_lq T)
        * CH.ctriad (ctl_C T) (ctl_uk T) (ctl_up T) (ctl_uq T).
Proof.
  intro T.
  unfold ctl_parent_class.
  rewrite
    (CTL03_THREE_SOURCE_PARENT_SIGNED_WORK
      (ctl_rk T) (ctl_rp T) (ctl_rq T)
      (ctl_dk T) (ctl_dp T) (ctl_dq T)
      (ctl_Mk T) (ctl_Mp T) (ctl_Mq T)
      (ctl_env_k T) (ctl_env_p T) (ctl_env_q T)).
  symmetry.
  exact (CTL10_ACTUAL_COMPLEX_SOURCE_SPLIT T).
Qed.

Theorem CTL12_CHILD_ACTIONS_NONNEG :
  forall T : ComplexThreeLegPhysicalCertificate,
    0 <= ctl_child_k_action T /\
    0 <= ctl_child_p_action T /\
    0 <= ctl_child_q_action T.
Proof.
  intro T.
  repeat split.
  - apply TL.TL01_CANONICAL_PARENT_ACTION_NONNEG.
  - apply TL.TL01_CANONICAL_PARENT_ACTION_NONNEG.
  - apply TL.TL01_CANONICAL_PARENT_ACTION_NONNEG.
Qed.

Theorem CTL13_OUTGOING_CAPACITY_NONNEG :
  forall T : ComplexThreeLegPhysicalCertificate,
    0 <= ctl_outgoing_capacity T.
Proof.
  intro T.
  unfold ctl_outgoing_capacity.
  destruct (CTL12_CHILD_ACTIONS_NONNEG T) as [Hk [Hp Hq]].
  lra.
Qed.

Theorem CTL14_EACH_CHILD_BOUNDED_BY_CANONICAL_OUTGOING :
  forall T : ComplexThreeLegPhysicalCertificate,
    ctl_child_k_action T <= ctl_outgoing_capacity T /\
    ctl_child_p_action T <= ctl_outgoing_capacity T /\
    ctl_child_q_action T <= ctl_outgoing_capacity T.
Proof.
  intro T.
  unfold ctl_outgoing_capacity.
  destruct (CTL12_CHILD_ACTIONS_NONNEG T) as [Hk [Hp Hq]].
  repeat split; lra.
Qed.

Theorem CTL15_EACH_CHILD_ACTION_BOUNDED_BY_ITS_SOURCE_BUDGET :
  forall T : ComplexThreeLegPhysicalCertificate,
    ctl_child_k_action T <= ctl_Mk T /\
    ctl_child_p_action T <= ctl_Mp T /\
    ctl_child_q_action T <= ctl_Mq T.
Proof.
  intro T.
  repeat split.
  - unfold ctl_child_k_action.
    exact (TL.TL02_CANONICAL_PARENT_ACTION_BUDGET (ctl_class_k T)).
  - unfold ctl_child_p_action.
    exact (TL.TL02_CANONICAL_PARENT_ACTION_BUDGET (ctl_class_p T)).
  - unfold ctl_child_q_action.
    exact (TL.TL02_CANONICAL_PARENT_ACTION_BUDGET (ctl_class_q T)).
Qed.

Theorem CTL16_OUTGOING_CAPACITY_BOUNDED_BY_THREE_SOURCE_BUDGETS :
  forall T : ComplexThreeLegPhysicalCertificate,
    ctl_outgoing_capacity T
    <= ctl_Mk T + ctl_Mp T + ctl_Mq T.
Proof.
  intro T.
  unfold ctl_outgoing_capacity.
  destruct (CTL15_EACH_CHILD_ACTION_BOUNDED_BY_ITS_SOURCE_BUDGET T)
    as [Hk [Hp Hq]].
  lra.
Qed.

(* ===================================================================== *)
(* Construct the v0.36.4 ThreeLegPhysicalRoute directly                  *)
(* ===================================================================== *)

Definition build_complex_three_leg_physical_route
  (T : ComplexThreeLegPhysicalCertificate)
  : TL.ThreeLegPhysicalRoute :=
  {|
    TL.tl_source_class := ctl_parent_class T;

    TL.tl_outgoing_capacity := ctl_outgoing_capacity T;
    TL.tl_outgoing_capacity_nonnegative :=
      CTL13_OUTGOING_CAPACITY_NONNEG T;

    TL.tl_child_k := ctl_child_k_action T;
    TL.tl_child_p := ctl_child_p_action T;
    TL.tl_child_q := ctl_child_q_action T;

    TL.tl_child_k_nonnegative :=
      proj1 (CTL12_CHILD_ACTIONS_NONNEG T);

    TL.tl_child_p_nonnegative :=
      proj1 (proj2 (CTL12_CHILD_ACTIONS_NONNEG T));

    TL.tl_child_q_nonnegative :=
      proj2 (proj2 (CTL12_CHILD_ACTIONS_NONNEG T));

    TL.tl_child_k_bounded :=
      proj1 (CTL14_EACH_CHILD_BOUNDED_BY_CANONICAL_OUTGOING T);

    TL.tl_child_p_bounded :=
      proj1 (proj2
        (CTL14_EACH_CHILD_BOUNDED_BY_CANONICAL_OUTGOING T));

    TL.tl_child_q_bounded :=
      proj2 (proj2
        (CTL14_EACH_CHILD_BOUNDED_BY_CANONICAL_OUTGOING T))
  |}.

Theorem CTL20_COMPLEX_TRIAD_CONSTRUCTS_PARENT_ROUTE :
  forall T : ComplexThreeLegPhysicalCertificate,
    exists P : PR.ParentRoute 3,
      PR.pr_source_class 3 P = ctl_parent_class T.
Proof.
  intro T.
  exists
    (TL.build_three_leg_parent_route
      (build_complex_three_leg_physical_route T)).
  reflexivity.
Qed.

Theorem CTL21_COMPLEX_ROUTE_REPRODUCTION :
  forall T : ComplexThreeLegPhysicalCertificate,
    4 *
      PR.route_child_action
        (TL.build_three_leg_parent_route
          (build_complex_three_leg_physical_route T))
    <=
      PR.pr_parent_action 3
        (TL.build_three_leg_parent_route
          (build_complex_three_leg_physical_route T))
      +
      PR.pr_legal_cost 3
        (TL.build_three_leg_parent_route
          (build_complex_three_leg_physical_route T)).
Proof.
  intro T.
  apply TL.TL24_CANONICAL_ROUTE_REPRODUCTION.
Qed.

Theorem CTL22_COMPLEX_ROUTE_COST_IS_EXPLICIT_DEFICIT :
  forall T : ComplexThreeLegPhysicalCertificate,
    PR.pr_legal_cost 3
      (TL.build_three_leg_parent_route
        (build_complex_three_leg_physical_route T))
    =
    TL.reproduction_deficit
      (TL.canonical_parent_action (ctl_parent_class T))
      (ctl_outgoing_capacity T).
Proof.
  intro T.
  reflexivity.
Qed.

Definition build_complex_three_leg_routes
  (Ts : list ComplexThreeLegPhysicalCertificate)
  : list TL.ThreeLegPhysicalRoute :=
  map build_complex_three_leg_physical_route Ts.

(* ===================================================================== *)
(* Sequence-level: actual complex triads -> three-leg GK -> M7            *)
(* ===================================================================== *)

Record ComplexTriadGKSequenceCertificate : Type := {
  ctg_action : nat -> R;
  ctg_triads : nat -> list ComplexThreeLegPhysicalCertificate;

  ctg_scale_paid : nat -> R;
  ctg_future_paid : nat -> R;
  ctg_residual_paid : nat -> R;

  ctg_action_nonnegative :
    forall n : nat, 0 <= ctg_action n;

  ctg_next_owned :
    forall n : nat,
      ctg_action (S n)
      <=
      PR.forest_child_action
        (TL.build_three_leg_forest
          (build_complex_three_leg_routes (ctg_triads n)));

  ctg_parent_paid :
    forall n : nat,
      PR.forest_parent_action
        (TL.build_three_leg_forest
          (build_complex_three_leg_routes (ctg_triads n)))
      <= ctg_action n;

  ctg_legal_cost_split :
    forall n : nat,
      PR.forest_legal_cost
        (TL.build_three_leg_forest
          (build_complex_three_leg_routes (ctg_triads n)))
      <=
      ctg_scale_paid n
      + ctg_future_paid n
      + ctg_residual_paid n;

  ctg_scale_gk :
    GK.GKChannelCertificate ctg_scale_paid;

  ctg_future_gk :
    GK.GKChannelCertificate ctg_future_paid;

  ctg_residual_gk :
    GK.GKChannelCertificate ctg_residual_paid
}.

Definition build_three_leg_gk_from_complex
  (C : ComplexTriadGKSequenceCertificate)
  : TL.ThreeLegGKSequenceCertificate.
Proof.
  refine {|
    TL.tlg_action := ctg_action C;
    TL.tlg_physical_routes :=
      fun n => build_complex_three_leg_routes (ctg_triads C n);

    TL.tlg_scale_paid := ctg_scale_paid C;
    TL.tlg_future_paid := ctg_future_paid C;
    TL.tlg_residual_paid := ctg_residual_paid C;

    TL.tlg_action_nonnegative := ctg_action_nonnegative C;
    TL.tlg_next_owned := ctg_next_owned C;
    TL.tlg_parent_paid := ctg_parent_paid C;
    TL.tlg_legal_cost_split := ctg_legal_cost_split C;

    TL.tlg_scale_gk := ctg_scale_gk C;
    TL.tlg_future_gk := ctg_future_gk C;
    TL.tlg_residual_gk := ctg_residual_gk C
  |}.
Defined.

Theorem CTL30_COMPLEX_GK_BUILDS_THREE_LEG_GK :
  forall C : ComplexTriadGKSequenceCertificate,
    exists G : TL.ThreeLegGKSequenceCertificate,
      forall n : nat,
        TL.tlg_action G n = ctg_action C n.
Proof.
  intro C.
  exists (build_three_leg_gk_from_complex C).
  intro n.
  reflexivity.
Qed.

Theorem CTL31_ACTUAL_COMPLEX_THREE_LEG_GK_IMPLIES_DISCRETE_M7 :
  forall C : ComplexTriadGKSequenceCertificate,
    MR.ActualDiscreteGPM7 (ctg_action C).
Proof.
  intro C.
  exact
    (TL.TL31_THREE_LEG_GK_IMPLIES_DISCRETE_M7
      (build_three_leg_gk_from_complex C)).
Qed.

Theorem CTL32_ACTUAL_COMPLEX_THREE_LEG_GK_IMPLIES_OLD_FINITE_MEMORY_M7 :
  forall C : ComplexTriadGKSequenceCertificate,
    MR.RR.finite_memory_gpm7 (ctg_action C).
Proof.
  intro C.
  exact
    (TL.TL32_THREE_LEG_GK_IMPLIES_OLD_FINITE_MEMORY_M7
      (build_three_leg_gk_from_complex C)).
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_COMPLEX_THREE_LEG_REALIZATION.

Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.singleton_source_class.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.CTL02_THREE_SIGNED_SOURCE_GROUP_ENVELOPE.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.three_source_parent_class.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.ComplexThreeLegPhysicalCertificate.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.CTL10_ACTUAL_COMPLEX_SOURCE_SPLIT.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.CTL11_PARENT_CLASS_IS_ACTUAL_DAMPED_TRIAD_SOURCE.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.CTL16_OUTGOING_CAPACITY_BOUNDED_BY_THREE_SOURCE_BUDGETS.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.build_complex_three_leg_physical_route.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.CTL20_COMPLEX_TRIAD_CONSTRUCTS_PARENT_ROUTE.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.CTL21_COMPLEX_ROUTE_REPRODUCTION.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.CTL22_COMPLEX_ROUTE_COST_IS_EXPLICIT_DEFICIT.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.ComplexTriadGKSequenceCertificate.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.build_three_leg_gk_from_complex.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.CTL31_ACTUAL_COMPLEX_THREE_LEG_GK_IMPLIES_DISCRETE_M7.
Check NSE_GP_COMPLEX_THREE_LEG_REALIZATION.CTL32_ACTUAL_COMPLEX_THREE_LEG_GK_IMPLIES_OLD_FINITE_MEMORY_M7.
