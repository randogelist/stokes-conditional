
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_perspective_action_v0_11_2.
Require Import awpi_nse_gp_closed_action_envelope_v0_19_2.
Require Import awpi_nse_gp_leray_modal_triad_adapter_v0_13_3.
Require Import awpi_nse_gp_source_class_ownership_v0_25_4.
Require Import awpi_nse_gp_parent_degree_reproduction_v0_26_0.
Require Import awpi_nse_gp_to_m7_route_v0_28_3.
Require Import awpi_nse_gp_gk_cohomology_realization_v0_35_3.

Import ListNotations.
Open Scope R_scope.

Module NSE_GP_THREE_LEG_ROUTE_REALIZATION.

Module PA := NSE_GP_PERSPECTIVE_ACTION.
Module CE := NSE_GP_CLOSED_ACTION_ENVELOPE.
Module LM := NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.
Module SO := NSE_GP_SOURCE_CLASS_OWNERSHIP.
Module PR := NSE_GP_PARENT_DEGREE_REPRODUCTION.
Module MR := NSE_GP_TO_M7_ROUTE.
Module GK := NSE_GP_GK_COHOMOLOGY_REALIZATION.

(* ===================================================================== *)
(* Canonical exact action of a grouped physical source class              *)
(* ===================================================================== *)

Definition canonical_parent_action
  (P : SO.PhysicalSourceClass) : R :=
  (SO.class_positive_work P * SO.class_positive_work P)
    / SO.psc_capacity P.

Theorem TL00_CANONICAL_PARENT_ACTION_REL :
  forall P : SO.PhysicalSourceClass,
    PA.ActionRel
      (SO.class_positive_work P)
      (SO.psc_capacity P)
      (canonical_parent_action P).
Proof.
  intro P.
  destruct (Req_dec (SO.psc_capacity P) 0) as [Hz | Hnz].
  - pose proof
      (CE.GPCE01_ZERO_CAPACITY_FORCES_ZERO_WORK
        (SO.class_positive_work P)
        (SO.psc_budget P)) as Hzero.
    assert
      (Henv :
        CE.ActionEnvelope
          (SO.class_positive_work P)
          0
          (SO.psc_budget P)).
    {
      rewrite <- Hz.
      exact (SO.GPSO11_CLASS_ACTION_IS_GROUP_FIRST P).
    }
    specialize (Hzero Henv).
    unfold canonical_parent_action.
    unfold PA.ActionRel.
    rewrite Hz.
    rewrite Hzero.
    unfold Rdiv.
    ring.
  - assert (Hdpos : 0 < SO.psc_capacity P).
    {
      pose proof (SO.psc_capacity_nonnegative P).
      lra.
    }
    unfold canonical_parent_action.
    unfold PA.ActionRel.
    unfold Rdiv.
    replace
      (SO.psc_capacity P *
        ((SO.class_positive_work P * SO.class_positive_work P)
          * / SO.psc_capacity P))
      with
      ((SO.class_positive_work P * SO.class_positive_work P)
        * (SO.psc_capacity P * / SO.psc_capacity P))
      by ring.
    rewrite Rinv_r.
    + ring.
    + exact Hnz.
Qed.

Theorem TL01_CANONICAL_PARENT_ACTION_NONNEG :
  forall P : SO.PhysicalSourceClass,
    0 <= canonical_parent_action P.
Proof.
  intro P.
  destruct (Req_dec (SO.psc_capacity P) 0) as [Hz | Hnz].
  - pose proof
      (CE.GPCE01_ZERO_CAPACITY_FORCES_ZERO_WORK
        (SO.class_positive_work P)
        (SO.psc_budget P)) as Hzero.
    assert
      (Henv :
        CE.ActionEnvelope
          (SO.class_positive_work P)
          0
          (SO.psc_budget P)).
    {
      rewrite <- Hz.
      exact (SO.GPSO11_CLASS_ACTION_IS_GROUP_FIRST P).
    }
    specialize (Hzero Henv).
    unfold canonical_parent_action.
    rewrite Hz.
    rewrite Hzero.
    unfold Rdiv.
    nra.
  - assert (Hdpos : 0 < SO.psc_capacity P).
    {
      pose proof (SO.psc_capacity_nonnegative P).
      lra.
    }
    unfold canonical_parent_action.
    unfold Rdiv.
    apply Rmult_le_pos.
    + pose proof (Rle_0_sqr (SO.class_positive_work P)) as Hsq.
      unfold Rsqr in Hsq.
      exact Hsq.
    + left.
      apply Rinv_0_lt_compat.
      exact Hdpos.
Qed.

Theorem TL02_CANONICAL_PARENT_ACTION_BUDGET :
  forall P : SO.PhysicalSourceClass,
    canonical_parent_action P <= SO.psc_budget P.
Proof.
  intro P.
  destruct (Req_dec (SO.psc_capacity P) 0) as [Hz | Hnz].
  - pose proof
      (CE.GPCE01_ZERO_CAPACITY_FORCES_ZERO_WORK
        (SO.class_positive_work P)
        (SO.psc_budget P)) as Hzero.
    assert
      (Henv :
        CE.ActionEnvelope
          (SO.class_positive_work P)
          0
          (SO.psc_budget P)).
    {
      rewrite <- Hz.
      exact (SO.GPSO11_CLASS_ACTION_IS_GROUP_FIRST P).
    }
    specialize (Hzero Henv).
    unfold canonical_parent_action.
    rewrite Hz.
    rewrite Hzero.
    unfold Rdiv.
    pose proof (SO.psc_budget_nonnegative P).
    nra.
  - assert (Hdpos : 0 < SO.psc_capacity P).
    {
      pose proof (SO.psc_capacity_nonnegative P).
      lra.
    }
    pose proof (TL00_CANONICAL_PARENT_ACTION_REL P) as Hrel.
    pose proof (SO.GPSO12_CLASS_POLYNOMIAL_BOUND P) as Hpoly.
    unfold PA.ActionRel in Hrel.
    nra.
Qed.

(* ===================================================================== *)
(* Canonical exact positive reproduction deficit                         *)
(* ===================================================================== *)

Definition reproduction_deficit (A B : R) : R :=
  LM.pos (12 * B - A).

Theorem TL10_REPRODUCTION_DEFICIT_NONNEG :
  forall A B : R,
    0 <= reproduction_deficit A B.
Proof.
  intros A B.
  unfold reproduction_deficit.
  apply LM.GPLM00_POS_NONNEG.
Qed.

Theorem TL11_REPRODUCTION_DEFICIT_COVERS :
  forall A B : R,
    12 * B <= A + reproduction_deficit A B.
Proof.
  intros A B.
  unfold reproduction_deficit.
  pose proof (LM.GPLM01_POS_DOMINATES (12 * B - A)) as H.
  lra.
Qed.

Theorem TL12_REPRODUCTION_DEFICIT_ZERO_IF_ALREADY_PAID :
  forall A B : R,
    12 * B <= A ->
    reproduction_deficit A B = 0.
Proof.
  intros A B H.
  unfold reproduction_deficit, LM.pos.
  destruct (Rle_dec 0 (12 * B - A)) as [Hp | Hn].
  - assert (Heq : 12 * B - A = 0) by lra.
    rewrite Heq.
    rewrite Rabs_R0.
    lra.
  - assert (Hlt : 12 * B - A < 0) by lra.
    rewrite (Rabs_left (12 * B - A) Hlt).
    ring_simplify.
    lra.
Qed.

Theorem TL13_REPRODUCTION_DEFICIT_EXACT_IF_UNPAID :
  forall A B : R,
    A < 12 * B ->
    reproduction_deficit A B = 12 * B - A.
Proof.
  intros A B H.
  unfold reproduction_deficit, LM.pos.
  assert (Hpos : 0 <= 12 * B - A) by lra.
  rewrite (Rabs_pos_eq (12 * B - A) Hpos).
  ring_simplify.
  lra.
Qed.

(* ===================================================================== *)
(* Physical triad/source leg data: exactly three outgoing children        *)
(* ===================================================================== *)

Record ThreeLegPhysicalRoute : Type := {
  tl_source_class : SO.PhysicalSourceClass;

  tl_outgoing_capacity : R;
  tl_outgoing_capacity_nonnegative :
    0 <= tl_outgoing_capacity;

  tl_child_k : R;
  tl_child_p : R;
  tl_child_q : R;

  tl_child_k_nonnegative : 0 <= tl_child_k;
  tl_child_p_nonnegative : 0 <= tl_child_p;
  tl_child_q_nonnegative : 0 <= tl_child_q;

  tl_child_k_bounded : tl_child_k <= tl_outgoing_capacity;
  tl_child_p_bounded : tl_child_p <= tl_outgoing_capacity;
  tl_child_q_bounded : tl_child_q <= tl_outgoing_capacity
}.

Definition three_leg_children
  (T : ThreeLegPhysicalRoute) : list R :=
  [tl_child_k T; tl_child_p T; tl_child_q T].

Definition three_leg_legal_cost
  (T : ThreeLegPhysicalRoute) : R :=
  reproduction_deficit
    (canonical_parent_action (tl_source_class T))
    (tl_outgoing_capacity T).

Theorem TL20_THREE_LEG_CHILDREN_NONNEG :
  forall T : ThreeLegPhysicalRoute,
    PR.AllNonnegative (three_leg_children T).
Proof.
  intro T.
  unfold three_leg_children.
  simpl.
  repeat split.
  - exact (tl_child_k_nonnegative T).
  - exact (tl_child_p_nonnegative T).
  - exact (tl_child_q_nonnegative T).
Qed.

Theorem TL21_THREE_LEG_CHILDREN_BOUNDED :
  forall T : ThreeLegPhysicalRoute,
    PR.AllLe
      (tl_outgoing_capacity T)
      (three_leg_children T).
Proof.
  intro T.
  unfold three_leg_children.
  simpl.
  repeat split.
  - exact (tl_child_k_bounded T).
  - exact (tl_child_p_bounded T).
  - exact (tl_child_q_bounded T).
Qed.

Theorem TL22_THREE_LEG_DEGREE_IS_THREE :
  forall T : ThreeLegPhysicalRoute,
    (length (three_leg_children T) <= 3)%nat.
Proof.
  intro T.
  unfold three_leg_children.
  simpl.
  auto.
Qed.

Theorem TL23_THREE_LEG_LEGAL_COST_NONNEG :
  forall T : ThreeLegPhysicalRoute,
    0 <= three_leg_legal_cost T.
Proof.
  intro T.
  unfold three_leg_legal_cost.
  apply TL10_REPRODUCTION_DEFICIT_NONNEG.
Qed.

(* The ParentRoute reproduction field is now a theorem, not input data. *)
Definition build_three_leg_parent_route
  (T : ThreeLegPhysicalRoute)
  : PR.ParentRoute 3.
Proof.
  refine {|
    PR.pr_source_class := tl_source_class T;

    PR.pr_parent_action :=
      canonical_parent_action (tl_source_class T);

    PR.pr_parent_action_nonnegative :=
      TL01_CANONICAL_PARENT_ACTION_NONNEG (tl_source_class T);

    PR.pr_parent_action_rel :=
      TL00_CANONICAL_PARENT_ACTION_REL (tl_source_class T);

    PR.pr_parent_action_budget :=
      TL02_CANONICAL_PARENT_ACTION_BUDGET (tl_source_class T);

    PR.pr_outgoing_capacity := tl_outgoing_capacity T;

    PR.pr_outgoing_capacity_nonnegative :=
      tl_outgoing_capacity_nonnegative T;

    PR.pr_child_actions := three_leg_children T;

    PR.pr_child_actions_nonnegative :=
      TL20_THREE_LEG_CHILDREN_NONNEG T;

    PR.pr_each_child_bounded :=
      TL21_THREE_LEG_CHILDREN_BOUNDED T;

    PR.pr_degree_bound :=
      TL22_THREE_LEG_DEGREE_IS_THREE T;

    PR.pr_legal_cost := three_leg_legal_cost T;

    PR.pr_legal_cost_nonnegative :=
      TL23_THREE_LEG_LEGAL_COST_NONNEG T
  |}.
  simpl.
  unfold three_leg_legal_cost.
  pose proof
    (TL11_REPRODUCTION_DEFICIT_COVERS
      (canonical_parent_action (tl_source_class T))
      (tl_outgoing_capacity T)) as H.
  nra.
Defined.

Theorem TL24_CANONICAL_ROUTE_REPRODUCTION :
  forall T : ThreeLegPhysicalRoute,
    4 * PR.route_child_action (build_three_leg_parent_route T)
    <=
    PR.pr_parent_action 3 (build_three_leg_parent_route T)
    +
    PR.pr_legal_cost 3 (build_three_leg_parent_route T).
Proof.
  intro T.
  exact
    (PR.GPPR22_ROUTE_REPRODUCTION_PAYS_ALL_CHILDREN
      3
      (build_three_leg_parent_route T)).
Qed.

Theorem TL25_CANONICAL_ROUTE_COST_IS_EXACT_DEFICIT :
  forall T : ThreeLegPhysicalRoute,
    PR.pr_legal_cost 3 (build_three_leg_parent_route T)
    =
    reproduction_deficit
      (canonical_parent_action (tl_source_class T))
      (tl_outgoing_capacity T).
Proof.
  intro T.
  reflexivity.
Qed.

Definition build_three_leg_forest
  (Ts : list ThreeLegPhysicalRoute)
  : list (PR.ParentRoute 3) :=
  map build_three_leg_parent_route Ts.

(* ===================================================================== *)
(* Sequence-level realization: arbitrary ParentRoute forests disappear    *)
(* ===================================================================== *)

Record ThreeLegGKSequenceCertificate : Type := {
  tlg_action : nat -> R;
  tlg_physical_routes : nat -> list ThreeLegPhysicalRoute;

  tlg_scale_paid : nat -> R;
  tlg_future_paid : nat -> R;
  tlg_residual_paid : nat -> R;

  tlg_action_nonnegative :
    forall n : nat, 0 <= tlg_action n;

  tlg_next_owned :
    forall n : nat,
      tlg_action (S n)
      <=
      PR.forest_child_action
        (build_three_leg_forest (tlg_physical_routes n));

  tlg_parent_paid :
    forall n : nat,
      PR.forest_parent_action
        (build_three_leg_forest (tlg_physical_routes n))
      <= tlg_action n;

  tlg_legal_cost_split :
    forall n : nat,
      PR.forest_legal_cost
        (build_three_leg_forest (tlg_physical_routes n))
      <=
      tlg_scale_paid n
      + tlg_future_paid n
      + tlg_residual_paid n;

  tlg_scale_gk :
    GK.GKChannelCertificate tlg_scale_paid;

  tlg_future_gk :
    GK.GKChannelCertificate tlg_future_paid;

  tlg_residual_gk :
    GK.GKChannelCertificate tlg_residual_paid
}.

Definition build_gk_route_from_three_leg
  (C : ThreeLegGKSequenceCertificate)
  : GK.GPRouteGKCertificate 3.
Proof.
  refine {|
    GK.gkg_action := tlg_action C;
    GK.gkg_routes :=
      fun n => build_three_leg_forest (tlg_physical_routes C n);

    GK.gkg_scale_paid := tlg_scale_paid C;
    GK.gkg_future_paid := tlg_future_paid C;
    GK.gkg_residual_paid := tlg_residual_paid C;

    GK.gkg_action_nonnegative := tlg_action_nonnegative C;
    GK.gkg_next_owned := tlg_next_owned C;
    GK.gkg_parent_paid := tlg_parent_paid C;
    GK.gkg_legal_cost_split := tlg_legal_cost_split C;

    GK.gkg_scale_gk := tlg_scale_gk C;
    GK.gkg_future_gk := tlg_future_gk C;
    GK.gkg_residual_gk := tlg_residual_gk C
  |}.
Defined.

Theorem TL30_THREE_LEG_GK_BUILDS_ROUTE_GK :
  forall C : ThreeLegGKSequenceCertificate,
    exists G : GK.GPRouteGKCertificate 3,
      forall n : nat,
        GK.gkg_action 3 G n = tlg_action C n.
Proof.
  intro C.
  exists (build_gk_route_from_three_leg C).
  intro n.
  reflexivity.
Qed.

Theorem TL31_THREE_LEG_GK_IMPLIES_DISCRETE_M7 :
  forall C : ThreeLegGKSequenceCertificate,
    MR.ActualDiscreteGPM7 (tlg_action C).
Proof.
  intro C.
  exact
    (GK.GKGK30_GK_REALIZATION_IMPLIES_DISCRETE_M7
      3
      (build_gk_route_from_three_leg C)).
Qed.

Theorem TL32_THREE_LEG_GK_IMPLIES_OLD_FINITE_MEMORY_M7 :
  forall C : ThreeLegGKSequenceCertificate,
    MR.RR.finite_memory_gpm7 (tlg_action C).
Proof.
  intro C.
  exact
    (GK.GKGK31_GK_REALIZATION_IMPLIES_OLD_FINITE_MEMORY_M7
      3
      (build_gk_route_from_three_leg C)).
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_THREE_LEG_ROUTE_REALIZATION.

Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.canonical_parent_action.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.TL00_CANONICAL_PARENT_ACTION_REL.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.TL01_CANONICAL_PARENT_ACTION_NONNEG.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.TL02_CANONICAL_PARENT_ACTION_BUDGET.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.reproduction_deficit.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.TL10_REPRODUCTION_DEFICIT_NONNEG.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.TL11_REPRODUCTION_DEFICIT_COVERS.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.ThreeLegPhysicalRoute.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.build_three_leg_parent_route.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.TL24_CANONICAL_ROUTE_REPRODUCTION.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.ThreeLegGKSequenceCertificate.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.build_gk_route_from_three_leg.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.TL31_THREE_LEG_GK_IMPLIES_DISCRETE_M7.
Check NSE_GP_THREE_LEG_ROUTE_REALIZATION.TL32_THREE_LEG_GK_IMPLIES_OLD_FINITE_MEMORY_M7.
