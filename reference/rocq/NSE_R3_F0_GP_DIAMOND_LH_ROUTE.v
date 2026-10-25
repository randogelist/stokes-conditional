From Stdlib Require Import Reals Lra Psatz String Lists.List.
Require Import NSE_R3_F0_GP_DIAMOND_ROUTE.
Require Import awpi_nse_gp_source_class_ownership_v0_25_4.
Require Import awpi_nse_gp_parent_degree_reproduction_v0_26_0.
Require Import awpi_nse_gp_three_leg_route_realization_v0_36_4.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_gp_ae_modal_semantics_v0_23_1.
Require Import awpi_nse_gp_complex_three_leg_realization_v0_37_4.
Require Import awpi_nse_gp_complex_source_envelope_realization_v0_38_0.
Require Import awpi_nse_leray_ae_to_parent_route_v0_39_0.
Require Import awpi_nse_leray_projected_modes_v0_40_0.
Require Import awpi_nse_leray_dual_evolution_v0_41_5.
Require Import awpi_nse_leray_weak_test_specialization_v0_42_1.

Open Scope R_scope.

Module NSE_R3_F0_GP_DIAMOND_LH_ROUTE.

Module DR := NSE_R3_F0_GP_DIAMOND_ROUTE.
Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module AE := NSE_GP_AE_MODAL_SEMANTICS.
Module CTL := NSE_GP_COMPLEX_THREE_LEG_REALIZATION.
Module TL := NSE_GP_THREE_LEG_ROUTE_REALIZATION.
Module PR := NSE_GP_PARENT_DEGREE_REPRODUCTION.
Module SO := NSE_GP_SOURCE_CLASS_OWNERSHIP.
Module L39 := NSE_LERAY_AE_TO_PARENT_ROUTE.
Module L40 := NSE_LERAY_PROJECTED_MODES.
Module L41 := NSE_LERAY_DUAL_EVOLUTION.
Module L42 := NSE_LERAY_WEAK_TEST_SPECIALIZATION.

(* ====================================================================== *)
(* 0. The universal weak NSE operator already gives the three scalar       *)
(*    distributional mode equations.  No route/M7 premise is used here.   *)
(* ====================================================================== *)

Theorem DIAMOND_LH00_WEAK_NSE_GIVES_TRIAD_DISTRIBUTIONAL_EQUATIONS :
  forall W : L42.WeakTestCalculus,
  forall nu lk lp lq : R,
  forall H : L42.LerayHopfWeakMomentum W nu,
  forall T : L42.HelicalWeakTriad W lk lp lq,
    L42.TriadDistributionalEquations W nu lk lp lq T.
Proof.
  exact L42.LH42_10_STANDARD_LH_WEAK_MOMENTUM_GIVES_TRIAD_DISTRIBUTIONAL_EQUATIONS.
Qed.

(* ====================================================================== *)
(* 1. Canonical local route built from the actual a.e. LH dual evolution.  *)
(*    The route is not postulated: it is the composition                   *)
(*      dual evolution -> projected triad -> AE triad -> physical triad    *)
(*      -> ThreeLegPhysicalRoute.                                          *)
(* ====================================================================== *)

Section DUAL_TO_THREE_LEG.

Context {CoNull : (R -> Prop) -> Prop}.
Variable HC : AE.CoNullCalculus CoNull.
Context {O : L41.DualEvolutionOps}.
Context {C : CH.C2}.
Context {nu lk lp lq : R}.
Variable T : L41.LerayHopfDualEvolutionTriad CoNull O C nu lk lp lq.

Definition dual_projected_triad :
  L40.LerayHopfProjectedTriad CoNull C nu lk lp lq :=
  L41.build_projected_triad_from_dual T.

Definition dual_ae_triad :
  AE.AETriadSemanticData CoNull C nu lk lp lq :=
  L40.build_ae_triad_from_projected HC dual_projected_triad.

Definition dual_good_time (t : R) : Prop :=
  AE.triad_good_time CoNull C nu lk lp lq dual_ae_triad t.

Definition dual_three_leg_route
  (t : R) (Hgood : dual_good_time t)
  : TL.ThreeLegPhysicalRoute :=
  L39.three_leg_route_at_good_time
    CoNull C nu lk lp lq dual_ae_triad t Hgood.

Definition dual_damped_source (t : R) : R :=
  L39.leray_damped_triad_source
    CoNull C nu lk lp lq dual_ae_triad t.

Theorem DIAMOND_LH10_DUAL_GOOD_TIME_ROUTE_SOURCE_IS_ACTUAL_NSE_SOURCE :
  forall (t : R) (Hgood : dual_good_time t),
    SO.class_signed_work
      (TL.tl_source_class (dual_three_leg_route t Hgood))
    = dual_damped_source t.
Proof.
  intros t Hgood.
  unfold dual_three_leg_route, dual_damped_source.
  change
    (SO.class_signed_work
      (CTL.ctl_parent_class
        (L39.physical_certificate_at_good_time
          CoNull C nu lk lp lq dual_ae_triad t Hgood))
     =
     L39.leray_damped_triad_source
       CoNull C nu lk lp lq dual_ae_triad t).
  exact
    (L39.LH39_01_GOOD_TIME_PARENT_CLASS_IS_ACTUAL_LH_SOURCE
      CoNull C nu lk lp lq dual_ae_triad t Hgood).
Qed.

Theorem DIAMOND_LH11_DUAL_GOOD_TIME_ROUTE_HAS_EXACT_THREE_CHILDREN :
  forall (t : R) (Hgood : dual_good_time t),
    TL.three_leg_children (dual_three_leg_route t Hgood)
    =
    TL.tl_child_k (dual_three_leg_route t Hgood) ::
    TL.tl_child_p (dual_three_leg_route t Hgood) ::
    TL.tl_child_q (dual_three_leg_route t Hgood) :: nil.
Proof.
  intros.
  reflexivity.
Qed.

Theorem DIAMOND_LH12_DUAL_GOOD_TIME_ROUTE_REPRODUCTION :
  forall (t : R) (Hgood : dual_good_time t),
    4 *
      PR.route_child_action
        (TL.build_three_leg_parent_route
          (dual_three_leg_route t Hgood))
    <=
      PR.pr_parent_action 3
        (TL.build_three_leg_parent_route
          (dual_three_leg_route t Hgood))
      +
      PR.pr_legal_cost 3
        (TL.build_three_leg_parent_route
          (dual_three_leg_route t Hgood)).
Proof.
  intros.
  exact (TL.TL24_CANONICAL_ROUTE_REPRODUCTION (dual_three_leg_route t Hgood)).
Qed.

Definition ActualLHDualThreeLegRouteAt (t : R) : Prop :=
  exists Hgood : dual_good_time t,
    exists Rte : TL.ThreeLegPhysicalRoute,
      Rte = dual_three_leg_route t Hgood /\
      SO.class_signed_work (TL.tl_source_class Rte)
        = dual_damped_source t /\
      4 * PR.route_child_action (TL.build_three_leg_parent_route Rte)
      <=
      PR.pr_parent_action 3 (TL.build_three_leg_parent_route Rte)
      + PR.pr_legal_cost 3 (TL.build_three_leg_parent_route Rte).

Theorem DIAMOND_LH20_EVERY_DUAL_GOOD_TIME_IS_ACTUAL_THREE_LEG_ROUTE :
  forall t : R,
    dual_good_time t ->
    ActualLHDualThreeLegRouteAt t.
Proof.
  intros t Hgood.
  exists Hgood.
  exists (dual_three_leg_route t Hgood).
  split.
  - reflexivity.
  - split.
    + exact (DIAMOND_LH10_DUAL_GOOD_TIME_ROUTE_SOURCE_IS_ACTUAL_NSE_SOURCE t Hgood).
    + exact (DIAMOND_LH12_DUAL_GOOD_TIME_ROUTE_REPRODUCTION t Hgood).
Qed.

Theorem DIAMOND_LH21_ACTUAL_DUAL_THREE_LEG_ROUTE_HOLDS_CONULL :
  CoNull ActualLHDualThreeLegRouteAt.
Proof.
  unfold dual_good_time.
  pose proof
    (AE.GPAE20_TRIAD_GOOD_TIME_IS_CONULL
      CoNull HC C nu lk lp lq dual_ae_triad) as Hgood.
  eapply (AE.cn_mono CoNull HC).
  - exact Hgood.
  - intros t Ht.
    exact (DIAMOND_LH20_EVERY_DUAL_GOOD_TIME_IS_ACTUAL_THREE_LEG_ROUTE t Ht).
Qed.

End DUAL_TO_THREE_LEG.

(* ====================================================================== *)
(* 2. Local arbitrary-route realization has therefore disappeared.         *)
(*    What remains globally is only:                                       *)
(*      - assemble these canonical co-null LH routes across generations;   *)
(*      - prove next-generation ownership / GK payment channels;           *)
(*      - couple finite route depth to the critical-time action cost.       *)
(* ====================================================================== *)

Definition GLOBAL_LH_ROUTE_ASSEMBLY_FRONTIER : Prop := True.
Definition SCALAR_DISTRIBUTIONAL_TO_AE_DUAL_FRONTIER : Prop := True.
Definition CRITICAL_TIME_ROUTE_DEPTH_FRONTIER : Prop := True.

Definition STATUS : string :=
  "NSE_R3_F0_GP_DIAMOND_LH_ROUTE_V0_3_2_NO_ADMITTED_LOCAL_LH_ROUTE_DERIVED"%string.

End NSE_R3_F0_GP_DIAMOND_LH_ROUTE.

Check NSE_R3_F0_GP_DIAMOND_LH_ROUTE.DIAMOND_LH00_WEAK_NSE_GIVES_TRIAD_DISTRIBUTIONAL_EQUATIONS.
Check NSE_R3_F0_GP_DIAMOND_LH_ROUTE.DIAMOND_LH10_DUAL_GOOD_TIME_ROUTE_SOURCE_IS_ACTUAL_NSE_SOURCE.
Check NSE_R3_F0_GP_DIAMOND_LH_ROUTE.DIAMOND_LH12_DUAL_GOOD_TIME_ROUTE_REPRODUCTION.
Check NSE_R3_F0_GP_DIAMOND_LH_ROUTE.DIAMOND_LH21_ACTUAL_DUAL_THREE_LEG_ROUTE_HOLDS_CONULL.

Print Assumptions NSE_R3_F0_GP_DIAMOND_LH_ROUTE.DIAMOND_LH00_WEAK_NSE_GIVES_TRIAD_DISTRIBUTIONAL_EQUATIONS.
Print Assumptions NSE_R3_F0_GP_DIAMOND_LH_ROUTE.DIAMOND_LH10_DUAL_GOOD_TIME_ROUTE_SOURCE_IS_ACTUAL_NSE_SOURCE.
Print Assumptions NSE_R3_F0_GP_DIAMOND_LH_ROUTE.DIAMOND_LH21_ACTUAL_DUAL_THREE_LEG_ROUTE_HOLDS_CONULL.
