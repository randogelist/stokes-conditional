From Stdlib Require Import Reals Lra Psatz String.
Require Import NSE_R3_F0_GP_DIAMOND.
Require Import awpi_nse_gp_three_leg_route_realization_v0_36_4.
Require Import awpi_nse_gp_to_m7_route_v0_28_3.
Require Import awpi_nse_gp_renewal_reduction_v0_3_1.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.
Require Import awpi_nse_gp_restart_action_covariance_v0_14_2.

Module NSE_R3_F0_GP_DIAMOND_ROUTE.

Open Scope R_scope.

Module TL := NSE_GP_THREE_LEG_ROUTE_REALIZATION.
Module MR := NSE_GP_TO_M7_ROUTE.
Module RR := NSE_GP_RENEWAL_REDUCTION.
Module Spine := NSE_GP_TO_M7_SPINE.
Module Energy := NSE_M7_CRITICAL_ENERGY_INJECTION.
Module Cov := NSE_GP_RESTART_ACTION_COVARIANCE.

Definition R3 : Type := (R * (R * R))%type.
Definition R3Velocity : Type := R3 -> R3.
Definition R3Trajectory : Type := R -> R3Velocity.

(* ======================================================================== *)
(* 1. A physical three-leg GK route certificate already contains all local   *)
(*    renewal and all three global payment-prefix budgets.  Therefore the    *)
(*    Diamond no longer needs 509/605 renewal and paid budget as separate    *)
(*    realization fields.                                                    *)
(* ======================================================================== *)

Section ROUTE_TO_SPINE.

Context {GPState : Type}.
Variable mass : GPState -> nat -> R.

Definition ThreeLegRouteRealizes (U : GPState) : Prop :=
  exists C : TL.ThreeLegGKSequenceCertificate,
    forall n : nat,
      TL.tlg_action C n = mass U n.

Lemma DIAMOND_ROUTE01_PREFIX_IDENTIFICATION :
  forall (U : GPState) (C : TL.ThreeLegGKSequenceCertificate),
    (forall n : nat, TL.tlg_action C n = mass U n) ->
    forall N : nat,
      RR.prefix_sum (TL.tlg_action C) N =
      Spine.resistant_prefix (mass U) N.
Proof.
  intros U C Hmatch N.
  induction N as [|N IHN].
  - reflexivity.
  - simpl.
    rewrite IHN.
    rewrite (Hmatch N).
    reflexivity.
Qed.

Theorem DIAMOND_ROUTE10_THREE_LEG_GK_GIVES_SPINE_M7 :
  forall U : GPState,
    ThreeLegRouteRealizes U ->
    Spine.GPSequenceM7 (mass U).
Proof.
  intros U [C Hmatch].
  pose proof (TL.TL31_THREE_LEG_GK_IMPLIES_DISCRETE_M7 C) as Hdisc.
  unfold MR.ActualDiscreteGPM7, RR.uniform_prefix_budget in Hdisc.
  destruct Hdisc as [B [HB Hprefix]].
  exists B.
  split.
  - exact HB.
  - intro N.
    rewrite <- (DIAMOND_ROUTE01_PREFIX_IDENTIFICATION U C Hmatch N).
    exact (Hprefix N).
Qed.

End ROUTE_TO_SPINE.

(* ======================================================================== *)
(* 2. Physical action identity.  The GP/BKQR terminal mass is not a free      *)
(*    sequence: inverse transport + cut commutation make it exactly the       *)
(*    physical LH/NSE scalar action on each channel.                          *)
(* ======================================================================== *)

Section PHYSICAL_ACTION_MATCH.

Context {GPState Cut : Type}.

Variable gp_forward : R3Trajectory -> GPState.
Variable gp_back : GPState -> R3Trajectory.
Variable physical_cut : Cut -> R3Trajectory -> R3Trajectory.
Variable gp_cut_operator : Cut -> GPState -> GPState.

Hypothesis gp_left_inverse :
  forall u : R3Trajectory,
    gp_back (gp_forward u) = u.

Hypothesis gp_cut_commutes :
  forall (q : Cut) (u : R3Trajectory),
    gp_cut_operator q (gp_forward u) =
    gp_forward (physical_cut q u).

Variable LHForm : R3Trajectory -> R3Trajectory -> R.
Variable NSEForm :
  R3Trajectory -> R3Trajectory -> R3Trajectory -> R.
Variable channel : nat -> Cut.

Definition route_capacity (q : Cut) (U : GPState) : R :=
  LHForm (gp_back U) (gp_back (gp_cut_operator q U)).

Definition route_current (q : Cut) (U : GPState) : R :=
  NSEForm (gp_back U) (gp_back U) (gp_back (gp_cut_operator q U)).

Definition route_mass (U : GPState) (n : nat) : R :=
  Cov.action
    (route_current (channel n) U)
    (route_capacity (channel n) U).

Definition physical_capacity (q : Cut) (u : R3Trajectory) : R :=
  LHForm u (physical_cut q u).

Definition physical_current (q : Cut) (u : R3Trajectory) : R :=
  NSEForm u u (physical_cut q u).

Definition physical_mass (u : R3Trajectory) (n : nat) : R :=
  Cov.action
    (physical_current (channel n) u)
    (physical_capacity (channel n) u).

Theorem DIAMOND_ROUTE20_GP_MASS_IS_PHYSICAL_ACTION :
  forall (u : R3Trajectory) (n : nat),
    route_mass (gp_forward u) n = physical_mass u n.
Proof.
  intros u n.
  unfold route_mass, physical_mass,
    route_current, route_capacity,
    physical_current, physical_capacity.
  repeat rewrite (gp_left_inverse u).
  rewrite (gp_cut_commutes (channel n) u).
  repeat rewrite (gp_left_inverse (physical_cut (channel n) u)).
  reflexivity.
Qed.

Definition PhysicalThreeLegRouteRealizes
  (u : R3Trajectory) : Prop :=
  exists C : TL.ThreeLegGKSequenceCertificate,
    forall n : nat,
      TL.tlg_action C n = physical_mass u n.

Theorem DIAMOND_ROUTE21_PHYSICAL_THREE_LEG_ROUTE_GIVES_SPINE_M7 :
  forall u : R3Trajectory,
    PhysicalThreeLegRouteRealizes u ->
    Spine.GPSequenceM7 (route_mass (gp_forward u)).
Proof.
  intros u [C Hphysical].
  apply (@DIAMOND_ROUTE10_THREE_LEG_GK_GIVES_SPINE_M7
    GPState route_mass (gp_forward u)).
  exists C.
  intro n.
  rewrite (DIAMOND_ROUTE20_GP_MASS_IS_PHYSICAL_ACTION u n).
  exact (Hphysical n).
Qed.

End PHYSICAL_ACTION_MATCH.

(* ======================================================================== *)
(* 3. Time coupling.  Instead of a bare existential M7ActionCostRealization, *)
(*    expose an actual depth selector.  The checked M7 semantic interface is  *)
(*    then a theorem.                                                        *)
(* ======================================================================== *)

Section EXPLICIT_DEPTH_COUPLING.

Context {Time : Type}.
Variable mass : nat -> R.
Variable action_cost : Time -> R.
Variable depth : Time -> nat.

Definition ExplicitM7DepthCoupling : Prop :=
  forall t : Time,
    action_cost t <= Spine.resistant_prefix mass (depth t).

Theorem DIAMOND_ROUTE30_EXPLICIT_DEPTH_GIVES_ACTION_COST_REALIZATION :
  ExplicitM7DepthCoupling ->
  Energy.M7ActionCostRealization Time mass action_cost.
Proof.
  intros Hdepth t.
  exists (depth t).
  exact (Hdepth t).
Qed.

End EXPLICIT_DEPTH_COUPLING.

(* ======================================================================== *)
(* 4. Contracted R^3, f=0 terminal.                                           *)
(*                                                                            *)
(*    All recurrence/payment algebra is now BELOW the route certificate.       *)
(*    The remaining continuum interface says only:                             *)
(*      (i) actual GP/BKQR cells form the physical three-leg GK route;          *)
(*     (ii) an explicit finite M7 depth pays each physical-time action cost;    *)
(*    (iii) the same cost occurs in the critical energy balance.                *)
(* ======================================================================== *)

Section R3_F0_ROUTE_TERMINAL.

Context {GPState Cut Time : Type}.

Variable gp_forward : R3Trajectory -> GPState.
Variable gp_back : GPState -> R3Trajectory.
Variable physical_cut : Cut -> R3Trajectory -> R3Trajectory.
Variable gp_cut_operator : Cut -> GPState -> GPState.

Hypothesis gp_left_inverse :
  forall u : R3Trajectory,
    gp_back (gp_forward u) = u.

Hypothesis gp_cut_commutes :
  forall (q : Cut) (u : R3Trajectory),
    gp_cut_operator q (gp_forward u) =
    gp_forward (physical_cut q u).

Variable LerayHopfR3F0 : R3Trajectory -> Prop.
Variable NSER3F0 : R3Trajectory -> Prop.

Variable LHForm : R3Trajectory -> R3Trajectory -> R.
Variable NSEForm :
  R3Trajectory -> R3Trajectory -> R3Trajectory -> R.
Variable channel : nat -> Cut.

Definition terminal_capacity (q : Cut) (U : GPState) : R :=
  LHForm (gp_back U) (gp_back (gp_cut_operator q U)).

Definition terminal_current (q : Cut) (U : GPState) : R :=
  NSEForm (gp_back U) (gp_back U) (gp_back (gp_cut_operator q U)).

Definition terminal_mass (U : GPState) (n : nat) : R :=
  Cov.action
    (terminal_current (channel n) U)
    (terminal_capacity (channel n) U).

Definition terminal_physical_capacity
  (q : Cut) (u : R3Trajectory) : R :=
  LHForm u (physical_cut q u).

Definition terminal_physical_current
  (q : Cut) (u : R3Trajectory) : R :=
  NSEForm u u (physical_cut q u).

Definition terminal_physical_mass
  (u : R3Trajectory) (n : nat) : R :=
  Cov.action
    (terminal_physical_current (channel n) u)
    (terminal_physical_capacity (channel n) u).

Theorem DIAMOND_ROUTE40_TERMINAL_MASS_IS_PHYSICAL :
  forall (u : R3Trajectory) (n : nat),
    terminal_mass (gp_forward u) n = terminal_physical_mass u n.
Proof.
  intros u n.
  unfold terminal_mass, terminal_physical_mass,
    terminal_current, terminal_capacity,
    terminal_physical_current, terminal_physical_capacity.
  repeat rewrite (gp_left_inverse u).
  rewrite (gp_cut_commutes (channel n) u).
  repeat rewrite (gp_left_inverse (physical_cut (channel n) u)).
  reflexivity.
Qed.

Variable nu sigma initial_mass : R.
Variable critical_mass : GPState -> Time -> R.
Variable critical_dissipation : GPState -> Time -> R.
Variable action_cost : GPState -> Time -> R.
Variable depth : GPState -> Time -> nat.

Definition DiamondRouteCriticalRegular (U : GPState) : Prop :=
  Energy.CriticalH12Bound Time (critical_mass U) /\
  Energy.CriticalH32Dissipation Time (critical_dissipation U).

Record DiamondR3F0RouteCoupling (u : R3Trajectory) : Prop := {
  drc_route : TL.ThreeLegGKSequenceCertificate;

  drc_route_matches_physical_action :
    forall n : nat,
      TL.tlg_action drc_route n = terminal_physical_mass u n;

  drc_explicit_depth_payment :
    forall t : Time,
      action_cost (gp_forward u) t <=
      Spine.resistant_prefix
        (terminal_mass (gp_forward u))
        (depth (gp_forward u) t);

  drc_critical_balance :
    Energy.CriticalEnergyBalance
      Time nu sigma initial_mass
      (critical_mass (gp_forward u))
      (critical_dissipation (gp_forward u))
      (action_cost (gp_forward u))
}.

Definition UniversalDiamondR3F0RouteCoupling : Prop :=
  forall u : R3Trajectory,
    LerayHopfR3F0 u ->
    NSER3F0 u ->
    DiamondR3F0RouteCoupling u.

Theorem DIAMOND_ROUTE50_COUPLING_GIVES_SEQUENCE_M7 :
  forall u : R3Trajectory,
    DiamondR3F0RouteCoupling u ->
    Spine.GPSequenceM7 (terminal_mass (gp_forward u)).
Proof.
  intros u Hc.
  destruct Hc as [C Hmatch Hdepth Hbalance].
  apply (@DIAMOND_ROUTE10_THREE_LEG_GK_GIVES_SPINE_M7
    GPState terminal_mass (gp_forward u)).
  exists C.
  intro n.
  rewrite (DIAMOND_ROUTE40_TERMINAL_MASS_IS_PHYSICAL u n).
  exact (Hmatch n).
Qed.

Theorem DIAMOND_ROUTE51_COUPLING_GIVES_ACTION_COST_REALIZATION :
  forall u : R3Trajectory,
    DiamondR3F0RouteCoupling u ->
    Energy.M7ActionCostRealization
      Time
      (terminal_mass (gp_forward u))
      (action_cost (gp_forward u)).
Proof.
  intros u Hc.
  destruct Hc as [C Hmatch Hdepth Hbalance].
  apply (@DIAMOND_ROUTE30_EXPLICIT_DEPTH_GIVES_ACTION_COST_REALIZATION
    Time
    (terminal_mass (gp_forward u))
    (action_cost (gp_forward u))
    (depth (gp_forward u))).
  exact Hdepth.
Qed.

Theorem DIAMOND_ROUTE90_COUPLING_GIVES_CRITICAL_REGULARITY :
  forall u : R3Trajectory,
    DiamondR3F0RouteCoupling u ->
    DiamondRouteCriticalRegular (gp_forward u).
Proof.
  intros u Hc.
  assert (HM7 :
    Spine.GPSequenceM7 (terminal_mass (gp_forward u))).
  {
    exact (DIAMOND_ROUTE50_COUPLING_GIVES_SEQUENCE_M7 u Hc).
  }
  assert (Hcost :
    Energy.M7ActionCostRealization
      Time
      (terminal_mass (gp_forward u))
      (action_cost (gp_forward u))).
  {
    exact (DIAMOND_ROUTE51_COUPLING_GIVES_ACTION_COST_REALIZATION u Hc).
  }
  destruct Hc as [C Hmatch Hdepth Hbalance].
  unfold DiamondRouteCriticalRegular.
  exact
    (Energy.NSCE90_M7_INJECTS_INTO_CRITICAL_ENERGY_TARGET
      Time
      (terminal_mass (gp_forward u))
      nu sigma initial_mass
      (critical_mass (gp_forward u))
      (critical_dissipation (gp_forward u))
      (action_cost (gp_forward u))
      HM7 Hcost Hbalance).
Qed.

Theorem DIAMOND_ROUTE91_UNIVERSAL_R3_F0_CRITICAL_REGULARITY :
  UniversalDiamondR3F0RouteCoupling ->
  forall u : R3Trajectory,
    LerayHopfR3F0 u ->
    NSER3F0 u ->
    DiamondRouteCriticalRegular (gp_forward u).
Proof.
  intros Huniv u HLH HNSE.
  apply DIAMOND_ROUTE90_COUPLING_GIVES_CRITICAL_REGULARITY.
  exact (Huniv u HLH HNSE).
Qed.

Variable PhysicalRegular : R3Trajectory -> Prop.
Variable critical_to_physical_regular :
  forall u : R3Trajectory,
    DiamondRouteCriticalRegular (gp_forward u) ->
    PhysicalRegular u.

Theorem DIAMOND_ROUTE99_UNIVERSAL_R3_F0_PDE_REGULARITY :
  UniversalDiamondR3F0RouteCoupling ->
  forall u : R3Trajectory,
    LerayHopfR3F0 u ->
    NSER3F0 u ->
    PhysicalRegular u.
Proof.
  intros Huniv u HLH HNSE.
  apply critical_to_physical_regular.
  exact (DIAMOND_ROUTE91_UNIVERSAL_R3_F0_CRITICAL_REGULARITY
    Huniv u HLH HNSE).
Qed.

End R3_F0_ROUTE_TERMINAL.

Definition STATUS : string :=
  "NSE_R3_F0_GP_DIAMOND_ROUTE_V0_2_0_NO_ADMITTED_ROUTE_PAYMENT_DERIVED"%string.

End NSE_R3_F0_GP_DIAMOND_ROUTE.

Check NSE_R3_F0_GP_DIAMOND_ROUTE.DIAMOND_ROUTE10_THREE_LEG_GK_GIVES_SPINE_M7.
Check NSE_R3_F0_GP_DIAMOND_ROUTE.DIAMOND_ROUTE20_GP_MASS_IS_PHYSICAL_ACTION.
Check NSE_R3_F0_GP_DIAMOND_ROUTE.DIAMOND_ROUTE30_EXPLICIT_DEPTH_GIVES_ACTION_COST_REALIZATION.
Check NSE_R3_F0_GP_DIAMOND_ROUTE.DIAMOND_ROUTE40_TERMINAL_MASS_IS_PHYSICAL.
Check NSE_R3_F0_GP_DIAMOND_ROUTE.DIAMOND_ROUTE90_COUPLING_GIVES_CRITICAL_REGULARITY.
Check NSE_R3_F0_GP_DIAMOND_ROUTE.DIAMOND_ROUTE91_UNIVERSAL_R3_F0_CRITICAL_REGULARITY.
Check NSE_R3_F0_GP_DIAMOND_ROUTE.DIAMOND_ROUTE99_UNIVERSAL_R3_F0_PDE_REGULARITY.

Print Assumptions NSE_R3_F0_GP_DIAMOND_ROUTE.DIAMOND_ROUTE10_THREE_LEG_GK_GIVES_SPINE_M7.
Print Assumptions NSE_R3_F0_GP_DIAMOND_ROUTE.DIAMOND_ROUTE20_GP_MASS_IS_PHYSICAL_ACTION.
Print Assumptions NSE_R3_F0_GP_DIAMOND_ROUTE.DIAMOND_ROUTE90_COUPLING_GIVES_CRITICAL_REGULARITY.
