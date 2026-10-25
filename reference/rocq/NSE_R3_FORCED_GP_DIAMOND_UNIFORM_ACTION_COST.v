From Stdlib Require Import Reals Lra Psatz.
Require Import NSE_R3_FORCED_GP_DIAMOND_UNIFORM_CUTOFF_M7.
Require Import NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.
Require Import awpi_nse_gp_to_m7_route_v0_28_3.
Require Import awpi_nse_gp_renewal_reduction_v0_3_1.
Require Import awpi_nse_gp_gk_cohomology_realization_v0_35_3.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_R3_FORCED_GP_DIAMOND_UNIFORM_ACTION_COST.
Module UCM := NSE_R3_FORCED_GP_DIAMOND_UNIFORM_CUTOFF_M7.NSE_R3_FORCED_GP_DIAMOND_UNIFORM_CUTOFF_M7.
Module FC := NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.
Module MR := NSE_GP_TO_M7_ROUTE.
Module RR := NSE_GP_RENEWAL_REDUCTION.
Module GK := NSE_GP_GK_COHOMOLOGY_REALIZATION.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* 1. A common GK cost/drift envelope gives a cutoff-independent paid *)
(*    prefix budget.                                                   *)
(* ------------------------------------------------------------------ *)

Section UniformGKEnvelope.

Variable Cut : Type.
Variable paid : Cut -> nat -> R.
Variable cert : forall c : Cut, GK.GKChannelCertificate (paid c).

Record UniformGKCostDriftEnvelope (Bcost Bdrift : R) : Prop := {
  ugk_cost_nonneg : 0 <= Bcost;
  ugk_drift_nonneg : 0 <= Bdrift;
  ugk_cost_prefix :
    forall (c : Cut) (N : nat),
      RR.prefix_sum (GK.gkc_cost (paid c) (cert c)) N <= Bcost;
  ugk_initial_drift :
    forall c : Cut,
      GK.gkc_alpha (paid c) (cert c)
      * (GK.gkc_potential (paid c) (cert c) 0%nat
         - GK.gkc_lower (paid c) (cert c))
      <= Bdrift
}.

Theorem UAC00_UNIFORM_GK_ENVELOPE_GIVES_COMMON_PAID_PREFIX :
  forall Bcost Bdrift,
    UniformGKCostDriftEnvelope Bcost Bdrift ->
    forall (c : Cut) (N : nat),
      RR.prefix_sum (paid c) N <= Bcost + Bdrift.
Proof.
  intros Bcost Bdrift Henv c N.
  destruct Henv as [HBc HBd Hcost Hdrift].
  pose proof
    (GK.GKGK11_EXPLICIT_CHANNEL_BOUND
      (paid c) (cert c) Bcost HBc (Hcost c) N) as Hpaid.
  specialize (Hdrift c).
  lra.
Qed.

End UniformGKEnvelope.

(* ------------------------------------------------------------------ *)
(* 2. Common initial critical mass + initial route-action domination + *)
(*    common GK envelopes build the old UniformRouteBudget record.     *)
(* ------------------------------------------------------------------ *)

Section RouteBudgetFromGK.

Variable Cut : Type.
Variable dstar : Cut -> nat.
Variable route : forall c : Cut, MR.GPRouteCertificate (dstar c).

Variable initial_mass : Cut -> R.
Variable M0max : R.

Variable scale_gk :
  forall c : Cut,
    GK.GKChannelCertificate
      (MR.gpr_scale_paid (dstar c) (route c)).
Variable future_gk :
  forall c : Cut,
    GK.GKChannelCertificate
      (MR.gpr_future_paid (dstar c) (route c)).
Variable residual_gk :
  forall c : Cut,
    GK.GKChannelCertificate
      (MR.gpr_residual_paid (dstar c) (route c)).

Variable Bscost Bsdrift Bfcost Bfdrift Brcost Brdrift : R.

Hypothesis HM0 : 0 <= M0max.
Hypothesis Hinitial_mass : forall c : Cut, initial_mass c <= M0max.
Hypothesis Hinitial_route_action :
  forall c : Cut,
    MR.gpr_action (dstar c) (route c) 0%nat <= initial_mass c.

Hypothesis Hscale_gk :
  UniformGKCostDriftEnvelope
    Cut
    (fun c => MR.gpr_scale_paid (dstar c) (route c))
    scale_gk Bscost Bsdrift.
Hypothesis Hfuture_gk :
  UniformGKCostDriftEnvelope
    Cut
    (fun c => MR.gpr_future_paid (dstar c) (route c))
    future_gk Bfcost Bfdrift.
Hypothesis Hresidual_gk :
  UniformGKCostDriftEnvelope
    Cut
    (fun c => MR.gpr_residual_paid (dstar c) (route c))
    residual_gk Brcost Brdrift.

Theorem UAC10_GK_ENVELOPES_PLUS_INITIAL_MASS_GIVE_UNIFORM_ROUTE_BUDGET :
  UCM.UniformRouteBudget
    Cut dstar route
    M0max
    (Bscost + Bsdrift)
    (Bfcost + Bfdrift)
    (Brcost + Brdrift).
Proof.
  constructor.
  - exact HM0.
  - destruct Hscale_gk as [Hs0 Hsd0 _ _]. lra.
  - destruct Hfuture_gk as [Hf0 Hfd0 _ _]. lra.
  - destruct Hresidual_gk as [Hr0 Hrd0 _ _]. lra.
  - intro c.
    specialize (Hinitial_route_action c).
    specialize (Hinitial_mass c).
    lra.
  - intros c N.
    exact (UAC00_UNIFORM_GK_ENVELOPE_GIVES_COMMON_PAID_PREFIX
      Cut
      (fun c0 => MR.gpr_scale_paid (dstar c0) (route c0))
      scale_gk Bscost Bsdrift Hscale_gk c N).
  - intros c N.
    exact (UAC00_UNIFORM_GK_ENVELOPE_GIVES_COMMON_PAID_PREFIX
      Cut
      (fun c0 => MR.gpr_future_paid (dstar c0) (route c0))
      future_gk Bfcost Bfdrift Hfuture_gk c N).
  - intros c N.
    exact (UAC00_UNIFORM_GK_ENVELOPE_GIVES_COMMON_PAID_PREFIX
      Cut
      (fun c0 => MR.gpr_residual_paid (dstar c0) (route c0))
      residual_gk Brcost Brdrift Hresidual_gk c N).
Qed.

End RouteBudgetFromGK.

(* ------------------------------------------------------------------ *)
(* 3. The physical M7 coupling pays action_cost, not critical_mass.    *)
(*    The critical-energy balance adds initial mass separately.        *)
(* ------------------------------------------------------------------ *)

Section UniformActionCostToCriticalMass.

Variable Cut Time : Type.
Variable dstar : Cut -> nat.
Variable route : forall c : Cut, MR.GPRouteCertificate (dstar c).

Variable nu sigma : R.
Variable initial_mass : Cut -> R.
Variable critical_mass critical_dissipation action_cost : Cut -> Time -> R.

Definition FiniteCutActionCostRouteRealization : Prop :=
  forall (c : Cut) (t : Time),
    exists N : nat,
      action_cost c t <=
      RR.prefix_sum (MR.gpr_action (dstar c) (route c)) N.

Definition UniformFiniteCutCriticalBalance : Prop :=
  forall c : Cut,
    CE.CriticalEnergyBalance
      Time nu sigma (initial_mass c)
      (critical_mass c)
      (critical_dissipation c)
      (action_cost c).

Theorem UAC20_ROUTE_PREFIX_PAYS_ACTION_COST_GIVES_UNIFORM_CRITICAL_MASS :
  forall M0max A0max Bs Bf Br,
    0 <= M0max ->
    (forall c : Cut, initial_mass c <= M0max) ->
    UCM.UniformRouteBudget Cut dstar route A0max Bs Bf Br ->
    FiniteCutActionCostRouteRealization ->
    UniformFiniteCutCriticalBalance ->
    exists B : R,
      forall (c : Cut) (t : Time), critical_mass c t <= B.
Proof.
  intros M0max A0max Bs Bf Br HM0 Hinit Hbud Hreal Hbal.
  exists (M0max + 4 * A0max + Bs + Bf + Br).
  intros c t.
  destruct (Hreal c t) as [N Hact].
  pose proof
    (UCM.UCM10_COMMON_ROUTE_BUDGET_GIVES_UNIFORM_ACTION_PREFIX
      Cut dstar route A0max Bs Bf Br Hbud c N) as Hprefix.
  pose proof (Hbal c) as HB.
  destruct HB as
    [Hnu Hsig0 Hsig1 Hinit0 Hmass0 Hdiss0 Hact0 Hbalance].
  specialize (Hbalance t).
  specialize (Hdiss0 t).
  specialize (Hinit c).
  assert (He : 0 < CE.effective_viscosity nu sigma).
  { unfold CE.effective_viscosity; nra. }
  assert (Hed : 0 <= CE.effective_viscosity nu sigma * critical_dissipation c t).
  { apply Rmult_le_pos; [exact (Rlt_le _ _ He)|exact Hdiss0]. }
  lra.
Qed.

Theorem UAC21_ROUTE_PREFIX_PAYS_ACTION_COST_GIVES_UNIFORM_CUT_BOUND_AT_EACH_TIME :
  forall M0max A0max Bs Bf Br,
    0 <= M0max ->
    (forall c : Cut, initial_mass c <= M0max) ->
    UCM.UniformRouteBudget Cut dstar route A0max Bs Bf Br ->
    FiniteCutActionCostRouteRealization ->
    UniformFiniteCutCriticalBalance ->
    exists B : R,
      forall t : Time,
        FC.UniformFiniteCutBound Cut (fun c => critical_mass c t) /\
        (forall c : Cut, critical_mass c t <= B).
Proof.
  intros M0max A0max Bs Bf Br HM0 Hinit Hbud Hreal Hbal.
  destruct
    (UAC20_ROUTE_PREFIX_PAYS_ACTION_COST_GIVES_UNIFORM_CRITICAL_MASS
      M0max A0max Bs Bf Br HM0 Hinit Hbud Hreal Hbal)
    as [B HB].
  exists B.
  intro t.
  split.
  - exists B. intro c. exact (HB c t).
  - intro c. exact (HB c t).
Qed.

Theorem UAC22_ACTION_COST_COUPLING_CONTROLS_FULL_CRITICAL_READOUT :
  forall (full_mass : Time -> R) M0max A0max Bs Bf Br,
    0 <= M0max ->
    (forall c : Cut, initial_mass c <= M0max) ->
    UCM.UniformRouteBudget Cut dstar route A0max Bs Bf Br ->
    FiniteCutActionCostRouteRealization ->
    UniformFiniteCutCriticalBalance ->
    (forall t : Time,
      FC.FullCriticalLimitReadout Cut (fun c => critical_mass c t) (full_mass t)) ->
    exists B : R, forall t : Time, full_mass t <= B.
Proof.
  intros full_mass M0max A0max Bs Bf Br HM0 Hinit Hbud Hreal Hbal Hread.
  destruct
    (UAC20_ROUTE_PREFIX_PAYS_ACTION_COST_GIVES_UNIFORM_CRITICAL_MASS
      M0max A0max Bs Bf Br HM0 Hinit Hbud Hreal Hbal)
    as [B HB].
  exists B.
  intro t.
  destruct (Hread t) as [_ Hleast].
  apply Hleast.
  intro c.
  exact (HB c t).
Qed.

End UniformActionCostToCriticalMass.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_R3_FORCED_GP_DIAMOND_UNIFORM_ACTION_COST.

Print NSE_R3_FORCED_GP_DIAMOND_UNIFORM_ACTION_COST.UAC00_UNIFORM_GK_ENVELOPE_GIVES_COMMON_PAID_PREFIX.
Print NSE_R3_FORCED_GP_DIAMOND_UNIFORM_ACTION_COST.UAC10_GK_ENVELOPES_PLUS_INITIAL_MASS_GIVE_UNIFORM_ROUTE_BUDGET.
Print NSE_R3_FORCED_GP_DIAMOND_UNIFORM_ACTION_COST.UAC20_ROUTE_PREFIX_PAYS_ACTION_COST_GIVES_UNIFORM_CRITICAL_MASS.
Print NSE_R3_FORCED_GP_DIAMOND_UNIFORM_ACTION_COST.UAC22_ACTION_COST_COUPLING_CONTROLS_FULL_CRITICAL_READOUT.
