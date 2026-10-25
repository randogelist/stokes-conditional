From Stdlib Require Import Reals Lra Psatz String.
Require Import NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.
Require Import awpi_nse_gp_to_m7_route_v0_28_3.
Require Import awpi_nse_gp_renewal_reduction_v0_3_1.

Module NSE_R3_FORCED_GP_DIAMOND_UNIFORM_CUTOFF_M7.
Module FC := NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.
Module MR := NSE_GP_TO_M7_ROUTE.
Module RR := NSE_GP_RENEWAL_REDUCTION.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* Cutoff-independent local role constants.                            *)
(* ------------------------------------------------------------------ *)

Record UniformGalerkRoleConstants : Type := {
  ugr_theta : R;
  ugr_eps_safe : R;
  ugr_eps_paid : R;
  ugr_Cstar : R;
  ugr_theta_nonneg : 0 <= ugr_theta;
  ugr_eps_safe_nonneg : 0 <= ugr_eps_safe;
  ugr_eps_paid_nonneg : 0 <= ugr_eps_paid;
  ugr_gap_pos : ugr_theta + ugr_eps_safe + ugr_eps_paid < 1;
  ugr_Cstar_pos : 0 < ugr_Cstar
}.

Definition uniform_injection_coefficient (C : UniformGalerkRoleConstants) : R :=
  ((1 - ugr_theta C - ugr_eps_safe C - ugr_eps_paid C) ^ 2)
  / (9 * ugr_Cstar C).

Theorem UCM00_UNIFORM_INJECTION_COEFFICIENT_POSITIVE :
  forall C : UniformGalerkRoleConstants,
    0 < uniform_injection_coefficient C.
Proof.
  intros C.
  unfold uniform_injection_coefficient.
  assert (Hgap : 0 < 1 - ugr_theta C - ugr_eps_safe C - ugr_eps_paid C).
  { pose proof (ugr_gap_pos C); lra. }
  assert (Hsq : 0 < (1 - ugr_theta C - ugr_eps_safe C - ugr_eps_paid C)^2).
  { nra. }
  assert (Hden : 0 < 9 * ugr_Cstar C).
  { pose proof (ugr_Cstar_pos C); nra. }
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  - exact Hsq.
  - apply Rinv_0_lt_compat; exact Hden.
Qed.

(* ------------------------------------------------------------------ *)
(* Uniform route family: global upper ledger is a separate issue from  *)
(* the local role adapter.                                             *)
(* ------------------------------------------------------------------ *)

Section UniformRouteFamily.

Variable Cut : Type.
Variable dstar : Cut -> nat.
Variable route : forall c : Cut, MR.GPRouteCertificate (dstar c).

Record UniformRouteBudget
  (A0max Bs Bf Br : R) : Prop := {
  urb_A0_nonneg : 0 <= A0max;
  urb_Bs_nonneg : 0 <= Bs;
  urb_Bf_nonneg : 0 <= Bf;
  urb_Br_nonneg : 0 <= Br;
  urb_initial_action : forall c : Cut,
    MR.gpr_action (dstar c) (route c) 0%nat <= A0max;
  urb_scale_prefix : forall (c : Cut) (N : nat),
    RR.prefix_sum (MR.gpr_scale_paid (dstar c) (route c)) N <= Bs;
  urb_future_prefix : forall (c : Cut) (N : nat),
    RR.prefix_sum (MR.gpr_future_paid (dstar c) (route c)) N <= Bf;
  urb_residual_prefix : forall (c : Cut) (N : nat),
    RR.prefix_sum (MR.gpr_residual_paid (dstar c) (route c)) N <= Br
}.

Theorem UCM10_COMMON_ROUTE_BUDGET_GIVES_UNIFORM_ACTION_PREFIX :
  forall A0max Bs Bf Br,
    UniformRouteBudget A0max Bs Bf Br ->
    forall (c : Cut) (N : nat),
      RR.prefix_sum (MR.gpr_action (dstar c) (route c)) N
      <= 4 * A0max + Bs + Bf + Br.
Proof.
  intros A0max Bs Bf Br Hbud c N.
  destruct Hbud as [HA0 HBs0 HBf0 HBr0 Hinit Hs Hf Hr].
  pose proof
    (MR.GPMR40_EXPLICIT_GP_M7_BOUND
      (dstar c) (route c) Bs Bf Br
      HBs0 HBf0 HBr0 (Hs c) (Hf c) (Hr c) N) as Hroute.
  specialize (Hinit c).
  lra.
Qed.

Definition FiniteCutMassRouteRealization
  (critical_mass : Cut -> R) : Prop :=
  forall c : Cut,
    exists N : nat,
      critical_mass c <=
      RR.prefix_sum (MR.gpr_action (dstar c) (route c)) N.

Theorem UCM20_UNIFORM_ROUTE_BUDGET_CONTROLS_ALL_FINITE_CUT_MASSES :
  forall (critical_mass : Cut -> R) A0max Bs Bf Br,
    UniformRouteBudget A0max Bs Bf Br ->
    FiniteCutMassRouteRealization critical_mass ->
    FC.UniformFiniteCutBound Cut critical_mass.
Proof.
  intros critical_mass A0max Bs Bf Br Hbud Hreal.
  exists (4 * A0max + Bs + Bf + Br).
  intro c.
  destruct (Hreal c) as [N Hmass].
  eapply Rle_trans; [exact Hmass|].
  exact (UCM10_COMMON_ROUTE_BUDGET_GIVES_UNIFORM_ACTION_PREFIX
    A0max Bs Bf Br Hbud c N).
Qed.

Theorem UCM21_UNIFORM_ROUTE_BUDGET_CONTROLS_FULL_CRITICAL_READOUT :
  forall (critical_mass : Cut -> R) (full_mass : R) A0max Bs Bf Br,
    UniformRouteBudget A0max Bs Bf Br ->
    FiniteCutMassRouteRealization critical_mass ->
    FC.FullCriticalLimitReadout Cut critical_mass full_mass ->
    exists B : R, full_mass <= B.
Proof.
  intros critical_mass full_mass A0max Bs Bf Br Hbud Hreal Hread.
  apply (FC.FC30_UNIFORM_FINITE_CUT_BOUND_CONTROLS_FULL_CRITICAL_READOUT
    Cut critical_mass full_mass Hread).
  exact (UCM20_UNIFORM_ROUTE_BUDGET_CONTROLS_ALL_FINITE_CUT_MASSES
    critical_mass A0max Bs Bf Br Hbud Hreal).
Qed.

End UniformRouteFamily.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_R3_FORCED_GP_DIAMOND_UNIFORM_CUTOFF_M7.

Print NSE_R3_FORCED_GP_DIAMOND_UNIFORM_CUTOFF_M7.UCM00_UNIFORM_INJECTION_COEFFICIENT_POSITIVE.
Print NSE_R3_FORCED_GP_DIAMOND_UNIFORM_CUTOFF_M7.UCM10_COMMON_ROUTE_BUDGET_GIVES_UNIFORM_ACTION_PREFIX.
Print NSE_R3_FORCED_GP_DIAMOND_UNIFORM_CUTOFF_M7.UCM20_UNIFORM_ROUTE_BUDGET_CONTROLS_ALL_FINITE_CUT_MASSES.
Print NSE_R3_FORCED_GP_DIAMOND_UNIFORM_CUTOFF_M7.UCM21_UNIFORM_ROUTE_BUDGET_CONTROLS_FULL_CRITICAL_READOUT.
