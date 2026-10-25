From Stdlib Require Import Reals Lra String.
Require Import NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.
Require Import awpi_nse_gp_storage_replenishment_v0_51_7.
Require Import awpi_nse_direct_gp_shell_occupancy_v0_48_4.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.
Require Import awpi_nse_scalar_comparison_v0_48_4.
Require Import awpi_nse_direct_gp_action_m7_chain_v0_47_0.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.

Module NSE_R3_FORCED_GP_DIAMOND_STORAGE_BRIDGE.
Module FC := NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.
Module SR := NSE_GP_STORAGE_REPLENISHMENT.
Module O := NSE_DIRECT_GP_SHELL_OCCUPANCY.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Module SC := NSE_SCALAR_COMPARISON.
Module DG := NSE_DIRECT_GP_ACTION_M7_CHAIN.
Module M7 := NSE_GP_TO_M7_SPINE.
Open Scope R_scope.

(* Storage/replenishment is an alternate uniform-cut closure engine.
   The theorem below does not assert its physical hypotheses automatically. *)

Section STORAGE_TO_UNIFORM_CUTS.

Context {Cut Time : Type}.
Variable ev : Cut -> O.ShellEvolution.
Variable path : Cut -> SR.StoragePath.
Variable stamp : Time -> R.
Variable cut_time : nat -> Time.
Variable nu cap theta cs E0 M0 T kappa Hinit gamma Chigh : R.

Hypothesis Hnu : 0 < nu.
Hypothesis Hcap : 0 <= cap.
Hypothesis HE0 : 0 <= E0.
Hypothesis Htheta0 : 0 <= theta.
Hypothesis Htheta1 : theta < 1.
Hypothesis Hkappa : 0 <= kappa.
Hypothesis Hgamma : gamma < 1.
Hypothesis Hbindings :
  forall c : Cut,
    O.EvolutionBindings nu cap theta cs E0 M0 T (ev c).
Hypothesis Hstorage :
  forall c : Cut,
    SR.ExactIntegratedStorage T (ev c) (path c).
Hypothesis Hinitial_storage :
  forall c : Cut,
    SR.sp_H (path c) 0 <= Hinit.
Hypothesis Hlower_payments :
  forall c : Cut,
    SR.LowerOutputPayments nu cap kappa T (ev c) (path c).
Hypothesis Hhigh_absorption :
  forall c : Cut,
    SR.HighOutputAbsorption gamma Chigh T (ev c) (path c).
Hypothesis Htime : forall t : Time, SC.within T (stamp t).
Hypothesis Hzero : stamp (cut_time O) = 0.
Hypothesis Horder : forall n, stamp (cut_time n) <= stamp (cut_time (S n)).
Hypothesis Hcofinal : forall t : Time, exists n, stamp t <= stamp (cut_time n).

Theorem SB10_STORAGE_TERMINAL_GIVES_UNIFORM_CUT_CRITICAL_MASS :
  forall t0 : Time,
    FC.UniformFiniteCutBound
      Cut
      (fun c : Cut => O.ev_E (ev c) (stamp t0)).
Proof.
  intro t0.
  pose proof
    (SR.NSRA99_STORAGE_REPLENISHMENT_TO_EXISTING_M7_TERMINAL
      Cut Time ev path stamp cut_time
      nu cap theta cs E0 M0 T kappa Hinit gamma Chigh
      Hnu Hcap HE0 Htheta0 Htheta1 Hkappa Hgamma
      Hbindings Hstorage Hinitial_storage Hlower_payments Hhigh_absorption
      Htime Hzero Horder Hcofinal) as Hterm.
  cbv zeta in Hterm.
  destruct Hterm as [HM7 [Hreal [Hseed [Hpaid Hcrit]]]].
  unfold CE.UniformCriticalEnergy in Hcrit.
  destruct Hcrit as [Mmax [Dmax [HMmax [HDmax [Hmass Hdiss]]]]].
  exists Mmax.
  intro c.
  exact (Hmass (c, t0)).
Qed.

Theorem SB20_STORAGE_TERMINAL_GIVES_FULL_CRITICAL_BOUND :
  forall (full_mass : Time -> R),
    (forall t : Time,
      FC.FullCriticalLimitReadout
        Cut
        (fun c : Cut => O.ev_E (ev c) (stamp t))
        (full_mass t)) ->
    forall t : Time,
      exists B : R, full_mass t <= B.
Proof.
  intros full_mass Hread t.
  eapply FC.FC30_UNIFORM_FINITE_CUT_BOUND_CONTROLS_FULL_CRITICAL_READOUT.
  - exact (Hread t).
  - exact (SB10_STORAGE_TERMINAL_GIVES_UNIFORM_CUT_CRITICAL_MASS t).
Qed.

(* The same storage theorem also supplies the old M7 sequence/action-cost
   conclusions uniformly in the regulator index. *)
Theorem SB30_STORAGE_TERMINAL_GIVES_UNIFORM_M7_AND_ACTION_COST :
  exists Cmax : R,
    (forall c : Cut,
      M7.GPSequenceM7
        (DG.action_increment
          (fun c0 t => O.ev_C (ev c0) (stamp t)) cut_time c)) /\
    (forall c : Cut,
      CE.M7ActionCostRealization
        Time
        (DG.action_increment
          (fun c0 t => O.ev_C (ev c0) (stamp t)) cut_time c)
        (fun t => O.ev_C (ev c) (stamp t))) /\
    (forall c n,
      M7.paid_prefix
        (DG.renewal_debt
          (DG.action_increment
            (fun c0 t => O.ev_C (ev c0) (stamp t)) cut_time c)) n
      <= Cmax).
Proof.
  pose proof
    (SR.NSRA99_STORAGE_REPLENISHMENT_TO_EXISTING_M7_TERMINAL
      Cut Time ev path stamp cut_time
      nu cap theta cs E0 M0 T kappa Hinit gamma Chigh
      Hnu Hcap HE0 Htheta0 Htheta1 Hkappa Hgamma
      Hbindings Hstorage Hinitial_storage Hlower_payments Hhigh_absorption
      Htime Hzero Horder Hcofinal) as Hterm.
  cbv zeta in Hterm.
  set (Ustar := SR.upstream_budget nu cap kappa Hinit M0 gamma Chigh).
  set (Cmax := O.action_budget cs nu theta (SC.energy_budget nu cap M0 E0 Ustar)).
  exists Cmax.
  destruct Hterm as [HM7 [Hreal [Hseed [Hpaid Hcrit]]]].
  repeat split; assumption.
Qed.

End STORAGE_TO_UNIFORM_CUTS.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_STORAGE_BRIDGE_V0_23_1"%string.
End NSE_R3_FORCED_GP_DIAMOND_STORAGE_BRIDGE.

Print NSE_R3_FORCED_GP_DIAMOND_STORAGE_BRIDGE.SB10_STORAGE_TERMINAL_GIVES_UNIFORM_CUT_CRITICAL_MASS.
Print NSE_R3_FORCED_GP_DIAMOND_STORAGE_BRIDGE.SB20_STORAGE_TERMINAL_GIVES_FULL_CRITICAL_BOUND.
Print NSE_R3_FORCED_GP_DIAMOND_STORAGE_BRIDGE.SB30_STORAGE_TERMINAL_GIVES_UNIFORM_M7_AND_ACTION_COST.
