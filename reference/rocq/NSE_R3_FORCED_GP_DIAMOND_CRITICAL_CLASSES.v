From Stdlib Require Import Reals Lra Psatz String.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.
Require Import NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.

Module NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.

Open Scope R_scope.

Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.

(*
  Forced-Diamond critical classes.

  The internal nonlinear transfer is already handled by the unforced M7
  ledger.  A forcing term contributes a second, nonnegative external ledger.
  Class A is the largest class at this scalar ledger level for which the
  existing upper-bound mechanism closes: both ledgers are uniformly bounded.

  The breakdown side must use an exact net-work balance, not the mere failure
  of an upper-bound criterion.  Class B is therefore the exact scalar class
  in which net critical work is unbounded above.  This forces critical mass
  to be unbounded.
*)

Section FORCED_LEDGER.

Variable Time : Type.
Variable nu sigma initial_mass : R.
Variable critical_mass critical_dissipation : Time -> R.
Variable internal_cost force_cost : Time -> R.

Definition total_action_cost (t : Time) : R :=
  internal_cost t + force_cost t.

Record ForcedCriticalEnergyBalance : Prop := {
  fceb_nu_pos : 0 < nu;
  fceb_sigma_nonneg : 0 <= sigma;
  fceb_sigma_lt_one : sigma < 1;
  fceb_initial_nonneg : 0 <= initial_mass;
  fceb_mass_nonneg : forall t : Time, 0 <= critical_mass t;
  fceb_dissipation_nonneg : forall t : Time, 0 <= critical_dissipation t;
  fceb_internal_nonneg : forall t : Time, 0 <= internal_cost t;
  fceb_force_nonneg : forall t : Time, 0 <= force_cost t;
  fceb_integrated_balance :
    forall t : Time,
      critical_mass t +
      CE.effective_viscosity nu sigma * critical_dissipation t <=
      initial_mass + internal_cost t + force_cost t
}.

Definition BoundedLedger (cost : Time -> R) : Prop :=
  exists Cmax : R,
    0 <= Cmax /\
    forall t : Time, cost t <= Cmax.

Definition ForcedRegularClassA : Prop :=
  BoundedLedger internal_cost /\ BoundedLedger force_cost.

Theorem FD01_FORCED_BALANCE_TO_EXISTING_CRITICAL_BALANCE :
  ForcedCriticalEnergyBalance ->
  CE.CriticalEnergyBalance
    Time nu sigma initial_mass
    critical_mass critical_dissipation total_action_cost.
Proof.
  intro H.
  destruct H as
    [Hnu Hs0 Hs1 Hinit Hm Hd Hi Hf Hbal].
  constructor.
  - exact Hnu.
  - exact Hs0.
  - exact Hs1.
  - exact Hinit.
  - exact Hm.
  - exact Hd.
  - intro t. unfold total_action_cost. specialize (Hi t). specialize (Hf t). lra.
  - intro t. unfold total_action_cost. specialize (Hbal t). lra.
Qed.

Theorem FD02_CLASS_A_GIVES_UNIFORM_CRITICAL_ENERGY :
  ForcedCriticalEnergyBalance ->
  ForcedRegularClassA ->
  CE.UniformCriticalEnergy Time critical_mass critical_dissipation.
Proof.
  intros Hbal [Hint Hforce].
  destruct Hint as [Imax [HI0 HI]].
  destruct Hforce as [Fmax [HF0 HF]].
  eapply CE.NSCE10_ACTION_COST_BOUND_GIVES_CRITICAL_ENERGY
    with (Amax := Imax + Fmax)
         (action_cost := total_action_cost).
  - apply FD01_FORCED_BALANCE_TO_EXISTING_CRITICAL_BALANCE.
    exact Hbal.
  - lra.
  - intro t. unfold total_action_cost. specialize (HI t). specialize (HF t). lra.
Qed.

Theorem FD03_ZERO_FORCE_LEDGER_RECOVERS_UNFORCED_CLASS :
  (forall t : Time, force_cost t = 0) ->
  BoundedLedger internal_cost ->
  ForcedRegularClassA.
Proof.
  intros Hzero Hint.
  split.
  - exact Hint.
  - exists 0. split.
    + lra.
    + intro t. rewrite (Hzero t). lra.
Qed.

End FORCED_LEDGER.

Section BREAKDOWN_LEDGER.

Variable Time : Type.
Variable initial_mass : R.
Variable critical_mass net_critical_work : Time -> R.

Record ExactNetCriticalBalance : Prop := {
  encb_mass_nonneg : forall t : Time, 0 <= critical_mass t;
  encb_exact_balance :
    forall t : Time,
      critical_mass t = initial_mass + net_critical_work t
}.

Definition CriticalMassBounded : Prop :=
  exists Mmax : R, forall t : Time, critical_mass t <= Mmax.

Definition CriticalMassUnbounded : Prop :=
  forall M : R, exists t : Time, M < critical_mass t.

Definition NetCriticalWorkUnboundedAbove : Prop :=
  forall W : R, exists t : Time, W < net_critical_work t.

Definition ForcedBreakdownClassB : Prop :=
  ExactNetCriticalBalance /\ NetCriticalWorkUnboundedAbove.

Theorem FD10_NET_WORK_UNBOUNDED_GIVES_CRITICAL_MASS_UNBOUNDED :
  ExactNetCriticalBalance ->
  NetCriticalWorkUnboundedAbove ->
  CriticalMassUnbounded.
Proof.
  intros Hbal Hwork M.
  destruct Hbal as [Hm Hbal].
  destruct (Hwork (M - initial_mass)) as [t Ht].
  exists t.
  specialize (Hbal t).
  lra.
Qed.

Theorem FD11_CRITICAL_MASS_UNBOUNDED_EXCLUDES_BOUNDEDNESS :
  CriticalMassUnbounded ->
  ~ CriticalMassBounded.
Proof.
  intros Hunb [Mmax HM].
  destruct (Hunb Mmax) as [t Ht].
  specialize (HM t).
  lra.
Qed.

Theorem FD12_CLASS_B_EXCLUDES_CRITICAL_BOUNDEDNESS :
  ForcedBreakdownClassB ->
  ~ CriticalMassBounded.
Proof.
  intros [Hbal Hwork].
  apply FD11_CRITICAL_MASS_UNBOUNDED_EXCLUDES_BOUNDEDNESS.
  eapply FD10_NET_WORK_UNBOUNDED_GIVES_CRITICAL_MASS_UNBOUNDED.
  - exact Hbal.
  - exact Hwork.
Qed.

Variable PhysicalRegular : Prop.
Variable physical_regular_implies_critical_bounded :
  PhysicalRegular -> CriticalMassBounded.

Theorem FD13_CLASS_B_EXCLUDES_PHYSICAL_REGULARITY :
  ForcedBreakdownClassB ->
  ~ PhysicalRegular.
Proof.
  intro HB.
  intro Hreg.
  apply (FD12_CLASS_B_EXCLUDES_CRITICAL_BOUNDEDNESS HB).
  apply physical_regular_implies_critical_bounded.
  exact Hreg.
Qed.

End BREAKDOWN_LEDGER.

(* Exact scalar boundary object: the transition is whether the external ledger
   remains bounded on the regular side, versus whether the exact net critical
   work becomes unbounded on the breakdown side.  Identification of the
   maximal uniform forcing-only class with L^2_t H^{-1/2}_x is a separate
   functional-analytic/Riesz representation theorem. *)

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES_V0_9_0"%string.

End NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.
