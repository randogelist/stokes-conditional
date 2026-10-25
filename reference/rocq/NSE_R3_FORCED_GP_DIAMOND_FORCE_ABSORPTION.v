From Stdlib Require Import Reals Lra Psatz String.
Require Import NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.
Require Import NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.

Module IFC := NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.
Module FC := NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.

Open Scope R_scope.

(*
  Forced critical-energy absorption after the internal M7 step.

  The unforced Diamond leaves the effective viscosity
      e = (1-sigma) nu > 0.

  Spend only a fraction theta in (0,1) of this remaining viscosity to absorb
  the external force.  Then the residual viscosity is
      (1-theta)e
  and the force ledger is normalized by 1/(theta e).
*)

Definition forced_sigma (sigma theta : R) : R :=
  sigma + theta * (1 - sigma).

Theorem FA00_FORCED_SIGMA_RANGE :
  forall sigma theta : R,
    0 <= sigma -> sigma < 1 ->
    0 < theta -> theta < 1 ->
    0 <= forced_sigma sigma theta /\
    forced_sigma sigma theta < 1.
Proof.
  intros sigma theta Hs0 Hs1 Ht0 Ht1.
  unfold forced_sigma.
  split; nra.
Qed.

Theorem FA01_RESIDUAL_VISCOSITY_IDENTITY :
  forall nu sigma theta : R,
    CE.effective_viscosity nu (forced_sigma sigma theta) =
    (1 - theta) * CE.effective_viscosity nu sigma.
Proof.
  intros nu sigma theta.
  unfold CE.effective_viscosity, forced_sigma.
  ring.
Qed.

Section INTEGRATED_ABSORPTION.

Variable Time : Type.
Variable nu sigma theta initial_mass : R.
Variable critical_mass critical_dissipation : Time -> R.
Variable internal_cost force_work intrinsic_force_cost : Time -> R.

Record PostM7ForcedCriticalBalance : Prop := {
  pmfb_nu_pos : 0 < nu;
  pmfb_sigma_nonneg : 0 <= sigma;
  pmfb_sigma_lt_one : sigma < 1;
  pmfb_initial_nonneg : 0 <= initial_mass;
  pmfb_mass_nonneg : forall t : Time, 0 <= critical_mass t;
  pmfb_dissipation_nonneg : forall t : Time, 0 <= critical_dissipation t;
  pmfb_internal_nonneg : forall t : Time, 0 <= internal_cost t;
  pmfb_integrated_balance :
    forall t : Time,
      critical_mass t +
      CE.effective_viscosity nu sigma * critical_dissipation t <=
      initial_mass + internal_cost t + 2 * force_work t
}.

Definition normalized_intrinsic_force_cost (t : Time) : R :=
  intrinsic_force_cost t /
  (theta * CE.effective_viscosity nu sigma).

Record AccumulatedIntrinsicForceAbsorption : Prop := {
  aifa_theta_pos : 0 < theta;
  aifa_theta_lt_one : theta < 1;
  aifa_intrinsic_nonneg : forall t : Time, 0 <= intrinsic_force_cost t;
  aifa_absorption :
    forall t : Time,
      2 * force_work t <=
      theta * CE.effective_viscosity nu sigma * critical_dissipation t +
      normalized_intrinsic_force_cost t
}.

Theorem FA10_POST_M7_PLUS_INTRINSIC_ABSORPTION_GIVES_FORCED_BALANCE :
  PostM7ForcedCriticalBalance ->
  AccumulatedIntrinsicForceAbsorption ->
  FC.ForcedCriticalEnergyBalance
    Time nu (forced_sigma sigma theta) initial_mass
    critical_mass critical_dissipation
    internal_cost normalized_intrinsic_force_cost.
Proof.
  intros Hraw Habs.
  destruct Hraw as
    [Hnu Hs0 Hs1 Hinit Hm Hd Hi Hrawbal].
  destruct Habs as [Ht0 Ht1 Hf0 Habsorb].
  pose proof (FA00_FORCED_SIGMA_RANGE sigma theta Hs0 Hs1 Ht0 Ht1)
    as [Hfs0 Hfs1].
  assert (He : 0 < CE.effective_viscosity nu sigma).
  {
    unfold CE.effective_viscosity.
    nra.
  }
  assert (Hden : 0 < theta * CE.effective_viscosity nu sigma) by nra.
  constructor.
  - exact Hnu.
  - exact Hfs0.
  - exact Hfs1.
  - exact Hinit.
  - exact Hm.
  - exact Hd.
  - exact Hi.
  - intro t.
    unfold normalized_intrinsic_force_cost, Rdiv.
    apply Rmult_le_pos.
    + apply Hf0.
    + apply Rlt_le.
      apply Rinv_0_lt_compat.
      exact Hden.
  - intro t.
    specialize (Hrawbal t).
    specialize (Habsorb t).
    rewrite FA01_RESIDUAL_VISCOSITY_IDENTITY.
    nra.
Qed.

Theorem FA11_BOUNDED_INTRINSIC_SIZE_GIVES_BOUNDED_NORMALIZED_LEDGER :
  PostM7ForcedCriticalBalance ->
  AccumulatedIntrinsicForceAbsorption ->
  FC.BoundedLedger Time intrinsic_force_cost ->
  FC.BoundedLedger Time normalized_intrinsic_force_cost.
Proof.
  intros Hraw Habs Hbounded.
  destruct Hraw as
    [Hnu Hs0 Hs1 Hinit Hm Hd Hi Hrawbal].
  destruct Habs as [Ht0 Ht1 Hf0 Habsorb].
  destruct Hbounded as [Fmax [HF0 HF]].
  assert (He : 0 < CE.effective_viscosity nu sigma).
  {
    unfold CE.effective_viscosity.
    nra.
  }
  assert (Hden : 0 < theta * CE.effective_viscosity nu sigma) by nra.
  exists (Fmax / (theta * CE.effective_viscosity nu sigma)).
  split.
  - unfold Rdiv.
    apply Rmult_le_pos.
    + exact HF0.
    + apply Rlt_le.
      apply Rinv_0_lt_compat.
      exact Hden.
  - intro t.
    unfold normalized_intrinsic_force_cost, Rdiv.
    apply Rmult_le_compat_r.
    + apply Rlt_le.
      apply Rinv_0_lt_compat.
      exact Hden.
    + apply HF.
Qed.

Theorem FA12_POST_M7_INTRINSIC_CLASS_GIVES_REGULARITY :
  PostM7ForcedCriticalBalance ->
  AccumulatedIntrinsicForceAbsorption ->
  FC.BoundedLedger Time internal_cost ->
  FC.BoundedLedger Time intrinsic_force_cost ->
  CE.UniformCriticalEnergy Time critical_mass critical_dissipation.
Proof.
  intros Hraw Habs Hint Hforce.
  pose proof
    (FA10_POST_M7_PLUS_INTRINSIC_ABSORPTION_GIVES_FORCED_BALANCE
      Hraw Habs) as Hbal.
  pose proof
    (FA11_BOUNDED_INTRINSIC_SIZE_GIVES_BOUNDED_NORMALIZED_LEDGER
      Hraw Habs Hforce) as Hnorm.
  eapply (@FC.FD02_CLASS_A_GIVES_UNIFORM_CRITICAL_ENERGY
    Time nu (forced_sigma sigma theta) initial_mass
    critical_mass critical_dissipation
    internal_cost normalized_intrinsic_force_cost).
  - exact Hbal.
  - split; assumption.
Qed.

End INTEGRATED_ABSORPTION.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION_V0_14_0"%string.

End NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.

Check NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.FA10_POST_M7_PLUS_INTRINSIC_ABSORPTION_GIVES_FORCED_BALANCE.
Check NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.FA12_POST_M7_INTRINSIC_CLASS_GIVES_REGULARITY.
