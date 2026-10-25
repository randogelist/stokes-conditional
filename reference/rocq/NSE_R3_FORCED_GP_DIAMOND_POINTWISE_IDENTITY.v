From Stdlib Require Import Reals Lra Psatz String FunctionalExtensionality.
Require Import NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.
Require Import NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.
Require Import NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_R3_FORCED_GP_DIAMOND_POINTWISE_IDENTITY.

Module CBB := NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.
Module AB := NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.
Module FA := NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.

Open Scope R_scope.

(* --------------------------------------------------------------------- *)
(* Pointwise forced critical pairing identity.                            *)
(* --------------------------------------------------------------------- *)

Section POINTWISE_OPERATOR_IDENTITY.

Variable Time : Type.
Variable nu : R.
Variable mass_derivative : Time -> R.
Variable dt_pair viscous_pair nonlinear_pair forcing_pair : Time -> R.
Variable instantaneous_dissipation : Time -> R.
Variable instantaneous_safe instantaneous_resistant instantaneous_force : Time -> R.

Record ForcedNSECriticalPairingData : Prop := {
  fncp_mass_derivative :
    forall t : Time,
      mass_derivative t = 2 * dt_pair t;
  fncp_viscous_pair :
    forall t : Time,
      viscous_pair t = instantaneous_dissipation t;
  fncp_nonlinear_split :
    forall t : Time,
      nonlinear_pair t = - (instantaneous_safe t + instantaneous_resistant t);
  fncp_force_pair :
    forall t : Time,
      forcing_pair t = instantaneous_force t;
  fncp_forced_nse_pairing :
    forall t : Time,
      dt_pair t + nu * viscous_pair t + nonlinear_pair t = forcing_pair t
}.

Theorem PI00_FORCED_NSE_PAIRING_GIVES_POINTWISE_CRITICAL_IDENTITY :
  ForcedNSECriticalPairingData ->
  forall t : Time,
    mass_derivative t + 2 * nu * instantaneous_dissipation t =
    2 * instantaneous_safe t +
    2 * instantaneous_resistant t +
    2 * instantaneous_force t.
Proof.
  intros H t.
  destruct H as [Hm Hv Hn Hf Hnse].
  specialize (Hm t).
  specialize (Hv t).
  specialize (Hn t).
  specialize (Hf t).
  specialize (Hnse t).
  nra.
Qed.

End POINTWISE_OPERATOR_IDENTITY.

(* --------------------------------------------------------------------- *)
(* Fundamental-theorem bridge from pointwise critical identity to the    *)
(* raw integrated forced critical balance used by v0.16.1.              *)
(* --------------------------------------------------------------------- *)

Section POINTWISE_TO_RAW_BALANCE.

Variable Time : Type.
Variable accumulate_until : Time -> (Time -> R) -> R.
Variable nu sigma initial_mass : R.
Variable critical_mass mass_derivative : Time -> R.
Variable instantaneous_dissipation : Time -> R.
Variable instantaneous_safe instantaneous_resistant instantaneous_force : Time -> R.

Definition pi_acc_dissipation (t : Time) : R :=
  accumulate_until t instantaneous_dissipation.

Definition pi_acc_safe (t : Time) : R :=
  accumulate_until t instantaneous_safe.

Definition pi_acc_resistant (t : Time) : R :=
  accumulate_until t instantaneous_resistant.

Definition pi_acc_force (t : Time) : R :=
  accumulate_until t instantaneous_force.

Record CriticalMassPrimitive : Prop := {
  cmp_fundamental_theorem :
    forall t : Time,
      critical_mass t = initial_mass + accumulate_until t mass_derivative
}.

Definition PointwiseForcedCriticalIdentity : Prop :=
  forall t : Time,
    mass_derivative t + 2 * nu * instantaneous_dissipation t =
    2 * instantaneous_safe t +
    2 * instantaneous_resistant t +
    2 * instantaneous_force t.

Theorem PI10_POINTWISE_IDENTITY_ACCUMULATES_TO_RAW_FORCED_BALANCE :
  @AB.PositiveLinearAccumulator Time accumulate_until ->
  0 < nu ->
  0 <= sigma -> sigma < 1 ->
  0 <= initial_mass ->
  (forall t : Time, 0 <= critical_mass t) ->
  (forall t : Time, 0 <= instantaneous_dissipation t) ->
  CriticalMassPrimitive ->
  PointwiseForcedCriticalIdentity ->
  @CBB.ForcedCriticalPreM7Balance
    Time nu sigma initial_mass
    critical_mass pi_acc_dissipation
    pi_acc_safe pi_acc_resistant pi_acc_force.
Proof.
  intros Hacc Hnu Hs0 Hs1 Hinit Hmass Hdiss Hprim Hpoint.
  destruct Hacc as [Hmono Hadd Hscale Hzero].
  destruct Hprim as [Hfund].
  constructor.
  - exact Hnu.
  - exact Hs0.
  - exact Hs1.
  - exact Hinit.
  - exact Hmass.
  - intro t.
    unfold pi_acc_dissipation.
    pose proof
      (Hmono t (fun _ : Time => 0) instantaneous_dissipation
        (fun s => Hdiss s)) as Hm.
    rewrite Hzero in Hm.
    exact Hm.
  - intro t.
    assert (Hle :
      forall s : Time,
        mass_derivative s + 2 * nu * instantaneous_dissipation s <=
        2 * instantaneous_safe s +
        2 * instantaneous_resistant s +
        2 * instantaneous_force s).
    {
      intro s.
      rewrite (Hpoint s).
      lra.
    }
    pose proof
      (Hmono t
        (fun s => mass_derivative s + 2 * nu * instantaneous_dissipation s)
        (fun s => 2 * instantaneous_safe s +
                  2 * instantaneous_resistant s +
                  2 * instantaneous_force s)
        Hle) as Haccineq.
    rewrite (Hadd t mass_derivative
      (fun s => 2 * nu * instantaneous_dissipation s)) in Haccineq.
    rewrite (Hscale t (2 * nu) instantaneous_dissipation) in Haccineq by lra.
    rewrite (Hadd t
      (fun s => 2 * instantaneous_safe s + 2 * instantaneous_resistant s)
      (fun s => 2 * instantaneous_force s)) in Haccineq.
    rewrite (Hadd t
      (fun s => 2 * instantaneous_safe s)
      (fun s => 2 * instantaneous_resistant s)) in Haccineq.
    rewrite (Hscale t 2 instantaneous_safe) in Haccineq by lra.
    rewrite (Hscale t 2 instantaneous_resistant) in Haccineq by lra.
    rewrite (Hscale t 2 instantaneous_force) in Haccineq by lra.
    unfold pi_acc_dissipation, pi_acc_safe, pi_acc_resistant, pi_acc_force.
    specialize (Hfund t).
    nra.
Qed.

End POINTWISE_TO_RAW_BALANCE.

(* --------------------------------------------------------------------- *)
(* One-shot contraction: standard pointwise forced NSE pairing + a       *)
(* critical-mass primitive + the already existing pointwise M7 data give *)
(* the post-M7 forced critical balance consumed downstream.              *)
(* --------------------------------------------------------------------- *)

Section ONE_SHOT_POINTWISE_TO_POST_M7.

Variable Time : Type.
Variable accumulate_until : Time -> (Time -> R) -> R.
Variable nu sigma initial_mass : R.
Variable critical_mass mass_derivative : Time -> R.
Variable dt_pair viscous_pair nonlinear_pair forcing_pair : Time -> R.
Variable instantaneous_dissipation instantaneous_action : Time -> R.
Variable instantaneous_safe instantaneous_resistant instantaneous_force : Time -> R.

Definition pi_bridge_dissipation (t : Time) : R :=
  accumulate_until t instantaneous_dissipation.

Definition pi_bridge_internal_cost (t : Time) : R :=
  accumulate_until t
    (fun s => instantaneous_action s /
      CE.effective_viscosity nu sigma).

Definition pi_bridge_force_work (t : Time) : R :=
  accumulate_until t instantaneous_force.

Theorem PI20_POINTWISE_FORCED_NSE_PLUS_M7_GIVES_POST_M7_BALANCE :
  @AB.PositiveLinearAccumulator Time accumulate_until ->
  0 < nu ->
  0 <= sigma -> sigma < 1 ->
  0 <= initial_mass ->
  (forall t : Time, 0 <= critical_mass t) ->
  (forall t : Time, 0 <= instantaneous_dissipation t) ->
  @CriticalMassPrimitive
    Time accumulate_until initial_mass
    critical_mass mass_derivative ->
  @ForcedNSECriticalPairingData
    Time nu mass_derivative
    dt_pair viscous_pair nonlinear_pair forcing_pair
    instantaneous_dissipation instantaneous_safe
    instantaneous_resistant instantaneous_force ->
  @CBB.PointwiseM7SafeResistantData
    Time nu sigma
    instantaneous_dissipation instantaneous_action
    instantaneous_safe instantaneous_resistant ->
  @FA.PostM7ForcedCriticalBalance
    Time nu sigma initial_mass
    critical_mass pi_bridge_dissipation
    pi_bridge_internal_cost pi_bridge_force_work.
Proof.
  intros Hacc Hnu Hs0 Hs1 Hinit Hmass Hdiss Hprim Hpair Hm7.
  assert (Hpoint :
    @PointwiseForcedCriticalIdentity
      Time nu mass_derivative
      instantaneous_dissipation instantaneous_safe
      instantaneous_resistant instantaneous_force).
  {
    intro t.
    exact
      (@PI00_FORCED_NSE_PAIRING_GIVES_POINTWISE_CRITICAL_IDENTITY
        Time nu mass_derivative
        dt_pair viscous_pair nonlinear_pair forcing_pair
        instantaneous_dissipation instantaneous_safe
        instantaneous_resistant instantaneous_force
        Hpair t).
  }
  assert (Hraw :
    @CBB.ForcedCriticalPreM7Balance
      Time nu sigma initial_mass
      critical_mass pi_bridge_dissipation
      (fun t => accumulate_until t instantaneous_safe)
      (fun t => accumulate_until t instantaneous_resistant)
      pi_bridge_force_work).
  {
    exact
      (@PI10_POINTWISE_IDENTITY_ACCUMULATES_TO_RAW_FORCED_BALANCE
        Time accumulate_until nu sigma initial_mass
        critical_mass mass_derivative
        instantaneous_dissipation instantaneous_safe
        instantaneous_resistant instantaneous_force
        Hacc Hnu Hs0 Hs1 Hinit Hmass Hdiss Hprim Hpoint).
  }
  exact
    (@CBB.CBB30_RAW_FORCED_IDENTITY_PLUS_POINTWISE_M7_GIVES_POST_M7_BALANCE
      Time accumulate_until nu sigma initial_mass
      critical_mass instantaneous_dissipation instantaneous_action
      instantaneous_safe instantaneous_resistant
      pi_bridge_force_work
      Hacc Hraw Hm7).
Qed.

End ONE_SHOT_POINTWISE_TO_POST_M7.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_POINTWISE_IDENTITY_V0_17_2"%string.

End NSE_R3_FORCED_GP_DIAMOND_POINTWISE_IDENTITY.

Check NSE_R3_FORCED_GP_DIAMOND_POINTWISE_IDENTITY.PI00_FORCED_NSE_PAIRING_GIVES_POINTWISE_CRITICAL_IDENTITY.
Check NSE_R3_FORCED_GP_DIAMOND_POINTWISE_IDENTITY.PI10_POINTWISE_IDENTITY_ACCUMULATES_TO_RAW_FORCED_BALANCE.
Check NSE_R3_FORCED_GP_DIAMOND_POINTWISE_IDENTITY.PI20_POINTWISE_FORCED_NSE_PLUS_M7_GIVES_POST_M7_BALANCE.
