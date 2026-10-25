From Stdlib Require Import Reals Lra Psatz String FunctionalExtensionality.
Require Import NSE_R3_FORCED_GP_DIAMOND_POINTWISE_IDENTITY.
Require Import NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.
Require Import NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.
Require Import NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_R3_FORCED_GP_DIAMOND_CANONICAL_PAIRING.

Module PI := NSE_R3_FORCED_GP_DIAMOND_POINTWISE_IDENTITY.NSE_R3_FORCED_GP_DIAMOND_POINTWISE_IDENTITY.
Module CBB := NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.
Module AB := NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.
Module FA := NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.

Open Scope R_scope.

(* Canonical definitions: the mass derivative, dissipation and force current are
   read directly from the critical test pairing. *)
Definition canonical_mass_derivative
  (Time : Type) (dt_pair : Time -> R) (t : Time) : R :=
  2 * dt_pair t.

Definition canonical_dissipation
  (Time : Type) (viscous_pair : Time -> R) (t : Time) : R :=
  viscous_pair t.

Definition canonical_force_current
  (Time : Type) (forcing_pair : Time -> R) (t : Time) : R :=
  forcing_pair t.

Definition ForcedCriticalOperatorPairing
  (Time : Type) (nu : R)
  (dt_pair viscous_pair nonlinear_pair forcing_pair : Time -> R) : Prop :=
  forall t : Time,
    dt_pair t + nu * viscous_pair t + nonlinear_pair t = forcing_pair t.

Definition CriticalNonlinearSplit
  (Time : Type)
  (nonlinear_pair instantaneous_safe instantaneous_resistant : Time -> R) : Prop :=
  forall t : Time,
    nonlinear_pair t = - (instantaneous_safe t + instantaneous_resistant t).

Theorem CP00_OPERATOR_PAIRING_PLUS_SPLIT_GIVES_POINTWISE_PAIRING_DATA :
  forall (Time : Type) (nu : R)
         (dt_pair viscous_pair nonlinear_pair forcing_pair : Time -> R)
         (instantaneous_safe instantaneous_resistant : Time -> R),
    ForcedCriticalOperatorPairing
      Time nu dt_pair viscous_pair nonlinear_pair forcing_pair ->
    CriticalNonlinearSplit
      Time nonlinear_pair instantaneous_safe instantaneous_resistant ->
    @PI.ForcedNSECriticalPairingData
      Time nu
      (canonical_mass_derivative Time dt_pair)
      dt_pair viscous_pair nonlinear_pair forcing_pair
      (canonical_dissipation Time viscous_pair)
      instantaneous_safe instantaneous_resistant
      (canonical_force_current Time forcing_pair).
Proof.
  intros Time nu dt_pair viscous_pair nonlinear_pair forcing_pair
         instantaneous_safe instantaneous_resistant Hnse Hsplit.
  constructor.
  - intro t. unfold canonical_mass_derivative. reflexivity.
  - intro t. unfold canonical_dissipation. reflexivity.
  - exact Hsplit.
  - intro t. unfold canonical_force_current. reflexivity.
  - exact Hnse.
Qed.

(* The critical-mass primitive is made canonical rather than assumed. *)
Definition canonical_critical_mass
  (Time : Type)
  (accumulate_until : Time -> (Time -> R) -> R)
  (initial_mass : R)
  (mass_derivative : Time -> R)
  (t : Time) : R :=
  initial_mass + accumulate_until t mass_derivative.

Theorem CP10_CANONICAL_CRITICAL_MASS_IS_A_PRIMITIVE :
  forall (Time : Type)
         (accumulate_until : Time -> (Time -> R) -> R)
         (initial_mass : R)
         (mass_derivative : Time -> R),
    @PI.CriticalMassPrimitive
      Time accumulate_until initial_mass
      (canonical_critical_mass Time accumulate_until initial_mass mass_derivative)
      mass_derivative.
Proof.
  intros Time accumulate_until initial_mass mass_derivative.
  constructor.
  intro t.
  unfold canonical_critical_mass.
  reflexivity.
Qed.

(* One-shot canonical contraction.  The standard analytic input is now only
   the actual forced critical-test identity.  The nonlinear split and M7
   coercivity remain on the M7 side. *)
Theorem CP20_CANONICAL_FORCED_PAIRING_PLUS_M7_GIVES_POST_M7_BALANCE :
  forall (Time : Type)
         (accumulate_until : Time -> (Time -> R) -> R)
         (nu sigma initial_mass : R)
         (dt_pair viscous_pair nonlinear_pair forcing_pair : Time -> R)
         (instantaneous_action instantaneous_safe instantaneous_resistant : Time -> R),
    @AB.PositiveLinearAccumulator Time accumulate_until ->
    0 < nu ->
    0 <= sigma -> sigma < 1 ->
    0 <= initial_mass ->
    (forall t : Time,
      0 <= canonical_critical_mass
        Time accumulate_until initial_mass
        (canonical_mass_derivative Time dt_pair) t) ->
    ForcedCriticalOperatorPairing
      Time nu dt_pair viscous_pair nonlinear_pair forcing_pair ->
    CriticalNonlinearSplit
      Time nonlinear_pair instantaneous_safe instantaneous_resistant ->
    @CBB.PointwiseM7SafeResistantData
      Time nu sigma
      (canonical_dissipation Time viscous_pair)
      instantaneous_action instantaneous_safe instantaneous_resistant ->
    @FA.PostM7ForcedCriticalBalance
      Time nu sigma initial_mass
      (canonical_critical_mass
        Time accumulate_until initial_mass
        (canonical_mass_derivative Time dt_pair))
      (fun t => accumulate_until t (canonical_dissipation Time viscous_pair))
      (fun t => accumulate_until t
        (fun s => instantaneous_action s / CE.effective_viscosity nu sigma))
      (fun t => accumulate_until t (canonical_force_current Time forcing_pair)).
Proof.
  intros Time accumulate_until nu sigma initial_mass
         dt_pair viscous_pair nonlinear_pair forcing_pair
         instantaneous_action instantaneous_safe instantaneous_resistant
         Hacc Hnu Hs0 Hs1 Hinit Hmass Hnse Hsplit Hm7.
  pose proof Hm7 as Hm7bounds.
  destruct Hm7bounds as [Hdiss Hact Hsafe0 Hres0 Hsafe Hquad].
  assert (Hpair :
    @PI.ForcedNSECriticalPairingData
      Time nu
      (canonical_mass_derivative Time dt_pair)
      dt_pair viscous_pair nonlinear_pair forcing_pair
      (canonical_dissipation Time viscous_pair)
      instantaneous_safe instantaneous_resistant
      (canonical_force_current Time forcing_pair)).
  {
    exact
      (CP00_OPERATOR_PAIRING_PLUS_SPLIT_GIVES_POINTWISE_PAIRING_DATA
        Time nu dt_pair viscous_pair nonlinear_pair forcing_pair
        instantaneous_safe instantaneous_resistant Hnse Hsplit).
  }
  assert (Hprim :
    @PI.CriticalMassPrimitive
      Time accumulate_until initial_mass
      (canonical_critical_mass Time accumulate_until initial_mass
        (canonical_mass_derivative Time dt_pair))
      (canonical_mass_derivative Time dt_pair)).
  {
    exact
      (CP10_CANONICAL_CRITICAL_MASS_IS_A_PRIMITIVE
        Time accumulate_until initial_mass
        (canonical_mass_derivative Time dt_pair)).
  }
  exact
    (@PI.PI20_POINTWISE_FORCED_NSE_PLUS_M7_GIVES_POST_M7_BALANCE
      Time accumulate_until nu sigma initial_mass
      (canonical_critical_mass Time accumulate_until initial_mass
        (canonical_mass_derivative Time dt_pair))
      (canonical_mass_derivative Time dt_pair)
      dt_pair viscous_pair nonlinear_pair forcing_pair
      (canonical_dissipation Time viscous_pair)
      instantaneous_action instantaneous_safe instantaneous_resistant
      (canonical_force_current Time forcing_pair)
      Hacc Hnu Hs0 Hs1 Hinit Hmass Hdiss Hprim Hpair Hm7).
Qed.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_CANONICAL_PAIRING_V0_18_0"%string.

End NSE_R3_FORCED_GP_DIAMOND_CANONICAL_PAIRING.

Check NSE_R3_FORCED_GP_DIAMOND_CANONICAL_PAIRING.CP00_OPERATOR_PAIRING_PLUS_SPLIT_GIVES_POINTWISE_PAIRING_DATA.
Check NSE_R3_FORCED_GP_DIAMOND_CANONICAL_PAIRING.CP10_CANONICAL_CRITICAL_MASS_IS_A_PRIMITIVE.
Check NSE_R3_FORCED_GP_DIAMOND_CANONICAL_PAIRING.CP20_CANONICAL_FORCED_PAIRING_PLUS_M7_GIVES_POST_M7_BALANCE.
