From Stdlib Require Import Reals Lra Psatz String FunctionalExtensionality.
Require Import NSE_R3_FORCED_GP_DIAMOND_CANONICAL_PAIRING.
Require Import NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.
Require Import NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.
Require Import NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_R3_FORCED_GP_DIAMOND_OPERATOR_TEST.

Module CP := NSE_R3_FORCED_GP_DIAMOND_CANONICAL_PAIRING.NSE_R3_FORCED_GP_DIAMOND_CANONICAL_PAIRING.
Module AB := NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.
Module CBB := NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.
Module FA := NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.

Open Scope R_scope.

(* Minimal algebra needed to pair an operator identity with a critical test vector. *)
Record CriticalPairingAlgebra
  (Vec : Type)
  (vadd : Vec -> Vec -> Vec)
  (smul : R -> Vec -> Vec)
  (inner : Vec -> Vec -> R) : Prop := {
  cpa_inner_add_l : forall x y z : Vec,
    inner (vadd x y) z = inner x z + inner y z;
  cpa_inner_smul_l : forall (a : R) (x z : Vec),
    inner (smul a x) z = a * inner x z
}.

Definition ForcedNSEOperatorEquation
  (Time Vec : Type)
  (vadd : Vec -> Vec -> Vec)
  (smul : R -> Vec -> Vec)
  (nu : R)
  (dt_state viscous_state nonlinear_state forcing_state : Time -> Vec) : Prop :=
  forall t : Time,
    vadd (dt_state t)
      (vadd (smul nu (viscous_state t)) (nonlinear_state t))
    = forcing_state t.

Definition paired_dt
  (Time Vec : Type) (inner : Vec -> Vec -> R)
  (dt_state test_state : Time -> Vec) (t : Time) : R :=
  inner (dt_state t) (test_state t).

Definition paired_viscous
  (Time Vec : Type) (inner : Vec -> Vec -> R)
  (viscous_state test_state : Time -> Vec) (t : Time) : R :=
  inner (viscous_state t) (test_state t).

Definition paired_nonlinear
  (Time Vec : Type) (inner : Vec -> Vec -> R)
  (nonlinear_state test_state : Time -> Vec) (t : Time) : R :=
  inner (nonlinear_state t) (test_state t).

Definition paired_forcing
  (Time Vec : Type) (inner : Vec -> Vec -> R)
  (forcing_state test_state : Time -> Vec) (t : Time) : R :=
  inner (forcing_state t) (test_state t).

Theorem OT00_OPERATOR_EQUALITY_GIVES_FORCED_CRITICAL_PAIRING :
  forall (Time Vec : Type)
         (vadd : Vec -> Vec -> Vec)
         (smul : R -> Vec -> Vec)
         (inner : Vec -> Vec -> R)
         (nu : R)
         (dt_state viscous_state nonlinear_state forcing_state test_state : Time -> Vec),
    CriticalPairingAlgebra Vec vadd smul inner ->
    ForcedNSEOperatorEquation
      Time Vec vadd smul nu
      dt_state viscous_state nonlinear_state forcing_state ->
    CP.ForcedCriticalOperatorPairing
      Time nu
      (paired_dt Time Vec inner dt_state test_state)
      (paired_viscous Time Vec inner viscous_state test_state)
      (paired_nonlinear Time Vec inner nonlinear_state test_state)
      (paired_forcing Time Vec inner forcing_state test_state).
Proof.
  intros Time Vec vadd smul inner nu
         dt_state viscous_state nonlinear_state forcing_state test_state
         Halg Hop t.
  destruct Halg as [Hadd Hsmul].
  specialize (Hop t).
  pose proof (f_equal (fun z : Vec => inner z (test_state t)) Hop) as Hpair.
  change
    (inner
      (vadd (dt_state t)
        (vadd (smul nu (viscous_state t)) (nonlinear_state t)))
      (test_state t)
     = inner (forcing_state t) (test_state t)) in Hpair.
  rewrite (Hadd
    (dt_state t)
    (vadd (smul nu (viscous_state t)) (nonlinear_state t))
    (test_state t)) in Hpair.
  rewrite (Hadd
    (smul nu (viscous_state t))
    (nonlinear_state t)
    (test_state t)) in Hpair.
  rewrite (Hsmul nu (viscous_state t) (test_state t)) in Hpair.
  unfold paired_dt, paired_viscous, paired_nonlinear, paired_forcing.
  lra.
Qed.

(* The physical critical mass is a norm-square readout.  The only analytic
   content needed to identify CP's canonical primitive with that physical mass
   is the usual critical-space chain rule / fundamental theorem. *)
Record NormSquareStructure
  (Vec : Type) (norm_sq : Vec -> R) : Prop := {
  nss_nonnegative : forall x : Vec, 0 <= norm_sq x
}.

Definition CriticalMassChainRule
  (Time Vec : Type)
  (accumulate_until : Time -> (Time -> R) -> R)
  (initial_mass : R)
  (mass_derivative : Time -> R)
  (critical_state : Time -> Vec)
  (norm_sq : Vec -> R) : Prop :=
  forall t : Time,
    CP.canonical_critical_mass
      Time accumulate_until initial_mass mass_derivative t
    = norm_sq (critical_state t).

Theorem OT10_CHAIN_RULE_PLUS_NORM_SQUARE_GIVES_CANONICAL_MASS_NONNEG :
  forall (Time Vec : Type)
         (accumulate_until : Time -> (Time -> R) -> R)
         (initial_mass : R)
         (mass_derivative : Time -> R)
         (critical_state : Time -> Vec)
         (norm_sq : Vec -> R),
    NormSquareStructure Vec norm_sq ->
    CriticalMassChainRule
      Time Vec accumulate_until initial_mass mass_derivative
      critical_state norm_sq ->
    forall t : Time,
      0 <= CP.canonical_critical_mass
        Time accumulate_until initial_mass mass_derivative t.
Proof.
  intros Time Vec accumulate_until initial_mass mass_derivative
         critical_state norm_sq Hnorm Hchain t.
  destruct Hnorm as [Hnonneg].
  rewrite (Hchain t).
  apply Hnonneg.
Qed.

(* One-shot operator-level contraction.  The scalar pairing record is no longer
   an interface: it is derived from the actual operator equality.  Likewise,
   nonnegativity of the canonical mass is derived from the physical norm-square
   readout once the standard critical-space chain rule is available. *)
Theorem OT20_OPERATOR_NSE_PLUS_CHAIN_RULE_PLUS_M7_GIVES_POST_M7_BALANCE :
  forall (Time Vec : Type)
         (vadd : Vec -> Vec -> Vec)
         (smul : R -> Vec -> Vec)
         (inner : Vec -> Vec -> R)
         (norm_sq : Vec -> R)
         (accumulate_until : Time -> (Time -> R) -> R)
         (nu sigma initial_mass : R)
         (dt_state viscous_state nonlinear_state forcing_state test_state critical_state : Time -> Vec)
         (instantaneous_action instantaneous_safe instantaneous_resistant : Time -> R),
    @AB.PositiveLinearAccumulator Time accumulate_until ->
    CriticalPairingAlgebra Vec vadd smul inner ->
    NormSquareStructure Vec norm_sq ->
    0 < nu ->
    0 <= sigma -> sigma < 1 ->
    0 <= initial_mass ->
    ForcedNSEOperatorEquation
      Time Vec vadd smul nu
      dt_state viscous_state nonlinear_state forcing_state ->
    CP.CriticalNonlinearSplit
      Time
      (paired_nonlinear Time Vec inner nonlinear_state test_state)
      instantaneous_safe instantaneous_resistant ->
    CriticalMassChainRule
      Time Vec accumulate_until initial_mass
      (CP.canonical_mass_derivative Time
        (paired_dt Time Vec inner dt_state test_state))
      critical_state norm_sq ->
    @CBB.PointwiseM7SafeResistantData
      Time nu sigma
      (CP.canonical_dissipation Time
        (paired_viscous Time Vec inner viscous_state test_state))
      instantaneous_action instantaneous_safe instantaneous_resistant ->
    @FA.PostM7ForcedCriticalBalance
      Time nu sigma initial_mass
      (CP.canonical_critical_mass
        Time accumulate_until initial_mass
        (CP.canonical_mass_derivative Time
          (paired_dt Time Vec inner dt_state test_state)))
      (fun t => accumulate_until t
        (CP.canonical_dissipation Time
          (paired_viscous Time Vec inner viscous_state test_state)))
      (fun t => accumulate_until t
        (fun s => instantaneous_action s /
          NSE_M7_CRITICAL_ENERGY_INJECTION.effective_viscosity nu sigma))
      (fun t => accumulate_until t
        (CP.canonical_force_current Time
          (paired_forcing Time Vec inner forcing_state test_state))).
Proof.
  intros Time Vec vadd smul inner norm_sq accumulate_until
         nu sigma initial_mass
         dt_state viscous_state nonlinear_state forcing_state test_state critical_state
         instantaneous_action instantaneous_safe instantaneous_resistant
         Hacc Halg Hnorm Hnu Hs0 Hs1 Hinit Hop Hsplit Hchain Hm7.
  assert (Hpair :
    CP.ForcedCriticalOperatorPairing
      Time nu
      (paired_dt Time Vec inner dt_state test_state)
      (paired_viscous Time Vec inner viscous_state test_state)
      (paired_nonlinear Time Vec inner nonlinear_state test_state)
      (paired_forcing Time Vec inner forcing_state test_state)).
  {
    exact
      (OT00_OPERATOR_EQUALITY_GIVES_FORCED_CRITICAL_PAIRING
        Time Vec vadd smul inner nu
        dt_state viscous_state nonlinear_state forcing_state test_state
        Halg Hop).
  }
  assert (Hmass : forall t : Time,
    0 <= CP.canonical_critical_mass
      Time accumulate_until initial_mass
      (CP.canonical_mass_derivative Time
        (paired_dt Time Vec inner dt_state test_state)) t).
  {
    exact
      (OT10_CHAIN_RULE_PLUS_NORM_SQUARE_GIVES_CANONICAL_MASS_NONNEG
        Time Vec accumulate_until initial_mass
        (CP.canonical_mass_derivative Time
          (paired_dt Time Vec inner dt_state test_state))
        critical_state norm_sq Hnorm Hchain).
  }
  exact
    (@CP.CP20_CANONICAL_FORCED_PAIRING_PLUS_M7_GIVES_POST_M7_BALANCE
      Time accumulate_until nu sigma initial_mass
      (paired_dt Time Vec inner dt_state test_state)
      (paired_viscous Time Vec inner viscous_state test_state)
      (paired_nonlinear Time Vec inner nonlinear_state test_state)
      (paired_forcing Time Vec inner forcing_state test_state)
      instantaneous_action instantaneous_safe instantaneous_resistant
      Hacc Hnu Hs0 Hs1 Hinit Hmass Hpair Hsplit Hm7).
Qed.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_OPERATOR_TEST_V0_19_1"%string.

End NSE_R3_FORCED_GP_DIAMOND_OPERATOR_TEST.

Check NSE_R3_FORCED_GP_DIAMOND_OPERATOR_TEST.OT00_OPERATOR_EQUALITY_GIVES_FORCED_CRITICAL_PAIRING.
Check NSE_R3_FORCED_GP_DIAMOND_OPERATOR_TEST.OT10_CHAIN_RULE_PLUS_NORM_SQUARE_GIVES_CANONICAL_MASS_NONNEG.
Check NSE_R3_FORCED_GP_DIAMOND_OPERATOR_TEST.OT20_OPERATOR_NSE_PLUS_CHAIN_RULE_PLUS_M7_GIVES_POST_M7_BALANCE.
