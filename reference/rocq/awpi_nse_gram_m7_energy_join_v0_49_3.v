From Stdlib Require Import Reals Lra Psatz Field Lia String.
Require Import awpi_nse_schur_action_ledger_v0_49_3.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_GRAM_M7_ENERGY_JOIN.
Import NSE_SCHUR_ACTION_LEDGER.
Module GM := NSE_GP_TO_M7_SPINE.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

(* IMPORTANT: actual masses must be supplied by physical ownership.
   No artificial one-term/geometric sequence is manufactured from the bound.
   This direction bounds the genealogy BY the physical action, not conversely. *)
Definition ActualMassPrefixDominated (Point : Type) (mass : nat -> R)
  (action : Point -> R) : Prop :=
  (forall n : nat, 0 <= mass n) /\
  forall N : nat, exists p : Point, GM.resistant_prefix mass N <= action p.

Theorem NSGE10_CAPACITY_AND_OWNERSHIP_GIVE_EXISTING_M7 :
  forall Point Y Vend Q Z net V L c Z0 mass,
  IntegratedGramLedger Point Y Vend Q Z net V L ->
  ReducedCapacityBound Point Y Z c Z0 ->
  ActualMassPrefixDominated Point mass Y -> GM.GPSequenceM7 mass.
Proof.
  intros Point Y Vend Q Z net V L c Z0 mass Hledger Hcap [Hmass Hown].
  exists (action_bound V L c Z0); split.
  - destruct Hledger as [HV HL HY HP HQ HZ HB Hbal HG].
    destruct Hcap as [Hc [HZ0 HC]].
    apply action_bound_nonneg; assumption.
  - intro N; destruct (Hown N) as [p Hp].
    eapply Rle_trans; [exact Hp |].
    exact (NSAR20_UNIFORM_REDUCED_CAPACITY_TO_ACTION
      Point Y Vend Q Z net V L c Z0 Hledger Hcap p).
Qed.

(* Direct attachment to the supplied NSCE10 interface.  rho is the known
   physical normalization, for example rho=1/effective_viscosity. *)
Theorem NSGE20_CAPACITY_TO_UNIFORM_CRITICAL_ENERGY :
  forall Point Y Vend Q Z net V L c Z0 rho nu sigma initial_mass
    (critical_mass critical_dissipation action_cost : Point -> R),
  IntegratedGramLedger Point Y Vend Q Z net V L ->
  ReducedCapacityBound Point Y Z c Z0 ->
  0 <= rho ->
  (forall p, action_cost p <= rho*Y p) ->
  CE.CriticalEnergyBalance Point nu sigma initial_mass
    critical_mass critical_dissipation action_cost ->
  CE.UniformCriticalEnergy Point critical_mass critical_dissipation.
Proof.
  intros Point Y Vend Q Z net V L c Z0 rho nu sigma initial_mass
    critical_mass critical_dissipation action_cost Hledger Hcap Hrho Hscale Hbalance.
  assert (Hbound : forall p, Y p <= action_bound V L c Z0).
  { exact (NSAR20_UNIFORM_REDUCED_CAPACITY_TO_ACTION
      Point Y Vend Q Z net V L c Z0 Hledger Hcap). }
  assert (HA : 0 <= action_bound V L c Z0).
  { destruct Hledger as [HV HL HY HP HQ HZ HB Hbal HG].
    destruct Hcap as [Hc [HZ0 HC]].
    apply action_bound_nonneg; assumption. }
  apply (CE.NSCE10_ACTION_COST_BOUND_GIVES_CRITICAL_ENERGY
    Point nu sigma initial_mass (rho*action_bound V L c Z0)
    critical_mass critical_dissipation action_cost Hbalance).
  - apply Rmult_le_pos; assumption.
  - intro p.
    eapply Rle_trans; [apply Hscale |].
    apply Rmult_le_compat_l; [exact Hrho | apply Hbound].
Qed.

(* Legacy M7 attachment: both ownership directions have distinct meanings.
   Hown: finite genealogy prefix <= some actual accumulated action.
   Hreal: physical normalized energy cost <= some genealogy prefix.
   They cannot be exchanged or silently identified. *)
Theorem NSGE30_GRAM_TO_M7_TO_CRITICAL_ENERGY :
  forall Point Y Vend Q Z net V L c Z0 mass nu sigma initial_mass
    (critical_mass critical_dissipation action_cost : Point -> R),
  IntegratedGramLedger Point Y Vend Q Z net V L ->
  ReducedCapacityBound Point Y Z c Z0 ->
  ActualMassPrefixDominated Point mass Y ->
  CE.M7ActionCostRealization Point mass action_cost ->
  CE.CriticalEnergyBalance Point nu sigma initial_mass
    critical_mass critical_dissipation action_cost ->
  CE.UniformCriticalEnergy Point critical_mass critical_dissipation.
Proof.
  intros Point Y Vend Q Z net V L c Z0 mass nu sigma initial_mass
    critical_mass critical_dissipation action_cost Hledger Hcap Hown Hreal Hbalance.
  apply (CE.NSCE30_M7_PLUS_BALANCE_GIVES_CRITICAL_ENERGY
    Point mass nu sigma initial_mass critical_mass critical_dissipation action_cost).
  - exact (NSGE10_CAPACITY_AND_OWNERSHIP_GIVE_EXISTING_M7
      Point Y Vend Q Z net V L c Z0 mass Hledger Hcap Hown).
  - exact Hreal.
  - exact Hbalance.
Qed.

Theorem NSGE90_GP_KQ_GRAM_M7_CRITICAL_TARGET :
  forall Point Y Vend Q Z net V L c Z0 mass nu sigma initial_mass
    (critical_mass critical_dissipation action_cost : Point -> R),
  IntegratedGramLedger Point Y Vend Q Z net V L ->
  ReducedCapacityBound Point Y Z c Z0 ->
  ActualMassPrefixDominated Point mass Y ->
  CE.M7ActionCostRealization Point mass action_cost ->
  CE.CriticalEnergyBalance Point nu sigma initial_mass
    critical_mass critical_dissipation action_cost ->
  CE.CriticalH12Bound Point critical_mass /\
  CE.CriticalH32Dissipation Point critical_dissipation.
Proof.
  intros Point Y Vend Q Z net V L c Z0 mass nu sigma initial_mass
    critical_mass critical_dissipation action_cost Hledger Hcap Hown Hreal Hbalance.
  apply CE.NSCE40_UNIFORM_CRITICAL_ENERGY_SPLITS_TO_H12_H32.
  exact (NSGE30_GRAM_TO_M7_TO_CRITICAL_ENERGY
    Point Y Vend Q Z net V L c Z0 mass nu sigma initial_mass
    critical_mass critical_dissipation action_cost Hledger Hcap Hown Hreal Hbalance).
Qed.

Definition STATUS : string :=
  "NSE_GP_KQ_GRAM_RENEWAL_V0_49_3_FINITE_ALGEBRA_CONDITIONAL_ENERGY_JOIN"%string.

End NSE_GRAM_M7_ENERGY_JOIN.
