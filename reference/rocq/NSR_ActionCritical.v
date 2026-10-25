From Stdlib Require Import Reals Lra Psatz Field Lia.
Require Import NSH_ChainInterface.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.
Require Import awpi_nse_gram_m7_energy_join_v0_49_3.

Module NSE_ACTION_CRITICAL_BACK_ANCHOR.
Import NSE_SHARED_CHAIN_INTERFACE.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Module GM := NSE_GP_TO_M7_SPINE.
Module GE := NSE_GRAM_M7_ENERGY_JOIN.
Open Scope R_scope.

Theorem NSR10_SAME_ACTION_BOUND_TO_CRITICAL_ENERGY :
  forall Point (Y cost mass diss : Point -> R) rho nu sigma initial,
  UniformAction Point Y -> 0 <= rho ->
  (forall p, cost p <= rho*Y p) ->
  CE.CriticalEnergyBalance Point nu sigma initial mass diss cost ->
  CE.UniformCriticalEnergy Point mass diss.
Proof.
  intros Point Y cost mass diss rho nu sigma initial
    [B [HB HY]] Hr Hscale Hbalance.
  apply (CE.NSCE10_ACTION_COST_BOUND_GIVES_CRITICAL_ENERGY
    Point nu sigma initial (rho*B) mass diss cost Hbalance).
  - apply Rmult_le_pos; assumption.
  - intro p; eapply Rle_trans; [exact (Hscale p)|].
    apply Rmult_le_compat_l; [exact Hr|exact (HY p)].
Qed.

Theorem NSR11_SHARED_GRAM_INTERFACE_TO_CRITICAL_ENERGY :
  forall Point Y W Q Z net V0 Q0 c Z0 rho nu sigma initial mass diss cost,
  SharedGramLedger Point Y W Q Z net V0 Q0 ->
  SharedCapacityEstimate Point Y Z c Z0 ->
  0 <= rho -> (forall p, cost p<=rho*Y p) ->
  CE.CriticalEnergyBalance Point nu sigma initial mass diss cost ->
  CE.UniformCriticalEnergy Point mass diss.
Proof.
  intros Point Y W Q Z net V0 Q0 c Z0 rho nu sigma initial mass diss cost
    Hledger Hcap Hr Hscale Hbalance.
  apply (NSR10_SAME_ACTION_BOUND_TO_CRITICAL_ENERGY
    Point Y cost mass diss rho nu sigma initial).
  - exact (NSH00_SHARED_CAPACITY_CLOSES_ACTION
      Point Y W Q Z net V0 Q0 c Z0 Hledger Hcap).
  - exact Hr.
  - exact Hscale.
  - exact Hbalance.
Qed.

(* Alternative entrance: actual supplied genealogy, not a sequence fabricated
   from an already known bound.  Its energy action cost is identified by a
   separate, same-physical-cost realization. *)
Theorem NSR12_509_RENEWAL_TO_CRITICAL_ENERGY :
  forall Point resistant paid nu sigma initial mass diss cost,
  GM.GP509RenewalCertificate resistant paid ->
  GM.GPUniformPaidPrefix paid ->
  CE.M7ActionCostRealization Point resistant cost ->
  CE.CriticalEnergyBalance Point nu sigma initial mass diss cost ->
  GM.GPSequenceM7 resistant /\ CE.UniformCriticalEnergy Point mass diss.
Proof.
  intros Point resistant paid nu sigma initial mass diss cost Hren Hpaid Hreal Hbalance.
  pose proof (GM.NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7
    resistant paid Hren Hpaid) as HM7.
  split; [exact HM7|].
  exact (CE.NSCE30_M7_PLUS_BALANCE_GIVES_CRITICAL_ENERGY
    Point resistant nu sigma initial mass diss cost HM7 Hreal Hbalance).
Qed.

(* The two directions of physical ownership are intentionally not exchanged:
   prefix <= actual action derives M7; energy cost <= prefix consumes M7. *)
Theorem NSR13_SHARED_LEDGER_TO_OWNED_M7_AND_CRITICAL_ENERGY :
  forall Point Y W Q Z net V0 Q0 c Z0 resistant nu sigma initial mass diss cost,
  SharedGramLedger Point Y W Q Z net V0 Q0 ->
  SharedCapacityEstimate Point Y Z c Z0 ->
  GE.ActualMassPrefixDominated Point resistant Y ->
  CE.M7ActionCostRealization Point resistant cost ->
  CE.CriticalEnergyBalance Point nu sigma initial mass diss cost ->
  GM.GPSequenceM7 resistant /\ CE.UniformCriticalEnergy Point mass diss.
Proof.
  intros Point Y W Q Z net V0 Q0 c Z0 resistant nu sigma initial mass diss cost
    HG HC Hown Hreal Hbalance.
  pose proof (GE.NSGE10_CAPACITY_AND_OWNERSHIP_GIVE_EXISTING_M7
    Point Y W Q Z net V0 Q0 c Z0 resistant HG HC Hown) as HM7.
  split; [exact HM7|].
  exact (CE.NSCE30_M7_PLUS_BALANCE_GIVES_CRITICAL_ENERGY
    Point resistant nu sigma initial mass diss cost HM7 Hreal Hbalance).
Qed.

End NSE_ACTION_CRITICAL_BACK_ANCHOR.
