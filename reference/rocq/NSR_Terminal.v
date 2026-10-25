From Stdlib Require Import Reals Lra Psatz Field Lia.
Require Import NSH_ChainInterface NSR_ActionCritical NSR_CriticalInterpolation.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.
Require Import awpi_nse_gram_m7_energy_join_v0_49_3.

Module NSE_SERRIN_BACK_TERMINAL.
Import NSE_SHARED_CHAIN_INTERFACE NSE_ACTION_CRITICAL_BACK_ANCHOR.
Import NSE_CRITICAL_SERRIN_INTERPOLATION.
Module Energy := NSE_M7_CRITICAL_ENERGY_INJECTION.
Module M7 := NSE_GP_TO_M7_SPINE.
Module Owned := NSE_GRAM_M7_ENERGY_JOIN.
Open Scope R_scope.

(* Explicit analytic exit, not a proof of the Prodi--Serrin theorem.
   ActualSerrin46 and Continues are supplied for the SAME solution u.
   The identification must pass through the real norm integrals / cut limit,
   not equate an arbitrary scalar observable with a PDE function class. *)
Record SerrinExitContract (Solution Point : Type) (u : Solution)
  (observable : Point -> R)
  (ActualSerrin46 Continues : Solution -> Prop) : Prop := {
  serrin_actual_norm_and_limit_identification :
    UniformAction Point observable -> ActualSerrin46 u;
  serrin_continuation_principle :
    forall v : Solution, ActualSerrin46 v -> Continues v
}.

Theorem NSR80_OBSERVABLE_AND_EXPLICIT_SERRIN_EXIT :
  forall Solution Point u observable ActualSerrin46 Continues,
  SerrinExitContract Solution Point u observable ActualSerrin46 Continues ->
  UniformAction Point observable -> ActualSerrin46 u /\ Continues u.
Proof.
  intros Solution Point u observable ActualSerrin46 Continues [Hid Hprinciple] HB.
  pose proof (Hid HB) as HS; split; [exact HS|exact (Hprinciple u HS)].
Qed.

Theorem NSR90_SHARED_LEDGER_TO_CRITICAL_AND_SERRIN_OBSERVABLE :
  forall Point Y W Q Z net V0 Q0 c Z0 rho nu sigma initial mass diss cost D Csq,
  SharedGramLedger Point Y W Q Z net V0 Q0 ->
  SharedCapacityEstimate Point Y Z c Z0 ->
  0<=rho -> (forall p, cost p<=rho*Y p) ->
  Energy.CriticalEnergyBalance Point nu sigma initial mass diss cost ->
  CriticalNormBinding Point D mass diss Csq ->
  Energy.UniformCriticalEnergy Point mass diss /\
  UniformAction Point (fun p=>serrin46_observation (D p)).
Proof.
  intros Point Y W Q Z net V0 Q0 c Z0 rho nu sigma initial mass diss cost D Csq
    HG HC Hr Hscale Hbalance Hnorm.
  pose proof (NSR11_SHARED_GRAM_INTERFACE_TO_CRITICAL_ENERGY
    Point Y W Q Z net V0 Q0 c Z0 rho nu sigma initial mass diss cost
    HG HC Hr Hscale Hbalance) as HE.
  split; [exact HE|].
  exact (NSR23_CRITICAL_ENERGY_TO_UNIFORM_SERRIN46_OBSERVABLE
    Point D mass diss Csq Hnorm HE).
Qed.

Theorem NSR91_OWNED_M7_CHAIN_TO_SERRIN_OBSERVABLE :
  forall Point Y W Q Z net V0 Q0 c Z0 resistant nu sigma initial mass diss cost D Csq,
  SharedGramLedger Point Y W Q Z net V0 Q0 ->
  SharedCapacityEstimate Point Y Z c Z0 ->
  Owned.ActualMassPrefixDominated Point resistant Y ->
  Energy.M7ActionCostRealization Point resistant cost ->
  Energy.CriticalEnergyBalance Point nu sigma initial mass diss cost ->
  CriticalNormBinding Point D mass diss Csq ->
  M7.GPSequenceM7 resistant /\
  Energy.UniformCriticalEnergy Point mass diss /\
  UniformAction Point (fun p=>serrin46_observation (D p)).
Proof.
  intros Point Y W Q Z net V0 Q0 c Z0 resistant nu sigma initial mass diss cost D Csq
    HG HC Hown Hreal Hbalance Hnorm.
  destruct (NSR13_SHARED_LEDGER_TO_OWNED_M7_AND_CRITICAL_ENERGY
    Point Y W Q Z net V0 Q0 c Z0 resistant nu sigma initial mass diss cost
    HG HC Hown Hreal Hbalance) as [HM7 HE].
  split; [exact HM7|].
  split; [exact HE|].
  exact (NSR23_CRITICAL_ENERGY_TO_UNIFORM_SERRIN46_OBSERVABLE
    Point D mass diss Csq Hnorm HE).
Qed.

Theorem NSR92_PHYSICAL_509_RENEWAL_TO_SERRIN_OBSERVABLE :
  forall Point resistant paid nu sigma initial mass diss cost D Csq,
  M7.GP509RenewalCertificate resistant paid ->
  M7.GPUniformPaidPrefix paid ->
  Energy.M7ActionCostRealization Point resistant cost ->
  Energy.CriticalEnergyBalance Point nu sigma initial mass diss cost ->
  CriticalNormBinding Point D mass diss Csq ->
  M7.GPSequenceM7 resistant /\
  Energy.UniformCriticalEnergy Point mass diss /\
  UniformAction Point (fun p=>serrin46_observation (D p)).
Proof.
  intros Point resistant paid nu sigma initial mass diss cost D Csq
    Hrenew Hpaid Hreal Hbalance Hnorm.
  destruct (NSR12_509_RENEWAL_TO_CRITICAL_ENERGY
    Point resistant paid nu sigma initial mass diss cost Hrenew Hpaid Hreal Hbalance)
    as [HM7 HE].
  split; [exact HM7|].
  split; [exact HE|].
  exact (NSR23_CRITICAL_ENERGY_TO_UNIFORM_SERRIN46_OBSERVABLE
    Point D mass diss Csq Hnorm HE).
Qed.

Theorem NSR99_CONDITIONAL_SHARED_LEDGER_TO_CONTINUATION :
  forall Solution Point (u : Solution) (ActualSerrin46 Continues : Solution -> Prop)
    Y W Q Z net V0 Q0 c Z0 rho nu sigma initial mass diss cost D Csq,
  SharedGramLedger Point Y W Q Z net V0 Q0 ->
  SharedCapacityEstimate Point Y Z c Z0 ->
  0<=rho -> (forall p, cost p<=rho*Y p) ->
  Energy.CriticalEnergyBalance Point nu sigma initial mass diss cost ->
  CriticalNormBinding Point D mass diss Csq ->
  SerrinExitContract Solution Point u
    (fun p=>serrin46_observation (D p)) ActualSerrin46 Continues ->
  ActualSerrin46 u /\ Continues u.
Proof.
  intros Solution Point u ActualSerrin46 Continues
    Y W Q Z net V0 Q0 c Z0 rho nu sigma initial mass diss cost D Csq
    HG HC Hr Hscale Hbalance Hnorm Hexit.
  destruct (NSR90_SHARED_LEDGER_TO_CRITICAL_AND_SERRIN_OBSERVABLE
    Point Y W Q Z net V0 Q0 c Z0 rho nu sigma initial mass diss cost D Csq
    HG HC Hr Hscale Hbalance Hnorm) as [_ HS].
  exact (NSR80_OBSERVABLE_AND_EXPLICIT_SERRIN_EXIT
    Solution Point u (fun p=>serrin46_observation (D p))
    ActualSerrin46 Continues Hexit HS).
Qed.

End NSE_SERRIN_BACK_TERMINAL.
