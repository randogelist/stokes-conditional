(* Supplied LH entrance -> exact native encoding -> actual-action M7 ->
   countable critical readouts -> a supplied same-solution Serrin exit.
   Analytic realization and payment are explicit sufficient conditions. *)
From Stdlib Require Import Reals Lra Psatz Field.
Require Import LHGP_Hilbert LHGP_Evolution LHGP_Equivalence LHGP_InitialEnergy.
Require Import LHGP_ForwardGradient LHGP_ForwardContainment.
Require Import BKQR_ClassificationAudit BKQR_LHGP_ForwardBridge.
Require Import BKQR_M7_CriticalCalculus BKQR_M7_ActionCells BKQR_M7_LHPayment.
Require Import BKQR_LHGP_M7Injection BKQR_M7_GeneralOperator.
Require Import BKQR_M7_PrefixPayment BKQR_M7_SerrinBridge.
Require Import NSH_ChainInterface NSR_CriticalInterpolation NSR_Terminal.

Module BKQR_LHGP_CONDITIONAL_CONTINUATION.
Module I := BKQR_LHGP_M7_INJECTION.
Module O := BKQR_M7_GENERAL_OPERATOR.
Module M := BKQR_M7_CRITICAL_CALCULUS.
Module A := BKQR_M7_ACTION_CELLS.
Module P := BKQR_M7_LH_PAYMENT.
Module Q := BKQR_M7_PREFIX_PAYMENT.
Module R := BKQR_M7_SERRIN_BRIDGE.
Module C := BKQR_CLASSIFICATION.
Module F := BKQR_LHGP_FORWARD_BRIDGE.
Module S := NSE_CRITICAL_SERRIN_INTERPOLATION.
Module E := NSE_SERRIN_BACK_TERMINAL.
Open Scope R_scope.

Record M7RealizationConditions hd (basis : OrthonormalBasis hd)
    (tests : EvolutionTests hd) T nu lambda
    (mode_test : nat -> ETest hd tests) (u : R -> HCarrier hd)
    (Dcum Ccum : nat -> R -> R) X0 : Prop := {
  realization_modal : O.OperatorModalEquation hd basis tests T nu mode_test u;
  realization_dissipation : forall N, M.OpenPrimitive T
    (M.critical_density lambda (I.same_coordinates hd basis u) N) (Dcum N);
  realization_action : forall N, M.OpenPrimitive T
    (M.normalized_action nu lambda (I.same_coordinates hd basis u)
      (O.effective_source hd basis tests nu lambda mode_test u) N) (Ccum N);
  realization_initial_seed : forall N,
    M.critical_mass lambda (I.same_coordinates hd basis u) N 0 <= X0
}.

Lemma REALIZATION_GIVES_MONOTONE_ACTION :
  forall hd basis tests T nu lambda mode_test u Dcum Ccum X0,
  0 < nu -> (forall i, 0 <= lambda i) ->
  M7RealizationConditions hd basis tests T nu lambda mode_test u Dcum Ccum X0 ->
  A.MonotoneCumulativeAction T Ccum.
Proof.
  intros hd basis tests T nu lambda mode_test u Dcum Ccum X0
    Hnu Hlambda [_ _ HC _].
  constructor.
  - intro N. exact (proj1 (HC N)).
  - intros N s t Hs Hst Ht.
    apply (M.BKMC31_OPEN_PRIMITIVE_MONOTONE T
      (M.normalized_action nu lambda (I.same_coordinates hd basis u)
        (O.effective_source hd basis tests nu lambda mode_test u) N)
      (Ccum N) (HC N)).
    + intros r Hr. apply M.normalized_action_nonnegative; assumption.
    + unfold M.OpenTime; lra.
    + unfold M.OpenTime; lra.
    + exact Hst.
Qed.

Theorem BKC10_COMMON_PAYMENT_INJECTS_SAME_PATH :
  forall q step lambda (Hq : 0 < q < 1) (Hstep : 0 < step),
  (forall i, 0 <= lambda i) ->
  forall hd kd (basis : OrthonormalBasis hd), HComplete hd ->
  forall fg tests td nu T (u : R -> HCarrier hd) u0
    (mode_test : nat -> ETest hd tests) Dcum Ccum X0 Seed Paid,
  HilbertForwardLHModel hd kd fg tests td nu T u u0 ->
  M7RealizationConditions hd basis tests T nu lambda mode_test u Dcum Ccum X0 ->
  A.CommonActionPayment Ccum (A.canonical_cut T) Seed Paid ->
  F.NativeForwardLHModel hd kd basis fg tests td nu T
    (C.bkqr_weights q step lambda Hq Hstep) lambda (C.bkqr_ell q step)
    (fun t => F.HilbertShellEncode hd basis
      (C.bkqr_weights q step lambda Hq Hstep) (u t))
    (F.HilbertShellEncode hd basis (C.bkqr_weights q step lambda Hq Hstep) u0) /\
  I.SamePathM7Injection T nu lambda (I.same_coordinates hd basis u)
    Dcum Ccum X0 Seed Paid.
Proof.
  intros q step lambda Hq Hstep Hlambda hd kd basis Hcomplete
    fg tests td nu T u u0 mode_test Dcum Ccum X0 Seed Paid
    HLH [Hoperator HD HC HX0] Hpayment.
  pose proof (proj1 HLH) as Hnu.
  pose proof (proj1 (proj2 HLH)) as HT.
  split.
  - exact (F.BKLF30_CANONICAL_HILBERT_FORWARD_CONTAINMENT q step lambda
      Hq Hstep Hlambda hd kd basis Hcomplete fg tests td nu T u u0 HLH).
  - apply (I.BKM710_DERIVED_BALANCE_AND_ACTUAL_CELLS_INJECT_M7 T nu lambda
      (I.same_coordinates hd basis u)
      (O.effective_source hd basis tests nu lambda mode_test u)
      Dcum Ccum X0 Seed Paid); try assumption.
    apply O.BKMO10_FULL_OPERATOR_GIVES_REFERENCE_MODAL_EQUATION. exact Hoperator.
Qed.

Theorem BKC20_PREFIX_PAYMENT_INJECTS_SAME_PATH :
  forall q step lambda (Hq : 0 < q < 1) (Hstep : 0 < step),
  (forall i, 0 <= lambda i) ->
  forall hd kd (basis : OrthonormalBasis hd), HComplete hd ->
  forall fg tests td nu T (u : R -> HCarrier hd) u0
    (mode_test : nat -> ETest hd tests) Dcum Ccum X0 Seed Paid theta,
  HilbertForwardLHModel hd kd fg tests td nu T u u0 ->
  M7RealizationConditions hd basis tests T nu lambda mode_test u Dcum Ccum X0 ->
  Q.SubcriticalPrefixPayment (A.actual_action_mass Ccum (A.canonical_cut T))
    Seed Paid theta ->
  F.NativeForwardLHModel hd kd basis fg tests td nu T
    (C.bkqr_weights q step lambda Hq Hstep) lambda (C.bkqr_ell q step)
    (fun t => F.HilbertShellEncode hd basis
      (C.bkqr_weights q step lambda Hq Hstep) (u t))
    (F.HilbertShellEncode hd basis (C.bkqr_weights q step lambda Hq Hstep) u0) /\
  I.SamePathM7Injection T nu lambda (I.same_coordinates hd basis u)
    Dcum Ccum X0 Seed (Paid + theta * Q.prefix_action_budget Seed Paid theta).
Proof.
  intros q step lambda Hq Hstep Hlambda hd kd basis Hcomplete
    fg tests td nu T u u0 mode_test Dcum Ccum X0 Seed Paid theta
    HLH Hreal Hpayment.
  apply (BKC10_COMMON_PAYMENT_INJECTS_SAME_PATH q step lambda Hq Hstep
    Hlambda hd kd basis Hcomplete fg tests td nu T u u0 mode_test
    Dcum Ccum X0 Seed (Paid + theta * Q.prefix_action_budget Seed Paid theta)
    HLH Hreal).
  apply (Q.PREFIX_PAYMENT_CONSTRUCTS_COMMON_ACTION_PAYMENT T Ccum
    (A.canonical_cut T) Seed Paid theta).
  - apply A.CANONICAL_CUTS_ARE_COFINAL. exact (proj1 (proj2 HLH)).
  - exact (REALIZATION_GIVES_MONOTONE_ACTION hd basis tests T nu lambda
      mode_test u Dcum Ccum X0 (proj1 HLH) Hlambda Hreal).
  - exact Hpayment.
Qed.

(* An optional way to establish the prefix condition uses the expenditure
   of the supplied LH path.  Only its initial energy schedule is used.
   There is no derivation of the displayed charge from the LH law alone. *)
Theorem BKC30_SAME_LH_PREFIX_CHARGE_BUILDS_PAYMENT :
  forall hd td nu T (u : R -> HCarrier hd) Dkin GoodD Ccum
    Seed P0 kappa theta,
  0 < T -> 0 <= nu -> IntegralNonnegative td ->
  EnergySchedule0 td nu T (fun t => HNorm hd (u t)) Dkin GoodD ->
  0 <= Seed -> 0 <= P0 -> 0 <= kappa -> 0 <= theta < 96 / 605 ->
  (forall N, A.actual_action_mass Ccum (A.canonical_cut T) N O <= Seed) ->
  (forall N k, Q.GM.paid_prefix
    (A.canonical_action_debt Ccum (A.canonical_cut T) N) k <=
    P0 + kappa * P.leray_expenditure td nu Dkin (A.canonical_cut T k) +
    theta * Q.GM.resistant_prefix
      (A.actual_action_mass Ccum (A.canonical_cut T) N) k) ->
  Q.SubcriticalPrefixPayment (A.actual_action_mass Ccum (A.canonical_cut T))
    Seed (P0 + kappa * HNorm hd (u 0)) theta.
Proof.
  intros hd td nu T u Dkin GoodD Ccum Seed P0 kappa theta
    HT Hnu HI Hschedule HS HP Hk Htheta Hseed Hcharge.
  apply (Q.LEDGER_PREFIX_CHARGE_GIVES_SUBCRITICAL_PAYMENT T Ccum
    (A.canonical_cut T) (fun _ => P.leray_expenditure td nu Dkin)
    Seed P0 kappa (HNorm hd (u 0)) theta).
  - apply A.CANONICAL_CUTS_ARE_COFINAL. exact HT.
  - exact HS.
  - exact HP.
  - exact Hk.
  - apply HNorm_nonnegative.
  - exact Htheta.
  - exact Hseed.
  - intros N t Ht. assert (Htclosed : 0 <= t <= T) by lra.
    exact (proj2 (P.BKLP10_INITIAL_LEDGER_EXPENDITURE_BOUND
      td nu T (fun s => HNorm hd (u s)) Dkin GoodD Hnu HI
      (fun s => HNorm_nonnegative hd (u s)) Hschedule t Htclosed)).
  - exact Hcharge.
Qed.

(* Completed readouts are constructed internally. The binding premise
   applies to the actual totals; their existence is not an analytic input.
   The external exit concerns exactly the u in the supplied LH entrance. *)
Theorem BKC50_LH_ENCODING_M7_SERRIN_CONTINUATION :
  forall q step lambda (Hq : 0 < q < 1) (Hstep : 0 < step),
  (forall i, 0 <= lambda i) ->
  forall hd kd (basis : OrthonormalBasis hd), HComplete hd ->
  forall fg tests td nu T (u : R -> HCarrier hd) u0
    (mode_test : nat -> ETest hd tests) Dcum Ccum X0 Seed Paid theta
    (endpoints : A.OpenTime T -> S.NormEndpoint) Csq
    (ActualSerrin46 Continues : (R -> HCarrier hd) -> Prop),
  HilbertForwardLHModel hd kd fg tests td nu T u u0 ->
  M7RealizationConditions hd basis tests T nu lambda mode_test u Dcum Ccum X0 ->
  Q.SubcriticalPrefixPayment (A.actual_action_mass Ccum (A.canonical_cut T))
    Seed Paid theta ->
  (forall Xinf Dinf,
    R.CountableCriticalReadout T lambda (I.same_coordinates hd basis u)
      Dcum Xinf Dinf ->
    R.SerrinNormBinding T endpoints Xinf Dinf Csq) ->
  E.SerrinExitContract (R -> HCarrier hd) (A.OpenTime T) u
    (fun p => S.serrin46_observation (endpoints p)) ActualSerrin46 Continues ->
  F.NativeForwardLHModel hd kd basis fg tests td nu T
    (C.bkqr_weights q step lambda Hq Hstep) lambda (C.bkqr_ell q step)
    (fun t => F.HilbertShellEncode hd basis
      (C.bkqr_weights q step lambda Hq Hstep) (u t))
    (F.HilbertShellEncode hd basis (C.bkqr_weights q step lambda Hq Hstep) u0) /\
  I.SamePathM7Injection T nu lambda (I.same_coordinates hd basis u)
    Dcum Ccum X0 Seed (Paid + theta * Q.prefix_action_budget Seed Paid theta) /\
  (forall p, S.serrin46_observation (endpoints p) <=
    Csq * Csq * (X0 + Q.prefix_action_budget Seed Paid theta)^2 / nu) /\
  ActualSerrin46 u /\ Continues u.
Proof.
  intros q step lambda Hq Hstep Hlambda hd kd basis Hcomplete
    fg tests td nu T u u0 mode_test Dcum Ccum X0 Seed Paid theta
    endpoints Csq ActualSerrin46 Continues HLH Hreal Hpayment Hnorm Hexit.
  pose proof (proj1 HLH) as Hnu.
  pose proof (proj1 (proj2 HLH)) as HT.
  assert (Htheta : theta < 96 / 605).
  { destruct Hpayment as [_ [_ [[_ H] _]]]. exact H. }
  destruct (BKC20_PREFIX_PAYMENT_INJECTS_SAME_PATH q step lambda Hq Hstep
    Hlambda hd kd basis Hcomplete fg tests td nu T u u0 mode_test
    Dcum Ccum X0 Seed Paid theta HLH Hreal Hpayment) as [Hnative Hinj].
  destruct (R.BKMS12_COUNTABLE_READOUT_EXISTS T nu lambda
    (I.same_coordinates hd basis u) Dcum Ccum X0 Seed
    (Paid + theta * Q.prefix_action_budget Seed Paid theta) Hinj)
    as [Xinf [Dinf Hreadout]].
  specialize (Hnorm Xinf Dinf Hreadout).
  split; [exact Hnative|]. split; [exact Hinj|]. split.
  - intro p.
    pose proof (R.BKMS30_INJECTION_TO_SERRIN_OBSERVABLE T nu lambda
      (I.same_coordinates hd basis u) Dcum Ccum X0 Seed
      (Paid + theta * Q.prefix_action_budget Seed Paid theta)
      Xinf Dinf endpoints Csq HT Hnu Hinj Hreadout Hnorm p) as Hbound.
    unfold R.serrin_budget, R.critical_cap in Hbound.
    rewrite (Q.ABSORBED_PAYMENT_RETAINS_SHARP_ACTION_BUDGET
      Seed Paid theta Htheta) in Hbound. exact Hbound.
  - exact (R.BKMS50_SAME_PATH_SERRIN_CONTINUATION hd basis u T nu lambda
      Dcum Ccum X0 Seed (Paid + theta * Q.prefix_action_budget Seed Paid theta)
      Xinf Dinf endpoints Csq ActualSerrin46 Continues
      HT Hnu Hinj Hreadout Hnorm Hexit).
Qed.

Theorem BKC60_LH_LEDGER_TO_ENCODING_M7_SERRIN_CONTINUATION :
  forall q step lambda (Hq : 0 < q < 1) (Hstep : 0 < step),
  (forall i, 0 <= lambda i) ->
  forall hd kd (basis : OrthonormalBasis hd), HComplete hd ->
  forall fg tests td nu T (u : R -> HCarrier hd) u0
    (mode_test : nat -> ETest hd tests) Dkin GoodD Dcum Ccum X0 Seed P0 kappa theta
    (endpoints : A.OpenTime T -> S.NormEndpoint) Csq
    (ActualSerrin46 Continues : (R -> HCarrier hd) -> Prop),
  let Paid := P0 + kappa * HNorm hd u0 in
  HilbertForwardLHModel hd kd fg tests td nu T u u0 ->
  M7RealizationConditions hd basis tests T nu lambda mode_test u Dcum Ccum X0 ->
  IntegralNonnegative td ->
  EnergySchedule0 td nu T (fun t => HNorm hd (u t)) Dkin GoodD ->
  (forall t, 0 <= t <= T -> GoodD t ->
    ForwardGradientEnergyAt hd kd fg (u t) (Dkin t)) ->
  0 <= Seed -> 0 <= P0 -> 0 <= kappa -> 0 <= theta < 96 / 605 ->
  (forall N, A.actual_action_mass Ccum (A.canonical_cut T) N O <= Seed) ->
  (forall N k, Q.GM.paid_prefix
    (A.canonical_action_debt Ccum (A.canonical_cut T) N) k <=
    P0 + kappa * P.leray_expenditure td nu Dkin (A.canonical_cut T k) +
    theta * Q.GM.resistant_prefix
      (A.actual_action_mass Ccum (A.canonical_cut T) N) k) ->
  (forall Xinf Dinf,
    R.CountableCriticalReadout T lambda (I.same_coordinates hd basis u)
      Dcum Xinf Dinf ->
    R.SerrinNormBinding T endpoints Xinf Dinf Csq) ->
  E.SerrinExitContract (R -> HCarrier hd) (A.OpenTime T) u
    (fun p => S.serrin46_observation (endpoints p)) ActualSerrin46 Continues ->
  F.NativeForwardLHModel hd kd basis fg tests td nu T
    (C.bkqr_weights q step lambda Hq Hstep) lambda (C.bkqr_ell q step)
    (fun t => F.HilbertShellEncode hd basis
      (C.bkqr_weights q step lambda Hq Hstep) (u t))
    (F.HilbertShellEncode hd basis (C.bkqr_weights q step lambda Hq Hstep) u0) /\
  I.SamePathM7Injection T nu lambda (I.same_coordinates hd basis u)
    Dcum Ccum X0 Seed (Paid + theta * Q.prefix_action_budget Seed Paid theta) /\
  (forall p, S.serrin46_observation (endpoints p) <=
    Csq * Csq * (X0 + Q.prefix_action_budget Seed Paid theta)^2 / nu) /\
  ActualSerrin46 u /\ Continues u.
Proof.
  intros q step lambda Hq Hstep Hlambda hd kd basis Hcomplete
    fg tests td nu T u u0 mode_test Dkin GoodD Dcum Ccum X0 Seed P0 kappa theta
    endpoints Csq ActualSerrin46 Continues Paid HLH Hreal HI Hschedule Hgradient
    HS HP Hk Htheta Hseed Hcharge Hnorm Hexit.
  apply (BKC50_LH_ENCODING_M7_SERRIN_CONTINUATION q step lambda Hq Hstep
    Hlambda hd kd basis Hcomplete fg tests td nu T u u0 mode_test
    Dcum Ccum X0 Seed Paid theta endpoints Csq ActualSerrin46 Continues
    HLH Hreal).
  - pose proof (BKC30_SAME_LH_PREFIX_CHARGE_BUILDS_PAYMENT hd td nu T u
      Dkin GoodD Ccum Seed P0 kappa theta (proj1 (proj2 HLH))
      (Rlt_le _ _ (proj1 HLH)) HI Hschedule HS HP Hk Htheta Hseed Hcharge) as Hpay.
    pose proof (proj1 (proj2 (proj2 HLH))) as Hinitial.
    rewrite Hinitial in Hpay. exact Hpay.
  - exact Hnorm.
  - exact Hexit.
Qed.

Print Assumptions BKC60_LH_LEDGER_TO_ENCODING_M7_SERRIN_CONTINUATION.

Print Assumptions BKC20_PREFIX_PAYMENT_INJECTS_SAME_PATH.
Print Assumptions BKC30_SAME_LH_PREFIX_CHARGE_BUILDS_PAYMENT.
Print Assumptions BKC50_LH_ENCODING_M7_SERRIN_CONTINUATION.
End BKQR_LHGP_CONDITIONAL_CONTINUATION.
