(* Same-path injection. The velocity, nonlinear source, critical moments,
   and cumulative action are tied by their actual formulas. Remaining
   modal/time realization, critical seed, and local payment assumptions
   are exposed in the terminal rather than replaced by an M7 assumption. *)
From Stdlib Require Import Reals Lra Psatz Field.
Require Import LHGP_Hilbert LHGP_Evolution LHGP_Equivalence LHGP_InitialEnergy.
Require Import LHGP_ForwardGradient LHGP_ForwardContainment.
Require Import BKQR_CountableRange BKQR_ClassificationAudit.
Require Import BKQR_LHGP_CoordinateBridge BKQR_LHGP_EvolutionBridge.
Require Import BKQR_LHGP_ForwardBridge.
Require Import BKQR_M7_CriticalCalculus BKQR_M7_ActionCells.
Require Import BKQR_M7_WeightedCompletion BKQR_M7_LHPayment.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module BKQR_LHGP_M7_INJECTION.
Module B := GP_COUNTABLE_RANGE.
Module W := BKQR_M7_WEIGHTED_COMPLETION.
Module M := BKQR_M7_CRITICAL_CALCULUS.
Module A := BKQR_M7_ACTION_CELLS.
Module P := BKQR_M7_LH_PAYMENT.
Module G := NSE_GP_TO_M7_SPINE.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Module C := BKQR_CLASSIFICATION.
Module F := BKQR_LHGP_FORWARD_BRIDGE.
Module E := BKQR_LHGP_EVOLUTION_BRIDGE.
Open Scope R_scope.

Definition same_coordinates hd (basis : OrthonormalBasis hd)
    (u : R -> HCarrier hd) : R -> nat -> R :=
  fun t => HAnalysis basis (u t).

Definition same_source hd (tests : EvolutionTests hd)
    (mode_test : nat -> ETest hd tests) (u : R -> HCarrier hd) : R -> nat -> R :=
  fun t i => EConvection hd tests (mode_test i) t (u t) (u t).

Theorem BKM700_SAME_SOURCE_IS_NATIVE_QUADRATIC_READOUT :
  forall hd (basis : OrthonormalBasis hd), HComplete hd ->
  forall tests mode_test psi (u : R -> HCarrier hd),
  (forall i, psi 0%nat i <> 0) ->
  forall mode t,
  E.native_quadratic_limit psi (F.HilbertShellEncode hd basis psi (u t))
    (fun i j => EConvection hd tests (mode_test mode) t
      (HBasis hd basis i) (HBasis hd basis j))
    (same_source hd tests mode_test u t mode).
Proof.
  intros hd basis Hcomplete tests mode_test psi u Hzero mode t.
  exact (E.BKLE31_ACTUAL_NATIVE_QUADRATIC_READOUT hd basis Hcomplete tests psi
    (fun s => F.HilbertShellEncode hd basis psi (u s)) u Hzero
    (fun s i => eq_refl) (mode_test mode) t).
Qed.

Lemma critical_mass_is_weighted_prefix : forall lambda a N t,
  M.critical_mass lambda a N t = W.weighted_prefix lambda (a t) N.
Proof.
  intros lambda a N t. induction N; simpl; [reflexivity|].
  unfold M.critical_mass, W.weighted_prefix in *; simpl in *.
  rewrite IHN. reflexivity.
Qed.

Record SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid : Prop := {
  injection_sequence_m7 : forall N,
    G.GPSequenceM7 (A.actual_action_mass Ccum (A.canonical_cut T) N);
  injection_same_action_realized : forall N,
    CE.M7ActionCostRealization (A.OpenTime T)
      (A.actual_action_mass Ccum (A.canonical_cut T) N)
      (fun t => Ccum N (proj1_sig t));
  injection_action_bound : forall N t, M.OpenTime T t ->
    Ccum N t <= A.sharp_action_budget Seed Paid;
  injection_critical_mass_bound : forall N t, M.OpenTime T t ->
    M.critical_mass lambda a N t <= X0 + A.sharp_action_budget Seed Paid;
  injection_critical_dissipation_bound : forall N t, M.OpenTime T t ->
    Dcum N t <= (X0 + A.sharp_action_budget Seed Paid) / nu;
  injection_countable_mass : forall t, M.OpenTime T t ->
    exists X, 0 <= X <= X0 + A.sharp_action_budget Seed Paid /\
      W.WeightedTotal lambda (a t) X;
  injection_countable_dissipation : forall t, M.OpenTime T t ->
    exists D, 0 <= D <= (X0 + A.sharp_action_budget Seed Paid) / nu /\
      W.PrefixTotal (fun N => Dcum N t) D
}.

Theorem BKM710_DERIVED_BALANCE_AND_ACTUAL_CELLS_INJECT_M7 :
  forall T nu lambda a b Dcum Ccum X0 Seed Paid,
  0 < T -> 0 < nu -> (forall i, 0 <= lambda i) ->
  M.ModalEquation T nu lambda a b ->
  (forall N, M.OpenPrimitive T (M.critical_density lambda a N) (Dcum N)) ->
  (forall N, M.OpenPrimitive T (M.normalized_action nu lambda a b N) (Ccum N)) ->
  (forall N, M.critical_mass lambda a N 0 <= X0) ->
  A.CommonActionPayment Ccum (A.canonical_cut T) Seed Paid ->
  SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid.
Proof.
  intros T nu lambda a b Dcum Ccum X0 Seed Paid HT Hnu Hlambda
    Hmodal HD HC HX0 Hpayment.
  assert (Hcuts : A.CofinalActionCuts T (A.canonical_cut T)).
  { apply A.CANONICAL_CUTS_ARE_COFINAL. exact HT. }
  assert (Hmono : A.MonotoneCumulativeAction T Ccum).
  { constructor.
    - intro N. exact (proj1 (HC N)).
    - intros N s t Hs Hst Ht.
      apply (M.BKMC31_OPEN_PRIMITIVE_MONOTONE T
        (M.normalized_action nu lambda a b N) (Ccum N) (HC N)).
      + intros r Hr. apply M.normalized_action_nonnegative; assumption.
      + unfold M.OpenTime; lra.
      + unfold M.OpenTime; lra.
      + exact Hst. }
  pose proof (A.COMMON_PAYMENT_GIVES_UNIFORM_ACTUAL_ACTION T Ccum
    (A.canonical_cut T) Seed Paid Hcuts Hmono Hpayment) as HCbound.
  pose proof (M.BKMC40_DERIVED_CRITICAL_ENERGY_BALANCE T nu lambda a b
    Dcum Ccum X0 HT Hnu Hlambda Hmodal HD HC HX0) as Hbalance.
  assert (HDnonneg : forall N t, M.OpenTime T t -> 0 <= Dcum N t).
  { intros N t Ht. exact (CE.ceb_dissipation_nonneg _ _ _ _ _ _ _ Hbalance
      (N, exist _ t Ht)). }
  assert (HXbound : forall N t, M.OpenTime T t ->
      M.critical_mass lambda a N t <= X0 + A.sharp_action_budget Seed Paid).
  { intros N t Ht.
    pose proof (CE.ceb_integrated_balance _ _ _ _ _ _ _ Hbalance
      (N, exist _ t Ht)) as Hbal.
    change (M.critical_mass lambda a N t +
      CE.effective_viscosity nu 0 * Dcum N t <= X0 + Ccum N t) in Hbal.
    unfold CE.effective_viscosity in Hbal.
    pose proof (HDnonneg N t Ht). pose proof (HCbound N t Ht). nra. }
  assert (HDbound : forall N t, M.OpenTime T t ->
      Dcum N t <= (X0 + A.sharp_action_budget Seed Paid) / nu).
  { intros N t Ht.
    pose proof (CE.ceb_integrated_balance _ _ _ _ _ _ _ Hbalance
      (N, exist _ t Ht)) as Hbal.
    change (M.critical_mass lambda a N t +
      CE.effective_viscosity nu 0 * Dcum N t <= X0 + Ccum N t) in Hbal.
    unfold CE.effective_viscosity in Hbal.
    pose proof (M.critical_mass_nonnegative lambda a N t Hlambda).
    pose proof (HCbound N t Ht).
    apply (Rmult_le_reg_r nu); [exact Hnu|].
    replace ((X0 + A.sharp_action_budget Seed Paid) / nu * nu)
      with (X0 + A.sharp_action_budget Seed Paid) by (field; lra). nra. }
  constructor.
  - exact (A.COMMON_PAYMENT_GIVES_ACTUAL_M7 T Ccum (A.canonical_cut T)
      Seed Paid Hcuts Hmono Hpayment).
  - exact (A.ACTION_CELLS_CONSTRUCT_M7_REALIZATION T Ccum
      (A.canonical_cut T) Hcuts Hmono).
  - exact HCbound.
  - exact HXbound.
  - exact HDbound.
  - intros t Ht.
    destruct (W.WEIGHTED_COMPLETION lambda (a t)
      (X0 + A.sharp_action_budget Seed Paid) Hlambda) as [X [HX [HTotal HPhysical]]].
    + intro N. rewrite <- critical_mass_is_weighted_prefix. apply HXbound. exact Ht.
    + exists X. split; assumption.
  - intros t Ht. apply W.CUMULATIVE_NONNEGATIVE_COMPLETION.
    + intro N. apply HDnonneg. exact Ht.
    + intro N. apply HDbound. exact Ht.
Qed.

(* Public same-u endpoint. The critical modal equation and its primitives
   are explicit analytic realization conditions, not consequences asserted
   for an arbitrary weak path. Debt is charged to the SAME LH expenditure. *)
Theorem BKM750_LH_GP_BKQR_M7_INJECTION :
  forall q step lambda (Hq : 0 < q < 1) (Hstep : 0 < step),
  (forall i, 0 <= lambda i) ->
  forall hd kd (basis : OrthonormalBasis hd), HComplete hd ->
  forall fg tests td nu T (u : R -> HCarrier hd) u0
    (mode_test : nat -> ETest hd tests) Dkin GoodD Dcum Ccum X0 Seed kappa,
  HilbertForwardLHModel hd kd fg tests td nu T u u0 ->
  IntegralNonnegative td ->
  EnergySchedule0 td nu T (fun t => HNorm hd (u t)) Dkin GoodD ->
  (forall t, 0 <= t <= T -> GoodD t ->
    ForwardGradientEnergyAt hd kd fg (u t) (Dkin t)) ->
  M.ModalEquation T nu lambda (same_coordinates hd basis u)
    (same_source hd tests mode_test u) ->
  (forall N, M.OpenPrimitive T
    (M.critical_density lambda (same_coordinates hd basis u) N) (Dcum N)) ->
  (forall N, M.OpenPrimitive T
    (M.normalized_action nu lambda (same_coordinates hd basis u)
      (same_source hd tests mode_test u) N) (Ccum N)) ->
  (forall N, M.critical_mass lambda (same_coordinates hd basis u) N 0 <= X0) ->
  0 <= Seed -> 0 <= kappa ->
  (forall N, A.actual_action_mass Ccum (A.canonical_cut T) N O <= Seed) ->
  (forall N n, A.canonical_action_debt Ccum (A.canonical_cut T) N n <=
    kappa * (P.leray_expenditure td nu Dkin (A.canonical_cut T (Datatypes.S n)) -
             P.leray_expenditure td nu Dkin (A.canonical_cut T n))) ->
  F.NativeForwardLHModel hd kd basis fg tests td nu T
    (C.bkqr_weights q step lambda Hq Hstep) lambda (C.bkqr_ell q step)
    (fun t => F.HilbertShellEncode hd basis
      (C.bkqr_weights q step lambda Hq Hstep) (u t))
    (F.HilbertShellEncode hd basis (C.bkqr_weights q step lambda Hq Hstep) u0) /\
  SamePathM7Injection T nu lambda (same_coordinates hd basis u)
    Dcum Ccum X0 Seed (kappa * HNorm hd u0).
Proof.
  intros q step lambda Hq Hstep Hlambda hd kd basis Hcomplete
    fg tests td nu T u u0 mode_test Dkin GoodD Dcum Ccum X0 Seed kappa
    HLH HI Hschedule Hgradient Hmodal HD HC HX0 HSeed Hk Hseed Hcharge.
  pose proof (proj1 HLH) as Hnu.
  pose proof (proj1 (proj2 HLH)) as HT.
  pose proof (proj1 (proj2 (proj2 HLH))) as Hinitial.
  split.
  - apply (F.BKLF30_CANONICAL_HILBERT_FORWARD_CONTAINMENT q step lambda
      Hq Hstep Hlambda hd kd basis Hcomplete fg tests td nu T u u0). exact HLH.
  - apply (BKM710_DERIVED_BALANCE_AND_ACTUAL_CELLS_INJECT_M7 T nu lambda
      (same_coordinates hd basis u) (same_source hd tests mode_test u)
      Dcum Ccum X0 Seed (kappa * HNorm hd u0)); try assumption.
    assert (Hcuts : A.CofinalActionCuts T (A.canonical_cut T)).
    { apply A.CANONICAL_CUTS_ARE_COFINAL. exact HT. }
    assert (Hinside : forall n, 0 <= A.canonical_cut T n <= T).
    { intro n. pose proof (A.cuts_inside T (A.canonical_cut T) Hcuts n). lra. }
    pose proof (P.BKLP30_SAME_HILBERT_PATH_FUNDS_PAYMENT hd td nu T u
      Dkin GoodD (A.canonical_cut T)
      (A.actual_action_mass Ccum (A.canonical_cut T)) kappa
      (Rlt_le _ _ Hnu) Hk HI Hschedule Hinside Hcharge) as [HP HPbound].
    rewrite Hinitial in HP, HPbound.
    split; [exact HSeed|]. split; [exact HP|]. split; assumption.
Qed.

(* The critical weighted sequence is synthesized in the SAME complete
   Hilbert carrier. Identifying this diagonal weight with a physical
   fractional Stokes operator is a separate theorem, not a definition. *)
Theorem BKM760_INJECTED_WEIGHTED_STATE_IS_REALIZED :
  forall hd (basis : OrthonormalBasis hd) psi T nu lambda
    (u : R -> HCarrier hd) Dcum Ccum X0 Seed Paid,
  HComplete hd -> B.ScalarPartition psi -> (forall i, 0 <= lambda i) ->
  SamePathM7Injection T nu lambda (same_coordinates hd basis u)
    Dcum Ccum X0 Seed Paid ->
  forall t, M.OpenTime T t -> exists x : HCarrier hd,
    LHGP_Coordinates.seq_eq (HAnalysis basis x)
      (W.weighted_vector lambda (same_coordinates hd basis u t)) /\
    HConverges hd
      (HFinite basis (W.weighted_vector lambda (same_coordinates hd basis u t))) x /\
    0 <= HNorm hd x <= X0 + A.sharp_action_budget Seed Paid /\
    W.WeightedTotal lambda (same_coordinates hd basis u t) (HNorm hd x) /\
    B.ShellTotal (B.gp_encode psi
      (W.weighted_vector lambda (same_coordinates hd basis u t))) (HNorm hd x).
Proof.
  intros hd basis psi T nu lambda u Dcum Ccum X0 Seed Paid
    Hcomplete Hpartition Hlambda Hinj t Ht.
  apply W.WEIGHTED_HILBERT_COMPLETION; try assumption.
  intro N. rewrite <- critical_mass_is_weighted_prefix.
  exact (injection_critical_mass_bound _ _ _ _ _ _ _ _ _ Hinj N t Ht).
Qed.

Print Assumptions BKM700_SAME_SOURCE_IS_NATIVE_QUADRATIC_READOUT.
Print Assumptions BKM710_DERIVED_BALANCE_AND_ACTUAL_CELLS_INJECT_M7.
Print Assumptions BKM750_LH_GP_BKQR_M7_INJECTION.
Print Assumptions BKM760_INJECTED_WEIGHTED_STATE_IS_REALIZED.
End BKQR_LHGP_M7_INJECTION.
