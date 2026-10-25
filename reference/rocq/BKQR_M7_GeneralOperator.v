(* A general-basis variant keeps the off-diagonal viscous contribution.
   No countable Laplacian eigenbasis on R3 is postulated. The price is that
   action and its payment use the full effective source, including this
   remainder. Modal testing and physical Sobolev identification stay open. *)
From Stdlib Require Import Reals Ranalysis1 Lra Psatz.
Require Import LHGP_Hilbert LHGP_Evolution LHGP_Equivalence LHGP_InitialEnergy.
Require Import LHGP_ForwardGradient LHGP_ForwardContainment.
Require Import BKQR_ClassificationAudit BKQR_LHGP_ForwardBridge.
Require Import BKQR_CountableRange BKQR_LHGP_EvolutionBridge.
Require Import BKQR_M7_CriticalCalculus BKQR_M7_ActionCells BKQR_M7_LHPayment.
Require Import BKQR_LHGP_M7Injection.

Module BKQR_M7_GENERAL_OPERATOR.
Module I := BKQR_LHGP_M7_INJECTION.
Module M := BKQR_M7_CRITICAL_CALCULUS.
Module A := BKQR_M7_ACTION_CELLS.
Module P := BKQR_M7_LH_PAYMENT.
Module C := BKQR_CLASSIFICATION.
Module F := BKQR_LHGP_FORWARD_BRIDGE.
Module B := GP_COUNTABLE_RANGE.
Module E := BKQR_LHGP_EVOLUTION_BRIDGE.
Open Scope R_scope.

Definition same_viscous_readout hd (tests : EvolutionTests hd)
    (mode_test : nat -> ETest hd tests) (u : R -> HCarrier hd) t i :=
  - HInner hd (u t) (ELap hd tests (mode_test i) t).

Definition effective_source hd (basis : OrthonormalBasis hd) tests
    nu lambda mode_test u t i :=
  I.same_source hd tests mode_test u t i +
    nu * (same_viscous_readout hd tests mode_test u t i -
      lambda i * lambda i * I.same_coordinates hd basis u t i).

Definition OperatorModalEquation hd (basis : OrthonormalBasis hd) tests
    T nu mode_test (u : R -> HCarrier hd) : Prop :=
  forall t i, M.OpenTime T t ->
    derivable_pt_lim (fun s => I.same_coordinates hd basis u s i) t
      (-nu * same_viscous_readout hd tests mode_test u t i -
        I.same_source hd tests mode_test u t i).

Theorem BKMO10_FULL_OPERATOR_GIVES_REFERENCE_MODAL_EQUATION :
  forall hd basis tests T nu lambda mode_test u,
  OperatorModalEquation hd basis tests T nu mode_test u ->
  M.ModalEquation T nu lambda (I.same_coordinates hd basis u)
    (effective_source hd basis tests nu lambda mode_test u).
Proof.
  intros hd basis tests T nu lambda mode_test u Hoperator t i Ht.
  pose proof (Hoperator t i Ht) as H.
  unfold effective_source.
  replace (-nu * lambda i * lambda i * I.same_coordinates hd basis u t i -
    (I.same_source hd tests mode_test u t i +
      nu * (same_viscous_readout hd tests mode_test u t i -
        lambda i * lambda i * I.same_coordinates hd basis u t i)))
    with (-nu * same_viscous_readout hd tests mode_test u t i -
      I.same_source hd tests mode_test u t i) by ring.
  exact H.
Qed.

Theorem BKMO11_DIAGONAL_CASE_HAS_NO_VISCOUS_REMAINDER :
  forall hd basis tests nu lambda mode_test u t i,
  same_viscous_readout hd tests mode_test u t i =
    lambda i * lambda i * I.same_coordinates hd basis u t i ->
  effective_source hd basis tests nu lambda mode_test u t i =
    I.same_source hd tests mode_test u t i.
Proof. intros. unfold effective_source. rewrite H. ring. Qed.

Definition native_effective_source_prefix hd (basis : OrthonormalBasis hd)
    tests nu lambda mode_test psi U t mode N :=
  E.native_quadratic_prefix psi U
    (fun i j => EConvection hd tests (mode_test mode) t
      (HBasis hd basis i) (HBasis hd basis j)) N +
  (-nu) * E.native_linear_prefix psi U
    (HAnalysis basis (ELap hd tests (mode_test mode) t)) N +
  (-nu * lambda mode * lambda mode) * (U 0%nat mode / psi 0%nat mode).

Theorem BKMO20_EFFECTIVE_SOURCE_IS_NATIVE_LINEAR_QUADRATIC_LIMIT :
  forall hd (basis : OrthonormalBasis hd), HComplete hd ->
  forall tests nu lambda mode_test psi (u : R -> HCarrier hd),
  (forall i, psi 0%nat i <> 0) -> forall t mode,
  B.SeqLimit
    (native_effective_source_prefix hd basis tests nu lambda mode_test psi
      (F.HilbertShellEncode hd basis psi (u t)) t mode)
    (effective_source hd basis tests nu lambda mode_test u t mode).
Proof.
  intros hd basis Hcomplete tests nu lambda mode_test psi u Hzero t mode.
  pose proof (I.BKM700_SAME_SOURCE_IS_NATIVE_QUADRATIC_READOUT
    hd basis Hcomplete tests mode_test psi u Hzero mode t) as Hquad.
  assert (Hlin : E.native_linear_limit psi
      (F.HilbertShellEncode hd basis psi (u t))
      (HAnalysis basis (ELap hd tests (mode_test mode) t))
      (HInner hd (u t) (ELap hd tests (mode_test mode) t))).
  { apply (proj2 (E.BKLE03_NATIVE_LINEAR_LIMIT _ _ _ _)).
    exact (EVOLUTION_INITIAL_READOUT hd basis Hcomplete (psi 0%nat) (u t)
      (fun i => F.HilbertShellEncode hd basis psi (u t) 0%nat i)
      Hzero (fun i => eq_refl) (ELap hd tests (mode_test mode) t)). }
  unfold native_effective_source_prefix.
  assert (Hcoord : F.HilbertShellEncode hd basis psi (u t) 0%nat mode /
    psi 0%nat mode = I.same_coordinates hd basis u t mode).
  { unfold F.HilbertShellEncode, B.gp_encode, I.same_coordinates.
    field. apply Hzero. }
  rewrite Hcoord.
  replace (effective_source hd basis tests nu lambda mode_test u t mode) with
    ((I.same_source hd tests mode_test u t mode +
       (-nu) * HInner hd (u t) (ELap hd tests (mode_test mode) t)) +
     (-nu * lambda mode * lambda mode) * I.same_coordinates hd basis u t mode)
    by (unfold effective_source, same_viscous_readout; ring).
  apply B.limit_plus.
  - apply B.limit_plus; [exact Hquad|]. apply B.limit_scale. exact Hlin.
  - apply B.limit_const.
Qed.

Theorem BKMO50_GENERAL_OPERATOR_LH_GP_BKQR_M7_INJECTION :
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
  OperatorModalEquation hd basis tests T nu mode_test u ->
  (forall N, M.OpenPrimitive T
    (M.critical_density lambda (I.same_coordinates hd basis u) N) (Dcum N)) ->
  (forall N, M.OpenPrimitive T
    (M.normalized_action nu lambda (I.same_coordinates hd basis u)
      (effective_source hd basis tests nu lambda mode_test u) N) (Ccum N)) ->
  (forall N, M.critical_mass lambda (I.same_coordinates hd basis u) N 0 <= X0) ->
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
  I.SamePathM7Injection T nu lambda (I.same_coordinates hd basis u)
    Dcum Ccum X0 Seed (kappa * HNorm hd u0).
Proof.
  intros q step lambda Hq Hstep Hlambda hd kd basis Hcomplete
    fg tests td nu T u u0 mode_test Dkin GoodD Dcum Ccum X0 Seed kappa
    HLH HI Hschedule Hgradient Hoperator HD HC HX0 HSeed Hk Hseed Hcharge.
  pose proof (proj1 HLH) as Hnu.
  pose proof (proj1 (proj2 HLH)) as HT.
  pose proof (proj1 (proj2 (proj2 HLH))) as Hinitial.
  split.
  - apply (F.BKLF30_CANONICAL_HILBERT_FORWARD_CONTAINMENT q step lambda
      Hq Hstep Hlambda hd kd basis Hcomplete fg tests td nu T u u0). exact HLH.
  - apply (I.BKM710_DERIVED_BALANCE_AND_ACTUAL_CELLS_INJECT_M7 T nu lambda
      (I.same_coordinates hd basis u)
      (effective_source hd basis tests nu lambda mode_test u)
      Dcum Ccum X0 Seed (kappa * HNorm hd u0)); try assumption.
    + apply BKMO10_FULL_OPERATOR_GIVES_REFERENCE_MODAL_EQUATION. exact Hoperator.
    + assert (Hcuts : A.CofinalActionCuts T (A.canonical_cut T)).
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

Print Assumptions BKMO10_FULL_OPERATOR_GIVES_REFERENCE_MODAL_EQUATION.
Print Assumptions BKMO20_EFFECTIVE_SOURCE_IS_NATIVE_LINEAR_QUADRATIC_LIMIT.
Print Assumptions BKMO50_GENERAL_OPERATOR_LH_GP_BKQR_M7_INJECTION.
End BKQR_M7_GENERAL_OPERATOR.
