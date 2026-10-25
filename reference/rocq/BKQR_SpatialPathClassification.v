From Stdlib Require Import Reals Lra Psatz.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_ClassificationAudit.
Require Import BKQR_TimeIntegrals BKQR_WeakBalance BKQR_EnergyPaths.
Require Import BKQR_QuadraticTransport BKQR_SourceConstruction BKQR_NonlinearTimeSource.
Require Import BKQR_FourierSchur BKQR_NSEFourierKernel BKQR_NSEFourierClassification.
Require Import BKQR_FourierAdmissibility BKQR_AdmissibleFourierPaths.
Require Import BKQR_FourierSourceStability BKQR_SpatialSource.

(* The spatial weak source is defined by ACTUAL finite spatial integrals,
   followed by the proved limit.  This does not supply an infinite Lebesgue
   field or identify its product integral; those remain separate obligations. *)
Module BKQR_SPATIAL_PATH_CLASSIFICATION.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_TIME_INTEGRALS.
Import BKQR_WEAK_BALANCE BKQR_ENERGY_PATHS BKQR_QUADRATIC_TRANSPORT.
Import BKQR_SOURCE_CONSTRUCTION BKQR_FOURIER_SCHUR BKQR_NSE_FOURIER_KERNEL.
Import BKQR_ADMISSIBLE_FOURIER_PATHS BKQR_FOURIER_SOURCE_STABILITY BKQR_SPATIAL_SOURCE.
Module C := BKQR_CLASSIFICATION.
Open Scope R_scope.

Definition SpatialPolynomialWeakEquation nu u a b Hab Hu : Prop :=
  forall (eta:C1ZeroEndpointTest a b) i,
  SeqLimit (spatial_tested_source u a b Hab Hu (test_value a b eta)
    (test_value_continuous a b eta) i)
    (-coordinate_linear stokes_frequency nu u a b Hab Hu eta i).

Theorem BKSP40_SPATIAL_AND_COORDINATE_WEAK_EQUATIONS_EQUIVALENT :
  forall nu u a b Hab Hu E,
  (forall t,a<=t<=b ->PhysicalBound(u t)E) ->
  (SpatialPolynomialWeakEquation nu u a b Hab Hu <->
   CoordinateQuadraticWeakEquation indexed_convection_kernel stokes_frequency
     nu u a b Hab Hu).
Proof.
  intros nu u a b Hab Hu E Hcap.
  assert (HC:forall eta i,
    SeqLimit (coordinate_source indexed_convection_kernel u a b Hab Hu eta i)
      (concrete_source_value u a b Hab Hu (test_value a b eta)
        (test_value_continuous a b eta) E Hcap i)).
  { intros eta i. apply (limit_ext
      (BKQR_NONLINEAR_TIME_SOURCE.tested_source (indexed_convection_kernel i)
        u a b Hab Hu (test_value a b eta) (test_value_continuous a b eta))).
    - intro N. symmetry. apply coordinate_source_is_tested_source.
    - apply concrete_source_value_spec. }
  assert (HS:forall eta i,
    SeqLimit (spatial_tested_source u a b Hab Hu (test_value a b eta)
      (test_value_continuous a b eta) i)
      (concrete_source_value u a b Hab Hu (test_value a b eta)
        (test_value_continuous a b eta) E Hcap i)).
  { intros. apply BKSP30_ACTUAL_SPATIAL_PRODUCT_LIMIT_IS_CONSTRUCTED_SOURCE. }
  split; intros H eta i.
  - assert (Heq:-coordinate_linear stokes_frequency nu u a b Hab Hu eta i=
      concrete_source_value u a b Hab Hu (test_value a b eta)
        (test_value_continuous a b eta) E Hcap i).
    { eapply UL_sequence; [apply H|apply HS]. }
    rewrite Heq. apply HC.
  - assert (Heq:-coordinate_linear stokes_frequency nu u a b Hab Hu eta i=
      concrete_source_value u a b Hab Hu (test_value a b eta)
        (test_value_continuous a b eta) E Hcap i).
    { eapply UL_sequence; [apply H|apply HC]. }
    rewrite Heq. apply HS.
Qed.

Definition AdmissibleSpatialPolynomialEnergyPath nu T Start u v0 E0 : Prop :=
  (SpectralEnergyPath stokes_frequency nu T Start u v0 E0 /\
    forall (HT:0<=T) (Hu:CoordinateContinuous u 0 T),
      SpatialPolynomialWeakEquation nu u 0 T HT Hu) /\
  FourierAdmissibleOn T u.

Theorem BKSP41_EXACT_ADMISSIBLE_SPATIAL_AND_SPECTRAL_PATHS :
  forall nu T Start u v0 E0,0<=nu ->
  (AdmissibleSpatialPolynomialEnergyPath nu T Start u v0 E0 <->
   AdmissibleSpectralQuadraticEnergyPath nu T Start u v0 E0).
Proof.
  intros nu T Start u v0 E0 Hnu.
  unfold AdmissibleSpatialPolynomialEnergyPath,AdmissibleSpectralQuadraticEnergyPath,
    SpectralQuadraticEnergyPath.
  split; intros [[Henergy Heq] Hadm]; split; [split|exact Hadm|split|exact Hadm];
    try exact Henergy.
  - intros HT Hu. apply (proj1 (BKSP40_SPATIAL_AND_COORDINATE_WEAK_EQUATIONS_EQUIVALENT
      nu u 0 T HT Hu E0
      (BKEP10_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP stokes_frequency nu T Start u v0 E0 Hnu Henergy))).
    apply Heq.
  - intros HT Hu. apply (proj2 (BKSP40_SPATIAL_AND_COORDINATE_WEAK_EQUATIONS_EQUIVALENT
      nu u 0 T HT Hu E0
      (BKEP10_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP stokes_frequency nu T Start u v0 E0 Hnu Henergy))).
    apply Heq.
Qed.

Theorem BKSP50_EXACT_BKQR_AND_ADMISSIBLE_SPATIAL_POLYNOMIAL_PATHS :
  forall q h nu T (Hq:0<q<1) (Hh:0<h) (HT:0<=T) Start U,
  0<=nu -> ShellCoordinateContinuous U 0 T ->
  (forall t,0<=t<=T ->C.BKQRCompatible q h stokes_frequency(U t)) ->
  forall v0 E0,
  let psi:=C.bkqr_weights q h stokes_frequency Hq Hh in
  AdmissibleNativeQuadraticEnergyPath q h Hq Hh nu T Start U (gp_encode psi v0) E0
  <-> AdmissibleSpatialPolynomialEnergyPath nu T Start
    (fun t=>reconstruct psi(U t)) v0 E0.
Proof.
  intros q h nu T Hq Hh HT Start U Hnu HU Hcomp v0 E0. cbv zeta.
  rewrite (BKSP41_EXACT_ADMISSIBLE_SPATIAL_AND_SPECTRAL_PATHS nu T Start
    (fun t=>reconstruct (C.bkqr_weights q h stokes_frequency Hq Hh)(U t)) v0 E0 Hnu).
  apply BKAFP20_EXACT_ADMISSIBLE_QUADRATIC_ENERGY_PATH_CLASSIFICATION; assumption.
Qed.

Check BKSP50_EXACT_BKQR_AND_ADMISSIBLE_SPATIAL_POLYNOMIAL_PATHS.
Print Assumptions BKSP40_SPATIAL_AND_COORDINATE_WEAK_EQUATIONS_EQUIVALENT.
Print Assumptions BKSP50_EXACT_BKQR_AND_ADMISSIBLE_SPATIAL_POLYNOMIAL_PATHS.
End BKQR_SPATIAL_PATH_CLASSIFICATION.
