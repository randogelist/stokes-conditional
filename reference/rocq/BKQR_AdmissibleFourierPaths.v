From Stdlib Require Import Reals Lra Psatz.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_ClassificationAudit.
Require Import BKQR_TimeIntegrals BKQR_EnergyPaths BKQR_QuadraticTransport BKQR_BilinearKernel.
Require Import BKQR_FourierIndices BKQR_FourierConvection BKQR_FourierSchur.
Require Import BKQR_NSEFourierKernel BKQR_NSEFourierClassification.
Require Import BKQR_FourierAdmissibility.

(* The already constructed Fourier quadratic equation and energy path are
   now restricted by literal reality and divergence constraints.  Zero mean
   remains optional.  This is a spectral path theorem, not an identification
   of those paths with a completed physical L2/Leray--Hopf model. *)
Module BKQR_ADMISSIBLE_FOURIER_PATHS.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_TIME_INTEGRALS.
Import BKQR_QUADRATIC_TRANSPORT BKQR_FOURIER_SCHUR BKQR_NSE_FOURIER_KERNEL.
Import BKQR_NSE_FOURIER_CLASSIFICATION BKQR_FOURIER_ADMISSIBILITY.
Module C := BKQR_CLASSIFICATION.
Open Scope R_scope.

Definition FourierAdmissibleOn T (u:R->nat->R) : Prop :=
  forall t,0<=t<=T -> FourierAdmissible (u t).
Definition NativeAdmissibleOn T (U:R->nat->nat->R) : Prop :=
  forall t,0<=t<=T -> NativeAdmissible (U t).
Definition FourierZeroMeanOn T (u:R->nat->R) : Prop :=
  forall t,0<=t<=T -> FourierZeroMean (u t).
Definition NativeZeroMeanOn T (U:R->nat->nat->R) : Prop :=
  forall t,0<=t<=T -> NativeZeroMean (U t).

Definition AdmissibleSpectralQuadraticEnergyPath nu T Start u v0 E0 : Prop :=
  SpectralQuadraticEnergyPath indexed_convection_kernel stokes_frequency
    nu T Start u v0 E0 /\ FourierAdmissibleOn T u.

Definition AdmissibleNativeQuadraticEnergyPath q h Hq Hh nu T Start U V0 E0 : Prop :=
  NativeQuadraticEnergyPath indexed_convection_kernel
    (C.bkqr_weights q h stokes_frequency Hq Hh) stokes_frequency
    (C.bkqr_ell q h) nu T Start U V0 E0 /\ NativeAdmissibleOn T U.

Theorem BKAFP10_EXACT_ADMISSIBILITY_PATH_TRANSPORT :
  forall q h (Hq:0<q<1) (Hh:0<h) T U,
  (forall t,0<=t<=T -> C.BKQRCompatible q h stokes_frequency (U t)) ->
  let psi:=C.bkqr_weights q h stokes_frequency Hq Hh in
  FourierAdmissibleOn T (fun t=>reconstruct psi (U t)) <-> NativeAdmissibleOn T U.
Proof.
  intros q h Hq Hh T U Hcomp. cbv zeta. split; intros H t Ht.
  - apply (proj1 (BKFA50_ADMISSIBILITY_ON_COMPATIBLE_RANGE q h Hq Hh
      (U t) (Hcomp t Ht))). apply H. exact Ht.
  - apply (proj2 (BKFA50_ADMISSIBILITY_ON_COMPATIBLE_RANGE q h Hq Hh
      (U t) (Hcomp t Ht))). apply H. exact Ht.
Qed.

Theorem BKAFP11_EXACT_ZERO_MEAN_PATH_TRANSPORT :
  forall q h (Hq:0<q<1) (Hh:0<h) T U,
  (forall t,0<=t<=T -> C.BKQRCompatible q h stokes_frequency (U t)) ->
  let psi:=C.bkqr_weights q h stokes_frequency Hq Hh in
  FourierZeroMeanOn T (fun t=>reconstruct psi (U t)) <-> NativeZeroMeanOn T U.
Proof.
  intros q h Hq Hh T U Hcomp. cbv zeta. split; intros H t Ht.
  - apply (proj1 (BKFA42_ZERO_MEAN_ON_COMPATIBLE_RANGE q h Hq Hh
      (U t) (Hcomp t Ht))). apply H. exact Ht.
  - apply (proj2 (BKFA42_ZERO_MEAN_ON_COMPATIBLE_RANGE q h Hq Hh
      (U t) (Hcomp t Ht))). apply H. exact Ht.
Qed.

Theorem BKAFP20_EXACT_ADMISSIBLE_QUADRATIC_ENERGY_PATH_CLASSIFICATION :
  forall q h nu T (Hq:0<q<1) (Hh:0<h) (HT:0<=T) Start U,
  ShellCoordinateContinuous U 0 T ->
  (forall t,0<=t<=T -> C.BKQRCompatible q h stokes_frequency (U t)) ->
  forall v0 E0,
  let psi:=C.bkqr_weights q h stokes_frequency Hq Hh in
  AdmissibleNativeQuadraticEnergyPath q h Hq Hh nu T Start U (gp_encode psi v0) E0
  <-> AdmissibleSpectralQuadraticEnergyPath nu T Start
    (fun t=>reconstruct psi (U t)) v0 E0.
Proof.
  intros q h nu T Hq Hh HT Start U HU Hcomp v0 E0. cbv zeta.
  unfold AdmissibleNativeQuadraticEnergyPath,AdmissibleSpectralQuadraticEnergyPath.
  rewrite (BKNSE30_EXACT_FOURIER_QUADRATIC_ENERGY_PATH_CLASSIFICATION
    q h nu T Hq Hh HT Start U HU Hcomp v0 E0).
  rewrite (BKAFP10_EXACT_ADMISSIBILITY_PATH_TRANSPORT q h Hq Hh T U Hcomp).
  reflexivity.
Qed.

Theorem BKAFP30_ADMISSIBLE_PATH_HAS_ADVECTIVE_FINITE_CONVOLUTION :
  forall nu T Start u v0 E0,
  AdmissibleSpectralQuadraticEnergyPath nu T Start u v0 E0 ->
  forall t,0<=t<=T -> forall i N,
  BKQR_BILINEAR_KERNEL.quadratic_form
    (indexed_convection_kernel i) (6*N)%nat (u t)=
  finite_advective_convolution i N (u t).
Proof.
  intros nu T Start u v0 E0 [Hpath Hadm] t Ht i N.
  apply BKNF21_SOLENOIDAL_ADVECTIVE_CONVOLUTION_IDENTITY.
  apply FOURIER_SOLENOIDAL_IMPLIES_BLOCK_SOLENOIDAL.
  exact (proj2 (Hadm t Ht)).
Qed.

Print Assumptions BKAFP20_EXACT_ADMISSIBLE_QUADRATIC_ENERGY_PATH_CLASSIFICATION.
Print Assumptions BKAFP30_ADMISSIBLE_PATH_HAS_ADVECTIVE_FINITE_CONVOLUTION.
End BKQR_ADMISSIBLE_FOURIER_PATHS.
