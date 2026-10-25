From Stdlib Require Import String Lists.List.
Require Import NSE_CLAY_FEFFERMAN_FRAMEWORK.
Require Import awpi_nse_torus_fourier_periodic_admissibility_v0_45_1.
Require Import awpi_nse_lh_torus_fourier_tests_v0_44_3.
Require Import awpi_nse_lh_fourier_polynomial_convolution_v0_45_1.

Module CLAY_FEFFERMAN_B_T3_UNFORCED.
Module FW := CLAY_FEFFERMAN_FRAMEWORK.
Module TPER := NSE_TORUS_FOURIER_PERIODIC_ADMISSIBILITY_V0451.
Module TCONV := NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.

Theorem B00_PERIODIC_STOKES_GEOMETRY_READY :
  TPER.FullConcretePlaneWaveFamilyGeometry.
Proof. exact FW.FW10_TORUS_PLANE_WAVE_GEOMETRY_READY. Qed.

Theorem B01_PERIODIC_FINITE_PRODUCT_CONVOLUTION_READY :
  forall P Q : list TCONV.FourierTerm,
  forall x : TCONV.R3,
    TCONV.poly_eval (TCONV.product_terms P Q) x =
    TCONV.CH.cmul (TCONV.poly_eval P x) (TCONV.poly_eval Q x).
Proof. exact FW.FW11_TORUS_FINITE_FOURIER_PRODUCT_IS_CONVOLUTION. Qed.

Section B_STATEMENT.
Context {InitialData Force SmoothSolution : Type}.
Variable T3InitialAdmissible : InitialData -> Prop.
Variable T3ForceAdmissible : Force -> Prop.
Variable T3ZeroForce : Force.
Variable T3SmoothSolution : InitialData -> Force -> SmoothSolution -> Prop.
Variable T3CriticalClosed : InitialData -> Force -> Prop.
Variable T3IntrinsicRegularForce : Force -> Prop.

Definition FEFFERMAN_B : Prop :=
  forall u0 : InitialData,
    T3InitialAdmissible u0 ->
    exists sol : SmoothSolution, T3SmoothSolution u0 T3ZeroForce sol.

Hypothesis T3_DOMAIN_DIAMOND :
  FW.DomainDiamondClosure
    T3InitialAdmissible T3ForceAdmissible T3ZeroForce
    T3SmoothSolution T3CriticalClosed T3IntrinsicRegularForce.

Theorem B10_T3_DOMAIN_DIAMOND_GIVES_FEFFERMAN_B :
  FEFFERMAN_B.
Proof.
  intros u0 Hu0.
  destruct T3_DOMAIN_DIAMOND as [Hzero HzeroReg Hclose Hexit].
  apply Hexit.
  exact (Hclose u0 T3ZeroForce Hu0 Hzero HzeroReg).
Qed.

Definition B_STATUS : string :=
  "B_T3_UNFORCED_REDUCED_TO_SHARED_T3_DOMAIN_DIAMOND_PERIODIC_FRONTEND_KERNEL_READY"%string.
End B_STATEMENT.
End CLAY_FEFFERMAN_B_T3_UNFORCED.

Print CLAY_FEFFERMAN_B_T3_UNFORCED.B00_PERIODIC_STOKES_GEOMETRY_READY.
Print CLAY_FEFFERMAN_B_T3_UNFORCED.B01_PERIODIC_FINITE_PRODUCT_CONVOLUTION_READY.
Print CLAY_FEFFERMAN_B_T3_UNFORCED.B10_T3_DOMAIN_DIAMOND_GIVES_FEFFERMAN_B.
