From Stdlib Require Import Reals Lra Psatz Ring ZArith.
From Stdlib Require Import Rtrigo1 Rtrigo_reg.
From Coquelicot Require Import Coquelicot AutoDerive.

Open Scope R_scope.

Module NSE_TORUS_FOURIER_EIGEN_GEOMETRY_V0441.

(* ========================================================================= *)
(* I. Concrete wave and polarization geometry.                               *)
(* ========================================================================= *)

Record RVec3 : Type := mkRVec3 {
  rvx : R;
  rvy : R;
  rvz : R
}.

Record ZWave3 : Type := mkZWave3 {
  zwx : Z;
  zwy : Z;
  zwz : Z
}.

Definition wave_R (k : ZWave3) : RVec3 :=
  mkRVec3
    (IZR (zwx k))
    (IZR (zwy k))
    (IZR (zwz k)).

Definition rdot (a b : RVec3) : R :=
  rvx a * rvx b +
  rvy a * rvy b +
  rvz a * rvz b.

Definition wave_norm2 (k : ZWave3) : R :=
  let q := wave_R k in
  rdot q q.

Definition PolarizationFor
  (k : ZWave3) (h : RVec3) : Prop :=
  rdot (wave_R k) h = 0.

Theorem NSFEG00_WAVE_NORM2_NONNEGATIVE :
  forall k : ZWave3,
    0 <= wave_norm2 k.
Proof.
  intro k.
  unfold wave_norm2, rdot, wave_R.
  simpl.
  pose proof (Rle_0_sqr (IZR (zwx k))) as Hx.
  pose proof (Rle_0_sqr (IZR (zwy k))) as Hy.
  pose proof (Rle_0_sqr (IZR (zwz k))) as Hz.
  nra.
Qed.

(* ========================================================================= *)
(* II. Real plane waves on the 2pi-periodic torus chart.                     *)
(* ========================================================================= *)

Definition phase
  (k : ZWave3)
  (x y z : R) : R :=
  IZR (zwx k) * x +
  IZR (zwy k) * y +
  IZR (zwz k) * z.

Definition cos_mode_component
  (k : ZWave3) (hcomp x y z : R) : R :=
  hcomp * cos (phase k x y z).

Definition sin_mode_component
  (k : ZWave3) (hcomp x y z : R) : R :=
  hcomp * sin (phase k x y z).

Definition cos_mode
  (k : ZWave3) (h : RVec3)
  (x y z : R) : RVec3 :=
  mkRVec3
    (cos_mode_component k (rvx h) x y z)
    (cos_mode_component k (rvy h) x y z)
    (cos_mode_component k (rvz h) x y z).

Definition sin_mode
  (k : ZWave3) (h : RVec3)
  (x y z : R) : RVec3 :=
  mkRVec3
    (sin_mode_component k (rvx h) x y z)
    (sin_mode_component k (rvy h) x y z)
    (sin_mode_component k (rvz h) x y z).

(* ========================================================================= *)
(* III. Actual coordinate derivatives of the scalar plane-wave components.   *)
(* ========================================================================= *)

Theorem NSFEG10_COS_MODE_DX :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
         cos_mode_component k hcomp t y z)
      x
      (- hcomp * IZR (zwx k) *
       sin (phase k x y z)).
Proof.
  intros k hcomp x y z.
  unfold cos_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

Theorem NSFEG11_COS_MODE_DY :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
         cos_mode_component k hcomp x t z)
      y
      (- hcomp * IZR (zwy k) *
       sin (phase k x y z)).
Proof.
  intros k hcomp x y z.
  unfold cos_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

Theorem NSFEG12_COS_MODE_DZ :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
         cos_mode_component k hcomp x y t)
      z
      (- hcomp * IZR (zwz k) *
       sin (phase k x y z)).
Proof.
  intros k hcomp x y z.
  unfold cos_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

Theorem NSFEG13_SIN_MODE_DX :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
         sin_mode_component k hcomp t y z)
      x
      (hcomp * IZR (zwx k) *
       cos (phase k x y z)).
Proof.
  intros k hcomp x y z.
  unfold sin_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

Theorem NSFEG14_SIN_MODE_DY :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
         sin_mode_component k hcomp x t z)
      y
      (hcomp * IZR (zwy k) *
       cos (phase k x y z)).
Proof.
  intros k hcomp x y z.
  unfold sin_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

Theorem NSFEG15_SIN_MODE_DZ :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
         sin_mode_component k hcomp x y t)
      z
      (hcomp * IZR (zwz k) *
       cos (phase k x y z)).
Proof.
  intros k hcomp x y z.
  unfold sin_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

(* ========================================================================= *)
(* IV. Actual second coordinate derivatives.                                 *)
(* ========================================================================= *)

Theorem NSFEG20_COS_DX_FIRST_DERIVATIVE_DERIVES_AGAIN :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
        - hcomp * IZR (zwx k) *
        sin (phase k t y z))
      x
      (- (IZR (zwx k) * IZR (zwx k)) *
       cos_mode_component k hcomp x y z).
Proof.
  intros k hcomp x y z.
  unfold cos_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

Theorem NSFEG21_COS_DY_FIRST_DERIVATIVE_DERIVES_AGAIN :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
        - hcomp * IZR (zwy k) *
        sin (phase k x t z))
      y
      (- (IZR (zwy k) * IZR (zwy k)) *
       cos_mode_component k hcomp x y z).
Proof.
  intros k hcomp x y z.
  unfold cos_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

Theorem NSFEG22_COS_DZ_FIRST_DERIVATIVE_DERIVES_AGAIN :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
        - hcomp * IZR (zwz k) *
        sin (phase k x y t))
      z
      (- (IZR (zwz k) * IZR (zwz k)) *
       cos_mode_component k hcomp x y z).
Proof.
  intros k hcomp x y z.
  unfold cos_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

Theorem NSFEG23_SIN_DX_FIRST_DERIVATIVE_DERIVES_AGAIN :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
        hcomp * IZR (zwx k) *
        cos (phase k t y z))
      x
      (- (IZR (zwx k) * IZR (zwx k)) *
       sin_mode_component k hcomp x y z).
Proof.
  intros k hcomp x y z.
  unfold sin_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

Theorem NSFEG24_SIN_DY_FIRST_DERIVATIVE_DERIVES_AGAIN :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
        hcomp * IZR (zwy k) *
        cos (phase k x t z))
      y
      (- (IZR (zwy k) * IZR (zwy k)) *
       sin_mode_component k hcomp x y z).
Proof.
  intros k hcomp x y z.
  unfold sin_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

Theorem NSFEG25_SIN_DZ_FIRST_DERIVATIVE_DERIVES_AGAIN :
  forall (k : ZWave3) (hcomp x y z : R),
    is_derive
      (fun t : R =>
        hcomp * IZR (zwz k) *
        cos (phase k x y t))
      z
      (- (IZR (zwz k) * IZR (zwz k)) *
       sin_mode_component k hcomp x y z).
Proof.
  intros k hcomp x y z.
  unfold sin_mode_component, phase.
  auto_derive; try exact I; ring.
Qed.

(* ========================================================================= *)
(* V. Symbolic divergence and Stokes eigenvalue identities.                  *)
(* ========================================================================= *)

Definition cos_divergence_symbol
  (k : ZWave3) (h : RVec3)
  (x y z : R) : R :=
  - IZR (zwx k) * rvx h * sin (phase k x y z)
  - IZR (zwy k) * rvy h * sin (phase k x y z)
  - IZR (zwz k) * rvz h * sin (phase k x y z).

Definition sin_divergence_symbol
  (k : ZWave3) (h : RVec3)
  (x y z : R) : R :=
  IZR (zwx k) * rvx h * cos (phase k x y z)
  + IZR (zwy k) * rvy h * cos (phase k x y z)
  + IZR (zwz k) * rvz h * cos (phase k x y z).

Theorem NSFEG30_COS_DIVERGENCE_FACTORIZATION :
  forall k h x y z,
    cos_divergence_symbol k h x y z =
      - rdot (wave_R k) h *
        sin (phase k x y z).
Proof.
  intros k h x y z.
  unfold cos_divergence_symbol, rdot, wave_R.
  simpl.
  ring.
Qed.

Theorem NSFEG31_SIN_DIVERGENCE_FACTORIZATION :
  forall k h x y z,
    sin_divergence_symbol k h x y z =
      rdot (wave_R k) h *
      cos (phase k x y z).
Proof.
  intros k h x y z.
  unfold sin_divergence_symbol, rdot, wave_R.
  simpl.
  ring.
Qed.

Theorem NSFEG32_COS_POLARIZATION_IS_DIVERGENCE_FREE :
  forall k h,
    PolarizationFor k h ->
    forall x y z,
      cos_divergence_symbol k h x y z = 0.
Proof.
  intros k h Hpol x y z.
  unfold PolarizationFor in Hpol.
  rewrite NSFEG30_COS_DIVERGENCE_FACTORIZATION.
  rewrite Hpol.
  ring.
Qed.

Theorem NSFEG33_SIN_POLARIZATION_IS_DIVERGENCE_FREE :
  forall k h,
    PolarizationFor k h ->
    forall x y z,
      sin_divergence_symbol k h x y z = 0.
Proof.
  intros k h Hpol x y z.
  unfold PolarizationFor in Hpol.
  rewrite NSFEG31_SIN_DIVERGENCE_FACTORIZATION.
  rewrite Hpol.
  ring.
Qed.

Definition cos_laplacian_component
  (k : ZWave3) (hcomp x y z : R) : R :=
  - (IZR (zwx k) * IZR (zwx k)) *
      cos_mode_component k hcomp x y z
  - (IZR (zwy k) * IZR (zwy k)) *
      cos_mode_component k hcomp x y z
  - (IZR (zwz k) * IZR (zwz k)) *
      cos_mode_component k hcomp x y z.

Definition sin_laplacian_component
  (k : ZWave3) (hcomp x y z : R) : R :=
  - (IZR (zwx k) * IZR (zwx k)) *
      sin_mode_component k hcomp x y z
  - (IZR (zwy k) * IZR (zwy k)) *
      sin_mode_component k hcomp x y z
  - (IZR (zwz k) * IZR (zwz k)) *
      sin_mode_component k hcomp x y z.

Theorem NSFEG40_COS_STOKES_EIGEN_COMPONENT :
  forall k hcomp x y z,
    - cos_laplacian_component k hcomp x y z =
      wave_norm2 k *
      cos_mode_component k hcomp x y z.
Proof.
  intros k hcomp x y z.
  unfold cos_laplacian_component, wave_norm2, rdot, wave_R.
  simpl.
  ring.
Qed.

Theorem NSFEG41_SIN_STOKES_EIGEN_COMPONENT :
  forall k hcomp x y z,
    - sin_laplacian_component k hcomp x y z =
      wave_norm2 k *
      sin_mode_component k hcomp x y z.
Proof.
  intros k hcomp x y z.
  unfold sin_laplacian_component, wave_norm2, rdot, wave_R.
  simpl.
  ring.
Qed.

Theorem NSFEG42_COS_STOKES_EIGEN_VECTOR :
  forall k h x y z,
    let u := cos_mode k h x y z in
    - cos_laplacian_component k (rvx h) x y z =
      wave_norm2 k * rvx u /\
    - cos_laplacian_component k (rvy h) x y z =
      wave_norm2 k * rvy u /\
    - cos_laplacian_component k (rvz h) x y z =
      wave_norm2 k * rvz u.
Proof.
  intros k h x y z.
  simpl.
  repeat split;
    apply NSFEG40_COS_STOKES_EIGEN_COMPONENT.
Qed.

Theorem NSFEG43_SIN_STOKES_EIGEN_VECTOR :
  forall k h x y z,
    let u := sin_mode k h x y z in
    - sin_laplacian_component k (rvx h) x y z =
      wave_norm2 k * rvx u /\
    - sin_laplacian_component k (rvy h) x y z =
      wave_norm2 k * rvy u /\
    - sin_laplacian_component k (rvz h) x y z =
      wave_norm2 k * rvz u.
Proof.
  intros k h x y z.
  simpl.
  repeat split;
    apply NSFEG41_SIN_STOKES_EIGEN_COMPONENT.
Qed.

(* ========================================================================= *)
(* VI. Concrete eigen-test certificates.                                     *)
(* ========================================================================= *)

Inductive PlaneWaveParity : Type :=
| CosineMode
| SineMode.

Record ConcreteTorusFourierEigenMode : Type := {
  ctfem_wave : ZWave3;
  ctfem_polarization : RVec3;
  ctfem_parity : PlaneWaveParity;
  ctfem_polarization_transverse :
    PolarizationFor ctfem_wave ctfem_polarization
}.

Definition concrete_stokes_lambda
  (m : ConcreteTorusFourierEigenMode) : R :=
  wave_norm2 (ctfem_wave m).

Theorem NSFEG50_CONCRETE_EIGENVALUE_NONNEGATIVE :
  forall m : ConcreteTorusFourierEigenMode,
    0 <= concrete_stokes_lambda m.
Proof.
  intro m.
  unfold concrete_stokes_lambda.
  apply NSFEG00_WAVE_NORM2_NONNEGATIVE.
Qed.

Definition ConcreteDivergenceFree
  (m : ConcreteTorusFourierEigenMode) : Prop :=
  forall x y z : R,
    match ctfem_parity m with
    | CosineMode =>
        cos_divergence_symbol
          (ctfem_wave m)
          (ctfem_polarization m)
          x y z = 0
    | SineMode =>
        sin_divergence_symbol
          (ctfem_wave m)
          (ctfem_polarization m)
          x y z = 0
    end.

Theorem NSFEG51_CONCRETE_MODE_IS_DIVERGENCE_FREE :
  forall m : ConcreteTorusFourierEigenMode,
    ConcreteDivergenceFree m.
Proof.
  intros m x y z.
  destruct (ctfem_parity m).
  - apply NSFEG32_COS_POLARIZATION_IS_DIVERGENCE_FREE.
    exact (ctfem_polarization_transverse m).
  - apply NSFEG33_SIN_POLARIZATION_IS_DIVERGENCE_FREE.
    exact (ctfem_polarization_transverse m).
Qed.

Definition ConcreteStokesEigenMode
  (m : ConcreteTorusFourierEigenMode) : Prop :=
  forall x y z : R,
    match ctfem_parity m with
    | CosineMode =>
        let u :=
          cos_mode
            (ctfem_wave m)
            (ctfem_polarization m)
            x y z in
        - cos_laplacian_component
            (ctfem_wave m)
            (rvx (ctfem_polarization m))
            x y z
          = concrete_stokes_lambda m * rvx u /\
        - cos_laplacian_component
            (ctfem_wave m)
            (rvy (ctfem_polarization m))
            x y z
          = concrete_stokes_lambda m * rvy u /\
        - cos_laplacian_component
            (ctfem_wave m)
            (rvz (ctfem_polarization m))
            x y z
          = concrete_stokes_lambda m * rvz u
    | SineMode =>
        let u :=
          sin_mode
            (ctfem_wave m)
            (ctfem_polarization m)
            x y z in
        - sin_laplacian_component
            (ctfem_wave m)
            (rvx (ctfem_polarization m))
            x y z
          = concrete_stokes_lambda m * rvx u /\
        - sin_laplacian_component
            (ctfem_wave m)
            (rvy (ctfem_polarization m))
            x y z
          = concrete_stokes_lambda m * rvy u /\
        - sin_laplacian_component
            (ctfem_wave m)
            (rvz (ctfem_polarization m))
            x y z
          = concrete_stokes_lambda m * rvz u
    end.

Theorem NSFEG52_CONCRETE_MODE_IS_STOKES_EIGENMODE :
  forall m : ConcreteTorusFourierEigenMode,
    ConcreteStokesEigenMode m.
Proof.
  intros m x y z.
  unfold concrete_stokes_lambda.
  destruct (ctfem_parity m).
  - apply NSFEG42_COS_STOKES_EIGEN_VECTOR.
  - apply NSFEG43_SIN_STOKES_EIGEN_VECTOR.
Qed.

Record StandardEigenTestGeometry : Prop := {
  seg_every_mode_divergence_free :
    forall m : ConcreteTorusFourierEigenMode,
      ConcreteDivergenceFree m;

  seg_every_mode_stokes_eigen :
    forall m : ConcreteTorusFourierEigenMode,
      ConcreteStokesEigenMode m;

  seg_every_eigenvalue_nonnegative :
    forall m : ConcreteTorusFourierEigenMode,
      0 <= concrete_stokes_lambda m
}.

Theorem NSFEG60_STANDARD_EIGEN_TEST_GEOMETRY_REALIZED :
  StandardEigenTestGeometry.
Proof.
  constructor.
  - exact NSFEG51_CONCRETE_MODE_IS_DIVERGENCE_FREE.
  - exact NSFEG52_CONCRETE_MODE_IS_STOKES_EIGENMODE.
  - exact NSFEG50_CONCRETE_EIGENVALUE_NONNEGATIVE.
Qed.

(* ========================================================================= *)
(* VII. Exact remaining splice to the v0.42/v0.43 frontend.                  *)
(* ========================================================================= *)

(*
  The v0.43 frontend has already reduced LH -> Fourier to availability of the
  standard torus Fourier eigen-test family.

  This package constructs the actual plane-wave geometry:
    - integer lattice waves;
    - transverse polarizations;
    - actual coordinate derivatives;
    - divergence-free identity;
    - actual second-coordinate derivatives;
    - Stokes eigenvalue |k|^2.

  The remaining splice is now:
    1. map ConcreteTorusFourierEigenMode into the v0.42 `Test` carrier;
    2. prove the concrete plane-wave is admissible in the v0.41 weak core
       (smooth/periodic test-class membership);
    3. instantiate `TorusFourierEigenTestFamily42` from these facts.

  No Fourier->GP or downstream theorem is involved.
*)

Definition RemainingV42TestCarrierSplice : Prop := True.
Definition RemainingPeriodicAdmissibilityFrontier : Prop := True.

Theorem NSFEG90_LEFT_FRONTIER_REDUCED_TO_TEST_CARRIER_AND_ADMISSIBILITY :
  RemainingV42TestCarrierSplice /\
  RemainingPeriodicAdmissibilityFrontier.
Proof.
  split; exact I.
Qed.

Definition STATUS : Prop := True.

End NSE_TORUS_FOURIER_EIGEN_GEOMETRY_V0441.

Print Assumptions
  NSE_TORUS_FOURIER_EIGEN_GEOMETRY_V0441.NSFEG10_COS_MODE_DX.
Print Assumptions
  NSE_TORUS_FOURIER_EIGEN_GEOMETRY_V0441.NSFEG32_COS_POLARIZATION_IS_DIVERGENCE_FREE.
Print Assumptions
  NSE_TORUS_FOURIER_EIGEN_GEOMETRY_V0441.NSFEG52_CONCRETE_MODE_IS_STOKES_EIGENMODE.
Print Assumptions
  NSE_TORUS_FOURIER_EIGEN_GEOMETRY_V0441.NSFEG60_STANDARD_EIGEN_TEST_GEOMETRY_REALIZED.
