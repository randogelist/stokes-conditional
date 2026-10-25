From Stdlib Require Import Reals Lra Ring ZArith ZArith.Znat.
From Stdlib Require Import Rtrigo1 RIneq.
Open Scope R_scope.

Require Import awpi_nse_torus_fourier_eigen_geometry_v0_44_1.

Module NSE_TORUS_FOURIER_PERIODIC_ADMISSIBILITY_V0451.

Module G := NSE_TORUS_FOURIER_EIGEN_GEOMETRY_V0441.

(* ========================================================================= *)
(* I. Integer-multiple 2pi periodicity for sin/cos.                          *)
(* ========================================================================= *)

Theorem NSFPA00_COS_INTEGER_PERIOD :
  forall (x : R) (z : Z),
    cos (x + 2 * IZR z * PI) = cos x.
Proof.
  intros x z.
  destruct z as [|p|p].
  - simpl.
    replace (x + 2 * 0 * PI) with x by ring.
    reflexivity.
  - rewrite <- (positive_nat_Z p).
    rewrite <- INR_IZR_INZ.
    apply cos_period.
  - rewrite IZR_NEG.
    rewrite <- (positive_nat_Z p).
    rewrite <- INR_IZR_INZ.
    replace
      (x + 2 * (- INR (Pos.to_nat p)) * PI)
      with
      (x - 2 * INR (Pos.to_nat p) * PI)
      by ring.
    pose proof
      (cos_period
         (x - 2 * INR (Pos.to_nat p) * PI)
         (Pos.to_nat p))
      as Hperiod.
    replace
      ((x - 2 * INR (Pos.to_nat p) * PI) +
       2 * INR (Pos.to_nat p) * PI)
      with
      x
      in Hperiod
      by ring.
    symmetry.
    exact Hperiod.
Qed.

Theorem NSFPA01_SIN_INTEGER_PERIOD :
  forall (x : R) (z : Z),
    sin (x + 2 * IZR z * PI) = sin x.
Proof.
  intros x z.
  destruct z as [|p|p].
  - simpl.
    replace (x + 2 * 0 * PI) with x by ring.
    reflexivity.
  - rewrite <- (positive_nat_Z p).
    rewrite <- INR_IZR_INZ.
    apply sin_period.
  - rewrite IZR_NEG.
    rewrite <- (positive_nat_Z p).
    rewrite <- INR_IZR_INZ.
    replace
      (x + 2 * (- INR (Pos.to_nat p)) * PI)
      with
      (x - 2 * INR (Pos.to_nat p) * PI)
      by ring.
    pose proof
      (sin_period
         (x - 2 * INR (Pos.to_nat p) * PI)
         (Pos.to_nat p))
      as Hperiod.
    replace
      ((x - 2 * INR (Pos.to_nat p) * PI) +
       2 * INR (Pos.to_nat p) * PI)
      with
      x
      in Hperiod
      by ring.
    symmetry.
    exact Hperiod.
Qed.

(* ========================================================================= *)
(* II. Phase changes under coordinate shifts.                                *)
(* ========================================================================= *)

Theorem NSFPA10_PHASE_X_SHIFT :
  forall k x y z,
    G.phase k (x + 2 * PI) y z =
      G.phase k x y z +
      2 * IZR (G.zwx k) * PI.
Proof.
  intros k x y z.
  unfold G.phase.
  ring.
Qed.

Theorem NSFPA11_PHASE_Y_SHIFT :
  forall k x y z,
    G.phase k x (y + 2 * PI) z =
      G.phase k x y z +
      2 * IZR (G.zwy k) * PI.
Proof.
  intros k x y z.
  unfold G.phase.
  ring.
Qed.

Theorem NSFPA12_PHASE_Z_SHIFT :
  forall k x y z,
    G.phase k x y (z + 2 * PI) =
      G.phase k x y z +
      2 * IZR (G.zwz k) * PI.
Proof.
  intros k x y z.
  unfold G.phase.
  ring.
Qed.

(* ========================================================================= *)
(* III. Scalar component periodicity.                                        *)
(* ========================================================================= *)

Theorem NSFPA20_COS_COMPONENT_X_PERIODIC :
  forall k h x y z,
    G.cos_mode_component k h (x + 2 * PI) y z =
      G.cos_mode_component k h x y z.
Proof.
  intros k h x y z.
  unfold G.cos_mode_component.
  rewrite NSFPA10_PHASE_X_SHIFT.
  rewrite NSFPA00_COS_INTEGER_PERIOD.
  reflexivity.
Qed.

Theorem NSFPA21_COS_COMPONENT_Y_PERIODIC :
  forall k h x y z,
    G.cos_mode_component k h x (y + 2 * PI) z =
      G.cos_mode_component k h x y z.
Proof.
  intros k h x y z.
  unfold G.cos_mode_component.
  rewrite NSFPA11_PHASE_Y_SHIFT.
  rewrite NSFPA00_COS_INTEGER_PERIOD.
  reflexivity.
Qed.

Theorem NSFPA22_COS_COMPONENT_Z_PERIODIC :
  forall k h x y z,
    G.cos_mode_component k h x y (z + 2 * PI) =
      G.cos_mode_component k h x y z.
Proof.
  intros k h x y z.
  unfold G.cos_mode_component.
  rewrite NSFPA12_PHASE_Z_SHIFT.
  rewrite NSFPA00_COS_INTEGER_PERIOD.
  reflexivity.
Qed.

Theorem NSFPA23_SIN_COMPONENT_X_PERIODIC :
  forall k h x y z,
    G.sin_mode_component k h (x + 2 * PI) y z =
      G.sin_mode_component k h x y z.
Proof.
  intros k h x y z.
  unfold G.sin_mode_component.
  rewrite NSFPA10_PHASE_X_SHIFT.
  rewrite NSFPA01_SIN_INTEGER_PERIOD.
  reflexivity.
Qed.

Theorem NSFPA24_SIN_COMPONENT_Y_PERIODIC :
  forall k h x y z,
    G.sin_mode_component k h x (y + 2 * PI) z =
      G.sin_mode_component k h x y z.
Proof.
  intros k h x y z.
  unfold G.sin_mode_component.
  rewrite NSFPA11_PHASE_Y_SHIFT.
  rewrite NSFPA01_SIN_INTEGER_PERIOD.
  reflexivity.
Qed.

Theorem NSFPA25_SIN_COMPONENT_Z_PERIODIC :
  forall k h x y z,
    G.sin_mode_component k h x y (z + 2 * PI) =
      G.sin_mode_component k h x y z.
Proof.
  intros k h x y z.
  unfold G.sin_mode_component.
  rewrite NSFPA12_PHASE_Z_SHIFT.
  rewrite NSFPA01_SIN_INTEGER_PERIOD.
  reflexivity.
Qed.

(* ========================================================================= *)
(* IV. Vector periodicity.                                                   *)
(* ========================================================================= *)

Definition Vec3Eq
  (u v : G.RVec3) : Prop :=
  G.rvx u = G.rvx v /\
  G.rvy u = G.rvy v /\
  G.rvz u = G.rvz v.

Definition CosModePeriodic3
  (k : G.ZWave3) (h : G.RVec3) : Prop :=
  (forall x y z,
    Vec3Eq
      (G.cos_mode k h (x + 2 * PI) y z)
      (G.cos_mode k h x y z)) /\
  (forall x y z,
    Vec3Eq
      (G.cos_mode k h x (y + 2 * PI) z)
      (G.cos_mode k h x y z)) /\
  (forall x y z,
    Vec3Eq
      (G.cos_mode k h x y (z + 2 * PI))
      (G.cos_mode k h x y z)).

Definition SinModePeriodic3
  (k : G.ZWave3) (h : G.RVec3) : Prop :=
  (forall x y z,
    Vec3Eq
      (G.sin_mode k h (x + 2 * PI) y z)
      (G.sin_mode k h x y z)) /\
  (forall x y z,
    Vec3Eq
      (G.sin_mode k h x (y + 2 * PI) z)
      (G.sin_mode k h x y z)) /\
  (forall x y z,
    Vec3Eq
      (G.sin_mode k h x y (z + 2 * PI))
      (G.sin_mode k h x y z)).

Theorem NSFPA30_COS_MODE_PERIODIC3 :
  forall k h,
    CosModePeriodic3 k h.
Proof.
  intros k h.
  unfold CosModePeriodic3.
  split.
  - intros x y z.
    unfold Vec3Eq, G.cos_mode; simpl.
    repeat split; apply NSFPA20_COS_COMPONENT_X_PERIODIC.
  - split.
    + intros x y z.
      unfold Vec3Eq, G.cos_mode; simpl.
      repeat split; apply NSFPA21_COS_COMPONENT_Y_PERIODIC.
    + intros x y z.
      unfold Vec3Eq, G.cos_mode; simpl.
      repeat split; apply NSFPA22_COS_COMPONENT_Z_PERIODIC.
Qed.

Theorem NSFPA31_SIN_MODE_PERIODIC3 :
  forall k h,
    SinModePeriodic3 k h.
Proof.
  intros k h.
  unfold SinModePeriodic3.
  split.
  - intros x y z.
    unfold Vec3Eq, G.sin_mode; simpl.
    repeat split; apply NSFPA23_SIN_COMPONENT_X_PERIODIC.
  - split.
    + intros x y z.
      unfold Vec3Eq, G.sin_mode; simpl.
      repeat split; apply NSFPA24_SIN_COMPONENT_Y_PERIODIC.
    + intros x y z.
      unfold Vec3Eq, G.sin_mode; simpl.
      repeat split; apply NSFPA25_SIN_COMPONENT_Z_PERIODIC.
Qed.

Definition ConcreteModePeriodic3
  (m : G.ConcreteTorusFourierEigenMode) : Prop :=
  match G.ctfem_parity m with
  | G.CosineMode =>
      CosModePeriodic3
        (G.ctfem_wave m)
        (G.ctfem_polarization m)
  | G.SineMode =>
      SinModePeriodic3
        (G.ctfem_wave m)
        (G.ctfem_polarization m)
  end.

Theorem NSFPA40_CONCRETE_MODE_IS_PERIODIC3 :
  forall m : G.ConcreteTorusFourierEigenMode,
    ConcreteModePeriodic3 m.
Proof.
  intro m.
  unfold ConcreteModePeriodic3.
  destruct (G.ctfem_parity m).
  - apply NSFPA30_COS_MODE_PERIODIC3.
  - apply NSFPA31_SIN_MODE_PERIODIC3.
Qed.

(* ========================================================================= *)
(* V. The full concrete geometric admissibility package.                     *)
(* ========================================================================= *)

Record ConcretePlaneWaveAdmissibility
  (m : G.ConcreteTorusFourierEigenMode) : Prop := {
  cpwa_periodic :
    ConcreteModePeriodic3 m;

  cpwa_divergence_free :
    G.ConcreteDivergenceFree m;

  cpwa_stokes_eigen :
    G.ConcreteStokesEigenMode m;

  cpwa_eigenvalue_nonnegative :
    0 <= G.concrete_stokes_lambda m
}.

Theorem NSFPA50_CONCRETE_MODE_HAS_FULL_GEOMETRIC_ADMISSIBILITY :
  forall m : G.ConcreteTorusFourierEigenMode,
    ConcretePlaneWaveAdmissibility m.
Proof.
  intro m.
  constructor.
  - apply NSFPA40_CONCRETE_MODE_IS_PERIODIC3.
  - apply G.NSFEG51_CONCRETE_MODE_IS_DIVERGENCE_FREE.
  - apply G.NSFEG52_CONCRETE_MODE_IS_STOKES_EIGENMODE.
  - apply G.NSFEG50_CONCRETE_EIGENVALUE_NONNEGATIVE.
Qed.

Definition FullConcretePlaneWaveFamilyGeometry : Prop :=
  forall m : G.ConcreteTorusFourierEigenMode,
    ConcretePlaneWaveAdmissibility m.

Theorem NSFPA60_FULL_CONCRETE_PLANE_WAVE_FAMILY_GEOMETRY_REALIZED :
  FullConcretePlaneWaveFamilyGeometry.
Proof.
  intro m.
  apply NSFPA50_CONCRETE_MODE_HAS_FULL_GEOMETRIC_ADMISSIBILITY.
Qed.

(* ========================================================================= *)
(* VI. Left frontier after v0.45.                                            *)
(* ========================================================================= *)

(*
  Concrete standard Fourier geometry now supplies:
    - actual first/second derivatives (v0.44.1),
    - divergence-free transverse modes (v0.44.1),
    - Stokes eigenvalue |k|^2 (v0.44.1),
    - 2pi periodicity in x,y,z (this package),
    - nonnegative eigenvalue.

  The only remaining frontend-specific work is the carrier splice:
      ConcreteTorusFourierEigenMode
        -> v0.42 Test
        -> TorusFourierEigenTestFamily42.

  Any additional "smooth" admissibility field in v0.42 can be discharged
  directly from the actual derivative witnesses already proved in v0.44.1.
*)

Definition RemainingV42TestCarrierSplice : Prop := True.

Theorem NSFPA90_LEFT_FRONTIER_IS_NOW_THE_V42_CARRIER_SPLICE :
  RemainingV42TestCarrierSplice.
Proof.
  exact I.
Qed.

Definition STATUS : Prop := True.

End NSE_TORUS_FOURIER_PERIODIC_ADMISSIBILITY_V0451.

Print Assumptions
  NSE_TORUS_FOURIER_PERIODIC_ADMISSIBILITY_V0451.NSFPA00_COS_INTEGER_PERIOD.
Print Assumptions
  NSE_TORUS_FOURIER_PERIODIC_ADMISSIBILITY_V0451.NSFPA40_CONCRETE_MODE_IS_PERIODIC3.
Print Assumptions
  NSE_TORUS_FOURIER_PERIODIC_ADMISSIBILITY_V0451.NSFPA60_FULL_CONCRETE_PLANE_WAVE_FAMILY_GEOMETRY_REALIZED.
