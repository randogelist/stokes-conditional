From Stdlib Require Import Reals Lra Psatz String.
Require Import NSE_R3_FORCED_GP_DIAMOND_FORCE_ENVELOPE.

Module NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.

Module FE := NSE_R3_FORCED_GP_DIAMOND_FORCE_ENVELOPE.NSE_R3_FORCED_GP_DIAMOND_FORCE_ENVELOPE.

Open Scope R_scope.

(*
  Fractional-Stokes realization of the critical dual geometry.

  The common Hilbert carrier H represents the spectral image.  minus_quarter
  is A^{-1/4} on the force, while three_quarter is A^{3/4} on the state.
  The critical work then factors through the same Hilbert pairing.
*)
Section FRACTIONAL_STOKES.

Variable Force State H : Type.
Variable inner : H -> H -> R.
Variable norm2 : H -> R.
Variable minus_quarter : Force -> H.
Variable three_quarter : State -> H.
Variable force_size2 : Force -> R.
Variable critical_dissipation : State -> R.
Variable critical_work : Force -> State -> R.
Variable riesz_state : Force -> State.

Record FractionalStokesRealization : Prop := {
  fs_norm2_nonnegative :
    forall x : H, 0 <= norm2 x;
  fs_inner_cauchy :
    forall x y : H,
      FE.sq (inner x y) <= norm2 x * norm2 y;
  fs_inner_self :
    forall x : H, inner x x = norm2 x;
  fs_force_size :
    forall f : Force,
      force_size2 f = norm2 (minus_quarter f);
  fs_critical_dissipation :
    forall u : State,
      critical_dissipation u = norm2 (three_quarter u);
  fs_critical_work :
    forall (f : Force) (u : State),
      critical_work f u = inner (minus_quarter f) (three_quarter u);
  fs_riesz_alignment :
    forall f : Force,
      three_quarter (riesz_state f) = minus_quarter f
}.

Definition StokesHMinusHalfNormSq (f : Force) : R :=
  norm2 (minus_quarter f).

Theorem SD01_FRACTIONAL_STOKES_GIVES_CRITICAL_DUAL_GEOMETRY :
  FractionalStokesRealization ->
  @FE.CriticalDualGeometry
    Force State force_size2 critical_dissipation critical_work riesz_state.
Proof.
  intro Hfs.
  destruct Hfs as [Hnonneg Hcauchy Hself Hsize Hdiss Hwork Halign].
  constructor.
  - intro f.
    rewrite Hsize.
    apply Hnonneg.
  - intro u.
    rewrite Hdiss.
    apply Hnonneg.
  - intros f u.
    rewrite Hwork, Hsize, Hdiss.
    apply Hcauchy.
  - intro f.
    rewrite Hdiss, Halign, <- Hsize.
    reflexivity.
  - intro f.
    rewrite Hwork, Halign, Hself, <- Hsize.
    reflexivity.
Qed.

Theorem SD02_STOKES_HMINUSHALF_IS_EXACT_FORCE_SIZE :
  FractionalStokesRealization ->
  forall f : Force,
    force_size2 f = StokesHMinusHalfNormSq f.
Proof.
  intros Hfs f.
  destruct Hfs as [Hnonneg Hcauchy Hself Hsize Hdiss Hwork Halign].
  unfold StokesHMinusHalfNormSq.
  apply Hsize.
Qed.

Theorem SD03_STOKES_HMINUSHALF_IS_LEAST_UNIFORM_WORK_COEFFICIENT :
  FractionalStokesRealization ->
  forall f : Force,
    @FE.UniformWorkCoefficient
      Force State critical_dissipation critical_work
      f (StokesHMinusHalfNormSq f) /\
    forall C : R,
      @FE.UniformWorkCoefficient
        Force State critical_dissipation critical_work f C ->
      StokesHMinusHalfNormSq f <= C.
Proof.
  intros Hfs f.
  pose proof (SD01_FRACTIONAL_STOKES_GIVES_CRITICAL_DUAL_GEOMETRY Hfs) as Hgeo.
  pose proof (@FE.FE03_FORCE_SIZE_EXACTLY_CLASSIFIES_UNIFORM_CRITICAL_WORK
    Force State force_size2 critical_dissipation critical_work riesz_state
    Hgeo f) as Hexact.
  pose proof (SD02_STOKES_HMINUSHALF_IS_EXACT_FORCE_SIZE Hfs f) as Heq.
  rewrite Heq in Hexact.
  exact Hexact.
Qed.

End FRACTIONAL_STOKES.

(*
  R^3 readout.  This is the one genuinely standard spectral fact still needed:
  on divergence-free R^3, the Stokes A^{-1/4} norm is the homogeneous
  H^{-1/2} norm after Leray projection.
*)
Section R3_SOBOLEV_READOUT.

Variable PhysicalForce Force H : Type.
Variable solenoidal_project : PhysicalForce -> Force.
Variable minus_quarter : Force -> H.
Variable norm2 : H -> R.
Variable physical_hminus_half_norm2 : PhysicalForce -> R.

Definition StokesHMinusHalfNormSqR3 (f : PhysicalForce) : R :=
  norm2 (minus_quarter (solenoidal_project f)).

Record R3FractionalStokesSobolevIdentification : Prop := {
  r3_stokes_hminus_half :
    forall f : PhysicalForce,
      StokesHMinusHalfNormSqR3 f = physical_hminus_half_norm2 f
}.

Theorem SD10_R3_STOKES_HMINUSHALF_EQUALS_PHYSICAL_HMINUSHALF :
  R3FractionalStokesSobolevIdentification ->
  forall f : PhysicalForce,
    StokesHMinusHalfNormSqR3 f = physical_hminus_half_norm2 f.
Proof.
  intros HidStruct f.
  destruct HidStruct as [Hid].
  apply Hid.
Qed.

End R3_SOBOLEV_READOUT.

(*
  Time accumulation is formal once the pointwise identity is known.  No new
  Sobolev theorem is required: any extensional time accumulator transports the
  pointwise equality.
*)
Section TIME_ACCUMULATION.

Variable Time PhysicalForce : Type.
Variable stokes_size2 physical_hminus_half_norm2 : PhysicalForce -> R.
Variable accumulate : (Time -> R) -> R.

Record ExtensionalAccumulator : Prop := {
  ea_extensional :
    forall a b : Time -> R,
      (forall t : Time, a t = b t) ->
      accumulate a = accumulate b
}.

Definition TimeAccumulatedStokesForceSize
  (f : Time -> PhysicalForce) : R :=
  accumulate (fun t => stokes_size2 (f t)).

Definition L2TimeHMinusHalfNormSq
  (f : Time -> PhysicalForce) : R :=
  accumulate (fun t => physical_hminus_half_norm2 (f t)).

Theorem SD20_POINTWISE_HMINUSHALF_IDENTIFICATION_GIVES_TIME_IDENTITY :
  ExtensionalAccumulator ->
  (forall f : PhysicalForce,
    stokes_size2 f = physical_hminus_half_norm2 f) ->
  forall f : Time -> PhysicalForce,
    TimeAccumulatedStokesForceSize f = L2TimeHMinusHalfNormSq f.
Proof.
  intros Hacc Hpoint f.
  destruct Hacc as [Hext].
  unfold TimeAccumulatedStokesForceSize, L2TimeHMinusHalfNormSq.
  apply Hext.
  intro t.
  apply Hpoint.
Qed.

End TIME_ACCUMULATION.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY_V0_12_2"%string.

End NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.

Check NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.SD01_FRACTIONAL_STOKES_GIVES_CRITICAL_DUAL_GEOMETRY.
Check NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.SD03_STOKES_HMINUSHALF_IS_LEAST_UNIFORM_WORK_COEFFICIENT.
Check NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.SD20_POINTWISE_HMINUSHALF_IDENTIFICATION_GIVES_TIME_IDENTITY.
