From Stdlib Require Import String.
Require Import NSE_CLAY_FEFFERMAN_FRAMEWORK.
Require Import awpi_nse_torus_fourier_periodic_admissibility_v0_45_1.
Require Import awpi_nse_lh_torus_fourier_tests_v0_44_3.
Require Import NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.
Require Import NSE_R3_FORCED_GP_DIAMOND_SEPARATRIX.

Module CLAY_FEFFERMAN_D_T3_FORCED_BREAKDOWN.
Module FW := CLAY_FEFFERMAN_FRAMEWORK.
Module TPER := NSE_TORUS_FOURIER_PERIODIC_ADMISSIBILITY_V0451.

Theorem D00_PERIODIC_FORCE_FRONTEND_GEOMETRY_READY :
  TPER.FullConcretePlaneWaveFamilyGeometry.
Proof. exact FW.FW10_TORUS_PLANE_WAVE_GEOMETRY_READY. Qed.

Section D_STATEMENT.
Context {InitialData Force SmoothSolution : Type}.
Variable T3InitialAdmissible : InitialData -> Prop.
Variable T3ClayForceAdmissible : Force -> Prop.
Variable T3ZeroForce : Force.
Variable T3SmoothForcedSolution : InitialData -> Force -> SmoothSolution -> Prop.
Variable T3CriticalClosed : InitialData -> Force -> Prop.
Variable T3IntrinsicRegularForce : Force -> Prop.

Definition FEFFERMAN_D : Prop :=
  exists u0 : InitialData,
  exists f : Force,
    T3InitialAdmissible u0 /\
    T3ClayForceAdmissible f /\
    ~ exists sol : SmoothSolution, T3SmoothForcedSolution u0 f sol.

Hypothesis T3_DOMAIN_DIAMOND :
  FW.DomainDiamondClosure
    T3InitialAdmissible T3ClayForceAdmissible T3ZeroForce
    T3SmoothForcedSolution T3CriticalClosed T3IntrinsicRegularForce.

Theorem D10_ANY_FEFFERMAN_D_COUNTEREXAMPLE_ESCAPES_PERIODIC_INTRINSIC_CLASS :
  FEFFERMAN_D ->
  exists f : Force,
    T3ClayForceAdmissible f /\ ~ T3IntrinsicRegularForce f.
Proof.
  intros [u0 [f [Hu0 [Hf Hbad]]]].
  exists f. split; [exact Hf|].
  intro Hreg.
  apply Hbad.
  destruct T3_DOMAIN_DIAMOND as [Hzero HzeroReg Hclose Hexit].
  apply Hexit.
  exact (Hclose u0 f Hu0 Hf Hreg).
Qed.

Hypothesis D_CLAY_FORCES_EMBED_INTRINSIC :
  forall f : Force, T3ClayForceAdmissible f -> T3IntrinsicRegularForce f.

Theorem D20_T3_DOMAIN_DIAMOND_PLUS_CLAY_FORCE_EMBEDDING_EXCLUDES_FEFFERMAN_D :
  ~ FEFFERMAN_D.
Proof.
  intro HD.
  destruct (D10_ANY_FEFFERMAN_D_COUNTEREXAMPLE_ESCAPES_PERIODIC_INTRINSIC_CLASS HD)
    as [f [Hf Hnot]].
  exact (Hnot (D_CLAY_FORCES_EMBED_INTRINSIC f Hf)).
Qed.

Definition D_STATUS : string :=
  "D_T3_BREAKDOWN_REDUCED_TO_SHARED_T3_DOMAIN_DIAMOND_PLUS_CLAY_FORCE_EMBEDDING"%string.
End D_STATEMENT.
End CLAY_FEFFERMAN_D_T3_FORCED_BREAKDOWN.

Print CLAY_FEFFERMAN_D_T3_FORCED_BREAKDOWN.D00_PERIODIC_FORCE_FRONTEND_GEOMETRY_READY.
Print CLAY_FEFFERMAN_D_T3_FORCED_BREAKDOWN.D10_ANY_FEFFERMAN_D_COUNTEREXAMPLE_ESCAPES_PERIODIC_INTRINSIC_CLASS.
Print CLAY_FEFFERMAN_D_T3_FORCED_BREAKDOWN.D20_T3_DOMAIN_DIAMOND_PLUS_CLAY_FORCE_EMBEDDING_EXCLUDES_FEFFERMAN_D.
