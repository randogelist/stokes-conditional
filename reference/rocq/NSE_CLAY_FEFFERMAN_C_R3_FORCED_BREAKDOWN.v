From Stdlib Require Import Reals String.
Require Import NSE_CLAY_FEFFERMAN_FRAMEWORK.
Require Import NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.
Require Import NSE_R3_FORCED_GP_DIAMOND_SEPARATRIX.
Require Import NSE_R3_FORCED_GP_DIAMOND_STORAGE_BRIDGE.

Module CLAY_FEFFERMAN_C_R3_FORCED_BREAKDOWN.
Module FW := CLAY_FEFFERMAN_FRAMEWORK.
Open Scope R_scope.

Section C_STATEMENT.
Context {InitialData Force SmoothSolution Cut Time : Type}.
Variable R3InitialAdmissible : InitialData -> Prop.
Variable R3ClayForceAdmissible : Force -> Prop.
Variable R3ZeroForce : Force.
Variable R3SmoothForcedSolution : InitialData -> Force -> SmoothSolution -> Prop.
Variable R3IntrinsicRegularForce : Force -> Prop.
Variable R3CriticalMass : InitialData -> Force -> Time -> R.

Definition FEFFERMAN_C : Prop :=
  exists u0 : InitialData,
  exists f : Force,
    R3InitialAdmissible u0 /\
    R3ClayForceAdmissible f /\
    ~ exists sol : SmoothSolution, R3SmoothForcedSolution u0 f sol.

Hypothesis R3_CONCRETE_STORAGE_DIAMOND :
  @FW.ConcreteR3StorageDiamondClosure
    InitialData Force SmoothSolution Cut Time
    R3InitialAdmissible R3ClayForceAdmissible R3ZeroForce
    R3SmoothForcedSolution R3IntrinsicRegularForce R3CriticalMass.

Theorem C10_ANY_FEFFERMAN_C_COUNTEREXAMPLE_ESCAPES_INTRINSIC_REGULAR_CLASS :
  FEFFERMAN_C ->
  exists f : Force,
    R3ClayForceAdmissible f /\ ~ R3IntrinsicRegularForce f.
Proof.
  intros [u0 [f [Hu0 [Hf Hbad]]]].
  exists f. split; [exact Hf|].
  intro Hreg.
  apply Hbad.
  destruct R3_CONCRETE_STORAGE_DIAMOND as [Hzero HzeroReg Hstore Hexit].
  destruct (Hstore u0 f Hu0 Hf Hreg) as [w _].
  apply Hexit.
  exact (FW.FW40_STORAGE_TERMINAL_WITNESS_GIVES_UNIFORM_CRITICAL_BOUND
           R3CriticalMass u0 f w).
Qed.

Hypothesis C_CLAY_FORCES_EMBED_INTRINSIC :
  forall f : Force, R3ClayForceAdmissible f -> R3IntrinsicRegularForce f.

Theorem C20_R3_CONCRETE_STORAGE_DIAMOND_PLUS_CLAY_FORCE_EMBEDDING_EXCLUDES_FEFFERMAN_C :
  ~ FEFFERMAN_C.
Proof.
  intro HC.
  destruct (C10_ANY_FEFFERMAN_C_COUNTEREXAMPLE_ESCAPES_INTRINSIC_REGULAR_CLASS HC)
    as [f [Hf Hnot]].
  exact (Hnot (C_CLAY_FORCES_EMBED_INTRINSIC f Hf)).
Qed.

Definition C_STATUS : string :=
  "C_R3_BREAKDOWN_REDUCED_TO_CONCRETE_STORAGE_WITNESS_PLUS_CLAY_FORCE_EMBEDDING"%string.
End C_STATEMENT.
End CLAY_FEFFERMAN_C_R3_FORCED_BREAKDOWN.

Print CLAY_FEFFERMAN_C_R3_FORCED_BREAKDOWN.C10_ANY_FEFFERMAN_C_COUNTEREXAMPLE_ESCAPES_INTRINSIC_REGULAR_CLASS.
Print CLAY_FEFFERMAN_C_R3_FORCED_BREAKDOWN.C20_R3_CONCRETE_STORAGE_DIAMOND_PLUS_CLAY_FORCE_EMBEDDING_EXCLUDES_FEFFERMAN_C.
