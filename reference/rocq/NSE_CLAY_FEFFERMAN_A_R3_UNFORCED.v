From Stdlib Require Import Reals String.
Require Import NSE_CLAY_FEFFERMAN_FRAMEWORK.
Require Import NSE_R3_FORCED_GP_DIAMOND_STORAGE_BRIDGE.
Require Import NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.

Module CLAY_FEFFERMAN_A_R3_UNFORCED.
Module FW := CLAY_FEFFERMAN_FRAMEWORK.
Open Scope R_scope.

Section A_STATEMENT.
Context {InitialData Force SmoothSolution Cut Time : Type}.
Variable R3InitialAdmissible : InitialData -> Prop.
Variable R3ForceAdmissible : Force -> Prop.
Variable R3ZeroForce : Force.
Variable R3SmoothSolution : InitialData -> Force -> SmoothSolution -> Prop.
Variable R3IntrinsicRegularForce : Force -> Prop.
Variable R3CriticalMass : InitialData -> Force -> Time -> R.

Definition FEFFERMAN_A : Prop :=
  forall u0 : InitialData,
    R3InitialAdmissible u0 ->
    exists sol : SmoothSolution, R3SmoothSolution u0 R3ZeroForce sol.

Hypothesis R3_CONCRETE_STORAGE_DIAMOND :
  @FW.ConcreteR3StorageDiamondClosure
    InitialData Force SmoothSolution Cut Time
    R3InitialAdmissible R3ForceAdmissible R3ZeroForce
    R3SmoothSolution R3IntrinsicRegularForce R3CriticalMass.

Theorem A10_R3_CONCRETE_STORAGE_DIAMOND_GIVES_FEFFERMAN_A :
  FEFFERMAN_A.
Proof.
  intros u0 Hu0.
  destruct R3_CONCRETE_STORAGE_DIAMOND as [Hzero HzeroReg Hstore Hexit].
  destruct (Hstore u0 R3ZeroForce Hu0 Hzero HzeroReg) as [w _].
  apply Hexit.
  exact (FW.FW40_STORAGE_TERMINAL_WITNESS_GIVES_UNIFORM_CRITICAL_BOUND
           R3CriticalMass u0 R3ZeroForce w).
Qed.

Definition A_STATUS : string :=
  "A_R3_UNFORCED_REDUCED_TO_CONCRETE_STORAGE_WITNESS_PLUS_CLASSICAL_EXIT"%string.
End A_STATEMENT.
End CLAY_FEFFERMAN_A_R3_UNFORCED.

Print CLAY_FEFFERMAN_A_R3_UNFORCED.A10_R3_CONCRETE_STORAGE_DIAMOND_GIVES_FEFFERMAN_A.
