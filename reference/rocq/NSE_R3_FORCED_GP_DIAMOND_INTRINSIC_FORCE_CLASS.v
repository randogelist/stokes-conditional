From Stdlib Require Import Reals Lra Psatz String.
Require Import NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.
Require Import NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.

Module SD := NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.
Module FC := NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.

Open Scope R_scope.

(*
  Intrinsic forced Diamond.

  The external force does not need a BKQR channel decomposition for the
  regularity implication.  The global Stokes critical-dual geometry already
  supplies the exact least uniform work coefficient.  BKQR is therefore
  optional on the force side: it refines where forcing acts, while M7/BKQR
  remains essential for the internal nonlinear transfer.
*)

Section DIRECT_STOKES_FORCE_ABSORPTION.

Variable Force State H : Type.
Variable inner : H -> H -> R.
Variable norm2 : H -> R.
Variable minus_quarter : Force -> H.
Variable three_quarter : State -> H.
Variable force_size2 : Force -> R.
Variable critical_dissipation : State -> R.
Variable critical_work : Force -> State -> R.
Variable riesz_state : Force -> State.

Theorem IF01_GLOBAL_STOKES_FORCE_ABSORPTION :
  @SD.FractionalStokesRealization
    Force State H inner norm2 minus_quarter three_quarter
    force_size2 critical_dissipation critical_work riesz_state ->
  forall (e : R) (f : Force) (u : State),
    0 < e ->
    2 * e * critical_work f u <=
      e * e * critical_dissipation u +
      @SD.StokesHMinusHalfNormSq Force H norm2 minus_quarter f.
Proof.
  intros Hfs e f u He.
  pose proof
    (@SD.SD01_FRACTIONAL_STOKES_GIVES_CRITICAL_DUAL_GEOMETRY
      Force State H inner norm2 minus_quarter three_quarter
      force_size2 critical_dissipation critical_work riesz_state Hfs)
    as Hgeo.
  pose proof
    (@SD.SD02_STOKES_HMINUSHALF_IS_EXACT_FORCE_SIZE
      Force State H inner norm2 minus_quarter three_quarter
      force_size2 critical_dissipation critical_work riesz_state Hfs f)
    as Hsizeeq.
  destruct Hgeo as [Hsize Hdiss Hcs Hrd Hrw].
  pose proof (Hsize f) as Hsize0.
  pose proof (Hdiss u) as Hdiss0.
  pose proof (Hcs f u) as Hquad.
  destruct (Rle_dec 0 (critical_work f u)) as [Hw0|Hwneg].
  - pose proof
      (CE.NSCE00_QUADRATIC_RESISTANT_ACTION_YOUNG
        e (critical_dissipation u) (force_size2 f)
        (critical_work f u)
        He Hdiss0 Hsize0 Hw0 Hquad) as Hy.
    rewrite <- Hsizeeq.
    exact Hy.
  - assert (Hw : critical_work f u < 0) by lra.
    rewrite <- Hsizeeq.
    nra.
Qed.

Theorem IF02_INTRINSIC_FORCE_SIZE_IS_LEAST_UNIFORM_COEFFICIENT :
  @SD.FractionalStokesRealization
    Force State H inner norm2 minus_quarter three_quarter
    force_size2 critical_dissipation critical_work riesz_state ->
  forall f : Force,
    @SD.StokesHMinusHalfNormSq Force H norm2 minus_quarter f = force_size2 f /\
    (forall C : R,
      @NSE_R3_FORCED_GP_DIAMOND_FORCE_ENVELOPE.NSE_R3_FORCED_GP_DIAMOND_FORCE_ENVELOPE.UniformWorkCoefficient
        Force State critical_dissipation critical_work f C ->
      @SD.StokesHMinusHalfNormSq Force H norm2 minus_quarter f <= C).
Proof.
  intros Hfs f.
  split.
  - symmetry.
    apply (@SD.SD02_STOKES_HMINUSHALF_IS_EXACT_FORCE_SIZE
      Force State H inner norm2 minus_quarter three_quarter
      force_size2 critical_dissipation critical_work riesz_state Hfs f).
  - intros C HC.
    pose proof
      (@SD.SD03_STOKES_HMINUSHALF_IS_LEAST_UNIFORM_WORK_COEFFICIENT
        Force State H inner norm2 minus_quarter three_quarter
        force_size2 critical_dissipation critical_work riesz_state Hfs f)
      as Hleast.
    destruct Hleast as [Hcoeff Hminimal].
    apply Hminimal.
    exact HC.
Qed.

End DIRECT_STOKES_FORCE_ABSORPTION.

(*
  Time-dependent class A is defined intrinsically, without naming a Fourier
  Sobolev space.  A classical R^3 H^{-1/2} identification may be attached as
  a readout later, but it is not needed by the regularity implication.
*)
Section INTRINSIC_TIME_CLASS.

Variable Time Force : Type.
Variable intrinsic_force_size2 : Force -> R.
Variable accumulate_until : Time -> (Time -> R) -> R.

Definition intrinsic_force_cost
  (f : Time -> Force) (t : Time) : R :=
  accumulate_until t (fun s => intrinsic_force_size2 (f s)).

Definition IntrinsicCriticalForceClassA (f : Time -> Force) : Prop :=
  FC.BoundedLedger Time (intrinsic_force_cost f).

Variable nu sigma initial_mass : R.
Variable critical_mass critical_dissipation : Time -> R.
Variable internal_cost : Time -> R.
Variable f : Time -> Force.

Theorem IF10_INTRINSIC_FORCE_CLASS_PLUS_INTERNAL_LEDGER_GIVES_REGULARITY :
  FC.ForcedCriticalEnergyBalance
    Time nu sigma initial_mass critical_mass critical_dissipation
    internal_cost (intrinsic_force_cost f) ->
  FC.BoundedLedger Time internal_cost ->
  IntrinsicCriticalForceClassA f ->
  CE.UniformCriticalEnergy Time critical_mass critical_dissipation.
Proof.
  intros Hbal Hint Hforce.
  eapply (@FC.FD02_CLASS_A_GIVES_UNIFORM_CRITICAL_ENERGY
    Time nu sigma initial_mass critical_mass critical_dissipation
    internal_cost (intrinsic_force_cost f)).
  - exact Hbal.
  - split; assumption.
Qed.

End INTRINSIC_TIME_CLASS.

(* Optional classical R^3 readout.  It changes the name of the intrinsic
   space, not the regularity proof. *)
Section OPTIONAL_CLASSICAL_READOUT.

Variable PhysicalForce Force H : Type.
Variable solenoidal_project : PhysicalForce -> Force.
Variable minus_quarter : Force -> H.
Variable norm2 : H -> R.
Variable classical_hminus_half_norm2 : PhysicalForce -> R.

Definition IntrinsicR3ForceSize (f : PhysicalForce) : R :=
  norm2 (minus_quarter (solenoidal_project f)).

Definition ClassicalHMinusHalfReadout : Prop :=
  forall f : PhysicalForce,
    IntrinsicR3ForceSize f = classical_hminus_half_norm2 f.

Theorem IF20_CLASSICAL_HMINUSHALF_IS_OPTIONAL_READOUT :
  ClassicalHMinusHalfReadout ->
  forall f : PhysicalForce,
    IntrinsicR3ForceSize f = classical_hminus_half_norm2 f.
Proof.
  intros Hread f.
  apply Hread.
Qed.

End OPTIONAL_CLASSICAL_READOUT.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS_V0_13_1"%string.

End NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.

Check NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.IF01_GLOBAL_STOKES_FORCE_ABSORPTION.
Check NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.IF10_INTRINSIC_FORCE_CLASS_PLUS_INTERNAL_LEDGER_GIVES_REGULARITY.
