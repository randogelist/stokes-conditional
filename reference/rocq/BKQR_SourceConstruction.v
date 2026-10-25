From Stdlib Require Import Reals Lra Psatz.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_TimeIntegrals.
Require Import BKQR_WeakBalance BKQR_EnergyPaths BKQR_QuadraticTransport.
Require Import BKQR_BilinearKernel BKQR_NonlinearTimeSource.

Module BKQR_SOURCE_CONSTRUCTION.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_TIME_INTEGRALS.
Import BKQR_WEAK_BALANCE BKQR_ENERGY_PATHS BKQR_QUADRATIC_TRANSPORT.
Module B := BKQR_BILINEAR_KERNEL.
Module N := BKQR_NONLINEAR_TIME_SOURCE.
Open Scope R_scope.

Lemma coordinate_source_is_tested_source : forall K u a b Hab Hu eta i n,
  coordinate_source K u a b Hab Hu eta i n =
  N.tested_source (K i) u a b Hab Hu (test_value a b eta)
    (test_value_continuous a b eta) n.
Proof.
  intros. unfold coordinate_source, N.tested_source. apply integral_ext.
  intros t Ht. reflexivity.
Qed.

Section ConstructedSource.
Variables K : nat -> nat -> nat -> R.
Variable C : nat -> R.
Variables u : R -> nat -> R.
Variables a b E : R.
Variable Hab : a <= b.
Variable Hu : CoordinateContinuous u a b.
Hypothesis HK : forall i, B.SchurBound (K i) (C i).
Hypothesis Hcap : forall t, a <= t <= b -> PhysicalBound (u t) E.

Definition source_value i (eta : C1ZeroEndpointTest a b) : R :=
  proj1_sig (N.tested_source_limit (K i) (C i) u a b Hab Hu
    (test_value a b eta) (test_value_continuous a b eta) E (HK i) Hcap).

Theorem BKQS10_CONSTRUCTED_SOURCE_LIMIT : forall eta i,
  SeqLimit (coordinate_source K u a b Hab Hu eta i) (source_value i eta).
Proof.
  intros eta i. apply (limit_ext
    (N.tested_source (K i) u a b Hab Hu (test_value a b eta)
      (test_value_continuous a b eta)) _ _).
  - intro n. symmetry. apply coordinate_source_is_tested_source.
  - exact (proj2_sig (N.tested_source_limit (K i) (C i) u a b Hab Hu
      (test_value a b eta) (test_value_continuous a b eta) E (HK i) Hcap)).
Qed.

Theorem BKQS11_SOURCE_VALUE_UNIQUE : forall eta i L,
  SeqLimit (coordinate_source K u a b Hab Hu eta i) L ->
  L=source_value i eta.
Proof.
  intros eta i L HL. eapply N.TESTED_SOURCE_LIMIT_UNIQUE.
  - eapply limit_ext; [intro n; apply coordinate_source_is_tested_source|exact HL].
  - exact (proj2_sig (N.tested_source_limit (K i) (C i) u a b Hab Hu
      (test_value a b eta) (test_value_continuous a b eta) E (HK i) Hcap)).
Qed.

Theorem BKQS12_CONSTRUCTED_SOURCE_BOUND : forall eta i A,
  0 <= A -> (forall t, a <= t <= b -> Rabs (test_value a b eta t) <= A) ->
  Rabs (source_value i eta) <= A*C i*E*(b-a).
Proof.
  intros eta i A HA Heta. apply (N.TESTED_SOURCE_LIMIT_BOUND
    (K i) (C i) u a b Hab Hu (test_value a b eta)
    (test_value_continuous a b eta) E A (source_value i eta)); try assumption.
  - apply HK.
  - exact (proj2_sig (N.tested_source_limit (K i) (C i) u a b Hab Hu
      (test_value a b eta) (test_value_continuous a b eta) E (HK i) Hcap)).
Qed.

Theorem BKQS20_EQUATION_USES_CONSTRUCTED_SOURCE : forall lambda nu,
  CoordinateQuadraticWeakEquation K lambda nu u a b Hab Hu <->
  forall eta i, coordinate_linear lambda nu u a b Hab Hu eta i + source_value i eta=0.
Proof.
  intros lambda nu. split.
  - intros H eta i. pose proof (BKQS11_SOURCE_VALUE_UNIQUE eta i
      (-coordinate_linear lambda nu u a b Hab Hu eta i) (H eta i)). lra.
  - intros H eta i. pose proof (H eta i) as Heq.
    replace (-coordinate_linear lambda nu u a b Hab Hu eta i)
      with (source_value i eta) by lra. apply BKQS10_CONSTRUCTED_SOURCE_LIMIT.
Qed.
End ConstructedSource.

Theorem BKQS30_ENERGY_PATH_CONSTRUCTS_SAME_PATH_SOURCE :
  forall K C lambda nu T Start u v0 E0 (HT : 0 <= T)
    (Hu : CoordinateContinuous u 0 T),
  0 <= nu -> (forall i, B.SchurBound (K i) (C i)) ->
  SpectralEnergyPath lambda nu T Start u v0 E0 ->
  forall eta i, exists L,
    SeqLimit (coordinate_source K u 0 T HT Hu eta i) L /\
    forall R, SeqLimit (coordinate_source K u 0 T HT Hu eta i) R -> R=L.
Proof.
  intros K C lambda nu T Start u v0 E0 HT Hu Hnu HK Hpath eta i.
  pose proof (BKEP10_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP
    lambda nu T Start u v0 E0 Hnu Hpath) as Hcap.
  exists (source_value K C u 0 T E0 HT Hu HK Hcap i eta). split.
  - apply BKQS10_CONSTRUCTED_SOURCE_LIMIT.
  - intros R HR. apply BKQS11_SOURCE_VALUE_UNIQUE. exact HR.
Qed.

Theorem BKQS31_NATIVE_SOURCE_EXISTS_ON_COMPATIBLE_RANGE :
  forall K C psi u U a b E (Hab : a <= b)
    (Hu : CoordinateContinuous u a b) (HU : ShellCoordinateContinuous U a b),
  (forall i, B.SchurBound (K i) (C i)) ->
  (forall t, a <= t <= b -> PhysicalBound (u t) E) ->
  (forall i, psi 0%nat i <> 0) ->
  (forall t k i, a <= t <= b -> U t k i=psi k i*u t i) ->
  forall eta k i, exists L,
    SeqLimit (coordinate_source K u a b Hab Hu eta i) L /\
    SeqLimit (native_source K psi U a b Hab HU eta k i) (psi k i*L).
Proof.
  intros K C psi u U a b E Hab Hu HU HK Hcap Hzero HF eta k i.
  exists (source_value K C u a b E Hab Hu HK Hcap i eta).
  pose proof (BKQS10_CONSTRUCTED_SOURCE_LIMIT K C u a b E Hab Hu HK Hcap eta i) as HL.
  split; [exact HL|]. eapply limit_ext.
  - intro n. symmetry. apply (BKQT11_ACTUAL_TESTED_NONLINEAR_SOURCE_TRANSPORT
      K psi a b Hab u U Hu HU Hzero HF eta k i n).
  - apply limit_scale. exact HL.
Qed.

Check BKQS30_ENERGY_PATH_CONSTRUCTS_SAME_PATH_SOURCE.
Check BKQS31_NATIVE_SOURCE_EXISTS_ON_COMPATIBLE_RANGE.
Print Assumptions BKQS10_CONSTRUCTED_SOURCE_LIMIT.
Print Assumptions BKQS20_EQUATION_USES_CONSTRUCTED_SOURCE.
Print Assumptions BKQS30_ENERGY_PATH_CONSTRUCTS_SAME_PATH_SOURCE.
Print Assumptions BKQS31_NATIVE_SOURCE_EXISTS_ON_COMPATIBLE_RANGE.
End BKQR_SOURCE_CONSTRUCTION.
