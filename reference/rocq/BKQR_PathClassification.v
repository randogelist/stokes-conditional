From Stdlib Require Import Reals Lra Psatz.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_ClassificationAudit.
Require Import BKQR_TimeIntegrals BKQR_PathTopology BKQR_IntervalExtension.
Require Import BKQR_EnergyPaths BKQR_InitialTrace BKQR_WeakBalance.

Module BKQR_PATH_CLASSIFICATION.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_TIME_INTEGRALS.
Import BKQR_PATH_TOPOLOGY BKQR_ENERGY_PATHS BKQR_INITIAL_TRACE.
Module C := BKQR_CLASSIFICATION.
Module W := BKQR_WEAK_BALANCE.
Open Scope R_scope.

(* The canonical q-profile discharges every generic partition/raising
   hypothesis. Remaining source F is explicitly supplied; it is not
   declared to be a constructed Navier--Stokes nonlinear distribution. *)
Section CanonicalPaths.
Variables q h nu T : R.
Variable lambda : nat -> R.
Hypothesis Hq : 0 < q < 1.
Hypothesis Hh : 0 < h.
Hypothesis Hl : forall i, 0 <= lambda i.
Hypothesis Hnu : 0 <= nu.
Hypothesis HT : 0 <= T.
Variable Start : R -> Prop.

Let psi := C.bkqr_weights q h lambda Hq Hh.
Let ell := C.bkqr_ell q h.

Definition EncodePath (u : R -> nat -> R) t := gp_encode psi (u t).
Definition DecodePath (U : R -> nat -> nat -> R) t := reconstruct psi (U t).

Theorem BKPA10_CANONICAL_ENCODE_ENERGY_PATH : forall u v0 E0,
  SpectralEnergyPath lambda nu T Start u v0 E0 ->
  NativeEnergyPath lambda ell nu T Start (EncodePath u) (gp_encode psi v0) E0.
Proof.
  intros u v0 E0 H. eapply BKEP30_ENCODE_ENERGY_PATH.
  - exact HT.
  - apply C.BKCL01_SCALAR_PARTITION.
  - apply C.BKCL04_SCALAR_RAISING. exact Hl.
  - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
  - exact H.
Qed.

Theorem BKPA11_CANONICAL_DECODE_ENERGY_PATH : forall U v0 E0,
  NativeEnergyPath lambda ell nu T Start U (gp_encode psi v0) E0 ->
  SpectralEnergyPath lambda nu T Start (DecodePath U) v0 E0.
Proof.
  intros U v0 E0 H. eapply BKEP31_DECODE_ENERGY_PATH.
  - exact HT.
  - apply C.BKCL01_SCALAR_PARTITION.
  - apply C.BKCL04_SCALAR_RAISING. exact Hl.
  - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
  - apply C.BKCL03_ELL_NONZERO. exact Hq. exact Hh.
  - exact H.
Qed.

Theorem BKPA12_EXACT_CANONICAL_ENERGY_PATH_CLASSIFICATION : forall U,
  ShellCoordinateContinuous U 0 T ->
  (forall t, 0 <= t <= T -> C.BKQRCompatible q h lambda (U t)) ->
  forall v0 E0,
  NativeEnergyPath lambda ell nu T Start U (gp_encode psi v0) E0 <->
  SpectralEnergyPath lambda nu T Start (DecodePath U) v0 E0.
Proof.
  intros U HU Hcomp v0 E0.
  assert (HA : forall t, 0 <= t <= T -> AdjacentCompatible lambda ell (U t)).
  { intros t Ht. apply (proj1 (C.BKCL05_ADJACENCY_EQUIVALENCE q h lambda Hq Hh (U t))).
    apply Hcomp. exact Ht. }
  assert (HF : forall t k i, 0 <= t <= T ->
      U t k i=gp_encode psi (DecodePath U t) k i).
  { intros t k i Ht. unfold DecodePath.
    eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION.
    - apply C.BKCL04_SCALAR_RAISING. exact Hl.
    - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
    - apply C.BKCL03_ELL_NONZERO. exact Hq. exact Hh.
    - apply HA. exact Ht. }
  symmetry. apply BKEP22_EXACT_ENERGY_PATH.
  - exact HT.
  - apply C.BKCL01_SCALAR_PARTITION.
  - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
  - apply reconstruct_path_continuous. exact HU.
  - exact HU.
  - exact HA.
  - exact HF.
Qed.

Theorem BKPA20_ENERGY_PATH_IS_WEAKLY_CONTINUOUS : forall u v0 E0,
  SpectralEnergyPath lambda nu T Start u v0 E0 ->
  WeakContinuousOn (fun t => 0 <= t <= T) u.
Proof.
  intros u v0 E0 Hpath.
  apply (proj2 (BKPT20_BOUNDED_WEAK_CONTINUITY_IFF_COORDINATES
    (fun t => 0 <= t <= T) u E0
    (BKEP10_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP lambda nu T Start u v0 E0 Hnu Hpath))).
  intro i. apply ordinary_continuity_implies_relative. intros t Ht.
  exact (proj1 Hpath i t Ht).
Qed.

Theorem BKPA21_NATIVE_ENERGY_PATH_IS_WEAKLY_CONTINUOUS : forall U V0 E0,
  NativeEnergyPath lambda ell nu T Start U V0 E0 ->
  ShellWeakContinuousOn (fun t => 0 <= t <= T) lambda ell U.
Proof.
  intros U V0 E0 Hpath.
  pose proof (BKEP11_NATIVE_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP
    lambda ell nu T Start U V0 E0 Hnu Hpath) as Hb.
  assert (HU : forall t, 0 <= t <= T -> IntrinsicState lambda ell (U t)).
  { intros t Ht. split.
    - exact (proj1 (proj2 Hpath) t Ht).
    - exists E0. apply Hb. exact Ht. }
  apply (proj2 (BKPT33_BOUNDED_NATIVE_WEAK_CONTINUITY_IFF_SHELL_COORDINATES
    psi lambda ell (fun t => 0 <= t <= T) U E0
    (C.BKCL01_SCALAR_PARTITION q h lambda Hq Hh)
    (C.BKCL04_SCALAR_RAISING q h lambda Hq Hh Hl)
    (C.BKCL02_ZERO_WEIGHT_NONZERO q h lambda Hq Hh)
    (C.BKCL03_ELL_NONZERO q h Hq Hh) HU Hb)).
  intros k i. apply ordinary_continuity_implies_relative. intros t Ht.
  exact (proj1 Hpath k i t Ht).
Qed.

Theorem BKPA22_DERIVED_STRONG_INITIAL_TRACE : forall u v0 E0 ts,
  SpectralEnergyPath lambda nu T Start u v0 E0 ->
  (forall n, 0 <= ts n <= T) -> SeqLimit ts 0 ->
  StrongSeqLimit (fun n => u (ts n)) (u 0).
Proof.
  intros u v0 E0 ts Hpath Hts Hlim.
  apply BKIT10_INITIAL_ENERGY_CAP_FORCES_STRONG_TRACE with (E := E0).
  - exact (proj1 (proj2 (proj2 Hpath))).
  - intro n. apply (BKEP10_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP
      lambda nu T Start u v0 E0 Hnu Hpath). apply Hts.
  - intro i. apply (scalar_continuity_gives_sequence_limit
      (fun t => 0 <= t <= T) (fun t => u t i) 0 ts).
    + apply ordinary_continuity_implies_relative. intros t Ht.
      exact (proj1 Hpath i t Ht).
    + lra.
    + exact Hts.
    + exact Hlim.
Qed.

Theorem BKPA23_DERIVED_NATIVE_STRONG_INITIAL_TRACE : forall U V0 E0 ts,
  NativeEnergyPath lambda ell nu T Start U V0 E0 ->
  (forall n, 0 <= ts n <= T) -> SeqLimit ts 0 ->
  StrongShellSeqLimit (fun n => U (ts n)) (U 0).
Proof.
  intros U V0 E0 ts Hpath Hts Hlim.
  eapply BKIT12_NATIVE_INITIAL_ENERGY_CAP_FORCES_STRONG_TRACE
    with (psi := psi) (lambda := lambda) (ell := ell) (E := E0).
  - apply C.BKCL01_SCALAR_PARTITION.
  - apply C.BKCL04_SCALAR_RAISING. exact Hl.
  - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
  - apply C.BKCL03_ELL_NONZERO. exact Hq. exact Hh.
  - intro n. apply (proj1 (proj2 Hpath)). apply Hts.
  - apply (proj1 (proj2 Hpath)). lra.
  - exact (proj1 (proj2 (proj2 (proj2 Hpath)))).
  - intro n. apply (BKEP11_NATIVE_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP
      lambda ell nu T Start U V0 E0 Hnu Hpath). apply Hts.
  - intros k i. apply (scalar_continuity_gives_sequence_limit
      (fun t => 0 <= t <= T) (fun t => U t k i) 0 ts).
    + apply ordinary_continuity_implies_relative. intros t Ht.
      exact (proj1 Hpath k i t Ht).
    + lra.
    + exact Hts.
    + exact Hlim.
Qed.

Theorem BKPA30_CANONICAL_WEAK_LINEAR_BALANCE : forall U
  (HU : ShellCoordinateContinuous U 0 T),
  (forall t, 0 <= t <= T -> C.BKQRCompatible q h lambda (U t)) ->
  forall F : nat -> W.C1ZeroEndpointTest 0 T -> R,
  W.CoordinateWeakBalance psi lambda 0 T nu HT U HU F <->
  W.NativeBlockWeakBalance psi lambda ell 0 T nu HT U HU F.
Proof.
  intros U HU Hcomp F. apply W.WB40_EXACT_WEAK_LINEAR_BALANCE_CLASSIFICATION.
  - apply C.BKCL04_SCALAR_RAISING. exact Hl.
  - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
  - apply C.BKCL03_ELL_NONZERO. exact Hq. exact Hh.
  - intros t Ht. apply (proj1 (C.BKCL05_ADJACENCY_EQUIVALENCE q h lambda Hq Hh (U t))).
    apply Hcomp. exact Ht.
Qed.
End CanonicalPaths.

Check BKPA10_CANONICAL_ENCODE_ENERGY_PATH.
Check BKPA11_CANONICAL_DECODE_ENERGY_PATH.
Check BKPA12_EXACT_CANONICAL_ENERGY_PATH_CLASSIFICATION.
Check BKPA20_ENERGY_PATH_IS_WEAKLY_CONTINUOUS.
Check BKPA21_NATIVE_ENERGY_PATH_IS_WEAKLY_CONTINUOUS.
Check BKPA22_DERIVED_STRONG_INITIAL_TRACE.
Check BKPA23_DERIVED_NATIVE_STRONG_INITIAL_TRACE.
Check BKPA30_CANONICAL_WEAK_LINEAR_BALANCE.
Print Assumptions BKPA10_CANONICAL_ENCODE_ENERGY_PATH.
Print Assumptions BKPA11_CANONICAL_DECODE_ENERGY_PATH.
Print Assumptions BKPA12_EXACT_CANONICAL_ENERGY_PATH_CLASSIFICATION.
Print Assumptions BKPA20_ENERGY_PATH_IS_WEAKLY_CONTINUOUS.
Print Assumptions BKPA21_NATIVE_ENERGY_PATH_IS_WEAKLY_CONTINUOUS.
Print Assumptions BKPA22_DERIVED_STRONG_INITIAL_TRACE.
Print Assumptions BKPA23_DERIVED_NATIVE_STRONG_INITIAL_TRACE.
Print Assumptions BKPA30_CANONICAL_WEAK_LINEAR_BALANCE.
End BKQR_PATH_CLASSIFICATION.
