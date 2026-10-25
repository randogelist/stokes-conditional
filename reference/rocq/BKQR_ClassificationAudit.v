From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import BKQR_CountableRange BKQR_ScalarProfile BKQR_ShellCoordinates BKQR_StrongSynthesis.

Module BKQR_CLASSIFICATION.
Import GP_COUNTABLE_RANGE BKQR_SCALAR_PROFILE BKQR_SHELL_COORDINATES BKQR_STRONG_SYNTHESIS.
Open Scope R_scope.

(* Stage 1 of the supplied periodic classification note: static compatible
   states in a countable diagonal spectral model. The physical Fourier
   realization and the Leray--Hopf path theorem are not definitions here. *)
Section CanonicalProfile.
Variable q h : R.
Variable lambda : nat -> R.
Hypothesis Hq : 0 < q < 1.
Hypothesis Hh : 0 < h.
Hypothesis Hlambda : forall i, 0 <= lambda i.

Definition spectral_argument i := h * (lambda i * lambda i).
Lemma spectral_argument_nonnegative : forall i, 0 <= spectral_argument i.
Proof. intro i. unfold spectral_argument. apply Rmult_le_pos; nra. Qed.

Definition bkqr_weights k i :=
  psi q (spectral_argument i) Hq (spectral_argument_nonnegative i) k.
Definition bkqr_clock k := sqrt (clock q k).
Definition bkqr_ell k := bkqr_clock k / sqrt h.

(* This is the original adjacent shell equation, independently of J or R. *)
Definition BKQRCompatible (U : nat -> nat -> R) : Prop :=
  forall k i, sqrt h * lambda i * U k i = bkqr_clock k * U (S k) i.
Definition BKQRState (U : nat -> nat -> R) : Prop :=
  BKQRCompatible U /\ BKQR_SHELL_COORDINATES.ShellSquareSummable U.
Definition J (v : nat -> R) := gp_encode bkqr_weights v.
Definition R (U : nat -> nat -> R) := reconstruct bkqr_weights U.

Lemma h_root_positive : 0 < sqrt h.
Proof.
  pose proof (sqrt_pos h). pose proof (sqrt_def h (Rlt_le _ _ Hh)). nra.
Qed.

Lemma bkqr_clock_positive : forall k, 0 < bkqr_clock k.
Proof.
  intro k. unfold bkqr_clock.
  pose proof (SCALAR_CLOCK_POSITIVE q Hq k) as Hp.
  pose proof (sqrt_pos (clock q k)).
  pose proof (sqrt_def (clock q k) (Rlt_le _ _ Hp)). nra.
Qed.

Lemma bkqr_ell_positive : forall k, 0 < bkqr_ell k.
Proof.
  intro k. unfold bkqr_ell. apply Rdiv_lt_0_compat.
  - apply bkqr_clock_positive.
  - apply h_root_positive.
Qed.

Lemma BKCL01_SCALAR_PARTITION : ScalarPartition bkqr_weights.
Proof. apply SCALAR_PSI_COUNTABLE_PARTITION. Qed.

Lemma BKCL02_ZERO_WEIGHT_NONZERO : forall i, bkqr_weights 0%nat i <> 0.
Proof.
  intro i. unfold bkqr_weights.
  pose proof (SCALAR_PSI_ZERO_POSITIVE q (spectral_argument i)
    Hq (spectral_argument_nonnegative i)). lra.
Qed.

Lemma BKCL03_ELL_NONZERO : forall k, bkqr_ell k <> 0.
Proof. intro k. pose proof (bkqr_ell_positive k). lra. Qed.

Lemma root_spectral_argument : forall i,
  sqrt (spectral_argument i) = sqrt h * lambda i.
Proof.
  intro i. unfold spectral_argument.
  rewrite sqrt_mult; try nra. rewrite sqrt_square; [reflexivity|apply Hlambda].
Qed.

Lemma BKCL04_SCALAR_RAISING : ScalarRaising bkqr_weights lambda bkqr_ell.
Proof.
  intros k i.
  pose proof (SCALAR_PSI_RAISING q (spectral_argument i) Hq
    (spectral_argument_nonnegative i) k) as H.
  rewrite root_spectral_argument in H.
  apply (Rmult_eq_reg_l (sqrt h)).
  - unfold bkqr_ell, bkqr_clock, bkqr_weights.
    replace (sqrt h * (sqrt (clock q k) / sqrt h *
      psi q (spectral_argument i) Hq (spectral_argument_nonnegative i) (S k)))
      with (sqrt (clock q k) *
        psi q (spectral_argument i) Hq (spectral_argument_nonnegative i) (S k))
      by (field; pose proof h_root_positive; lra).
    nra.
  - pose proof h_root_positive. lra.
Qed.

Lemma BKCL05_ADJACENCY_EQUIVALENCE : forall U,
  BKQRCompatible U <-> AdjacentCompatible lambda bkqr_ell U.
Proof.
  intro U. split; intros HU k i; specialize (HU k i).
  - apply (Rmult_eq_reg_l (sqrt h)).
    + unfold bkqr_ell.
      replace (sqrt h * (bkqr_clock k / sqrt h * U (S k) i))
        with (bkqr_clock k * U (S k) i)
        by (field; pose proof h_root_positive; lra).
      nra.
    + pose proof h_root_positive. lra.
  - unfold bkqr_ell in HU.
    assert (Hcancel : sqrt h * (bkqr_clock k / sqrt h * U (S k) i) =
        bkqr_clock k * U (S k) i).
    { field. pose proof h_root_positive. lra. }
    rewrite <- HU in Hcancel.
    nra.
Qed.

Theorem BKCL10_EXACT_BKQR_STATE_CLASSIFICATION : forall U,
  BKQRState U <-> exists v, SquareSummable v /\ forall k i, U k i = J v k i.
Proof.
  intro U.
  pose proof (BKSC11_EXACT_INTRINSIC_RANGE bkqr_weights lambda bkqr_ell
    BKCL01_SCALAR_PARTITION BKCL04_SCALAR_RAISING
    BKCL02_ZERO_WEIGHT_NONZERO BKCL03_ELL_NONZERO U) as H.
  unfold J. rewrite <- H. unfold BKQRState, IntrinsicState.
  rewrite BKCL05_ADJACENCY_EQUIVALENCE. reflexivity.
Qed.

Theorem BKCL11_RECONSTRUCTION_AND_UNIQUENESS : forall U,
  BKQRCompatible U ->
  (forall k i, U k i = J (R U) k i) /\
  (forall v, (forall k i, U k i = J v k i) -> forall i, v i = R U i).
Proof.
  intros U HU.
  assert (Hfactor : forall k i, U k i = J (R U) k i).
  { eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION.
    - apply BKCL04_SCALAR_RAISING.
    - apply BKCL02_ZERO_WEIGHT_NONZERO.
    - apply BKCL03_ELL_NONZERO.
    - apply (proj1 (BKCL05_ADJACENCY_EQUIVALENCE U)). exact HU. }
  split; [exact Hfactor|]. intros v Hv i.
  eapply BKSC04_UNIQUE_REPRESENTATIVE.
  - apply BKCL02_ZERO_WEIGHT_NONZERO.
  - exact Hv.
  - exact Hfactor.
Qed.

Theorem BKCL12_ALL_ENERGY_BOUNDS : forall U,
  BKQRCompatible U -> forall E, PhysicalBound (R U) E <-> ShellBound U E.
Proof.
  intros U HU E. eapply BKSC10_RECONSTRUCTION_PRESERVES_ALL_BOUNDS.
  - apply BKCL01_SCALAR_PARTITION.
  - apply BKCL04_SCALAR_RAISING.
  - apply BKCL02_ZERO_WEIGHT_NONZERO.
  - apply BKCL03_ELL_NONZERO.
  - apply (proj1 (BKCL05_ADJACENCY_EQUIVALENCE U)). exact HU.
Qed.

Theorem BKCL13_EXACT_TOTAL_ENERGY : forall U,
  BKQRState U -> exists M, PhysicalTotal (R U) M /\ ShellTotal U M.
Proof.
  intros U [HU Hsq]. eapply BKSC12_EXACT_TOTAL_ENERGY.
  - apply BKCL01_SCALAR_PARTITION.
  - apply BKCL04_SCALAR_RAISING.
  - apply BKCL02_ZERO_WEIGHT_NONZERO.
  - apply BKCL03_ELL_NONZERO.
  - split; [apply (proj1 (BKCL05_ADJACENCY_EQUIVALENCE U)); exact HU|exact Hsq].
Qed.

Theorem BKCL14_EXACT_DISSIPATION_BOUNDS : forall U,
  BKQRCompatible U -> forall D,
  PhysicalBound (spectral_multiply lambda (R U)) D <->
  ShellBound (shell_shift bkqr_ell U) D.
Proof.
  intros U HU D. eapply BKSC13_EXACT_DISSIPATION_BOUNDS.
  - apply BKCL01_SCALAR_PARTITION.
  - apply BKCL04_SCALAR_RAISING.
  - apply BKCL02_ZERO_WEIGHT_NONZERO.
  - apply BKCL03_ELL_NONZERO.
  - apply (proj1 (BKCL05_ADJACENCY_EQUIVALENCE U)). exact HU.
Qed.

Theorem BKCL15_SYNTHESIS_COORDINATE_LIMIT : forall U,
  BKQRCompatible U -> forall i,
  GP_COUNTABLE_RANGE.SeqLimit (fun K => synthesis_partial bkqr_weights U K i)
    (R U i).
Proof.
  intros U HU i. eapply BKSC15_COORDINATE_SYNTHESIS_CONVERGES.
  - apply BKCL01_SCALAR_PARTITION.
  - apply BKCL04_SCALAR_RAISING.
  - apply BKCL02_ZERO_WEIGHT_NONZERO.
  - apply BKCL03_ELL_NONZERO.
  - apply (proj1 (BKCL05_ADJACENCY_EQUIVALENCE U)). exact HU.
Qed.

Theorem BKCL16_STRONG_SERIES_RECONSTRUCTION : forall U,
  BKQRState U -> StrongSynthesis bkqr_weights U (R U).
Proof.
  intros U [HU Hsq]. eapply BKSS20_INTRINSIC_RECONSTRUCTION_IS_STRONG_SYNTHESIS.
  - apply BKCL01_SCALAR_PARTITION.
  - apply BKCL04_SCALAR_RAISING.
  - apply BKCL02_ZERO_WEIGHT_NONZERO.
  - apply BKCL03_ELL_NONZERO.
  - split; [apply (proj1 (BKCL05_ADJACENCY_EQUIVALENCE U)); exact HU|exact Hsq].
Qed.
End CanonicalProfile.

(* The audit prints complete theorem types as well as foundational axioms.
   Only q,h,lambda and their numerical sign hypotheses remain in the
   concrete theorem; partition and raising are proved, not supplied. *)
Check BKCL10_EXACT_BKQR_STATE_CLASSIFICATION.
Check BKCL11_RECONSTRUCTION_AND_UNIQUENESS.
Check BKCL12_ALL_ENERGY_BOUNDS.
Check BKCL13_EXACT_TOTAL_ENERGY.
Check BKCL14_EXACT_DISSIPATION_BOUNDS.
Check BKCL16_STRONG_SERIES_RECONSTRUCTION.
Print Assumptions BKCL10_EXACT_BKQR_STATE_CLASSIFICATION.
Print Assumptions BKCL11_RECONSTRUCTION_AND_UNIQUENESS.
Print Assumptions BKCL12_ALL_ENERGY_BOUNDS.
Print Assumptions BKCL13_EXACT_TOTAL_ENERGY.
Print Assumptions BKCL14_EXACT_DISSIPATION_BOUNDS.
Print Assumptions BKCL15_SYNTHESIS_COORDINATE_LIMIT.
Print Assumptions BKCL16_STRONG_SERIES_RECONSTRUCTION.
End BKQR_CLASSIFICATION.
