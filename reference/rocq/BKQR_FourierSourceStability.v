From Stdlib Require Import Reals Lra Psatz Lia Arith.
Require Import BKQR_CountableRange BKQR_TimeIntegrals BKQR_SpectralTimeTail.
Require Import BKQR_NonlinearTimeSource BKQR_SourceStability.
Require Import BKQR_FourierSchur BKQR_NSEFourierClassification.

Module BKQR_FOURIER_SOURCE_STABILITY.
Import GP_COUNTABLE_RANGE BKQR_TIME_INTEGRALS BKQR_NONLINEAR_TIME_SOURCE.
Import BKQR_SOURCE_STABILITY BKQR_SPECTRAL_TIME_TAIL BKQR_FOURIER_SCHUR.
Open Scope R_scope.

Definition concrete_source_value u a b Hab Hu eta Heta E
  (Hcap:forall t,a<=t<=b -> PhysicalBound (u t) E) i : R :=
  proj1_sig (tested_source_limit (indexed_convection_kernel i)
    (indexed_convection_bound i) u a b Hab Hu eta Heta E
    (BKFS40_INDEXED_CONVECTION_HAS_DERIVED_SCHUR_BOUND i) Hcap).

Lemma concrete_source_value_spec : forall u a b Hab Hu eta Heta E Hcap i,
  SeqLimit (tested_source (indexed_convection_kernel i) u a b Hab Hu eta Heta)
    (concrete_source_value u a b Hab Hu eta Heta E Hcap i).
Proof. intros. apply (proj2_sig (tested_source_limit _ _ _ _ _ _ _ _ _ _ _ _)). Qed.

Theorem BKFS50_STRONG_TIME_L2_PRESERVES_CONSTRUCTED_FOURIER_SOURCE :
  forall us u a b Hab Hus Hu E
    (Husc:forall n t,a<=t<=b -> PhysicalBound (us n t) E)
    (Huc:forall t,a<=t<=b -> PhysicalBound (u t) E),
  StrongTimeL2 us u a b Hab Hus Hu -> forall eta Heta i,
  SeqLimit
    (fun n=>concrete_source_value (us n) a b Hab (Hus n) eta Heta E (Husc n) i)
    (concrete_source_value u a b Hab Hu eta Heta E Huc i).
Proof.
  intros us u a b Hab Hus Hu E Husc Huc Hstrong eta Heta i.
  apply (STRONG_TIME_L2_PRESERVES_NONLINEAR_SOURCE
    (indexed_convection_kernel i) (indexed_convection_bound i)
    us u a b Hab Hus Hu eta Heta E).
  - apply BKFS40_INDEXED_CONVECTION_HAS_DERIVED_SCHUR_BOUND.
  - exact Husc.
  - exact Huc.
  - exact Hstrong.
  - intro n. apply concrete_source_value_spec.
  - apply concrete_source_value_spec.
Qed.

Definition complete_mode_cutoff (u:R->nat->R) n := spectral_cutoff (6*n)%nat u.

Lemma complete_mode_cutoff_continuous : forall u a b,
  CoordinateContinuous u a b -> forall n,
  CoordinateContinuous (complete_mode_cutoff u n) a b.
Proof. intros. apply spectral_cutoff_continuous. assumption. Qed.

Lemma complete_mode_cutoff_cap : forall u a b E,
  (forall t,a<=t<=b -> PhysicalBound (u t) E) ->
  forall n t,a<=t<=b -> PhysicalBound (complete_mode_cutoff u n t) E.
Proof.
  intros u a b E Hcap n t Ht N. eapply Rle_trans; [|apply Hcap; exact Ht].
  unfold physical_prefix. apply gp_sum_le. intros i Hi.
  unfold complete_mode_cutoff,spectral_cutoff. destruct (lt_dec i (6*n)); nra.
Qed.

Theorem BKFS51_ENERGY_CAP_CONSTRUCTS_STRONG_TIME_L2_APPROXIMATION :
  forall u a b Hab Hu E,
  (forall t,a<=t<=b -> PhysicalBound (u t) E) ->
  StrongTimeL2 (complete_mode_cutoff u) u a b Hab
    (complete_mode_cutoff_continuous u a b Hu) Hu.
Proof.
  intros u a b Hab Hu E Hcap eps Heps.
  destruct (BKST14_POINTWISE_CAP_GIVES_STRONG_TIME_CUTOFFS u a b Hab Hu E Hcap
    eps Heps) as [J HJ]. exists J. intros n Hn N.
  specialize (HJ (6*n)%nat (ltac:(lia)) N).
  eapply Rle_trans; [|left; exact HJ]. right. apply time_prefix_ext.
  intros t i Ht. reflexivity.
Qed.

Theorem BKFS52_OWN_SPATIAL_MODE_CUTOFFS_HAVE_THE_SAME_SOURCE_LIMIT :
  forall u a b Hab Hu E
    (Hcap:forall t,a<=t<=b -> PhysicalBound (u t) E) eta Heta i,
  SeqLimit
    (fun n=>concrete_source_value (complete_mode_cutoff u n) a b Hab
      (complete_mode_cutoff_continuous u a b Hu n) eta Heta E
      (complete_mode_cutoff_cap u a b E Hcap n) i)
    (concrete_source_value u a b Hab Hu eta Heta E Hcap i).
Proof.
  intros. apply BKFS50_STRONG_TIME_L2_PRESERVES_CONSTRUCTED_FOURIER_SOURCE.
  exact (BKFS51_ENERGY_CAP_CONSTRUCTS_STRONG_TIME_L2_APPROXIMATION u a b Hab Hu E Hcap).
Qed.

Print Assumptions BKFS50_STRONG_TIME_L2_PRESERVES_CONSTRUCTED_FOURIER_SOURCE.
Print Assumptions BKFS51_ENERGY_CAP_CONSTRUCTS_STRONG_TIME_L2_APPROXIMATION.
Print Assumptions BKFS52_OWN_SPATIAL_MODE_CUTOFFS_HAVE_THE_SAME_SOURCE_LIMIT.
End BKQR_FOURIER_SOURCE_STABILITY.
