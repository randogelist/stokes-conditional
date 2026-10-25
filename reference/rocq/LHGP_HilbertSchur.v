From Stdlib Require Import Reals Lra Psatz Field.
Require Import LHGP_Hilbert.

Open Scope R_scope.

(* The actual two-direction construction of the supplied finite native
   Kq/Gram anchor, lifted to the inner-product carrier. The formula uses
   total real division and remains valid when either direction is zero
   or the two directions are dependent. No completeness, determinant
   lower bound, Moore-Penrose oracle, or physical realization is assumed. *)

Definition HCoefficient (h : HilbertData) (v x : HCarrier h) : R :=
  HInner h x v / HNorm h v.

Definition HRemove (h : HilbertData) (v x : HCarrier h) : HCarrier h :=
  HSub h x (HScale h (HCoefficient h v x) v).

Definition HSecondDirection h (n0 n1 : HCarrier h) := HRemove h n0 n1.
Definition HFirstResidual h (f n0 : HCarrier h) := HRemove h n0 f.
Definition HBeta h (f n0 n1 : HCarrier h) :=
  HCoefficient h (HSecondDirection h n0 n1) (HFirstResidual h f n0).
Definition HAlpha h (f n0 n1 : HCarrier h) :=
  HCoefficient h n0 f - HBeta h f n0 n1 * HCoefficient h n0 n1.
Definition HResidual h (f n0 n1 : HCarrier h) (a b : R) :=
  HSub h (HSub h f (HScale h a n0)) (HScale h b n1).
Definition HReduced h (f n0 n1 : HCarrier h) :=
  HResidual h f n0 n1 (HAlpha h f n0 n1) (HBeta h f n0 n1).
Definition HReducedCapacity h (f n0 n1 : HCarrier h) :=
  HNorm h (HReduced h f n0 n1).

Definition HNormalEquations h (f n0 n1 : HCarrier h) (a b : R) : Prop :=
  HInner h f n0 = a * HNorm h n0 + b * HInner h n1 n0 /\
  HInner h f n1 = a * HInner h n0 n1 + b * HNorm h n1.

Lemma HInner_remove_l : forall h (v x y : HCarrier h),
  HInner h (HRemove h v x) y =
  HInner h x y - HCoefficient h v x * HInner h v y.
Proof.
  intros; unfold HRemove; rewrite HInner_sub_l, HInner_scale_l; reflexivity.
Qed.

Lemma HInner_remove_r : forall h (x v y : HCarrier h),
  HInner h x (HRemove h v y) =
  HInner h x y - HCoefficient h v y * HInner h x v.
Proof.
  intros; unfold HRemove; rewrite HInner_sub_r, HInner_scale_r; reflexivity.
Qed.

Theorem HSG00_REMOVE_ORTHOGONAL : forall h (v x : HCarrier h),
  HInner h (HRemove h v x) v = 0.
Proof.
  intros h v x; rewrite HInner_remove_l; fold (HNorm h v).
  unfold HCoefficient.
  destruct (Req_dec (HNorm h v) 0) as [Hz | Hnz].
  - assert (Hv : v = HZero h) by (apply HNorm_definite; exact Hz).
    rewrite Hv, HInner_zero_r, HNorm_zero; unfold Rdiv; ring.
  - field; exact Hnz.
Qed.

Theorem HSG01_REMOVE_PRESERVES_ANNIHILATOR : forall h (d v x : HCarrier h),
  HInner h d v = 0 -> HInner h d (HRemove h v x) = HInner h d x.
Proof. intros; rewrite HInner_remove_r, H; ring. Qed.

Lemma HInner_residual_l : forall h (f n0 n1 : HCarrier h) a b y,
  HInner h (HResidual h f n0 n1 a b) y =
  HInner h f y - a * HInner h n0 y - b * HInner h n1 y.
Proof.
  intros; unfold HResidual; rewrite !HInner_sub_l, !HInner_scale_l; reflexivity.
Qed.

Lemma HInner_residual_r : forall h (x f n0 n1 : HCarrier h) a b,
  HInner h x (HResidual h f n0 n1 a b) =
  HInner h x f - a * HInner h x n0 - b * HInner h x n1.
Proof.
  intros; unfold HResidual; rewrite !HInner_sub_r, !HInner_scale_r; reflexivity.
Qed.

Lemma HReduced_two_steps : forall h (f n0 n1 : HCarrier h),
  HReduced h f n0 n1 =
  HRemove h (HSecondDirection h n0 n1) (HFirstResidual h f n0).
Proof.
  intros h f n0 n1; apply HInner_ext; intro y.
  unfold HReduced; rewrite HInner_residual_l, HInner_remove_l.
  unfold HAlpha, HBeta, HFirstResidual, HSecondDirection.
  rewrite !HInner_remove_l; ring.
Qed.

Theorem HSG10_RANK_SAFE_ORTHOGONALITY : forall h (f n0 n1 : HCarrier h),
  HInner h (HReduced h f n0 n1) n0 = 0 /\
  HInner h (HReduced h f n0 n1) n1 = 0.
Proof.
  intros h f n0 n1.
  set (w := HSecondDirection h n0 n1).
  set (f0 := HFirstResidual h f n0).
  set (r := HRemove h w f0).
  assert (Heq : HReduced h f n0 n1 = r).
  { unfold r, w, f0; apply HReduced_two_steps. }
  assert (Hw0 : HInner h w n0 = 0).
  { unfold w, HSecondDirection; apply HSG00_REMOVE_ORTHOGONAL. }
  assert (Hf0 : HInner h f0 n0 = 0).
  { unfold f0, HFirstResidual; apply HSG00_REMOVE_ORTHOGONAL. }
  assert (Hr0 : HInner h r n0 = 0).
  { unfold r; rewrite HInner_remove_l, Hf0, Hw0; ring. }
  assert (Hrw : HInner h r w = 0).
  { unfold r; apply HSG00_REMOVE_ORTHOGONAL. }
  assert (Hr1 : HInner h r n1 = 0).
  { unfold w, HSecondDirection in Hrw.
    rewrite HInner_remove_r, Hr0 in Hrw; lra. }
  rewrite Heq; split; assumption.
Qed.

Theorem HSG11_NORMAL_EQUATIONS : forall h (f n0 n1 : HCarrier h),
  HNormalEquations h f n0 n1 (HAlpha h f n0 n1) (HBeta h f n0 n1).
Proof.
  intros h f n0 n1.
  destruct (HSG10_RANK_SAFE_ORTHOGONALITY h f n0 n1) as [H0 H1].
  unfold HReduced in H0, H1; rewrite HInner_residual_l in H0, H1.
  unfold HNormalEquations, HNorm; split; lra.
Qed.

Theorem HSG12_REDUCED_PAIRING : forall h (d f n0 n1 : HCarrier h),
  HInner h d n0 = 0 -> HInner h d n1 = 0 ->
  HInner h d (HReduced h f n0 n1) = HInner h d f.
Proof.
  intros h d f n0 n1 H0 H1; unfold HReduced.
  rewrite HInner_residual_r, H0, H1; ring.
Qed.

Lemma HResidual_norm_expansion : forall h (f n0 n1 : HCarrier h) a b,
  HNorm h (HResidual h f n0 n1 a b) =
  HNorm h f - 2 * a * HInner h f n0 - 2 * b * HInner h f n1 +
  a * a * HNorm h n0 + 2 * a * b * HInner h n0 n1 + b * b * HNorm h n1.
Proof.
  intros h f n0 n1 a b; unfold HNorm.
  rewrite HInner_residual_l, !HInner_residual_r.
  rewrite (HInner_sym h n0 f), (HInner_sym h n1 f), (HInner_sym h n1 n0); ring.
Qed.

Theorem HSG13_NORMAL_SCHUR_VALUE : forall h (f n0 n1 : HCarrier h) a b,
  HNormalEquations h f n0 n1 a b ->
  HNorm h (HResidual h f n0 n1 a b) =
    HNorm h f - a * HInner h f n0 - b * HInner h f n1.
Proof.
  intros h f n0 n1 a b [H0 H1].
  rewrite (HInner_sym h n1 n0) in H0.
  rewrite HResidual_norm_expansion, H0, H1; ring.
Qed.

Theorem HSG14_SCHUR_VALUE : forall h (f n0 n1 : HCarrier h),
  HReducedCapacity h f n0 n1 = HNorm h f -
    HAlpha h f n0 n1 * HInner h f n0 - HBeta h f n0 n1 * HInner h f n1.
Proof.
  intros; unfold HReducedCapacity, HReduced.
  apply HSG13_NORMAL_SCHUR_VALUE; apply HSG11_NORMAL_EQUATIONS.
Qed.

(* This exact Pythagoras identity proves minimality even at a rank drop. *)
Theorem HSG15_RESIDUAL_PYTHAGORAS : forall h (f n0 n1 : HCarrier h) a b,
  HNorm h (HResidual h f n0 n1 a b) =
    HReducedCapacity h f n0 n1 +
    HNorm h (HAdd h (HScale h (HAlpha h f n0 n1 - a) n0)
                   (HScale h (HBeta h f n0 n1 - b) n1)).
Proof.
  intros h f n0 n1 a b.
  set (r := HReduced h f n0 n1).
  set (v := HAdd h (HScale h (HAlpha h f n0 n1 - a) n0)
                  (HScale h (HBeta h f n0 n1 - b) n1)).
  assert (Heq : HResidual h f n0 n1 a b = HAdd h r v).
  { apply HInner_ext; intro y.
    unfold r, v, HReduced.
    rewrite HInner_add_l, !HInner_residual_l, HInner_add_l, !HInner_scale_l; ring. }
  assert (Horth : HInner h r v = 0).
  { destruct (HSG10_RANK_SAFE_ORTHOGONALITY h f n0 n1) as [H0 H1].
    unfold v; rewrite HInner_add_r, !HInner_scale_r.
    unfold r; rewrite H0, H1; ring. }
  rewrite Heq, HNorm_add, Horth.
  unfold HReducedCapacity; fold r; ring.
Qed.

Theorem HSG15_CAPACITY_MINIMAL : forall h (f n0 n1 : HCarrier h) a b,
  HReducedCapacity h f n0 n1 <= HNorm h (HResidual h f n0 n1 a b).
Proof.
  intros; rewrite HSG15_RESIDUAL_PYTHAGORAS.
  pose proof (HNorm_nonnegative h
    (HAdd h (HScale h (HAlpha h f n0 n1 - a) n0)
            (HScale h (HBeta h f n0 n1 - b) n1))); lra.
Qed.

Theorem HSG16_CAPACITY_BOUNDS : forall h (f n0 n1 : HCarrier h),
  0 <= HReducedCapacity h f n0 n1 /\ HReducedCapacity h f n0 n1 <= HNorm h f.
Proof.
  intros h f n0 n1; split; [apply HNorm_nonnegative |].
  pose proof (HSG15_CAPACITY_MINIMAL h f n0 n1 0 0) as H.
  rewrite HResidual_norm_expansion in H; lra.
Qed.

Theorem HSG20_SCHUR_ACTION_BOUND : forall h (d f n0 n1 : HCarrier h),
  HInner h d n0 = 0 -> HInner h d n1 = 0 ->
  HInner h d f * HInner h d f <= HNorm h d * HReducedCapacity h f n0 n1.
Proof.
  intros h d f n0 n1 H0 H1.
  pose proof (HInner_cauchy_schwarz h d (HReduced h f n0 n1)) as Hcs.
  rewrite (HSG12_REDUCED_PAIRING h d f n0 n1 H0 H1) in Hcs; exact Hcs.
Qed.

Theorem HSG21_ZERO_CAPACITY_ZERO_RENEWAL : forall h (d f n0 n1 : HCarrier h),
  HInner h d n0 = 0 -> HInner h d n1 = 0 ->
  HReducedCapacity h f n0 n1 = 0 -> HInner h d f = 0.
Proof.
  intros h d f n0 n1 H0 H1 Hz.
  pose proof (HSG20_SCHUR_ACTION_BOUND h d f n0 n1 H0 H1) as H.
  rewrite Hz in H; nra.
Qed.

Print Assumptions HSG10_RANK_SAFE_ORTHOGONALITY.
Print Assumptions HSG14_SCHUR_VALUE.
Print Assumptions HSG15_RESIDUAL_PYTHAGORAS.
Print Assumptions HSG15_CAPACITY_MINIMAL.
Print Assumptions HSG20_SCHUR_ACTION_BOUND.
Print Assumptions HSG21_ZERO_CAPACITY_ZERO_RENEWAL.
