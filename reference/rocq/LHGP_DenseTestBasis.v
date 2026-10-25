From Stdlib Require Import Reals Lra Psatz Lia Classical_Prop Logic.ConstructiveEpsilon.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.
Require Import LHGP_Dual LHGP_FiniteFrames.

Open Scope R_scope.

(* Countably many genuine tests supply a norm-dense sequence. The full
   test domain remains the carrier of j; it is never replaced by the
   finite span of this sequence. Infinite dimension is a finite-span
   property, not an assumed orthonormal basis or reconstruction theorem. *)
Definition CountablyDense (h : HilbertData) (d : nat -> HCarrier h) : Prop :=
  forall x eps, 0 < eps -> exists n, HDist h x (d n) < eps.

Definition HInfiniteDimension (h : HilbertData) : Prop :=
  forall q n, exists x, ~ FSpan h q n x.

Lemma CountablyDense_annihilator_zero : forall h d,
  CountablyDense h d -> forall x,
  (forall n, HInner h x (d n) = 0) -> x = HZero h.
Proof.
  intros h d HD x Horth.
  apply HNorm_definite.
  destruct (Req_EM_T (HNorm h x) 0) as [Hz | Hnz]; [exact Hz |].
  assert (Hpos : 0 < HNorm h x).
  { pose proof (HNorm_nonnegative h x); lra. }
  destruct (HD x (HNorm h x) Hpos) as [n Hnear].
  pose proof (HInner_distance_bound h x (d n) x) as Hbound.
  rewrite (HInner_sym h (d n) x), Horth in Hbound.
  unfold HNorm in *; nra.
Qed.

Definition HZero_dec (h : HilbertData) (x : HCarrier h) :
  {x = HZero h} + {x <> HZero h}.
Proof.
  destruct (Req_EM_T (HNorm h x) 0) as [Hz | Hnz].
  - left; apply HNorm_definite; exact Hz.
  - right; intro Heq; apply Hnz; rewrite Heq; apply HNorm_zero.
Defined.

Section TestBasisBuilder.
Variables h j : HilbertData.
Variable J : HCarrier j -> HCarrier h.
Hypothesis J_inner : forall x y, HInner h (J x) (J y) = HInner j x y.
Hypothesis J_add : forall x y, J (HAdd j x y) = HAdd h (J x) (J y).
Hypothesis J_scale : forall c x, J (HScale j c x) = HScale h c (J x).
Variable d : nat -> HCarrier j.
Hypothesis d_dense : CountablyDense h (fun n => J (d n)).
Hypothesis h_infinite : HInfiniteDimension h.

Lemma TestEmbed_zero : J (HZero j) = HZero h.
Proof.
  apply HNorm_definite; unfold HNorm; rewrite J_inner, HInner_zero_l; reflexivity.
Qed.

Lemma TestEmbed_finite : forall q a n,
  J (FFinite j q a n) = FFinite h (fun i => J (q i)) a n.
Proof.
  intros q a n; induction n as [|n IH]; simpl.
  - apply TestEmbed_zero.
  - rewrite J_add, J_scale, IH; reflexivity.
Qed.

Lemma TestEmbed_sub : forall x y,
  J (HSub j x y) = HSub h (J x) (J y).
Proof. intros x y; unfold HSub; rewrite J_add, J_scale; reflexivity. Qed.

Lemma Dense_residual_nonzero : forall q n,
  FOrthonormal h q n ->
  exists k, FResidual h q (J (d k)) n <> HZero h.
Proof.
  intros q n Hq.
  destruct (classic (exists k, FResidual h q (J (d k)) n <> HZero h))
    as [Hyes | Hno]; [exact Hyes |].
  exfalso.
  destruct (h_infinite q n) as [x Houtside].
  assert (Hres : FResidual h q x n = HZero h).
  { apply (CountablyDense_annihilator_zero h (fun k => J (d k)) d_dense).
    intro k.
    apply (FOrthogonal_span h q n (J (d k)) (FResidual h q x n)).
    - intros i Hi; apply FResidual_orthogonal; assumption.
    - apply (proj1 (FResidual_zero_iff_span h q n Hq (J (d k)))).
      apply NNPP; intro Hneq; apply Hno; exists k; exact Hneq. }
  apply Houtside.
  apply (proj1 (FResidual_zero_iff_span h q n Hq x)); exact Hres.
Qed.

Definition DenseResidualIndex (q : nat -> HCarrier h) (n : nat)
    (Hq : FOrthonormal h q n) :
    {k : nat | FResidual h q (J (d k)) n <> HZero h}.
Proof.
  apply constructive_indefinite_description_nat.
  - intro k; destruct (HZero_dec h (FResidual h q (J (d k)) n)) as [Hz | Hnz].
    + right; intro H; apply H; exact Hz.
    + left; exact Hnz.
  - apply Dense_residual_nonzero; exact Hq.
Defined.

Record LiftedFiniteFrame (n : nat) : Type := {
  FrameTests : nat -> HCarrier j;
  FrameOrthonormal : FOrthonormal h (fun i => J (FrameTests i)) n
}.
Arguments FrameTests {n} _ _.
Arguments FrameOrthonormal {n} _.

Definition FrameCandidate {n : nat} (frame : LiftedFiniteFrame n) : HCarrier j :=
  match HZero_dec h (FResidual h (fun i => J (FrameTests frame i)) (J (d n)) n) with
  | left _ => d (proj1_sig (DenseResidualIndex _ n (FrameOrthonormal frame)))
  | right _ => d n
  end.

Lemma FrameCandidate_nonzero : forall n (frame : LiftedFiniteFrame n),
  FResidual h (fun i => J (FrameTests frame i)) (J (FrameCandidate frame)) n
    <> HZero h.
Proof.
  intros n frame; unfold FrameCandidate.
  destruct (HZero_dec h (FResidual h (fun i => J (FrameTests frame i)) (J (d n)) n))
    as [Hz | Hnz]; [|exact Hnz].
  exact (proj2_sig (DenseResidualIndex _ n (FrameOrthonormal frame))).
Qed.

Lemma FrameCandidate_covers : forall n (frame : LiftedFiniteFrame n),
  FResidual h (fun i => J (FrameTests frame i)) (J (d n)) n = HZero h \/
  FrameCandidate frame = d n.
Proof.
  intros n frame; unfold FrameCandidate.
  destruct (HZero_dec h (FResidual h (fun i => J (FrameTests frame i)) (J (d n)) n));
    [left; assumption | right; reflexivity].
Qed.

Definition LiftedResidual (q : nat -> HCarrier j) (z : HCarrier j) (n : nat) :=
  HSub j z (FFinite j q (fun i => HInner h (J z) (J (q i))) n).

Lemma LiftedResidual_image : forall q z n,
  J (LiftedResidual q z n) = FResidual h (fun i => J (q i)) (J z) n.
Proof.
  intros q z n; unfold LiftedResidual, FResidual, FProjection.
  rewrite TestEmbed_sub, TestEmbed_finite; reflexivity.
Qed.

Definition LiftedNormalizedResidual (q : nat -> HCarrier j) (z : HCarrier j)
    (n : nat) : HCarrier j :=
  HScale j (/ sqrt (HNorm h (FResidual h (fun i => J (q i)) (J z) n)))
    (LiftedResidual q z n).

Lemma LiftedNormalizedResidual_image : forall q z n,
  J (LiftedNormalizedResidual q z n) =
  FNormalizedResidual h (fun i => J (q i)) (J z) n.
Proof.
  intros q z n; unfold LiftedNormalizedResidual, FNormalizedResidual.
  rewrite J_scale, LiftedResidual_image; reflexivity.
Qed.

Lemma TestEmbed_extend : forall q n z i,
  J (FExtend j q n z i) = FExtend h (fun k => J (q k)) n (J z) i.
Proof.
  intros q n z i; unfold FExtend; destruct (Nat.eq_dec i n); reflexivity.
Qed.

Definition FrameNextTests {n : nat} (frame : LiftedFiniteFrame n) :=
  FExtend j (FrameTests frame) n
    (LiftedNormalizedResidual (FrameTests frame) (FrameCandidate frame) n).

Lemma FrameNextTests_image : forall n (frame : LiftedFiniteFrame n) i,
  J (FrameNextTests frame i) =
  FExtend h (fun k => J (FrameTests frame k)) n
    (FNormalizedResidual h (fun k => J (FrameTests frame k))
      (J (FrameCandidate frame)) n) i.
Proof.
  intros n frame i; unfold FrameNextTests.
  rewrite TestEmbed_extend, LiftedNormalizedResidual_image; reflexivity.
Qed.

Definition FrameNext {n : nat} (frame : LiftedFiniteFrame n) :
    LiftedFiniteFrame (S n).
Proof.
  refine {| FrameTests := FrameNextTests frame |}.
  intros i k Hi Hk; rewrite !FrameNextTests_image.
  exact (FOrthonormal_extend_normalized h
    (fun l => J (FrameTests frame l)) n (FrameOrthonormal frame)
    (J (FrameCandidate frame)) (FrameCandidate_nonzero n frame) i k Hi Hk).
Defined.

Lemma FrameNext_prefix : forall n (frame : LiftedFiniteFrame n) i,
  (i < n)%nat -> FrameTests (FrameNext frame) i = FrameTests frame i.
Proof.
  intros n frame i Hi; change (FrameNextTests frame i = FrameTests frame i).
  unfold FrameNextTests, FExtend; destruct (Nat.eq_dec i n); [lia | reflexivity].
Qed.

Lemma FrameNext_input_span : forall n (frame : LiftedFiniteFrame n),
  FSpan h (fun i => J (FrameTests (FrameNext frame) i)) (S n) (J (d n)).
Proof.
  intros n frame.
  assert (Heq : forall i, (i < S n)%nat ->
    FExtend h (fun k => J (FrameTests frame k)) n
      (FNormalizedResidual h (fun k => J (FrameTests frame k))
        (J (FrameCandidate frame)) n) i =
    J (FrameTests (FrameNext frame) i)).
  { intros i Hi; symmetry; apply FrameNextTests_image. }
  apply (proj1 (FSpan_ext h _ _ (S n) (J (d n)) Heq)).
  destruct (FrameCandidate_covers n frame) as [Hz | Hcandidate].
  - apply FSpan_extend.
    apply (proj1 (FResidual_zero_iff_span h
      (fun i => J (FrameTests frame i)) n (FrameOrthonormal frame) (J (d n)))).
    exact Hz.
  - rewrite Hcandidate.
    apply FSpan_extend_normalized_contains.
    rewrite <- Hcandidate; apply FrameCandidate_nonzero.
Qed.

Definition FrameEmpty : LiftedFiniteFrame O.
Proof.
  refine {| FrameTests := fun _ => HZero j |}.
  intros i k Hi Hk; lia.
Defined.

Fixpoint DenseFrames (n : nat) : LiftedFiniteFrame n :=
  match n with
  | O => FrameEmpty
  | S k => FrameNext (DenseFrames k)
  end.

Lemma DenseFrames_coherent : forall m n i,
  (n <= m)%nat -> (i < n)%nat ->
  FrameTests (DenseFrames m) i = FrameTests (DenseFrames n) i.
Proof.
  induction m as [|m IH]; intros n i Hnm Hin; [lia |].
  destruct (Nat.eq_dec n (S m)) as [Heq | Hneq].
  - subst n; reflexivity.
  - change (FrameTests (FrameNext (DenseFrames m)) i = FrameTests (DenseFrames n) i).
    rewrite FrameNext_prefix by lia.
    apply IH; lia.
Qed.

Definition DenseTestLift (i : nat) : HCarrier j := FrameTests (DenseFrames (S i)) i.

Lemma DenseTestLift_in_frame : forall n i,
  (i < n)%nat -> DenseTestLift i = FrameTests (DenseFrames n) i.
Proof.
  intros n i Hi; unfold DenseTestLift; symmetry.
  apply DenseFrames_coherent; lia.
Qed.

Theorem DENSE_TEST_BASIS_ORTHONORMAL : forall i k,
  HInner h (J (DenseTestLift i)) (J (DenseTestLift k)) =
    if Nat.eq_dec i k then 1 else 0.
Proof.
  intros i k.
  rewrite (DenseTestLift_in_frame (S (Nat.max i k)) i ltac:(lia)).
  rewrite (DenseTestLift_in_frame (S (Nat.max i k)) k ltac:(lia)).
  apply FrameOrthonormal; lia.
Qed.

Theorem DENSE_TEST_BASIS_COVERS_INPUT : forall n,
  FSpan h (fun i => J (DenseTestLift i)) (S n) (J (d n)).
Proof.
  intro n.
  assert (Heq : forall i, (i < S n)%nat ->
    J (FrameTests (DenseFrames (S n)) i) = J (DenseTestLift i)).
  { intros i Hi; rewrite DenseTestLift_in_frame with (n := S n) by exact Hi.
    reflexivity. }
  apply (proj1 (FSpan_ext h _ _ (S n) (J (d n)) Heq)).
  apply FrameNext_input_span.
Qed.

Theorem DENSE_TEST_BASIS_SEPARATES : forall x,
  (forall i, HInner h x (J (DenseTestLift i)) = 0) -> x = HZero h.
Proof.
  intros x Hx.
  apply (CountablyDense_annihilator_zero h (fun n => J (d n)) d_dense).
  intro n; apply (FOrthogonal_span h (fun i => J (DenseTestLift i)) (S n) (J (d n)) x).
  - intros i Hi; apply Hx.
  - apply DENSE_TEST_BASIS_COVERS_INPUT.
Qed.

Definition DenseTestONB : OrthonormalBasis h :=
  {| HBasis := fun i => J (DenseTestLift i);
     HBasis_orthonormal := DENSE_TEST_BASIS_ORTHONORMAL;
     HBasis_separating := DENSE_TEST_BASIS_SEPARATES |}.

Theorem DENSE_TEST_BASIS_EXISTS :
  exists b : OrthonormalBasis h, exists lifts : nat -> HCarrier j,
    forall i, J (lifts i) = HBasis h b i.
Proof.
  exists DenseTestONB, DenseTestLift; intro i; reflexivity.
Qed.

Definition DenseTestsDualModel (Hcomplete : HComplete h) : DualTestModel :=
  {| DTest := j;
     DTarget := h;
     DComplete := Hcomplete;
     DBasis := DenseTestONB;
     DEmbed := J;
     DEmbed_inner := J_inner;
     DEmbed_add := J_add;
     DEmbed_scale := J_scale;
     DTestBasis := DenseTestLift;
     DTestBasis_image := fun _ => eq_refl |}.

End TestBasisBuilder.

Print Assumptions DENSE_TEST_BASIS_ORTHONORMAL.
Print Assumptions DENSE_TEST_BASIS_COVERS_INPUT.
Print Assumptions DENSE_TEST_BASIS_SEPARATES.
Print Assumptions DENSE_TEST_BASIS_EXISTS.
Print Assumptions DenseTestsDualModel.
