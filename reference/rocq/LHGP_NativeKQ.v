From Stdlib Require Import Reals Lra Psatz Lia.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_gp_gram_geometry_v0_49_3.

Open Scope R_scope.
Module NativeKQ := NSE_KQ_FINITE_ALGEBRA.
Module NativeGram := NSE_GP_GRAM_GEOMETRY.

(* Literal use of the preserved finite Kq/Gram modules.  The weighted
   GP geometry is the donor dot/Gram applied to DECODED roles.  A diagonal
   encoding with arbitrary nonzero weights is not an isometry for the
   unweighted dot on encoded coordinates.
   This completion does not identify complex spectral powers, bilateral
   infinite Kq products, or physical source/detector assignments. *)

Lemma NativeSum_prefix : forall n f, NativeKQ.sum n f = prefix f n.
Proof. intros n f; induction n; simpl; [reflexivity|rewrite IHn; reflexivity]. Qed.

Lemma NativeDot_linear_prefix : forall n a c,
  NativeKQ.dot n a c = linear_prefix a c n.
Proof. intros; unfold NativeKQ.dot, linear_prefix; apply NativeSum_prefix. Qed.

Lemma NativeNorm_energy_prefix : forall n a,
  NativeKQ.norm2 n a = energy_prefix a n.
Proof. intros; unfold NativeKQ.norm2, NativeKQ.dot, energy_prefix; apply NativeSum_prefix. Qed.

Theorem LHGP_NATIVE_DOT_FINITE_SYNTHESIS : forall h (b : OrthonormalBasis h) a c n,
  NativeKQ.dot n a c = HInner h (HFinite b a n) (HFinite b c n).
Proof.
  intros h b a c n; rewrite NativeDot_linear_prefix, HFinite_inner.
  unfold linear_prefix; apply Hprefix_ext_below; intros i Hi.
  rewrite HInner_sym, HFinite_coefficient_inside by exact Hi; reflexivity.
Qed.

Definition HPick4 (h : HilbertData) (d f n0 n1 : HCarrier h)
    (i : NativeGram.Axis4) : HCarrier h :=
  match i with
  | NativeGram.D => d
  | NativeGram.F => f
  | NativeGram.N0 => n0
  | NativeGram.N1 => n1
  end.

Definition HilbertGram4 (h : HilbertData) (d f n0 n1 : HCarrier h)
    (i j : NativeGram.Axis4) : R :=
  HInner h (HPick4 h d f n0 n1 i) (HPick4 h d f n0 n1 j).

Definition HCombine4 (h : HilbertData) (d f n0 n1 : HCarrier h)
    (c : NativeGram.Axis4 -> R) : HCarrier h :=
  HAdd h
    (HAdd h (HScale h (c NativeGram.D) d) (HScale h (c NativeGram.F) f))
    (HAdd h (HScale h (c NativeGram.N0) n0) (HScale h (c NativeGram.N1) n1)).

Theorem LHGP_HILBERT_GRAM_QUADRATIC_IS_NORM : forall h d f n0 n1 c,
  NativeGram.quadratic4 (HilbertGram4 h d f n0 n1) c =
    HNorm h (HCombine4 h d f n0 n1 c).
Proof.
  intros; unfold NativeGram.quadratic4, NativeGram.sum4,
    HilbertGram4, HPick4, HNorm, HCombine4.
  rewrite !HInner_add_l, !HInner_add_r, !HInner_scale_l, !HInner_scale_r; ring.
Qed.

Theorem LHGP_NATIVE_COMPLETED_GRAM_IS_PSD : forall h d f n0 n1,
  NativeGram.PSD4 (HilbertGram4 h d f n0 n1).
Proof.
  intros h d f n0 n1 c; rewrite LHGP_HILBERT_GRAM_QUADRATIC_IS_NORM.
  apply HNorm_nonnegative.
Qed.

Theorem LHGP_NATIVE_GRAM_FINITE_REALIZATION :
  forall h (b : OrthonormalBasis h) d f n0 n1 n i j,
    NativeGram.gram4 n (HAnalysis b d) (HAnalysis b f)
      (HAnalysis b n0) (HAnalysis b n1) i j =
    HilbertGram4 h
      (HFinite b (HAnalysis b d) n) (HFinite b (HAnalysis b f) n)
      (HFinite b (HAnalysis b n0) n) (HFinite b (HAnalysis b n1) n) i j.
Proof.
  intros h b d f n0 n1 n i j; destruct i, j;
    unfold NativeGram.gram4, NativeGram.pick4, HilbertGram4, HPick4;
    apply LHGP_NATIVE_DOT_FINITE_SYNTHESIS.
Qed.

Theorem LHGP_NATIVE_DOT_ANALYSIS_LIMIT :
  forall h (b : OrthonormalBasis h), HComplete h -> forall x y,
    SeqLimit (fun n => NativeKQ.dot n (HAnalysis b x) (HAnalysis b y)) (HInner h x y).
Proof.
  intros h b Hcomplete x y eps Heps.
  destruct (HAnalysis_linear_readout h b Hcomplete x y eps Heps) as [N HN].
  exists N; intros n Hn; rewrite NativeDot_linear_prefix; apply HN; exact Hn.
Qed.

Theorem LHGP_NATIVE_GRAM_ENTRYWISE_COMPLETION :
  forall h (b : OrthonormalBasis h), HComplete h -> forall d f n0 n1 i j,
    SeqLimit (fun n => NativeGram.gram4 n
      (HAnalysis b d) (HAnalysis b f) (HAnalysis b n0) (HAnalysis b n1) i j)
      (HilbertGram4 h d f n0 n1 i j).
Proof.
  intros h b Hcomplete d f n0 n1 i j; destruct i, j;
    unfold NativeGram.gram4, NativeGram.pick4, HilbertGram4, HPick4;
    apply LHGP_NATIVE_DOT_ANALYSIS_LIMIT; exact Hcomplete.
Qed.

Definition NativeGPMetric n g p q := NativeKQ.dot n (decode g p) (decode g q).

Definition NativeDecodedGram4 n g d f n0 n1 :=
  NativeGram.gram4 n (decode g d) (decode g f) (decode g n0) (decode g n1).

Lemma NativeGPMetric_ext : forall n g p p' q q',
  seq_eq p p' -> seq_eq q q' ->
    NativeGPMetric n g p q = NativeGPMetric n g p' q'.
Proof.
  intros n g p p' q q' Hp Hq; unfold NativeGPMetric.
  rewrite (NativeKQ.dot_ext_l n (decode g p) (decode g p')).
  - apply NativeKQ.dot_ext_r; intros i Hi; unfold decode; rewrite Hq; reflexivity.
  - intros i Hi; unfold decode; rewrite Hp; reflexivity.
Qed.

(* Arguments alternate old/new roles: d d' f f' n0 n0' n1 n1'. *)
Lemma NativeDecodedGram4_ext : forall n g d d' f f' n0 n0' n1 n1',
  seq_eq d d' -> seq_eq f f' -> seq_eq n0 n0' -> seq_eq n1 n1' ->
  forall i j,
    NativeDecodedGram4 n g d f n0 n1 i j =
    NativeDecodedGram4 n g d' f' n0' n1' i j.
Proof.
  intros n g d d' f f' n0 n0' n1 n1' Hd Hf H0 H1 i j; destruct i, j;
    unfold NativeDecodedGram4, NativeGram.gram4, NativeGram.pick4;
    apply NativeGPMetric_ext; assumption.
Qed.

Theorem LHGP_NATIVE_GP_METRIC_EXACT : forall n g a c,
  GPNonzero g -> NativeGPMetric n g (encode g a) (encode g c) = NativeKQ.dot n a c.
Proof.
  intros n g a c Hg; unfold NativeGPMetric.
  rewrite (NativeKQ.dot_ext_l n (decode g (encode g a)) a)
    by (intros; apply decode_encode; exact Hg).
  apply NativeKQ.dot_ext_r; intros; apply decode_encode; exact Hg.
Qed.

Theorem LHGP_NATIVE_GP_GRAM_EXACT : forall n g d f n0 n1,
  GPNonzero g -> forall i j,
    NativeDecodedGram4 n g (encode g d) (encode g f) (encode g n0) (encode g n1) i j =
    NativeGram.gram4 n d f n0 n1 i j.
Proof.
  intros n g d f n0 n1 Hg i j; destruct i, j;
    unfold NativeDecodedGram4, NativeGram.gram4, NativeGram.pick4;
    apply LHGP_NATIVE_GP_METRIC_EXACT; exact Hg.
Qed.

Theorem LHGP_NATIVE_GP_GRAM_FINITE_REALIZATION :
  forall h (b : OrthonormalBasis h) g,
  GPNonzero g -> forall d f n0 n1 n i j,
    NativeDecodedGram4 n g
      (HGPEncode b g d) (HGPEncode b g f) (HGPEncode b g n0) (HGPEncode b g n1) i j =
    HilbertGram4 h
      (HFinite b (HAnalysis b d) n) (HFinite b (HAnalysis b f) n)
      (HFinite b (HAnalysis b n0) n) (HFinite b (HAnalysis b n1) n) i j.
Proof.
  intros h b g Hg d f n0 n1 n i j; unfold HGPEncode.
  rewrite LHGP_NATIVE_GP_GRAM_EXACT by exact Hg.
  apply LHGP_NATIVE_GRAM_FINITE_REALIZATION.
Qed.

Theorem LHGP_NATIVE_GP_GRAM_COMPLETION :
  forall h (b : OrthonormalBasis h) g,
  HComplete h -> GPNonzero g -> forall d f n0 n1,
    NativeGram.PSD4 (HilbertGram4 h d f n0 n1) /\
    (forall i j, SeqLimit (fun n => NativeDecodedGram4 n g
      (HGPEncode b g d) (HGPEncode b g f) (HGPEncode b g n0) (HGPEncode b g n1) i j)
      (HilbertGram4 h d f n0 n1 i j)).
Proof.
  intros h b g Hcomplete Hg d f n0 n1; split.
  - apply LHGP_NATIVE_COMPLETED_GRAM_IS_PSD.
  - intros i j eps Heps.
    destruct (LHGP_NATIVE_GRAM_ENTRYWISE_COMPLETION h b Hcomplete d f n0 n1 i j eps Heps)
      as [N HN].
    exists N; intros n Hn; unfold HGPEncode.
    rewrite LHGP_NATIVE_GP_GRAM_EXACT by exact Hg.
    apply HN; exact Hn.
Qed.

Theorem LHGP_NATIVE_COMPLETED_GRAM_ZERO_BLOCK : forall h d f n0 n1,
  HInner h d n0 = 0 -> HInner h d n1 = 0 ->
  HilbertGram4 h d f n0 n1 NativeGram.D NativeGram.N0 = 0 /\
  HilbertGram4 h d f n0 n1 NativeGram.D NativeGram.N1 = 0 /\
  HilbertGram4 h d f n0 n1 NativeGram.N0 NativeGram.D = 0 /\
  HilbertGram4 h d f n0 n1 NativeGram.N1 NativeGram.D = 0.
Proof.
  intros h d f n0 n1 H0 H1; unfold HilbertGram4, HPick4.
  repeat split; try assumption; rewrite HInner_sym; assumption.
Qed.

Theorem LHGP_NATIVE_GP_GRAM_COMPLETION_STATE :
  forall h (b : OrthonormalBasis h) g,
  HComplete h -> GPNonzero g -> forall u p f n0 n1,
    seq_eq (HGPEncode b g u) p ->
    NativeGram.PSD4 (HilbertGram4 h u f n0 n1) /\
    (forall i j, SeqLimit (fun n => NativeDecodedGram4 n g
      p (HGPEncode b g f) (HGPEncode b g n0) (HGPEncode b g n1) i j)
      (HilbertGram4 h u f n0 n1 i j)).
Proof.
  intros h b g Hcomplete Hg u p f n0 n1 Hp.
  destruct (LHGP_NATIVE_GP_GRAM_COMPLETION h b g Hcomplete Hg u f n0 n1)
    as [Hpsd Hlimit].
  split; [exact Hpsd|]; intros i j eps Heps.
  destruct (Hlimit i j eps Heps) as [N HN]; exists N; intros n Hn.
  rewrite <- (NativeDecodedGram4_ext n g
    (HGPEncode b g u) p
    (HGPEncode b g f) (HGPEncode b g f)
    (HGPEncode b g n0) (HGPEncode b g n0)
    (HGPEncode b g n1) (HGPEncode b g n1)
    Hp (seq_eq_refl _) (seq_eq_refl _) (seq_eq_refl _) i j).
  apply HN; exact Hn.
Qed.

Print Assumptions LHGP_NATIVE_GRAM_FINITE_REALIZATION.
Print Assumptions LHGP_NATIVE_GRAM_ENTRYWISE_COMPLETION.
Print Assumptions LHGP_NATIVE_GP_GRAM_COMPLETION.
