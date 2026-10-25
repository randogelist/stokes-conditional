From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Bilinear.
Require Import LHGP_Realization LHGP_PathSynthesis.

Open Scope R_scope.

(* Forward readouts of an already specified Hilbert velocity. Only L2
   synthesis is used. No gradient reconstruction, H1 convergence, or
   projection of an ambient test into the velocity space is required.
   A physical application must still identify the Hilbert inner products
   and the inclusion with the actual spatial L2 pairings. *)

Definition ForwardCut {h : HilbertData} (b : OrthonormalBasis h)
  (x : HCarrier h) (n : nat) : HCarrier h :=
  HFinite b (HAnalysis b x) n.

Lemma ForwardCut_energy_bound : forall h (b : OrthonormalBasis h) x n,
  HNorm h (ForwardCut b x n) <= HNorm h x.
Proof.
  intros h b x n. unfold ForwardCut. rewrite HFinite_norm. apply HAnalysis_bessel.
Qed.

Lemma ForwardCut_length_bound : forall h (b : OrthonormalBasis h) x n,
  HLength h (ForwardCut b x n) <= HLength h x.
Proof.
  intros h b x n. unfold HLength. apply sqrt_le_1.
  - apply HNorm_nonnegative.
  - apply HNorm_nonnegative.
  - apply ForwardCut_energy_bound.
Qed.

Lemma forward_length_sub : forall h x y,
  HLength h (HSub h x y) = sqrt (HDist h x y).
Proof. intros h x y. unfold HLength. rewrite HNorm_sub. reflexivity. Qed.

Lemma forward_length_square : forall h x,
  HLength h x * HLength h x = HNorm h x.
Proof. intros h x. unfold HLength. apply sqrt_sqrt. apply HNorm_nonnegative. Qed.

Theorem HInner_length_bound : forall h x y,
  Rabs (HInner h x y) <= HLength h x * HLength h y.
Proof.
  intros h x y.
  pose proof (HInner_cauchy_schwarz h x y) as Hcs.
  pose proof (HNorm_nonnegative h x) as Hx.
  pose proof (HNorm_nonnegative h y) as Hy.
  assert (Hxx : 0 <= HInner h x y * HInner h x y) by nra.
  assert (Hxy : 0 <= HNorm h x * HNorm h y) by nra.
  pose proof (sqrt_le_1 _ _ Hxx Hxy Hcs) as Hsqrt.
  rewrite (sqrt_mult (HNorm h x) (HNorm h y) Hx Hy) in Hsqrt.
  change (sqrt (Rsqr (HInner h x y)) <= HLength h x * HLength h y) in Hsqrt.
  rewrite sqrt_Rsqr_abs in Hsqrt. exact Hsqrt.
Qed.

Section BoundedLinearForward.
Variable h : HilbertData.
Variable b : OrthonormalBasis h.
Variable L : HCarrier h -> R.
Hypothesis L_add : forall x y, L (HAdd h x y) = L x + L y.
Hypothesis L_scale : forall c x, L (HScale h c x) = c * L x.
Variable C : R.
Hypothesis C_nonnegative : 0 <= C.
Hypothesis L_bound : forall x, Rabs (L x) <= C * HLength h x.

Lemma forward_linear_zero : L (HZero h) = 0.
Proof.
  pose proof (L_add (HZero h) (HZero h)) as Hzero.
  rewrite HAdd_zero_left in Hzero. lra.
Qed.

Lemma forward_linear_sub : forall x y, L (HSub h x y) = L x - L y.
Proof. intros x y. unfold HSub. rewrite L_add, L_scale. ring. Qed.

Theorem FORWARD_LINEAR_FINITE : forall a n,
  linear_prefix a (fun i => L (HBasis h b i)) n = L (HFinite b a n).
Proof.
  intros a n. induction n as [|n IH]; simpl.
  - unfold linear_prefix. simpl. symmetry. apply forward_linear_zero.
  - rewrite L_add, L_scale, <- IH. reflexivity.
Qed.

Theorem FORWARD_LINEAR_COEFFICIENT_BOUND : forall n,
  energy_prefix (fun i => L (HBasis h b i)) n <= C * C.
Proof.
  intro n.
  set (a := fun i => L (HBasis h b i)).
  pose proof (L_bound (HFinite b a n)) as Hbound.
  rewrite <- FORWARD_LINEAR_FINITE in Hbound.
  change (Rabs (energy_prefix a n) <= C * HLength h (HFinite b a n)) in Hbound.
  unfold HLength in Hbound. rewrite HFinite_norm in Hbound.
  pose proof (energy_prefix_nonnegative a n) as HE.
  rewrite Rabs_right in Hbound by lra.
  pose proof (sqrt_pos (energy_prefix a n)) as Hsqrtpos.
  pose proof (sqrt_sqrt _ HE) as Hsqr.
  assert (Hroot : sqrt (energy_prefix a n) <= C) by nra.
  nra.
Qed.

Theorem FORWARD_LINEAR_COEFFICIENTS_L2 : CoordinateL2 (fun i => L (HBasis h b i)).
Proof. exists (C * C). apply FORWARD_LINEAR_COEFFICIENT_BOUND. Qed.

Theorem FORWARD_LINEAR_ERROR : forall x n,
  Rabs (linear_prefix (HAnalysis b x) (fun i => L (HBasis h b i)) n - L x)
  <= C * sqrt (HDist h (ForwardCut b x n) x).
Proof.
  intros x n. rewrite FORWARD_LINEAR_FINITE.
  change (Rabs (L (ForwardCut b x n) - L x) <=
    C * sqrt (HDist h (ForwardCut b x n) x)).
  rewrite <- forward_linear_sub, <- forward_length_sub. apply L_bound.
Qed.

Theorem FORWARD_LINEAR_CUT_BOUND : forall x n,
  Rabs (linear_prefix (HAnalysis b x) (fun i => L (HBasis h b i)) n)
  <= C * HLength h x.
Proof.
  intros x n. rewrite FORWARD_LINEAR_FINITE.
  eapply Rle_trans; [apply L_bound |].
  apply Rmult_le_compat_l; [exact C_nonnegative | apply ForwardCut_length_bound].
Qed.

Theorem FORWARD_LINEAR_STRONG_CONTINUOUS : forall u x,
  HConverges h u x -> SeqLimit (fun n => L (u n)) (L x).
Proof.
  intros u x Hstrong.
  assert (Hlength : SeqLimit (fun n => HLength h (HSub h (u n) x)) 0).
  { apply nonnegative_square_limit.
    - intro n. apply sqrt_pos.
    - apply HConverges_length_square. exact Hstrong. }
  intros eps Heps.
  assert (Hdenom : 0 < C + 1) by lra.
  assert (Hdelta : 0 < eps / (C + 1)).
  { apply Rdiv_lt_0_compat; assumption. }
  destruct (Hlength _ Hdelta) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  destruct (Rabs_def2 _ _ HN) as [Hsmall _].
  pose proof (sqrt_pos (HNorm h (HSub h (u n) x))) as Hnonnegative.
  change (0 <= HLength h (HSub h (u n) x)) in Hnonnegative.
  assert (Hproduct : HLength h (HSub h (u n) x) * (C + 1) < eps).
  { assert (Hm : HLength h (HSub h (u n) x) * (C + 1) <
      (eps / (C + 1)) * (C + 1)).
    { apply Rmult_lt_compat_r; [exact Hdenom | lra]. }
    replace ((eps / (C + 1)) * (C + 1)) with eps in Hm by (field; lra).
    exact Hm. }
  pose proof (L_bound (HSub h (u n) x)) as Hbound.
  rewrite forward_linear_sub in Hbound. nra.
Qed.

Theorem FORWARD_LINEAR_READOUT : HComplete h -> forall x,
  linear_limit (HAnalysis b x) (fun i => L (HBasis h b i)) (L x).
Proof.
  intros Hcomplete x. unfold linear_limit.
  apply (proj2 (SeqLimit_ext
    (linear_prefix (HAnalysis b x) (fun i => L (HBasis h b i)))
    (fun n => L (ForwardCut b x n)) (L x)
    (fun n => FORWARD_LINEAR_FINITE (HAnalysis b x) n))).
  apply FORWARD_LINEAR_STRONG_CONTINUOUS.
  apply HAnalysis_reconstruction. exact Hcomplete.
Qed.
End BoundedLinearForward.

Section AmbientTestForward.
Variables h k : HilbertData.
Variable b : OrthonormalBasis h.
Variable J : HCarrier h -> HCarrier k.
Hypothesis J_inner : forall x y, HInner k (J x) (J y) = HInner h x y.
Hypothesis J_add : forall x y, J (HAdd h x y) = HAdd k (J x) (J y).
Hypothesis J_scale : forall c x, J (HScale h c x) = HScale k c (J x).

Lemma ForwardAmbient_norm : forall x, HNorm k (J x) = HNorm h x.
Proof. intro x. apply J_inner. Qed.

Lemma ForwardAmbient_length : forall x, HLength k (J x) = HLength h x.
Proof. intro x. unfold HLength. rewrite ForwardAmbient_norm. reflexivity. Qed.

Lemma ForwardAmbient_linear_bound : forall z x,
  Rabs (HInner k (J x) z) <= HLength k z * HLength h x.
Proof.
  intros z x. pose proof (HInner_length_bound k (J x) z) as Hbound.
  rewrite ForwardAmbient_length in Hbound. nra.
Qed.

Lemma ForwardAmbient_linear_add : forall z x y,
  HInner k (J (HAdd h x y)) z = HInner k (J x) z + HInner k (J y) z.
Proof. intros z x y. rewrite J_add, HInner_add_l. reflexivity. Qed.

Lemma ForwardAmbient_linear_scale : forall z c x,
  HInner k (J (HScale h c x)) z = c * HInner k (J x) z.
Proof. intros z c x. rewrite J_scale, HInner_scale_l. reflexivity. Qed.

Theorem FORWARD_AMBIENT_TEST_COEFFICIENTS_L2 : forall z : HCarrier k,
  CoordinateL2 (fun i => HInner k (J (HBasis h b i)) z).
Proof.
  intro z. apply (FORWARD_LINEAR_COEFFICIENTS_L2 h b
    (fun x => HInner k (J x) z)
    (ForwardAmbient_linear_add z) (ForwardAmbient_linear_scale z)
    (HLength k z) (sqrt_pos (HNorm k z)) (ForwardAmbient_linear_bound z)).
Qed.

Theorem FORWARD_AMBIENT_TEST_ERROR : forall x (z : HCarrier k) n,
  Rabs (linear_prefix (HAnalysis b x)
    (fun i => HInner k (J (HBasis h b i)) z) n - HInner k (J x) z)
  <= HLength k z * sqrt (HDist h (ForwardCut b x n) x).
Proof.
  intros x z n. apply (FORWARD_LINEAR_ERROR h b (fun v => HInner k (J v) z)
    (ForwardAmbient_linear_add z) (ForwardAmbient_linear_scale z)
    (HLength k z) (ForwardAmbient_linear_bound z)).
Qed.

Theorem FORWARD_AMBIENT_TEST_READOUT : HComplete h -> forall x (z : HCarrier k),
  linear_limit (HAnalysis b x) (fun i => HInner k (J (HBasis h b i)) z)
    (HInner k (J x) z).
Proof.
  intros Hcomplete x z. apply (FORWARD_LINEAR_READOUT h b
    (fun v => HInner k (J v) z)
    (ForwardAmbient_linear_add z) (ForwardAmbient_linear_scale z)
    (HLength k z) (sqrt_pos (HNorm k z)) (ForwardAmbient_linear_bound z) Hcomplete).
Qed.

Theorem FORWARD_AMBIENT_GP_READOUT : HComplete h -> forall g x (z : HCarrier k),
  GPNonzero g ->
  linear_limit (decode g (HGPEncode b g x))
    (fun i => HInner k (J (HBasis h b i)) z) (HInner k (J x) z).
Proof.
  intros Hcomplete g x z Hg. unfold HGPEncode.
  apply (proj2 (gp_linear_limit_transport g (HAnalysis b x)
    (fun i => HInner k (J (HBasis h b i)) z) (HInner k (J x) z) Hg)).
  apply FORWARD_AMBIENT_TEST_READOUT. exact Hcomplete.
Qed.
End AmbientTestForward.

Section BoundedBilinearForward.
Variable h : HilbertData.
Variable b : OrthonormalBasis h.
Variable B : HCarrier h -> HCarrier h -> R.
Hypothesis B_add_left : forall x y z, B (HAdd h x y) z = B x z + B y z.
Hypothesis B_add_right : forall x y z, B x (HAdd h y z) = B x y + B x z.
Hypothesis B_scale_left : forall c x y, B (HScale h c x) y = c * B x y.
Hypothesis B_scale_right : forall c x y, B x (HScale h c y) = c * B x y.
Variable C : R.
Hypothesis C_nonnegative : 0 <= C.
Hypothesis B_bound : forall x y,
  Rabs (B x y) <= C * HLength h x * HLength h y.

Theorem FORWARD_QUADRATIC_FINITE : forall x n,
  quadratic_prefix (HAnalysis b x)
    (fun i j => B (HBasis h b i) (HBasis h b j)) n =
  B (ForwardCut b x n) (ForwardCut b x n).
Proof.
  intros x n.
  rewrite (quadratic_prefix_realization (HZero h) (HAdd h) (HScale h) B
    (HAdd_zero_left h) B_add_left B_add_right B_scale_left B_scale_right).
  rewrite HFinite_bilinear_same. reflexivity.
Qed.

Theorem FORWARD_QUADRATIC_ERROR : forall x n,
  Rabs (quadratic_prefix (HAnalysis b x)
    (fun i j => B (HBasis h b i) (HBasis h b j)) n - B x x)
  <= C * (HLength h (ForwardCut b x n) + HLength h x) *
    sqrt (HDist h (ForwardCut b x n) x).
Proof.
  intros x n. rewrite FORWARD_QUADRATIC_FINITE, <- forward_length_sub.
  apply (quadratic_stability_bound (HAdd h) (HSub h) (HLength h) B
    (HSub_restore h) B_add_left B_add_right C B_bound).
Qed.

Theorem FORWARD_QUADRATIC_ERROR_CAP : forall x n,
  Rabs (quadratic_prefix (HAnalysis b x)
    (fun i j => B (HBasis h b i) (HBasis h b j)) n - B x x)
  <= 2 * C * HLength h x * sqrt (HDist h (ForwardCut b x n) x).
Proof.
  intros x n. eapply Rle_trans; [apply FORWARD_QUADRATIC_ERROR |].
  apply Rmult_le_compat_r; [apply sqrt_pos |].
  pose proof (ForwardCut_length_bound h b x n) as Hlength.
  replace (2 * C * HLength h x) with (C * (2 * HLength h x)) by ring.
  apply Rmult_le_compat_l; [exact C_nonnegative | lra].
Qed.

Theorem FORWARD_QUADRATIC_DOMINATION : forall x n,
  Rabs (quadratic_prefix (HAnalysis b x)
    (fun i j => B (HBasis h b i) (HBasis h b j)) n) <= C * HNorm h x.
Proof.
  intros x n. rewrite FORWARD_QUADRATIC_FINITE.
  pose proof (B_bound (ForwardCut b x n) (ForwardCut b x n)) as Hbound.
  rewrite Rmult_assoc, forward_length_square in Hbound.
  eapply Rle_trans; [exact Hbound |].
  apply Rmult_le_compat_l; [exact C_nonnegative | apply ForwardCut_energy_bound].
Qed.

Theorem FORWARD_QUADRATIC_PATH_DOMINATION : forall (u : R -> HCarrier h) T M,
  (forall t, 0 <= t <= T -> HNorm h (u t) <= M) ->
  forall t, 0 <= t <= T -> forall n,
  Rabs (quadratic_prefix (HAnalysis b (u t))
    (fun i j => B (HBasis h b i) (HBasis h b j)) n) <= C * M.
Proof.
  intros u T M Hu t Ht n. eapply Rle_trans; [apply FORWARD_QUADRATIC_DOMINATION |].
  apply Rmult_le_compat_l; [exact C_nonnegative | apply Hu; exact Ht].
Qed.

Theorem FORWARD_QUADRATIC_READOUT_WITH_BOUNDS : HComplete h -> forall x,
  quadratic_limit (HAnalysis b x)
    (fun i j => B (HBasis h b i) (HBasis h b j)) (B x x) /\
  (forall n, Rabs (quadratic_prefix (HAnalysis b x)
    (fun i j => B (HBasis h b i) (HBasis h b j)) n - B x x)
    <= 2 * C * HLength h x * sqrt (HDist h (ForwardCut b x n) x)) /\
  (forall n, Rabs (quadratic_prefix (HAnalysis b x)
    (fun i j => B (HBasis h b i) (HBasis h b j)) n) <= C * HNorm h x).
Proof.
  intros Hcomplete x. split.
  - apply (LHGP_HILBERT_QUADRATIC_READOUT h b Hcomplete B
      B_add_left B_add_right B_scale_left B_scale_right C C_nonnegative B_bound).
  - split; [apply FORWARD_QUADRATIC_ERROR_CAP | apply FORWARD_QUADRATIC_DOMINATION].
Qed.
End BoundedBilinearForward.

Print Assumptions FORWARD_LINEAR_COEFFICIENTS_L2.
Print Assumptions FORWARD_AMBIENT_TEST_READOUT.
Print Assumptions FORWARD_QUADRATIC_ERROR.
Print Assumptions FORWARD_QUADRATIC_READOUT_WITH_BOUNDS.
