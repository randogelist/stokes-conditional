From Stdlib Require Import Reals Lra Psatz Lia.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Bilinear.

Open Scope R_scope.

(* A strict estimate on every finite prefix need not stay strict at its
   supremum.  The reverse implication below deliberately uses eps/2. *)
Definition EnergyInitialTrace (distance_energy : R -> R) : Prop :=
  forall eps, 0 < eps -> exists delta, 0 < delta /\
    forall t, 0 <= t < delta -> distance_energy t < eps.

Theorem LHGP_ENERGY_STRONG_INITIAL_TRACE_EXACT :
  forall a a0 distance_energy,
  (forall t, EnergyValue (coefficient_difference (a t) a0)
                        (distance_energy t)) ->
  (StrongInitialTrace a a0 <-> EnergyInitialTrace distance_energy).
Proof.
  intros a a0 distance_energy HE; split.
  - intros H eps Heps.
    destruct (H (eps / 2) ltac:(lra)) as [delta [Hdelta Hbound]].
    exists delta; split; [exact Hdelta |].
    intros t Ht.
    destruct (HE t) as [_ Hleast].
    assert (Hupper : forall n,
      energy_prefix (coefficient_difference (a t) a0) n <= eps / 2).
    { intro n; specialize (Hbound t Ht n); lra. }
    specialize (Hleast (eps / 2) Hupper); lra.
  - intros H eps Heps.
    destruct (H eps Heps) as [delta [Hdelta Hbound]].
    exists delta; split; [exact Hdelta |].
    intros t Ht n.
    destruct (HE t) as [Hupper _].
    specialize (Hupper n); specialize (Hbound t Ht); lra.
Qed.

(* HNorm and HDist in the Hilbert core denote squared norm and squared
   distance. HLength is their ordinary nonnegative square-root norm. *)
Definition HLength (h : HilbertData) (x : HCarrier h) := sqrt (HNorm h x).

Lemma HAdd_zero_left : forall h (x : HCarrier h),
  HAdd h (HZero h) x = x.
Proof.
  intros h x; apply HInner_ext; intro z.
  rewrite HInner_add_l, HInner_zero_l; ring.
Qed.

Lemma HFinite_bilinear_same : forall h (b : OrthonormalBasis h) a n,
  BilinearFinite (HZero h) (HAdd h) (HScale h) (HBasis h b) a n =
  HFinite b a n.
Proof.
  intros h b a n; induction n; simpl; [reflexivity | rewrite IHn; reflexivity].
Qed.

Lemma HConverges_length_square : forall h f x,
  HConverges h f x ->
  SeqLimit (fun n => HLength h (HSub h (f n) x) *
                     HLength h (HSub h (f n) x)) 0.
Proof.
  intros h f x Hconv eps Heps.
  destruct (Hconv eps Heps) as [N HN].
  exists N; intros n Hn; specialize (HN n Hn).
  unfold HLength; rewrite sqrt_sqrt by apply HNorm_nonnegative.
  rewrite HNorm_sub, Rminus_0_r, Rabs_right; [exact HN |].
  pose proof (HDist_nonnegative h (f n) x); lra.
Qed.

Theorem HAnalysis_linear_readout : forall (h : HilbertData)
  (b : OrthonormalBasis h), HComplete h -> forall x y : HCarrier h,
  linear_limit (HAnalysis b x) (HAnalysis b y) (HInner h x y).
Proof.
  intros h b Hcomplete x y.
  assert (Hread : forall n,
    linear_prefix (HAnalysis b x) (HAnalysis b y) n =
    HInner h (HFinite b (HAnalysis b x) n) y).
  { intro n. rewrite HFinite_inner. unfold linear_prefix.
    apply prefix_ext. intro i. unfold HAnalysis.
    rewrite (HInner_sym h (HBasis h b i) y). reflexivity. }
  intros eps Heps.
  pose proof (HNorm_nonnegative h y) as Hy.
  assert (Hdenom : 0 < HNorm h y + 1) by lra.
  assert (Hdelta : 0 < eps * eps / (HNorm h y + 1)).
  { apply Rdiv_lt_0_compat; [nra | exact Hdenom]. }
  destruct (HAnalysis_reconstruction h b Hcomplete x _ Hdelta) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn). rewrite Hread.
  pose proof (HInner_distance_bound h
    (HFinite b (HAnalysis b x) n) x y) as Hbound.
  pose proof (HDist_nonnegative h
    (HFinite b (HAnalysis b x) n) x) as Hd.
  assert (Hproduct :
    HDist h (HFinite b (HAnalysis b x) n) x * (HNorm h y + 1)
    < eps * eps).
  { assert (Hmult :
      HDist h (HFinite b (HAnalysis b x) n) x * (HNorm h y + 1)
      < (eps * eps / (HNorm h y + 1)) * (HNorm h y + 1)).
    { apply Rmult_lt_compat_r; assumption. }
    replace ((eps * eps / (HNorm h y + 1)) * (HNorm h y + 1))
      with (eps * eps) in Hmult by (field; lra).
    exact Hmult. }
  apply Rabs_def1; nra.
Qed.

Section HilbertBilinearRealization.
Variable h : HilbertData.
Variable b : OrthonormalBasis h.
Hypothesis Hcomplete : HComplete h.
Variable B : HCarrier h -> HCarrier h -> R.
Hypothesis Badd_left : forall x y z,
  B (HAdd h x y) z = B x z + B y z.
Hypothesis Badd_right : forall x y z,
  B x (HAdd h y z) = B x y + B x z.
Hypothesis Bscale_left : forall c x y,
  B (HScale h c x) y = c * B x y.
Hypothesis Bscale_right : forall c x y,
  B x (HScale h c y) = c * B x y.
Variable C : R.
Hypothesis Cnonnegative : 0 <= C.
Hypothesis Bbound : forall x y,
  Rabs (B x y) <= C * HLength h x * HLength h y.

Theorem LHGP_HILBERT_QUADRATIC_READOUT : forall x,
  quadratic_limit (HAnalysis b x)
    (fun i j => B (HBasis h b i) (HBasis h b j)) (B x x).
Proof.
  intro x.
  eapply (@quadratic_limit_from_squared_synthesis_bound (HCarrier h)
    (HZero h) (HAdd h) (HScale h) (HSub h) (HLength h) B
    (HAdd_zero_left h) (HSub_restore h)
    (fun z => sqrt_pos (HNorm h z))
    Badd_left Badd_right Bscale_left Bscale_right
    C Cnonnegative Bbound (HBasis h b) (HAnalysis b x) x
    (2 * HLength h x) O).
  - unfold HLength; pose proof (sqrt_pos (HNorm h x)); lra.
  - intros n Hn; rewrite HFinite_bilinear_same.
    assert (Hbound : HLength h (HFinite b (HAnalysis b x) n) <= HLength h x).
    { unfold HLength; apply sqrt_le_1.
      - apply HNorm_nonnegative.
      - apply HNorm_nonnegative.
      - rewrite HFinite_norm; apply HAnalysis_bessel. }
    lra.
  - apply HConverges_length_square.
    intros eps Heps.
    destruct (HAnalysis_reconstruction h b Hcomplete x eps Heps) as [N HN].
    exists N; intros n Hn; rewrite HFinite_bilinear_same; apply HN; exact Hn.
Qed.

Theorem LHGP_WEIGHTED_HILBERT_QUADRATIC_READOUT : forall g x,
  GPNonzero g ->
  quadratic_limit (decode g (HGPEncode b g x))
    (fun i j => B (HBasis h b i) (HBasis h b j)) (B x x).
Proof.
  intros g x Hg; unfold HGPEncode.
  apply (proj2 (gp_quadratic_limit_transport g (HAnalysis b x)
    (fun i j => B (HBasis h b i) (HBasis h b j)) (B x x) Hg)).
  apply LHGP_HILBERT_QUADRATIC_READOUT.
Qed.

Theorem LHGP_COMPLETE_READOUT_REALIZATION : forall g p,
  GPNonzero g -> GPL2 g p -> exists x,
  seq_eq (HGPEncode b g x) p /\
  EnergyValue (decode g p) (HNorm h x) /\
  (forall y, linear_limit (decode g p) (HAnalysis b y) (HInner h x y)) /\
  quadratic_limit (decode g p)
    (fun i j => B (HBasis h b i) (HBasis h b j)) (B x x) /\
  (forall y, seq_eq (HGPEncode b g y) p -> y = x).
Proof.
  intros g p Hg Hp.
  destruct (HGP_surjective_unique h b Hcomplete g p Hg Hp)
    as [x [Henc [HE Hunique]]].
  assert (Hdec : seq_eq (decode g p) (HAnalysis b x)).
  { intro i; unfold decode; rewrite <- (Henc i).
    unfold HGPEncode, encode; field; apply Hg. }
  exists x; split; [exact Henc |]; split; [exact HE |]; split.
  - intro y.
    apply (proj2 (linear_limit_ext _ _ (HAnalysis b y) (HInner h x y) Hdec)).
    apply HAnalysis_linear_readout; exact Hcomplete.
  - split; [|exact Hunique].
    apply (proj2 (quadratic_limit_ext _ _
      (fun i j => B (HBasis h b i) (HBasis h b j)) (B x x) Hdec)).
    apply LHGP_HILBERT_QUADRATIC_READOUT.
Qed.
End HilbertBilinearRealization.

Theorem LHGP_HILBERT_DISTANCE_ENERGY : forall h (b : OrthonormalBasis h),
  HComplete h -> forall x y,
  EnergyValue (coefficient_difference (HAnalysis b x) (HAnalysis b y))
    (HDist h x y).
Proof.
  intros h b Hcomplete x y.
  assert (Heq : seq_eq
    (coefficient_difference (HAnalysis b x) (HAnalysis b y))
    (HAnalysis b (HSub h x y))).
  { intro i; unfold coefficient_difference, HAnalysis.
    rewrite HInner_sub_l; reflexivity. }
  apply (proj2 (EnergyValue_ext _ _ (HDist h x y) Heq)).
  rewrite <- HNorm_sub; apply HAnalysis_parseval; exact Hcomplete.
Qed.

Theorem LHGP_HILBERT_STRONG_INITIAL_TRACE : forall h (b : OrthonormalBasis h),
  HComplete h -> forall (u : R -> HCarrier h) u0,
  (StrongInitialTrace (fun t => HAnalysis b (u t)) (HAnalysis b u0) <->
   EnergyInitialTrace (fun t => HDist h (u t) u0)).
Proof.
  intros h b Hcomplete u u0.
  apply LHGP_ENERGY_STRONG_INITIAL_TRACE_EXACT.
  intro t; apply LHGP_HILBERT_DISTANCE_ENERGY; exact Hcomplete.
Qed.

(* This relation uses the complete coefficient state, not just an energy
   scalar.  Subsequent Hilbert realization results supply its exact energy. *)
Theorem LHGP_WEIGHTED_ENERGY_STRONG_INITIAL_TRACE_EXACT :
  forall g a a0 distance_energy,
  GPNonzero g ->
  (forall t, EnergyValue (coefficient_difference (a t) a0)
                        (distance_energy t)) ->
  (StrongInitialTrace (decode_path g (encode_path g a))
                      (decode g (encode g a0)) <->
   EnergyInitialTrace distance_energy).
Proof.
  intros g a a0 distance_energy Hg HE.
  apply LHGP_ENERGY_STRONG_INITIAL_TRACE_EXACT.
  intro t.
  assert (Heq : seq_eq
    (coefficient_difference (decode_path g (encode_path g a) t)
                            (decode g (encode g a0)))
    (coefficient_difference (a t) a0)).
  { intro i; unfold coefficient_difference, decode_path, encode_path.
    rewrite (decode_encode g (a t) Hg i), (decode_encode g a0 Hg i).
    reflexivity. }
  apply (proj2 (EnergyValue_ext _ _ (distance_energy t) Heq)).
  apply HE.
Qed.
