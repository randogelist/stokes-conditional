From Stdlib Require Import Reals Lra Psatz Lia Field ClassicalChoice.
Require Import LHGP_Hilbert LHGP_Readouts LHGP_Quantization
  LHGP_DissipationTopology LHGP_SobolevGraph LHGP_ClosedSubspace.

Open Scope R_scope.

(* Orthogonal projection is constructed from completeness and closed linearity.
   No projection, basis, minimizing point, or physical L2 realization is a
   field of the premises. HNorm and HDist are squared norms and distances. *)

Definition IsOrthogonalProjection {h : HilbertData}
    (s : ClosedLinearSubspace h) (x y : HCarrier h) : Prop :=
  subspace_predicate s y /\ forall z, subspace_predicate s z ->
    HInner h (HSub h x y) z = 0.

Section ProjectionConstruction.
Variable h : HilbertData.
Variable s : ClosedLinearSubspace h.

Lemma PROJECTION_DISTANCE_PARALLELOGRAM : forall x y z,
  HDist h y z = 2 * HDist h x y + 2 * HDist h x z -
    4 * HDist h x (HScale h (/2) (HAdd h y z)).
Proof.
  intros; unfold HDist; rewrite HNorm_scale, HNorm_add,
    HInner_scale_r, HInner_add_r; field.
Qed.

Lemma PROJECTION_DISTANCE_CONTINUOUS : forall f y x,
  HConverges h f y ->
  SeqLimit (fun n => HDist h x (f n)) (HDist h x y).
Proof.
  intros f y x Hconv eps Heps.
  pose proof (SOBOLEV_HNORM_STRONG_CONTINUOUS h f y Hconv) as Hnorm.
  pose proof (HStrongSequential_to_weak h f y Hconv x) as Hpair.
  destruct (Hnorm (eps/2) ltac:(lra)) as [N HN].
  destruct (Hpair (eps/4) ltac:(lra)) as [M HM].
  exists (Nat.max N M); intros n Hn.
  specialize (HN n ltac:(lia)); specialize (HM n ltac:(lia)).
  destruct (Rabs_def2 _ _ HN) as [Hnp Hnm].
  destruct (Rabs_def2 _ _ HM) as [Hmp Hmm].
  unfold HDist; rewrite (HInner_sym h x (f n)), (HInner_sym h x y).
  apply Rabs_def1; lra.
Qed.

Lemma PROJECTION_DISTANCE_INFIMUM : forall x,
  exists d, (forall y, subspace_predicate s y -> d <= HDist h x y) /\
    (forall eps, 0 < eps -> exists y,
      subspace_predicate s y /\ HDist h x y < d + eps).
Proof.
  intro x.
  set (E := fun r : R => exists y, subspace_predicate s y /\ r = - HDist h x y).
  assert (Hb : bound E).
  { exists 0; intros r [y [Hy Hr]]. subst r.
    pose proof (HDist_nonnegative h x y); lra. }
  assert (Hne : exists r, E r).
  { exists (-HDist h x (HZero h)); exists (HZero h); split;
      [apply subspace_zero|reflexivity]. }
  destruct (completeness E Hb Hne) as [a [Ha Hleast]].
  exists (-a); split.
  - intros y Hy; specialize (Ha (-HDist h x y)).
    assert (E (-HDist h x y)) by (exists y; auto). specialize (Ha H); lra.
  - intros eps Heps.
    destruct (classic (exists y, subspace_predicate s y /\
      HDist h x y < -a + eps)) as [Hyes|Hno]; [exact Hyes|].
    assert (Hub : is_upper_bound E (a-eps)).
    { intros r [y [Hy Hr]]. subst r.
      destruct (Rlt_dec (HDist h x y) (-a+eps)) as [Hl|Hl].
      - exfalso; apply Hno; exists y; auto.
      - lra. }
    specialize (Hleast (a-eps) Hub); lra.
Qed.

Theorem CLOSED_SUBSPACE_MINIMIZER : HComplete h -> forall x,
  exists y, subspace_predicate s y /\
    forall z, subspace_predicate s z -> HDist h x y <= HDist h x z.
Proof.
  intros Hcomplete x.
  destruct (PROJECTION_DISTANCE_INFIMUM x) as [d [Hlower Happrox]].
  assert (Hap : forall n : nat, exists y,
    subspace_predicate s y /\ HDist h x y < d + 1 / QuantDen n).
  { intro n; apply Happrox; apply Rdiv_lt_0_compat; [lra|apply QuantDen_positive]. }
  destruct (choice _ Hap) as [f Hf].
  assert (Hfc : HCauchy h f).
  { intros eps Heps.
    destruct (QUANTIZE_MESH_TENDS_ZERO (eps/4) ltac:(lra)) as [N HN].
    exists N; intros n m Hn Hm.
    destruct (Hf n) as [Hfn Hdn]; destruct (Hf m) as [Hfm Hdm].
    pose proof (Hlower (HScale h (/2) (HAdd h (f n) (f m)))) as Hmid.
    assert (Hms : subspace_predicate s (HScale h (/2) (HAdd h (f n) (f m)))).
    { apply subspace_scale; apply subspace_add; assumption. }
    specialize (Hmid Hms); specialize (HN n Hn) as Hnn.
    specialize (HN m Hm) as Hmm.
    rewrite (PROJECTION_DISTANCE_PARALLELOGRAM x (f n) (f m)); lra. }
  destruct (Hcomplete f Hfc) as [y Hconv].
  assert (Hy : subspace_predicate s y).
  { eapply subspace_strong_closed; [intro n; apply (proj1 (Hf n))|exact Hconv]. }
  assert (Hlim : SeqLimit (fun n => HDist h x (f n)) d).
  { intros eps Heps.
    destruct (QUANTIZE_MESH_TENDS_ZERO eps Heps) as [N HN].
    exists N; intros n Hn.
    destruct (Hf n) as [Hfn Hdn]; specialize (Hlower (f n) Hfn).
    specialize (HN n Hn); apply Rabs_def1; lra. }
  assert (Heq : HDist h x y = d).
  { eapply SeqLimit_unique; [apply PROJECTION_DISTANCE_CONTINUOUS; exact Hconv|exact Hlim]. }
  exists y; split; [exact Hy|intros z Hz; rewrite Heq; apply Hlower; exact Hz].
Qed.

Lemma PROJECTION_DISTANCE_VARIATION : forall x y z c,
  HDist h x (HAdd h y (HScale h c z)) = HDist h x y -
    2*c*HInner h (HSub h x y) z + c*c*HNorm h z.
Proof.
  intros; unfold HDist; rewrite HNorm_affine, HInner_add_r,
    HInner_scale_r, HInner_sub_l; ring.
Qed.

Theorem CLOSED_SUBSPACE_ORTHOGONAL_PROJECTION_EXISTS : HComplete h ->
  forall x, exists y, IsOrthogonalProjection s x y.
Proof.
  intros Hcomplete x.
  destruct (CLOSED_SUBSPACE_MINIMIZER Hcomplete x) as [y [Hy Hmin]].
  exists y; split; [exact Hy|].
  intros z Hz.
  set (r := HInner h (HSub h x y) z).
  set (q := HNorm h z).
  assert (Hq : 0 <= q) by (unfold q; apply HNorm_nonnegative).
  set (c := r/(q+1)).
  assert (Hc : c*(q+1)=r) by (unfold c; field; lra).
  specialize (Hmin (HAdd h y (HScale h c z))).
  assert (Hys : subspace_predicate s (HAdd h y (HScale h c z))).
  { apply subspace_add; [exact Hy|apply subspace_scale; exact Hz]. }
  specialize (Hmin Hys); rewrite PROJECTION_DISTANCE_VARIATION in Hmin.
  fold r q in Hmin.
  assert (Hr : r = 0).
  { assert (Hcq : c*r = c*c*(q+1)) by nra.
    assert (Hcc : c*c = 0) by nra.
    assert (Hcz : c=0) by nra. nra. }
  exact Hr.
Qed.

Theorem ORTHOGONAL_PROJECTION_UNIQUE : forall x y z,
  IsOrthogonalProjection s x y -> IsOrthogonalProjection s x z -> y=z.
Proof.
  intros x y z [Hy Hyo] [Hz Hzo].
  assert (Hsub : subspace_predicate s (HSub h y z)).
  { unfold HSub; apply subspace_add; [exact Hy|apply subspace_scale; exact Hz]. }
  specialize (Hyo (HSub h y z) Hsub); specialize (Hzo (HSub h y z) Hsub).
  rewrite !HInner_sub_l, !HInner_sub_r in Hyo, Hzo.
  rewrite (HInner_sym h z y) in Hzo.
  apply HInner_definite; lra.
Qed.

Theorem CLOSED_SUBSPACE_PROJECTION_MAP_EXISTS : HComplete h ->
  exists P : HCarrier h -> HCarrier h,
    forall x, IsOrthogonalProjection s x (P x).
Proof.
  intro Hcomplete; apply unique_choice; intro x.
  destruct (CLOSED_SUBSPACE_ORTHOGONAL_PROJECTION_EXISTS Hcomplete x) as [y Hy].
  exists y; split; [exact Hy|].
  intros z Hz; eapply ORTHOGONAL_PROJECTION_UNIQUE; eassumption.
Qed.

Variable P : HCarrier h -> HCarrier h.
Hypothesis Pspec : forall x, IsOrthogonalProjection s x (P x).

Theorem ORTHOGONAL_PROJECTION_IN_SUBSPACE : forall x,
  subspace_predicate s (P x).
Proof. intro x; apply (proj1 (Pspec x)). Qed.

Theorem ORTHOGONAL_PROJECTION_PAIRING : forall x u,
  subspace_predicate s u -> HInner h u (P x) = HInner h u x.
Proof.
  intros x u Hu; pose proof (proj2 (Pspec x) u Hu) as H.
  rewrite HInner_sub_l, (HInner_sym h x u), (HInner_sym h (P x) u) in H.
  lra.
Qed.

Theorem ORTHOGONAL_PROJECTION_ADD : forall x y,
  P (HAdd h x y) = HAdd h (P x) (P y).
Proof.
  intros x y; apply (ORTHOGONAL_PROJECTION_UNIQUE (HAdd h x y));
    [apply Pspec|].
  split.
  - apply subspace_add; apply ORTHOGONAL_PROJECTION_IN_SUBSPACE.
  - intros z Hz.
    pose proof (proj2 (Pspec x) z Hz) as Hx.
    pose proof (proj2 (Pspec y) z Hz) as Hy.
    rewrite HInner_sub_l in Hx, Hy.
    rewrite HInner_sub_l, !HInner_add_l; lra.
Qed.

Theorem ORTHOGONAL_PROJECTION_SCALE : forall c x,
  P (HScale h c x) = HScale h c (P x).
Proof.
  intros c x; apply (ORTHOGONAL_PROJECTION_UNIQUE (HScale h c x));
    [apply Pspec|].
  split.
  - apply subspace_scale; apply ORTHOGONAL_PROJECTION_IN_SUBSPACE.
  - intros z Hz; pose proof (proj2 (Pspec x) z Hz) as Hx.
    rewrite HInner_sub_l in Hx.
    rewrite HInner_sub_l, !HInner_scale_l; nra.
Qed.

Theorem ORTHOGONAL_PROJECTION_FIXED : forall x,
  subspace_predicate s x -> P x = x.
Proof.
  intros x Hx; apply (ORTHOGONAL_PROJECTION_UNIQUE x); [apply Pspec|].
  split; [exact Hx|intros z Hz; rewrite HInner_sub_l; ring].
Qed.

Theorem ORTHOGONAL_PROJECTION_IDEMPOTENT : forall x, P (P x) = P x.
Proof. intro x; apply ORTHOGONAL_PROJECTION_FIXED; apply ORTHOGONAL_PROJECTION_IN_SUBSPACE. Qed.

Theorem ORTHOGONAL_PROJECTION_PYTHAGORAS : forall x,
  HNorm h x = HNorm h (P x) + HDist h x (P x).
Proof.
  intro x.
  pose proof (ORTHOGONAL_PROJECTION_PAIRING x (P x)
    (ORTHOGONAL_PROJECTION_IN_SUBSPACE x)) as Hp.
  unfold HNorm, HDist; rewrite (HInner_sym h x (P x)); unfold HNorm; lra.
Qed.

Theorem ORTHOGONAL_PROJECTION_NORM_BOUND : forall x,
  HNorm h (P x) <= HNorm h x.
Proof.
  intro x; pose proof (ORTHOGONAL_PROJECTION_PYTHAGORAS x).
  pose proof (HDist_nonnegative h x (P x)); lra.
Qed.

Theorem ORTHOGONAL_PROJECTION_CONTRACTION : forall x y,
  HDist h (P x) (P y) <= HDist h x y.
Proof.
  intros x y.
  pose proof (ORTHOGONAL_PROJECTION_NORM_BOUND (HSub h x y)) as H.
  unfold HSub at 1 in H; rewrite ORTHOGONAL_PROJECTION_ADD,
    ORTHOGONAL_PROJECTION_SCALE in H.
  change (HNorm h (HSub h (P x) (P y)) <= HNorm h (HSub h x y)) in H.
  rewrite !HNorm_sub in H; exact H.
Qed.

End ProjectionConstruction.
