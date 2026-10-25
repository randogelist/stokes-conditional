From Stdlib Require Import Reals Lra Psatz Lia Arith.Compare_dec.
Require Import LHGP_Coordinates LHGP_Readouts.

Open Scope R_scope.

(* Abstract real Hilbert realization.  The primitive hypotheses are inner
   product algebra, completeness, and an orthonormal separating family.
   Synthesis, reconstruction, square summability, and Parseval are conclusions.
   No concrete physical R^3 function space is constructed in this module. *)

Record HilbertData := {
  HCarrier : Type;
  HZero : HCarrier;
  HAdd : HCarrier -> HCarrier -> HCarrier;
  HScale : R -> HCarrier -> HCarrier;
  HInner : HCarrier -> HCarrier -> R;
  HInner_zero_l : forall x, HInner HZero x = 0;
  HInner_add_l : forall x y z,
    HInner (HAdd x y) z = HInner x z + HInner y z;
  HInner_scale_l : forall c x y,
    HInner (HScale c x) y = c * HInner x y;
  HInner_sym : forall x y, HInner x y = HInner y x;
  HInner_pos : forall x, 0 <= HInner x x;
  HInner_definite : forall x y,
    HInner x x + HInner y y - 2 * HInner x y = 0 -> x = y
}.

Definition HNorm (h : HilbertData) (x : HCarrier h) : R := HInner h x x.

Definition HSub (h : HilbertData) (x y : HCarrier h) : HCarrier h :=
  HAdd h x (HScale h (-1) y).

Definition HDist (h : HilbertData) (x y : HCarrier h) : R :=
  HNorm h x + HNorm h y - 2 * HInner h x y.

Definition HCauchy (h : HilbertData) (f : nat -> HCarrier h) : Prop :=
  forall eps : R, 0 < eps -> exists N : nat,
    forall n m : nat, (N <= n)%nat -> (N <= m)%nat ->
      HDist h (f n) (f m) < eps.

Definition HConverges (h : HilbertData) (f : nat -> HCarrier h)
    (x : HCarrier h) : Prop :=
  forall eps : R, 0 < eps -> exists N : nat,
    forall n : nat, (N <= n)%nat -> HDist h (f n) x < eps.

Definition HComplete (h : HilbertData) : Prop :=
  forall f, HCauchy h f -> exists x, HConverges h f x.

Record OrthonormalBasis (h : HilbertData) := {
  HBasis : nat -> HCarrier h;
  HBasis_orthonormal : forall i j,
    HInner h (HBasis i) (HBasis j) = if Nat.eq_dec i j then 1 else 0;
  HBasis_separating : forall x,
    (forall i, HInner h x (HBasis i) = 0) -> x = HZero h
}.

Definition HAnalysis {h : HilbertData} (b : OrthonormalBasis h)
    (x : HCarrier h) : Seq := fun i => HInner h x (HBasis h b i).

Fixpoint HFinite {h : HilbertData} (b : OrthonormalBasis h)
    (a : Seq) (n : nat) : HCarrier h :=
  match n with
  | O => HZero h
  | S k => HAdd h (HFinite b a k) (HScale h (a k) (HBasis h b k))
  end.

Definition HGPEncode {h : HilbertData} (b : OrthonormalBasis h)
    (g : Seq) (x : HCarrier h) : Seq := encode g (HAnalysis b x).

Section InnerAlgebra.
Variable h : HilbertData.

Lemma HInner_zero_r : forall x, HInner h x (HZero h) = 0.
Proof. intro x; rewrite HInner_sym; apply HInner_zero_l. Qed.

Lemma HInner_add_r : forall x y z,
  HInner h x (HAdd h y z) = HInner h x y + HInner h x z.
Proof.
  intros x y z; rewrite HInner_sym, HInner_add_l.
  rewrite (HInner_sym h y x), (HInner_sym h z x); reflexivity.
Qed.

Lemma HInner_scale_r : forall c x y,
  HInner h x (HScale h c y) = c * HInner h x y.
Proof.
  intros c x y; rewrite HInner_sym, HInner_scale_l, (HInner_sym h y x); reflexivity.
Qed.

Lemma HInner_sub_l : forall x y z,
  HInner h (HSub h x y) z = HInner h x z - HInner h y z.
Proof. intros; unfold HSub; rewrite HInner_add_l, HInner_scale_l; ring. Qed.

Lemma HInner_sub_r : forall x y z,
  HInner h x (HSub h y z) = HInner h x y - HInner h x z.
Proof. intros; unfold HSub; rewrite HInner_add_r, HInner_scale_r; ring. Qed.

Lemma HNorm_zero : HNorm h (HZero h) = 0.
Proof. unfold HNorm; apply HInner_zero_l. Qed.

Lemma HNorm_nonnegative : forall x, 0 <= HNorm h x.
Proof. apply HInner_pos. Qed.

Lemma HNorm_scale : forall c x, HNorm h (HScale h c x) = c * c * HNorm h x.
Proof.
  intros c x; unfold HNorm; rewrite HInner_scale_l, HInner_scale_r; ring.
Qed.

Lemma HNorm_add : forall x y,
  HNorm h (HAdd h x y) = HNorm h x + 2 * HInner h x y + HNorm h y.
Proof.
  intros x y; unfold HNorm.
  rewrite HInner_add_l; repeat rewrite HInner_add_r.
  rewrite (HInner_sym h y x); ring.
Qed.

Lemma HNorm_affine : forall x y c,
  HNorm h (HAdd h x (HScale h c y)) =
    HNorm h x + 2 * c * HInner h x y + c * c * HNorm h y.
Proof.
  intros x y c; rewrite HNorm_add, HInner_scale_r, HNorm_scale; ring.
Qed.

Lemma HNorm_sub : forall x y, HNorm h (HSub h x y) = HDist h x y.
Proof. intros x y; unfold HSub, HDist; rewrite HNorm_affine; ring. Qed.

Lemma HDist_nonnegative : forall x y, 0 <= HDist h x y.
Proof. intros x y; rewrite <- HNorm_sub; apply HNorm_nonnegative. Qed.

Lemma HDist_sym : forall x y, HDist h x y = HDist h y x.
Proof. intros x y; unfold HDist; rewrite (HInner_sym h y x); ring. Qed.

Lemma HDist_refl : forall x, HDist h x x = 0.
Proof. intro x; unfold HDist, HNorm; ring. Qed.

Lemma HInner_ext : forall x y,
  (forall z, HInner h x z = HInner h y z) -> x = y.
Proof.
  intros x y H; apply HInner_definite.
  pose proof (H x) as Hx; pose proof (H y) as Hy.
  rewrite (HInner_sym h y x) in Hx; lra.
Qed.

Lemma HNorm_definite : forall x, HNorm h x = 0 -> x = HZero h.
Proof.
  intros x Hx; apply HInner_definite.
  repeat rewrite HInner_zero_r; repeat rewrite HInner_zero_l; unfold HNorm in Hx; lra.
Qed.

Lemma HSub_zero : forall x y, HSub h x y = HZero h -> x = y.
Proof.
  intros x y H; apply HInner_definite.
  change (HDist h x y = 0); rewrite <- HNorm_sub, H, HNorm_zero; reflexivity.
Qed.

Lemma HSub_restore : forall x y, HAdd h (HSub h x y) y = x.
Proof.
  intros x y; apply HInner_ext; intro z; rewrite HInner_add_l, HInner_sub_l; ring.
Qed.

Lemma HInner_cauchy_schwarz : forall x y,
  HInner h x y * HInner h x y <= HNorm h x * HNorm h y.
Proof.
  intros x y.
  destruct (Req_EM_T (HNorm h y) 0) as [Hz|Hnz].
  - rewrite (HNorm_definite y Hz), HInner_zero_r, HNorm_zero; nra.
  - pose proof (HNorm_nonnegative y) as Hy.
    pose proof (HNorm_nonnegative
      (HAdd h (HScale h (HNorm h y) x)
        (HScale h (- HInner h x y) y))) as Hq.
    rewrite HNorm_affine, HNorm_scale, HInner_scale_l in Hq.
    nra.
Qed.

Lemma HInner_distance_bound : forall x y z,
  (HInner h x z - HInner h y z) * (HInner h x z - HInner h y z)
  <= HDist h x y * HNorm h z.
Proof.
  intros x y z; pose proof (HInner_cauchy_schwarz (HSub h x y) z) as H.
  rewrite HInner_sub_l, HNorm_sub in H; exact H.
Qed.

End InnerAlgebra.

Section OrthonormalRealization.
Variable h : HilbertData.
Variable b : OrthonormalBasis h.

Lemma Hprefix_ext_below : forall f k n,
  (forall i, (i < n)%nat -> f i = k i) -> prefix f n = prefix k n.
Proof.
  intros f k n; induction n as [|n IH]; intro H; simpl; [reflexivity|].
  rewrite IH; [rewrite H; [reflexivity|lia]|intros i Hi; apply H; lia].
Qed.

Lemma HBasis_norm : forall i, HNorm h (HBasis h b i) = 1.
Proof.
  intro i; unfold HNorm; rewrite HBasis_orthonormal.
  destruct (Nat.eq_dec i i); [reflexivity|contradiction].
Qed.

Lemma HFinite_inner : forall a n x,
  HInner h (HFinite b a n) x =
    prefix (fun i => a i * HInner h (HBasis h b i) x) n.
Proof.
  intros a n x; induction n as [|n IH]; simpl.
  - apply HInner_zero_l.
  - rewrite HInner_add_l, HInner_scale_l, IH; reflexivity.
Qed.

Lemma HFinite_coefficient : forall a n i,
  HInner h (HFinite b a n) (HBasis h b i) =
    if Compare_dec.lt_dec i n then a i else 0.
Proof.
  intros a n; induction n as [|n IH]; intro i; simpl.
  - rewrite HInner_zero_l; destruct (Compare_dec.lt_dec i 0); [lia|reflexivity].
  - rewrite HInner_add_l, HInner_scale_l, IH, HBasis_orthonormal.
    destruct (Compare_dec.lt_dec i n); destruct (Nat.eq_dec n i);
      destruct (Compare_dec.lt_dec i (S n)); subst; try lia; ring.
Qed.

Lemma HFinite_coefficient_inside : forall a n i,
  (i < n)%nat -> HInner h (HFinite b a n) (HBasis h b i) = a i.
Proof.
  intros a n i H; rewrite HFinite_coefficient; destruct (Compare_dec.lt_dec i n); [reflexivity|lia].
Qed.

Lemma HFinite_coefficient_outside : forall a n i,
  (n <= i)%nat -> HInner h (HFinite b a n) (HBasis h b i) = 0.
Proof.
  intros a n i H; rewrite HFinite_coefficient; destruct (Compare_dec.lt_dec i n); [lia|reflexivity].
Qed.

Theorem HFinite_norm : forall a n, HNorm h (HFinite b a n) = energy_prefix a n.
Proof.
  intros a n; induction n as [|n IH].
  - simpl; apply HNorm_zero.
  - simpl; rewrite HNorm_affine, IH, HBasis_norm.
    rewrite HFinite_coefficient_outside by lia.
    unfold energy_prefix; simpl; ring.
Qed.

Lemma HFinite_inner_nested : forall a n m,
  (n <= m)%nat -> HInner h (HFinite b a m) (HFinite b a n) = energy_prefix a n.
Proof.
  intros a n m Hnm; rewrite HInner_sym, HFinite_inner.
  unfold energy_prefix; apply Hprefix_ext_below; intros i Hi.
  rewrite HInner_sym, HFinite_coefficient_inside by lia; reflexivity.
Qed.

Theorem HFinite_tail_distance : forall a n m,
  (n <= m)%nat -> HDist h (HFinite b a m) (HFinite b a n) =
    energy_prefix a m - energy_prefix a n.
Proof.
  intros a n m Hnm; unfold HDist.
  rewrite !HFinite_norm, HFinite_inner_nested by exact Hnm; ring.
Qed.

Theorem HFinite_cauchy : forall a,
  CoordinateL2 a -> HCauchy h (HFinite b a).
Proof.
  intros a HL2 eps Heps.
  destruct (CoordinateL2_tail a HL2 eps Heps) as [N HN].
  exists N; intros n m Hn Hm.
  destruct (Compare_dec.le_dec n m) as [Hnm|Hmn].
  - rewrite HDist_sym, HFinite_tail_distance by exact Hnm.
    pose proof (HN m Hm) as HM.
    pose proof (energy_prefix_monotone a N n Hn); lra.
  - rewrite HFinite_tail_distance by lia.
    pose proof (HN n Hn) as HM.
    pose proof (energy_prefix_monotone a N m Hm); lra.
Qed.

Theorem HFinite_limit_coordinates : forall a x,
  HConverges h (HFinite b a) x -> seq_eq (HAnalysis b x) a.
Proof.
  intros a x Hconv i; unfold HAnalysis.
  destruct (Req_EM_T (HInner h x (HBasis h b i)) (a i)) as [Heq|Hneq]; [exact Heq|].
  assert (Heps : 0 < (a i - HInner h x (HBasis h b i)) *
    (a i - HInner h x (HBasis h b i))) by nra.
  destruct (Hconv _ Heps) as [N HN].
  specialize (HN (Nat.max N (S i)) (Nat.le_max_l _ _)).
  pose proof (HInner_distance_bound h
    (HFinite b a (Nat.max N (S i))) x (HBasis h b i)) as Hbound.
  rewrite HFinite_coefficient_inside in Hbound by
    (pose proof (Nat.le_max_r N (S i)); lia).
  rewrite HBasis_norm in Hbound; nra.
Qed.

Theorem HAnalysis_injective : forall x y,
  seq_eq (HAnalysis b x) (HAnalysis b y) -> x = y.
Proof.
  intros x y Heq; apply HSub_zero.
  apply (HBasis_separating h b); intro i; rewrite HInner_sub_l.
  specialize (Heq i); unfold HAnalysis in Heq; lra.
Qed.

Lemma HAnalysis_projection_inner : forall x n,
  HInner h x (HFinite b (HAnalysis b x) n) =
    energy_prefix (HAnalysis b x) n.
Proof.
  intros x n; rewrite HInner_sym, HFinite_inner.
  unfold energy_prefix; apply prefix_ext; intro i.
  unfold HAnalysis; rewrite (HInner_sym h (HBasis h b i) x); reflexivity.
Qed.

Theorem HAnalysis_residual : forall x n,
  HDist h x (HFinite b (HAnalysis b x) n) =
    HNorm h x - energy_prefix (HAnalysis b x) n.
Proof.
  intros x n; unfold HDist; rewrite HFinite_norm, HAnalysis_projection_inner; ring.
Qed.

Theorem HAnalysis_bessel : forall x n,
  energy_prefix (HAnalysis b x) n <= HNorm h x.
Proof.
  intros x n; pose proof (HDist_nonnegative h x (HFinite b (HAnalysis b x) n)) as H.
  rewrite HAnalysis_residual in H; lra.
Qed.

Theorem HAnalysis_L2 : forall x, CoordinateL2 (HAnalysis b x).
Proof. intro x; exists (HNorm h x); intro n; apply HAnalysis_bessel. Qed.

Theorem HAnalysis_reconstruction : HComplete h -> forall x,
  HConverges h (HFinite b (HAnalysis b x)) x.
Proof.
  intros Hcomplete x.
  destruct (Hcomplete _ (HFinite_cauchy _ (HAnalysis_L2 x))) as [y Hy].
  pose proof (HFinite_limit_coordinates _ _ Hy) as Hcoords.
  assert (Heq : y = x) by (apply HAnalysis_injective; exact Hcoords).
  rewrite Heq in Hy; exact Hy.
Qed.

Theorem HAnalysis_parseval : HComplete h -> forall x,
  EnergyValue (HAnalysis b x) (HNorm h x).
Proof.
  intros Hcomplete x; split; [apply HAnalysis_bessel|].
  intros B HB; destruct (Rle_dec (HNorm h x) B) as [Hle|Hnot]; [exact Hle|].
  assert (Heps : 0 < HNorm h x - B) by lra.
  destruct (HAnalysis_reconstruction Hcomplete x _ Heps) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  rewrite HDist_sym, HAnalysis_residual in HN.
  specialize (HB N); lra.
Qed.

Theorem HSynthesis_exists : HComplete h -> forall a,
  CoordinateL2 a -> exists x,
    seq_eq (HAnalysis b x) a /\
    HConverges h (HFinite b a) x /\
    EnergyValue a (HNorm h x).
Proof.
  intros Hcomplete a HL2.
  destruct (Hcomplete _ (HFinite_cauchy a HL2)) as [x Hconv].
  pose proof (HFinite_limit_coordinates a x Hconv) as Heq.
  exists x; split; [exact Heq|]; split; [exact Hconv|].
  apply (proj1 (EnergyValue_ext (HAnalysis b x) a (HNorm h x) Heq)).
  apply HAnalysis_parseval; exact Hcomplete.
Qed.

Theorem HSynthesis_unique : HComplete h -> forall a,
  CoordinateL2 a -> exists x,
    seq_eq (HAnalysis b x) a /\
    (forall y, seq_eq (HAnalysis b y) a -> y = x).
Proof.
  intros Hcomplete a HL2.
  destruct (HSynthesis_exists Hcomplete a HL2) as [x [Hx _]].
  exists x; split; [exact Hx|].
  intros y Hy; apply HAnalysis_injective; intro i; rewrite Hy, Hx; reflexivity.
Qed.

Theorem HGP_energy_exact : forall g x,
  HComplete h -> GPNonzero g ->
  EnergyValue (decode g (HGPEncode b g x)) (HNorm h x).
Proof.
  intros g x Hcomplete Hg; unfold HGPEncode.
  apply (proj2 (GP_energy_value_exact g (HAnalysis b x) (HNorm h x) Hg)).
  apply HAnalysis_parseval; exact Hcomplete.
Qed.

Theorem HGP_L2 : forall g x,
  GPNonzero g -> GPL2 g (HGPEncode b g x).
Proof.
  intros g x Hg; unfold HGPEncode; apply (proj2 (GP_L2_exact g (HAnalysis b x) Hg)).
  apply HAnalysis_L2.
Qed.

Theorem HGP_injective : forall g x y,
  GPNonzero g -> seq_eq (HGPEncode b g x) (HGPEncode b g y) -> x = y.
Proof.
  intros g x y Hg Heq; apply HAnalysis_injective.
  apply (encode_injective g); [exact Hg|exact Heq].
Qed.

Theorem HGP_surjective_unique : HComplete h -> forall g p,
  GPNonzero g -> GPL2 g p -> exists x,
    seq_eq (HGPEncode b g x) p /\
    EnergyValue (decode g p) (HNorm h x) /\
    (forall y, seq_eq (HGPEncode b g y) p -> y = x).
Proof.
  intros Hcomplete g p Hg Hp.
  destruct (HSynthesis_exists Hcomplete (decode g p) Hp)
    as [x [Hx [Hconv HE]]].
  assert (Hencoded : seq_eq (HGPEncode b g x) p).
  { intro i; unfold HGPEncode, encode; rewrite Hx.
    apply (encode_decode g p Hg i). }
  exists x; split; [exact Hencoded|]; split; [exact HE|].
  intros y Hy; apply (HGP_injective g); [exact Hg|].
  intro i; rewrite Hy, Hencoded; reflexivity.
Qed.

End OrthonormalRealization.

Print Assumptions HFinite_norm.
Print Assumptions HAnalysis_reconstruction.
Print Assumptions HAnalysis_parseval.
Print Assumptions HSynthesis_exists.
Print Assumptions HGP_surjective_unique.
