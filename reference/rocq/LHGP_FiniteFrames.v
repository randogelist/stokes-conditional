From Stdlib Require Import Reals Lra Psatz Lia Arith.Compare_dec Field.
Require Import LHGP_Coordinates LHGP_Hilbert.

Open Scope R_scope.

(* Finite orthonormal-frame algebra, proved independently of an existing
   complete basis.  Projection, residual normalization, and one-vector
   extension are derived from the primitive Hilbert operations. *)

Definition FOrthonormal (h : HilbertData) (q : nat -> HCarrier h) (n : nat) : Prop :=
  forall i j, (i < n)%nat -> (j < n)%nat ->
    HInner h (q i) (q j) = if Nat.eq_dec i j then 1 else 0.

Fixpoint FFinite (h : HilbertData) (q : nat -> HCarrier h) (a : Seq) (n : nat)
    : HCarrier h :=
  match n with
  | O => HZero h
  | S k => HAdd h (FFinite h q a k) (HScale h (a k) (q k))
  end.

Definition FProjection h (q : nat -> HCarrier h) (x : HCarrier h) n :=
  FFinite h q (fun i => HInner h x (q i)) n.

Definition FResidual h (q : nat -> HCarrier h) (x : HCarrier h) n :=
  HSub h x (FProjection h q x n).

Definition FSpan h (q : nat -> HCarrier h) n (x : HCarrier h) : Prop :=
  exists a : Seq, FFinite h q a n = x.

Definition FNormalizedResidual h (q : nat -> HCarrier h) (x : HCarrier h) n :=
  HScale h (/ sqrt (HNorm h (FResidual h q x n))) (FResidual h q x n).

Definition FExtend h (q : nat -> HCarrier h) n (v : HCarrier h) i :=
  if Nat.eq_dec i n then v else q i.

Definition FExtendCoefficients (a : Seq) n c i :=
  if Nat.eq_dec i n then c else a i.

Lemma Fprefix_ext_below : forall f k n,
  (forall i, (i < n)%nat -> f i = k i) -> prefix f n = prefix k n.
Proof.
  intros f k n. induction n as [|n IH]; intro H; simpl; [reflexivity |].
  rewrite IH; [rewrite H; [reflexivity | lia] | intros i Hi; apply H; lia].
Qed.

Lemma FFinite_ext_below : forall h (q r : nat -> HCarrier h) a c n,
  (forall i, (i < n)%nat -> q i = r i) ->
  (forall i, (i < n)%nat -> a i = c i) ->
  FFinite h q a n = FFinite h r c n.
Proof.
  intros h q r a c n. induction n as [|n IH]; intros Hq Ha; simpl; [reflexivity |].
  rewrite IH; [rewrite Hq, Ha; try lia; reflexivity |
    intros i Hi; apply Hq; lia | intros i Hi; apply Ha; lia].
Qed.

Lemma FSpan_ext : forall h (q r : nat -> HCarrier h) n x,
  (forall i, (i < n)%nat -> q i = r i) ->
  (FSpan h q n x <-> FSpan h r n x).
Proof.
  intros h q r n x Heq. split; intros [a Ha]; exists a.
  - rewrite <- (FFinite_ext_below h q r a a n Heq (fun i Hi => eq_refl)). exact Ha.
  - rewrite (FFinite_ext_below h q r a a n Heq (fun i Hi => eq_refl)). exact Ha.
Qed.

Lemma FOrthonormal_ext : forall h (q r : nat -> HCarrier h) n,
  (forall i, (i < n)%nat -> q i = r i) ->
  (FOrthonormal h q n <-> FOrthonormal h r n).
Proof.
  intros h q r n Heq. split; intros HO i j Hi Hj.
  - rewrite <- (Heq i Hi), <- (Heq j Hj). apply HO; assumption.
  - rewrite (Heq i Hi), (Heq j Hj). apply HO; assumption.
Qed.

Lemma FOrthonormal_restrict : forall h q n k,
  FOrthonormal h q n -> (k <= n)%nat -> FOrthonormal h q k.
Proof. intros h q n k HO Hkn i j Hi Hj. apply HO; lia. Qed.

Lemma FFinite_inner : forall h q a n x,
  HInner h (FFinite h q a n) x =
  prefix (fun i => a i * HInner h (q i) x) n.
Proof.
  intros h q a n x. induction n as [|n IH]; simpl.
  - apply HInner_zero_l.
  - rewrite HInner_add_l, HInner_scale_l, IH. reflexivity.
Qed.

Lemma FFinite_inner_zero_right : forall h q a n y,
  (forall i, (i < n)%nat -> HInner h (q i) y = 0) ->
  HInner h (FFinite h q a n) y = 0.
Proof.
  intros h q a n y. induction n as [|n IH]; intro Horth; simpl.
  - apply HInner_zero_l.
  - rewrite HInner_add_l, HInner_scale_l, IH,
      (Horth n ltac:(lia)); [ring | intros i Hi; apply Horth; lia].
Qed.

Lemma FFinite_coefficient_cut : forall h q n,
  FOrthonormal h q n -> forall a k i,
  (k <= n)%nat -> (i < n)%nat ->
  HInner h (FFinite h q a k) (q i) =
    if Compare_dec.lt_dec i k then a i else 0.
Proof.
  intros h q n HO a k. induction k as [|k IH]; intros i Hk Hi; simpl.
  - rewrite HInner_zero_l. destruct (Compare_dec.lt_dec i O); [lia | reflexivity].
  - rewrite HInner_add_l, HInner_scale_l, (IH i ltac:(lia) Hi),
      (HO k i ltac:(lia) Hi).
    destruct (Compare_dec.lt_dec i k); destruct (Nat.eq_dec k i);
      destruct (Compare_dec.lt_dec i (S k)); subst; try lia; ring.
Qed.

Lemma FFinite_coefficient_inside : forall h q n,
  FOrthonormal h q n -> forall a i,
  (i < n)%nat -> HInner h (FFinite h q a n) (q i) = a i.
Proof.
  intros h q n HO a i Hi.
  rewrite (FFinite_coefficient_cut h q n HO a n i ltac:(lia) Hi).
  destruct (Compare_dec.lt_dec i n); [reflexivity | lia].
Qed.

Theorem FFinite_norm : forall h q n,
  FOrthonormal h q n -> forall a,
  HNorm h (FFinite h q a n) = energy_prefix a n.
Proof.
  intros h q n HO a. unfold HNorm. rewrite FFinite_inner.
  unfold energy_prefix. apply Fprefix_ext_below. intros i Hi.
  rewrite (HInner_sym h (q i) (FFinite h q a n)),
    (FFinite_coefficient_inside h q n HO a i Hi). reflexivity.
Qed.

Lemma FProjection_inner : forall h q x n,
  HInner h (FProjection h q x n) x =
    energy_prefix (fun i => HInner h x (q i)) n.
Proof.
  intros h q x n. unfold FProjection. rewrite FFinite_inner.
  unfold energy_prefix. apply prefix_ext. intro i.
  rewrite (HInner_sym h (q i) x). reflexivity.
Qed.

Lemma FProjection_norm : forall h q n,
  FOrthonormal h q n -> forall x,
  HNorm h (FProjection h q x n) =
    energy_prefix (fun i => HInner h x (q i)) n.
Proof. intros h q n HO x. apply FFinite_norm. exact HO. Qed.

Theorem FResidual_orthogonal : forall h q n,
  FOrthonormal h q n -> forall x i,
  (i < n)%nat -> HInner h (FResidual h q x n) (q i) = 0.
Proof.
  intros h q n HO x i Hi. unfold FResidual.
  rewrite HInner_sub_l. unfold FProjection.
  rewrite (FFinite_coefficient_inside h q n HO _ i Hi). ring.
Qed.

Theorem FOrthogonal_span : forall h q n x y,
  (forall i, (i < n)%nat -> HInner h y (q i) = 0) ->
  FSpan h q n x -> HInner h y x = 0.
Proof.
  intros h q n x y Hy [a Ha]. rewrite <- Ha, HInner_sym.
  apply FFinite_inner_zero_right. intros i Hi.
  rewrite HInner_sym. apply Hy. exact Hi.
Qed.

Lemma FProjection_recovers_finite : forall h q n,
  FOrthonormal h q n -> forall a,
  FProjection h q (FFinite h q a n) n = FFinite h q a n.
Proof.
  intros h q n HO a. unfold FProjection.
  apply FFinite_ext_below; [intros; reflexivity |].
  intros i Hi. apply FFinite_coefficient_inside; assumption.
Qed.

Theorem FProjection_fixed_iff_span : forall h q n,
  FOrthonormal h q n -> forall x,
  (FProjection h q x n = x <-> FSpan h q n x).
Proof.
  intros h q n HO x. split.
  - intro H. exists (fun i => HInner h x (q i)). exact H.
  - intros [a Ha]. rewrite <- Ha. apply FProjection_recovers_finite. exact HO.
Qed.

Theorem FResidual_zero_iff_span : forall h q n,
  FOrthonormal h q n -> forall x,
  (FResidual h q x n = HZero h <-> FSpan h q n x).
Proof.
  intros h q n HO x. split.
  - intro Hz. apply (proj1 (FProjection_fixed_iff_span h q n HO x)).
    symmetry. apply HSub_zero. exact Hz.
  - intro Hspan.
    pose proof (proj2 (FProjection_fixed_iff_span h q n HO x) Hspan) as Hp.
    unfold FResidual. rewrite Hp.
    apply HNorm_definite. rewrite HNorm_sub, HDist_refl. reflexivity.
Qed.

Theorem FResidual_norm : forall h q n,
  FOrthonormal h q n -> forall x,
  HNorm h (FResidual h q x n) =
    HNorm h x - energy_prefix (fun i => HInner h x (q i)) n.
Proof.
  intros h q n HO x. unfold FResidual. rewrite HNorm_sub.
  unfold HDist. rewrite (FProjection_norm h q n HO x),
    (HInner_sym h x (FProjection h q x n)), FProjection_inner. ring.
Qed.

Theorem FProjection_distance : forall h q n,
  FOrthonormal h q n -> forall x,
  HDist h (FProjection h q x n) x =
    HNorm h x - energy_prefix (fun i => HInner h x (q i)) n.
Proof.
  intros h q n HO x. rewrite HDist_sym, <- HNorm_sub.
  apply FResidual_norm. exact HO.
Qed.

Lemma FResidual_norm_positive : forall h q x n,
  FResidual h q x n <> HZero h -> 0 < HNorm h (FResidual h q x n).
Proof.
  intros h q x n Hnonzero.
  pose proof (HNorm_nonnegative h (FResidual h q x n)) as Hpos.
  destruct (Rlt_dec 0 (HNorm h (FResidual h q x n))) as [Hlt | Hnot]; [exact Hlt |].
  exfalso. apply Hnonzero. apply HNorm_definite. lra.
Qed.

Theorem FNormalizedResidual_norm : forall h q x n,
  FResidual h q x n <> HZero h ->
  HNorm h (FNormalizedResidual h q x n) = 1.
Proof.
  intros h q x n Hnonzero.
  pose proof (FResidual_norm_positive h q x n Hnonzero) as Hpos.
  pose proof (sqrt_lt_R0 _ Hpos) as Hroot.
  pose proof (sqrt_sqrt _ (Rlt_le _ _ Hpos)) as Hsquare.
  unfold FNormalizedResidual. rewrite HNorm_scale.
  set (s := sqrt (HNorm h (FResidual h q x n))) in *.
  rewrite <- Hsquare. field. lra.
Qed.

Theorem FNormalizedResidual_orthogonal : forall h q n,
  FOrthonormal h q n -> forall x i,
  (i < n)%nat -> HInner h (FNormalizedResidual h q x n) (q i) = 0.
Proof.
  intros h q n HO x i Hi. unfold FNormalizedResidual.
  rewrite HInner_scale_l, (FResidual_orthogonal h q n HO x i Hi). ring.
Qed.

Theorem FNormalizedResidual_scale_back : forall h q x n,
  FResidual h q x n <> HZero h ->
  HScale h (sqrt (HNorm h (FResidual h q x n)))
    (FNormalizedResidual h q x n) = FResidual h q x n.
Proof.
  intros h q x n Hnonzero.
  pose proof (FResidual_norm_positive h q x n Hnonzero) as Hpos.
  pose proof (sqrt_lt_R0 _ Hpos) as Hroot.
  apply HInner_ext. intro z. unfold FNormalizedResidual.
  rewrite !HInner_scale_l. field. lra.
Qed.

Lemma FExtend_below : forall h q n v i,
  (i < n)%nat -> FExtend h q n v i = q i.
Proof.
  intros h q n v i Hi. unfold FExtend.
  destruct (Nat.eq_dec i n); [lia | reflexivity].
Qed.

Lemma FExtend_at : forall h q n v, FExtend h q n v n = v.
Proof.
  intros h q n v. unfold FExtend.
  destruct (Nat.eq_dec n n); [reflexivity | contradiction].
Qed.

Theorem FFinite_extend : forall h q a n v c,
  FFinite h (FExtend h q n v) (FExtendCoefficients a n c) (S n) =
  HAdd h (FFinite h q a n) (HScale h c v).
Proof.
  intros h q a n v c. simpl.
  rewrite FExtend_at.
  assert (Ha : FExtendCoefficients a n c n = c).
  { unfold FExtendCoefficients. destruct (Nat.eq_dec n n); [reflexivity | contradiction]. }
  rewrite Ha.
  f_equal. apply FFinite_ext_below.
  - intros i Hi. apply FExtend_below. exact Hi.
  - intros i Hi. unfold FExtendCoefficients.
    destruct (Nat.eq_dec i n); [lia | reflexivity].
Qed.

Theorem FSpan_extend : forall h q n v x,
  FSpan h q n x -> FSpan h (FExtend h q n v) (S n) x.
Proof.
  intros h q n v x [a Ha]. exists (FExtendCoefficients a n 0).
  rewrite FFinite_extend, Ha. apply HInner_ext. intro z.
  rewrite HInner_add_l, HInner_scale_l. ring.
Qed.

Theorem FOrthonormal_extend_normalized : forall h q n,
  FOrthonormal h q n -> forall x,
  FResidual h q x n <> HZero h ->
  FOrthonormal h (FExtend h q n (FNormalizedResidual h q x n)) (S n).
Proof.
  intros h q n HO x Hnonzero i j Hi Hj. unfold FExtend.
  destruct (Nat.eq_dec i n) as [Hin | Hin];
    destruct (Nat.eq_dec j n) as [Hjn | Hjn].
  - subst i j. destruct (Nat.eq_dec n n); [| contradiction].
    apply FNormalizedResidual_norm. exact Hnonzero.
  - subst i. destruct (Nat.eq_dec n j); [lia |].
    apply FNormalizedResidual_orthogonal; [exact HO | lia].
  - subst j. destruct (Nat.eq_dec i n); [contradiction |].
    rewrite HInner_sym. apply FNormalizedResidual_orthogonal; [exact HO | lia].
  - apply HO; lia.
Qed.

Theorem FSpan_extend_normalized_contains : forall h q x n,
  FResidual h q x n <> HZero h ->
  FSpan h (FExtend h q n (FNormalizedResidual h q x n)) (S n) x.
Proof.
  intros h q x n Hnonzero.
  exists (FExtendCoefficients (fun i => HInner h x (q i)) n
    (sqrt (HNorm h (FResidual h q x n)))).
  rewrite FFinite_extend, FNormalizedResidual_scale_back by exact Hnonzero.
  apply HInner_ext. intro z.
  rewrite HInner_add_l. unfold FResidual.
  rewrite HInner_sub_l. unfold FProjection. ring.
Qed.

Print Assumptions FResidual_zero_iff_span.
Print Assumptions FNormalizedResidual_norm.
Print Assumptions FOrthonormal_extend_normalized.
Print Assumptions FSpan_extend_normalized_contains.
