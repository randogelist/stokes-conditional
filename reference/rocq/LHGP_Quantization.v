From Stdlib Require Import Reals R_Ifp ZArith List Lra Psatz Lia Field.

Open Scope R_scope.

(* A genuine finite-range scalar quantizer.  Stage m has mesh 1/(m+1)
   and clipping radius m+1. Its interval fibers are proved explicitly;
   no measurable-function or finite-range oracle is assumed. *)

Definition QuantDen (m : nat) : R := INR (S m).
Definition QuantBound (m : nat) : Z := Z.of_nat ((S m) * (S m)).
Definition ZClip (lo hi z : Z) : Z := Z.max lo (Z.min z hi).
Definition QuantIndex (m : nat) (r : R) : Z :=
  ZClip (- QuantBound m) (QuantBound m) (Int_part (QuantDen m * r)).
Definition Quantize (m : nat) (r : R) : R :=
  IZR (QuantIndex m r) / QuantDen m.

Lemma QuantDen_positive : forall m, 0 < QuantDen m.
Proof. intro m; unfold QuantDen; apply lt_0_INR; lia. Qed.

Lemma QuantDen_at_least_one : forall m, 1 <= QuantDen m.
Proof. intro m; unfold QuantDen; change (INR 1 <= INR (S m)); apply le_INR; lia. Qed.

Lemma QuantDen_eventually_above : forall A : R,
  exists N : nat, forall m : nat, (N <= m)%nat -> A < QuantDen m.
Proof.
  intro A; destruct (INR_unbounded A) as [N HN].
  exists N; intros m Hm; unfold QuantDen.
  assert (Hle : INR N <= INR (S m)) by (apply le_INR; lia).
  lra.
Qed.

Theorem QUANTIZE_MESH_TENDS_ZERO : forall eps : R, 0 < eps ->
  exists N : nat, forall m : nat, (N <= m)%nat -> 1 / QuantDen m < eps.
Proof.
  intros eps Heps.
  destruct (QuantDen_eventually_above (1 / eps)) as [N HN].
  exists N; intros m Hm; specialize (HN m Hm).
  pose proof (QuantDen_positive m) as Hd.
  assert (He : (1 / eps) * eps = 1) by (field; lra).
  assert (Hd1 : (1 / QuantDen m) * QuantDen m = 1) by (field; lra).
  nra.
Qed.

Lemma QuantBound_positive : forall m, (0 < QuantBound m)%Z.
Proof. intro m; unfold QuantBound; lia. Qed.

Lemma QuantBound_real : forall m,
  IZR (QuantBound m) = QuantDen m * QuantDen m.
Proof.
  intro m; unfold QuantBound, QuantDen; rewrite <- INR_IZR_INZ, mult_INR; reflexivity.
Qed.

Lemma quant_floor_bounds : forall r,
  IZR (Int_part r) <= r < IZR (Int_part r) + 1.
Proof. intro r; pose proof (base_Int_part r); lra. Qed.

Lemma quant_floor_equal : forall r k,
  Int_part r = k <-> IZR k <= r < IZR k + 1.
Proof.
  intros r k; split.
  - intro H; rewrite <- H; apply quant_floor_bounds.
  - intros [Hlo Hhi]; symmetry; apply Int_part_spec; split; lra.
Qed.

Lemma quant_floor_le : forall r k,
  (Int_part r <= k)%Z <-> r < IZR k + 1.
Proof.
  intros r k; split.
  - intro H; pose proof (IZR_le _ _ H); pose proof (quant_floor_bounds r); lra.
  - intro H; assert (Hlt : (Int_part r < k + 1)%Z).
    { apply lt_IZR; rewrite plus_IZR; simpl.
      pose proof (quant_floor_bounds r); lra. }
    lia.
Qed.

Lemma quant_floor_ge : forall r k,
  (k <= Int_part r)%Z <-> IZR k <= r.
Proof.
  intros r k; split.
  - intro H; pose proof (IZR_le _ _ H); pose proof (quant_floor_bounds r); lra.
  - intro H; destruct (Z_le_dec k (Int_part r)) as [Hle|Hnot]; [exact Hle|].
    assert (Hstep : (Int_part r + 1 <= k)%Z) by lia.
    pose proof (IZR_le _ _ Hstep) as Hr; rewrite plus_IZR in Hr; simpl in Hr.
    pose proof (quant_floor_bounds r); lra.
Qed.

Lemma ZClip_bounds : forall lo hi z,
  (lo <= hi)%Z -> (lo <= ZClip lo hi z <= hi)%Z.
Proof.
  intros lo hi z H; unfold ZClip.
  destruct (Z.min_spec z hi) as [[H1 E1]|[H1 E1]];
  destruct (Z.max_spec lo (Z.min z hi)) as [[H2 E2]|[H2 E2]]; lia.
Qed.

Lemma ZClip_inside : forall lo hi z,
  (lo <= z <= hi)%Z -> ZClip lo hi z = z.
Proof.
  intros lo hi z [Hlo Hhi]; unfold ZClip.
  rewrite Z.min_l by exact Hhi; apply Z.max_r; exact Hlo.
Qed.

Lemma ZClip_fiber : forall lo hi z k,
  (lo < hi)%Z ->
  (ZClip lo hi z = k <->
   (k = lo /\ (z <= lo)%Z) \/
   (k = hi /\ (hi <= z)%Z) \/
   ((lo < k < hi)%Z /\ z = k)).
Proof.
  intros lo hi z k H; unfold ZClip.
  destruct (Z.min_spec z hi) as [[H1 E1]|[H1 E1]];
  destruct (Z.max_spec lo (Z.min z hi)) as [[H2 E2]|[H2 E2]]; lia.
Qed.

Theorem QUANTIZE_INDEX_RANGE : forall m r,
  (- QuantBound m <= QuantIndex m r <= QuantBound m)%Z.
Proof.
  intros m r; unfold QuantIndex; apply ZClip_bounds.
  pose proof (QuantBound_positive m); lia.
Qed.

Theorem QUANTIZE_RANGE : forall m r,
  exists k : Z, (- QuantBound m <= k <= QuantBound m)%Z /\
    Quantize m r = IZR k / QuantDen m.
Proof.
  intros m r; exists (QuantIndex m r); split.
  - apply QUANTIZE_INDEX_RANGE.
  - reflexivity.
Qed.

Definition QuantValues (m : nat) : list R :=
  map (fun j : nat => IZR (- QuantBound m + Z.of_nat j) / QuantDen m)
    (seq 0 (Z.to_nat (2 * QuantBound m + 1))).

Theorem QUANTIZE_IN_VALUES : forall m r, In (Quantize m r) (QuantValues m).
Proof.
  intros m r.
  pose proof (QUANTIZE_INDEX_RANGE m r) as Hrange.
  pose proof (QuantBound_positive m) as Hbound.
  unfold QuantValues; apply in_map_iff.
  exists (Z.to_nat (QuantIndex m r + QuantBound m)); split.
  - rewrite Z2Nat.id by lia.
    replace (- QuantBound m + (QuantIndex m r + QuantBound m))%Z
      with (QuantIndex m r) by lia.
    reflexivity.
  - apply in_seq; split; [lia|]; simpl.
    apply (proj1 (Z2Nat.inj_lt (QuantIndex m r + QuantBound m)
      (2 * QuantBound m + 1) ltac:(lia) ltac:(lia))); lia.
Qed.

Theorem QUANTIZE_FINITE_RANGE : forall m,
  exists values : list R, forall r, In (Quantize m r) values.
Proof. intro m; exists (QuantValues m); apply QUANTIZE_IN_VALUES. Qed.

Lemma QuantIndex_unclipped : forall m r,
  Rabs r <= QuantDen m ->
  QuantIndex m r = Int_part (QuantDen m * r).
Proof.
  intros m r Hbound.
  pose proof (QuantDen_positive m) as Hd.
  pose proof (Rle_abs r) as Habs.
  pose proof (Rle_abs (-r)) as Habsneg; rewrite Rabs_Ropp in Habsneg.
  unfold QuantIndex; apply ZClip_inside; split.
  - apply quant_floor_ge; rewrite opp_IZR, QuantBound_real; nra.
  - apply quant_floor_le; rewrite QuantBound_real; nra.
Qed.

Theorem QUANTIZE_ERROR : forall m r,
  Rabs r <= QuantDen m ->
  Rabs (Quantize m r - r) <= 1 / QuantDen m.
Proof.
  intros m r Hbound.
  pose proof (QuantDen_positive m) as Hd.
  pose proof (quant_floor_bounds (QuantDen m * r)) as Hfloor.
  assert (Hscale : Quantize m r * QuantDen m = IZR (Int_part (QuantDen m * r))).
  { unfold Quantize; rewrite QuantIndex_unclipped by exact Hbound; field; lra. }
  assert (Hinv : (1 / QuantDen m) * QuantDen m = 1) by (field; lra).
  assert (Hinvpos : 0 < 1 / QuantDen m).
  { apply Rdiv_lt_0_compat; [lra|exact Hd]. }
  apply Rabs_le; split; nra.
Qed.

Theorem QUANTIZE_SQUARE_ERROR : forall m r,
  Rabs r <= QuantDen m ->
  (Quantize m r - r) * (Quantize m r - r) <=
    (1 / QuantDen m) * (1 / QuantDen m).
Proof.
  intros m r Hbound.
  pose proof (QUANTIZE_ERROR m r Hbound) as Herror.
  pose proof (Rle_abs (Quantize m r - r)) as Hup.
  pose proof (Rle_abs (- (Quantize m r - r))) as Hlo.
  rewrite Rabs_Ropp in Hlo.
  pose proof (Rabs_pos (Quantize m r - r)); nra.
Qed.

Lemma quant_scaled_lt : forall d r k,
  0 < d -> (d * r < IZR k <-> r < IZR k / d).
Proof.
  intros d r k Hd.
  assert (Hcancel : IZR k / d * d = IZR k) by (field; lra).
  split; intro H; nra.
Qed.

Lemma quant_scaled_le : forall d r k,
  0 < d -> (IZR k <= d * r <-> IZR k / d <= r).
Proof.
  intros d r k Hd.
  assert (Hcancel : IZR k / d * d = IZR k) by (field; lra).
  split; intro H; nra.
Qed.

(* Outside the bounded integer range the fiber is empty.  The two clipping
   endpoints give half-lines; every interior value has a half-open interval. *)
Definition QuantFiber (m : nat) (k : Z) (r : R) : Prop :=
  (k = (- QuantBound m)%Z /\ r < IZR (- QuantBound m + 1) / QuantDen m) \/
  (k = QuantBound m /\ IZR (QuantBound m) / QuantDen m <= r) \/
  ((- QuantBound m < k < QuantBound m)%Z /\
    IZR k / QuantDen m <= r < IZR (k + 1) / QuantDen m).

Theorem QUANTIZE_INDEX_FIBER : forall m k r,
  QuantIndex m r = k <-> QuantFiber m k r.
Proof.
  intros m k r; unfold QuantIndex, QuantFiber.
  rewrite ZClip_fiber by (pose proof (QuantBound_positive m); lia).
  assert (Hlo : (Int_part (QuantDen m * r) <= - QuantBound m)%Z <->
    r < IZR (- QuantBound m + 1) / QuantDen m).
  { rewrite quant_floor_le.
    replace (IZR (- QuantBound m) + 1) with (IZR (- QuantBound m + 1))
      by (rewrite plus_IZR; simpl; reflexivity).
    apply quant_scaled_lt; apply QuantDen_positive. }
  assert (Hhi : (QuantBound m <= Int_part (QuantDen m * r))%Z <->
    IZR (QuantBound m) / QuantDen m <= r).
  { rewrite quant_floor_ge; apply quant_scaled_le; apply QuantDen_positive. }
  assert (Hmid : Int_part (QuantDen m * r) = k <->
    IZR k / QuantDen m <= r < IZR (k + 1) / QuantDen m).
  { rewrite quant_floor_equal.
    replace (IZR k + 1) with (IZR (k + 1))
      by (rewrite plus_IZR; simpl; reflexivity).
    rewrite (quant_scaled_le (QuantDen m) r k (QuantDen_positive m)),
      (quant_scaled_lt (QuantDen m) r (k + 1) (QuantDen_positive m)).
    reflexivity. }
  rewrite Hlo, Hhi, Hmid; reflexivity.
Qed.

Theorem QUANTIZE_VALUE_FIBER : forall m k r,
  Quantize m r = IZR k / QuantDen m <-> QuantFiber m k r.
Proof.
  intros m k r; rewrite <- QUANTIZE_INDEX_FIBER; unfold Quantize.
  split; [|intro H; rewrite H; reflexivity].
  intro H; apply eq_IZR.
  pose proof (QuantDen_positive m) as Hd.
  assert (Hq : IZR (QuantIndex m r) / QuantDen m * QuantDen m = IZR (QuantIndex m r))
    by (field; lra).
  assert (Hk : IZR k / QuantDen m * QuantDen m = IZR k) by (field; lra).
  rewrite H in Hq; lra.
Qed.

Print Assumptions QUANTIZE_RANGE.
Print Assumptions QUANTIZE_FINITE_RANGE.
Print Assumptions QUANTIZE_ERROR.
Print Assumptions QUANTIZE_SQUARE_ERROR.
Print Assumptions QUANTIZE_VALUE_FIBER.
