From Stdlib Require Import Reals Lra Psatz Lia Field Classical.
Require Import BKQR_CountableRange.

(* Concrete q-profile construction over the standard real numbers.
   The geometric-small and monotone-supremum proof patterns are adapted
   from NUL09/NUL10 in the supplied v0.5.10 real-uniform-limits anchor.
   No continuum Fourier or Leray--Hopf interpretation is asserted here. *)
Module BKQR_SCALAR_PROFILE.
Open Scope R_scope.

Fixpoint prefix (f : nat -> R) (n : nat) : R :=
  match n with O => 0 | S k => prefix f k + f k end.

Definition SeqLimit (f : nat -> R) (l : R) : Prop :=
  forall eps, 0 < eps -> exists N, forall n,
    (N <= n)%nat -> Rabs (f n-l) < eps.

Lemma prefix_nonnegative : forall f,
  (forall k, 0 <= f k) -> forall n, 0 <= prefix f n.
Proof.
  intros f Hf n; induction n as [|n IH]; simpl.
  - lra.
  - pose proof (Hf n); lra.
Qed.

Lemma prefix_monotone : forall f,
  (forall k, 0 <= f k) -> forall n m,
  (n <= m)%nat -> prefix f n <= prefix f m.
Proof.
  intros f Hf n m Hnm; induction Hnm as [|m Hnm IH].
  - apply Rle_refl.
  - simpl; pose proof (Hf m); lra.
Qed.

Lemma prefix_ext : forall f g n,
  (forall k, f k=g k) -> prefix f n=prefix g n.
Proof.
  intros f g n H; induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH,H; reflexivity.
Qed.

Lemma prefix_divide : forall f z n,
  prefix (fun k => f k/z) n=prefix f n/z.
Proof.
  intros f z n; induction n as [|n IH]; simpl.
  - unfold Rdiv; ring.
  - rewrite IH; unfold Rdiv; ring.
Qed.

Lemma divide_times_denominator : forall a z,
  z <> 0 -> (a/z)*z=a.
Proof.
  intros a z Hz; unfold Rdiv.
  rewrite Rmult_assoc, (Rinv_l z Hz), Rmult_1_r; reflexivity.
Qed.

Lemma geometric_small : forall q C eps,
  0 < q < 1 -> 0 <= C -> 0 < eps ->
  exists K, forall k, (K <= k)%nat -> C*q^k < eps.
Proof.
  intros q C eps Hq HC He.
  assert (Habs : Rabs q < 1) by (rewrite Rabs_right; lra).
  assert (Hsmall : 0 < eps/(C+1)).
  { unfold Rdiv; apply Rmult_lt_0_compat; [exact He|].
    apply Rinv_0_lt_compat; lra. }
  destruct (pow_lt_1_zero q Habs (eps/(C+1)) Hsmall) as [K HK].
  exists K; intros k Hk; specialize (HK k Hk).
  rewrite Rabs_right in HK by (apply Rle_ge, pow_le; lra).
  assert (Hcancel : (C+1)*(eps/(C+1))=eps) by (field; lra).
  pose proof (Rmult_lt_compat_l (C+1) _ _ (ltac:(lra)) HK) as Hscaled.
  rewrite Hcancel in Hscaled.
  pose proof (pow_le q k (ltac:(lra))); nra.
Qed.

Lemma monotone_sup_limit : forall f L,
  (forall n m, (n <= m)%nat -> f n <= f m) ->
  is_lub (fun v => exists n, v=f n) L -> SeqLimit f L.
Proof.
  intros f L Hmono [Hupper Hleast] eps He.
  assert (Hex : exists N, L-eps < f N).
  { apply NNPP; intro Hnone.
    assert (Hu : is_upper_bound (fun v => exists n, v=f n) (L-eps)).
    { intros v [n ->].
      destruct (Rle_dec (f n) (L-eps)); [assumption|].
      exfalso; apply Hnone; exists n; lra. }
    specialize (Hleast _ Hu); lra. }
  destruct Hex as [N HN]; exists N; intros n Hn.
  pose proof (Hmono N n Hn).
  assert (Hb : f n <= L) by (apply Hupper; exists n; reflexivity).
  rewrite Rabs_left1; lra.
Qed.

Lemma q_power_bounds : forall q,
  0 < q < 1 -> forall k, 0 < q^k /\ q^k <= 1.
Proof.
  intros q Hq k; induction k as [|k [Hpos Hupper]]; simpl.
  - split; lra.
  - split.
    + apply Rmult_lt_0_compat; lra.
    + nra.
Qed.

Lemma q_denominator_positive : forall q k,
  0 < q < 1 -> 0 < 1-q^(S k).
Proof.
  intros q k Hq; pose proof (q_power_bounds q Hq k); simpl; nra.
Qed.

Lemma q_denominator_lower : forall q k,
  0 < q < 1 -> 1-q <= 1-q^(S k).
Proof.
  intros q k Hq; pose proof (q_power_bounds q Hq k); simpl; nra.
Qed.

Fixpoint coefficient (q x : R) (k : nat) : R :=
  match k with
  | O => 1
  | S j => x*q^j*coefficient q x j/(1-q^(S j))
  end.

Theorem SCALAR_COEFFICIENT_NONNEGATIVE : forall q x,
  0 < q < 1 -> 0 <= x -> forall k, 0 <= coefficient q x k.
Proof.
  intros q x Hq Hx k; induction k as [|k IH].
  - simpl; lra.
  - change (0 <= x*q^k*coefficient q x k/(1-q^(S k))).
    unfold Rdiv; apply Rmult_le_pos.
    + apply Rmult_le_pos; [|exact IH].
      apply Rmult_le_pos; [exact Hx|apply pow_le; lra].
    + apply Rlt_le, Rinv_0_lt_compat, q_denominator_positive; exact Hq.
Qed.

Theorem SCALAR_EVENTUAL_HALF_RATIO : forall q x,
  0 < q < 1 -> 0 <= x ->
  exists K, forall k, (K <= k)%nat ->
    coefficient q x (S k) <= coefficient q x k/2.
Proof.
  intros q x Hq Hx.
  assert (HC : 0 <= x/(1-q)).
  { unfold Rdiv; apply Rmult_le_pos; [exact Hx|].
    apply Rlt_le, Rinv_0_lt_compat; lra. }
  destruct (geometric_small q (x/(1-q)) (1/2) Hq HC (ltac:(lra)))
    as [K HK].
  exists K; intros k Hk; specialize (HK k Hk).
  pose proof (q_denominator_positive q k Hq) as HD.
  pose proof (q_denominator_lower q k Hq) as HL.
  pose proof (SCALAR_COEFFICIENT_NONNEGATIVE q x Hq Hx k) as Ha.
  assert (Hcancel : (x/(1-q)*q^k)*(1-q)=x*q^k) by (field; lra).
  pose proof (Rmult_lt_compat_r (1-q) _ _ (ltac:(lra)) HK) as Hmul.
  rewrite Hcancel in Hmul.
  assert (Hratio : x*q^k <= (1-q^(S k))/2) by lra.
  change (x*q^k*coefficient q x k/(1-q^(S k)) <= coefficient q x k/2).
  apply (Rmult_le_reg_r (1-q^(S k))); [exact HD|].
  replace ((x*q^k*coefficient q x k/(1-q^(S k)))*(1-q^(S k)))
    with (x*q^k*coefficient q x k) by (field; lra).
  pose proof (Rmult_le_compat_r (coefficient q x k) _ _ Ha Hratio); nra.
Qed.

Lemma half_ratio_prefix_bound : forall f K,
  (forall k, 0 <= f k) ->
  (forall k, (K <= k)%nat -> f (S k) <= f k/2) ->
  forall n, prefix f n <= prefix f K+2*f K.
Proof.
  intros f K Hnon Hhalf n.
  destruct (Nat.le_ge_cases n K) as [Hnk|Hkn].
  - pose proof (prefix_monotone f Hnon n K Hnk).
    pose proof (Hnon K); lra.
  - assert (Htail : prefix f n+2*f n <= prefix f K+2*f K).
    { induction Hkn as [|n Hkn IH].
      - apply Rle_refl.
      - simpl; pose proof (Hhalf n Hkn); lra. }
    pose proof (Hnon n); lra.
Qed.

Definition PrefixValues (q x v : R) : Prop :=
  exists n, v=prefix (coefficient q x) n.

Theorem SCALAR_COEFFICIENT_SUMMABLE : forall q x,
  0 < q < 1 -> 0 <= x -> bound (PrefixValues q x).
Proof.
  intros q x Hq Hx.
  destruct (SCALAR_EVENTUAL_HALF_RATIO q x Hq Hx) as [K HK].
  exists (prefix (coefficient q x) K+2*coefficient q x K).
  intros v [n ->]; apply (half_ratio_prefix_bound (coefficient q x) K).
  - exact (SCALAR_COEFFICIENT_NONNEGATIVE q x Hq Hx).
  - exact HK.
Qed.

Definition construct_normalizer (q x : R) (Hq : 0 < q < 1) (Hx : 0 <= x) :
  { Z : R | is_lub (PrefixValues q x) Z /\ 1 <= Z /\
    SeqLimit (fun n => prefix (coefficient q x) n) Z }.
Proof.
  assert (Hb : bound (PrefixValues q x)) by
    (apply SCALAR_COEFFICIENT_SUMMABLE; assumption).
  assert (He : exists v, PrefixValues q x v).
  { exists 0; exists O; reflexivity. }
  destruct (completeness _ Hb He) as [Z HZ].
  exists Z; split; [exact HZ|]; split.
  - assert (Hone : prefix (coefficient q x) 1 <= Z).
    { apply (proj1 HZ); exists 1%nat; reflexivity. }
    change (0+1 <= Z) in Hone; lra.
  - apply monotone_sup_limit.
    + apply prefix_monotone; exact (SCALAR_COEFFICIENT_NONNEGATIVE q x Hq Hx).
    + exact HZ.
Defined.

Definition normalizer q x Hq Hx := proj1_sig (construct_normalizer q x Hq Hx).

Theorem SCALAR_NORMALIZER_SPEC : forall q x Hq Hx,
  is_lub (PrefixValues q x) (normalizer q x Hq Hx) /\
  1 <= normalizer q x Hq Hx /\
  SeqLimit (fun n => prefix (coefficient q x) n) (normalizer q x Hq Hx).
Proof. intros; exact (proj2_sig (construct_normalizer q x Hq Hx)). Qed.

Theorem SCALAR_NORMALIZER_GE_ONE : forall q x Hq Hx,
  1 <= normalizer q x Hq Hx.
Proof. intros; exact (proj1 (proj2 (SCALAR_NORMALIZER_SPEC q x Hq Hx))). Qed.

Definition probability q x Hq Hx k :=
  coefficient q x k/normalizer q x Hq Hx.
Definition psi q x Hq Hx k := sqrt (probability q x Hq Hx k).

Theorem SCALAR_PROBABILITY_NONNEGATIVE : forall q x Hq Hx k,
  0 <= probability q x Hq Hx k.
Proof.
  intros; unfold probability,Rdiv; apply Rmult_le_pos.
  - exact (SCALAR_COEFFICIENT_NONNEGATIVE q x Hq Hx k).
  - apply Rlt_le, Rinv_0_lt_compat.
    pose proof (SCALAR_NORMALIZER_GE_ONE q x Hq Hx); lra.
Qed.

Lemma probability_prefix : forall q x Hq Hx n,
  prefix (probability q x Hq Hx) n=
  prefix (coefficient q x) n/normalizer q x Hq Hx.
Proof. intros; unfold probability; apply prefix_divide. Qed.

Theorem SCALAR_PROBABILITY_PARTITION_LUB : forall q x Hq Hx,
  is_lub (fun v => exists n, v=prefix (probability q x Hq Hx) n) 1.
Proof.
  intros q x Hq Hx.
  destruct (SCALAR_NORMALIZER_SPEC q x Hq Hx) as [HZ [HZ1 Hlim]].
  assert (HZpos : 0 < normalizer q x Hq Hx) by lra.
  assert (HZneq : normalizer q x Hq Hx <> 0).
  { intro Hzero; rewrite Hzero in HZpos; lra. }
  split.
  - intros v [n ->]; rewrite probability_prefix.
    apply (Rmult_le_reg_r (normalizer q x Hq Hx)); [exact HZpos|].
    rewrite (divide_times_denominator (prefix (coefficient q x) n)
      (normalizer q x Hq Hx) HZneq).
    replace (1*normalizer q x Hq Hx) with (normalizer q x Hq Hx) by ring.
    apply (proj1 HZ); exists n; reflexivity.
  - intros B HB.
    assert (Hupper : is_upper_bound (PrefixValues q x) (B*normalizer q x Hq Hx)).
    { intros v [n ->].
      assert (Hp : prefix (probability q x Hq Hx) n <= B).
      { apply HB; exists n; reflexivity. }
      rewrite probability_prefix in Hp.
      pose proof (Rmult_le_compat_r (normalizer q x Hq Hx) _ _ (Rlt_le _ _ HZpos) Hp)
        as Hmul.
      rewrite (divide_times_denominator (prefix (coefficient q x) n)
        (normalizer q x Hq Hx) HZneq) in Hmul.
      exact Hmul. }
    pose proof ((proj2 HZ) _ Hupper) as Hleast.
    apply (Rmult_le_reg_r (normalizer q x Hq Hx)); [exact HZpos|]; nra.
Qed.

Theorem SCALAR_PROBABILITY_PARTITION : forall q x Hq Hx,
  SeqLimit (fun n => prefix (probability q x Hq Hx) n) 1.
Proof.
  intros; apply monotone_sup_limit.
  - apply prefix_monotone; apply SCALAR_PROBABILITY_NONNEGATIVE.
  - apply SCALAR_PROBABILITY_PARTITION_LUB.
Qed.

Theorem SCALAR_PSI_SQUARE : forall q x Hq Hx k,
  psi q x Hq Hx k*psi q x Hq Hx k=probability q x Hq Hx k.
Proof.
  intros; unfold psi; apply sqrt_def; apply SCALAR_PROBABILITY_NONNEGATIVE.
Qed.

Theorem SCALAR_PSI_NONNEGATIVE : forall q x Hq Hx k,
  0 <= psi q x Hq Hx k.
Proof. intros; unfold psi; apply sqrt_pos. Qed.

Theorem SCALAR_PSI_ZERO_POSITIVE : forall q x Hq Hx,
  0 < psi q x Hq Hx O.
Proof.
  intros q x Hq Hx.
  assert (Hp : 0 < probability q x Hq Hx O).
  { unfold probability; change (0 < 1/normalizer q x Hq Hx).
    unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat.
    pose proof (SCALAR_NORMALIZER_GE_ONE q x Hq Hx); lra. }
  unfold psi; apply sqrt_lt_R0; exact Hp.
Qed.

Theorem SCALAR_PSI_SQUARE_PARTITION : forall q x Hq Hx,
  SeqLimit (fun n => prefix (fun k => psi q x Hq Hx k*psi q x Hq Hx k) n) 1.
Proof.
  intros q x Hq Hx eps He.
  destruct (SCALAR_PROBABILITY_PARTITION q x Hq Hx eps He) as [N HN].
  exists N; intros n Hn.
  assert (Hp : prefix (fun k => psi q x Hq Hx k*psi q x Hq Hx k) n=
      prefix (probability q x Hq Hx) n).
  { apply prefix_ext; intro k; apply SCALAR_PSI_SQUARE. }
  rewrite Hp; apply HN; exact Hn.
Qed.

Definition clock (q : R) (k : nat) := /q^k-q.

Theorem SCALAR_CLOCK_POSITIVE : forall q,
  0 < q < 1 -> forall k, 0 < clock q k.
Proof.
  intros q Hq k; pose proof (q_power_bounds q Hq k) as [Hp Hu].
  pose proof (q_denominator_positive q k Hq) as HD.
  unfold clock; apply (Rmult_lt_reg_r (q^k)); [exact Hp|].
  replace (0*q^k) with 0 by ring.
  replace ((/q^k-q)*q^k) with (1-q^(S k)) by (simpl; field; lra).
  exact HD.
Qed.

Theorem SCALAR_COEFFICIENT_RAISING : forall q x,
  0 < q < 1 -> forall k,
  x*coefficient q x k=clock q k*coefficient q x (S k).
Proof.
  intros q x Hq k.
  pose proof (q_power_bounds q Hq k) as [Hp Hu].
  pose proof (q_denominator_positive q k Hq) as HD.
  unfold clock; change (x*coefficient q x k=
    (/q^k-q)*(x*q^k*coefficient q x k/(1-q^(S k)))).
  simpl in HD; simpl; field; lra.
Qed.

Theorem SCALAR_PROBABILITY_RAISING : forall q x Hq Hx k,
  x*probability q x Hq Hx k=
  clock q k*probability q x Hq Hx (S k).
Proof.
  intros; unfold probability,Rdiv.
  pose proof (SCALAR_COEFFICIENT_RAISING q x Hq k) as H.
  rewrite <- Rmult_assoc, <- Rmult_assoc, <- H; reflexivity.
Qed.

Theorem SCALAR_PSI_RAISING : forall q x Hq Hx k,
  sqrt x*psi q x Hq Hx k=
  sqrt (clock q k)*psi q x Hq Hx (S k).
Proof.
  intros q x Hq Hx k.
  pose proof (SCALAR_CLOCK_POSITIVE q Hq k) as Hclock.
  pose proof (SCALAR_PSI_NONNEGATIVE q x Hq Hx k) as Hp.
  pose proof (SCALAR_PSI_NONNEGATIVE q x Hq Hx (S k)) as Hp'.
  pose proof (sqrt_pos x) as Hsx.
  pose proof (sqrt_pos (clock q k)) as Hsc.
  assert (Hleft : (sqrt x*psi q x Hq Hx k)*(sqrt x*psi q x Hq Hx k)=
      x*probability q x Hq Hx k).
  { replace ((sqrt x*psi q x Hq Hx k)*(sqrt x*psi q x Hq Hx k))
      with ((sqrt x*sqrt x)*(psi q x Hq Hx k*psi q x Hq Hx k)) by ring.
    rewrite (sqrt_def x Hx), SCALAR_PSI_SQUARE; reflexivity. }
  assert (Hright :
      (sqrt (clock q k)*psi q x Hq Hx (S k))*(sqrt (clock q k)*psi q x Hq Hx (S k))=
      clock q k*probability q x Hq Hx (S k)).
  { replace ((sqrt (clock q k)*psi q x Hq Hx (S k))*
      (sqrt (clock q k)*psi q x Hq Hx (S k)))
      with ((sqrt (clock q k)*sqrt (clock q k))*
      (psi q x Hq Hx (S k)*psi q x Hq Hx (S k))) by ring.
    rewrite (sqrt_def (clock q k) (Rlt_le _ _ Hclock)), SCALAR_PSI_SQUARE; reflexivity. }
  pose proof (SCALAR_PROBABILITY_RAISING q x Hq Hx k).
  assert (0 <= sqrt x*psi q x Hq Hx k) by (apply Rmult_le_pos; assumption).
  assert (0 <= sqrt (clock q k)*psi q x Hq Hx (S k))
    by (apply Rmult_le_pos; assumption).
  nra.
Qed.

Theorem SCALAR_PSI_RAISING_NONNEGATIVE_LAMBDA :
  forall q lambda Hq Hx k,
  0 <= lambda ->
  lambda*psi q (lambda*lambda) Hq Hx k=
  sqrt (clock q k)*psi q (lambda*lambda) Hq Hx (S k).
Proof.
  intros q lambda Hq Hx k Hlambda.
  pose proof (SCALAR_PSI_RAISING q (lambda*lambda) Hq Hx k) as H.
  rewrite (sqrt_square lambda Hlambda) in H; exact H.
Qed.

Lemma prefix_is_gp_sum : forall f n,
  prefix f n=GP_COUNTABLE_RANGE.gp_sum n f.
Proof.
  intros f n; induction n as [|n IH]; simpl; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

Theorem SCALAR_PSI_COUNTABLE_PARTITION : forall q (Hq : 0 < q < 1)
  (x : nat -> R) (Hx : forall i, 0 <= x i),
  GP_COUNTABLE_RANGE.ScalarPartition
    (fun k i => psi q (x i) Hq (Hx i) k).
Proof.
  intros q Hq x Hx i eps He.
  destruct (SCALAR_PSI_SQUARE_PARTITION q (x i) Hq (Hx i) eps He)
    as [N HN].
  exists N; intros n Hn.
  rewrite <- prefix_is_gp_sum; apply HN; exact Hn.
Qed.

End BKQR_SCALAR_PROFILE.
