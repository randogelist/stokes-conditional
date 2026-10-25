(* Finite estimates for genuinely countable signed kernels.  A Schur bound
   is an explicit coefficient hypothesis, not a physical NSE realization. *)
From Stdlib Require Import Reals Lra Psatz Lia Field Arith.
Require Import BKQR_CountableRange.

Module BKQR_BILINEAR_KERNEL.
Import GP_COUNTABLE_RANGE.
Open Scope R_scope.

Definition SchurBound (K : nat -> nat -> R) (C : R) : Prop :=
  0 <= C /\
  (forall j M, gp_sum M (fun k => Rabs (K j k)) <= C) /\
  (forall k N, gp_sum N (fun j => Rabs (K j k)) <= C).

Definition bilinear_rectangle (K : nat -> nat -> R) (N M : nat)
  (x y : nat -> R) : R :=
  gp_sum N (fun j => gp_sum M (fun k => K j k * x j * y k)).
Definition bilinear_form K N x y := bilinear_rectangle K N N x y.
Definition quadratic_form K N x := bilinear_form K N x x.

Lemma sum_plus : forall N f g,
  gp_sum N (fun i => f i + g i) = gp_sum N f + gp_sum N g.
Proof. induction N; intros; simpl; [ring|rewrite IHN; ring]. Qed.
Lemma sum_zero : forall N, gp_sum N (fun _ => 0) = 0.
Proof. induction N; simpl; [reflexivity|rewrite IHN; ring]. Qed.
Lemma sum_swap : forall N M f,
  gp_sum N (fun j => gp_sum M (fun k => f j k)) =
  gp_sum M (fun k => gp_sum N (fun j => f j k)).
Proof.
  induction N; intros M f; simpl.
  - symmetry. apply sum_zero.
  - rewrite IHN, <- sum_plus. apply gp_sum_ext. intros; reflexivity.
Qed.
Lemma sum_abs : forall N f,
  Rabs (gp_sum N f) <= gp_sum N (fun i => Rabs (f i)).
Proof.
  induction N; intros f; simpl; [rewrite Rabs_R0; lra|].
  pose proof (Rabs_triang (gp_sum N f) (f N)). specialize (IHN f). lra.
Qed.
Lemma prefix_nonneg : forall x N, 0 <= physical_prefix x N.
Proof. intros. apply gp_sum_nonneg. intro; nra. Qed.
Lemma prefix_monotone : forall x N M, (N <= M)%nat ->
  physical_prefix x N <= physical_prefix x M.
Proof. intros. apply gp_sum_prefix_le; [intro; nra|assumption]. Qed.

Lemma abs_square : forall x, Rabs x * Rabs x = x*x.
Proof. intro x. rewrite <- Rabs_mult. apply Rabs_pos_eq. nra. Qed.
Lemma weighted_young : forall x y rho, 0 < rho ->
  2 * Rabs x * Rabs y <= rho * (x*x) + /rho * (y*y).
Proof.
  intros x y rho Hrho.
  assert (Hi : 0 < /rho) by (apply Rinv_0_lt_compat; exact Hrho).
  assert (Hcancel : rho * /rho = 1) by (field; lra).
  pose proof (Rle_0_sqr (rho * Rabs x - Rabs y)) as Hsq.
  unfold Rsqr in Hsq.
  pose proof (abs_square x) as Hx. pose proof (abs_square y) as Hy.
  assert (H0 : 0 <= /rho * ((rho * Rabs x - Rabs y) *
    (rho * Rabs x - Rabs y))) by (apply Rmult_le_pos; lra).
  nra.
Qed.

Theorem bilinear_rectangle_young : forall K C,
  SchurBound K C -> forall N M x y rho, 0 < rho ->
  Rabs (bilinear_rectangle K N M x y) <=
  (C/2) * (rho * physical_prefix x N + /rho * physical_prefix y M).
Proof.
  intros K C [HC [Hrow Hcol]] N M x y rho Hrho.
  assert (Hi : 0 < /rho) by (apply Rinv_0_lt_compat; exact Hrho).
  unfold bilinear_rectangle.
  eapply Rle_trans; [apply sum_abs|].
  eapply Rle_trans.
  { apply gp_sum_le. intros j Hj. apply sum_abs. }
  eapply Rle_trans with (r2 := gp_sum N (fun j => gp_sum M (fun k =>
    (rho/2)*(x j*x j)*Rabs(K j k) +
    (/rho/2)*(y k*y k)*Rabs(K j k)))).
  { apply gp_sum_le. intros j Hj. apply gp_sum_le. intros k Hk.
    rewrite !Rabs_mult. pose proof (weighted_young (x j) (y k) rho Hrho).
    pose proof (Rabs_pos (K j k)). nra. }
  set (f := fun j k => (rho/2)*(x j*x j)*Rabs(K j k)).
  set (g := fun j k => (/rho/2)*(y k*y k)*Rabs(K j k)).
  change (gp_sum N (fun j => gp_sum M (fun k => f j k + g j k)) <=
    (C/2) * (rho * physical_prefix x N + /rho * physical_prefix y M)).
  assert (Hsplit : gp_sum N (fun j => gp_sum M (fun k => f j k + g j k)) =
    gp_sum N (fun j => gp_sum M (f j)) +
    gp_sum N (fun j => gp_sum M (g j))).
  { rewrite <- sum_plus. apply gp_sum_ext. intros; apply sum_plus. }
  rewrite Hsplit.
  assert (HF : gp_sum N (fun j => gp_sum M (f j)) <=
    (rho/2)*C*physical_prefix x N).
  { unfold f, physical_prefix. rewrite <- gp_sum_scale. apply gp_sum_le.
    intros j Hj. rewrite gp_sum_scale. specialize (Hrow j M).
    assert (0 <= (rho/2)*(x j*x j)) by nra. nra. }
  assert (HG : gp_sum N (fun j => gp_sum M (g j)) <=
    (/rho/2)*C*physical_prefix y M).
  { rewrite sum_swap. unfold g, physical_prefix. rewrite <- gp_sum_scale.
    apply gp_sum_le. intros k Hk. rewrite gp_sum_scale.
    specialize (Hcol k N). assert (0 <= (/rho/2)*(y k*y k)) by nra. nra. }
  nra.
Qed.

Theorem bilinear_form_young : forall K C,
  SchurBound K C -> forall N x y rho, 0 < rho ->
  Rabs (bilinear_form K N x y) <=
  (C/2) * (rho * physical_prefix x N + /rho * physical_prefix y N).
Proof. intros. apply bilinear_rectangle_young; assumption. Qed.

Theorem quadratic_form_bound : forall K C,
  SchurBound K C -> forall N x,
  Rabs (quadratic_form K N x) <= C * physical_prefix x N.
Proof.
  intros K C HK N x. pose proof (bilinear_form_young K C HK N x x 1 Rlt_0_1).
  unfold quadratic_form. rewrite Rinv_1 in H. nra.
Qed.

Lemma bilinear_rectangle_ext : forall K N M x x' y y',
  (forall j, (j < N)%nat -> x j = x' j) ->
  (forall k, (k < M)%nat -> y k = y' k) ->
  bilinear_rectangle K N M x y = bilinear_rectangle K N M x' y'.
Proof.
  intros K N M x x' y y' Hx Hy. unfold bilinear_rectangle.
  apply gp_sum_ext. intros j Hj. apply gp_sum_ext. intros k Hk.
  rewrite Hx, Hy by assumption. reflexivity.
Qed.

Lemma bilinear_rectangle_plus_left : forall K N M x z y,
  bilinear_rectangle K N M (fun i => x i + z i) y =
  bilinear_rectangle K N M x y + bilinear_rectangle K N M z y.
Proof.
  intros. unfold bilinear_rectangle. rewrite <- sum_plus.
  apply gp_sum_ext. intros. rewrite <- sum_plus.
  apply gp_sum_ext. intros; ring.
Qed.
Lemma bilinear_rectangle_plus_right : forall K N M x y z,
  bilinear_rectangle K N M x (fun i => y i + z i) =
  bilinear_rectangle K N M x y + bilinear_rectangle K N M x z.
Proof.
  intros. unfold bilinear_rectangle. rewrite <- sum_plus.
  apply gp_sum_ext. intros. rewrite <- sum_plus.
  apply gp_sum_ext. intros; ring.
Qed.
Lemma bilinear_rectangle_scale_left : forall K N M c x y,
  bilinear_rectangle K N M (fun i => c*x i) y =
  c * bilinear_rectangle K N M x y.
Proof.
  intros. unfold bilinear_rectangle. rewrite <- gp_sum_scale.
  apply gp_sum_ext. intros. rewrite <- gp_sum_scale.
  apply gp_sum_ext. intros; ring.
Qed.
Lemma bilinear_rectangle_scale_right : forall K N M c x y,
  bilinear_rectangle K N M x (fun i => c*y i) =
  c * bilinear_rectangle K N M x y.
Proof.
  intros. unfold bilinear_rectangle. rewrite <- gp_sum_scale.
  apply gp_sum_ext. intros. rewrite <- gp_sum_scale.
  apply gp_sum_ext. intros; ring.
Qed.

Definition cutoff_vector (N : nat) (x : nat -> R) (i : nat) : R :=
  if lt_dec i N then x i else 0.
Definition tail_vector N x i := x i - cutoff_vector N x i.

Lemma sum_cutoff : forall N M f, (N <= M)%nat ->
  gp_sum M (fun i => if lt_dec i N then f i else 0) = gp_sum N f.
Proof.
  intros N M f HNM. induction HNM.
  - apply gp_sum_ext. intros i Hi. destruct (lt_dec i N); [reflexivity|lia].
  - simpl. rewrite IHHNM. destruct (lt_dec m N); [lia|ring].
Qed.

Lemma cutoff_prefix : forall N M x, (N <= M)%nat ->
  physical_prefix (cutoff_vector N x) M = physical_prefix x N.
Proof.
  intros N M x HNM. unfold physical_prefix, cutoff_vector.
  rewrite <- (sum_cutoff N M (fun i => x i*x i) HNM).
  apply gp_sum_ext. intros i Hi. destruct (lt_dec i N); ring.
Qed.
Lemma tail_prefix : forall N M x, (N <= M)%nat ->
  physical_prefix (tail_vector N x) M =
  physical_prefix x M - physical_prefix x N.
Proof.
  intros N M x HNM. rewrite <- (cutoff_prefix N M x HNM).
  unfold physical_prefix.
  apply Rplus_eq_reg_r with (r := gp_sum M
    (fun i => cutoff_vector N x i * cutoff_vector N x i)).
  replace (gp_sum M (fun i => tail_vector N x i * tail_vector N x i) +
    gp_sum M (fun i => cutoff_vector N x i * cutoff_vector N x i)) with
    (gp_sum M (fun i => tail_vector N x i * tail_vector N x i +
      cutoff_vector N x i * cutoff_vector N x i)) by apply sum_plus.
  replace (gp_sum M (fun i => x i*x i) -
    gp_sum M (fun i => cutoff_vector N x i * cutoff_vector N x i) +
    gp_sum M (fun i => cutoff_vector N x i * cutoff_vector N x i)) with
    (gp_sum M (fun i => x i*x i)) by ring.
  apply gp_sum_ext. intros i Hi. unfold tail_vector, cutoff_vector.
  destruct (lt_dec i N); ring.
Qed.

Lemma bilinear_cutoff : forall K N M x y, (N <= M)%nat ->
  bilinear_form K M (cutoff_vector N x) (cutoff_vector N y) =
  bilinear_form K N x y.
Proof.
  intros K N M x y HNM. unfold bilinear_form, bilinear_rectangle.
  rewrite <- (sum_cutoff N M (fun j => gp_sum N
    (fun k => K j k*x j*y k)) HNM).
  apply gp_sum_ext. intros j Hj. unfold cutoff_vector.
  destruct (lt_dec j N) as [HjN|HjN].
  - rewrite <- (sum_cutoff N M (fun k => K j k*x j*y k) HNM).
    apply gp_sum_ext. intros k Hk. destruct (lt_dec k N); ring.
  - transitivity (gp_sum M (fun _ => 0)); [|apply sum_zero].
    apply gp_sum_ext. intros; ring.
Qed.

Lemma quadratic_cutoff_decomposition : forall K N M x, (N <= M)%nat ->
  quadratic_form K M x - quadratic_form K N x =
  bilinear_form K M (tail_vector N x) x +
  bilinear_form K M (cutoff_vector N x) (tail_vector N x).
Proof.
  intros K N M x HNM. unfold quadratic_form.
  rewrite <- (bilinear_cutoff K N M x x HNM).
  assert (Hx : bilinear_form K M x x =
    bilinear_form K M (fun i => cutoff_vector N x i + tail_vector N x i) x).
  { apply bilinear_rectangle_ext; intros; unfold tail_vector; ring. }
  rewrite Hx. unfold bilinear_form. rewrite bilinear_rectangle_plus_left.
  assert (Hy : bilinear_rectangle K M M (cutoff_vector N x) x =
    bilinear_rectangle K M M (cutoff_vector N x)
      (fun i => cutoff_vector N x i + tail_vector N x i)).
  { apply bilinear_rectangle_ext; intros; unfold tail_vector; ring. }
  rewrite Hy, bilinear_rectangle_plus_right. ring.
Qed.

Theorem quadratic_form_difference_bound : forall K C,
  SchurBound K C -> forall N M x E delta,
  (N <= M)%nat -> physical_prefix x M <= E -> 0 < delta ->
  Rabs (quadratic_form K M x - quadratic_form K N x) <=
  2*C*delta*E + (2*C/delta)*(physical_prefix x M - physical_prefix x N).
Proof.
  intros K C HK N M x E delta HNM HE Hd.
  pose proof (proj1 HK) as HC.
  assert (Hi : 0 < /delta) by (apply Rinv_0_lt_compat; exact Hd).
  pose proof (bilinear_form_young K C HK M (tail_vector N x) x (/delta) Hi) as H1.
  pose proof (bilinear_form_young K C HK M (cutoff_vector N x)
    (tail_vector N x) delta Hd) as H2.
  rewrite Rinv_inv in H1 by lra. rewrite tail_prefix in H1 by assumption.
  rewrite cutoff_prefix, tail_prefix in H2 by assumption.
  rewrite quadratic_cutoff_decomposition by assumption.
  eapply Rle_trans; [apply Rabs_triang|].
  pose proof (prefix_monotone x N M HNM) as Hmono.
  pose proof (prefix_nonneg x N) as HposN.
  pose proof (prefix_nonneg x M) as HposM.
  assert (HCE : C*delta*physical_prefix x M <= C*delta*E).
  { apply Rmult_le_compat_l; [nra|exact HE]. }
  assert (Hhead : C*delta*physical_prefix x N <= C*delta*physical_prefix x M).
  { apply Rmult_le_compat_l; [nra|exact Hmono]. }
  assert (Htail : 0 <= C*/delta*(physical_prefix x M-physical_prefix x N)).
  { apply Rmult_le_pos; [apply Rmult_le_pos; lra|lra]. }
  assert (HEpos : 0 <= C*delta*E).
  { apply Rmult_le_pos; [nra|lra]. }
  unfold Rdiv. nra.
Qed.

(* These kernels have countably many nonzero entries.  The estimate therefore
   supplies a nontrivial infinite instance, without a finite-support premise. *)
Definition injection_kernel (f : nat -> nat) (j k : nat) : R :=
  if Nat.eq_dec (f j) k then 1 else 0.
Definition diagonal_kernel := injection_kernel (fun j => j).

Lemma injection_spike_sum_bound : forall f : nat -> nat,
  (forall i j, f i = f j -> i = j) -> forall target N,
  gp_sum N (fun i => if Nat.eq_dec (f i) target then 1 else 0) <= 1.
Proof.
  intros f Hinj target N. induction N; simpl; [lra|].
  destruct (Nat.eq_dec (f N) target) as [Heq|Hneq]; [|lra].
  assert (Hzero : gp_sum N (fun i => if Nat.eq_dec (f i) target then 1 else 0) = 0).
  { transitivity (gp_sum N (fun _ => 0)); [|apply sum_zero].
    apply gp_sum_ext. intros i Hi. destruct (Nat.eq_dec (f i) target) as [Hei|Hni].
    - assert (i = N) by (apply Hinj; congruence). lia.
    - reflexivity. }
  rewrite Hzero. lra.
Qed.

Theorem injection_kernel_schur : forall f : nat -> nat,
  (forall i j, f i = f j -> i = j) -> SchurBound (injection_kernel f) 1.
Proof.
  intros f Hinj. split; [lra|]. split.
  - intros j M. eapply Rle_trans with (r2 :=
      gp_sum M (fun k => if Nat.eq_dec k (f j) then 1 else 0)).
    + apply gp_sum_le. intros k Hk. unfold injection_kernel.
      destruct (Nat.eq_dec (f j) k), (Nat.eq_dec k (f j));
        try congruence; rewrite Rabs_R0 || rewrite Rabs_R1; lra.
    + apply injection_spike_sum_bound with (f := fun k => k).
      intros; assumption.
  - intros k N. eapply Rle_trans with (r2 :=
      gp_sum N (fun j => if Nat.eq_dec (f j) k then 1 else 0)).
    + apply gp_sum_le. intros j Hj. unfold injection_kernel.
      destruct (Nat.eq_dec (f j) k); rewrite Rabs_R0 || rewrite Rabs_R1; lra.
    + apply injection_spike_sum_bound. exact Hinj.
Qed.

Theorem diagonal_kernel_schur : SchurBound diagonal_kernel 1.
Proof. apply injection_kernel_schur. intros; assumption. Qed.

Theorem successor_kernel_schur : SchurBound (injection_kernel S) 1.
Proof. apply injection_kernel_schur. intros; lia. Qed.

End BKQR_BILINEAR_KERNEL.
