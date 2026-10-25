(* Canonical BKQR high-pass envelope, derived from the constructed scalar
   profile. All cutoffs are arbitrary finite prefixes of the same infinite
   partition. No tail-envelope estimate is an input to the main theorem. *)
From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import BKQR_CountableRange BKQR_ScalarProfile BKQR_ShellCoordinates BKQR_ClassificationAudit.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.
Require Import awpi_nse_finite_cut_defect_bound_v0_51_0.

Module BKQR_M7_PROFILE_ENVELOPE.
Module B := GP_COUNTABLE_RANGE.
Module SP := BKQR_SCALAR_PROFILE.
Module C := BKQR_CLASSIFICATION.
Module F := NSE_KQ_FINITE_ALGEBRA.
Module M := NSE_GALERKIN_MODAL_CALCULUS.
Module E := NSE_FINITE_CUT_DEFECT_BOUND.
Module S := BKQR_SHELL_COORDINATES.
Open Scope R_scope.

Lemma finite_sum_is_gp_sum : forall n f, F.sum n f = B.gp_sum n f.
Proof. induction n; intros; simpl; [reflexivity|rewrite IHn; reflexivity]. Qed.
Lemma scalar_prefix_is_finite_sum : forall n f, SP.prefix f n = F.sum n f.
Proof. induction n; intros; simpl; [reflexivity|rewrite IHn; reflexivity]. Qed.

Lemma finite_sum_limit : forall J f l,
  (forall j, B.SeqLimit (fun n => f n j) (l j)) ->
  B.SeqLimit (fun n => F.sum J (f n)) (F.sum J l).
Proof.
  intros J f l H. rewrite finite_sum_is_gp_sum.
  eapply B.limit_ext.
  - intro n. symmetry. apply finite_sum_is_gp_sum.
  - apply B.limit_gp_sum. exact H.
Qed.

Lemma prefix_above_cut : forall pi N m, (S N <= m)%nat ->
  F.sum m (fun k => if Nat.ltb N k then pi k else 0) =
  F.sum m pi - F.sum (S N) pi.
Proof.
  intros pi N m Hm. induction Hm as [|m Hm IH].
  - replace (F.sum (S N) (fun k => if Nat.ltb N k then pi k else 0))
      with (F.sum (S N) (fun _ => 0)).
    + rewrite M.finite_sum_zero. ring.
    + apply F.sum_ext. intros k Hk. destruct (Nat.ltb_spec N k); [lia|reflexivity].
  - change (F.sum m (fun k => if Nat.ltb N k then pi k else 0)+
      (if Nat.ltb N m then pi m else 0) =
      F.sum m pi+pi m-F.sum (S N) pi). rewrite IH.
    destruct (Nat.ltb_spec N m); [ring|lia].
Qed.

Lemma clipped_weight_sum : forall w J k,
  F.sum J (fun N => if Nat.ltb N k then w N else 0) = F.sum (Nat.min J k) w.
Proof.
  intros w J. induction J as [|J IH]; intro k; [reflexivity|].
  cbn [F.sum]. rewrite IH.
  destruct (Nat.ltb_spec J k).
  - rewrite Nat.min_l by lia. rewrite Nat.min_l by lia. reflexivity.
  - rewrite Nat.min_r by lia. rewrite Nat.min_r by lia. ring.
Qed.

Definition clipped_level (r : nat -> R) J k := r (Nat.min J k) - 1.

Lemma clipped_level_is_weight_sum : forall r J k, r 0%nat = 1 ->
  clipped_level r J k =
  F.sum J (fun N => if Nat.ltb N k then r (S N)-r N else 0).
Proof.
  intros r J k H0. rewrite clipped_weight_sum, F.sum_telescoping, H0. reflexivity.
Qed.

Lemma finite_tail_interchange : forall pi r J m,
  r 0%nat = 1 -> (J <= m)%nat ->
  F.sum m (fun k => pi k * clipped_level r J k) =
  F.sum J (fun N => (r (S N)-r N) *
    (F.sum m pi-F.sum (S N) pi)).
Proof.
  intros pi r J m H0 Hm.
  transitivity (F.sum m (fun k => F.sum J (fun N =>
    pi k * (if Nat.ltb N k then r (S N)-r N else 0)))).
  - apply F.sum_ext. intros k Hk.
    rewrite (clipped_level_is_weight_sum r J k H0), F.sum_scale. reflexivity.
  - rewrite M.finite_sum_swap. apply F.sum_ext. intros N HN.
    transitivity ((r (S N)-r N) * F.sum m
      (fun k => if Nat.ltb N k then pi k else 0)).
    + rewrite <- F.sum_scale. apply F.sum_ext. intros k Hk.
      destruct (Nat.ltb_spec N k); ring.
    + rewrite prefix_above_cut by lia. reflexivity.
Qed.

Lemma clipped_level_square_bound : forall r,
  r 0%nat = 1 -> (forall n m, (n <= m)%nat -> r n <= r m) ->
  forall J k, 0 <= clipped_level r J k /\
    clipped_level r J k * clipped_level r J k <= r k*r k-1.
Proof.
  intros r H0 Hmono J k.
  pose proof (Hmono 0%nat (Nat.min J k) (Nat.le_0_l _)) as Hmin.
  pose proof (Hmono (Nat.min J k) k (Nat.le_min_r _ _)) as Hmk.
  rewrite H0 in Hmin. unfold clipped_level. split; [lra|].
  assert (0 <= (r k-r (Nat.min J k))*(r k+r (Nat.min J k)))
    by (apply Rmult_le_pos; lra). nra.
Qed.

Theorem BKME00_PARTITION_MOMENT_GIVES_TAIL_ENVELOPE : forall pi r L,
  (forall k, 0 <= pi k) ->
  (forall m, F.sum m pi <= 1) ->
  B.SeqLimit (fun m => F.sum m pi) 1 ->
  r 0%nat = 1 -> (forall n m, (n <= m)%nat -> r n <= r m) ->
  0 <= L ->
  (forall m, F.sum m (fun k => pi k*(r k*r k-1)) <= L) ->
  forall J, F.sum J (fun N => (r (S N)-r N)*(1-F.sum (S N) pi)) <= sqrt L.
Proof.
  intros pi r L Hpi HP Hlim H0 Hmono HL Hmoment J.
  assert (Hfinite : forall m,
    F.sum m (fun k => pi k*clipped_level r J k) <= sqrt L).
  { intro m.
    pose proof (F.NSKA20_WEIGHTED_CAUCHY m pi
      (fun k => clipped_level r J k*clipped_level r J k)
      (fun _ => 1) (clipped_level r J)
      (fun k _ => Hpi k) (fun k _ => Rle_0_sqr _)
      (fun k _ => Rle_0_1) (fun k _ => ltac:(nra))) as Hcs.
    cbn beta zeta in Hcs.
    assert (Hone : F.sum m (fun i => pi i*1)=F.sum m pi).
    { apply F.sum_ext. intros. ring. }
    rewrite Hone in Hcs.
    assert (Hq0 : 0 <= F.sum m (fun k => pi k*
      (clipped_level r J k*clipped_level r J k))).
    { apply F.sum_nonneg. intros k Hk. apply Rmult_le_pos; [apply Hpi|nra]. }
    assert (Hq : F.sum m (fun k => pi k*
      (clipped_level r J k*clipped_level r J k)) <= L).
    { eapply Rle_trans; [|apply Hmoment]. apply F.sum_mono.
      intros k Hk. apply Rmult_le_compat_l; [apply Hpi|].
      exact (proj2 (clipped_level_square_bound r H0 Hmono J k)). }
    pose proof (Rmult_le_compat_l _ _ _ Hq0 (HP m)) as Hprod.
    pose proof (sqrt_pos L). pose proof (sqrt_def L HL). nra. }
  apply (B.limit_upper_bound
    (fun m => F.sum (J+m) (fun k => pi k*clipped_level r J k))).
  - eapply B.limit_ext with (f := fun m => F.sum J (fun N =>
      (r (S N)-r N)*(F.sum (J+m) pi-F.sum (S N) pi))).
    + intro m. symmetry. apply finite_tail_interchange; [exact H0|lia].
    + apply finite_sum_limit. intro N. apply B.limit_scale.
      replace (1-F.sum (S N) pi) with (1+(-F.sum (S N) pi)) by ring.
      apply B.limit_plus.
      * intros eps Heps. destruct (Hlim eps Heps) as [n Hn].
        exists n. intros m Hm. apply Hn. lia.
      * apply B.limit_const.
  - intro m. apply Hfinite.
Qed.

Definition profile_root q k := sqrt (/q^k).
Definition profile_weight q N := profile_root q (S N)-profile_root q N.

Lemma profile_root_zero : forall q, profile_root q 0%nat = 1.
Proof. intro q. unfold profile_root. simpl. rewrite Rinv_1, sqrt_1. reflexivity. Qed.

Lemma inverse_q_power_positive : forall q, 0<q<1 -> forall k, 0 < /q^k.
Proof. intros q Hq k. apply Rinv_0_lt_compat. apply (SP.q_power_bounds q Hq k). Qed.

Lemma inverse_q_power_monotone : forall q, 0<q<1 -> forall n m,
  (n <= m)%nat -> /q^n <= /q^m.
Proof.
  intros q Hq n m Hnm. induction Hnm as [|m Hnm IH]; [lra|].
  eapply Rle_trans; [exact IH|].
  apply Rinv_le_contravar.
  - pose proof (SP.q_power_bounds q Hq m). simpl. nra.
  - simpl. pose proof (SP.q_power_bounds q Hq m). nra.
Qed.

Lemma profile_root_monotone : forall q, 0<q<1 -> forall n m,
  (n <= m)%nat -> profile_root q n <= profile_root q m.
Proof. intros q Hq n m Hnm. apply sqrt_le_1_alt.
  apply inverse_q_power_monotone; assumption. Qed.

Theorem BKME10_PROFILE_WEIGHT_NONNEGATIVE : forall q, 0<q<1 -> forall N,
  0 <= profile_weight q N.
Proof. intros q Hq N. unfold profile_weight.
  pose proof (profile_root_monotone q Hq N (S N) (Nat.le_succ_diag_r N)). lra. Qed.

Lemma profile_weight_positive : forall q, 0<q<1 -> forall N,
  0 < profile_weight q N.
Proof.
  intros q Hq N.
  assert (Hinv : /q^N < /q^(S N)).
  { apply Rinv_lt_contravar.
    - apply Rmult_lt_0_compat; apply (SP.q_power_bounds q Hq).
    - pose proof (SP.q_power_bounds q Hq N). simpl. nra. }
  pose proof (sqrt_pos (/q^N)). pose proof (sqrt_pos (/q^(S N))).
  pose proof (sqrt_def (/q^N) (Rlt_le _ _ (inverse_q_power_positive q Hq N))).
  pose proof (sqrt_def (/q^(S N))
    (Rlt_le _ _ (inverse_q_power_positive q Hq (S N)))).
  unfold profile_weight, profile_root. nra.
Qed.

Lemma scalar_moment_step : forall q x Hq Hx k,
  (/q^(S k)-1)*SP.probability q x Hq Hx (S k) =
  (x/q)*SP.probability q x Hq Hx k.
Proof.
  intros q x Hq Hx k.
  pose proof (SP.SCALAR_PROBABILITY_RAISING q x Hq Hx k) as Hr.
  assert (He : /q^(S k)-1 = SP.clock q k/q).
  { unfold SP.clock. simpl. field. split; pose proof (SP.q_power_bounds q Hq k); lra. }
  rewrite He.
  replace (SP.clock q k/q*SP.probability q x Hq Hx (S k)) with
    ((SP.clock q k*SP.probability q x Hq Hx (S k))/q) by (unfold Rdiv; ring).
  rewrite <- Hr. unfold Rdiv. ring.
Qed.

Lemma scalar_moment_prefix : forall q x Hq Hx m,
  F.sum (S m) (fun k => (/q^k-1)*SP.probability q x Hq Hx k) =
  (x/q)*F.sum m (SP.probability q x Hq Hx).
Proof.
  intros q x Hq Hx m. induction m as [|m IH].
  - cbn [F.sum pow]. rewrite Rinv_1. ring.
  - change (F.sum (S m) (fun k => (/q^k-1)*SP.probability q x Hq Hx k)+
      (/q^(S m)-1)*SP.probability q x Hq Hx (S m) =
      (x/q)*(F.sum m (SP.probability q x Hq Hx)+SP.probability q x Hq Hx m)).
    rewrite IH, scalar_moment_step. ring.
Qed.

Theorem BKME15_SCALAR_HIGH_PASS_ENVELOPE : forall q x Hq Hx J,
  F.sum J (fun N => profile_weight q N *
    (1-F.sum (S N) (SP.probability q x Hq Hx))) <= sqrt (x/q).
Proof.
  intros q x Hq Hx J.
  assert (HL : 0 <= x/q).
  { unfold Rdiv. apply Rmult_le_pos; [exact Hx|].
    apply Rlt_le, Rinv_0_lt_compat. exact (proj1 Hq). }
  assert (HP : forall m, F.sum m (SP.probability q x Hq Hx)<=1).
  { intro m. rewrite <- scalar_prefix_is_finite_sum.
    apply (proj1 (SP.SCALAR_PROBABILITY_PARTITION_LUB q x Hq Hx)).
    exists m. reflexivity. }
  apply (BKME00_PARTITION_MOMENT_GIVES_TAIL_ENVELOPE
    (SP.probability q x Hq Hx) (profile_root q) (x/q)).
  - apply SP.SCALAR_PROBABILITY_NONNEGATIVE.
  - exact HP.
  - intros eps Heps. destruct (SP.SCALAR_PROBABILITY_PARTITION q x Hq Hx eps Heps)
      as [N HN]. exists N. intros n Hn.
    rewrite <- scalar_prefix_is_finite_sum. apply HN. exact Hn.
  - apply profile_root_zero.
  - apply profile_root_monotone. exact Hq.
  - exact HL.
  - intro m. transitivity (F.sum m
      (fun k => (/q^k-1)*SP.probability q x Hq Hx k)).
    + apply Req_le, F.sum_ext. intros k Hk. unfold profile_root.
      rewrite sqrt_def by (apply Rlt_le, inverse_q_power_positive; exact Hq). ring.
    + destruct m as [|m]; [simpl; exact HL|]. rewrite scalar_moment_prefix.
      pose proof (Rmult_le_compat_l _ _ _ HL (HP m)). nra.
Qed.

Definition profile_tail q step lambda Hq Hstep N i :=
  1-B.gp_sum (S N) (fun k =>
    C.bkqr_weights q step lambda Hq Hstep k i *
    C.bkqr_weights q step lambda Hq Hstep k i).

Theorem BKME20_PROFILE_TAIL_BOUNDS : forall q step lambda Hq Hstep N i,
  0 <= profile_tail q step lambda Hq Hstep N i <= 1.
Proof.
  intros q step lambda Hq Hstep N i.
  pose proof (B.partition_prefix_bounds _
    (C.BKCL01_SCALAR_PARTITION q step lambda Hq Hstep) (S N) i) as H.
  unfold profile_tail. lra.
Qed.

Theorem BKME30_CANONICAL_HIGH_PASS_ENVELOPE :
  forall q step lambda Hq Hstep,
  (forall i, 0 <= lambda i) -> forall i J,
  F.sum J (fun N => profile_weight q N *
    profile_tail q step lambda Hq Hstep N i) <= sqrt (step/q)*lambda i.
Proof.
  intros q step lambda Hq Hstep Hlambda i J.
  pose proof (BKME15_SCALAR_HIGH_PASS_ENVELOPE q
    (C.spectral_argument step lambda i) Hq
    (C.spectral_argument_nonnegative step lambda Hstep i) J) as H.
  assert (Htail : forall N, profile_tail q step lambda Hq Hstep N i =
    1-F.sum (S N) (SP.probability q (C.spectral_argument step lambda i)
      Hq (C.spectral_argument_nonnegative step lambda Hstep i))).
  { intro N. unfold profile_tail. rewrite <- finite_sum_is_gp_sum.
    f_equal. apply F.sum_ext. intros k Hk.
    unfold C.bkqr_weights. apply SP.SCALAR_PSI_SQUARE. }
  assert (Hsum : F.sum J (fun N => profile_weight q N*
    profile_tail q step lambda Hq Hstep N i) =
    F.sum J (fun N => profile_weight q N *
      (1-F.sum (S N) (SP.probability q (C.spectral_argument step lambda i)
      Hq (C.spectral_argument_nonnegative step lambda Hstep i))))).
  { apply F.sum_ext. intros N HN. rewrite Htail. reflexivity. }
  rewrite Hsum. eapply Rle_trans; [exact H|].
  unfold C.spectral_argument.
  replace (step*(lambda i*lambda i)/q) with ((step/q)*(lambda i*lambda i))
    by (unfold Rdiv; ring).
  rewrite sqrt_mult; [|unfold Rdiv; apply Rmult_le_pos; [lra|apply Rlt_le, Rinv_0_lt_compat; lra]
    |nra]. rewrite sqrt_square by apply Hlambda. lra.
Qed.

(* The envelope includes zero spectral modes without division. Their
   canonical high-pass symbols vanish. Only the subsequent inverse-source
   norm specialization restricts the retained modal carrier to lambda>0. *)
Theorem BKME31_ZERO_FREQUENCY_HAS_ZERO_TAIL :
  forall q step lambda Hq Hstep,
  (forall i, 0 <= lambda i) -> forall i, lambda i=0 -> forall N,
  profile_tail q step lambda Hq Hstep N i = 0.
Proof.
  intros q step lambda Hq Hstep Hlambda i Hz N.
  pose proof (BKME30_CANONICAL_HIGH_PASS_ENVELOPE q step lambda Hq Hstep
    Hlambda i (S N)) as Henv.
  rewrite Hz in Henv.
  assert (Hp : forall k, (k<S N)%nat -> 0 <= profile_weight q k *
    profile_tail q step lambda Hq Hstep k i).
  { intros k Hk. apply Rmult_le_pos.
    - apply BKME10_PROFILE_WEIGHT_NONNEGATIVE. exact Hq.
    - apply BKME20_PROFILE_TAIL_BOUNDS. }
  pose proof (M.sum_term_at_most_sum (S N)
    (fun k => profile_weight q k*profile_tail q step lambda Hq Hstep k i)
    N Hp (Nat.lt_succ_diag_r N)) as Hterm.
  pose proof (profile_weight_positive q Hq N).
  pose proof (BKME20_PROFILE_TAIL_BOUNDS q step lambda Hq Hstep N i).
  nra.
Qed.

(* The profile symbol lambda is first order.  The Stokes symbol in the
   modal action is lambda squared, and the source norm is of order -1/2.
   Both the current and the nonlinear source use exactly the same a. *)
Theorem BKMA10_ACTION_FROM_FIRST_ORDER_ENVELOPE :
  forall n J lambda weights theta K table a,
  (forall i, (i<n)%nat -> 0<lambda i) ->
  (forall N, (N<J)%nat -> 0<=weights N) ->
  (forall N i, (N<J)%nat -> (i<n)%nat -> 0<=theta N i) ->
  (forall i, (i<n)%nat ->
     F.sum J (fun N => weights N*theta N i)<=K*lambda i) ->
  M.finite_cut_action n table (fun i => lambda i*lambda i) J
    weights theta a <=
  K*F.sum n (fun i =>
    M.modal_source n table a i*M.modal_source n table a i/lambda i).
Proof.
  intros n J lambda weights theta K table a Hlambda Hw Htheta Henv.
  assert (Hmu : forall i, (i<n)%nat -> 0<lambda i*lambda i).
  { intros i Hi. pose proof (Hlambda i Hi). nra. }
  assert (Htail : E.FiniteTailEnvelope n J
      (fun i => lambda i*lambda i) weights theta
      (fun i => /lambda i) K).
  { intros i Hi. cbn.
    replace (K*(lambda i*lambda i)*/lambda i) with (K*lambda i).
    - apply Henv. exact Hi.
    - field. pose proof (Hlambda i Hi). lra. }
  pose proof (E.NSHC21_FINITE_SOURCE_ACTION_FROM_TAIL_ENVELOPE
    n J (fun i => lambda i*lambda i) weights theta
    (fun i => /lambda i) K (M.modal_source n table a) a
    Hmu Hw Htheta Htail) as Haction.
  change (M.finite_cut_action n table (fun i => lambda i*lambda i)
    J weights theta a <=
    K*E.source_norm n (fun i => /lambda i) (M.modal_source n table a))
    in Haction.
  assert (Hnorm : E.source_norm n (fun i => /lambda i)
      (M.modal_source n table a) =
    F.sum n (fun i =>
      M.modal_source n table a i*M.modal_source n table a i/lambda i)).
  { unfold E.source_norm. apply F.sum_ext. intros i Hi. unfold Rdiv. ring. }
  rewrite Hnorm in Haction. exact Haction.
Qed.


Theorem BKME40_CANONICAL_FINITE_CUT_ACTION :
  forall q step lambda (Hq:0<q<1) (Hstep:0<step)
    (Hlambda:forall i,0<=lambda i) n J table a,
  (forall i, (i<n)%nat -> 0<lambda i) ->
  M.finite_cut_action n table (fun i => lambda i*lambda i) J
    (profile_weight q) (profile_tail q step lambda Hq Hstep) a <=
  sqrt(step/q)*F.sum n (fun i =>
    M.modal_source n table a i*M.modal_source n table a i/lambda i).
Proof.
  intros q step lambda Hq Hstep Hlambda n J table a Hpositive.
  apply BKMA10_ACTION_FROM_FIRST_ORDER_ENVELOPE.
  - exact Hpositive.
  - intros N HN. exact (BKME10_PROFILE_WEIGHT_NONNEGATIVE q Hq N).
  - intros N i HN Hi.
    exact (proj1 (BKME20_PROFILE_TAIL_BOUNDS q step lambda Hq Hstep N i)).
  - intros i Hi.
    exact (BKME30_CANONICAL_HIGH_PASS_ENVELOPE
      q step lambda Hq Hstep Hlambda i J).
Qed.

(* All occurrences of the modal state are literally the same reconstructed
   coordinate vector.  No independent source or surrogate state appears. *)
Corollary BKME41_RECONSTRUCTED_FINITE_CUT_ACTION :
  forall q step lambda (Hq:0<q<1) (Hstep:0<step)
    (Hlambda:forall i,0<=lambda i) n J table U,
  (forall i, (i<n)%nat -> 0<lambda i) ->
  let a := S.reconstruct (C.bkqr_weights q step lambda Hq Hstep) U in
  M.finite_cut_action n table (fun i => lambda i*lambda i) J
    (profile_weight q) (profile_tail q step lambda Hq Hstep) a <=
  sqrt(step/q)*F.sum n (fun i =>
    M.modal_source n table a i*M.modal_source n table a i/lambda i).
Proof.
  intros q step lambda Hq Hstep Hlambda n J table U Hpositive.
  apply BKME40_CANONICAL_FINITE_CUT_ACTION; assumption.
Qed.

Print Assumptions BKME30_CANONICAL_HIGH_PASS_ENVELOPE.
Print Assumptions BKME40_CANONICAL_FINITE_CUT_ACTION.
Print Assumptions BKME41_RECONSTRUCTED_FINITE_CUT_ACTION.
End BKQR_M7_PROFILE_ENVELOPE.
