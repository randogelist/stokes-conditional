From Stdlib Require Import Reals Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.

Module NSE_CANDIDATE_F_WORK.
Import NSE_KQ_FINITE_ALGEBRA NSE_GALERKIN_MODAL_CALCULUS.
Open Scope R_scope.

Definition sqrt_filter_residual n T eta u :=
  sub (modal_source n T (mul eta u)) (mul eta (modal_source n T u)).

Lemma diagonal_pairing_square : forall n eta F u,
  dot n (mul eta F) (mul eta u) = dot n F (mul (mul eta eta) u).
Proof. intros; unfold dot, mul; apply sum_ext; intros; ring. Qed.

Theorem NSFW00_FULL_FILTERED_RESIDUAL_WORK : forall n T eta u,
  SkewTable n T ->
  -dot n (sqrt_filter_residual n T eta u) (mul eta u) =
  dot n (modal_source n T u) (mul (mul eta eta) u).
Proof.
  intros n T eta u HT; unfold sqrt_filter_residual.
  rewrite dot_sub_l.
  rewrite (NSMG02_ACTUAL_MODAL_SOURCE_ENERGY_CANCELLATION n T (mul eta u) HT).
  rewrite diagonal_pairing_square; ring.
Qed.

Theorem NSFW01_SQUARE_ROOT_FILTER_IS_EXACT_CUT_WORK : forall n T eta theta u,
  SkewTable n T ->
  (forall i, (i<n)%nat -> eta i*eta i+theta i=1) ->
  -dot n (sqrt_filter_residual n T eta u) (mul eta u) =
  cut_current n T theta u.
Proof.
  intros n T eta theta u HT Hsplit.
  rewrite (NSFW00_FULL_FILTERED_RESIDUAL_WORK n T eta u HT).
  assert (Hpair : dot n (modal_source n T u) (mul (mul eta eta) u) +
    dot n (modal_source n T u) (mul theta u) =
    dot n (modal_source n T u) u).
  { unfold dot, mul; rewrite <- sum_add; apply sum_ext; intros i Hi.
    pose proof (Hsplit i Hi) as Hs.
    replace (modal_source n T u i*(eta i*eta i*u i)+
      modal_source n T u i*(theta i*u i)) with
      (modal_source n T u i*u i*(eta i*eta i+theta i)) by ring.
    rewrite Hs; ring. }
  rewrite (NSMG02_ACTUAL_MODAL_SOURCE_ENERGY_CANCELLATION n T u HT) in Hpair.
  unfold cut_current; lra.
Qed.

Theorem NSFW02_ACTUAL_SQRT_FILTER_WORK : forall n T theta u,
  SkewTable n T ->
  (forall i, (i<n)%nat -> theta i<=1) ->
  -dot n (sqrt_filter_residual n T (fun i => sqrt (1-theta i)) u)
    (mul (fun i => sqrt (1-theta i)) u) = cut_current n T theta u.
Proof.
  intros n T theta u HT Htheta.
  apply NSFW01_SQUARE_ROOT_FILTER_IS_EXACT_CUT_WORK; [exact HT|].
  intros i Hi; assert (Hpos : 0<=1-theta i) by (pose proof (Htheta i Hi); lra).
  pose proof (sqrt_def (1-theta i) Hpos) as Hsq; lra.
Qed.

(* The ordinary filtered field has squared-filter self-work.  This is
   intentionally different from claiming that L itself is a projection. *)
Theorem NSFW03_ORDINARY_FILTER_WORK_HAS_SQUARED_SYMBOL : forall n T ell u,
  SkewTable n T ->
  -dot n (sqrt_filter_residual n T ell u) (mul ell u) =
  dot n (modal_source n T u) (mul (mul ell ell) u).
Proof. exact NSFW00_FULL_FILTERED_RESIDUAL_WORK. Qed.

(* Concrete real diagonal pullback.  Complex spectral powers and their
   domain/limit theory are not implemented by this finite identity. *)
Definition gp_pull (s x : Vec) := mul s x.
Definition gp_push (s x : Vec) : Vec := fun i => x i/s i.
Definition gp_metric n s x y := dot n (gp_push s x) (gp_push s y).

Theorem NSFW10_REAL_DIAGONAL_GP_ISOMETRY : forall n s x y,
  (forall i, (i<n)%nat -> s i<>0) ->
  gp_metric n s (gp_pull s x) (gp_pull s y)=dot n x y.
Proof.
  intros n s x y Hs; unfold gp_metric, gp_push, gp_pull, mul, dot.
  apply sum_ext; intros i Hi; field; exact (Hs i Hi).
Qed.

End NSE_CANDIDATE_F_WORK.
