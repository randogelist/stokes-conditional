From Stdlib Require Import Reals Lra Psatz Field Lia.
Require Import awpi_nse_native_kq_ladder_v0_49_3.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_schur_action_ledger_v0_49_3.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.
Require Import awpi_nse_helicity_defect_geometry_v0_51_0.

Module NSE_FINITE_CUT_DEFECT_BOUND.
Import NSE_KQ_FINITE_ALGEBRA NSE_SCHUR_ACTION_LEDGER.
Import NSE_GALERKIN_MODAL_CALCULUS NSE_HELICITY_DEFECT_GEOMETRY NSE_NATIVE_KQ_LADDER.
Open Scope R_scope.

Definition source_current n theta F u := -dot n F (mul theta u).
Definition source_dual n lambda theta F :=
  sum n (fun i => theta i/lambda i*F i*F i).
Definition source_norm n beta F := sum n (fun i => beta i*F i*F i).
Definition source_action n J lambda weights theta F u :=
  sum J (fun m => weights m*positive_action
    (source_current n (theta m) F u)
    (cut_dissipation n lambda (theta m) u)).

Lemma source_dual_nonnegative : forall n lambda theta F,
  (forall i, (i<n)%nat -> 0<lambda i) ->
  (forall i, (i<n)%nat -> 0<=theta i) ->
  0<=source_dual n lambda theta F.
Proof.
  intros n lambda theta F Hl Ht; unfold source_dual; apply sum_nonneg.
  intros i Hi; unfold Rdiv.
  replace (theta i * /lambda i * F i * F i) with
    ((theta i * /lambda i)*(F i*F i)) by ring.
  apply Rmult_le_pos.
  - apply Rmult_le_pos; [exact (Ht i Hi)|].
    apply Rlt_le; apply Rinv_0_lt_compat; exact (Hl i Hi).
  - exact (Rle_0_sqr (F i)).
Qed.

Theorem NSHC10_ACTUAL_SOURCE_WEIGHTED_CAUCHY : forall n lambda theta F u,
  (forall i, (i<n)%nat -> 0<lambda i) ->
  (forall i, (i<n)%nat -> 0<=theta i) ->
  source_current n theta F u * source_current n theta F u <=
  source_dual n lambda theta F * cut_dissipation n lambda theta u.
Proof.
  intros n lambda theta F u Hl Ht.
  assert (HQ : forall i, (i<n)%nat -> 0<=F i*F i/lambda i).
  { intros i Hi; unfold Rdiv; apply Rmult_le_pos.
    - exact (Rle_0_sqr (F i)).
    - apply Rlt_le; apply Rinv_0_lt_compat; exact (Hl i Hi). }
  assert (HZ : forall i, (i<n)%nat -> 0<=lambda i*u i*u i).
  { intros i Hi; replace (lambda i*u i*u i) with (lambda i*(u i*u i)) by ring.
    apply Rmult_le_pos; [pose proof (Hl i Hi); lra|exact (Rle_0_sqr (u i))]. }
  assert (Hpoint : forall i, (i<n)%nat ->
    (-F i*u i)*(-F i*u i) <= (F i*F i/lambda i)*(lambda i*u i*u i)).
  { intros i Hi; assert (He : (F i*F i/lambda i)*(lambda i*u i*u i)=
      (-F i*u i)*(-F i*u i)).
    { field; pose proof (Hl i Hi); lra. }
    rewrite He; apply Rle_refl. }
  pose proof (NSKA20_WEIGHTED_CAUCHY n theta
    (fun i => F i*F i/lambda i) (fun i => lambda i*u i*u i)
    (fun i => -F i*u i) Ht HQ HZ Hpoint) as HC.
  cbn beta zeta in HC.
  assert (HeQ : sum n (fun i => theta i*(F i*F i/lambda i)) =
    source_dual n lambda theta F).
  { unfold source_dual; apply sum_ext; intros; unfold Rdiv; ring. }
  assert (HeZ : sum n (fun i => theta i*(lambda i*u i*u i)) =
    cut_dissipation n lambda theta u).
  { unfold cut_dissipation; apply sum_ext; intros; ring. }
  assert (HeR : sum n (fun i => theta i*(-F i*u i)) = source_current n theta F u).
  { unfold source_current, dot, mul.
    replace (-sum n (fun i => F i*(theta i*u i))) with
      ((-1)*sum n (fun i => F i*(theta i*u i))) by ring.
    rewrite <- sum_scale; apply sum_ext; intros; ring. }
  rewrite HeQ, HeZ, HeR in HC; exact HC.
Qed.

Theorem NSHC11_ZERO_CAPACITY_SOURCE_FIREWALL : forall n lambda theta F u,
  (forall i, (i<n)%nat -> 0<lambda i) ->
  (forall i, (i<n)%nat -> 0<=theta i) ->
  cut_dissipation n lambda theta u=0 -> source_current n theta F u=0.
Proof.
  intros n lambda theta F u Hl Ht HD.
  pose proof (NSHC10_ACTUAL_SOURCE_WEIGHTED_CAUCHY n lambda theta F u Hl Ht) as HC.
  rewrite HD in HC; nra.
Qed.

Lemma positive_action_from_cauchy : forall phi d Q,
  0<=d -> 0<=Q -> phi*phi<=Q*d -> positive_action phi d<=Q.
Proof.
  intros phi d Q HD HQ HC.
  destruct (Req_dec d 0) as [Hz|Hz].
  - subst d; unfold positive_action, Rdiv; rewrite Rinv_0, Rmult_0_r; exact HQ.
  - assert (Hd : 0<d) by lra.
    unfold positive_action.
    destruct (Rle_dec 0 phi) as [Hp|Hp].
    + rewrite Rmax_left by lra.
      apply (Rmult_le_reg_r d); [exact Hd|].
      replace (phi*phi/d*d) with (phi*phi) by (field; exact Hz).
      exact HC.
    + rewrite Rmax_right by lra; unfold Rdiv; nra.
Qed.

Theorem NSHC12_SINGLE_CUT_ACTION_BOUND : forall n lambda theta F u,
  (forall i, (i<n)%nat -> 0<lambda i) ->
  (forall i, (i<n)%nat -> 0<=theta i) ->
  positive_action (source_current n theta F u)
    (cut_dissipation n lambda theta u) <= source_dual n lambda theta F.
Proof.
  intros n lambda theta F u Hl Ht; apply positive_action_from_cauchy.
  - apply cut_dissipation_nonnegative; [intros; apply Rlt_le; auto|exact Ht].
  - apply source_dual_nonnegative; assumption.
  - apply NSHC10_ACTUAL_SOURCE_WEIGHTED_CAUCHY; assumption.
Qed.

Theorem NSHC20_FINITE_CUT_SUM_INTERCHANGE : forall n J lambda weights theta F,
  sum J (fun m => weights m*source_dual n lambda (theta m) F) =
  sum n (fun i => (sum J (fun m => weights m*theta m i))/lambda i*F i*F i).
Proof.
  intros n J lambda weights theta F; unfold source_dual.
  transitivity (sum J (fun m => sum n (fun i =>
    weights m*(theta m i/lambda i*F i*F i)))).
  - apply sum_ext; intros; symmetry; apply sum_scale.
  - rewrite (finite_sum_swap J n (fun m i =>
      weights m*(theta m i/lambda i*F i*F i))).
    apply sum_ext; intros i Hi.
    transitivity (sum J (fun m =>
      (F i*F i/lambda i)*(weights m*theta m i))).
    + apply sum_ext; intros; unfold Rdiv; ring.
    + rewrite sum_scale; unfold Rdiv; ring.
Qed.

(* The finite multiplier envelope is an explicit physical-clock interface.
   This file does NOT construct the infinite q-product or its shell law. *)
Definition FiniteTailEnvelope n J lambda weights theta beta K : Prop :=
  forall i, (i<n)%nat ->
    sum J (fun m => weights m*theta m i) <= K*lambda i*beta i.

Theorem NSHC21_FINITE_SOURCE_ACTION_FROM_TAIL_ENVELOPE :
  forall n J lambda weights theta beta K F u,
  (forall i, (i<n)%nat -> 0<lambda i) ->
  (forall m, (m<J)%nat -> 0<=weights m) ->
  (forall m i, (m<J)%nat -> (i<n)%nat -> 0<=theta m i) ->
  FiniteTailEnvelope n J lambda weights theta beta K ->
  source_action n J lambda weights theta F u <= K*source_norm n beta F.
Proof.
  intros n J lambda weights theta beta K F u Hl Hw Ht Henv.
  eapply Rle_trans with
    (r2:=sum J (fun m => weights m*source_dual n lambda (theta m) F)).
  - unfold source_action; apply sum_mono; intros m Hm.
    apply Rmult_le_compat_l; [exact (Hw m Hm)|].
    apply NSHC12_SINGLE_CUT_ACTION_BOUND; [exact Hl|].
    intros i Hi; exact (Ht m i Hm Hi).
  - rewrite NSHC20_FINITE_CUT_SUM_INTERCHANGE.
    unfold source_norm; rewrite <- sum_scale.
    apply sum_mono; intros i Hi.
    assert (Hcoef : (sum J (fun m => weights m*theta m i))/lambda i<=K*beta i).
    { apply (Rmult_le_reg_r (lambda i)); [exact (Hl i Hi)|].
      replace ((sum J (fun m => weights m*theta m i))/lambda i*lambda i)
        with (sum J (fun m => weights m*theta m i)) by
        (field; pose proof (Hl i Hi); lra).
      pose proof (Henv i Hi) as HM; nra. }
    pose proof (Rmult_le_compat_r (F i*F i)
      ((sum J (fun m => weights m*theta m i))/lambda i) (K*beta i)
      (Rle_0_sqr (F i)) Hcoef) as Hscaled.
    nra.
Qed.

Theorem NSHC22_SCALAR_NATIVE_MOMENT_ENVELOPE : forall M x q,
  0<q -> 0<=x -> M*M<=1+x/q -> M-1<=sqrt (x/q).
Proof.
  intros M x q Hq Hx HM.
  assert (Hratio : 0<=x/q).
  { unfold Rdiv; apply Rmult_le_pos; [exact Hx|].
    apply Rlt_le; apply Rinv_0_lt_compat; exact Hq. }
  pose proof (sqrt_pos (x/q)) as Hs.
  pose proof (sqrt_def (x/q) Hratio) as Hsq.
  destruct (Rle_dec M (1+sqrt (x/q))) as [Hle|Hle]; [lra|].
  assert (Hp : 0<(M-1-sqrt (x/q))*(M+1+sqrt (x/q))).
  { apply Rmult_lt_0_compat; lra. }
  nra.
Qed.

(* This is the finite, normalized, nonnegative-weight moment calculation.
   Native infinite shell construction remains separate. *)
Theorem NSHC23_FINITE_PROBABILITY_MOMENT : forall N pi v,
  (forall j, (j<N)%nat -> 0<=pi j) -> sum N pi=1 ->
  sum N (fun j => pi j*v j)*sum N (fun j => pi j*v j) <=
    sum N (fun j => pi j*(v j*v j)).
Proof.
  intros N pi v Hp Hsum.
  assert (Hq : forall j, (j<N)%nat -> 0<=v j*v j).
  { intros; exact (Rle_0_sqr (v j)). }
  assert (Hz : forall j, (j<N)%nat -> 0 <= (1:R)) by (intros; lra).
  assert (Hr : forall j, (j<N)%nat -> v j*v j<=(v j*v j)*1) by (intros; nra).
  pose proof (NSKA20_WEIGHTED_CAUCHY N pi (fun j => v j*v j)
    (fun _ => 1) v Hp Hq Hz Hr) as HC.
  cbn beta zeta in HC.
  assert (He : sum N (fun j => pi j*1)=sum N pi).
  { apply sum_ext; intros; ring. }
  rewrite He, Hsum in HC; nra.
Qed.

(* The precise analytic Sobolev/Lamb estimate used by this anchor is
   visible here.  It is NOT provided as a project axiom or claimed proved. *)
Definition SourceDefectEstimate n lambda T beta u omega C : Prop :=
  source_norm n beta (modal_source n T u) <=
    C*spectral_energy n lambda u*hd_defect n u omega.

Theorem NSHC30_MODAL_ACTION_FROM_DEFECT_SOURCE_ESTIMATE :
  forall n J lambda T weights theta beta K C u omega,
  0<=K ->
  (forall i, (i<n)%nat -> 0<lambda i) ->
  (forall m, (m<J)%nat -> 0<=weights m) ->
  (forall m i, (m<J)%nat -> (i<n)%nat -> 0<=theta m i) ->
  FiniteTailEnvelope n J lambda weights theta beta K ->
  SourceDefectEstimate n lambda T beta u omega C ->
  finite_cut_action n T lambda J weights theta u <=
    (K*C)*spectral_energy n lambda u*hd_defect n u omega.
Proof.
  intros n J lambda T weights theta beta K C u omega HK Hl Hw Ht Henv Hsource.
  pose proof (NSHC21_FINITE_SOURCE_ACTION_FROM_TAIL_ENVELOPE
    n J lambda weights theta beta K (modal_source n T u) u Hl Hw Ht Henv) as HA.
  change (finite_cut_action n T lambda J weights theta u <=
    K*source_norm n beta (modal_source n T u)) in HA.
  unfold SourceDefectEstimate in Hsource.
  pose proof (Rmult_le_compat_l K
    (source_norm n beta (modal_source n T u))
    (C*spectral_energy n lambda u*hd_defect n u omega) HK Hsource) as HS.
  nra.
Qed.

End NSE_FINITE_CUT_DEFECT_BOUND.
