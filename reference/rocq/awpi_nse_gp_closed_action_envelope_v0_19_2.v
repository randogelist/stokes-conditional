
From Stdlib Require Import Reals Lra Psatz Field.
Require Import awpi_nse_gp_perspective_action_v0_11_2.
Open Scope R_scope.

Module NSE_GP_CLOSED_ACTION_ENVELOPE.

Module PA := NSE_GP_PERSPECTIVE_ACTION.

(* Closed, denominator-free form of the bound A = w^2/d <= M. *)
Definition ActionEnvelope (w d M : R) : Prop :=
  0 <= d /\ 0 <= M /\ w*w <= d*M.

(* Any nonnegative action certificate bounded by M gives the closed envelope. *)
Theorem GPCE00_ACTION_BOUND_GIVES_ENVELOPE :
  forall w d A M : R,
    0 <= d ->
    0 <= A ->
    PA.ActionRel w d A ->
    A <= M ->
    ActionEnvelope w d M.
Proof.
  intros w d A M Hd HA Hact HAM.
  unfold ActionEnvelope.
  split.
  - exact Hd.
  - split.
    + lra.
    + unfold PA.ActionRel in Hact.
      nra.
Qed.

(* At zero capacity, the closed envelope forces zero work. *)
Theorem GPCE01_ZERO_CAPACITY_FORCES_ZERO_WORK :
  forall w M : R,
    ActionEnvelope w 0 M ->
    w = 0.
Proof.
  intros w M H.
  unfold ActionEnvelope in H.
  destruct H as [Hd [HM Hbound]].
  simpl in Hbound.
  pose proof (Rle_0_sqr w) as Hsq.
  unfold Rsqr in Hsq.
  assert (Hw2 : w*w = 0) by lra.
  destruct (Rmult_integral w w Hw2) as [Hz | Hz].
  - exact Hz.
  - exact Hz.
Qed.

(* Positive capacity: reconstruct the exact perspective action without
   losing the closed bound. *)
Theorem GPCE10_POSITIVE_ENVELOPE_RECONSTRUCTS_ACTION :
  forall w d M : R,
    0 < d ->
    ActionEnvelope w d M ->
    exists A : R,
      0 <= A /\
      A <= M /\
      PA.ActionRel w d A.
Proof.
  intros w d M Hd Henv.
  unfold ActionEnvelope in Henv.
  destruct Henv as [Hd0 [HM Hbound]].
  exists (w*w/d).
  assert (Hdne : d <> 0) by lra.
  assert (HArel : d * (w*w/d) = w*w).
  {
    unfold Rdiv.
    replace (d * (w*w * / d))
      with ((w*w) * (d * / d)) by ring.
    rewrite Rinv_r.
    - ring.
    - exact Hdne.
  }
  assert (HA0 : 0 <= w*w/d).
  {
    unfold Rdiv.
    apply Rmult_le_pos.
    - pose proof (Rle_0_sqr w) as Hsq.
      unfold Rsqr in Hsq.
      exact Hsq.
    - left.
      apply Rinv_0_lt_compat.
      exact Hd.
  }
  assert (HAM : w*w/d <= M).
  {
    nra.
  }
  repeat split.
  - exact HA0.
  - exact HAM.
  - unfold PA.ActionRel.
    exact HArel.
Qed.

(* Zero capacity: reconstruct the canonical zero action. *)
Theorem GPCE11_ZERO_ENVELOPE_RECONSTRUCTS_ACTION :
  forall w M : R,
    ActionEnvelope w 0 M ->
    exists A : R,
      0 <= A /\
      A <= M /\
      PA.ActionRel w 0 A.
Proof.
  intros w M Henv.
  pose proof (GPCE01_ZERO_CAPACITY_FORCES_ZERO_WORK w M Henv) as Hw.
  unfold ActionEnvelope in Henv.
  destruct Henv as [Hd [HM Hbound]].
  exists 0.
  subst w.
  split.
  - lra.
  - split.
    + exact HM.
    + unfold PA.ActionRel.
      ring.
Qed.

(* Unified reconstruction, including d=0. *)
Theorem GPCE12_CLOSED_ENVELOPE_RECONSTRUCTS_ACTION :
  forall w d M : R,
    ActionEnvelope w d M ->
    exists A : R,
      0 <= A /\
      A <= M /\
      PA.ActionRel w d A.
Proof.
  intros w d M Henv.
  unfold ActionEnvelope in Henv.
  destruct Henv as [Hd [HM Hbound]].
  destruct (Req_dec d 0) as [Hz | Hnz].
  - subst d.
    apply GPCE11_ZERO_ENVELOPE_RECONSTRUCTS_ACTION.
    unfold ActionEnvelope.
    repeat split; assumption.
  - apply GPCE10_POSITIVE_ENVELOPE_RECONSTRUCTS_ACTION.
    + lra.
    + unfold ActionEnvelope.
      repeat split; assumption.
Qed.

(* The envelope is exactly the polynomial inequality needed for
   cutoff/weak-limit passage: no division and no undefined 0/0 case. *)
Theorem GPCE20_ENVELOPE_IS_POLYNOMIAL_BOUND :
  forall w d M : R,
    ActionEnvelope w d M ->
    w*w <= d*M.
Proof.
  intros w d M H.
  unfold ActionEnvelope in H.
  tauto.
Qed.

(* Uniform bound specialization used after a Galerkin limit. *)
Theorem GPCE21_LIMIT_BOUND_TO_ACTION_CERTIFICATE :
  forall w d M : R,
    0 <= d ->
    0 <= M ->
    w*w <= d*M ->
    exists A : R,
      0 <= A /\
      A <= M /\
      PA.ActionRel w d A.
Proof.
  intros w d M Hd HM Hpoly.
  apply GPCE12_CLOSED_ENVELOPE_RECONSTRUCTS_ACTION.
  unfold ActionEnvelope.
  repeat split; assumption.
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_CLOSED_ACTION_ENVELOPE.

Check NSE_GP_CLOSED_ACTION_ENVELOPE.GPCE00_ACTION_BOUND_GIVES_ENVELOPE.
Check NSE_GP_CLOSED_ACTION_ENVELOPE.GPCE01_ZERO_CAPACITY_FORCES_ZERO_WORK.
Check NSE_GP_CLOSED_ACTION_ENVELOPE.GPCE10_POSITIVE_ENVELOPE_RECONSTRUCTS_ACTION.
Check NSE_GP_CLOSED_ACTION_ENVELOPE.GPCE11_ZERO_ENVELOPE_RECONSTRUCTS_ACTION.
Check NSE_GP_CLOSED_ACTION_ENVELOPE.GPCE12_CLOSED_ENVELOPE_RECONSTRUCTS_ACTION.
Check NSE_GP_CLOSED_ACTION_ENVELOPE.GPCE20_ENVELOPE_IS_POLYNOMIAL_BOUND.
Check NSE_GP_CLOSED_ACTION_ENVELOPE.GPCE21_LIMIT_BOUND_TO_ACTION_CERTIFICATE.
