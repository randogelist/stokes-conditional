
From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

Module NSE_GP_PERSPECTIVE_ACTION.

Definition ActionRel (w d A : R) : Prop :=
  d * A = w * w.

Theorem GPPA00_ACTION_NONNEGATIVE :
  forall w d A : R,
    0 < d ->
    ActionRel w d A ->
    0 <= A.
Proof.
  intros w d A Hd Hact.
  unfold ActionRel in Hact.
  pose proof (Rle_0_sqr w) as Hw.
  unfold Rsqr in Hw.
  nra.
Qed.

Theorem GPPA01_MATCHED_GAUGE :
  forall w d A p : R,
    ActionRel w d A ->
    ActionRel (p * w) (p * d) (p * A).
Proof.
  intros w d A p Hact.
  unfold ActionRel in *.
  replace ((p * d) * (p * A)) with ((p * p) * (d * A)) by ring.
  rewrite Hact.
  ring.
Qed.

Theorem GPPA02_SAME_DENOMINATOR_GAUGE :
  forall w d A p : R,
    ActionRel w d A ->
    ActionRel (p * w) d ((p * p) * A).
Proof.
  intros w d A p Hact.
  unfold ActionRel in *.
  replace (d * ((p * p) * A)) with ((p * p) * (d * A)) by ring.
  rewrite Hact.
  ring.
Qed.

Theorem GPPA10_BINARY_PERSPECTIVE_DEFECT :
  forall w1 w2 d1 d2 A1 A2 Ac : R,
    ActionRel w1 d1 A1 ->
    ActionRel w2 d2 A2 ->
    ActionRel (w1 + w2) (d1 + d2) Ac ->
    d1 * d2 * (d1 + d2) * (A1 + A2 - Ac)
      = (d2 * w1 - d1 * w2) * (d2 * w1 - d1 * w2).
Proof.
  intros w1 w2 d1 d2 A1 A2 Ac H1 H2 Hc.
  unfold ActionRel in H1, H2, Hc.
  replace (d1 * d2 * (d1 + d2) * (A1 + A2 - Ac))
    with
      (d2 * (d1 + d2) * (d1 * A1)
       + d1 * (d1 + d2) * (d2 * A2)
       - d1 * d2 * ((d1 + d2) * Ac)) by ring.
  rewrite H1, H2, Hc.
  ring.
Qed.

Theorem GPPA11_BINARY_FUSION_CONTRACTS_ACTION :
  forall w1 w2 d1 d2 A1 A2 Ac : R,
    0 < d1 ->
    0 < d2 ->
    ActionRel w1 d1 A1 ->
    ActionRel w2 d2 A2 ->
    ActionRel (w1 + w2) (d1 + d2) Ac ->
    Ac <= A1 + A2.
Proof.
  intros w1 w2 d1 d2 A1 A2 Ac Hd1 Hd2 H1 H2 Hc.
  pose proof
    (GPPA10_BINARY_PERSPECTIVE_DEFECT
      w1 w2 d1 d2 A1 A2 Ac H1 H2 Hc) as Hdef.
  pose proof (Rle_0_sqr (d2*w1 - d1*w2)) as Hsq.
  unfold Rsqr in Hsq.
  assert (Hcoef : 0 < d1 * d2 * (d1 + d2)).
  {
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; assumption.
    - lra.
  }
  nra.
Qed.

Theorem GPPA12_ZERO_DEFECT_FORCES_MATCH :
  forall w1 w2 d1 d2 A1 A2 Ac : R,
    ActionRel w1 d1 A1 ->
    ActionRel w2 d2 A2 ->
    ActionRel (w1 + w2) (d1 + d2) Ac ->
    Ac = A1 + A2 ->
    d2 * w1 = d1 * w2.
Proof.
  intros w1 w2 d1 d2 A1 A2 Ac H1 H2 Hc Heq.
  pose proof
    (GPPA10_BINARY_PERSPECTIVE_DEFECT
      w1 w2 d1 d2 A1 A2 Ac H1 H2 Hc) as Hdef.
  assert (Hz :
    (d2*w1 - d1*w2) * (d2*w1 - d1*w2) = 0).
  {
    rewrite Heq in Hdef.
    lra.
  }
  destruct (Rmult_integral _ _ Hz) as [H | H].
  - lra.
  - lra.
Qed.

Theorem GPPA20_MATCHED_TWO_CHILD_ACTION_SUM :
  forall A p q : R,
    p + q = 1 ->
    p * A + q * A = A.
Proof.
  intros A p q Hpq.
  replace (p * A + q * A) with ((p + q) * A) by ring.
  rewrite Hpq.
  ring.
Qed.

Theorem GPPA21_THREE_FIFTHS_GIVES_NINE_TWENTY_FIFTHS :
  forall A p : R,
    0 <= A ->
    0 <= p ->
    5 * p <= 3 ->
    (p * p) * A <= (9 / 25) * A.
Proof.
  intros A p HA Hp H35.
  assert (Hminus : 0 <= 3 - 5*p) by lra.
  assert (Hplus : 0 <= 3 + 5*p) by lra.
  assert (Hsq : 0 <= (3 - 5*p) * (3 + 5*p)).
  {
    apply Rmult_le_pos.
    - exact Hminus.
    - exact Hplus.
  }
  replace ((3 - 5*p) * (3 + 5*p))
    with (9 - 25*(p*p)) in Hsq by ring.
  assert (Hscaled : 0 <= (9 - 25*(p*p)) * A).
  {
    apply Rmult_le_pos.
    - exact Hsq.
    - exact HA.
  }
  replace ((9 - 25*(p*p)) * A)
    with (9*A - 25*((p*p)*A)) in Hscaled by ring.
  lra.
Qed.

Theorem GPPA22_SAME_DENOM_SELECTED_ACTION_GAP :
  forall w d A p : R,
    0 < d ->
    0 <= p ->
    5 * p <= 3 ->
    ActionRel w d A ->
    exists Achild : R,
      ActionRel (p*w) d Achild /\
      Achild <= (9/25) * A.
Proof.
  intros w d A p Hd Hp H35 Hact.
  exists ((p*p)*A).
  split.
  - apply GPPA02_SAME_DENOMINATOR_GAUGE.
    exact Hact.
  - apply GPPA21_THREE_FIFTHS_GIVES_NINE_TWENTY_FIFTHS.
    + eapply GPPA00_ACTION_NONNEGATIVE; eauto.
    + exact Hp.
    + exact H35.
Qed.

Theorem GPPA30_MATCHED_LINEAR_OBSERVABLE :
  forall A p q x y z : R,
    p + q = 1 ->
    p*x + q*y = z ->
    x*(p*A) + y*(q*A) = z*A.
Proof.
  intros A p q x y z Hsum Hobs.
  replace (x * (p * A) + y * (q * A))
    with ((p*x + q*y) * A) by ring.
  rewrite Hobs.
  ring.
Qed.

Theorem GPPA31_MATCHED_DEFECT_SCALES_WITH_ACTION :
  forall A p q x y z delta : R,
    p*x + q*y - z = delta ->
    x*(p*A) + y*(q*A) - z*A = delta*A.
Proof.
  intros A p q x y z delta H.
  replace (x * (p * A) + y * (q * A) - z * A)
    with ((p*x + q*y - z) * A) by ring.
  rewrite H.
  ring.
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_PERSPECTIVE_ACTION.

Check NSE_GP_PERSPECTIVE_ACTION.GPPA00_ACTION_NONNEGATIVE.
Check NSE_GP_PERSPECTIVE_ACTION.GPPA01_MATCHED_GAUGE.
Check NSE_GP_PERSPECTIVE_ACTION.GPPA02_SAME_DENOMINATOR_GAUGE.
Check NSE_GP_PERSPECTIVE_ACTION.GPPA10_BINARY_PERSPECTIVE_DEFECT.
Check NSE_GP_PERSPECTIVE_ACTION.GPPA11_BINARY_FUSION_CONTRACTS_ACTION.
Check NSE_GP_PERSPECTIVE_ACTION.GPPA12_ZERO_DEFECT_FORCES_MATCH.
Check NSE_GP_PERSPECTIVE_ACTION.GPPA20_MATCHED_TWO_CHILD_ACTION_SUM.
Check NSE_GP_PERSPECTIVE_ACTION.GPPA21_THREE_FIFTHS_GIVES_NINE_TWENTY_FIFTHS.
Check NSE_GP_PERSPECTIVE_ACTION.GPPA22_SAME_DENOM_SELECTED_ACTION_GAP.
Check NSE_GP_PERSPECTIVE_ACTION.GPPA30_MATCHED_LINEAR_OBSERVABLE.
Check NSE_GP_PERSPECTIVE_ACTION.GPPA31_MATCHED_DEFECT_SCALES_WITH_ACTION.
