From Stdlib Require Import Reals Lra Psatz String.
Require Import awpi_nse_gp_matched_heat_renewal_v0_6_0.

Module NSE_GP_COMPACT_TRIAD_PROJECTION.

Open Scope R_scope.

(*
  Compact complete-triad matched-heat projection algebra.

  Physical interpretation for one complete three-leg Fourier/helical packet:

    w_i  : the unweighted energy-direction coordinate,
    c_i  : matched heat weight, with 3/4 <= c_i <= 1,
    x_i  : c_i * w_i,
    y_i  : allocated nonlinear source coordinate.

  Complete-triad energy conservation becomes
      sum_i y_i w_i = 0.

  The matched heat range gives a quantitative angle bound between x and w.
  Combining that angle bound with the Gram/projection identity forces
      49 <x,y>^2 <= ||x||^2 ||y||^2.

  Thus the resistant projection of a complete compact triad is at most 1/49
  of its source capacity.  No general Hilbert-space or Kantorovich theorem is
  assumed here; the three-dimensional real algebra is proved explicitly.
*)

Definition dot3
  (a1 a2 a3 b1 b2 b3 : R) : R :=
  a1 * b1 + a2 * b2 + a3 * b3.

Definition norm3sq (a1 a2 a3 : R) : R :=
  a1 * a1 + a2 * a2 + a3 * a3.

Definition triple3
  (x1 x2 x3 y1 y2 y3 w1 w2 w3 : R) : R :=
  x1 * (y2 * w3 - y3 * w2) -
  x2 * (y1 * w3 - y3 * w1) +
  x3 * (y1 * w2 - y2 * w1).

Section MATCHED_HEAT_ANGLE.

  Theorem NSCT01_ONE_LEG_MATCHED_HEAT_QUADRATIC :
    forall c w : R,
      3 <= 4 * c ->
      c <= 1 ->
      4 * (c * c * w * w) + 3 * (w * w) <=
      7 * (c * w * w).
  Proof.
    intros c w Hlow Hhigh.
    assert (H1 : 0 <= 1 - c) by lra.
    assert (H2 : 0 <= 4 * c - 3) by lra.
    assert (Hw : 0 <= w * w).
    { nra. }
    assert (Hprod : 0 <= ((1 - c) * (4 * c - 3)) * (w * w)).
    {
      apply Rmult_le_pos.
      - apply Rmult_le_pos; assumption.
      - exact Hw.
    }
    nra.
  Qed.

  Theorem NSCT02_THREE_LEG_MATCHED_HEAT_SUM :
    forall c1 c2 c3 w1 w2 w3 : R,
      3 <= 4 * c1 -> c1 <= 1 ->
      3 <= 4 * c2 -> c2 <= 1 ->
      3 <= 4 * c3 -> c3 <= 1 ->
      4 * norm3sq (c1*w1) (c2*w2) (c3*w3) +
      3 * norm3sq w1 w2 w3 <=
      7 * dot3 (c1*w1) (c2*w2) (c3*w3) w1 w2 w3.
  Proof.
    intros c1 c2 c3 w1 w2 w3
           H1l H1u H2l H2u H3l H3u.
    pose proof (NSCT01_ONE_LEG_MATCHED_HEAT_QUADRATIC c1 w1 H1l H1u) as H1.
    pose proof (NSCT01_ONE_LEG_MATCHED_HEAT_QUADRATIC c2 w2 H2l H2u) as H2.
    pose proof (NSCT01_ONE_LEG_MATCHED_HEAT_QUADRATIC c3 w3 H3l H3u) as H3.
    unfold norm3sq, dot3.
    nra.
  Qed.

  Theorem NSCT03_THREE_LEG_MATCHED_HEAT_CORRELATION_48_OVER_49 :
    forall c1 c2 c3 w1 w2 w3 : R,
      3 <= 4 * c1 -> c1 <= 1 ->
      3 <= 4 * c2 -> c2 <= 1 ->
      3 <= 4 * c3 -> c3 <= 1 ->
      48 *
        norm3sq (c1*w1) (c2*w2) (c3*w3) *
        norm3sq w1 w2 w3 <=
      49 *
        dot3 (c1*w1) (c2*w2) (c3*w3) w1 w2 w3 *
        dot3 (c1*w1) (c2*w2) (c3*w3) w1 w2 w3.
  Proof.
    intros c1 c2 c3 w1 w2 w3
           H1l H1u H2l H2u H3l H3u.
    pose proof
      (NSCT02_THREE_LEG_MATCHED_HEAT_SUM
         c1 c2 c3 w1 w2 w3
         H1l H1u H2l H2u H3l H3u) as Hsum.
    set (X2 := norm3sq (c1*w1) (c2*w2) (c3*w3)).
    set (W2 := norm3sq w1 w2 w3).
    set (XW := dot3 (c1*w1) (c2*w2) (c3*w3) w1 w2 w3).
    assert (HX2 : 0 <= X2).
    {
      unfold X2, norm3sq.
      nra.
    }
    assert (HW2 : 0 <= W2).
    {
      unfold W2, norm3sq.
      nra.
    }
    assert (Hc1 : 0 <= c1) by lra.
    assert (Hc2 : 0 <= c2) by lra.
    assert (Hc3 : 0 <= c3) by lra.
    assert (Hw1 : 0 <= w1*w1) by nra.
    assert (Hw2 : 0 <= w2*w2) by nra.
    assert (Hw3 : 0 <= w3*w3) by nra.
    assert (Hcw1 : 0 <= c1 * (w1*w1)).
    { apply Rmult_le_pos; assumption. }
    assert (Hcw2 : 0 <= c2 * (w2*w2)).
    { apply Rmult_le_pos; assumption. }
    assert (Hcw3 : 0 <= c3 * (w3*w3)).
    { apply Rmult_le_pos; assumption. }
    assert (HXW : 0 <= XW).
    {
      unfold XW, dot3.
      nra.
    }
    assert (Hminus : 0 <= Rsqr (4 * X2 - 3 * W2)).
    { apply Rle_0_sqr. }
    unfold Rsqr in Hminus.
    change (4 * X2 + 3 * W2 <= 7 * XW) in Hsum.
    assert (Hgap1 : 0 <= 7 * XW - (4 * X2 + 3 * W2)).
    { lra. }
    assert (Hgap2 : 0 <= 7 * XW + (4 * X2 + 3 * W2)) by nra.
    assert (Hsquare_order :
      0 <=
      (7 * XW - (4 * X2 + 3 * W2)) *
      (7 * XW + (4 * X2 + 3 * W2))).
    { apply Rmult_le_pos; assumption. }
    nra.
  Qed.

End MATCHED_HEAT_ANGLE.

Section THREE_DIMENSIONAL_PROJECTION.

  Theorem NSCT10_GRAM_DETERMINANT_IDENTITY :
    forall x1 x2 x3 y1 y2 y3 w1 w2 w3 : R,
      norm3sq x1 x2 x3 * norm3sq y1 y2 y3 * norm3sq w1 w2 w3 +
      2 * dot3 x1 x2 x3 y1 y2 y3 *
          dot3 x1 x2 x3 w1 w2 w3 *
          dot3 y1 y2 y3 w1 w2 w3 -
      norm3sq x1 x2 x3 *
          dot3 y1 y2 y3 w1 w2 w3 *
          dot3 y1 y2 y3 w1 w2 w3 -
      norm3sq y1 y2 y3 *
          dot3 x1 x2 x3 w1 w2 w3 *
          dot3 x1 x2 x3 w1 w2 w3 -
      norm3sq w1 w2 w3 *
          dot3 x1 x2 x3 y1 y2 y3 *
          dot3 x1 x2 x3 y1 y2 y3 =
      triple3 x1 x2 x3 y1 y2 y3 w1 w2 w3 *
      triple3 x1 x2 x3 y1 y2 y3 w1 w2 w3.
  Proof.
    intros x1 x2 x3 y1 y2 y3 w1 w2 w3.
    unfold norm3sq, dot3, triple3.
    ring.
  Qed.

  Theorem NSCT11_ORTHOGONAL_SOURCE_PROJECTION_BOUND :
    forall x1 x2 x3 y1 y2 y3 w1 w2 w3 : R,
      dot3 y1 y2 y3 w1 w2 w3 = 0 ->
      dot3 x1 x2 x3 y1 y2 y3 *
      dot3 x1 x2 x3 y1 y2 y3 *
      norm3sq w1 w2 w3 <=
      norm3sq y1 y2 y3 *
      (norm3sq x1 x2 x3 * norm3sq w1 w2 w3 -
       dot3 x1 x2 x3 w1 w2 w3 *
       dot3 x1 x2 x3 w1 w2 w3).
  Proof.
    intros x1 x2 x3 y1 y2 y3 w1 w2 w3 Horth.
    pose proof
      (NSCT10_GRAM_DETERMINANT_IDENTITY
         x1 x2 x3 y1 y2 y3 w1 w2 w3) as Hgram.
    rewrite Horth in Hgram.
    assert (Hsq :
      0 <=
      triple3 x1 x2 x3 y1 y2 y3 w1 w2 w3 *
      triple3 x1 x2 x3 y1 y2 y3 w1 w2 w3).
    { nra. }
    nra.
  Qed.

  Theorem NSCT12_CORRELATION_PLUS_PROJECTION_GIVES_ONE_OVER_49 :
    forall X2 W2 Y2 XW XY : R,
      0 < W2 ->
      0 <= Y2 ->
      48 * X2 * W2 <= 49 * XW * XW ->
      XY * XY * W2 <= Y2 * (X2 * W2 - XW * XW) ->
      49 * XY * XY <= X2 * Y2.
  Proof.
    intros X2 W2 Y2 XW XY HW2 HY2 Hcorr Hproj.
    assert (HcorrY :
      48 * X2 * W2 * Y2 <= 49 * XW * XW * Y2).
    {
      apply Rmult_le_compat_r.
      - exact HY2.
      - exact Hcorr.
    }
    assert (Htimes :
      (49 * XY * XY) * W2 <= (X2 * Y2) * W2).
    {
      nra.
    }
    destruct (Rle_dec (49 * XY * XY) (X2 * Y2)) as [Hdone | Hbad].
    - exact Hdone.
    - assert (Hdiff : 0 < 49 * XY * XY - X2 * Y2) by lra.
      assert (Hposprod :
        0 < (49 * XY * XY - X2 * Y2) * W2).
      {
        apply Rmult_lt_0_compat; assumption.
      }
      nra.
  Qed.

End THREE_DIMENSIONAL_PROJECTION.

Section COMPACT_TRIAD_GAP.

  Theorem NSCT20_COMPLETE_COMPACT_TRIAD_ONE_OVER_49_GAP :
    forall c1 c2 c3 w1 w2 w3 y1 y2 y3 : R,
      3 <= 4 * c1 -> c1 <= 1 ->
      3 <= 4 * c2 -> c2 <= 1 ->
      3 <= 4 * c3 -> c3 <= 1 ->
      0 < norm3sq w1 w2 w3 ->
      dot3 y1 y2 y3 w1 w2 w3 = 0 ->
      49 *
        dot3 (c1*w1) (c2*w2) (c3*w3) y1 y2 y3 *
        dot3 (c1*w1) (c2*w2) (c3*w3) y1 y2 y3 <=
      norm3sq (c1*w1) (c2*w2) (c3*w3) *
      norm3sq y1 y2 y3.
  Proof.
    intros c1 c2 c3 w1 w2 w3 y1 y2 y3
           H1l H1u H2l H2u H3l H3u HWpos Horth.
    pose proof
      (NSCT03_THREE_LEG_MATCHED_HEAT_CORRELATION_48_OVER_49
         c1 c2 c3 w1 w2 w3
         H1l H1u H2l H2u H3l H3u) as Hcorr.
    pose proof
      (NSCT11_ORTHOGONAL_SOURCE_PROJECTION_BOUND
         (c1*w1) (c2*w2) (c3*w3)
         y1 y2 y3 w1 w2 w3 Horth) as Hproj.
    assert (HY2 : 0 <= norm3sq y1 y2 y3).
    { unfold norm3sq; nra. }
    eapply NSCT12_CORRELATION_PLUS_PROJECTION_GIVES_ONE_OVER_49.
    - exact HWpos.
    - exact HY2.
    - exact Hcorr.
    - exact Hproj.
  Qed.

  Theorem NSCT21_CROSS_MULTIPLIED_GAP_GIVES_INTERNAL_ACTION_RATIO :
    forall X2 Y2 XY internal : R,
      0 < X2 ->
      0 <= internal ->
      X2 * internal = XY * XY ->
      49 * XY * XY <= X2 * Y2 ->
      49 * internal <= Y2.
  Proof.
    intros X2 Y2 XY internal HX2 Hint Hdef Hgap.
    assert (Htimes :
      X2 * (49 * internal) <= X2 * Y2).
    {
      nra.
    }
    destruct (Rle_dec (49 * internal) Y2) as [Hdone | Hbad].
    - exact Hdone.
    - assert (Hdiff : 0 < 49 * internal - Y2) by lra.
      assert (Hposprod : 0 < X2 * (49 * internal - Y2)).
      { apply Rmult_lt_0_compat; assumption. }
      nra.
  Qed.

  (*
    Stronger renewal available when the routed boundary is the exact
    orthogonal residual: parent = internal + boundary.
  *)
  Theorem NSCT22_ORTHOGONAL_RESIDUAL_PLUS_DT_GIVES_13_OVER_49 :
    forall parent internal boundary uv child paid : R,
      0 <= parent ->
      0 <= internal ->
      0 <= boundary ->
      0 <= uv ->
      0 <= child ->
      0 <= paid ->
      parent = internal + boundary ->
      49 * internal <= parent ->
      4 * uv <= boundary ->
      child <= internal + uv + paid ->
      49 * child <= 13 * parent + 49 * paid.
  Proof.
    intros parent internal boundary uv child paid
           Hp Hi Hb Huv Hchild Hpaid Hsplit Hint Hdt Hchildsplit.
    nra.
  Qed.

End COMPACT_TRIAD_GAP.

Section ABSTRACT_PHYSICAL_FRONTIER.

  Context {Velocity : Type}.

  Variable LerayHopfT3 : Velocity -> Prop.
  Variable CompleteTriadMatchedProjectionCertificate : Velocity -> Prop.
  Variable OrthogonalResidualDTRoutingCertificate : Velocity -> Prop.
  Variable UniformPaidInjectionBudget : Velocity -> Prop.
  Variable ActualGPM7 : Velocity -> Prop.

  Definition CompactTriadProjectionToGPM7Principle : Prop :=
    forall u : Velocity,
      LerayHopfT3 u ->
      CompleteTriadMatchedProjectionCertificate u ->
      OrthogonalResidualDTRoutingCertificate u ->
      UniformPaidInjectionBudget u ->
      ActualGPM7 u.

  Theorem NSCT90_COMPACT_TRIAD_PROJECTION_REDUCES_PHYSICAL_FRONTIER :
    CompactTriadProjectionToGPM7Principle ->
    forall u : Velocity,
      LerayHopfT3 u ->
      CompleteTriadMatchedProjectionCertificate u ->
      OrthogonalResidualDTRoutingCertificate u ->
      UniformPaidInjectionBudget u ->
      ActualGPM7 u.
  Proof.
    intros H u Hlh Hproj Hroute Hpaid.
    exact (H u Hlh Hproj Hroute Hpaid).
  Qed.

End ABSTRACT_PHYSICAL_FRONTIER.

Definition STATUS : string :=
  "NSE_GP_COMPLETE_COMPACT_TRIAD_MATCHED_PROJECTION_ONE_OVER_49_NO_ADMITTED"%string.

End NSE_GP_COMPACT_TRIAD_PROJECTION.

Print Assumptions NSE_GP_COMPACT_TRIAD_PROJECTION.NSCT03_THREE_LEG_MATCHED_HEAT_CORRELATION_48_OVER_49.
Print Assumptions NSE_GP_COMPACT_TRIAD_PROJECTION.NSCT20_COMPLETE_COMPACT_TRIAD_ONE_OVER_49_GAP.
Print Assumptions NSE_GP_COMPACT_TRIAD_PROJECTION.NSCT22_ORTHOGONAL_RESIDUAL_PLUS_DT_GIVES_13_OVER_49.
