From Stdlib Require Import Reals Lra Psatz String.
Require Import awpi_nse_gp_compact_triad_projection_v0_7_1.

Module NSE_GP_QUARTER_SHIFT_FIREWALL.

Open Scope R_scope.

(*
  Finite-shift GP firewall.

  Interpretation:
    - c is the matched-heat coefficient, 3/4 <= c <= 1;
    - s is the effective DT quarter-shift multiplier, 1 <= s <= 2;
    - q = s*c is the critical-line effective coefficient, hence 3/4 <= q <= 2;
    - x_i = q_i w_i and the source y stays orthogonal to the oppositely
      transformed annihilator w.

  The critical projection estimate is proved with rational polynomial
  inequalities only: no logarithms, roots, or transcendental bounds.
*)

Definition dot3 := NSE_GP_COMPACT_TRIAD_PROJECTION.dot3.
Definition norm3sq := NSE_GP_COMPACT_TRIAD_PROJECTION.norm3sq.

Section QUARTER_SHIFT_WEIGHT_BOUNDS.

  Theorem NSQF01_MATCHED_HEAT_TIMES_QUARTER_SHIFT_STAYS_IN_CRITICAL_RANGE :
    forall c s q : R,
      3 <= 4 * c ->
      c <= 1 ->
      1 <= s ->
      s <= 2 ->
      q = s * c ->
      3 <= 4 * q /\ q <= 2.
  Proof.
    intros c s q Hcl Hcu Hsl Hsu Hq.
    subst q.
    split; nra.
  Qed.

  Theorem NSQF02_ONE_LEG_CRITICAL_QUADRATIC :
    forall q : R,
      3 <= 4 * q ->
      q <= 2 ->
      4 * q * q + 6 <= 11 * q.
  Proof.
    intros q Hlo Hhi.
    assert (Hprod : 0 <= (q - (3/4)) * (2 - q)).
    { apply Rmult_le_pos; nra. }
    nra.
  Qed.

  Theorem NSQF03_THREE_LEG_CRITICAL_HEAT_SUM :
    forall q1 q2 q3 w1 w2 w3 : R,
      3 <= 4 * q1 -> q1 <= 2 ->
      3 <= 4 * q2 -> q2 <= 2 ->
      3 <= 4 * q3 -> q3 <= 2 ->
      4 * norm3sq (q1*w1) (q2*w2) (q3*w3) +
      6 * norm3sq w1 w2 w3 <=
      11 * dot3 (q1*w1) (q2*w2) (q3*w3) w1 w2 w3.
  Proof.
    intros q1 q2 q3 w1 w2 w3
           H1l H1u H2l H2u H3l H3u.
    pose proof (NSQF02_ONE_LEG_CRITICAL_QUADRATIC q1 H1l H1u) as H1.
    pose proof (NSQF02_ONE_LEG_CRITICAL_QUADRATIC q2 H2l H2u) as H2.
    pose proof (NSQF02_ONE_LEG_CRITICAL_QUADRATIC q3 H3l H3u) as H3.
    assert (Hw1 : 0 <= w1 * w1) by nra.
    assert (Hw2 : 0 <= w2 * w2) by nra.
    assert (Hw3 : 0 <= w3 * w3) by nra.
    assert (H1w :
      (4 * q1 * q1 + 6) * (w1 * w1) <=
      (11 * q1) * (w1 * w1)).
    { apply Rmult_le_compat_r; assumption. }
    assert (H2w :
      (4 * q2 * q2 + 6) * (w2 * w2) <=
      (11 * q2) * (w2 * w2)).
    { apply Rmult_le_compat_r; assumption. }
    assert (H3w :
      (4 * q3 * q3 + 6) * (w3 * w3) <=
      (11 * q3) * (w3 * w3)).
    { apply Rmult_le_compat_r; assumption. }
    assert (Hleft :
      4 * norm3sq (q1*w1) (q2*w2) (q3*w3) +
      6 * norm3sq w1 w2 w3 =
      (4 * q1 * q1 + 6) * (w1 * w1) +
      (4 * q2 * q2 + 6) * (w2 * w2) +
      (4 * q3 * q3 + 6) * (w3 * w3)).
    { cbv [norm3sq NSE_GP_COMPACT_TRIAD_PROJECTION.norm3sq]; ring. }
    assert (Hright :
      11 * dot3 (q1*w1) (q2*w2) (q3*w3) w1 w2 w3 =
      (11 * q1) * (w1 * w1) +
      (11 * q2) * (w2 * w2) +
      (11 * q3) * (w3 * w3)).
    { cbv [dot3 NSE_GP_COMPACT_TRIAD_PROJECTION.dot3]; ring. }
    rewrite Hleft, Hright.
    lra.
  Qed.

  Theorem NSQF04_CRITICAL_CORRELATION_96_OVER_121 :
    forall q1 q2 q3 w1 w2 w3 : R,
      3 <= 4 * q1 -> q1 <= 2 ->
      3 <= 4 * q2 -> q2 <= 2 ->
      3 <= 4 * q3 -> q3 <= 2 ->
      96 *
        norm3sq (q1*w1) (q2*w2) (q3*w3) *
        norm3sq w1 w2 w3 <=
      121 *
        dot3 (q1*w1) (q2*w2) (q3*w3) w1 w2 w3 *
        dot3 (q1*w1) (q2*w2) (q3*w3) w1 w2 w3.
  Proof.
    intros q1 q2 q3 w1 w2 w3
           H1l H1u H2l H2u H3l H3u.
    pose proof
      (NSQF03_THREE_LEG_CRITICAL_HEAT_SUM
         q1 q2 q3 w1 w2 w3 H1l H1u H2l H2u H3l H3u) as Hsum.
    set (X2 := norm3sq (q1*w1) (q2*w2) (q3*w3)).
    set (W2 := norm3sq w1 w2 w3).
    set (XW := dot3 (q1*w1) (q2*w2) (q3*w3) w1 w2 w3).
    change (4 * X2 + 6 * W2 <= 11 * XW) in Hsum.
    assert (HX2 : 0 <= X2).
    {
      unfold X2.
      pose proof (Rle_0_sqr (q1*w1)) as Hx1.
      pose proof (Rle_0_sqr (q2*w2)) as Hx2.
      pose proof (Rle_0_sqr (q3*w3)) as Hx3.
      unfold Rsqr in Hx1, Hx2, Hx3.
      cbv [norm3sq NSE_GP_COMPACT_TRIAD_PROJECTION.norm3sq].
      nra.
    }
    assert (HW2 : 0 <= W2).
    {
      unfold W2.
      pose proof (Rle_0_sqr w1) as Hw1.
      pose proof (Rle_0_sqr w2) as Hw2.
      pose proof (Rle_0_sqr w3) as Hw3.
      unfold Rsqr in Hw1, Hw2, Hw3.
      cbv [norm3sq NSE_GP_COMPACT_TRIAD_PROJECTION.norm3sq].
      nra.
    }
    assert (Hlhs : 0 <= 4 * X2 + 6 * W2) by nra.
    assert (HXW : 0 <= XW) by nra.
    assert (Hd : 0 <= 11 * XW - (4 * X2 + 6 * W2)) by lra.
    assert (Hs : 0 <= 11 * XW + (4 * X2 + 6 * W2)) by nra.
    pose proof (Rmult_le_pos _ _ Hd Hs) as Hprod.
    assert (Hsquare :
      (4 * X2 + 6 * W2) * (4 * X2 + 6 * W2) <=
      121 * XW * XW).
    { nra. }
    assert (Hsq : 0 <= Rsqr (4 * X2 - 6 * W2)).
    { apply Rle_0_sqr. }
    unfold Rsqr in Hsq.
    assert (Hcross :
      96 * X2 * W2 <=
      (4 * X2 + 6 * W2) * (4 * X2 + 6 * W2)).
    { nra. }
    nra.
  Qed.

End QUARTER_SHIFT_WEIGHT_BOUNDS.

Section CRITICAL_PROJECTION.

  Theorem NSQF10_CORRELATION_PLUS_ORTHOGONAL_PROJECTION_GIVES_25_OVER_121 :
    forall X2 W2 Y2 XW XY : R,
      0 < W2 ->
      0 <= Y2 ->
      96 * X2 * W2 <= 121 * XW * XW ->
      XY * XY * W2 <= Y2 * (X2 * W2 - XW * XW) ->
      121 * XY * XY <= 25 * X2 * Y2.
  Proof.
    intros X2 W2 Y2 XW XY HW2 HY2 Hcorr Hproj.
    assert (HcorrY :
      96 * X2 * W2 * Y2 <= 121 * XW * XW * Y2).
    {
      apply Rmult_le_compat_r.
      - exact HY2.
      - exact Hcorr.
    }
    assert (Htimes :
      (121 * XY * XY) * W2 <= (25 * X2 * Y2) * W2).
    {
      nra.
    }
    destruct (Rle_dec (121 * XY * XY) (25 * X2 * Y2)) as [Hdone | Hbad].
    - exact Hdone.
    - assert (Hdiff : 0 < 121 * XY * XY - 25 * X2 * Y2) by lra.
      assert (Hposprod :
        0 < (121 * XY * XY - 25 * X2 * Y2) * W2).
      {
        apply Rmult_lt_0_compat; assumption.
      }
      nra.
  Qed.

  Theorem NSQF11_COMPLETE_CRITICAL_TRIAD_25_OVER_121_GAP :
    forall q1 q2 q3 w1 w2 w3 y1 y2 y3 : R,
      3 <= 4 * q1 -> q1 <= 2 ->
      3 <= 4 * q2 -> q2 <= 2 ->
      3 <= 4 * q3 -> q3 <= 2 ->
      0 < norm3sq w1 w2 w3 ->
      dot3 y1 y2 y3 w1 w2 w3 = 0 ->
      121 *
        dot3 (q1*w1) (q2*w2) (q3*w3) y1 y2 y3 *
        dot3 (q1*w1) (q2*w2) (q3*w3) y1 y2 y3 <=
      25 *
        norm3sq (q1*w1) (q2*w2) (q3*w3) *
        norm3sq y1 y2 y3.
  Proof.
    intros q1 q2 q3 w1 w2 w3 y1 y2 y3
           H1l H1u H2l H2u H3l H3u HWpos Horth.
    pose proof
      (NSQF04_CRITICAL_CORRELATION_96_OVER_121
         q1 q2 q3 w1 w2 w3 H1l H1u H2l H2u H3l H3u) as Hcorr.
    pose proof
      (NSE_GP_COMPACT_TRIAD_PROJECTION.NSCT11_ORTHOGONAL_SOURCE_PROJECTION_BOUND
         (q1*w1) (q2*w2) (q3*w3)
         y1 y2 y3 w1 w2 w3 Horth) as Hproj.
    assert (HY2 : 0 <= norm3sq y1 y2 y3).
    { cbv [norm3sq NSE_GP_COMPACT_TRIAD_PROJECTION.norm3sq]; nra. }
    eapply NSQF10_CORRELATION_PLUS_ORTHOGONAL_PROJECTION_GIVES_25_OVER_121.
    - exact HWpos.
    - exact HY2.
    - exact Hcorr.
    - exact Hproj.
  Qed.

  Theorem NSQF12_CROSS_MULTIPLIED_GAP_GIVES_CRITICAL_INTERNAL_RATIO :
    forall X2 Y2 XY internal : R,
      0 < X2 ->
      0 <= internal ->
      X2 * internal = XY * XY ->
      121 * XY * XY <= 25 * X2 * Y2 ->
      121 * internal <= 25 * Y2.
  Proof.
    intros X2 Y2 XY internal HX2 Hint Hdef Hgap.
    assert (Htimes :
      X2 * (121 * internal) <= X2 * (25 * Y2)).
    {
      nra.
    }
    destruct (Rle_dec (121 * internal) (25 * Y2)) as [Hdone | Hbad].
    - exact Hdone.
    - assert (Hdiff : 0 < 121 * internal - 25 * Y2) by lra.
      assert (Hposprod : 0 < X2 * (121 * internal - 25 * Y2)).
      { apply Rmult_lt_0_compat; assumption. }
      nra.
  Qed.

End CRITICAL_PROJECTION.

Section CRITICAL_RENEWAL.

  Theorem NSQF20_CRITICAL_COMPACT_PLUS_HELICITY_UV_GIVES_509_OVER_605 :
    forall parent internal boundary uv child paid : R,
      0 <= parent ->
      0 <= internal ->
      0 <= boundary ->
      0 <= uv ->
      0 <= child ->
      0 <= paid ->
      parent = internal + boundary ->
      121 * internal <= 25 * parent ->
      5 * uv <= 4 * boundary ->
      child <= internal + uv + paid ->
      605 * child <= 509 * parent + 605 * paid.
  Proof.
    intros parent internal boundary uv child paid
           Hp Hi Hb Huv Hc Hpaid Hsplit Hint Huvgap Hchild.
    nra.
  Qed.

  Theorem NSQF21_ZERO_PAID_GIVES_STRICT_CRITICAL_RENEWAL :
    forall parent internal boundary uv child : R,
      0 < parent ->
      0 <= internal ->
      0 <= boundary ->
      0 <= uv ->
      0 <= child ->
      parent = internal + boundary ->
      121 * internal <= 25 * parent ->
      5 * uv <= 4 * boundary ->
      child <= internal + uv ->
      child < parent.
  Proof.
    intros parent internal boundary uv child
           Hp Hi Hb Huv Hc Hsplit Hint Huvgap Hchild.
    assert (Hrenew : 605 * child <= 509 * parent).
    {
      nra.
    }
    nra.
  Qed.

  Theorem NSQF22_EXPLICIT_CRITICAL_GAP_96_OVER_605 :
    forall parent child paid : R,
      0 <= parent ->
      0 <= child ->
      0 <= paid ->
      605 * child <= 509 * parent + 605 * paid ->
      96 * parent <= 605 * (parent - child + paid).
  Proof.
    intros parent child paid Hp Hc Hpaid Hrenew.
    nra.
  Qed.

End CRITICAL_RENEWAL.

Section PREFIX_CONTRACTION.

  Fixpoint resistant_prefix (mass : nat -> R) (N : nat) : R :=
    match N with
    | O => 0
    | S n => resistant_prefix mass n + mass n
    end.

  Fixpoint paid_prefix (paid : nat -> R) (N : nat) : R :=
    match N with
    | O => 0
    | S n => paid_prefix paid n + paid n
    end.

  Theorem NSQF30_EXACT_509_OVER_605_PREFIX_INVARIANT :
    forall mass paid : nat -> R,
      (forall n, 0 <= mass n) ->
      (forall n, 0 <= paid n) ->
      (forall n, 605 * mass (S n) <= 509 * mass n + 605 * paid n) ->
      forall N,
        96 * resistant_prefix mass N + 605 * mass N <=
        605 * mass O + 605 * paid_prefix paid N.
  Proof.
    intros mass paid Hmass Hpaid Hstep N.
    induction N as [|N IHN].
    - simpl. nra.
    - simpl.
      specialize (Hstep N).
      nra.
  Qed.

  Theorem NSQF31_UNIFORM_PAID_PREFIX_GIVES_CRITICAL_PREFIX_BOUND :
    forall mass paid : nat -> R,
      (forall n, 0 <= mass n) ->
      (forall n, 0 <= paid n) ->
      (forall n, 605 * mass (S n) <= 509 * mass n + 605 * paid n) ->
      forall N Pmax,
        paid_prefix paid N <= Pmax ->
        96 * resistant_prefix mass N <=
        605 * mass O + 605 * Pmax.
  Proof.
    intros mass paid Hmass Hpaid Hstep N Pmax Hbudget.
    pose proof
      (NSQF30_EXACT_509_OVER_605_PREFIX_INVARIANT
         mass paid Hmass Hpaid Hstep N) as Hinv.
    specialize (Hmass N).
    nra.
  Qed.

End PREFIX_CONTRACTION.

Section ABSTRACT_FRONTIER.

  Context {Velocity : Type}.

  Variable LerayHopfT3 : Velocity -> Prop.
  Variable QuarterShiftCriticalProjection : Velocity -> Prop.
  Variable HelicityCriticalOctaveRetention : Velocity -> Prop.
  Variable RestartLocalPhysicalSourceRealization : Velocity -> Prop.
  Variable ActualGPM7 : Velocity -> Prop.

  Definition QuarterShiftFirewallToGPM7Principle : Prop :=
    forall u : Velocity,
      LerayHopfT3 u ->
      QuarterShiftCriticalProjection u ->
      HelicityCriticalOctaveRetention u ->
      RestartLocalPhysicalSourceRealization u ->
      ActualGPM7 u.

  Theorem NSQF90_QUARTER_SHIFT_FIREWALL_REDUCES_TO_PHYSICAL_REALIZATION :
    QuarterShiftFirewallToGPM7Principle ->
    forall u : Velocity,
      LerayHopfT3 u ->
      QuarterShiftCriticalProjection u ->
      HelicityCriticalOctaveRetention u ->
      RestartLocalPhysicalSourceRealization u ->
      ActualGPM7 u.
  Proof.
    intros H u Hlh Hproj Hhel Hphys.
    exact (H u Hlh Hproj Hhel Hphys).
  Qed.

End ABSTRACT_FRONTIER.

Definition STATUS : string :=
  "NSE_GP_QUARTER_SHIFT_CRITICAL_FIREWALL_509_OVER_605_NO_ADMITTED"%string.

End NSE_GP_QUARTER_SHIFT_FIREWALL.
