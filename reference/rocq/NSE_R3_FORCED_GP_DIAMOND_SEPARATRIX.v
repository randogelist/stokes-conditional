From Stdlib Require Import Reals Lra Psatz String.
Require Import NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.

Module NSE_R3_FORCED_GP_DIAMOND_SEPARATRIX.

Open Scope R_scope.

(*
  Exact critical separatrix at the scalar Diamond level.

  positive_work = cumulative positive critical injection,
  loss_work     = cumulative critical loss (viscosity plus adverse work).

  The exact identity is
      mass = initial_mass + 2 * (positive_work - loss_work).

  Hence bounded mass with arbitrarily large turnover forces the relative
  injection/loss defect toward zero.  A fixed subcritical gap cannot support
  unbounded turnover, while a fixed supercritical gap with unbounded turnover
  forces critical mass to be unbounded.
*)

Section SEPARATRIX.

Variable Time : Type.
Variable initial_mass : R.
Variable critical_mass positive_work loss_work : Time -> R.

Record ExactCriticalTurnoverBalance : Prop := {
  ectb_initial_nonneg : 0 <= initial_mass;
  ectb_mass_nonneg : forall t : Time, 0 <= critical_mass t;
  ectb_positive_nonneg : forall t : Time, 0 <= positive_work t;
  ectb_loss_nonneg : forall t : Time, 0 <= loss_work t;
  ectb_exact : forall t : Time,
    critical_mass t =
      initial_mass + 2 * (positive_work t - loss_work t)
}.

Definition CriticalMassBoundedBy (Mmax : R) : Prop :=
  0 <= Mmax /\ forall t : Time, critical_mass t <= Mmax.

Definition CriticalMassUnbounded : Prop :=
  forall M : R, exists t : Time, M < critical_mass t.

Definition UniformSubcriticalGap (delta : R) : Prop :=
  forall t : Time,
    positive_work t <= (1 - delta) * loss_work t.

Definition UniformSupercriticalGap (delta : R) : Prop :=
  forall t : Time,
    (1 + delta) * loss_work t <= positive_work t.

Definition ScaledLossUnbounded (delta : R) : Prop :=
  forall M : R,
    exists t : Time, M < 2 * delta * loss_work t.

Theorem SEP01_BOUNDED_MASS_TRAPS_CUMULATIVE_DEFECT :
  forall Mmax : R,
    ExactCriticalTurnoverBalance ->
    CriticalMassBoundedBy Mmax ->
    forall t : Time,
      - initial_mass <= 2 * (positive_work t - loss_work t) /\
      2 * (positive_work t - loss_work t) <= Mmax - initial_mass.
Proof.
  intros Mmax Hbal [HM0 HM] t.
  destruct Hbal as [Hi Hm Hp Hl Hex].
  specialize (Hm t).
  specialize (HM t).
  specialize (Hex t).
  split; lra.
Qed.

Theorem SEP02_BOUNDED_MASS_GIVES_QUANTITATIVE_SEPARATRIX_BAND :
  forall Mmax eps : R,
    ExactCriticalTurnoverBalance ->
    CriticalMassBoundedBy Mmax ->
    0 <= eps ->
    forall t : Time,
      Mmax + initial_mass <= 2 * eps * loss_work t ->
      - eps * loss_work t <= positive_work t - loss_work t /\
      positive_work t - loss_work t <= eps * loss_work t.
Proof.
  intros Mmax eps Hbal HMb Heps t Hlarge.
  destruct HMb as [HM0 HM].
  assert (Hbounds := SEP01_BOUNDED_MASS_TRAPS_CUMULATIVE_DEFECT
    Mmax Hbal (conj HM0 HM) t).
  destruct Hbal as [Hi Hm Hp Hl Hex].
  destruct Hbounds as [Hlo Hhi].
  specialize (Hl t).
  split; nra.
Qed.

Theorem SEP03_FIXED_SUBCRITICAL_GAP_BOUNDS_TURNOVER :
  forall delta : R,
    ExactCriticalTurnoverBalance ->
    0 < delta ->
    UniformSubcriticalGap delta ->
    forall t : Time,
      2 * delta * loss_work t <= initial_mass.
Proof.
  intros delta Hbal Hd Hsub t.
  destruct Hbal as [Hi Hm Hp Hl Hex].
  specialize (Hm t).
  specialize (Hsub t).
  specialize (Hex t).
  nra.
Qed.

Theorem SEP04_FIXED_SUPERCRITICAL_GAP_FORCES_MASS_GROWTH :
  forall delta : R,
    ExactCriticalTurnoverBalance ->
    0 < delta ->
    UniformSupercriticalGap delta ->
    forall t : Time,
      initial_mass + 2 * delta * loss_work t <= critical_mass t.
Proof.
  intros delta Hbal Hd Hsuper t.
  destruct Hbal as [Hi Hm Hp Hl Hex].
  specialize (Hsuper t).
  specialize (Hex t).
  nra.
Qed.

Theorem SEP05_SUPERCRITICAL_UNBOUNDED_TURNOVER_GIVES_BREAKDOWN :
  forall delta : R,
    ExactCriticalTurnoverBalance ->
    0 < delta ->
    UniformSupercriticalGap delta ->
    ScaledLossUnbounded delta ->
    CriticalMassUnbounded.
Proof.
  intros delta Hbal Hd Hsuper Hloss M.
  destruct (Hloss (M - initial_mass)) as [t Ht].
  exists t.
  assert (Hgrowth := SEP04_FIXED_SUPERCRITICAL_GAP_FORCES_MASS_GROWTH
    delta Hbal Hd Hsuper t).
  lra.
Qed.

Theorem SEP06_BOUNDED_MASS_EXCLUDES_SUPERCRITICAL_UNBOUNDED_TURNOVER :
  forall Mmax delta : R,
    ExactCriticalTurnoverBalance ->
    CriticalMassBoundedBy Mmax ->
    0 < delta ->
    UniformSupercriticalGap delta ->
    ScaledLossUnbounded delta ->
    False.
Proof.
  intros Mmax delta Hbal [HM0 HM] Hd Hsuper Hloss.
  pose proof (SEP05_SUPERCRITICAL_UNBOUNDED_TURNOVER_GIVES_BREAKDOWN
    delta Hbal Hd Hsuper Hloss) as Hunb.
  destruct (Hunb Mmax) as [t Ht].
  specialize (HM t).
  lra.
Qed.

Theorem SEP07_SUBCRITICAL_UNBOUNDED_TURNOVER_IMPOSSIBLE :
  forall delta : R,
    ExactCriticalTurnoverBalance ->
    0 < delta ->
    UniformSubcriticalGap delta ->
    ScaledLossUnbounded delta ->
    False.
Proof.
  intros delta Hbal Hd Hsub Hloss.
  destruct (Hloss initial_mass) as [t Ht].
  pose proof (SEP03_FIXED_SUBCRITICAL_GAP_BOUNDS_TURNOVER
    delta Hbal Hd Hsub t) as Hbound.
  lra.
Qed.

Theorem SEP08_BOUNDED_HIGH_TURNOVER_FORCES_SEPARATRIX :
  forall Mmax delta : R,
    ExactCriticalTurnoverBalance ->
    CriticalMassBoundedBy Mmax ->
    0 < delta ->
    ScaledLossUnbounded delta ->
    ~ UniformSubcriticalGap delta /\
    ~ UniformSupercriticalGap delta.
Proof.
  intros Mmax delta Hbal HMb Hd Hloss.
  split.
  - intro Hsub.
    eapply SEP07_SUBCRITICAL_UNBOUNDED_TURNOVER_IMPOSSIBLE;
      eauto.
  - intro Hsuper.
    eapply SEP06_BOUNDED_MASS_EXCLUDES_SUPERCRITICAL_UNBOUNDED_TURNOVER
      with (Mmax := Mmax) (delta := delta);
      eauto.
Qed.

End SEPARATRIX.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_SEPARATRIX_V0_10_0"%string.

End NSE_R3_FORCED_GP_DIAMOND_SEPARATRIX.
