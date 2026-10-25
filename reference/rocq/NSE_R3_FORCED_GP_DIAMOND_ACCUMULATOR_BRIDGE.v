From Stdlib Require Import Reals Lra Psatz String FunctionalExtensionality.
Require Import NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.
Require Import NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.
Require Import NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.

Module FA := NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.
Module IFC := NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.
Module SD := NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.NSE_R3_FORCED_GP_DIAMOND_STOKES_DUALITY.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.

Open Scope R_scope.

(* A generic positive linear prefix accumulator.  This abstracts exactly the
   integration step needed to pass from pointwise Stokes/Young absorption to
   the already kernel-checked accumulated forced Diamond. *)
Section POSITIVE_LINEAR_ACCUMULATOR.

Variable Time : Type.
Variable accumulate_until : Time -> (Time -> R) -> R.

Record PositiveLinearAccumulator : Prop := {
  pla_monotone :
    forall (t : Time) (a b : Time -> R),
      (forall s : Time, a s <= b s) ->
      accumulate_until t a <= accumulate_until t b;
  pla_add :
    forall (t : Time) (a b : Time -> R),
      accumulate_until t (fun s => a s + b s) =
      accumulate_until t a + accumulate_until t b;
  pla_scale_nonnegative :
    forall (t : Time) (c : R) (a : Time -> R),
      0 <= c ->
      accumulate_until t (fun s => c * a s) =
      c * accumulate_until t a;
  pla_zero :
    forall t : Time,
      accumulate_until t (fun _ => 0) = 0
}.

Variable nu sigma theta : R.
Variable instantaneous_work instantaneous_dissipation instantaneous_force_size : Time -> R.

Definition accumulated_force_work (t : Time) : R :=
  accumulate_until t instantaneous_work.

Definition accumulated_critical_dissipation (t : Time) : R :=
  accumulate_until t instantaneous_dissipation.

Definition accumulated_intrinsic_force_size (t : Time) : R :=
  accumulate_until t instantaneous_force_size.

Definition PointwiseNormalizedStokesAbsorption : Prop :=
  forall s : Time,
    2 * instantaneous_work s <=
    theta * CE.effective_viscosity nu sigma * instantaneous_dissipation s +
    instantaneous_force_size s /
      (theta * CE.effective_viscosity nu sigma).

Theorem AB00_POINTWISE_ABSORPTION_ACCUMULATES :
  PositiveLinearAccumulator ->
  0 < nu ->
  0 <= sigma -> sigma < 1 ->
  0 < theta -> theta < 1 ->
  (forall s : Time, 0 <= instantaneous_force_size s) ->
  PointwiseNormalizedStokesAbsorption ->
  @FA.AccumulatedIntrinsicForceAbsorption
    Time nu sigma theta
    accumulated_critical_dissipation accumulated_force_work
    accumulated_intrinsic_force_size.
Proof.
  intros Hacc Hnu Hs0 Hs1 Ht0 Ht1 Hsize Hpoint.
  destruct Hacc as [Hmono Hadd Hscale Hzero].
  assert (He : 0 < CE.effective_viscosity nu sigma).
  {
    unfold CE.effective_viscosity.
    nra.
  }
  assert (Ha : 0 < theta * CE.effective_viscosity nu sigma) by nra.
  constructor.
  - exact Ht0.
  - exact Ht1.
  - intro t.
    unfold accumulated_intrinsic_force_size.
    pose proof
      (Hmono t (fun _ : Time => 0) instantaneous_force_size
        (fun s => Hsize s)) as Hm.
    rewrite Hzero in Hm.
    exact Hm.
  - intro t.
    unfold accumulated_force_work,
      accumulated_critical_dissipation,
      accumulated_intrinsic_force_size.
    pose proof
      (Hmono t
        (fun s => 2 * instantaneous_work s)
        (fun s =>
          theta * CE.effective_viscosity nu sigma * instantaneous_dissipation s +
          instantaneous_force_size s /
            (theta * CE.effective_viscosity nu sigma))
        Hpoint) as Hm.
    rewrite (Hscale t 2 instantaneous_work) in Hm by lra.
    rewrite (Hadd t
      (fun s => theta * CE.effective_viscosity nu sigma * instantaneous_dissipation s)
      (fun s => instantaneous_force_size s /
        (theta * CE.effective_viscosity nu sigma))) in Hm.
    rewrite (Hscale t
      (theta * CE.effective_viscosity nu sigma)
      instantaneous_dissipation) in Hm by lra.
    assert (Hfun :
      (fun s : Time => instantaneous_force_size s /
        (theta * CE.effective_viscosity nu sigma)) =
      (fun s : Time =>
        (/ (theta * CE.effective_viscosity nu sigma)) * instantaneous_force_size s)).
    {
      apply functional_extensionality.
      intro s.
      unfold Rdiv.
      ring.
    }
    rewrite Hfun in Hm.
    rewrite (Hscale t
      (/ (theta * CE.effective_viscosity nu sigma))
      instantaneous_force_size) in Hm.
    + unfold FA.normalized_intrinsic_force_cost.
      unfold Rdiv.
      nra.
    + apply Rlt_le.
      apply Rinv_0_lt_compat.
      exact Ha.
Qed.

End POSITIVE_LINEAR_ACCUMULATOR.

(* Derive the normalized pointwise estimate directly from the already checked
   global fractional-Stokes Young inequality. *)
Section STOKES_POINTWISE_BRIDGE.

Variable Time Force State H : Type.
Variable inner : H -> H -> R.
Variable norm2 : H -> R.
Variable minus_quarter : Force -> H.
Variable three_quarter : State -> H.
Variable force_size2 : Force -> R.
Variable critical_dissipation : State -> R.
Variable critical_work : Force -> State -> R.
Variable riesz_state : Force -> State.
Variable f : Time -> Force.
Variable u : Time -> State.
Variable nu sigma theta : R.

Definition stokes_instantaneous_work (t : Time) : R :=
  critical_work (f t) (u t).

Definition stokes_instantaneous_dissipation (t : Time) : R :=
  critical_dissipation (u t).

Definition stokes_instantaneous_force_size (t : Time) : R :=
  @SD.StokesHMinusHalfNormSq Force H norm2 minus_quarter (f t).

Theorem AB10_STOKES_YOUNG_GIVES_POINTWISE_NORMALIZED_ABSORPTION :
  @SD.FractionalStokesRealization
    Force State H inner norm2 minus_quarter three_quarter
    force_size2 critical_dissipation critical_work riesz_state ->
  0 < nu ->
  0 <= sigma -> sigma < 1 ->
  0 < theta -> theta < 1 ->
  @PointwiseNormalizedStokesAbsorption
    Time nu sigma theta
    stokes_instantaneous_work
    stokes_instantaneous_dissipation
    stokes_instantaneous_force_size.
Proof.
  intros Hfs Hnu Hs0 Hs1 Ht0 Ht1 t.
  assert (He : 0 < CE.effective_viscosity nu sigma).
  {
    unfold CE.effective_viscosity.
    nra.
  }
  set (a := theta * CE.effective_viscosity nu sigma).
  assert (Ha : 0 < a) by (unfold a; nra).
  pose proof
    (@IFC.IF01_GLOBAL_STOKES_FORCE_ABSORPTION
      Force State H inner norm2 minus_quarter three_quarter
      force_size2 critical_dissipation critical_work riesz_state
      Hfs a (f t) (u t) Ha) as Hy.
  unfold stokes_instantaneous_work,
    stokes_instantaneous_dissipation,
    stokes_instantaneous_force_size.
  fold a.
  apply (Rmult_le_reg_l a).
  - exact Ha.
  - replace (a * (2 * critical_work (f t) (u t)))
      with (2 * a * critical_work (f t) (u t)) by ring.
    replace
      (a *
        (a * critical_dissipation (u t) +
         @SD.StokesHMinusHalfNormSq Force H norm2 minus_quarter (f t) / a))
      with
      (a * a * critical_dissipation (u t) +
       @SD.StokesHMinusHalfNormSq Force H norm2 minus_quarter (f t)).
    + exact Hy.
    + assert (Hane : a <> 0) by lra.
      unfold Rdiv.
      rewrite Rmult_plus_distr_l.
      replace
        (a * (@SD.StokesHMinusHalfNormSq Force H norm2 minus_quarter (f t) * / a))
        with
        (@SD.StokesHMinusHalfNormSq Force H norm2 minus_quarter (f t) * (a * / a)) by ring.
      rewrite (Rinv_r a Hane).
      ring.
Qed.

Theorem AB11_STOKES_FORCE_SIZE_NONNEGATIVE :
  @SD.FractionalStokesRealization
    Force State H inner norm2 minus_quarter three_quarter
    force_size2 critical_dissipation critical_work riesz_state ->
  forall t : Time, 0 <= stokes_instantaneous_force_size t.
Proof.
  intros Hfs t.
  destruct Hfs as [Hnonneg Hcauchy Hself Hsize Hdiss Hwork Halign].
  unfold stokes_instantaneous_force_size, SD.StokesHMinusHalfNormSq.
  apply Hnonneg.
Qed.

End STOKES_POINTWISE_BRIDGE.

(* One-shot composition: a positive linear time accumulator and the checked
   fractional Stokes realization automatically produce the accumulated force
   absorption record used by v0.14.0. *)
Section FULL_ACCUMULATOR_BRIDGE.

Variable Time Force State H : Type.
Variable accumulate_until : Time -> (Time -> R) -> R.
Variable inner : H -> H -> R.
Variable norm2 : H -> R.
Variable minus_quarter : Force -> H.
Variable three_quarter : State -> H.
Variable force_size2 : Force -> R.
Variable critical_dissipation_state : State -> R.
Variable critical_work : Force -> State -> R.
Variable riesz_state : Force -> State.
Variable f : Time -> Force.
Variable u : Time -> State.
Variable nu sigma theta : R.

Definition full_inst_work : Time -> R :=
  @stokes_instantaneous_work Time Force State
    critical_work f u.

Definition full_inst_diss : Time -> R :=
  @stokes_instantaneous_dissipation Time State
    critical_dissipation_state u.

Definition full_inst_size : Time -> R :=
  @stokes_instantaneous_force_size Time Force H
    norm2 minus_quarter f.

Definition full_acc_work (t : Time) : R :=
  accumulate_until t full_inst_work.

Definition full_acc_diss (t : Time) : R :=
  accumulate_until t full_inst_diss.

Definition full_acc_force_size (t : Time) : R :=
  accumulate_until t full_inst_size.

Theorem AB20_POINTWISE_STOKES_YOUNG_TO_ACCUMULATED_ABSORPTION :
  @PositiveLinearAccumulator Time accumulate_until ->
  @SD.FractionalStokesRealization
    Force State H inner norm2 minus_quarter three_quarter
    force_size2 critical_dissipation_state critical_work riesz_state ->
  0 < nu ->
  0 <= sigma -> sigma < 1 ->
  0 < theta -> theta < 1 ->
  @FA.AccumulatedIntrinsicForceAbsorption
    Time nu sigma theta full_acc_diss full_acc_work full_acc_force_size.
Proof.
  intros Hacc Hfs Hnu Hs0 Hs1 Ht0 Ht1.
  eapply (@AB00_POINTWISE_ABSORPTION_ACCUMULATES
    Time accumulate_until nu sigma theta
    full_inst_work full_inst_diss full_inst_size).
  - exact Hacc.
  - exact Hnu.
  - exact Hs0.
  - exact Hs1.
  - exact Ht0.
  - exact Ht1.
  - intro t.
    unfold full_inst_size, stokes_instantaneous_force_size,
      SD.StokesHMinusHalfNormSq.
    pose proof Hfs as Hfs_nonneg.
    destruct Hfs_nonneg as
      [Hnonneg Hcauchy Hself Hsize Hdiss Hwork Halign].
    apply Hnonneg.
  - unfold PointwiseNormalizedStokesAbsorption.
    intro t.
    unfold full_inst_work, full_inst_diss, full_inst_size.
    apply (@AB10_STOKES_YOUNG_GIVES_POINTWISE_NORMALIZED_ABSORPTION
      Time Force State H inner norm2 minus_quarter three_quarter
      force_size2 critical_dissipation_state critical_work riesz_state
      f u nu sigma theta Hfs Hnu Hs0 Hs1 Ht0 Ht1 t).
Qed.

End FULL_ACCUMULATOR_BRIDGE.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE_V0_15_2"%string.

End NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.

Check NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.AB00_POINTWISE_ABSORPTION_ACCUMULATES.
Check NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.AB20_POINTWISE_STOKES_YOUNG_TO_ACCUMULATED_ABSORPTION.
