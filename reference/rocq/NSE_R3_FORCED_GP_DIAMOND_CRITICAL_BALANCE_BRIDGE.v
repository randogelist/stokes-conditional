From Stdlib Require Import Reals Lra Psatz String FunctionalExtensionality.
Require Import NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.
Require Import NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.

Module AB := NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.NSE_R3_FORCED_GP_DIAMOND_ACCUMULATOR_BRIDGE.
Module FA := NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.NSE_R3_FORCED_GP_DIAMOND_FORCE_ABSORPTION.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.

Open Scope R_scope.

(*
  Last forced A-side entrance contraction.

  Start before the internal M7 absorption with the standard forced critical
  energy inequality

      M + 2 nu D <= M0 + 2 S + 2 R + 2 W_f.

  Here S is the safe nonlinear work, R the resistant nonlinear work, and W_f
  the external forcing work.  The M7 local algebra supplies

      S <= sigma nu D,
      2 R <= e D + I,        e=(1-sigma)nu,

  where I is the normalized resistant-action cost.  These identities imply

      M + e D <= M0 + I + 2 W_f,

  exactly the PostM7ForcedCriticalBalance consumed by v0.14/v0.15.
*)

Section RAW_TO_POST_M7.

Variable Time : Type.
Variable nu sigma initial_mass : R.
Variable critical_mass critical_dissipation : Time -> R.
Variable safe_work resistant_work internal_cost force_work : Time -> R.

Record ForcedCriticalPreM7Balance : Prop := {
  fcpb_nu_pos : 0 < nu;
  fcpb_sigma_nonneg : 0 <= sigma;
  fcpb_sigma_lt_one : sigma < 1;
  fcpb_initial_nonneg : 0 <= initial_mass;
  fcpb_mass_nonneg : forall t : Time, 0 <= critical_mass t;
  fcpb_dissipation_nonneg : forall t : Time, 0 <= critical_dissipation t;
  fcpb_raw_balance :
    forall t : Time,
      critical_mass t + 2 * nu * critical_dissipation t <=
      initial_mass +
      2 * safe_work t +
      2 * resistant_work t +
      2 * force_work t
}.

Record AccumulatedInternalM7Absorption : Prop := {
  aima_internal_nonneg : forall t : Time, 0 <= internal_cost t;
  aima_safe_absorption :
    forall t : Time,
      safe_work t <= sigma * nu * critical_dissipation t;
  aima_resistant_absorption :
    forall t : Time,
      2 * resistant_work t <=
      CE.effective_viscosity nu sigma * critical_dissipation t +
      internal_cost t
}.

Theorem CBB10_PRE_M7_PLUS_INTERNAL_ABSORPTION_GIVES_POST_M7 :
  ForcedCriticalPreM7Balance ->
  AccumulatedInternalM7Absorption ->
  @FA.PostM7ForcedCriticalBalance
    Time nu sigma initial_mass
    critical_mass critical_dissipation
    internal_cost force_work.
Proof.
  intros Hraw Hint.
  destruct Hraw as [Hnu Hs0 Hs1 Hinit Hm Hd Hrawbal].
  destruct Hint as [Hi Hsafe Hres].
  constructor.
  - exact Hnu.
  - exact Hs0.
  - exact Hs1.
  - exact Hinit.
  - exact Hm.
  - exact Hd.
  - exact Hi.
  - intro t.
    specialize (Hrawbal t).
    specialize (Hsafe t).
    specialize (Hres t).
    unfold CE.effective_viscosity in Hres |- *.
    nra.
Qed.

End RAW_TO_POST_M7.

(* Pointwise M7 safe/resistant geometry. *)
Section POINTWISE_INTERNAL_M7.

Variable Time : Type.
Variable nu sigma : R.
Variable instantaneous_dissipation : Time -> R.
Variable instantaneous_action : Time -> R.
Variable instantaneous_safe : Time -> R.
Variable instantaneous_resistant : Time -> R.

Definition normalized_instantaneous_action (t : Time) : R :=
  instantaneous_action t / CE.effective_viscosity nu sigma.

Record PointwiseM7SafeResistantData : Prop := {
  pm7_dissipation_nonneg :
    forall t : Time, 0 <= instantaneous_dissipation t;
  pm7_action_nonneg :
    forall t : Time, 0 <= instantaneous_action t;
  pm7_safe_nonneg :
    forall t : Time, 0 <= instantaneous_safe t;
  pm7_resistant_nonneg :
    forall t : Time, 0 <= instantaneous_resistant t;
  pm7_safe_bound :
    forall t : Time,
      instantaneous_safe t <=
      sigma * nu * instantaneous_dissipation t;
  pm7_quadratic_action :
    forall t : Time,
      instantaneous_resistant t * instantaneous_resistant t <=
      instantaneous_action t * instantaneous_dissipation t
}.

Theorem CBB20_QUADRATIC_ACTION_GIVES_NORMALIZED_RESISTANT_ABSORPTION :
  0 < nu ->
  0 <= sigma -> sigma < 1 ->
  PointwiseM7SafeResistantData ->
  forall t : Time,
    2 * instantaneous_resistant t <=
    CE.effective_viscosity nu sigma * instantaneous_dissipation t +
    normalized_instantaneous_action t.
Proof.
  intros Hnu Hs0 Hs1 Hdata t.
  destruct Hdata as [Hd Ha Hsafe0 Hr Hsafe Hquad].
  assert (He : 0 < CE.effective_viscosity nu sigma).
  {
    unfold CE.effective_viscosity.
    nra.
  }
  pose proof
    (CE.NSCE00_QUADRATIC_RESISTANT_ACTION_YOUNG
      (CE.effective_viscosity nu sigma)
      (instantaneous_dissipation t)
      (instantaneous_action t)
      (instantaneous_resistant t)
      He (Hd t) (Ha t) (Hr t) (Hquad t)) as Hy.
  apply (Rmult_le_reg_l (CE.effective_viscosity nu sigma)).
  - exact He.
  - replace
      (CE.effective_viscosity nu sigma *
        (2 * instantaneous_resistant t))
      with
      (2 * CE.effective_viscosity nu sigma * instantaneous_resistant t)
      by ring.
    unfold normalized_instantaneous_action.
    replace
      (CE.effective_viscosity nu sigma *
        (CE.effective_viscosity nu sigma * instantaneous_dissipation t +
         instantaneous_action t / CE.effective_viscosity nu sigma))
      with
      (CE.effective_viscosity nu sigma *
         CE.effective_viscosity nu sigma * instantaneous_dissipation t +
       instantaneous_action t).
    + exact Hy.
    + assert (Hene : CE.effective_viscosity nu sigma <> 0) by lra.
      unfold Rdiv.
      rewrite Rmult_plus_distr_l.
      replace
        (CE.effective_viscosity nu sigma *
          (instantaneous_action t * / CE.effective_viscosity nu sigma))
        with
        (instantaneous_action t *
          (CE.effective_viscosity nu sigma *
           / CE.effective_viscosity nu sigma)) by ring.
      rewrite (Rinv_r (CE.effective_viscosity nu sigma) Hene).
      ring.
Qed.

End POINTWISE_INTERNAL_M7.

(* Accumulation of the pointwise M7 absorption. *)
Section INTERNAL_M7_ACCUMULATION.

Variable Time : Type.
Variable accumulate_until : Time -> (Time -> R) -> R.
Variable nu sigma : R.
Variable instantaneous_dissipation : Time -> R.
Variable instantaneous_action : Time -> R.
Variable instantaneous_safe : Time -> R.
Variable instantaneous_resistant : Time -> R.

Definition accumulated_safe_work (t : Time) : R :=
  accumulate_until t instantaneous_safe.

Definition accumulated_resistant_work (t : Time) : R :=
  accumulate_until t instantaneous_resistant.

Definition accumulated_internal_dissipation (t : Time) : R :=
  accumulate_until t instantaneous_dissipation.

Definition accumulated_normalized_action (t : Time) : R :=
  accumulate_until t
    (fun s => instantaneous_action s / CE.effective_viscosity nu sigma).

Theorem CBB21_POINTWISE_M7_DATA_ACCUMULATES :
  @AB.PositiveLinearAccumulator Time accumulate_until ->
  0 < nu ->
  0 <= sigma -> sigma < 1 ->
  @PointwiseM7SafeResistantData
    Time nu sigma
    instantaneous_dissipation instantaneous_action
    instantaneous_safe instantaneous_resistant ->
  @AccumulatedInternalM7Absorption
    Time nu sigma
    accumulated_internal_dissipation
    accumulated_safe_work accumulated_resistant_work
    accumulated_normalized_action.
Proof.
  intros Hacc Hnu Hs0 Hs1 Hdata.
  pose proof Hdata as Hdata_for_resistant.
  destruct Hdata as [Hd Ha Hsafe0 Hr Hsafe Hquad].
  destruct Hacc as [Hmono Hadd Hscale Hzero].
  assert (He : 0 < CE.effective_viscosity nu sigma).
  {
    unfold CE.effective_viscosity.
    nra.
  }
  assert (Hnorm0 :
    forall s : Time,
      0 <= instantaneous_action s / CE.effective_viscosity nu sigma).
  {
    intro s.
    unfold Rdiv.
    apply Rmult_le_pos.
    - exact (Ha s).
    - apply Rlt_le.
      apply Rinv_0_lt_compat.
      exact He.
  }
  assert (Hrespt :
    forall s : Time,
      2 * instantaneous_resistant s <=
      CE.effective_viscosity nu sigma * instantaneous_dissipation s +
      instantaneous_action s / CE.effective_viscosity nu sigma).
  {
    intro s.
    exact
      (@CBB20_QUADRATIC_ACTION_GIVES_NORMALIZED_RESISTANT_ABSORPTION
        Time nu sigma
        instantaneous_dissipation instantaneous_action
        instantaneous_safe instantaneous_resistant
        Hnu Hs0 Hs1 Hdata_for_resistant s).
  }
  constructor.
  - intro t.
    unfold accumulated_normalized_action.
    pose proof
      (Hmono t
        (fun _ : Time => 0)
        (fun s => instantaneous_action s / CE.effective_viscosity nu sigma)
        (fun s => Hnorm0 s)) as Hm.
    rewrite Hzero in Hm.
    exact Hm.
  - intro t.
    unfold accumulated_safe_work, accumulated_internal_dissipation.
    pose proof
      (Hmono t
        instantaneous_safe
        (fun s => sigma * nu * instantaneous_dissipation s)
        Hsafe) as Hm.
    rewrite (Hscale t (sigma * nu) instantaneous_dissipation) in Hm by nra.
    exact Hm.
  - intro t.
    unfold accumulated_resistant_work,
      accumulated_internal_dissipation,
      accumulated_normalized_action.
    pose proof
      (Hmono t
        (fun s => 2 * instantaneous_resistant s)
        (fun s =>
          CE.effective_viscosity nu sigma * instantaneous_dissipation s +
          instantaneous_action s / CE.effective_viscosity nu sigma)
        Hrespt) as Hm.
    rewrite (Hscale t 2 instantaneous_resistant) in Hm by lra.
    rewrite (Hadd t
      (fun s => CE.effective_viscosity nu sigma * instantaneous_dissipation s)
      (fun s => instantaneous_action s / CE.effective_viscosity nu sigma)) in Hm.
    rewrite (Hscale t
      (CE.effective_viscosity nu sigma)
      instantaneous_dissipation) in Hm by lra.
    exact Hm.
Qed.

End INTERNAL_M7_ACCUMULATION.

(* One-shot deterministic bridge from the standard raw forced critical balance
   to the post-M7 balance consumed by the force-absorption layers. *)
Section ONE_SHOT_FORCED_BRIDGE.

Variable Time : Type.
Variable accumulate_until : Time -> (Time -> R) -> R.
Variable nu sigma initial_mass : R.
Variable critical_mass : Time -> R.
Variable instantaneous_dissipation : Time -> R.
Variable instantaneous_action : Time -> R.
Variable instantaneous_safe : Time -> R.
Variable instantaneous_resistant : Time -> R.
Variable force_work : Time -> R.

Definition bridge_dissipation (t : Time) : R :=
  accumulate_until t instantaneous_dissipation.

Definition bridge_safe_work (t : Time) : R :=
  accumulate_until t instantaneous_safe.

Definition bridge_resistant_work (t : Time) : R :=
  accumulate_until t instantaneous_resistant.

Definition bridge_internal_cost (t : Time) : R :=
  accumulate_until t
    (fun s => instantaneous_action s / CE.effective_viscosity nu sigma).

Theorem CBB30_RAW_FORCED_IDENTITY_PLUS_POINTWISE_M7_GIVES_POST_M7_BALANCE :
  @AB.PositiveLinearAccumulator Time accumulate_until ->
  @ForcedCriticalPreM7Balance
    Time nu sigma initial_mass
    critical_mass bridge_dissipation
    bridge_safe_work bridge_resistant_work
    force_work ->
  @PointwiseM7SafeResistantData
    Time nu sigma
    instantaneous_dissipation instantaneous_action
    instantaneous_safe instantaneous_resistant ->
  @FA.PostM7ForcedCriticalBalance
    Time nu sigma initial_mass
    critical_mass bridge_dissipation
    bridge_internal_cost force_work.
Proof.
  intros Hacc Hraw Hpoint.
  pose proof Hraw as Hraw_bounds.
  destruct Hraw_bounds as [Hnu Hs0 Hs1 Hinit Hm Hd Hrawbal].
  apply (@CBB10_PRE_M7_PLUS_INTERNAL_ABSORPTION_GIVES_POST_M7
    Time nu sigma initial_mass
    critical_mass bridge_dissipation
    bridge_safe_work bridge_resistant_work
    bridge_internal_cost force_work).
  - exact Hraw.
  - exact
      (@CBB21_POINTWISE_M7_DATA_ACCUMULATES
        Time accumulate_until nu sigma
        instantaneous_dissipation instantaneous_action
        instantaneous_safe instantaneous_resistant
        Hacc Hnu Hs0 Hs1 Hpoint).
Qed.

End ONE_SHOT_FORCED_BRIDGE.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE_V0_16_1"%string.

End NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.

Check NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.CBB10_PRE_M7_PLUS_INTERNAL_ABSORPTION_GIVES_POST_M7.
Check NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.CBB20_QUADRATIC_ACTION_GIVES_NORMALIZED_RESISTANT_ABSORPTION.
Check NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.CBB21_POINTWISE_M7_DATA_ACCUMULATES.
Check NSE_R3_FORCED_GP_DIAMOND_CRITICAL_BALANCE_BRIDGE.CBB30_RAW_FORCED_IDENTITY_PLUS_POINTWISE_M7_GIVES_POST_M7_BALANCE.
