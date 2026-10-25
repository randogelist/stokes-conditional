From Stdlib Require Import Reals Lra Psatz String.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.

Module NSE_M7_CRITICAL_ENERGY_INJECTION.

Open Scope R_scope.

(*
  New central target
  ------------------
  Separate the formerly opaque implication

      M7 -> L^\infty_t H^(1/2) /\ L^2_t H^(3/2)

  into two pieces:

    (A) M7 genealogy -> a uniform bound on the normalized resistant-action cost;

    (B) normalized resistant-action cost
        + the critical energy balance
        -> uniform critical mass and dissipation bounds.

  Piece (B) is deterministic energy algebra.  The only substantive semantic
  input from M7 is Piece (A).
*)

Definition effective_viscosity (nu sigma : R) : R :=
  (1 - sigma) * nu.

(*
  Algebraic Young/absorption lemma.

  r^2 <= a*d is the quadratic-over-linear resistant action relation.
  e=(1-sigma)nu > 0.
  Then
      2 e r <= e^2 d + a.
*)
Theorem NSCE00_QUADRATIC_RESISTANT_ACTION_YOUNG :
  forall (e d a r : R),
    0 < e ->
    0 <= d ->
    0 <= a ->
    0 <= r ->
    r * r <= a * d ->
    2 * e * r <= e * e * d + a.
Proof.
  intros e d a r He Hd Ha Hr Hquad.
  assert (He2 : 0 <= e * e) by nra.
  assert (Had : 0 <= a * d - r * r) by nra.
  assert (Hprod : 0 <= 4 * (e * e) * (a * d - r * r)).
  {
    apply Rmult_le_pos.
    - nra.
    - exact Had.
  }
  assert (Hsq : 0 <= (e * e * d - a) ^ 2).
  {
    pose proof (Rle_0_sqr (e * e * d - a)) as Hsq0.
    unfold Rsqr in Hsq0.
    replace ((e * e * d - a) ^ 2)
      with ((e * e * d - a) * (e * e * d - a)) by ring.
    exact Hsq0.
  }
  assert (Hsquare :
    (2 * e * r) ^ 2 <= (e * e * d + a) ^ 2).
  {
    nra.
  }
  assert (Hleft : 0 <= 2 * e * r) by nra.
  assert (Hright : 0 <= e * e * d + a) by nra.
  nra.
Qed.

(*
  Safe + resistant local transfer absorption.

  safe <= sigma*nu*d,
  r^2 <= a*d,
  e=(1-sigma)nu,

  gives the denominator-free multiplied form
      2 e (safe+r) <= e(1+sigma)nu*d + a.
*)
Theorem NSCE01_SAFE_RESISTANT_LOCAL_ABSORPTION :
  forall (nu sigma d a safe r : R),
    0 < nu ->
    0 <= sigma ->
    sigma < 1 ->
    0 <= d ->
    0 <= a ->
    0 <= safe ->
    0 <= r ->
    safe <= sigma * nu * d ->
    r * r <= a * d ->
    let e := effective_viscosity nu sigma in
    2 * e * (safe + r) <=
      e * (1 + sigma) * nu * d + a.
Proof.
  intros nu sigma d a safe r Hnu Hsig0 Hsig1 Hd Ha Hsafe0 Hr0 Hsafe Hquad.
  unfold effective_viscosity.
  set (e := (1 - sigma) * nu).
  assert (He : 0 < e).
  {
    unfold e.
    nra.
  }
  pose proof
    (NSCE00_QUADRATIC_RESISTANT_ACTION_YOUNG
       e d a r He Hd Ha Hr0 Hquad) as Hy.
  assert (H2e : 0 <= 2 * e) by nra.
  pose proof
    (Rmult_le_compat_l (2 * e) safe (sigma * nu * d) H2e Hsafe)
    as Hsafe_scaled.
  assert (Hid :
    2 * e * (sigma * nu * d) + e * e * d =
    e * (1 + sigma) * nu * d).
  {
    unfold e.
    ring.
  }
  replace (2 * e * (safe + r))
    with (2 * e * safe + 2 * e * r) by ring.
  rewrite <- Hid.
  lra.
Qed.

(*
  Integrated critical-energy representation.

  critical_mass t corresponds to ||A^(1/4) u(t)||_2^2.
  critical_dissipation t corresponds to the cumulative integral
      integral_0^t ||A^(3/4)u(s)||_2^2 ds.
  action_cost t is the normalized resistant-action cost
      integral_0^t a(s)/((1-sigma)nu) ds.

  The integrated balance is exactly what results from integrating the
  absorbed critical-energy inequality.
*)
Record CriticalEnergyBalance
  (Time : Type) (nu sigma initial_mass : R)
  (critical_mass critical_dissipation action_cost : Time -> R) : Prop := {
  ceb_nu_pos : 0 < nu;
  ceb_sigma_nonneg : 0 <= sigma;
  ceb_sigma_lt_one : sigma < 1;
  ceb_initial_nonneg : 0 <= initial_mass;

  ceb_mass_nonneg :
    forall t : Time, 0 <= critical_mass t;

  ceb_dissipation_nonneg :
    forall t : Time, 0 <= critical_dissipation t;

  ceb_action_nonneg :
    forall t : Time, 0 <= action_cost t;

  ceb_integrated_balance :
    forall t : Time,
      critical_mass t +
      effective_viscosity nu sigma * critical_dissipation t <=
      initial_mass + action_cost t
}.

Definition UniformCriticalEnergy
  (Time : Type)
  (critical_mass critical_dissipation : Time -> R) : Prop :=
  exists Mmax Dmax : R,
    0 <= Mmax /\
    0 <= Dmax /\
    (forall t : Time, critical_mass t <= Mmax) /\
    (forall t : Time, critical_dissipation t <= Dmax).

Theorem NSCE10_ACTION_COST_BOUND_GIVES_CRITICAL_ENERGY :
  forall (Time : Type)
         (nu sigma initial_mass Amax : R)
         (critical_mass critical_dissipation action_cost : Time -> R),
    CriticalEnergyBalance
      Time nu sigma initial_mass
      critical_mass critical_dissipation action_cost ->
    0 <= Amax ->
    (forall t : Time, action_cost t <= Amax) ->
    UniformCriticalEnergy Time critical_mass critical_dissipation.
Proof.
  intros Time nu sigma initial_mass Amax
         critical_mass critical_dissipation action_cost
         Hbal HAmax Haction.
  destruct Hbal as
    [Hnu Hsig0 Hsig1 Hinit
     Hmass0 Hdiss0 Hact0 Hbalance].
  set (e := effective_viscosity nu sigma).
  assert (He : 0 < e).
  {
    unfold e, effective_viscosity.
    nra.
  }
  exists (initial_mass + Amax).
  exists ((initial_mass + Amax) / e).
  repeat split.
  - nra.
  - unfold Rdiv.
    apply Rmult_le_pos.
    + nra.
    + apply Rlt_le.
      apply Rinv_0_lt_compat.
      exact He.
  - intro t.
    specialize (Hbalance t).
    fold e in Hbalance.
    specialize (Haction t).
    specialize (Hdiss0 t).
    assert (Hediss : 0 <= e * critical_dissipation t).
    {
      apply Rmult_le_pos.
      - exact (Rlt_le _ _ He).
      - exact Hdiss0.
    }
    lra.
  - intro t.
    specialize (Hbalance t).
    fold e in Hbalance.
    specialize (Haction t).
    specialize (Hmass0 t).
    assert (He0 : e <> 0) by nra.
    apply (Rmult_le_reg_l e).
    + exact He.
    + replace (e * ((initial_mass + Amax) / e))
        with (initial_mass + Amax).
      * nra.
      * unfold Rdiv.
        rewrite <- Rmult_assoc.
        rewrite (Rmult_comm e (initial_mass + Amax)).
        rewrite Rmult_assoc.
        rewrite (Rinv_r e He0).
        ring.
Qed.

(*
  M7 semantics for the critical-energy target.

  This is now the ONLY M7-specific identification needed by this file:
  the normalized physical resistant-action cost up to any physical time is
  dominated by some finite M7 resistant prefix.
*)
Definition M7ActionCostRealization
  (Time : Type)
  (mass : nat -> R)
  (action_cost : Time -> R) : Prop :=
  forall t : Time,
    exists N : nat,
      action_cost t <= NSE_GP_TO_M7_SPINE.resistant_prefix mass N.

Theorem NSCE20_SEQUENCE_M7_GIVES_UNIFORM_ACTION_COST :
  forall (Time : Type)
         (mass : nat -> R)
         (action_cost : Time -> R),
    NSE_GP_TO_M7_SPINE.GPSequenceM7 mass ->
    M7ActionCostRealization Time mass action_cost ->
    exists Amax : R,
      0 <= Amax /\
      forall t : Time, action_cost t <= Amax.
Proof.
  intros Time mass action_cost HM7 Hreal.
  destruct HM7 as [B [HB Hprefix]].
  exists B.
  split.
  - exact HB.
  - intro t.
    destruct (Hreal t) as [N Hact].
    exact (Rle_trans _ _ _ Hact (Hprefix N)).
Qed.

Theorem NSCE30_M7_PLUS_BALANCE_GIVES_CRITICAL_ENERGY :
  forall (Time : Type)
         (mass : nat -> R)
         (nu sigma initial_mass : R)
         (critical_mass critical_dissipation action_cost : Time -> R),
    NSE_GP_TO_M7_SPINE.GPSequenceM7 mass ->
    M7ActionCostRealization Time mass action_cost ->
    CriticalEnergyBalance
      Time nu sigma initial_mass
      critical_mass critical_dissipation action_cost ->
    UniformCriticalEnergy Time critical_mass critical_dissipation.
Proof.
  intros Time mass nu sigma initial_mass
         critical_mass critical_dissipation action_cost
         HM7 Hreal Hbalance.
  destruct
    (NSCE20_SEQUENCE_M7_GIVES_UNIFORM_ACTION_COST
       Time mass action_cost HM7 Hreal)
    as [Amax [HAmax Haction]].
  exact
    (NSCE10_ACTION_COST_BOUND_GIVES_CRITICAL_ENERGY
       Time nu sigma initial_mass Amax
       critical_mass critical_dissipation action_cost
       Hbalance HAmax Haction).
Qed.

(*
  Semantic names matching the new externally visible target.
*)
Definition CriticalH12Bound
  (Time : Type) (critical_mass : Time -> R) : Prop :=
  exists Mmax : R,
    0 <= Mmax /\
    forall t : Time, critical_mass t <= Mmax.

Definition CriticalH32Dissipation
  (Time : Type) (critical_dissipation : Time -> R) : Prop :=
  exists Dmax : R,
    0 <= Dmax /\
    forall t : Time, critical_dissipation t <= Dmax.

Theorem NSCE40_UNIFORM_CRITICAL_ENERGY_SPLITS_TO_H12_H32 :
  forall (Time : Type)
         (critical_mass critical_dissipation : Time -> R),
    UniformCriticalEnergy Time critical_mass critical_dissipation ->
    CriticalH12Bound Time critical_mass /\
    CriticalH32Dissipation Time critical_dissipation.
Proof.
  intros Time critical_mass critical_dissipation H.
  destruct H as [Mmax [Dmax [HM [HD [Hmass Hdiss]]]]].
  split.
  - exists Mmax. split; assumption.
  - exists Dmax. split; assumption.
Qed.

Theorem NSCE90_M7_INJECTS_INTO_CRITICAL_ENERGY_TARGET :
  forall (Time : Type)
         (mass : nat -> R)
         (nu sigma initial_mass : R)
         (critical_mass critical_dissipation action_cost : Time -> R),
    NSE_GP_TO_M7_SPINE.GPSequenceM7 mass ->
    M7ActionCostRealization Time mass action_cost ->
    CriticalEnergyBalance
      Time nu sigma initial_mass
      critical_mass critical_dissipation action_cost ->
    CriticalH12Bound Time critical_mass /\
    CriticalH32Dissipation Time critical_dissipation.
Proof.
  intros Time mass nu sigma initial_mass
         critical_mass critical_dissipation action_cost
         HM7 Hreal Hbalance.
  apply NSCE40_UNIFORM_CRITICAL_ENERGY_SPLITS_TO_H12_H32.
  exact
    (NSCE30_M7_PLUS_BALANCE_GIVES_CRITICAL_ENERGY
       Time mass nu sigma initial_mass
       critical_mass critical_dissipation action_cost
       HM7 Hreal Hbalance).
Qed.

Definition STATUS : string :=
  "NSE_M7_TO_CRITICAL_ENERGY_INJECTION_V0_35_8_NO_ADMITTED"%string.

End NSE_M7_CRITICAL_ENERGY_INJECTION.

Print Assumptions
  NSE_M7_CRITICAL_ENERGY_INJECTION.NSCE00_QUADRATIC_RESISTANT_ACTION_YOUNG.
Print Assumptions
  NSE_M7_CRITICAL_ENERGY_INJECTION.NSCE10_ACTION_COST_BOUND_GIVES_CRITICAL_ENERGY.
Print Assumptions
  NSE_M7_CRITICAL_ENERGY_INJECTION.NSCE20_SEQUENCE_M7_GIVES_UNIFORM_ACTION_COST.
Print Assumptions
  NSE_M7_CRITICAL_ENERGY_INJECTION.NSCE30_M7_PLUS_BALANCE_GIVES_CRITICAL_ENERGY.
Print Assumptions
  NSE_M7_CRITICAL_ENERGY_INJECTION.NSCE90_M7_INJECTS_INTO_CRITICAL_ENERGY_TARGET.
