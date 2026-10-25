
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_perspective_action_v0_11_2.
Require Import awpi_nse_gp_closed_action_envelope_v0_19_2.
Require Import awpi_nse_gp_finite_cutoff_envelope_v0_20_0.
Require Import awpi_nse_gp_leray_modal_triad_adapter_v0_13_3.
Require Import awpi_nse_gp_source_class_ownership_v0_25_4.
Require Import awpi_nse_gp_parent_degree_reproduction_v0_26_0.
Require Import awpi_nse_gp_renewal_reduction_v0_3_1.
Require Import awpi_nse_gp_to_m7_route_v0_28_3.
Open Scope R_scope.

Module NSE_GP_GK_COHOMOLOGY_REALIZATION.

Module PR := NSE_GP_PARENT_DEGREE_REPRODUCTION.
Module RR := NSE_GP_RENEWAL_REDUCTION.
Module MR := NSE_GP_TO_M7_ROUTE.

Definition delta (V : nat -> R) (n : nat) : R :=
  V (S n) - V n.

Theorem GKGK00_PREFIX_DELTA_TELESCOPES :
  forall V : nat -> R,
  forall N : nat,
    RR.prefix_sum (delta V) N = V N - V 0%nat.
Proof.
  intros V N.
  induction N as [|N IH].
  - simpl. unfold delta. lra.
  - change
      (RR.prefix_sum (delta V) N
       + (V (S N) - V N)
       =
       V (S N) - V 0%nat).
    rewrite IH.
    lra.
Qed.

Theorem GKGK01_PREFIX_POINTWISE_LE :
  forall f g : nat -> R,
    (forall n : nat, f n <= g n) ->
    forall N : nat,
      RR.prefix_sum f N <= RR.prefix_sum g N.
Proof.
  intros f g Hle N.
  induction N as [|N IH].
  - simpl. lra.
  - simpl.
    specialize (Hle N).
    lra.
Qed.

Theorem GKGK02_PREFIX_PAID_PLUS_DRIFT :
  forall paid V : nat -> R,
  forall alpha : R,
  forall N : nat,
    RR.prefix_sum
      (fun n => paid n + alpha * delta V n) N
    =
    RR.prefix_sum paid N
    + alpha * (V N - V 0%nat).
Proof.
  intros paid V alpha N.
  induction N as [|N IH].
  - simpl. lra.
  - change
      (RR.prefix_sum
         (fun n => paid n + alpha * delta V n) N
       + (paid N + alpha * (V (S N) - V N))
       =
       (RR.prefix_sum paid N + paid N)
       + alpha * (V (S N) - V 0%nat)).
    rewrite IH.
    ring.
Qed.

Record GKChannelCertificate (paid : nat -> R) : Type := {
  gkc_cost : nat -> R;
  gkc_potential : nat -> R;
  gkc_alpha : R;
  gkc_lower : R;

  gkc_paid_nonnegative :
    forall n : nat, 0 <= paid n;

  gkc_cost_nonnegative :
    forall n : nat, 0 <= gkc_cost n;

  gkc_alpha_nonnegative :
    0 <= gkc_alpha;

  gkc_potential_lower :
    forall n : nat, gkc_lower <= gkc_potential n;

  gkc_local :
    forall n : nat,
      paid n
      + gkc_alpha * delta gkc_potential n
      <= gkc_cost n;

  gkc_cost_budget :
    RR.uniform_prefix_budget gkc_cost
}.

Theorem GKGK10_CHANNEL_GIVES_UNIFORM_PAID_BUDGET :
  forall paid : nat -> R,
  forall C : GKChannelCertificate paid,
    RR.uniform_prefix_budget paid.
Proof.
  intros paid C.
  destruct (gkc_cost_budget paid C) as [B [HB Hcost]].
  exists
    (B
     + gkc_alpha paid C
       * (gkc_potential paid C 0%nat - gkc_lower paid C)).
  split.
  - pose proof (gkc_potential_lower paid C 0%nat) as Hlower0.
    pose proof (gkc_alpha_nonnegative paid C) as Halpha.
    nra.
  - intro N.
    pose proof
      (GKGK01_PREFIX_POINTWISE_LE
        (fun n =>
          paid n
          + gkc_alpha paid C
            * delta (gkc_potential paid C) n)
        (gkc_cost paid C)
        (gkc_local paid C)
        N) as Hsum.
    rewrite
      (GKGK02_PREFIX_PAID_PLUS_DRIFT
        paid
        (gkc_potential paid C)
        (gkc_alpha paid C)
        N)
      in Hsum.
    specialize (Hcost N).
    pose proof (gkc_potential_lower paid C N) as HlowerN.
    pose proof (gkc_alpha_nonnegative paid C) as Halpha.
    nra.
Qed.

Theorem GKGK11_EXPLICIT_CHANNEL_BOUND :
  forall paid : nat -> R,
  forall C : GKChannelCertificate paid,
  forall B : R,
    0 <= B ->
    (forall N : nat,
      RR.prefix_sum (gkc_cost paid C) N <= B) ->
    forall N : nat,
      RR.prefix_sum paid N
      <=
      B
      + gkc_alpha paid C
        * (gkc_potential paid C 0%nat - gkc_lower paid C).
Proof.
  intros paid C B HB Hcost N.
  pose proof
    (GKGK01_PREFIX_POINTWISE_LE
      (fun n =>
        paid n
        + gkc_alpha paid C
          * delta (gkc_potential paid C) n)
      (gkc_cost paid C)
      (gkc_local paid C)
      N) as Hsum.
  rewrite
    (GKGK02_PREFIX_PAID_PLUS_DRIFT
      paid
      (gkc_potential paid C)
      (gkc_alpha paid C)
      N)
    in Hsum.
  specialize (Hcost N).
  pose proof (gkc_potential_lower paid C N) as HlowerN.
  pose proof (gkc_alpha_nonnegative paid C) as Halpha.
  nra.
Qed.

Record GPRouteGKCertificate (dstar : nat) : Type := {
  gkg_action : nat -> R;
  gkg_routes : nat -> list (PR.ParentRoute dstar);

  gkg_scale_paid : nat -> R;
  gkg_future_paid : nat -> R;
  gkg_residual_paid : nat -> R;

  gkg_action_nonnegative :
    forall n : nat, 0 <= gkg_action n;

  gkg_next_owned :
    forall n : nat,
      gkg_action (S n)
      <= PR.forest_child_action (gkg_routes n);

  gkg_parent_paid :
    forall n : nat,
      PR.forest_parent_action (gkg_routes n)
      <= gkg_action n;

  gkg_legal_cost_split :
    forall n : nat,
      PR.forest_legal_cost (gkg_routes n)
      <=
      gkg_scale_paid n
      + gkg_future_paid n
      + gkg_residual_paid n;

  gkg_scale_gk :
    GKChannelCertificate gkg_scale_paid;

  gkg_future_gk :
    GKChannelCertificate gkg_future_paid;

  gkg_residual_gk :
    GKChannelCertificate gkg_residual_paid
}.

Definition build_gp_route_from_gk
  {dstar : nat}
  (C : GPRouteGKCertificate dstar)
  : MR.GPRouteCertificate dstar.
Proof.
  refine {|
    MR.gpr_action := gkg_action dstar C;
    MR.gpr_routes := gkg_routes dstar C;

    MR.gpr_scale_paid := gkg_scale_paid dstar C;
    MR.gpr_future_paid := gkg_future_paid dstar C;
    MR.gpr_residual_paid := gkg_residual_paid dstar C;

    MR.gpr_action_nonnegative := gkg_action_nonnegative dstar C;

    MR.gpr_scale_nonnegative :=
      gkc_paid_nonnegative
        (gkg_scale_paid dstar C)
        (gkg_scale_gk dstar C);

    MR.gpr_future_nonnegative :=
      gkc_paid_nonnegative
        (gkg_future_paid dstar C)
        (gkg_future_gk dstar C);

    MR.gpr_residual_nonnegative :=
      gkc_paid_nonnegative
        (gkg_residual_paid dstar C)
        (gkg_residual_gk dstar C);

    MR.gpr_next_owned := gkg_next_owned dstar C;
    MR.gpr_parent_paid := gkg_parent_paid dstar C;
    MR.gpr_legal_cost_split := gkg_legal_cost_split dstar C;

    MR.gpr_scale_budget :=
      GKGK10_CHANNEL_GIVES_UNIFORM_PAID_BUDGET
        (gkg_scale_paid dstar C)
        (gkg_scale_gk dstar C);

    MR.gpr_future_budget :=
      GKGK10_CHANNEL_GIVES_UNIFORM_PAID_BUDGET
        (gkg_future_paid dstar C)
        (gkg_future_gk dstar C);

    MR.gpr_residual_budget :=
      GKGK10_CHANNEL_GIVES_UNIFORM_PAID_BUDGET
        (gkg_residual_paid dstar C)
        (gkg_residual_gk dstar C)
  |}.
Defined.

Theorem GKGK20_GK_CERTIFICATE_BUILDS_GP_ROUTE :
  forall dstar : nat,
  forall C : GPRouteGKCertificate dstar,
    exists G : MR.GPRouteCertificate dstar,
      forall n : nat,
        MR.gpr_action dstar G n = gkg_action dstar C n.
Proof.
  intros dstar C.
  exists (build_gp_route_from_gk C).
  intro n.
  reflexivity.
Qed.

Theorem GKGK30_GK_REALIZATION_IMPLIES_DISCRETE_M7 :
  forall dstar : nat,
  forall C : GPRouteGKCertificate dstar,
    MR.ActualDiscreteGPM7 (gkg_action dstar C).
Proof.
  intros dstar C.
  exact
    (MR.GPMR30_GP_ROUTE_IMPLIES_DISCRETE_M7
      dstar
      (build_gp_route_from_gk C)).
Qed.

Theorem GKGK31_GK_REALIZATION_IMPLIES_OLD_FINITE_MEMORY_M7 :
  forall dstar : nat,
  forall C : GPRouteGKCertificate dstar,
    RR.finite_memory_gpm7 (gkg_action dstar C).
Proof.
  intros dstar C.
  exact
    (MR.GPMR33_GP_ROUTE_IMPLIES_OLD_FINITE_MEMORY_GPM7
      dstar
      (build_gp_route_from_gk C)).
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_GK_COHOMOLOGY_REALIZATION.

Check NSE_GP_GK_COHOMOLOGY_REALIZATION.delta.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.GKGK00_PREFIX_DELTA_TELESCOPES.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.GKGK01_PREFIX_POINTWISE_LE.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.GKGK02_PREFIX_PAID_PLUS_DRIFT.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.GKChannelCertificate.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.GKGK10_CHANNEL_GIVES_UNIFORM_PAID_BUDGET.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.GKGK11_EXPLICIT_CHANNEL_BOUND.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.GPRouteGKCertificate.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.build_gp_route_from_gk.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.GKGK20_GK_CERTIFICATE_BUILDS_GP_ROUTE.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.GKGK30_GK_REALIZATION_IMPLIES_DISCRETE_M7.
Check NSE_GP_GK_COHOMOLOGY_REALIZATION.GKGK31_GK_REALIZATION_IMPLIES_OLD_FINITE_MEMORY_M7.
