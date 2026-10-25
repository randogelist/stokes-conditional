
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_perspective_action_v0_11_2.
Require Import awpi_nse_gp_closed_action_envelope_v0_19_2.
Require Import awpi_nse_gp_finite_cutoff_envelope_v0_20_0.
Require Import awpi_nse_gp_leray_modal_triad_adapter_v0_13_3.
Require Import awpi_nse_gp_source_class_ownership_v0_25_4.
Require Import awpi_nse_gp_parent_degree_reproduction_v0_26_0.
Require Import awpi_nse_gp_renewal_reduction_v0_3_1.
Import ListNotations.
Open Scope R_scope.

Module NSE_GP_TO_M7_ROUTE.

Module PR := NSE_GP_PARENT_DEGREE_REPRODUCTION.
Module RR := NSE_GP_RENEWAL_REDUCTION.

(* --------------------------------------------------------------------- *)
(* Canonical GP -> M7 route interface.                                    *)
(* --------------------------------------------------------------------- *)

Record GPRouteCertificate (dstar : nat) : Type := {
  gpr_action : nat -> R;
  gpr_routes : nat -> list (PR.ParentRoute dstar);

  (* The three canonical payment channels produced by the transform picture. *)
  gpr_scale_paid : nat -> R;
  gpr_future_paid : nat -> R;
  gpr_residual_paid : nat -> R;

  gpr_action_nonnegative :
    forall n : nat, 0 <= gpr_action n;

  gpr_scale_nonnegative :
    forall n : nat, 0 <= gpr_scale_paid n;
  gpr_future_nonnegative :
    forall n : nat, 0 <= gpr_future_paid n;
  gpr_residual_nonnegative :
    forall n : nat, 0 <= gpr_residual_paid n;

  (* Every next GP/DT resistant cell is owned by the physical child forest. *)
  gpr_next_owned :
    forall n : nat,
      gpr_action (S n)
        <= PR.forest_child_action (gpr_routes n);

  (* Current grouped parent action is paid by the current GP cell. *)
  gpr_parent_paid :
    forall n : nat,
      PR.forest_parent_action (gpr_routes n)
        <= gpr_action n;

  (* Every legal forest cost is assigned to one of the three GP payment
     channels. *)
  gpr_legal_cost_split :
    forall n : nat,
      PR.forest_legal_cost (gpr_routes n)
        <=
        gpr_scale_paid n
        + gpr_future_paid n
        + gpr_residual_paid n;

  (* Global payment budgets. *)
  gpr_scale_budget :
    RR.uniform_prefix_budget gpr_scale_paid;
  gpr_future_budget :
    RR.uniform_prefix_budget gpr_future_paid;
  gpr_residual_budget :
    RR.uniform_prefix_budget gpr_residual_paid
}.

Definition gp_total_paid
  {dstar : nat} (G : GPRouteCertificate dstar) (n : nat) : R :=
  gpr_scale_paid dstar G n
  + gpr_future_paid dstar G n
  + gpr_residual_paid dstar G n.

Theorem GPMR00_TOTAL_PAID_NONNEG :
  forall dstar : nat,
  forall G : GPRouteCertificate dstar,
  forall n : nat,
    0 <= gp_total_paid G n.
Proof.
  intros dstar G n.
  unfold gp_total_paid.
  pose proof (gpr_scale_nonnegative dstar G n) as Hs.
  pose proof (gpr_future_nonnegative dstar G n) as Hf.
  pose proof (gpr_residual_nonnegative dstar G n) as Hr.
  lra.
Qed.

(* --------------------------------------------------------------------- *)
(* Physical parent forest -> local GP recurrence.                          *)
(* --------------------------------------------------------------------- *)

(* v0.26.0 actually gives the stronger coefficient 1 on the current cell. *)
Theorem GPMR10_PARENT_FOREST_GIVES_STRONG_LOCAL_RECURRENCE :
  forall dstar : nat,
  forall G : GPRouteCertificate dstar,
  forall n : nat,
    4 * gpr_action dstar G (S n)
      <= gpr_action dstar G n + gp_total_paid G n.
Proof.
  intros dstar G n.
  pose proof
    (PR.GPPR41_NEXT_ACTION_PAID_BY_PARENT_FOREST
      dstar
      (gpr_routes dstar G n)
      (gpr_action dstar G (S n))
      (gpr_next_owned dstar G n)) as Hforest.
  pose proof (gpr_parent_paid dstar G n) as Hparent.
  pose proof (gpr_legal_cost_split dstar G n) as Hcost.
  unfold gp_total_paid.
  lra.
Qed.

(* Relax to the common 3/4 renewal currency used by the semantic M7 spine. *)
Theorem GPMR11_PARENT_FOREST_GIVES_FOUR_THREE_RECURRENCE :
  forall dstar : nat,
  forall G : GPRouteCertificate dstar,
  forall n : nat,
    4 * gpr_action dstar G (S n)
      <= 3 * gpr_action dstar G n + gp_total_paid G n.
Proof.
  intros dstar G n.
  pose proof
    (GPMR10_PARENT_FOREST_GIVES_STRONG_LOCAL_RECURRENCE
      dstar G n) as Hstrong.
  pose proof (gpr_action_nonnegative dstar G n) as Ha.
  lra.
Qed.

Definition four_three_recurrence
  (a paid : nat -> R) : Prop :=
  forall n : nat,
    4 * a (S n) <= 3 * a n + paid n.

Theorem GPMR12_ROUTE_CERTIFICATE_GIVES_FOUR_THREE_RECURRENCE :
  forall dstar : nat,
  forall G : GPRouteCertificate dstar,
    four_three_recurrence
      (gpr_action dstar G)
      (gp_total_paid G).
Proof.
  intros dstar G n.
  apply GPMR11_PARENT_FOREST_GIVES_FOUR_THREE_RECURRENCE.
Qed.

(* --------------------------------------------------------------------- *)
(* Exact prefix invariant for the 4/3 recurrence.                          *)
(* --------------------------------------------------------------------- *)

Theorem GPMR20_PREFIX_INVARIANT :
  forall a paid : nat -> R,
    four_three_recurrence a paid ->
    forall N : nat,
      RR.prefix_sum a N + 4 * a N
        <= 4 * a 0%nat + RR.prefix_sum paid N.
Proof.
  intros a paid Hrec N.
  induction N as [|N IH].
  - simpl.
    lra.
  - simpl.
    specialize (Hrec N).
    lra.
Qed.

Theorem GPMR21_PREFIX_ACTION_BOUND :
  forall a paid : nat -> R,
    (forall n : nat, 0 <= a n) ->
    four_three_recurrence a paid ->
    forall N : nat,
      RR.prefix_sum a N
        <= 4 * a 0%nat + RR.prefix_sum paid N.
Proof.
  intros a paid Ha Hrec N.
  pose proof (GPMR20_PREFIX_INVARIANT a paid Hrec N) as Hinv.
  pose proof (Ha N) as HaN.
  lra.
Qed.

Theorem GPMR22_TOTAL_PAID_PREFIX_SPLITS :
  forall dstar : nat,
  forall G : GPRouteCertificate dstar,
  forall N : nat,
    RR.prefix_sum (gp_total_paid G) N
    =
    RR.prefix_sum (gpr_scale_paid dstar G) N
    + RR.prefix_sum (gpr_future_paid dstar G) N
    + RR.prefix_sum (gpr_residual_paid dstar G) N.
Proof.
  intros dstar G N.
  induction N as [|N IH].
  - simpl.
    ring.
  - simpl.
    rewrite IH.
    unfold gp_total_paid.
    ring.
Qed.

(* Three separate transform-payment budgets combine into one M7 budget. *)
Theorem GPMR23_TOTAL_PAID_HAS_UNIFORM_PREFIX_BUDGET :
  forall dstar : nat,
  forall G : GPRouteCertificate dstar,
    RR.uniform_prefix_budget (gp_total_paid G).
Proof.
  intros dstar G.
  destruct (gpr_scale_budget dstar G) as [Bs [HBs Hs]].
  destruct (gpr_future_budget dstar G) as [Bf [HBf Hf]].
  destruct (gpr_residual_budget dstar G) as [Br [HBr Hr]].
  exists (Bs + Bf + Br).
  split.
  - lra.
  - intro N.
    rewrite GPMR22_TOTAL_PAID_PREFIX_SPLITS.
    specialize (Hs N).
    specialize (Hf N).
    specialize (Hr N).
    lra.
Qed.

(* --------------------------------------------------------------------- *)
(* GP route -> M7.                                                        *)
(* --------------------------------------------------------------------- *)

Definition ActualDiscreteGPM7 (a : nat -> R) : Prop :=
  RR.uniform_prefix_budget a.

Theorem GPMR30_GP_ROUTE_IMPLIES_DISCRETE_M7 :
  forall dstar : nat,
  forall G : GPRouteCertificate dstar,
    ActualDiscreteGPM7 (gpr_action dstar G).
Proof.
  intros dstar G.
  destruct
    (GPMR23_TOTAL_PAID_HAS_UNIFORM_PREFIX_BUDGET dstar G)
    as [B [HB Hbudget]].
  exists (4 * gpr_action dstar G 0%nat + B).
  split.
  - pose proof (gpr_action_nonnegative dstar G 0%nat) as Ha0.
    nra.
  - intro N.
    pose proof
      (GPMR21_PREFIX_ACTION_BOUND
        (gpr_action dstar G)
        (gp_total_paid G)
        (gpr_action_nonnegative dstar G)
        (GPMR12_ROUTE_CERTIFICATE_GIVES_FOUR_THREE_RECURRENCE
          dstar G)
        N) as Hprefix.
    specialize (Hbudget N).
    lra.
Qed.

(* A uniform prefix bound on the full GP action also gives the older
   two-step finite-memory GP-M7 certificate of v0.3.1. *)
Theorem GPMR31_SHIFT2_PREFIX_IDENTITY :
  forall a : nat -> R,
  forall N : nat,
    RR.prefix_sum a (S (S N))
    =
    a 0%nat + a 1%nat + RR.prefix_sum (RR.shift2 a) N.
Proof.
  intros a N.
  induction N as [|N IH].
  - simpl.
    ring.
  - change
      (RR.prefix_sum a (S (S N)) + a (S (S N))
       =
       a 0%nat + a 1%nat
       + (RR.prefix_sum (RR.shift2 a) N + RR.shift2 a N)).
    rewrite IH.
    unfold RR.shift2.
    ring.
Qed.

Theorem GPMR32_DISCRETE_M7_IMPLIES_OLD_FINITE_MEMORY_GPM7 :
  forall a : nat -> R,
    (forall n : nat, 0 <= a n) ->
    ActualDiscreteGPM7 a ->
    RR.finite_memory_gpm7 a.
Proof.
  intros a Ha [B [HB Hbudget]].
  exists B.
  split.
  - exact HB.
  - intro N.
    specialize (Hbudget (S (S N))).
    rewrite GPMR31_SHIFT2_PREFIX_IDENTITY in Hbudget.
    pose proof (Ha 0%nat) as H0.
    pose proof (Ha 1%nat) as H1.
    lra.
Qed.

Theorem GPMR33_GP_ROUTE_IMPLIES_OLD_FINITE_MEMORY_GPM7 :
  forall dstar : nat,
  forall G : GPRouteCertificate dstar,
    RR.finite_memory_gpm7 (gpr_action dstar G).
Proof.
  intros dstar G.
  apply GPMR32_DISCRETE_M7_IMPLIES_OLD_FINITE_MEMORY_GPM7.
  - exact (gpr_action_nonnegative dstar G).
  - apply GPMR30_GP_ROUTE_IMPLIES_DISCRETE_M7.
Qed.

(* Fully explicit terminal bound: the three GP payment budgets are the only
   global hypotheses above the physical parent-route construction. *)
Theorem GPMR40_EXPLICIT_GP_M7_BOUND :
  forall dstar : nat,
  forall G : GPRouteCertificate dstar,
  forall Bs Bf Br : R,
    0 <= Bs ->
    0 <= Bf ->
    0 <= Br ->
    (forall N : nat,
      RR.prefix_sum (gpr_scale_paid dstar G) N <= Bs) ->
    (forall N : nat,
      RR.prefix_sum (gpr_future_paid dstar G) N <= Bf) ->
    (forall N : nat,
      RR.prefix_sum (gpr_residual_paid dstar G) N <= Br) ->
    forall N : nat,
      RR.prefix_sum (gpr_action dstar G) N
      <=
      4 * gpr_action dstar G 0%nat + Bs + Bf + Br.
Proof.
  intros dstar G Bs Bf Br HBs HBf HBr Hs Hf Hr N.
  pose proof
    (GPMR21_PREFIX_ACTION_BOUND
      (gpr_action dstar G)
      (gp_total_paid G)
      (gpr_action_nonnegative dstar G)
      (GPMR12_ROUTE_CERTIFICATE_GIVES_FOUR_THREE_RECURRENCE
        dstar G)
      N) as Hprefix.
  rewrite GPMR22_TOTAL_PAID_PREFIX_SPLITS in Hprefix.
  specialize (Hs N).
  specialize (Hf N).
  specialize (Hr N).
  lra.
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_TO_M7_ROUTE.

Check NSE_GP_TO_M7_ROUTE.GPRouteCertificate.
Check NSE_GP_TO_M7_ROUTE.gp_total_paid.
Check NSE_GP_TO_M7_ROUTE.GPMR10_PARENT_FOREST_GIVES_STRONG_LOCAL_RECURRENCE.
Check NSE_GP_TO_M7_ROUTE.GPMR11_PARENT_FOREST_GIVES_FOUR_THREE_RECURRENCE.
Check NSE_GP_TO_M7_ROUTE.four_three_recurrence.
Check NSE_GP_TO_M7_ROUTE.GPMR20_PREFIX_INVARIANT.
Check NSE_GP_TO_M7_ROUTE.GPMR21_PREFIX_ACTION_BOUND.
Check NSE_GP_TO_M7_ROUTE.GPMR22_TOTAL_PAID_PREFIX_SPLITS.
Check NSE_GP_TO_M7_ROUTE.GPMR23_TOTAL_PAID_HAS_UNIFORM_PREFIX_BUDGET.
Check NSE_GP_TO_M7_ROUTE.ActualDiscreteGPM7.
Check NSE_GP_TO_M7_ROUTE.GPMR30_GP_ROUTE_IMPLIES_DISCRETE_M7.
Check NSE_GP_TO_M7_ROUTE.GPMR31_SHIFT2_PREFIX_IDENTITY.
Check NSE_GP_TO_M7_ROUTE.GPMR32_DISCRETE_M7_IMPLIES_OLD_FINITE_MEMORY_GPM7.
Check NSE_GP_TO_M7_ROUTE.GPMR33_GP_ROUTE_IMPLIES_OLD_FINITE_MEMORY_GPM7.
Check NSE_GP_TO_M7_ROUTE.GPMR40_EXPLICIT_GP_M7_BOUND.
