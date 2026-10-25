From Stdlib Require Import Reals Lra Psatz String.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_gp_gram_geometry_v0_49_3.
Require Import awpi_nse_native_kq_ladder_v0_49_3.
Require Import awpi_nse_schur_action_ledger_v0_49_3.
Require Import awpi_nse_gram_m7_energy_join_v0_49_3.

Module NSE_GP_KQ_GRAM_RENEWAL.
Import NSE_KQ_FINITE_ALGEBRA NSE_GP_GRAM_GEOMETRY.
Open Scope R_scope.

Definition zero_vec : Vec := fun _ => 0.
Definition e0 : Vec := fun i => match i with O => 1 | _ => 0 end.
Definition e1 : Vec := fun i => match i with S O => 1 | _ => 0 end.

Example NSGK00_ZERO_NULL_DIRECTIONS_ARE_ALLOWED : forall f,
  dot 2 e1 f * dot 2 e1 f <= norm2 2 e1 * reduced_capacity 2 f zero_vec zero_vec.
Proof.
  intro f.
  (* Fix the concrete dot-product goal before using real zero laws. *)
  assert (Horth : dot 2 e1 zero_vec = 0).
  { change ((0 + 0 * 0) + 1 * 0 = 0).
    now rewrite !Rmult_0_r, !Rplus_0_r. }
  exact (NSGG20_RANK_SAFE_SCHUR_ACTION_BOUND
    2 e1 f zero_vec zero_vec Horth Horth).
Qed.

Example NSGK01_DEPENDENT_NULL_DIRECTIONS_ARE_ALLOWED : forall f,
  dot 2 e1 f * dot 2 e1 f <= norm2 2 e1 * reduced_capacity 2 f e0 (scale 2 e0).
Proof.
  intro f.
  assert (Horth : dot 2 e1 e0 = 0).
  { change ((0 + 0 * 1) + 1 * 0 = 0).
    now rewrite Rmult_0_l, Rmult_0_r, !Rplus_0_r. }
  (* Use the proved scaling identity rather than reducing the scaled vector. *)
  assert (Hscaled : dot 2 e1 (scale 2 e0) = 0).
  { now rewrite dot_scale_r, Horth, Rmult_0_r. }
  exact (NSGG20_RANK_SAFE_SCHUR_ACTION_BOUND
    2 e1 f e0 (scale 2 e0) Horth Hscaled).
Qed.

Definition STATUS : string :=
  "NSE_GP_KQ_GRAM_RENEWAL_V0_49_3_CONDITIONAL_NO_ADMITTED"%string.
End NSE_GP_KQ_GRAM_RENEWAL.

(* Proof dependency audit.  The standard real-number foundations remain
   visible here.  Quantified analytic premises are displayed separately. *)
Print Assumptions NSE_GP_GRAM_GEOMETRY.NSGG10_RANK_SAFE_TWO_DIRECTION_ORTHOGONALITY.
Print Assumptions NSE_GP_GRAM_GEOMETRY.NSGG15_REDUCED_CAPACITY_IS_MINIMAL.
Print Assumptions NSE_GP_GRAM_GEOMETRY.NSGG20_RANK_SAFE_SCHUR_ACTION_BOUND.
Print Assumptions NSE_GP_GRAM_GEOMETRY.NSGG30_CONCRETE_GRAM4_IS_PSD.
Print Assumptions NSE_GP_GRAM_GEOMETRY.NSGG42_GP_PRESERVES_REDUCED_CAPACITY.
Print Assumptions NSE_NATIVE_KQ_LADDER.NSKL11_FINITE_LADDER_NO_REUSE_BUDGET.
Print Assumptions NSE_NATIVE_KQ_LADDER.NSKL21_CANDIDATE_F_TENSOR_COVARIANCE.
Print Assumptions NSE_SCHUR_ACTION_LEDGER.NSAR01_MOVING_GP_RENEWAL_DRIFT_CANCELLATION.
Print Assumptions NSE_SCHUR_ACTION_LEDGER.NSAR40_FINITE_GRAM_LEDGER_ACTION_BOUND.
Print Assumptions NSE_SCHUR_ACTION_LEDGER.NSAR90_LEDGER_WITHOUT_CAPACITY_CAN_HAVE_UNBOUNDED_ACTION.
Print Assumptions NSE_GRAM_M7_ENERGY_JOIN.NSGE90_GP_KQ_GRAM_M7_CRITICAL_TARGET.

Print NSE_SCHUR_ACTION_LEDGER.IntegratedGramLedger.
Print NSE_SCHUR_ACTION_LEDGER.ReducedCapacityBound.
Print NSE_GRAM_M7_ENERGY_JOIN.ActualMassPrefixDominated.
Check NSE_GRAM_M7_ENERGY_JOIN.NSGE20_CAPACITY_TO_UNIFORM_CRITICAL_ENERGY.
Check NSE_GRAM_M7_ENERGY_JOIN.NSGE90_GP_KQ_GRAM_M7_CRITICAL_TARGET.
