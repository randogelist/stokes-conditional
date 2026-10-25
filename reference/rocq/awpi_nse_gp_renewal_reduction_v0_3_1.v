From Stdlib Require Import Reals Lra Psatz Lia String.

Open Scope R_scope.

Module NSE_GP_RENEWAL_REDUCTION.

(*
  Abstract finite-memory reduction for the q=1/4 GP/DT face dynamics.

  The analytic/PDE implementation is intentionally NOT assumed here.
  This module proves only the exact scalar consequences of a two-step
  renewal inequality:

      M_{n+2} <= W_n.

  In the intended NSE use, M_n is a nonnegative critical face/action mass
  and W_n is the paid renewal in the corresponding two-step memory window.
  The substantive open PDE theorem is to construct W_n from Leray-Hopf
  dynamics and prove a Galerkin-uniform summable budget for it.
*)

Fixpoint prefix_sum (f : nat -> R) (N : nat) : R :=
  match N with
  | O => 0
  | S n => prefix_sum f n + f n
  end.

Definition shift2 (f : nat -> R) : nat -> R :=
  fun n => f (S (S n)).

Definition two_step_renewal_bound
  (M W : nat -> R) : Prop :=
  forall n : nat, M (S (S n)) <= W n.

Definition nonnegative_sequence (f : nat -> R) : Prop :=
  forall n : nat, 0 <= f n.

Definition uniform_prefix_budget (f : nat -> R) : Prop :=
  exists C : R, 0 <= C /\ forall N : nat, prefix_sum f N <= C.

Definition finite_memory_gpm7 (M : nat -> R) : Prop :=
  uniform_prefix_budget (shift2 M).

Theorem GPR00_PREFIX_MONOTONE_POINTWISE :
  forall f g : nat -> R,
    (forall n, f n <= g n) ->
    forall N, prefix_sum f N <= prefix_sum g N.
Proof.
  intros f g Hfg N.
  induction N as [|N IHN].
  - simpl; lra.
  - simpl.
    specialize (Hfg N).
    lra.
Qed.

Theorem GPR01_TWO_STEP_PREFIX_REDUCTION :
  forall M W : nat -> R,
    two_step_renewal_bound M W ->
    forall N : nat,
      prefix_sum (shift2 M) N <= prefix_sum W N.
Proof.
  intros M W Hrenew N.
  apply GPR00_PREFIX_MONOTONE_POINTWISE.
  intro n.
  unfold shift2.
  apply Hrenew.
Qed.

Theorem GPR02_WINDOW_BUDGET_IMPLIES_GPM7 :
  forall M W : nat -> R,
    two_step_renewal_bound M W ->
    uniform_prefix_budget W ->
    finite_memory_gpm7 M.
Proof.
  intros M W Hrenew [C [HC Hbudget]].
  exists C.
  split; [exact HC|].
  intro N.
  eapply Rle_trans.
  - apply GPR01_TWO_STEP_PREFIX_REDUCTION; exact Hrenew.
  - apply Hbudget.
Qed.

(* If one resolves the two-step window W_n into two adjacent renewal costs
   R_n + R_{n+1}, then persistence at time n+2 forces at least one of those
   adjacent costs to be large. *)
Definition adjacent_window (Rcost : nat -> R) : nat -> R :=
  fun n => Rcost n + Rcost (S n).

Theorem GPR10_PERSISTENCE_FORCES_ONE_LARGE_RENEWAL :
  forall M Rcost : nat -> R,
  forall n : nat,
  forall m0 : R,
    two_step_renewal_bound M (adjacent_window Rcost) ->
    m0 <= M (S (S n)) ->
    Rcost n < m0 / 2 ->
    m0 / 2 <= Rcost (S n).
Proof.
  intros M Rcost n m0 Hrenew Hmass Hsmall.
  specialize (Hrenew n).
  unfold adjacent_window in Hrenew.
  lra.
Qed.

Theorem GPR11_TWO_SMALL_RENEWALS_KILL_PERSISTENCE :
  forall M Rcost : nat -> R,
  forall n : nat,
  forall eps : R,
    two_step_renewal_bound M (adjacent_window Rcost) ->
    Rcost n <= eps ->
    Rcost (S n) <= eps ->
    M (S (S n)) <= 2 * eps.
Proof.
  intros M Rcost n eps Hrenew Hn HSn.
  specialize (Hrenew n).
  unfold adjacent_window in Hrenew.
  lra.
Qed.

(* A local payment estimate W_n <= C P_n plus a finite total paid budget
   is sufficient for GP-M7.  This is the exact formal interface at which
   the remaining NSE analysis should enter. *)
Definition local_payment
  (W Paid : nat -> R) (C : R) : Prop :=
  forall n : nat, W n <= C * Paid n.

Theorem GPR20_PREFIX_PAYMENT :
  forall W Paid : nat -> R,
  forall C : R,
    0 <= C ->
    local_payment W Paid C ->
    forall N : nat,
      prefix_sum W N <= C * prefix_sum Paid N.
Proof.
  intros W Paid C HC Hpay N.
  induction N as [|N IHN].
  - simpl; nra.
  - simpl.
    specialize (Hpay N).
    nra.
Qed.

Theorem GPR21_LOCAL_PAYMENT_PLUS_BUDGET_IMPLIES_GPM7 :
  forall M W Paid : nat -> R,
  forall C : R,
    two_step_renewal_bound M W ->
    0 <= C ->
    local_payment W Paid C ->
    uniform_prefix_budget Paid ->
    finite_memory_gpm7 M.
Proof.
  intros M W Paid C Hrenew HC Hpay [B [HB Hbudget]].
  exists (C * B).
  split.
  - nra.
  - intro N.
    eapply Rle_trans.
    + apply GPR01_TWO_STEP_PREFIX_REDUCTION; exact Hrenew.
    + eapply Rle_trans.
      * apply GPR20_PREFIX_PAYMENT.
        -- exact HC.
        -- exact Hpay.
      * specialize (Hbudget N).
        apply Rmult_le_compat_l; assumption.
Qed.

(* Logical overlay: once an implementation identifies finite_memory_gpm7
   with the concrete GP-M7 certificate consumed by the already-checked
   Serrin bridge, no new analytic argument is required above this point. *)
Section LOGICAL_OVERLAY.

  Context {Velocity : Type}.
  Variable LerayHopfT3 : Velocity -> Prop.
  Variable RenewalCertificate : Velocity -> Prop.
  Variable GPM7Certificate : Velocity -> Prop.
  Variable Serrin46 : Velocity -> Prop.

  Variable RenewalToGPM7 :
    forall v : Velocity,
      LerayHopfT3 v -> RenewalCertificate v -> GPM7Certificate v.

  Variable GPM7ToSerrin46 :
    forall v : Velocity,
      LerayHopfT3 v -> GPM7Certificate v -> Serrin46 v.

  Theorem GPR30_RENEWAL_TO_SERRIN46 :
    forall v : Velocity,
      LerayHopfT3 v -> RenewalCertificate v -> Serrin46 v.
  Proof.
    intros v Hlh Hrenew.
    apply (GPM7ToSerrin46 v Hlh).
    exact (RenewalToGPM7 v Hlh Hrenew).
  Qed.

End LOGICAL_OVERLAY.

Definition STATUS : string :=
  "NSE_GP_TWO_STEP_RENEWAL_REDUCTION_ANCHOR_NO_ADMITTED"%string.

End NSE_GP_RENEWAL_REDUCTION.

Print Assumptions NSE_GP_RENEWAL_REDUCTION.GPR02_WINDOW_BUDGET_IMPLIES_GPM7.
Print Assumptions NSE_GP_RENEWAL_REDUCTION.GPR10_PERSISTENCE_FORCES_ONE_LARGE_RENEWAL.
Print Assumptions NSE_GP_RENEWAL_REDUCTION.GPR21_LOCAL_PAYMENT_PLUS_BUDGET_IMPLIES_GPM7.
Print Assumptions NSE_GP_RENEWAL_REDUCTION.GPR30_RENEWAL_TO_SERRIN46.
