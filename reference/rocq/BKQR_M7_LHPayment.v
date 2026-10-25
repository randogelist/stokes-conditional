(* Initial-time LH energy funds a common payment budget if the actual
   canonical renewal debt is charged to increments of this same ledger.
   The local charge is an explicit analytic premise. No restarted energy
   inequality or time-integral additivity is inferred by subtraction. *)
From Stdlib Require Import Reals Lra Psatz.
Require Import LHGP_Hilbert LHGP_Evolution LHGP_Equivalence LHGP_InitialEnergy.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_direct_gp_action_m7_chain_v0_47_0.

Module BKQR_M7_LH_PAYMENT.
Module S := NSE_GP_TO_M7_SPINE.
Module A := NSE_DIRECT_GP_ACTION_M7_CHAIN.
Open Scope R_scope.

Definition leray_expenditure (td : TimeData) (nu : R) (D : R -> R) t :=
  2 * nu * TIntegral td 0 t D.

Theorem BKLP10_INITIAL_LEDGER_EXPENDITURE_BOUND :
  forall td nu T E D GoodD,
  0 <= nu -> IntegralNonnegative td ->
  (forall t, 0 <= E t) -> EnergySchedule0 td nu T E D GoodD ->
  forall t, 0 <= t <= T ->
    0 <= leray_expenditure td nu D t <= E 0.
Proof.
  intros td nu T E D GoodD Hnu HI HE
    [Hfull [HD [Hz [Hint Henergy]]]] t Ht.
  assert (Hintegral : 0 <= TIntegral td 0 t D).
  { apply HI; [lra|apply Hint; lra|]. intros r Hr; apply HD. }
  unfold leray_expenditure. split.
  - apply Rmult_le_pos; [lra|exact Hintegral].
  - pose proof (Henergy t Ht). pose proof (HE t). lra.
Qed.

Lemma paid_prefix_difference : forall (F : R -> R) (cut : nat -> R) N,
  S.paid_prefix (fun n => F (cut (Datatypes.S n)) - F (cut n)) N =
  F (cut N) - F (cut O).
Proof.
  intros F cut N. induction N as [|N IH].
  - change (0 = F (cut O) - F (cut O)). ring.
  - change (S.paid_prefix
      (fun n => F (cut (Datatypes.S n)) - F (cut n)) N +
      (F (cut (Datatypes.S N)) - F (cut N)) =
      F (cut (Datatypes.S N)) - F (cut O)).
    rewrite IH. ring.
Qed.

Theorem BKLP20_LOCAL_CHARGE_TO_COMMON_LH_PAYMENT :
  forall td nu T E D GoodD (cut : nat -> R)
    (mass : nat -> nat -> R) kappa,
  0 <= nu -> 0 <= kappa -> IntegralNonnegative td ->
  (forall t, 0 <= E t) -> EnergySchedule0 td nu T E D GoodD ->
  (forall n, 0 <= cut n <= T) ->
  (forall cutoff n, A.renewal_debt (mass cutoff) n <=
    kappa * (leray_expenditure td nu D (cut (Datatypes.S n)) -
             leray_expenditure td nu D (cut n))) ->
  0 <= kappa * E 0 /\
  forall cutoff N,
    S.paid_prefix (A.renewal_debt (mass cutoff)) N <= kappa * E 0.
Proof.
  intros td nu T E D GoodD cut mass kappa Hnu Hk HI HE HS Hcut Hcharge.
  split.
  - apply Rmult_le_pos; [exact Hk|apply HE].
  - intros cutoff N.
    pose proof (A.NSDG30_LOCAL_LEDGER_CHARGE_GIVES_PREFIX_CHARGE
      (A.renewal_debt (mass cutoff))
      (fun n => leray_expenditure td nu D (cut (Datatypes.S n)) -
                leray_expenditure td nu D (cut n)) kappa
      (Hcharge cutoff) N) as Hp.
    rewrite paid_prefix_difference in Hp.
    pose proof (BKLP10_INITIAL_LEDGER_EXPENDITURE_BOUND
      td nu T E D GoodD Hnu HI HE HS (cut N) (Hcut N)) as HN.
    pose proof (BKLP10_INITIAL_LEDGER_EXPENDITURE_BOUND
      td nu T E D GoodD Hnu HI HE HS (cut O) (Hcut O)) as H0.
    assert (Hdiff : leray_expenditure td nu D (cut N) -
      leray_expenditure td nu D (cut O) <= E 0) by lra.
    pose proof (Rmult_le_compat_l kappa _ _ Hk Hdiff). lra.
Qed.

(* This specialization fixes E to the squared norm of the given path.
   The cumulative dissipation and schedule remain the supplied LH data. *)
Theorem BKLP30_SAME_HILBERT_PATH_FUNDS_PAYMENT :
  forall hd td nu T (u : R -> HCarrier hd) D GoodD cut
    (mass : nat -> nat -> R) kappa,
  0 <= nu -> 0 <= kappa -> IntegralNonnegative td ->
  EnergySchedule0 td nu T (fun t => HNorm hd (u t)) D GoodD ->
  (forall n, 0 <= cut n <= T) ->
  (forall cutoff n, A.renewal_debt (mass cutoff) n <=
    kappa * (leray_expenditure td nu D (cut (Datatypes.S n)) -
             leray_expenditure td nu D (cut n))) ->
  0 <= kappa * HNorm hd (u 0) /\
  forall cutoff N,
    S.paid_prefix (A.renewal_debt (mass cutoff)) N <=
    kappa * HNorm hd (u 0).
Proof.
  intros hd td nu T u D GoodD cut mass kappa Hnu Hk HI HS Hcut Hcharge.
  exact (BKLP20_LOCAL_CHARGE_TO_COMMON_LH_PAYMENT td nu T
    (fun t => HNorm hd (u t)) D GoodD cut mass kappa Hnu Hk HI
    (fun t => HNorm_nonnegative hd (u t)) HS Hcut Hcharge).
Qed.

Print Assumptions BKLP20_LOCAL_CHARGE_TO_COMMON_LH_PAYMENT.
Print Assumptions BKLP30_SAME_HILBERT_PATH_FUNDS_PAYMENT.
End BKQR_M7_LH_PAYMENT.
