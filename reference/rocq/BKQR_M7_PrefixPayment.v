From Stdlib Require Import Reals Lra Psatz.
Require Import awpi_nse_gp_quarter_shift_firewall_v0_13_6.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_direct_gp_action_m7_chain_v0_47_0.
Require Import BKQR_M7_ActionCells.

Module BKQR_M7_PREFIX_PAYMENT.
Module FW := NSE_GP_QUARTER_SHIFT_FIREWALL.
Module GM := NSE_GP_TO_M7_SPINE.
Module DG := NSE_DIRECT_GP_ACTION_M7_CHAIN.
Module AC := BKQR_M7_ACTION_CELLS.
Open Scope R_scope.

(* Payment may use a subcritical fraction of the accumulated action.
   This is an explicit sufficient estimate, not a consequence asserted
   for every Leray--Hopf path.  The masses and their canonical debt are
   unchanged from the existing injection. *)
Definition prefix_action_budget (Seed Paid theta : R) : R :=
  (Seed + Paid) / (96 / 605 - theta).

Definition SubcriticalPrefixPayment (mass : nat -> nat -> R)
    (Seed Paid theta : R) : Prop :=
  0 <= Seed /\ 0 <= Paid /\ 0 <= theta < 96 / 605 /\
  (forall eps, mass eps O <= Seed) /\
  (forall eps k, GM.paid_prefix (DG.renewal_debt (mass eps)) k
    <= Paid + theta * GM.resistant_prefix (mass eps) k).

Lemma PREFIX_ACTION_BUDGET_NONNEG : forall Seed Paid theta,
  0 <= Seed -> 0 <= Paid -> theta < 96 / 605 ->
  0 <= prefix_action_budget Seed Paid theta.
Proof.
  intros Seed Paid theta HS HP Htheta.
  unfold prefix_action_budget, Rdiv. apply Rmult_le_pos; [lra|].
  apply Rlt_le, Rinv_0_lt_compat. lra.
Qed.

Lemma PREFIX_ACTION_BUDGET_IDENTITY : forall Seed Paid theta,
  theta < 96 / 605 ->
  (96 / 605 - theta) * prefix_action_budget Seed Paid theta = Seed + Paid.
Proof.
  intros Seed Paid theta Htheta. unfold prefix_action_budget. field. lra.
Qed.

Theorem PREFIX_PAYMENT_SHARP_BOUND : forall mass Seed Paid theta,
  (forall eps n, 0 <= mass eps n) ->
  SubcriticalPrefixPayment mass Seed Paid theta ->
  forall eps k, GM.resistant_prefix (mass eps) k
    <= prefix_action_budget Seed Paid theta.
Proof.
  intros mass Seed Paid theta Hmass [HS [HP [[Ht0 Ht] [Hseed Hpaid]]]] eps k.
  destruct (DG.NSDG12_CANONICAL_DEBT_GIVES_RENEWAL (mass eps) (Hmass eps))
    as [HM [HD Hstep]].
  pose proof (FW.NSQF30_EXACT_509_OVER_605_PREFIX_INVARIANT
    (mass eps) (DG.renewal_debt (mass eps)) HM HD Hstep k) as Hinv.
  pose proof (Hmass eps k).
  pose proof (Hseed eps).
  pose proof (Hpaid eps k).
  pose proof (PREFIX_ACTION_BUDGET_IDENTITY Seed Paid theta Ht) as Hid.
  assert (Hpositive : 0 < 96 / 605 - theta) by lra.
  change (96 * GM.resistant_prefix (mass eps) k + 605 * mass eps k <=
    605 * mass eps O + 605 * GM.paid_prefix (DG.renewal_debt (mass eps)) k) in Hinv.
  nra.
Qed.

Theorem PREFIX_PAYMENT_CONSTRUCTS_COMMON_DEBT_BUDGET : forall mass Seed Paid theta,
  (forall eps n, 0 <= mass eps n) ->
  SubcriticalPrefixPayment mass Seed Paid theta ->
  forall eps k, GM.paid_prefix (DG.renewal_debt (mass eps)) k
    <= Paid + theta * prefix_action_budget Seed Paid theta.
Proof.
  intros mass Seed Paid theta Hmass Hpayment eps k.
  pose proof (PREFIX_PAYMENT_SHARP_BOUND mass Seed Paid theta Hmass Hpayment eps k) as Hbound.
  destruct Hpayment as [HS [HP [[Ht0 Ht] [Hseed Hpaid]]]].
  specialize (Hpaid eps k). nra.
Qed.

Theorem PREFIX_PAYMENT_GIVES_SEQUENCE_M7 : forall mass Seed Paid theta,
  (forall eps n, 0 <= mass eps n) ->
  SubcriticalPrefixPayment mass Seed Paid theta ->
  forall eps, GM.GPSequenceM7 (mass eps).
Proof.
  intros mass Seed Paid theta Hmass Hpayment eps.
  exists (prefix_action_budget Seed Paid theta). split.
  - destruct Hpayment as [HS [HP [[Ht0 Ht] _]]].
    apply PREFIX_ACTION_BUDGET_NONNEG; assumption.
  - exact (PREFIX_PAYMENT_SHARP_BOUND mass Seed Paid theta Hmass Hpayment eps).
Qed.

Theorem ABSORBED_PAYMENT_RETAINS_SHARP_ACTION_BUDGET : forall Seed Paid theta,
  theta < 96 / 605 ->
  AC.sharp_action_budget Seed (Paid + theta * prefix_action_budget Seed Paid theta)
    = prefix_action_budget Seed Paid theta.
Proof.
  intros Seed Paid theta Htheta.
  pose proof (PREFIX_ACTION_BUDGET_IDENTITY Seed Paid theta Htheta).
  unfold AC.sharp_action_budget. lra.
Qed.

Theorem PREFIX_PAYMENT_CONSTRUCTS_COMMON_ACTION_PAYMENT : forall T C cut Seed Paid theta,
  AC.CofinalActionCuts T cut -> AC.MonotoneCumulativeAction T C ->
  SubcriticalPrefixPayment (AC.actual_action_mass C cut) Seed Paid theta ->
  AC.CommonActionPayment C cut Seed
    (Paid + theta * prefix_action_budget Seed Paid theta).
Proof.
  intros T C cut Seed Paid theta Hcuts Haction Hpayment.
  pose proof (AC.ACTION_CELL_NONNEG T C cut Hcuts Haction) as Hmass.
  pose proof (PREFIX_PAYMENT_CONSTRUCTS_COMMON_DEBT_BUDGET
    (AC.actual_action_mass C cut) Seed Paid theta Hmass Hpayment) as Hdebt.
  destruct Hpayment as [HS [HP [[Ht0 Ht] [Hseed Hpaid]]]].
  pose proof (PREFIX_ACTION_BUDGET_NONNEG Seed Paid theta HS HP Ht) as HB.
  split; [exact HS|]. split; [nra|]. split; [exact Hseed|].
  exact Hdebt.
Qed.

Theorem PREFIX_PAYMENT_GIVES_ACTUAL_M7 : forall T C cut Seed Paid theta,
  AC.CofinalActionCuts T cut -> AC.MonotoneCumulativeAction T C ->
  SubcriticalPrefixPayment (AC.actual_action_mass C cut) Seed Paid theta ->
  forall eps, GM.GPSequenceM7 (AC.actual_action_mass C cut eps).
Proof.
  intros T C cut Seed Paid theta Hcuts Haction Hpayment.
  exact (PREFIX_PAYMENT_GIVES_SEQUENCE_M7 (AC.actual_action_mass C cut) Seed Paid theta
    (AC.ACTION_CELL_NONNEG T C cut Hcuts Haction) Hpayment).
Qed.

Theorem PREFIX_PAYMENT_GIVES_UNIFORM_ACTUAL_ACTION : forall T C cut Seed Paid theta,
  AC.CofinalActionCuts T cut -> AC.MonotoneCumulativeAction T C ->
  SubcriticalPrefixPayment (AC.actual_action_mass C cut) Seed Paid theta ->
  forall eps t, 0 <= t < T -> C eps t <= prefix_action_budget Seed Paid theta.
Proof.
  intros T C cut Seed Paid theta Hcuts Haction Hpayment eps t Ht.
  destruct (AC.ACTION_CELLS_COVER_THE_SAME_ACTION T C cut Hcuts Haction eps t Ht)
    as [k Hcover].
  pose proof (PREFIX_PAYMENT_SHARP_BOUND (AC.actual_action_mass C cut) Seed Paid theta
    (AC.ACTION_CELL_NONNEG T C cut Hcuts Haction) Hpayment eps k). lra.
Qed.

(* A prefix charge to one globally bounded same-path ledger suffices.
   No local cell charge, restart inequality, or ledger monotonicity is
   needed here.  Its bound and ownership remain the caller's evidence. *)
Theorem LEDGER_PREFIX_CHARGE_GIVES_SUBCRITICAL_PAYMENT :
  forall T C cut (L : nat -> R -> R) Seed P0 kappa E0 theta,
  AC.CofinalActionCuts T cut ->
  0 <= Seed -> 0 <= P0 -> 0 <= kappa -> 0 <= E0 -> 0 <= theta < 96 / 605 ->
  (forall eps, AC.actual_action_mass C cut eps O <= Seed) ->
  (forall eps t, 0 <= t < T -> L eps t <= E0) ->
  (forall eps k, GM.paid_prefix (AC.canonical_action_debt C cut eps) k
    <= P0 + kappa * L eps (cut k)
       + theta * GM.resistant_prefix (AC.actual_action_mass C cut eps) k) ->
  SubcriticalPrefixPayment (AC.actual_action_mass C cut) Seed (P0 + kappa * E0) theta.
Proof.
  intros T C cut L Seed P0 kappa E0 theta Hcuts HS HP Hk HE Htheta Hseed HL Hcharge.
  split; [exact HS|]. split; [nra|]. split; [exact Htheta|].
  split; [exact Hseed|]. intros eps k.
  pose proof (HL eps (cut k) (AC.cuts_inside T cut Hcuts k)).
  specialize (Hcharge eps k). unfold AC.canonical_action_debt in Hcharge. nra.
Qed.

Theorem LEDGER_PREFIX_CHARGE_CONSTRUCTS_COMMON_ACTION_PAYMENT :
  forall T C cut (L : nat -> R -> R) Seed P0 kappa E0 theta,
  AC.CofinalActionCuts T cut -> AC.MonotoneCumulativeAction T C ->
  0 <= Seed -> 0 <= P0 -> 0 <= kappa -> 0 <= E0 -> 0 <= theta < 96 / 605 ->
  (forall eps, AC.actual_action_mass C cut eps O <= Seed) ->
  (forall eps t, 0 <= t < T -> L eps t <= E0) ->
  (forall eps k, GM.paid_prefix (AC.canonical_action_debt C cut eps) k
    <= P0 + kappa * L eps (cut k)
       + theta * GM.resistant_prefix (AC.actual_action_mass C cut eps) k) ->
  AC.CommonActionPayment C cut Seed
    (P0 + kappa * E0 + theta * prefix_action_budget Seed (P0 + kappa * E0) theta).
Proof.
  intros T C cut L Seed P0 kappa E0 theta Hcuts Haction HS HP Hk HE Htheta Hseed HL Hcharge.
  apply (PREFIX_PAYMENT_CONSTRUCTS_COMMON_ACTION_PAYMENT T C cut Seed
    (P0 + kappa * E0) theta Hcuts Haction).
  exact (LEDGER_PREFIX_CHARGE_GIVES_SUBCRITICAL_PAYMENT T C cut L Seed P0 kappa E0 theta
    Hcuts HS HP Hk HE Htheta Hseed HL Hcharge).
Qed.

Theorem LEDGER_PREFIX_CHARGE_GIVES_UNIFORM_ACTUAL_ACTION :
  forall T C cut (L : nat -> R -> R) Seed P0 kappa E0 theta,
  AC.CofinalActionCuts T cut -> AC.MonotoneCumulativeAction T C ->
  0 <= Seed -> 0 <= P0 -> 0 <= kappa -> 0 <= E0 -> 0 <= theta < 96 / 605 ->
  (forall eps, AC.actual_action_mass C cut eps O <= Seed) ->
  (forall eps t, 0 <= t < T -> L eps t <= E0) ->
  (forall eps k, GM.paid_prefix (AC.canonical_action_debt C cut eps) k
    <= P0 + kappa * L eps (cut k)
       + theta * GM.resistant_prefix (AC.actual_action_mass C cut eps) k) ->
  forall eps t, 0 <= t < T ->
    C eps t <= prefix_action_budget Seed (P0 + kappa * E0) theta.
Proof.
  intros T C cut L Seed P0 kappa E0 theta Hcuts Haction HS HP Hk HE Htheta Hseed HL Hcharge.
  apply (PREFIX_PAYMENT_GIVES_UNIFORM_ACTUAL_ACTION T C cut Seed
    (P0 + kappa * E0) theta Hcuts Haction).
  exact (LEDGER_PREFIX_CHARGE_GIVES_SUBCRITICAL_PAYMENT T C cut L Seed P0 kappa E0 theta
    Hcuts HS HP Hk HE Htheta Hseed HL Hcharge).
Qed.

(* Sharpness of the strict absorption margin for this scalar criterion.
   This constant sequence is not asserted to be an NSE action sequence. *)
Definition threshold_constant_mass (_ _ : nat) : R := 1.

Lemma THRESHOLD_CONSTANT_DEBT : forall eps n,
  DG.renewal_debt (threshold_constant_mass eps) n = 96 / 605.
Proof.
  intros eps n. unfold DG.renewal_debt, threshold_constant_mass.
  rewrite Rmax_right by lra. lra.
Qed.

Lemma THRESHOLD_CONSTANT_PREFIX : forall eps k,
  GM.resistant_prefix (threshold_constant_mass eps) k = INR k.
Proof.
  intros eps k. induction k as [|k IH].
  - reflexivity.
  - change (GM.resistant_prefix (threshold_constant_mass eps) k + 1 = INR (S k)).
    rewrite IH, S_INR. ring.
Qed.

Theorem THRESHOLD_CONSTANT_EXACT_PREFIX_CHARGE : forall eps k,
  GM.paid_prefix (DG.renewal_debt (threshold_constant_mass eps)) k
    = 0 + (96 / 605) * GM.resistant_prefix (threshold_constant_mass eps) k.
Proof.
  intros eps k. induction k as [|k IH].
  - change (0 = 0 + (96 / 605) * 0). ring.
  - change (GM.paid_prefix (DG.renewal_debt (threshold_constant_mass eps)) k +
      DG.renewal_debt (threshold_constant_mass eps) k =
      0 + (96 / 605) * (GM.resistant_prefix (threshold_constant_mass eps) k + 1)).
    rewrite IH, THRESHOLD_CONSTANT_DEBT. ring.
Qed.

Theorem THRESHOLD_CONSTANT_PREFIX_UNBOUNDED : forall eps B,
  exists k, B < GM.resistant_prefix (threshold_constant_mass eps) k.
Proof.
  intros eps B. destruct (INR_unbounded B) as [k Hk].
  exists k. rewrite THRESHOLD_CONSTANT_PREFIX. exact Hk.
Qed.

Theorem STRICT_PAYMENT_MARGIN_CANNOT_BE_DROPPED :
  (forall eps n, 0 <= threshold_constant_mass eps n) /\
  (forall eps, threshold_constant_mass eps O <= 1) /\
  (forall eps k, GM.paid_prefix (DG.renewal_debt (threshold_constant_mass eps)) k
    = 0 + (96 / 605) * GM.resistant_prefix (threshold_constant_mass eps) k) /\
  (forall eps, ~ GM.GPSequenceM7 (threshold_constant_mass eps)).
Proof.
  split; [intros; unfold threshold_constant_mass; lra|].
  split; [intros; unfold threshold_constant_mass; lra|].
  split; [exact THRESHOLD_CONSTANT_EXACT_PREFIX_CHARGE|].
  intros eps [B [HB Hprefix]].
  destruct (THRESHOLD_CONSTANT_PREFIX_UNBOUNDED eps B) as [k Hk].
  specialize (Hprefix k). lra.
Qed.

End BKQR_M7_PREFIX_PAYMENT.

Print Assumptions BKQR_M7_PREFIX_PAYMENT.PREFIX_PAYMENT_SHARP_BOUND.
Print Assumptions BKQR_M7_PREFIX_PAYMENT.PREFIX_PAYMENT_CONSTRUCTS_COMMON_ACTION_PAYMENT.
Print Assumptions BKQR_M7_PREFIX_PAYMENT.PREFIX_PAYMENT_GIVES_ACTUAL_M7.
Print Assumptions BKQR_M7_PREFIX_PAYMENT.PREFIX_PAYMENT_GIVES_UNIFORM_ACTUAL_ACTION.
Print Assumptions BKQR_M7_PREFIX_PAYMENT.LEDGER_PREFIX_CHARGE_CONSTRUCTS_COMMON_ACTION_PAYMENT.
Print Assumptions BKQR_M7_PREFIX_PAYMENT.LEDGER_PREFIX_CHARGE_GIVES_UNIFORM_ACTUAL_ACTION.
Print Assumptions BKQR_M7_PREFIX_PAYMENT.STRICT_PAYMENT_MARGIN_CANNOT_BE_DROPPED.
