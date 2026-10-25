From Stdlib Require Import Reals Lra Lia Psatz.
Require Import awpi_nse_direct_gp_action_m7_chain_v0_47_0.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module BKQR_M7_ACTION_CELLS.
Module DG := NSE_DIRECT_GP_ACTION_M7_CHAIN.
Module GM := NSE_GP_TO_M7_SPINE.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

(* The time domain is genuinely half open.  Monotonicity outside it is
   neither needed nor postulated.  The regularization index is nat. *)
Definition OpenTime (T : R) := {t : R | 0 <= t < T}.

Record CofinalActionCuts (T : R) (cut : nat -> R) : Prop := {
  cuts_zero : cut O = 0;
  cuts_inside : forall N, 0 <= cut N < T;
  cuts_ordered : forall N, cut N <= cut (Datatypes.S N);
  cuts_cofinal : forall t, 0 <= t < T -> exists N, t <= cut N
}.

Record MonotoneCumulativeAction (T : R) (C : nat -> R -> R) : Prop := {
  action_zero : forall eps, C eps 0 = 0;
  action_monotone : forall eps s t,
    0 <= s -> s <= t -> t < T -> C eps s <= C eps t
}.

Definition canonical_cut (T : R) (n : nat) : R :=
  T * (1 - / INR (Datatypes.S n)).

Theorem CANONICAL_CUTS_ARE_COFINAL : forall T,
  0 < T -> CofinalActionCuts T (canonical_cut T).
Proof.
  intros T HT. constructor.
  - unfold canonical_cut. simpl. rewrite Rinv_1. ring.
  - intro N. unfold canonical_cut.
    assert (Hd : 1 <= INR (Datatypes.S N)).
    { change (INR 1 <= INR (Datatypes.S N)). apply le_INR. lia. }
    assert (Hi : 0 < / INR (Datatypes.S N)) by
      (apply Rinv_0_lt_compat; lra).
    pose proof (Rinv_le_contravar 1 (INR (Datatypes.S N)) ltac:(lra) Hd) as Hle.
    rewrite Rinv_1 in Hle. split; nra.
  - intro N. unfold canonical_cut.
    assert (Hd : 0 < INR (Datatypes.S N)).
    { apply lt_0_INR. lia. }
    assert (Horder : INR (Datatypes.S N) <= INR (Datatypes.S (Datatypes.S N))).
    { apply le_INR. lia. }
    pose proof (Rinv_le_contravar _ _ Hd Horder). nra.
  - intros t Ht.
    assert (Heps : 0 < (T - t) / T) by (apply Rdiv_lt_0_compat; lra).
    destruct (archimed_cor1 ((T - t) / T) Heps) as [N [HN HNpos]].
    exists N. unfold canonical_cut.
    assert (Hd : 0 < INR N) by (apply lt_0_INR; exact HNpos).
    assert (Horder : INR N <= INR (Datatypes.S N)) by (apply le_INR; lia).
    pose proof (Rinv_le_contravar _ _ Hd Horder) as Hinv.
    assert (Hsmall : / INR (Datatypes.S N) < (T - t) / T) by lra.
    pose proof (Rmult_lt_compat_l T _ _ HT Hsmall) as Hmul.
    replace (T * ((T - t) / T)) with (T - t) in Hmul by (field; lra).
    nra.
Qed.

Definition actual_action_mass (C : nat -> R -> R) (cut : nat -> R)
    (eps n : nat) : R := DG.action_increment C cut eps n.

Definition canonical_action_debt (C : nat -> R -> R) (cut : nat -> R)
    (eps : nat) : nat -> R := DG.renewal_debt (actual_action_mass C cut eps).

Definition sharp_action_budget (Seed Paid : R) : R :=
  605 * (Seed + Paid) / 96.

Definition CommonActionPayment (C : nat -> R -> R) (cut : nat -> R)
    (Seed Paid : R) : Prop :=
  0 <= Seed /\ 0 <= Paid /\
  (forall eps, actual_action_mass C cut eps O <= Seed) /\
  (forall eps N, GM.paid_prefix (canonical_action_debt C cut eps) N <= Paid).

Definition UniformOpenActionBound (T : R) (C : nat -> R -> R) : Prop :=
  exists B, 0 <= B /\ forall eps t, 0 <= t < T -> C eps t <= B.

Lemma ACTION_CUMULATIVE_NONNEG : forall T C,
  0 < T -> MonotoneCumulativeAction T C ->
  forall eps t, 0 <= t < T -> 0 <= C eps t.
Proof.
  intros T C HT [Hzero Hmono] eps t Ht.
  pose proof (Hmono eps 0 t (Rle_refl 0) (proj1 Ht) (proj2 Ht)) as H.
  rewrite Hzero in H. exact H.
Qed.

Lemma ACTION_CELL_NONNEG : forall T C cut,
  CofinalActionCuts T cut -> MonotoneCumulativeAction T C ->
  forall eps n, 0 <= actual_action_mass C cut eps n.
Proof.
  intros T C cut [_ Hinside Horder _] [_ Hmono] eps n.
  unfold actual_action_mass, DG.action_increment.
  pose proof (Hmono eps (cut n) (cut (Datatypes.S n))
    (proj1 (Hinside n)) (Horder n) (proj2 (Hinside (Datatypes.S n)))).
  lra.
Qed.

Theorem ACTION_CELL_PREFIX_EXACT : forall T C cut,
  CofinalActionCuts T cut -> MonotoneCumulativeAction T C ->
  forall eps N, GM.resistant_prefix (actual_action_mass C cut eps) N = C eps (cut N).
Proof.
  intros T C cut Hcuts Haction eps N.
  unfold actual_action_mass.
  apply DG.NSDG01_ACTION_PREFIX_TELESCOPES.
  intro r. rewrite (cuts_zero T cut Hcuts).
  apply (action_zero T C Haction).
Qed.

Theorem ACTION_CELLS_COVER_THE_SAME_ACTION : forall T C cut,
  CofinalActionCuts T cut -> MonotoneCumulativeAction T C ->
  forall eps t, 0 <= t < T ->
    exists N, C eps t <= GM.resistant_prefix (actual_action_mass C cut eps) N.
Proof.
  intros T C cut Hcuts Haction eps t Ht.
  destruct (cuts_cofinal T cut Hcuts t Ht) as [N HN].
  exists N. rewrite (ACTION_CELL_PREFIX_EXACT T C cut Hcuts Haction eps N).
  apply (action_monotone T C Haction); try lra.
  exact (proj2 (cuts_inside T cut Hcuts N)).
Qed.

Theorem ACTION_CELLS_CONSTRUCT_M7_REALIZATION : forall T C cut,
  CofinalActionCuts T cut -> MonotoneCumulativeAction T C ->
  forall eps, CE.M7ActionCostRealization (OpenTime T)
    (actual_action_mass C cut eps) (fun t => C eps (proj1_sig t)).
Proof.
  intros T C cut Hcuts Haction eps [t Ht].
  exact (ACTION_CELLS_COVER_THE_SAME_ACTION T C cut Hcuts Haction eps t Ht).
Qed.

Theorem COMMON_PAYMENT_BOUNDS_ACTUAL_PREFIXES : forall T C cut Seed Paid,
  CofinalActionCuts T cut -> MonotoneCumulativeAction T C ->
  CommonActionPayment C cut Seed Paid ->
  forall eps N, GM.resistant_prefix (actual_action_mass C cut eps) N
    <= sharp_action_budget Seed Paid.
Proof.
  intros T C cut Seed Paid Hcuts Haction [HSeed [HPaid [Hseed Hpaid]]] eps N.
  pose proof (DG.NSDG20_SHARP_SEED_AND_PAYMENT_BOUND
    (actual_action_mass C cut eps) Seed Paid
    (ACTION_CELL_NONNEG T C cut Hcuts Haction eps)
    (Hseed eps) HPaid (Hpaid eps) N) as H.
  unfold sharp_action_budget. lra.
Qed.

Theorem COMMON_PAYMENT_GIVES_ACTUAL_M7 : forall T C cut Seed Paid,
  CofinalActionCuts T cut -> MonotoneCumulativeAction T C ->
  CommonActionPayment C cut Seed Paid ->
  forall eps, GM.GPSequenceM7 (actual_action_mass C cut eps).
Proof.
  intros T C cut Seed Paid Hcuts Haction Hpayment eps.
  exists (sharp_action_budget Seed Paid). split.
  - destruct Hpayment as [HSeed [HPaid _]]. unfold sharp_action_budget. lra.
  - exact (COMMON_PAYMENT_BOUNDS_ACTUAL_PREFIXES T C cut Seed Paid
      Hcuts Haction Hpayment eps).
Qed.

Theorem COMMON_PAYMENT_GIVES_UNIFORM_ACTUAL_ACTION : forall T C cut Seed Paid,
  CofinalActionCuts T cut -> MonotoneCumulativeAction T C ->
  CommonActionPayment C cut Seed Paid ->
  forall eps t, 0 <= t < T -> C eps t <= sharp_action_budget Seed Paid.
Proof.
  intros T C cut Seed Paid Hcuts Haction Hpayment eps t Ht.
  destruct (ACTION_CELLS_COVER_THE_SAME_ACTION T C cut Hcuts Haction eps t Ht)
    as [N Hcover].
  pose proof (COMMON_PAYMENT_BOUNDS_ACTUAL_PREFIXES T C cut Seed Paid
    Hcuts Haction Hpayment eps N). lra.
Qed.

(* The converse is deliberately exposed: the canonical recurrence alone
   has not created an analytic payment estimate.  Common bounded action
   is equivalent to the existence of common seed and debt budgets. *)
Theorem UNIFORM_ACTION_CONSTRUCTS_COMMON_PAYMENT : forall T C cut B,
  CofinalActionCuts T cut -> MonotoneCumulativeAction T C ->
  0 <= B -> (forall eps t, 0 <= t < T -> C eps t <= B) ->
  CommonActionPayment C cut B B.
Proof.
  intros T C cut B Hcuts Haction HB Hbound.
  split; [exact HB|]. split; [exact HB|]. split.
  - intro eps. unfold actual_action_mass, DG.action_increment.
    rewrite (cuts_zero T cut Hcuts), (action_zero T C Haction eps).
    pose proof (Hbound eps (cut 1%nat) (cuts_inside T cut Hcuts 1%nat)). lra.
  - intros eps N.
    pose proof (DG.NSDG14_DEBT_PREFIX_AT_MOST_SHIFTED_MASS_PREFIX
      (actual_action_mass C cut eps)
      (ACTION_CELL_NONNEG T C cut Hcuts Haction eps) N) as Hdebt.
    rewrite (ACTION_CELL_PREFIX_EXACT T C cut Hcuts Haction eps (Datatypes.S N))
      in Hdebt.
    pose proof (Hbound eps (cut (Datatypes.S N))
      (cuts_inside T cut Hcuts (Datatypes.S N))).
    pose proof (ACTION_CELL_NONNEG T C cut Hcuts Haction eps O).
    unfold canonical_action_debt. lra.
Qed.

Theorem UNIFORM_ACTION_IFF_COMMON_CANONICAL_PAYMENT : forall T C cut,
  CofinalActionCuts T cut -> MonotoneCumulativeAction T C ->
  (UniformOpenActionBound T C <->
    exists Seed Paid, CommonActionPayment C cut Seed Paid).
Proof.
  intros T C cut Hcuts Haction. split.
  - intros [B [HB Hbound]]. exists B, B.
    exact (UNIFORM_ACTION_CONSTRUCTS_COMMON_PAYMENT T C cut B Hcuts Haction HB Hbound).
  - intros [Seed [Paid Hpayment]]. exists (sharp_action_budget Seed Paid). split.
    + destruct Hpayment as [HSeed [HPaid _]]. unfold sharp_action_budget. lra.
    + exact (COMMON_PAYMENT_GIVES_UNIFORM_ACTUAL_ACTION T C cut Seed Paid
        Hcuts Haction Hpayment).
Qed.

End BKQR_M7_ACTION_CELLS.

Print Assumptions BKQR_M7_ACTION_CELLS.ACTION_CELLS_CONSTRUCT_M7_REALIZATION.
Print Assumptions BKQR_M7_ACTION_CELLS.CANONICAL_CUTS_ARE_COFINAL.
Print Assumptions BKQR_M7_ACTION_CELLS.COMMON_PAYMENT_GIVES_ACTUAL_M7.
Print Assumptions BKQR_M7_ACTION_CELLS.COMMON_PAYMENT_GIVES_UNIFORM_ACTUAL_ACTION.
Print Assumptions BKQR_M7_ACTION_CELLS.UNIFORM_ACTION_IFF_COMMON_CANONICAL_PAYMENT.
