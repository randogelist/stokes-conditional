From Stdlib Require Import Reals Lra Psatz String.
Require Import awpi_nse_gp_quarter_shift_firewall_v0_13_6.
Require Import awpi_nse_gp_restart_action_covariance_v0_14_2.

Module NSE_GP_TO_M7_SPINE.

Open Scope R_scope.

(*
  GP -> M7 spine.

  Purpose:
    Freeze the downstream implication from a GP critical renewal certificate
    to a uniform resistant-prefix / sequence-M7 certificate, using the already
    checked 509/605 critical recurrence.

  This file intentionally does NOT claim that the actual Leray-Hopf solution
  already supplies the physical GP realization.  That remains an explicit
  frontier.  It also keeps the final sequence-to-continuous ActualGPM7 passage
  explicit.

  Checked ingredients imported here:
    - exact GP action/detector currency covariance under positive scaling;
    - critical GP quarter-shift firewall;
    - 509/605 resistant renewal;
    - exact critical prefix invariant.
*)

Definition resistant_prefix :=
  NSE_GP_QUARTER_SHIFT_FIREWALL.resistant_prefix.

Definition paid_prefix :=
  NSE_GP_QUARTER_SHIFT_FIREWALL.paid_prefix.

Section FINITE_GP_RENEWAL.

  Definition GP509RenewalCertificate
    (mass paid : nat -> R) : Prop :=
    (forall n : nat, 0 <= mass n) /\
    (forall n : nat, 0 <= paid n) /\
    (forall n : nat,
       605 * mass (S n) <= 509 * mass n + 605 * paid n).

  Definition GPUniformPaidPrefix
    (paid : nat -> R) : Prop :=
    exists Pmax : R,
      0 <= Pmax /\
      forall N : nat, paid_prefix paid N <= Pmax.

  Definition GPSequenceM7
    (mass : nat -> R) : Prop :=
    exists B : R,
      0 <= B /\
      forall N : nat, resistant_prefix mass N <= B.

  Theorem NSGM00_RESISTANT_PREFIX_NONNEG :
    forall mass : nat -> R,
      (forall n : nat, 0 <= mass n) ->
      forall N : nat, 0 <= resistant_prefix mass N.
  Proof.
    intros mass Hmass N.
    induction N as [|N IHN].
    - simpl. lra.
    - simpl. specialize (Hmass N). lra.
  Qed.

  Theorem NSGM01_GP_509_RENEWAL_GIVES_EXACT_PREFIX_BOUND :
    forall (mass paid : nat -> R) (Pmax : R),
      GP509RenewalCertificate mass paid ->
      0 <= Pmax ->
      (forall N : nat, paid_prefix paid N <= Pmax) ->
      forall N : nat,
        96 * resistant_prefix mass N <=
        605 * mass O + 605 * Pmax.
  Proof.
    intros mass paid Pmax Hcert HPmax Hbudget N.
    destruct Hcert as [Hmass [Hpaid Hstep]].
    exact
      (NSE_GP_QUARTER_SHIFT_FIREWALL.NSQF31_UNIFORM_PAID_PREFIX_GIVES_CRITICAL_PREFIX_BOUND
         mass paid Hmass Hpaid Hstep N Pmax (Hbudget N)).
  Qed.

  Theorem NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7 :
    forall mass paid : nat -> R,
      GP509RenewalCertificate mass paid ->
      GPUniformPaidPrefix paid ->
      GPSequenceM7 mass.
  Proof.
    intros mass paid Hcert Hpaidbudget.
    destruct Hpaidbudget as [Pmax [HPmax Hbudget]].
    destruct Hcert as [Hmass [Hpaid Hstep]].
    exists (605 * mass O + 605 * Pmax).
    split.
    - specialize (Hmass O). nra.
    - intro N.
      pose proof
        (NSE_GP_QUARTER_SHIFT_FIREWALL.NSQF31_UNIFORM_PAID_PREFIX_GIVES_CRITICAL_PREFIX_BOUND
           mass paid Hmass Hpaid Hstep N Pmax (Hbudget N)) as H96.
      pose proof (NSGM00_RESISTANT_PREFIX_NONNEG mass Hmass N) as Hpref.
      assert (Hscale : resistant_prefix mass N <=
                       96 * resistant_prefix mass N).
      { nra. }
      exact (Rle_trans _ _ _ Hscale H96).
  Qed.

  Theorem NSGM03_ZERO_PAID_CRITICAL_GP_RENEWAL_IS_SUMMABLE :
    forall mass : nat -> R,
      (forall n : nat, 0 <= mass n) ->
      (forall n : nat,
         605 * mass (S n) <= 509 * mass n) ->
      GPSequenceM7 mass.
  Proof.
    intros mass Hmass Hstep.
    set (paid := fun _ : nat => 0).
    assert (Hcert : GP509RenewalCertificate mass paid).
    {
      unfold GP509RenewalCertificate.
      split.
      - exact Hmass.
      - split.
        + intro n. unfold paid. lra.
        + intro n. unfold paid. specialize (Hstep n). lra.
    }
    assert (Hzero : forall N : nat,
              paid_prefix (fun _ : nat => 0) N = 0).
    {
      intro N.
      unfold paid_prefix.
      induction N as [|N IHN].
      - reflexivity.
      - simpl.
        rewrite IHN.
        lra.
    }
    assert (Hbudget : GPUniformPaidPrefix paid).
    {
      exists 0.
      split.
      - lra.
      - intro N.
        unfold paid.
        rewrite Hzero.
        lra.
    }
    exact (NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7
             mass paid Hcert Hbudget).
  Qed.

End FINITE_GP_RENEWAL.

Section GP_CURRENCY_COVARIANCE.

  (* Re-export the exact scalar currency invariance that justifies carrying
     the same resistant masses through a positive GP coordinate change. *)
  Theorem NSGM10_GP_ACTION_CURRENCY_IS_INVARIANT :
    forall s psi D : R,
      s <> 0 ->
      0 < D ->
      NSE_GP_RESTART_ACTION_COVARIANCE.action
        (NSE_GP_RESTART_ACTION_COVARIANCE.gp_cut s psi)
        (NSE_GP_RESTART_ACTION_COVARIANCE.gp_cap s D) =
      NSE_GP_RESTART_ACTION_COVARIANCE.action psi D.
  Proof.
    intros s psi D Hs HD.
    assert (HD0 : D <> 0).
    { intro Hzero. subst D. lra. }
    exact
      (NSE_GP_RESTART_ACTION_COVARIANCE.NSAC02_ACTION_QUOTIENT_INVARIANT
         s psi D Hs HD0).
  Qed.

  Theorem NSGM11_GP_SOURCE_PAIRING_IS_INVARIANT :
    forall s source g : R,
      s <> 0 ->
      NSE_GP_RESTART_ACTION_COVARIANCE.gp_cut s source *
      NSE_GP_RESTART_ACTION_COVARIANCE.gp_dual s g =
      source * g.
  Proof.
    intros s source g Hs.
    exact
      (NSE_GP_RESTART_ACTION_COVARIANCE.NSAC05_DUAL_SOURCE_PAIRING_INVARIANT
         s source g Hs).
  Qed.

End GP_CURRENCY_COVARIANCE.

Section ABSTRACT_GP_TO_M7_FRONTIER.

  Context {Velocity : Type}.

  Variable LerayHopfT3 : Velocity -> Prop.
  Variable GPPhysicalRealization : Velocity -> Prop.
  Variable ActualGPM7 : Velocity -> Prop.

  Variable mass_of : Velocity -> nat -> R.
  Variable paid_of : Velocity -> nat -> R.

  Definition GP509Renewal (u : Velocity) : Prop :=
    GP509RenewalCertificate (mass_of u) (paid_of u).

  Definition GPFinitePaidBudget (u : Velocity) : Prop :=
    GPUniformPaidPrefix (paid_of u).

  Definition GPSequenceM7For (u : Velocity) : Prop :=
    GPSequenceM7 (mass_of u).

  Theorem NSGM20_GP_RENEWAL_AND_PAID_BUDGET_GIVE_SEQUENCE_M7 :
    forall u : Velocity,
      GP509Renewal u ->
      GPFinitePaidBudget u ->
      GPSequenceM7For u.
  Proof.
    intros u Hrenew Hpaid.
    exact
      (NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7
         (mass_of u) (paid_of u) Hrenew Hpaid).
  Qed.

  (* Final analytic/physical handoff kept explicit:
       - GPPhysicalRealization says the abstract renewal sequence is genuinely
         the restart-local physical resistant action genealogy of u;
       - GPSequenceM7For is the finite-prefix output proved above;
       - this principle identifies that sequence certificate with ActualGPM7.
  *)
  Definition GPSequenceToActualGPM7Principle : Prop :=
    forall u : Velocity,
      LerayHopfT3 u ->
      GPPhysicalRealization u ->
      GPSequenceM7For u ->
      ActualGPM7 u.

  Theorem NSGM90_GP_TO_M7_TERMINAL_ANCHOR :
    GPSequenceToActualGPM7Principle ->
    forall u : Velocity,
      LerayHopfT3 u ->
      GPPhysicalRealization u ->
      GP509Renewal u ->
      GPFinitePaidBudget u ->
      ActualGPM7 u.
  Proof.
    intros Hbridge u Hlh Hphys Hrenew Hpaid.
    apply (Hbridge u Hlh Hphys).
    exact (NSGM20_GP_RENEWAL_AND_PAID_BUDGET_GIVE_SEQUENCE_M7
             u Hrenew Hpaid).
  Qed.

End ABSTRACT_GP_TO_M7_FRONTIER.

Definition STATUS : string :=
  "NSE_GP_509_OVER_605_TO_M7_SPINE_CONDITIONAL_ANCHOR_NO_ADMITTED"%string.

End NSE_GP_TO_M7_SPINE.

Print Assumptions NSE_GP_TO_M7_SPINE.NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7.
Print Assumptions NSE_GP_TO_M7_SPINE.NSGM10_GP_ACTION_CURRENCY_IS_INVARIANT.
Print Assumptions NSE_GP_TO_M7_SPINE.NSGM90_GP_TO_M7_TERMINAL_ANCHOR.
