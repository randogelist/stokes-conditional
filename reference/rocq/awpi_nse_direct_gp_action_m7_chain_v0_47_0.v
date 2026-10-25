From Stdlib Require Import Reals Lra Psatz String.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_DIRECT_GP_ACTION_M7_CHAIN.
Module S := NSE_GP_TO_M7_SPINE.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

(*
  Scope: finite-prefix and uniform-family algebra, not an analytic NSE library.
  For the direct GP application, C eps t = integral_{t0}^t a_eps(s)/eta ds.
  A cofinal sequence of time cuts on [t0,T) produces actual integral masses.
  Nonnegative, monotone cumulative action is analytic input. Its coverage
  by the constructed masses is proved below, not assumed as an M7 receipt.
*)

(* Cell masses are increments between adjacent endpoints. *)
Definition action_increment {Reg Time : Type}
  (C : Reg -> Time -> R) (cut : nat -> Time) (eps : Reg) (n : nat) : R :=
  C eps (cut (Datatypes.S n)) - C eps (cut n).

Theorem NSDG00_ACTION_INCREMENT_NONNEG :
  forall (Reg Time : Type) (C : Reg -> Time -> R)
         (stamp : Time -> R) (cut : nat -> Time),
    (forall eps s t, stamp s <= stamp t -> C eps s <= C eps t) ->
    (forall n, stamp (cut n) <= stamp (cut (Datatypes.S n))) ->
    forall eps n, 0 <= action_increment C cut eps n.
Proof.
  intros Reg Time C stamp cut Hmono Horder eps n.
  unfold action_increment.
  pose proof (Hmono eps (cut n) (cut (Datatypes.S n)) (Horder n)) as H.
  lra.
Qed.

Theorem NSDG01_ACTION_PREFIX_TELESCOPES :
  forall (Reg Time : Type) (C : Reg -> Time -> R) (cut : nat -> Time),
    (forall eps, C eps (cut O) = 0) ->
    forall eps N,
      S.resistant_prefix (action_increment C cut eps) N = C eps (cut N).
Proof.
  intros Reg Time C cut Hzero eps N.
  induction N as [|N IH].
  - change (0 = C eps (cut O)).
    rewrite Hzero. reflexivity.
  - change (S.resistant_prefix (action_increment C cut eps) N +
            action_increment C cut eps N = C eps (cut (Datatypes.S N))).
    rewrite IH.
    unfold action_increment. ring.
Qed.

Theorem NSDG02_TIME_COFINALITY_CONSTRUCTS_ACTION_REALIZATION :
  forall (Reg Time : Type) (C : Reg -> Time -> R)
         (stamp : Time -> R) (cut : nat -> Time),
    (forall eps, C eps (cut O) = 0) ->
    (forall eps s t, stamp s <= stamp t -> C eps s <= C eps t) ->
    (forall t, exists N, stamp t <= stamp (cut N)) ->
    forall eps,
      CE.M7ActionCostRealization Time
        (action_increment C cut eps) (C eps).
Proof.
  intros Reg Time C stamp cut Hzero Hmono Hcofinal eps t.
  destruct (Hcofinal t) as [N HN].
  exists N.
  rewrite (NSDG01_ACTION_PREFIX_TELESCOPES Reg Time C cut Hzero eps N).
  exact (Hmono eps t (cut N) HN).
Qed.

(* Integral-of-quotient and quotient-of-integrals must not be confused.
   Dividing this identity by d1*d2*(d1+d2)>0 gives the two-cell
   refinement gap for positive detector masses. *)
Theorem NSDG05_CELL_QUOTIENT_REFINEMENT_GAP_IDENTITY :
  forall d1 d2 r1 r2 : R,
    (d1 + d2) * (d2 * r1 * r1 + d1 * r2 * r2) -
    d1 * d2 * (r1 + r2) * (r1 + r2) =
    (d2 * r1 - d1 * r2) * (d2 * r1 - d1 * r2).
Proof. intros. ring. Qed.

Theorem NSDG06_CELL_QUOTIENT_REFINEMENT_GAP_NONNEG :
  forall d1 d2 r1 r2 : R,
    d1 * d2 * (r1 + r2) * (r1 + r2) <=
    (d1 + d2) * (d2 * r1 * r1 + d1 * r2 * r2).
Proof.
  intros d1 d2 r1 r2.
  pose proof (NSDG05_CELL_QUOTIENT_REFINEMENT_GAP_IDENTITY d1 d2 r1 r2) as H.
  pose proof (Rle_0_sqr (d2 * r1 - d1 * r2)) as Hsq.
  unfold Rsqr in Hsq. lra.
Qed.

(* This is the LEAST payment making a specified sequence obey renewal.
   Defining it makes the recurrence true, but does NOT bound its prefixes. *)
Definition renewal_debt (mass : nat -> R) (n : nat) : R :=
  Rmax 0 (mass (Datatypes.S n) - (509 / 605) * mass n).

Theorem NSDG10_RENEWAL_DEBT_NONNEG :
  forall mass n, 0 <= renewal_debt mass n.
Proof.
  intros mass n. unfold renewal_debt. apply Rmax_l.
Qed.

Theorem NSDG11_RENEWAL_DEBT_IS_MINIMAL :
  forall (mass : nat -> R) (n : nat) (paid : R),
    0 <= paid ->
    605 * mass (Datatypes.S n) <= 509 * mass n + 605 * paid ->
    renewal_debt mass n <= paid.
Proof.
  intros mass n paid Hpaid Hstep.
  unfold renewal_debt. apply Rmax_lub; lra.
Qed.

Theorem NSDG12_CANONICAL_DEBT_GIVES_RENEWAL :
  forall mass : nat -> R,
    (forall n, 0 <= mass n) ->
    S.GP509RenewalCertificate mass (renewal_debt mass).
Proof.
  intros mass Hmass.
  unfold S.GP509RenewalCertificate.
  split.
  - exact Hmass.
  - split.
    + intro n. apply NSDG10_RENEWAL_DEBT_NONNEG.
    + intro n.
      pose proof
        (Rmax_r 0 (mass (Datatypes.S n) - (509 / 605) * mass n)) as H.
      unfold renewal_debt. lra.
Qed.

Theorem NSDG13_DEBT_AT_MOST_NEXT_MASS :
  forall (mass : nat -> R),
    (forall n, 0 <= mass n) ->
    forall n, renewal_debt mass n <= mass (Datatypes.S n).
Proof.
  intros mass Hmass n.
  unfold renewal_debt. apply Rmax_lub.
  - apply Hmass.
  - pose proof (Hmass n). lra.
Qed.

Theorem NSDG14_DEBT_PREFIX_AT_MOST_SHIFTED_MASS_PREFIX :
  forall (mass : nat -> R),
    (forall n, 0 <= mass n) ->
    forall N,
      S.paid_prefix (renewal_debt mass) N <=
      S.resistant_prefix mass (Datatypes.S N) - mass O.
Proof.
  intros mass Hmass N.
  induction N as [|N IH].
  - change (0 <= (0 + mass O) - mass O). lra.
  - change (S.paid_prefix (renewal_debt mass) N + renewal_debt mass N <=
            (S.resistant_prefix mass (Datatypes.S N) +
             mass (Datatypes.S N)) - mass O).
    pose proof (NSDG13_DEBT_AT_MOST_NEXT_MASS mass Hmass N) as Hdebt.
    lra.
Qed.

Theorem NSDG15_DEBT_BUDGET_IFF_SEQUENCE_M7 :
  forall mass : nat -> R,
    (forall n, 0 <= mass n) ->
    (S.GPUniformPaidPrefix (renewal_debt mass) <-> S.GPSequenceM7 mass).
Proof.
  intros mass Hmass. split.
  - intro Hpaid.
    exact (S.NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7
      mass (renewal_debt mass)
      (NSDG12_CANONICAL_DEBT_GIVES_RENEWAL mass Hmass) Hpaid).
  - intros [B [HB Hprefix]].
    exists B. split.
    + exact HB.
    + intro N.
      pose proof
        (NSDG14_DEBT_PREFIX_AT_MOST_SHIFTED_MASS_PREFIX mass Hmass N) as H.
      pose proof (Hprefix (Datatypes.S N)) as HP.
      pose proof (Hmass O) as HM.
      lra.
Qed.

(* A simple obstruction to treating the recurrence as automatic with no
   physical payment. This is a scalar test, not a counterexample to NSE. *)
Theorem NSDG16_POSITIVE_CONSTANT_MASS_HAS_NO_ZERO_PAID_RENEWAL :
  ~ S.GP509RenewalCertificate (fun _ => 1) (fun _ => 0).
Proof.
  intros [_ [_ Hstep]]. specialize (Hstep O). cbn in Hstep. lra.
Qed.

Theorem NSDG20_SHARP_SEED_AND_PAYMENT_BOUND :
  forall (mass : nat -> R) (Seed Paid : R),
    (forall n, 0 <= mass n) ->
    mass O <= Seed ->
    0 <= Paid ->
    (forall N, S.paid_prefix (renewal_debt mass) N <= Paid) ->
    forall N,
      S.resistant_prefix mass N <= (605 / 96) * (Seed + Paid).
Proof.
  intros mass Seed Paid Hmass Hseed HPaid Hbudget N.
  pose proof
    (S.NSGM01_GP_509_RENEWAL_GIVES_EXACT_PREFIX_BOUND
      mass (renewal_debt mass) Paid
      (NSDG12_CANONICAL_DEBT_GIVES_RENEWAL mass Hmass)
      HPaid Hbudget N) as H.
  lra.
Qed.

Theorem NSDG21_PHYSICAL_CELLS_GIVE_UNIFORM_ACTION_BOUND :
  forall (Reg Time : Type) (C : Reg -> Time -> R)
         (stamp : Time -> R) (cut : nat -> Time) (Seed Paid : R),
    (forall eps, C eps (cut O) = 0) ->
    (forall eps s t, stamp s <= stamp t -> C eps s <= C eps t) ->
    (forall n, stamp (cut n) <= stamp (cut (Datatypes.S n))) ->
    (forall t, exists N, stamp t <= stamp (cut N)) ->
    (forall eps, action_increment C cut eps O <= Seed) ->
    0 <= Paid ->
    (forall eps N,
      S.paid_prefix (renewal_debt (action_increment C cut eps)) N <= Paid) ->
    forall eps t, C eps t <= (605 / 96) * (Seed + Paid).
Proof.
  intros Reg Time C stamp cut Seed Paid Hzero Hmono Horder Hcofinal
         Hseed HPaid Hbudget eps t.
  pose proof
    (NSDG00_ACTION_INCREMENT_NONNEG Reg Time C stamp cut Hmono Horder eps)
    as Hmass.
  destruct
    (NSDG02_TIME_COFINALITY_CONSTRUCTS_ACTION_REALIZATION
      Reg Time C stamp cut Hzero Hmono Hcofinal eps t) as [N Hcover].
  pose proof
    (NSDG20_SHARP_SEED_AND_PAYMENT_BOUND
      (action_increment C cut eps) Seed Paid Hmass
      (Hseed eps) HPaid (Hbudget eps) N) as Hprefix.
  lra.
Qed.

(* Local payment <= kappa * a physical ledger gives a summed budget.
   The physical meaning and bounded total of the ledger are hypotheses.
   In the intended application it is viscous kinetic-energy expenditure. *)
Theorem NSDG30_LOCAL_LEDGER_CHARGE_GIVES_PREFIX_CHARGE :
  forall (paid ledger : nat -> R) (kappa : R),
    (forall n, paid n <= kappa * ledger n) ->
    forall N, S.paid_prefix paid N <= kappa * S.paid_prefix ledger N.
Proof.
  intros paid ledger kappa Hcharge N.
  induction N as [|N IH].
  - change (0 <= kappa * 0). lra.
  - change (S.paid_prefix paid N + paid N <=
            kappa * (S.paid_prefix ledger N + ledger N)).
    specialize (Hcharge N). nra.
Qed.

Theorem NSDG31_COMMON_LEDGER_BOUND_GIVES_COMMON_PAYMENT_BOUND :
  forall (Reg : Type) (mass ledger : Reg -> nat -> R) (kappa LedgerMax : R),
    0 <= kappa ->
    (forall eps n, renewal_debt (mass eps) n <= kappa * ledger eps n) ->
    (forall eps N, S.paid_prefix (ledger eps) N <= LedgerMax) ->
    forall eps N,
      S.paid_prefix (renewal_debt (mass eps)) N <= kappa * LedgerMax.
Proof.
  intros Reg mass ledger kappa LedgerMax Hkappa Hcharge Hledger eps N.
  pose proof
    (NSDG30_LOCAL_LEDGER_CHARGE_GIVES_PREFIX_CHARGE
      (renewal_debt (mass eps)) (ledger eps) kappa (Hcharge eps) N) as H.
  pose proof
    (Rmult_le_compat_l kappa (S.paid_prefix (ledger eps) N) LedgerMax
      Hkappa (Hledger eps N)) as HL.
  lra.
Qed.

(* Uniformity is encoded by taking Time = Reg * physical-Time.
   One existential pair of bounds then applies to every regularization. *)
Theorem NSDG40_UNIFORM_DIRECT_GP_M7_CRITICAL_ENERGY_CHAIN :
  forall (Reg Time : Type) (C mass diss : Reg -> Time -> R)
         (stamp : Time -> R) (cut : nat -> Time)
         (nu theta E0 Seed Paid : R),
    (forall eps, C eps (cut O) = 0) ->
    (forall eps s t, stamp s <= stamp t -> C eps s <= C eps t) ->
    (forall n, stamp (cut n) <= stamp (cut (Datatypes.S n))) ->
    (forall t, exists N, stamp t <= stamp (cut N)) ->
    0 <= Seed ->
    (forall eps, action_increment C cut eps O <= Seed) ->
    0 <= Paid ->
    (forall eps N,
      S.paid_prefix (renewal_debt (action_increment C cut eps)) N <= Paid) ->
    CE.CriticalEnergyBalance (Reg * Time)%type nu theta E0
      (fun rt => mass (fst rt) (snd rt))
      (fun rt => diss (fst rt) (snd rt))
      (fun rt => C (fst rt) (snd rt)) ->
    CE.UniformCriticalEnergy (Reg * Time)%type
      (fun rt => mass (fst rt) (snd rt))
      (fun rt => diss (fst rt) (snd rt)).
Proof.
  intros Reg Time C mass diss stamp cut nu theta E0 Seed Paid
    Hzero Hmono Horder Hcofinal HSeed Hseed HPaid Hbudget Hbalance.
  assert (Hmax : 0 <= (605 / 96) * (Seed + Paid)) by lra.
  assert (Haction : forall rt : (Reg * Time)%type,
    C (fst rt) (snd rt) <= (605 / 96) * (Seed + Paid)).
  {
    intros [eps t]. cbn.
    exact
      (NSDG21_PHYSICAL_CELLS_GIVE_UNIFORM_ACTION_BOUND
        Reg Time C stamp cut Seed Paid Hzero Hmono Horder Hcofinal
        Hseed HPaid Hbudget eps t).
  }
  exact
    (CE.NSCE10_ACTION_COST_BOUND_GIVES_CRITICAL_ENERGY
      (Reg * Time)%type nu theta E0 ((605 / 96) * (Seed + Paid))
      (fun rt => mass (fst rt) (snd rt))
      (fun rt => diss (fst rt) (snd rt))
      (fun rt => C (fst rt) (snd rt)) Hbalance Hmax Haction).
Qed.

Definition STATUS : string :=
  "NSE_DIRECT_GP_ACTION_TO_M7_UNIFORM_CHAIN_CONDITIONAL_NO_ADMITTED"%string.

End NSE_DIRECT_GP_ACTION_M7_CHAIN.

Print Assumptions NSE_DIRECT_GP_ACTION_M7_CHAIN.NSDG02_TIME_COFINALITY_CONSTRUCTS_ACTION_REALIZATION.
Print Assumptions NSE_DIRECT_GP_ACTION_M7_CHAIN.NSDG15_DEBT_BUDGET_IFF_SEQUENCE_M7.
Print Assumptions NSE_DIRECT_GP_ACTION_M7_CHAIN.NSDG31_COMMON_LEDGER_BOUND_GIVES_COMMON_PAYMENT_BOUND.
Print Assumptions NSE_DIRECT_GP_ACTION_M7_CHAIN.NSDG40_UNIFORM_DIRECT_GP_M7_CRITICAL_ENERGY_CHAIN.
