import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
Finite M7 payment algebra and its connection to actual cumulative action.
The payment estimate is an explicit premise.  This file does not assert
that an arbitrary Leray--Hopf path satisfies that estimate.
-/

namespace NSE

noncomputable section

open scoped BigOperators

def massPrefix (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, f k

@[simp] theorem prefix_zero (f : ℕ → ℝ) : massPrefix f 0 = 0 := by
  simp [massPrefix]

theorem prefix_succ (f : ℕ → ℝ) (n : ℕ) :
    massPrefix f (n + 1) = massPrefix f n + f n := by
  simp [massPrefix, Finset.sum_range_succ]

theorem prefix_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (n : ℕ) :
    0 ≤ massPrefix f n := by
  exact Finset.sum_nonneg (fun k _ => hf k)

def renewalDebt (mass : ℕ → ℝ) (n : ℕ) : ℝ :=
  max 0 (mass (n + 1) - (509 / 605 : ℝ) * mass n)

theorem renewalDebt_nonneg (mass : ℕ → ℝ) (n : ℕ) :
    0 ≤ renewalDebt mass n := le_max_left _ _

theorem renewal_step (mass : ℕ → ℝ) (n : ℕ) :
    605 * mass (n + 1) ≤ 509 * mass n + 605 * renewalDebt mass n := by
  have h := le_max_right (0 : ℝ) (mass (n + 1) - (509 / 605 : ℝ) * mass n)
  change mass (n + 1) - (509 / 605 : ℝ) * mass n ≤ renewalDebt mass n at h
  nlinarith

theorem renewal_prefix_invariant (mass : ℕ → ℝ) (n : ℕ) :
    96 * massPrefix mass n + 605 * mass n ≤
      605 * mass 0 + 605 * massPrefix (renewalDebt mass) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [prefix_succ, prefix_succ]
      have hs := renewal_step mass n
      nlinarith

def actionBudget (Seed Paid θ : ℝ) : ℝ :=
  (Seed + Paid) / (96 / 605 - θ)

structure PrefixPayment (mass : ℕ → ℕ → ℝ) (Seed Paid θ : ℝ) : Prop where
  seed_nonneg : 0 ≤ Seed
  paid_nonneg : 0 ≤ Paid
  theta_nonneg : 0 ≤ θ
  theta_lt : θ < 96 / 605
  seed_bound : ∀ eps, mass eps 0 ≤ Seed
  charge : ∀ eps n,
    massPrefix (renewalDebt (mass eps)) n ≤ Paid + θ * massPrefix (mass eps) n

theorem actionBudget_nonneg {Seed Paid θ : ℝ}
    (hS : 0 ≤ Seed) (hP : 0 ≤ Paid) (hθ : θ < 96 / 605) :
    0 ≤ actionBudget Seed Paid θ := by
  unfold actionBudget
  exact div_nonneg (add_nonneg hS hP) (by linarith)

theorem actionBudget_identity {Seed Paid θ : ℝ} (hθ : θ < 96 / 605) :
    (96 / 605 - θ) * actionBudget Seed Paid θ = Seed + Paid := by
  unfold actionBudget
  have hd : (96 / 605 - θ : ℝ) ≠ 0 := by linarith
  exact mul_div_cancel₀ (Seed + Paid) hd

theorem prefixPayment_bound {mass : ℕ → ℕ → ℝ} {Seed Paid θ : ℝ}
    (hmass : ∀ eps n, 0 ≤ mass eps n)
    (hpay : PrefixPayment mass Seed Paid θ) (eps n : ℕ) :
    massPrefix (mass eps) n ≤ actionBudget Seed Paid θ := by
  have hi := renewal_prefix_invariant (mass eps) n
  have hm := hmass eps n
  have hs := hpay.seed_bound eps
  have hp := hpay.charge eps n
  have hd : (0 : ℝ) < 96 / 605 - θ := by linarith [hpay.theta_lt]
  unfold actionBudget
  apply (le_div_iff₀ hd).2
  nlinarith

def GPSequenceM7 (mass : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ n, massPrefix mass n ≤ B

theorem prefixPayment_m7 {mass : ℕ → ℕ → ℝ} {Seed Paid θ : ℝ}
    (hmass : ∀ eps n, 0 ≤ mass eps n)
    (hpay : PrefixPayment mass Seed Paid θ) (eps : ℕ) :
    GPSequenceM7 (mass eps) := by
  refine ⟨actionBudget Seed Paid θ,
    actionBudget_nonneg hpay.seed_nonneg hpay.paid_nonneg hpay.theta_lt, ?_⟩
  exact prefixPayment_bound hmass hpay eps

structure CommonPayment (mass : ℕ → ℕ → ℝ) (Seed Paid : ℝ) : Prop where
  seed_nonneg : 0 ≤ Seed
  paid_nonneg : 0 ≤ Paid
  seed_bound : ∀ eps, mass eps 0 ≤ Seed
  charge : ∀ eps n, massPrefix (renewalDebt (mass eps)) n ≤ Paid

theorem paymentToCommon {mass : ℕ → ℕ → ℝ} {Seed Paid θ : ℝ}
    (hmass : ∀ eps n, 0 ≤ mass eps n)
    (hpay : PrefixPayment mass Seed Paid θ) :
    CommonPayment mass Seed (Paid + θ * actionBudget Seed Paid θ) := by
  refine ⟨hpay.seed_nonneg, ?_, hpay.seed_bound, ?_⟩
  · exact add_nonneg hpay.paid_nonneg
      (mul_nonneg hpay.theta_nonneg
        (actionBudget_nonneg hpay.seed_nonneg hpay.paid_nonneg hpay.theta_lt))
  · intro eps n
    have hscaled := mul_le_mul_of_nonneg_left (prefixPayment_bound hmass hpay eps n)
      hpay.theta_nonneg
    have hcharge := hpay.charge eps n
    linarith

theorem absorbed_budget_exact {Seed Paid θ : ℝ} (hθ : θ < 96 / 605) :
    605 * (Seed + (Paid + θ * actionBudget Seed Paid θ)) / 96 =
      actionBudget Seed Paid θ := by
  have hi := actionBudget_identity (Seed := Seed) (Paid := Paid) hθ
  nlinarith

/- A genuine half-open time interval is used; no monotonicity outside it
is required.  The cells belong to the specified cumulative action. -/
structure ActionGrid (T : ℝ) (cut : ℕ → ℝ) : Prop where
  zero : cut 0 = 0
  inside : ∀ n, 0 ≤ cut n ∧ cut n < T
  ordered : ∀ n, cut n ≤ cut (n + 1)
  cofinal : ∀ t, 0 ≤ t ∧ t < T → ∃ n, t ≤ cut n

structure CumulativeAction (T : ℝ) (C : ℕ → ℝ → ℝ) : Prop where
  zero : ∀ eps, C eps 0 = 0
  mono : ∀ eps s t, 0 ≤ s → s ≤ t → t < T → C eps s ≤ C eps t

def canonicalCut (T : ℝ) (n : ℕ) : ℝ :=
  T * (1 - 1 / ((n : ℝ) + 1))

theorem canonicalCut_grid {T : ℝ} (hT : 0 < T) :
    ActionGrid T (canonicalCut T) := by
  constructor
  · simp [canonicalCut]
  · intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hi : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ hd).2 (by linarith)
    have hprodpos := mul_pos hT hi
    have hprodle := mul_le_mul_of_nonneg_left hle hT.le
    constructor <;> unfold canonicalCut <;> nlinarith
  · intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hd' : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
    have hi : (1 : ℝ) / ((n : ℝ) + 1 + 1) ≤ 1 / ((n : ℝ) + 1) :=
      (div_le_div_iff₀ hd' hd).2 (by linarith)
    simp only [canonicalCut, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (by linarith) hT.le
  · intro t ht
    have hdiff : 0 < T - t := by linarith [ht.2]
    obtain ⟨n, hn⟩ := exists_nat_gt (T / (T - t))
    have hmul : T < (n : ℝ) * (T - t) := (div_lt_iff₀ hdiff).1 hn
    refine ⟨n, ?_⟩
    have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hid : canonicalCut T n * ((n : ℝ) + 1) = T * (n : ℝ) := by
      unfold canonicalCut
      field_simp [ne_of_gt hd]; ring
    apply (mul_le_mul_iff_left₀ hd).1
    rw [hid]
    nlinarith [ht.2]

def actionMass (C : ℕ → ℝ → ℝ) (cut : ℕ → ℝ) (eps n : ℕ) : ℝ :=
  C eps (cut (n + 1)) - C eps (cut n)

theorem actionMass_nonneg {T : ℝ} {C : ℕ → ℝ → ℝ} {cut : ℕ → ℝ}
    (hgrid : ActionGrid T cut) (hC : CumulativeAction T C) (eps n : ℕ) :
    0 ≤ actionMass C cut eps n := by
  have h := hC.mono eps (cut n) (cut (n + 1))
    (hgrid.inside n).1 (hgrid.ordered n) (hgrid.inside (n + 1)).2
  unfold actionMass
  linarith

theorem actionMass_prefix {T : ℝ} {C : ℕ → ℝ → ℝ} {cut : ℕ → ℝ}
    (hgrid : ActionGrid T cut) (hC : CumulativeAction T C) (eps n : ℕ) :
    massPrefix (actionMass C cut eps) n = C eps (cut n) := by
  induction n with
  | zero => simp [hgrid.zero, hC.zero]
  | succ n ih =>
      rw [prefix_succ, ih]
      unfold actionMass
      ring

theorem actionMass_covers {T : ℝ} {C : ℕ → ℝ → ℝ} {cut : ℕ → ℝ}
    (hgrid : ActionGrid T cut) (hC : CumulativeAction T C) (eps : ℕ)
    {t : ℝ} (ht : 0 ≤ t ∧ t < T) :
    ∃ n, C eps t ≤ massPrefix (actionMass C cut eps) n := by
  obtain ⟨n, hn⟩ := hgrid.cofinal t ht
  refine ⟨n, ?_⟩
  rw [actionMass_prefix hgrid hC]
  exact hC.mono eps t (cut n) ht.1 hn (hgrid.inside n).2

theorem actionPayment_bound {T Seed Paid θ : ℝ}
    {C : ℕ → ℝ → ℝ} {cut : ℕ → ℝ}
    (hgrid : ActionGrid T cut) (hC : CumulativeAction T C)
    (hpay : PrefixPayment (actionMass C cut) Seed Paid θ)
    (eps : ℕ) {t : ℝ} (ht : 0 ≤ t ∧ t < T) :
    C eps t ≤ actionBudget Seed Paid θ := by
  obtain ⟨n, hn⟩ := actionMass_covers hgrid hC eps ht
  exact hn.trans (prefixPayment_bound (actionMass_nonneg hgrid hC) hpay eps n)

/- A globally bounded same-path ledger can pay the fixed part of the
massPrefix charge.  No local or restart estimate is assumed by this lemma. -/
theorem ledgerPrefixPayment {T Seed P₀ κ E₀ θ : ℝ}
    {C L : ℕ → ℝ → ℝ} {cut : ℕ → ℝ}
    (hgrid : ActionGrid T cut)
    (hS : 0 ≤ Seed) (hP : 0 ≤ P₀) (hκ : 0 ≤ κ) (hE : 0 ≤ E₀)
    (hθ₀ : 0 ≤ θ) (hθ : θ < 96 / 605)
    (hseed : ∀ eps, actionMass C cut eps 0 ≤ Seed)
    (hL : ∀ eps t, 0 ≤ t ∧ t < T → L eps t ≤ E₀)
    (hcharge : ∀ eps n, massPrefix (renewalDebt (actionMass C cut eps)) n ≤
      P₀ + κ * L eps (cut n) + θ * massPrefix (actionMass C cut eps) n) :
    PrefixPayment (actionMass C cut) Seed (P₀ + κ * E₀) θ := by
  refine ⟨hS, add_nonneg hP (mul_nonneg hκ hE), hθ₀, hθ, hseed, ?_⟩
  intro eps n
  have hbound := hL eps (cut n) (hgrid.inside n)
  have hpaid := hcharge eps n
  have hscaled := mul_le_mul_of_nonneg_left hbound hκ
  linarith

/- The strict threshold is necessary for this scalar criterion.  The
constant sequence is not claimed to arise from a Navier--Stokes path. -/
@[simp] theorem unit_prefix (n : ℕ) : massPrefix (fun _ => (1 : ℝ)) n = n := by
  simp [massPrefix]

@[simp] theorem unit_debt (n : ℕ) :
    renewalDebt (fun _ => (1 : ℝ)) n = 96 / 605 := by
  norm_num [renewalDebt]

theorem unit_exact_threshold_charge (n : ℕ) :
    massPrefix (renewalDebt (fun _ => (1 : ℝ))) n =
      (96 / 605 : ℝ) * massPrefix (fun _ => (1 : ℝ)) n := by
  simp [massPrefix, mul_comm]

theorem unit_prefix_unbounded (B : ℝ) :
    ∃ n, B < massPrefix (fun _ => (1 : ℝ)) n := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  exact ⟨n, by simpa using hn⟩

theorem unit_not_m7 : ¬ GPSequenceM7 (fun _ => (1 : ℝ)) := by
  rintro ⟨B, _, hB⟩
  obtain ⟨n, hn⟩ := unit_prefix_unbounded B
  exact (not_lt_of_ge (hB n)) hn

theorem strict_margin_cannot_be_dropped :
    (∀ _n : ℕ, 0 ≤ (1 : ℝ)) ∧ (1 : ℝ) ≤ 1 ∧
    (∀ n, massPrefix (renewalDebt (fun _ => (1 : ℝ))) n =
      0 + (96 / 605 : ℝ) * massPrefix (fun _ => (1 : ℝ)) n) ∧
    ¬ GPSequenceM7 (fun _ => (1 : ℝ)) := by
  refine ⟨fun _ => by norm_num, by norm_num, ?_, unit_not_m7⟩
  intro n
  simpa using unit_exact_threshold_charge n

end

end NSE
