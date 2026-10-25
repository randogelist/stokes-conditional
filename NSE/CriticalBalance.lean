import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert

/-! Finite modal critical balance using ordinary real derivatives.
The primitives and the modal equation are explicit hypotheses. An arbitrary
Hilbert basis is not asserted to diagonalize the physical viscous operator. -/

namespace NSE

open scoped BigOperators

noncomputable def criticalEnergy (lam : ℕ → ℝ) (a : ℝ → ℕ → ℝ)
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, lam i * (a t i) ^ 2

noncomputable def criticalDissipation (lam : ℕ → ℝ) (a : ℝ → ℕ → ℝ)
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, (lam i) ^ 3 * (a t i) ^ 2

noncomputable def criticalCurrent (lam : ℕ → ℝ) (a b : ℝ → ℕ → ℝ)
    (N : ℕ) (t : ℝ) : ℝ :=
  -(∑ i ∈ Finset.range N, lam i * a t i * b t i)

noncomputable def criticalSourceDensity (nu : ℝ) (lam : ℕ → ℝ)
    (a b : ℝ → ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (max 0 (criticalCurrent lam a b N t)) ^ 2 /
    (nu * criticalDissipation lam a N t)

theorem criticalEnergy_nonneg (lam : ℕ → ℝ) (a : ℝ → ℕ → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (N : ℕ) (t : ℝ) :
    0 ≤ criticalEnergy lam a N t := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (sq_nonneg _)

theorem criticalDissipation_nonneg (lam : ℕ → ℝ) (a : ℝ → ℕ → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (N : ℕ) (t : ℝ) :
    0 ≤ criticalDissipation lam a N t := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (pow_nonneg (hlam i) 3) (sq_nonneg _)

theorem zero_capacity_current (lam : ℕ → ℝ) (a b : ℝ → ℕ → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (N : ℕ) (t : ℝ)
    (hd : criticalDissipation lam a N t = 0) :
    criticalCurrent lam a b N t = 0 := by
  have hterm : ∀ i ∈ Finset.range N, (lam i) ^ 3 * (a t i) ^ 2 = 0 := by
    intro i hi
    have hle := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.range N) =>
        mul_nonneg (pow_nonneg (hlam j) 3) (sq_nonneg (a t j))) hi
    change (lam i) ^ 3 * (a t i) ^ 2 ≤ criticalDissipation lam a N t at hle
    have hpos := mul_nonneg (pow_nonneg (hlam i) 3) (sq_nonneg (a t i))
    linarith
  unfold criticalCurrent
  rw [Finset.sum_eq_zero]
  · simp
  · intro i hi
    rcases mul_eq_zero.mp (hterm i hi) with h | h
    · have hz : lam i = 0 := eq_zero_of_pow_eq_zero h
      simp [hz]
    · have hz : a t i = 0 := eq_zero_of_pow_eq_zero h
      simp [hz]

theorem normalized_young (nu d j : ℝ) (hnu : 0 < nu) (hd : 0 ≤ d)
    (hzero : d = 0 → j = 0) :
    2 * j ≤ nu * d + (max 0 j) ^ 2 / (nu * d) := by
  by_cases hz : d = 0
  · simp [hz, hzero hz]
  · have hden : 0 < nu * d := mul_pos hnu (lt_of_le_of_ne hd (Ne.symm hz))
    have hp : j ≤ max 0 j := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_right hp hden.le
    have hsq := sq_nonneg (max 0 j - nu * d)
    have hineq : 2 * j - nu * d ≤ (max 0 j) ^ 2 / (nu * d) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    linarith

theorem criticalSourceDensity_nonneg (nu : ℝ) (lam : ℕ → ℝ)
    (a b : ℝ → ℕ → ℝ) (hnu : 0 < nu) (hlam : ∀ i, 0 ≤ lam i)
    (N : ℕ) (t : ℝ) : 0 ≤ criticalSourceDensity nu lam a b N t := by
  exact div_nonneg (sq_nonneg _) (mul_nonneg hnu.le
    (criticalDissipation_nonneg lam a hlam N t))

theorem criticalDissipation_monotone (lam : ℕ → ℝ) (a : ℝ → ℕ → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (t : ℝ) :
    Monotone (fun N => criticalDissipation lam a N t) := by
  apply monotone_nat_of_le_succ
  intro N
  simp only [criticalDissipation, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (hlam N) 3) (sq_nonneg _))

theorem criticalEnergy_monotone (lam : ℕ → ℝ) (a : ℝ → ℕ → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (t : ℝ) :
    Monotone (fun N => criticalEnergy lam a N t) := by
  apply monotone_nat_of_le_succ
  intro N
  simp only [criticalEnergy, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (mul_nonneg (hlam N) (sq_nonneg _))

theorem critical_young (nu : ℝ) (lam : ℕ → ℝ) (a b : ℝ → ℕ → ℝ)
    (hnu : 0 < nu) (hlam : ∀ i, 0 ≤ lam i) (N : ℕ) (t : ℝ) :
    2 * criticalCurrent lam a b N t ≤
      nu * criticalDissipation lam a N t + criticalSourceDensity nu lam a b N t := by
  exact normalized_young nu _ _ hnu
    (criticalDissipation_nonneg lam a hlam N t)
    (zero_capacity_current lam a b hlam N t)

theorem criticalEnergy_hasDerivAt (nu : ℝ) (lam : ℕ → ℝ)
    (a b : ℝ → ℕ → ℝ) (N : ℕ) (t : ℝ)
    (ha : ∀ i ∈ Finset.range N,
      HasDerivAt (fun s => a s i) (-nu * (lam i)^2 * a t i - b t i) t) :
    HasDerivAt (criticalEnergy lam a N)
      (-2 * nu * criticalDissipation lam a N t + 2 * criticalCurrent lam a b N t) t := by
  induction N with
  | zero =>
    have hz : criticalEnergy lam a 0 = fun _ => 0 := by
      funext s
      simp [criticalEnergy]
    rw [hz]
    simp only [criticalDissipation, criticalCurrent, Finset.range_zero,
      Finset.sum_empty, mul_zero, neg_zero, add_zero]
    exact hasDerivAt_const t (0 : ℝ)
  | succ N ih =>
    have hprev := ih (fun i hi => ha i (Finset.mem_range.mpr
      (Nat.lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self N))))
    have hlast := ha N (Finset.mem_range.mpr (Nat.lt_succ_self N))
    have hsum := hprev.add ((hlast.mul hlast).const_mul (lam N))
    convert! hsum using 1
    · funext s
      simp [criticalEnergy, Finset.sum_range_succ, pow_two]
    · simp only [criticalDissipation, criticalCurrent, Finset.sum_range_succ]
      ring

theorem critical_balance_of_modal (nu T : ℝ) (lam : ℕ → ℝ)
    (a b : ℝ → ℕ → ℝ) (N : ℕ) (D C : ℝ → ℝ)
    (hnu : 0 < nu) (hlam : ∀ i, 0 ≤ lam i)
    (ha : ∀ t ∈ Set.Ico 0 T, ∀ i ∈ Finset.range N,
      HasDerivAt (fun s => a s i) (-nu * (lam i)^2 * a t i - b t i) t)
    (hD : ∀ t ∈ Set.Ico 0 T, HasDerivAt D (criticalDissipation lam a N t) t)
    (hC : ∀ t ∈ Set.Ico 0 T,
      HasDerivAt C (criticalSourceDensity nu lam a b N t) t)
    (hD0 : D 0 = 0) (hC0 : C 0 = 0) :
    ∀ t ∈ Set.Ico 0 T,
      criticalEnergy lam a N t + nu * D t ≤ criticalEnergy lam a N 0 + C t := by
  intro t ht
  let F : ℝ → ℝ := fun s => criticalEnergy lam a N s + nu * D s - C s
  let F' : ℝ → ℝ := fun s =>
    -2 * nu * criticalDissipation lam a N s + 2 * criticalCurrent lam a b N s +
      nu * criticalDissipation lam a N s - criticalSourceDensity nu lam a b N s
  have hF : ∀ s ∈ Set.Icc 0 t, HasDerivAt F (F' s) s := by
    intro s hs
    have hsT : s ∈ Set.Ico 0 T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    exact ((criticalEnergy_hasDerivAt nu lam a b N s (ha s hsT)).add
      ((hD s hsT).const_mul nu)).sub (hC s hsT)
  have hmono : AntitoneOn F (Set.Icc 0 t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
    · intro s hs
      exact (hF s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hF s (Set.mem_of_mem_of_subset hs interior_subset)).hasDerivWithinAt
    · intro s hs
      have h := critical_young nu lam a b hnu hlam N s
      dsimp [F']
      linarith
  have hle := hmono (show 0 ∈ Set.Icc 0 t from ⟨le_rfl, ht.1⟩)
    (show t ∈ Set.Icc 0 t from ⟨ht.1, le_rfl⟩) ht.1
  dsimp [F] at hle
  rw [hD0, hC0] at hle
  linarith

/- The nonspectral viscous coefficient is absorbed explicitly into the
effective source. This identity never assumes diagonalization. -/
noncomputable def effectiveSource (nu : ℝ) (lam : ℕ → ℝ)
    (a viscous b : ℝ → ℕ → ℝ) (t : ℝ) (i : ℕ) : ℝ :=
  b t i + nu * (viscous t i - (lam i)^2 * a t i)

theorem effectiveSource_modal_identity (nu : ℝ) (lam : ℕ → ℝ)
    (a viscous b : ℝ → ℕ → ℝ) (t : ℝ) (i : ℕ) :
    -nu * (lam i)^2 * a t i - effectiveSource nu lam a viscous b t i =
      -nu * viscous t i - b t i := by
  unfold effectiveSource
  ring

theorem effectiveSource_modal_derivative (nu : ℝ) (lam : ℕ → ℝ)
    (a viscous b : ℝ → ℕ → ℝ) (t : ℝ) (i : ℕ)
    (ha : HasDerivAt (fun s => a s i) (-nu * viscous t i - b t i) t) :
    HasDerivAt (fun s => a s i)
      (-nu * (lam i)^2 * a t i - effectiveSource nu lam a viscous b t i) t := by
  simpa only [effectiveSource_modal_identity] using ha

theorem effectiveSource_current_decomposition (nu : ℝ) (lam : ℕ → ℝ)
    (a viscous b : ℝ → ℕ → ℝ) (N : ℕ) (t : ℝ) :
    criticalCurrent lam a (effectiveSource nu lam a viscous b) N t =
      criticalCurrent lam a b N t - nu *
        ∑ i ∈ Finset.range N, lam i * a t i * (viscous t i - (lam i)^2 * a t i) := by
  have heq : (fun i => lam i * a t i * effectiveSource nu lam a viscous b t i) =
      (fun i => lam i * a t i * b t i +
        nu * (lam i * a t i * (viscous t i - (lam i)^2 * a t i))) := by
    funext i
    unfold effectiveSource
    ring
  unfold criticalCurrent
  rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end NSE
