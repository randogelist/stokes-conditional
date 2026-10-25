import Mathlib

namespace NSEForcingRegularityClasses

noncomputable section

/-!
Lean mirror of the GP-independent Rocq forcing classification.
This file classifies forcing exponents only. It does NOT claim that the
forcing class alone determines regularity or breakdown of the NSE solution.
-/

/-- Scaling exponent for the forcing norm `L^q_t H^s_x` under 3D NSE scaling. -/
def forcingScalingExponent (q s : ℝ) : ℝ := s + (3 / 2 : ℝ) - 2 / q

/-- Scaling-critical forcing pair. -/
def CriticalForcingPair (q s : ℝ) : Prop := 0 < q ∧ forcingScalingExponent q s = 0

/-- Natural Leray--Hopf forcing exponent range at fixed `L^2_t`. -/
def L2LHAdmissibleExponent (s : ℝ) : Prop := (-1 : ℝ) ≤ s

/-- Critical-or-smoother forcing exponent at fixed `L^2_t`. -/
def L2CriticalRegularExponent (s : ℝ) : Prop := (-1 / 2 : ℝ) ≤ s

/-- Rough but still Leray--Hopf admissible forcing exponent. -/
def L2IrregularButLHExponent (s : ℝ) : Prop := (-1 : ℝ) ≤ s ∧ s < (-1 / 2 : ℝ)

/-- Strictly smoother than critical at fixed `L^2_t`. -/
def L2SmoothExponent (s : ℝ) : Prop := (-1 / 2 : ℝ) < s

/-- Exact critical boundary at fixed `L^2_t`. -/
def L2ExactCriticalExponent (s : ℝ) : Prop := s = (-1 / 2 : ℝ)

/-- Strict rough/LH side of the critical boundary. -/
def L2RoughLHExponent (s : ℝ) : Prop := (-1 : ℝ) ≤ s ∧ s < (-1 / 2 : ℝ)

/-- Power-tail model threshold for `H^{-1}`. -/
def LHPowerTailExponent (α : ℝ) : Prop := (1 / 2 : ℝ) < α

/-- Power-tail model threshold for critical `H^{-1/2}` entrance. -/
def CriticalPowerTailExponent (α : ℝ) : Prop := (1 : ℝ) < α

/-- Exact power-tail boundary. -/
def ExactCriticalPowerTailExponent (α : ℝ) : Prop := α = (1 : ℝ)

/-- Strict power-tail rough strip between the LH and critical thresholds. -/
def RoughLHPowerTailExponent (α : ℝ) : Prop := (1 / 2 : ℝ) < α ∧ α < (1 : ℝ)

/-- Full irregular-but-LH power-tail strip, including the logarithmic boundary `α = 1`. -/
def IrregularButLHPowerTailExponent (α : ℝ) : Prop :=
  (1 / 2 : ℝ) < α ∧ α ≤ (1 : ℝ)

theorem CRITICAL_FORCING_SCALING_LINE (q s : ℝ) (hq : 0 < q) :
    CriticalForcingPair q s ↔ s = 2 / q - 3 / 2 := by
  constructor
  · rintro ⟨_, h⟩
    unfold forcingScalingExponent at h
    linarith
  · intro hs
    refine ⟨hq, ?_⟩
    unfold forcingScalingExponent
    rw [hs]
    ring

theorem L2_TIME_CRITICAL_SPATIAL_EXPONENT_MINUS_HALF :
    CriticalForcingPair 2 (-1 / 2 : ℝ) := by
  norm_num [CriticalForcingPair, forcingScalingExponent]

theorem L1_TIME_CRITICAL_SPATIAL_EXPONENT_PLUS_HALF :
    CriticalForcingPair 1 (1 / 2 : ℝ) := by
  norm_num [CriticalForcingPair, forcingScalingExponent]

theorem REGULAR_FORCE_EXPONENT_IMPLIES_LH_ADMISSIBLE_EXPONENT (s : ℝ)
    (h : L2CriticalRegularExponent s) : L2LHAdmissibleExponent s := by
  unfold L2CriticalRegularExponent at h
  unfold L2LHAdmissibleExponent
  linarith

theorem LH_EXPONENT_PARTITION_REGULAR_OR_IRREGULAR (s : ℝ)
    (hLH : L2LHAdmissibleExponent s) :
    L2CriticalRegularExponent s ∨ L2IrregularButLHExponent s := by
  unfold L2LHAdmissibleExponent at hLH
  simp only [L2CriticalRegularExponent, L2IrregularButLHExponent]
  by_cases h : (-1 / 2 : ℝ) ≤ s
  · exact Or.inl h
  · exact Or.inr ⟨hLH, lt_of_not_ge h⟩

theorem REGULAR_AND_IRREGULAR_FORCE_CLASSES_DISJOINT (s : ℝ) :
    ¬ (L2CriticalRegularExponent s ∧ L2IrregularButLHExponent s) := by
  simp only [L2CriticalRegularExponent, L2IrregularButLHExponent]
  linarith

theorem LH_POWER_TAIL_THRESHOLD_HALF (α : ℝ) :
    LHPowerTailExponent α ↔ (1 / 2 : ℝ) < α := by
  rfl

theorem CRITICAL_POWER_TAIL_THRESHOLD_ONE (α : ℝ) :
    CriticalPowerTailExponent α ↔ (1 : ℝ) < α := by
  rfl

theorem IRREGULAR_BUT_LH_POWER_TAIL_STRIP_HALF_TO_ONE (α : ℝ) :
    IrregularButLHPowerTailExponent α ↔ ((1 / 2 : ℝ) < α ∧ α ≤ 1) := by
  rfl

theorem L2_LH_TRICHOTOMY_SMOOTH_CRITICAL_ROUGH (s : ℝ)
    (hLH : L2LHAdmissibleExponent s) :
    L2SmoothExponent s ∨ L2ExactCriticalExponent s ∨ L2RoughLHExponent s := by
  unfold L2LHAdmissibleExponent at hLH
  simp only [L2SmoothExponent, L2ExactCriticalExponent, L2RoughLHExponent]
  rcases lt_trichotomy s (-1 / 2 : ℝ) with hlt | heq | hgt
  · exact Or.inr (Or.inr ⟨hLH, hlt⟩)
  · exact Or.inr (Or.inl heq)
  · exact Or.inl hgt

theorem EXACT_CRITICAL_IFF_SCALING_ZERO (s : ℝ) :
    L2ExactCriticalExponent s ↔ forcingScalingExponent 2 s = 0 := by
  simp only [L2ExactCriticalExponent, forcingScalingExponent]
  norm_num
  constructor <;> intro h <;> linarith

theorem SMOOTH_IFF_SCALING_POSITIVE (s : ℝ) :
    L2SmoothExponent s ↔ 0 < forcingScalingExponent 2 s := by
  simp only [L2SmoothExponent, forcingScalingExponent]
  norm_num
  constructor <;> intro h <;> linarith

theorem ROUGH_LH_IFF_SCALING_NEGATIVE_WITH_LH (s : ℝ) :
    L2RoughLHExponent s ↔
      (L2LHAdmissibleExponent s ∧ forcingScalingExponent 2 s < 0) := by
  constructor
  · intro h
    change (-1 : ℝ) ≤ s ∧ s < (-1 / 2 : ℝ) at h
    rcases h with ⟨hLH, hRough⟩
    constructor
    · exact hLH
    · dsimp [forcingScalingExponent]
      norm_num
      linarith
  · intro h
    rcases h with ⟨hLH, hNeg⟩
    change (-1 : ℝ) ≤ s at hLH
    dsimp [forcingScalingExponent] at hNeg
    norm_num at hNeg
    change (-1 : ℝ) ≤ s ∧ s < (-1 / 2 : ℝ)
    constructor
    · exact hLH
    · linarith

theorem POWER_TAIL_TRICHOTOMY (α : ℝ) (hLH : LHPowerTailExponent α) :
    CriticalPowerTailExponent α ∨
      ExactCriticalPowerTailExponent α ∨
      RoughLHPowerTailExponent α := by
  unfold LHPowerTailExponent at hLH
  simp only [CriticalPowerTailExponent, ExactCriticalPowerTailExponent, RoughLHPowerTailExponent]
  rcases lt_trichotomy α (1 : ℝ) with hlt | heq | hgt
  · exact Or.inr (Or.inr ⟨hLH, hlt⟩)
  · exact Or.inr (Or.inl heq)
  · exact Or.inl hgt

theorem POWER_TAIL_ALPHA_ONE_EXACT_BOUNDARY :
    ExactCriticalPowerTailExponent 1 := by
  rfl

theorem POWER_TAIL_ALPHA_ONE_FAILS_CRITICAL_ENTRANCE :
    ¬ CriticalPowerTailExponent 1 := by
  norm_num [CriticalPowerTailExponent]

/-- Marker theorem: the file intentionally makes no solution-regularity claim from force class alone. -/
theorem SOLUTION_REGULARITY_FROM_FORCE_CLASS_ALONE_NOT_CLAIMED : True := by
  trivial

/-- Marker theorem: the file intentionally makes no solution-breakdown claim from force class alone. -/
theorem SOLUTION_BREAKDOWN_FROM_FORCE_CLASS_ALONE_NOT_CLAIMED : True := by
  trivial

/-- Open analytic frontier marker: actual Sobolev-space realization is not formalized here. -/
def ActualSobolevSpaceRealizationFrontier : Prop := True

theorem STATUS : True := by trivial


end

end NSEForcingRegularityClasses
