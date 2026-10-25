import Fefferman.Statements

set_option autoImplicit false

namespace Fefferman

/- Zero-force admissibility is a realization obligation because the analytic
   operators above are interface parameters, with no built-in field laws. -/
def ZeroForceAdmissible (a : Analysis) (d : Domain) : Prop :=
  admissibleForce a d (zeroForce a)

theorem zeroBreakdown_iff_not_unforced (a : Analysis) (d : Domain)
    (ν : PositiveViscosity a) :
    zeroForceBreakdownAt a d ν ↔ ¬ unforcedGlobalAt a d ν := by
  constructor
  · intro h hall
    cases h with
    | intro u₀ hu => exact hu.2 (hall u₀ hu.1)
  · intro hnot
    apply Classical.byContradiction
    intro hnone
    apply hnot
    intro u₀ hu
    apply Classical.byContradiction
    intro hmissing
    exact hnone ⟨u₀, hu, hmissing⟩

theorem breakdown_iff_not_forced (a : Analysis) (d : Domain)
    (ν : PositiveViscosity a) :
    breakdownAt a d ν ↔ ¬ forcedGlobalAt a d ν := by
  constructor
  · intro h hall
    cases h with
    | intro u₀ hu =>
      cases hu.2 with
      | intro f hf => exact hf.2 (hall u₀ hu.1 f hf.1)
  · intro hnot
    apply Classical.byContradiction
    intro hnone
    apply hnot
    intro u₀ hu f hf
    apply Classical.byContradiction
    intro hmissing
    exact hnone ⟨u₀, hu, f, hf, hmissing⟩

theorem zeroBreakdown_to_breakdown (a : Analysis) (d : Domain)
    (ν : PositiveViscosity a) (hz : ZeroForceAdmissible a d)
    (h : zeroForceBreakdownAt a d ν) : breakdownAt a d ν := by
  cases h with
  | intro u₀ hu => exact ⟨u₀, hu.1, zeroForce a, hz, hu.2⟩

theorem forced_to_unforced (a : Analysis) (d : Domain)
    (ν : PositiveViscosity a) (hz : ZeroForceAdmissible a d)
    (h : forcedGlobalAt a d ν) : unforcedGlobalAt a d ν := by
  intro u₀ hu
  exact h u₀ hu (zeroForce a) hz

theorem failure_A_at_to_C_at (a : Analysis) (ν : PositiveViscosity a)
    (hz : ZeroForceAdmissible a .wholeSpace)
    (h : ¬ statementAt a ν .A) : statementAt a ν .C :=
  zeroBreakdown_to_breakdown a .wholeSpace ν hz
    ((zeroBreakdown_iff_not_unforced a .wholeSpace ν).mpr h)

theorem failure_B_at_to_D_at (a : Analysis) (ν : PositiveViscosity a)
    (hz : ZeroForceAdmissible a .periodic)
    (h : ¬ statementAt a ν .B) : statementAt a ν .D :=
  zeroBreakdown_to_breakdown a .periodic ν hz
    ((zeroBreakdown_iff_not_unforced a .periodic ν).mpr h)

/- A failure at some viscosity gives a witness at that viscosity.
   It does not, by quantifier logic alone, produce C for EVERY viscosity. -/
theorem failure_A_has_viscosity_witness (a : Analysis)
    (hz : ZeroForceAdmissible a .wholeSpace) (h : ¬ A a) :
    ∃ ν : PositiveViscosity a, statementAt a ν .C := by
  apply Classical.byContradiction
  intro hnone
  apply h
  intro ν
  apply Classical.byContradiction
  intro hfail
  exact hnone ⟨ν, failure_A_at_to_C_at a ν hz hfail⟩

theorem A_excludes_zeroForce_breakdown (a : Analysis) (h : A a)
    (ν : PositiveViscosity a) : ¬ zeroForceBreakdownAt a .wholeSpace ν := by
  intro hc
  exact (zeroBreakdown_iff_not_unforced a .wholeSpace ν).mp hc (h ν)

/- A/B and C/D use different force quantifiers. No theorem here identifies
   A with not-C, or B with not-D. No exclusive four-way partition is claimed. -/
end Fefferman
