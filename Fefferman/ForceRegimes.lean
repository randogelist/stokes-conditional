import Fefferman.Statements

set_option autoImplicit false

namespace Fefferman

/- The semantic alternatives use the exact Fefferman global-output clauses.
   Regular means every admissible datum; breakdown means at least one datum. -/
def regularForceAt (a : Analysis) (d : Domain) (ν : PositiveViscosity a)
    (f : Force a) : Prop :=
  admissibleForce a d f ∧
    ∀ u₀, admissibleInitial a d u₀ → hasGlobalSolution a d ν u₀ f

def breakdownForceAt (a : Analysis) (d : Domain) (ν : PositiveViscosity a)
    (f : Force a) : Prop :=
  admissibleForce a d f ∧
    ∃ u₀, admissibleInitial a d u₀ ∧ ¬ hasGlobalSolution a d ν u₀ f

/- Research criteria, awaiting concrete analytic definitions and proofs.
   These predicates may leave some admissible forces uncertified. -/
structure ForceRegimes (a : Analysis) (d : Domain) where
  regular : PositiveViscosity a → Force a → Prop
  breakdown : PositiveViscosity a → Force a → Prop

structure ForceRegimeSoundness (a : Analysis) (d : Domain)
    (r : ForceRegimes a d) : Prop where
  regularSound : ∀ ν f, r.regular ν f → regularForceAt a d ν f
  breakdownSound : ∀ ν f, r.breakdown ν f → breakdownForceAt a d ν f

/- Unresolved relative to these criteria, not a third truth value for NSE. -/
def unresolvedForceAt {a : Analysis} {d : Domain} (r : ForceRegimes a d)
    (ν : PositiveViscosity a) (f : Force a) : Prop :=
  admissibleForce a d f ∧ ¬ r.regular ν f ∧ ¬ r.breakdown ν f

theorem regularForceAt_excludes_breakdownForceAt {a : Analysis} {d : Domain}
    {ν : PositiveViscosity a} {f : Force a}
    (hR : regularForceAt a d ν f) : ¬ breakdownForceAt a d ν f := by
  intro hB
  cases hB.2 with
  | intro u₀ hu₀ => exact hu₀.2 (hR.2 u₀ hu₀.1)

theorem breakdownAt_iff_exists_breakdownForce (a : Analysis) (d : Domain)
    (ν : PositiveViscosity a) :
    breakdownAt a d ν ↔ ∃ f, breakdownForceAt a d ν f := by
  constructor
  · intro h
    cases h with
    | intro u₀ hu₀ =>
      cases hu₀.2 with
      | intro f hf => exact ⟨f, hf.1, u₀, hu₀.1, hf.2⟩
  · intro h
    cases h with
    | intro f hf =>
      cases hf.2 with
      | intro u₀ hu₀ => exact ⟨u₀, hu₀.1, f, hf.1, hu₀.2⟩

/- This is a classical logical alternative, not an effective classifier. -/
theorem admissibleForce_regular_or_breakdown {a : Analysis} {d : Domain}
    (ν : PositiveViscosity a) (f : Force a) (hf : admissibleForce a d f) :
    regularForceAt a d ν f ∨ breakdownForceAt a d ν f := by
  cases Classical.em (∀ u₀, admissibleInitial a d u₀ →
      hasGlobalSolution a d ν u₀ f) with
  | inl h => exact Or.inl ⟨hf, h⟩
  | inr h =>
    apply Or.inr
    constructor
    · exact hf
    · apply Classical.byContradiction
      intro hnone
      apply h
      intro u₀ hu₀
      apply Classical.byContradiction
      intro hno
      exact hnone ⟨u₀, hu₀, hno⟩

theorem breakdownForce_excludes_regular_certificate {a : Analysis} {d : Domain}
    {r : ForceRegimes a d} (h : ForceRegimeSoundness a d r)
    {ν : PositiveViscosity a} {f : Force a}
    (hB : breakdownForceAt a d ν f) : ¬ r.regular ν f := by
  intro hR
  exact regularForceAt_excludes_breakdownForceAt (h.regularSound ν f hR) hB

theorem certified_regimes_disjoint {a : Analysis} {d : Domain}
    {r : ForceRegimes a d} (h : ForceRegimeSoundness a d r)
    (ν : PositiveViscosity a) (f : Force a)
    (hR : r.regular ν f) : ¬ r.breakdown ν f := by
  intro hB
  exact breakdownForce_excludes_regular_certificate h (h.breakdownSound ν f hB) hR

theorem admissibleForce_certificate_trichotomy {a : Analysis} {d : Domain}
    (r : ForceRegimes a d) (ν : PositiveViscosity a) (f : Force a)
    (hf : admissibleForce a d f) :
    r.regular ν f ∨ r.breakdown ν f ∨ unresolvedForceAt r ν f := by
  cases Classical.em (r.regular ν f) with
  | inl hR => exact Or.inl hR
  | inr hR =>
    cases Classical.em (r.breakdown ν f) with
    | inl hB => exact Or.inr (Or.inl hB)
    | inr hB => exact Or.inr (Or.inr ⟨hf, hR, hB⟩)

end Fefferman
