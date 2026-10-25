import Fefferman.ForceRegimes

set_option autoImplicit false

namespace Fefferman

/- Shared domain contracts and conditional logical lemmas. -/
structure DomainMasterCore (a : Analysis) (d : Domain)
    (r : ForceRegimes a d) : Prop where
  sound : ForceRegimeSoundness a d r
  zeroRegular : ∀ ν, r.regular ν (zeroForce a)

structure DomainMaster (a : Analysis) (d : Domain)
    (r : ForceRegimes a d) : Prop where
  core : DomainMasterCore a d r
  breakdownNonempty : ∀ ν, ∃ f, r.breakdown ν f

theorem masterCore_unforcedAt {a : Analysis} {d : Domain}
    {r : ForceRegimes a d} (h : DomainMasterCore a d r)
    (ν : PositiveViscosity a) : unforcedGlobalAt a d ν :=
  (h.sound.regularSound ν (zeroForce a) (h.zeroRegular ν)).2

theorem masterCore_breakdownAt_of_certificate {a : Analysis} {d : Domain}
    {r : ForceRegimes a d} (h : DomainMasterCore a d r)
    (ν : PositiveViscosity a) (f : Force a) (hf : r.breakdown ν f) :
    breakdownAt a d ν :=
  (breakdownAt_iff_exists_breakdownForce a d ν).mpr
    ⟨f, h.sound.breakdownSound ν f hf⟩

theorem masterCore_no_breakdownAt_of_all_regular {a : Analysis} {d : Domain}
    {r : ForceRegimes a d} (h : DomainMasterCore a d r)
    (ν : PositiveViscosity a)
    (cover : ∀ f, admissibleForce a d f → r.regular ν f) :
    ¬ breakdownAt a d ν := by
  intro hB
  cases (breakdownAt_iff_exists_breakdownForce a d ν).mp hB with
  | intro f hf =>
    exact breakdownForce_excludes_regular_certificate h.sound hf (cover f hf.1)

theorem masterCore_breakdown_certificate_nonzero {a : Analysis} {d : Domain}
    {r : ForceRegimes a d} (h : DomainMasterCore a d r)
    (ν : PositiveViscosity a) (f : Force a) (hf : r.breakdown ν f) :
    f ≠ zeroForce a := by
  intro heq
  have hz : r.breakdown ν (zeroForce a) := heq ▸ hf
  exact certified_regimes_disjoint h.sound ν (zeroForce a) (h.zeroRegular ν) hz

theorem master_breakdownAt {a : Analysis} {d : Domain}
    {r : ForceRegimes a d} (h : DomainMaster a d r)
    (ν : PositiveViscosity a) : breakdownAt a d ν := by
  cases h.breakdownNonempty ν with
  | intro f hf => exact masterCore_breakdownAt_of_certificate h.core ν f hf

theorem master_no_all_regular_at {a : Analysis} {d : Domain}
    {r : ForceRegimes a d} (h : DomainMaster a d r)
    (ν : PositiveViscosity a) :
    ¬ (∀ f, admissibleForce a d f → r.regular ν f) := by
  intro cover
  exact masterCore_no_breakdownAt_of_all_regular h.core ν cover
    (master_breakdownAt h ν)

end Fefferman
