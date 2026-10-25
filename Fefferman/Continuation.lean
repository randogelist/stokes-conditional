import Fefferman.Statements

set_option autoImplicit false

namespace Fefferman

/- A trajectory may encode a maximal classical solution on its own lifespan.
   Its type depends on the SAME viscosity and initial datum. -/
structure LocalTheory (a : Analysis) (d : Domain) where
  Trajectory : UnforcedInput a d → Type
  raw : (i : UnforcedInput a d) → Trajectory i → Prop
  continues : (i : UnforcedInput a d) → Trajectory i → Prop

/- These are unfilled analytic proof obligations. In particular, the second
   field must establish global lifespan AND every clause of inputSolved,
   including pressure and the uniform energy bound in the whole-space case. -/
structure LocalTheoryPorts {a : Analysis} {d : Domain}
    (L : LocalTheory a d) : Prop where
  localExistence : ∀ i, ∃ u : L.Trajectory i, L.raw i u
  globalize : ∀ i, (∃ u : L.Trajectory i, L.raw i u) →
    (∀ u : L.Trajectory i, L.raw i u → L.continues i u) → inputSolved i

theorem inputs_solved_of_continuation {a : Analysis} {d : Domain}
    (L : LocalTheory a d) (P : LocalTheoryPorts L)
    (hc : ∀ i (u : L.Trajectory i), L.raw i u → L.continues i u) :
    ∀ i : UnforcedInput a d, inputSolved i := by
  intro i
  exact P.globalize i (P.localExistence i) (hc i)

theorem unforced_from_inputs {a : Analysis} {d : Domain}
    (h : ∀ i : UnforcedInput a d, inputSolved i) :
    ∀ ν, unforcedGlobalAt a d ν := by
  intro ν u₀ hu
  exact h { viscosity := ν, initial := u₀, admissible := hu }

theorem A_of_continuation {a : Analysis} (L : LocalTheory a .wholeSpace)
    (P : LocalTheoryPorts L)
    (hc : ∀ i (u : L.Trajectory i), L.raw i u → L.continues i u) : A a :=
  unforced_from_inputs (inputs_solved_of_continuation L P hc)

theorem B_of_continuation {a : Analysis} (L : LocalTheory a .periodic)
    (P : LocalTheoryPorts L)
    (hc : ∀ i (u : L.Trajectory i), L.raw i u → L.continues i u) : B a :=
  unforced_from_inputs (inputs_solved_of_continuation L P hc)

end Fefferman
