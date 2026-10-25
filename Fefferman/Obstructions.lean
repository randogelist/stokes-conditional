import Fefferman.Statements

set_option autoImplicit false

namespace Fefferman

structure BreakdownWitnessAt (a : Analysis) (d : Domain)
    (ν : PositiveViscosity a) where
  initial : Initial a
  force : Force a
  initialAdmissible : admissibleInitial a d initial
  forceAdmissible : admissibleForce a d force
  noGlobalSolution : ¬ hasGlobalSolution a d ν initial force

theorem breakdown_of_witness {a : Analysis} {d : Domain}
    {ν : PositiveViscosity a} (w : BreakdownWitnessAt a d ν) : breakdownAt a d ν :=
  ⟨w.initial, w.initialAdmissible, w.force, w.forceAdmissible, w.noGlobalSolution⟩

theorem C_at_of_witness {a : Analysis} {ν : PositiveViscosity a}
    (w : BreakdownWitnessAt a .wholeSpace ν) : statementAt a ν .C :=
  breakdown_of_witness w

theorem D_at_of_witness {a : Analysis} {ν : PositiveViscosity a}
    (w : BreakdownWitnessAt a .periodic ν) : statementAt a ν .D :=
  breakdown_of_witness w

theorem C_of_witness_family {a : Analysis}
    (w : (ν : PositiveViscosity a) → BreakdownWitnessAt a .wholeSpace ν) : C a :=
  fun ν => C_at_of_witness (w ν)

theorem D_of_witness_family {a : Analysis}
    (w : (ν : PositiveViscosity a) → BreakdownWitnessAt a .periodic ν) : D a :=
  fun ν => D_at_of_witness (w ν)

end Fefferman
