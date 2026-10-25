import Fefferman.Analysis

set_option autoImplicit false

namespace Fefferman

inductive Domain where
  | wholeSpace
  | periodic
  deriving DecidableEq, Repr

inductive Case where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

def admissibleInitial (a : Analysis) (d : Domain) (u₀ : Initial a) : Prop :=
  initialSmooth a u₀ ∧ initialDivergenceFree a u₀ ∧
    match d with
    | .wholeSpace => clause04 a u₀
    | .periodic => initialPeriodic a u₀

def admissibleForce (a : Analysis) (d : Domain) (f : Force a) : Prop :=
  vectorSmooth a f ∧
    match d with
    | .wholeSpace => clause05 a f
    | .periodic => vectorPeriodic a f ∧ clause09 a f

def globalSolution (a : Analysis) (d : Domain) (ν : PositiveViscosity a)
    (u₀ : Initial a) (f : Force a) (s : Solution a) : Prop :=
  clause01 a ν f s ∧ clause02 a s ∧ clause03 a u₀ s ∧
    match d with
    | .wholeSpace => clause06 a s ∧ clause07 a s
    | .periodic => clause10 a s ∧ clause11 a s ∧ periodicPressureErratum a s

def hasGlobalSolution (a : Analysis) (d : Domain) (ν : PositiveViscosity a)
    (u₀ : Initial a) (f : Force a) : Prop :=
  ∃ s : Solution a, globalSolution a d ν u₀ f s

def unforcedGlobalAt (a : Analysis) (d : Domain) (ν : PositiveViscosity a) : Prop :=
  ∀ u₀, admissibleInitial a d u₀ → hasGlobalSolution a d ν u₀ (zeroForce a)

def forcedGlobalAt (a : Analysis) (d : Domain) (ν : PositiveViscosity a) : Prop :=
  ∀ u₀, admissibleInitial a d u₀ → ∀ f, admissibleForce a d f →
    hasGlobalSolution a d ν u₀ f

def breakdownAt (a : Analysis) (d : Domain) (ν : PositiveViscosity a) : Prop :=
  ∃ u₀, admissibleInitial a d u₀ ∧ ∃ f, admissibleForce a d f ∧
    ¬ hasGlobalSolution a d ν u₀ f

def zeroForceBreakdownAt (a : Analysis) (d : Domain)
    (ν : PositiveViscosity a) : Prop :=
  ∃ u₀, admissibleInitial a d u₀ ∧
    ¬ hasGlobalSolution a d ν u₀ (zeroForce a)

/- Fixed-viscosity statements. Breakdown means nonexistence of a qualifying
   global solution, not merely failure of a chosen numerical trajectory. -/
def statementAt (a : Analysis) (ν : PositiveViscosity a) : Case → Prop
  | .A => unforcedGlobalAt a .wholeSpace ν
  | .B => unforcedGlobalAt a .periodic ν
  | .C => breakdownAt a .wholeSpace ν
  | .D => breakdownAt a .periodic ν

/- "Take nu > 0": keep the arbitrary-viscosity quantifier explicit.
   No viscosity-normalization/scaling theorem is silently assumed. -/
def statement (a : Analysis) (c : Case) : Prop :=
  ∀ ν : PositiveViscosity a, statementAt a ν c

abbrev A (a : Analysis) := statement a .A
abbrev B (a : Analysis) := statement a .B
abbrev C (a : Analysis) := statement a .C
abbrev D (a : Analysis) := statement a .D

/- This record is only a target type. No instance is constructed. -/
structure ClassifiedResult (a : Analysis) where
  selectedCase : Case
  proof : statement a selectedCase

structure UnforcedInput (a : Analysis) (d : Domain) where
  viscosity : PositiveViscosity a
  initial : Initial a
  admissible : admissibleInitial a d initial

def inputSolved {a : Analysis} {d : Domain} (i : UnforcedInput a d) : Prop :=
  hasGlobalSolution a d i.viscosity i.initial (zeroForce a)

end Fefferman
