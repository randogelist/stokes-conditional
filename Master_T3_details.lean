import Fefferman.DerivationSupport

set_option autoImplicit false

namespace Fefferman

abbrev T3Wave := Fin 3 → Int

def T3WaveAdd (p q : T3Wave) : T3Wave := fun j => p j + q j

def T3Triad (k p q : T3Wave) : Prop := k = T3WaveAdd p q

/- Finite Fourier algebra. The actual complex field, unit-periodic characters,
   and their analytic interpretation must be supplied; no convergence is used. -/
structure T3FourierAlgebra where
  Coefficient : Type
  Point : Type
  zero : Coefficient
  add : Coefficient → Coefficient → Coefficient
  mul : Coefficient → Coefficient → Coefficient
  zeroAdd : ∀ x, add zero x = x
  addAssoc : ∀ x y z, add (add x y) z = add x (add y z)
  mulZero : ∀ x, mul x zero = zero
  zeroMul : ∀ x, mul zero x = zero
  mulComm : ∀ x y, mul x y = mul y x
  mulAssoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mulAdd : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  addMul : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)
  character : T3Wave → Point → Coefficient
  characterProduct : ∀ p q x,
    mul (character p x) (character q x) = character (T3WaveAdd p q) x

abbrev T3FourierTerm (F : T3FourierAlgebra) := T3Wave × F.Coefficient

def T3TermEval (F : T3FourierAlgebra) (term : T3FourierTerm F) (x : F.Point) : F.Coefficient :=
  F.mul term.2 (F.character term.1 x)

def T3TermProduct (F : T3FourierAlgebra) (p q : T3FourierTerm F) : T3FourierTerm F :=
  (T3WaveAdd p.1 q.1, F.mul p.2 q.2)

def T3PolynomialEval (F : T3FourierAlgebra) : List (T3FourierTerm F) → F.Point → F.Coefficient
  | [], _ => F.zero
  | term :: rest, x => F.add (T3TermEval F term x) (T3PolynomialEval F rest x)

def T3ProductTerms (F : T3FourierAlgebra) :
    List (T3FourierTerm F) → List (T3FourierTerm F) → List (T3FourierTerm F)
  | [], _ => []
  | p :: rest, q => q.map (T3TermProduct F p) ++ T3ProductTerms F rest q

/- Periodic renewal data on one fixed admissible input. These are finite-cut
   ledgers, not an asserted Fourier realization of an arbitrary NSE solution. -/
structure T3RenewalWitness {a : Analysis} (i : ForcedInput a .periodic) where
  Cut : Type
  Time : Type
  before : Time → Time → Prop
  cutTime : Nat → Time
  sequence : Cut → Nat → a.Scalar
  paid : Cut → Nat → a.Scalar
  action : Cut → Time → a.Scalar
  forceCost : Cut → Time → a.Scalar
  mass : Cut → Time → a.Scalar
  dissipation : Cut → Time → a.Scalar
  fullMass : Time → a.Scalar
  fullDissipation : Time → a.Scalar
  gap : a.Scalar
  seedMax : a.Scalar
  paidMax : a.Scalar
  forceMax : a.Scalar
  initialMass : a.Scalar
  epsilon : a.Scalar
  gapPositive : a.lt a.zero gap
  positiveDissipation : a.lt a.zero epsilon
  sequenceNonnegative : ∀ c n, a.le a.zero (sequence c n)
  sequenceSeedBound : ∀ c, a.le (sequence c 0) seedMax
  renewalStep : ∀ c n,
    a.le (a.add (sequence c (n + 1)) (a.mul gap (sequence c n)))
      (a.add (sequence c n) (paid c n))
  paidPrefixBound : ∀ c n, a.le (ledgerPrefix a (paid c) n) paidMax
  cofinal : ∀ t, ∃ n, before t (cutTime n)
  actionMonotone : ∀ c t s, before t s → a.le (action c t) (action c s)
  sampleRealization : ∀ c n, a.le (action c (cutTime n)) (ledgerPrefix a (sequence c) n)
  forcingBound : ∀ c t, a.le (forceCost c t) forceMax
  massNonnegative : ∀ c t, a.le a.zero (mass c t)
  dissipationNonnegative : ∀ c t, a.le a.zero (dissipation c t)
  criticalBalance : ∀ c t, a.le (a.add (mass c t) (a.mul epsilon (dissipation c t)))
    (a.add initialMass (a.add (action c t) (forceCost c t)))
  massReadout : ∀ t, FullLedgerReadout a (fun c => mass c t) (fullMass t)
  dissipationReadout : ∀ t, FullLedgerReadout a (fun c => dissipation c t) (fullDissipation t)

def T3ActionBudget {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .periodic} (w : T3RenewalWitness i) : a.Scalar :=
  o.divide (a.add w.seedMax w.paidMax) w.gap

def T3CriticalBudget {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .periodic} (w : T3RenewalWitness i) : a.Scalar :=
  a.add w.initialMass (a.add (T3ActionBudget o w) w.forceMax)

def T3CriticalControl {a : Analysis} (i : ForcedInput a .periodic)
    (w : T3RenewalWitness i) : Prop :=
  ledgerBounded a w.fullMass ∧ ledgerBounded a w.fullDissipation

abbrev T3DerivationModel (a : Analysis) :=
  DerivationModel a .periodic (fun i => T3RenewalWitness i)

abbrev T3DerivationPorts {a : Analysis} (m : T3DerivationModel a) :=
  DerivationPorts m (fun i w => T3CriticalControl i w)

abbrev T3RegularDerivationPorts {a : Analysis} (m : T3DerivationModel a) :=
  RegularDerivationPorts m (fun i w => T3CriticalControl i w)

end Fefferman
