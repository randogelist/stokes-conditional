import Fefferman.DerivationSupport

set_option autoImplicit false

namespace Fefferman

/- R3 storage data on one fixed admissible input. All budgets are uniform
   over Cut and Time. Actual integrals and physical binding remain explicit. -/
structure R3StorageWitness {a : Analysis} (i : ForcedInput a .wholeSpace) where
  Cut : Type
  Time : Type
  initialStorage : Cut → a.Scalar
  storage : Cut → Time → a.Scalar
  crowd : Cut → Time → a.Scalar
  kinetic : Cut → Time → a.Scalar
  low : Cut → Time → a.Scalar
  high : Cut → Time → a.Scalar
  heat : Cut → Time → a.Scalar
  action : Cut → Time → a.Scalar
  forceCost : Cut → Time → a.Scalar
  mass : Cut → Time → a.Scalar
  dissipation : Cut → Time → a.Scalar
  fullMass : Time → a.Scalar
  storageMax : a.Scalar
  kineticMax : a.Scalar
  lowCoefficient : a.Scalar
  heatCoefficient : a.Scalar
  highMax : a.Scalar
  gamma : a.Scalar
  actionEnvelope : a.Scalar → a.Scalar
  forceMax : a.Scalar
  initialMass : a.Scalar
  epsilon : a.Scalar
  lowCoefficientNonnegative : a.le a.zero lowCoefficient
  heatCoefficientNonnegative : a.le a.zero heatCoefficient
  strictRetention : a.lt gamma a.one
  positiveDissipation : a.lt a.zero epsilon
  storageNonnegative : ∀ c t, a.le a.zero (storage c t)
  initialStorageBound : ∀ c, a.le (initialStorage c) storageMax
  kineticBound : ∀ c t, a.le (kinetic c t) kineticMax
  exactStorage : ∀ c t, a.add (storage c t) (crowd c t) =
    a.add (a.add (a.add (initialStorage c) (low c t)) (high c t)) (heat c t)
  lowPayment : ∀ c t, a.le (low c t) (a.mul lowCoefficient (kinetic c t))
  heatPayment : ∀ c t, a.le (heat c t) (a.mul heatCoefficient (kinetic c t))
  highAbsorption : ∀ c t, a.le (high c t) (a.add (a.mul gamma (crowd c t)) highMax)
  /- The NSOA90 occupation-to-action calculus port remains to be translated.
     Its source envelope uses exponential energy and quadratic action bounds. -/
  occupationToAction : ∀ bound, (∀ c t, a.le (crowd c t) bound) →
    ∀ c t, a.le (action c t) (actionEnvelope bound)
  forcingBound : ∀ c t, a.le (forceCost c t) forceMax
  massNonnegative : ∀ c t, a.le a.zero (mass c t)
  dissipationNonnegative : ∀ c t, a.le a.zero (dissipation c t)
  criticalBalance : ∀ c t, a.le (a.add (mass c t) (a.mul epsilon (dissipation c t)))
    (a.add initialMass (a.add (action c t) (forceCost c t)))
  massReadout : ∀ t, FullLedgerReadout a (fun c => mass c t) (fullMass t)

def R3StorageBudget {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .wholeSpace} (w : R3StorageWitness i) : a.Scalar :=
  o.divide
    (a.add (a.add (a.add w.storageMax (a.mul w.lowCoefficient w.kineticMax)) w.highMax)
      (a.mul w.heatCoefficient w.kineticMax))
    (a.add a.one (a.neg w.gamma))

def R3ActionBudget {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .wholeSpace} (w : R3StorageWitness i) : a.Scalar :=
  w.actionEnvelope (R3StorageBudget o w)

def R3CriticalBudget {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .wholeSpace} (w : R3StorageWitness i) : a.Scalar :=
  a.add w.initialMass (a.add (R3ActionBudget o w) w.forceMax)

def R3CriticalControl {a : Analysis} (i : ForcedInput a .wholeSpace)
    (w : R3StorageWitness i) : Prop :=
  ledgerBounded a w.fullMass

abbrev R3DerivationModel (a : Analysis) :=
  DerivationModel a .wholeSpace (fun i => R3StorageWitness i)

abbrev R3DerivationPorts {a : Analysis} (m : R3DerivationModel a) :=
  DerivationPorts m (fun i w => R3CriticalControl i w)

abbrev R3RegularDerivationPorts {a : Analysis} (m : R3DerivationModel a) :=
  RegularDerivationPorts m (fun i w => R3CriticalControl i w)

end Fefferman
