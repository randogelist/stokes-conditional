import Master_R3_details
import Fefferman.ReconstructedRoutes
import Fefferman.KernelCovariance

set_option autoImplicit false

namespace Fefferman

theorem R3_lower_payments_bounded {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .wholeSpace} (w : R3StorageWitness i) (c : w.Cut) (t : w.Time) :
    a.le (w.low c t) (a.mul w.lowCoefficient w.kineticMax) ∧
    a.le (w.heat c t) (a.mul w.heatCoefficient w.kineticMax) :=
  ⟨o.leTrans (w.lowPayment c t) (o.mulLeLeft w.lowCoefficientNonnegative (w.kineticBound c t)),
   o.leTrans (w.heatPayment c t) (o.mulLeLeft w.heatCoefficientNonnegative (w.kineticBound c t))⟩

theorem R3_storage_gives_crowd_bound {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .wholeSpace} (w : R3StorageWitness i) :
    ∀ c t, a.le (w.crowd c t) (R3StorageBudget o w) := by
  intro c t
  have hp := R3_lower_payments_bounded o w c t
  exact ledger_storage_bound o (w.storage c t) (w.initialStorage c) (w.crowd c t)
    (w.low c t) (w.high c t) (w.heat c t) w.storageMax
    (a.mul w.lowCoefficient w.kineticMax) w.highMax (a.mul w.heatCoefficient w.kineticMax) w.gamma
    (w.storageNonnegative c t) (w.initialStorageBound c) (w.exactStorage c t)
    hp.1 hp.2 (w.highAbsorption c t) w.strictRetention

theorem R3_crowd_gives_action_bound {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .wholeSpace} (w : R3StorageWitness i) :
    ∀ c t, a.le (w.action c t) (R3ActionBudget o w) :=
  w.occupationToAction (R3StorageBudget o w) (R3_storage_gives_crowd_bound o w)

theorem R3_action_gives_finite_critical_bounds {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .wholeSpace} (w : R3StorageWitness i) : ∀ c t,
    a.le (w.mass c t) (R3CriticalBudget o w) ∧
    a.le (w.dissipation c t) (o.divide (R3CriticalBudget o w) w.epsilon) := by
  intro c t
  exact ledger_forced_energy_bound o (w.mass c t) (w.dissipation c t) w.initialMass
    (w.action c t) (w.forceCost c t) (R3ActionBudget o w) w.forceMax w.epsilon
    w.positiveDissipation (w.massNonnegative c t) (w.dissipationNonnegative c t)
    (w.criticalBalance c t) (R3_crowd_gives_action_bound o w c t) (w.forcingBound c t)

theorem R3_full_critical_bounds {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .wholeSpace} (w : R3StorageWitness i) :
    (∀ t, a.le (w.fullMass t) (R3CriticalBudget o w)) ∧
    (∀ c t, a.le (w.dissipation c t) (o.divide (R3CriticalBudget o w) w.epsilon)) :=
  ⟨ledger_full_readout_bound w.mass w.fullMass (R3CriticalBudget o w) w.massReadout
      (fun c t => (R3_action_gives_finite_critical_bounds o w c t).1),
   fun c t => (R3_action_gives_finite_critical_bounds o w c t).2⟩

theorem R3_full_dissipation_bound {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .wholeSpace} (w : R3StorageWitness i)
    (fullDissipation : w.Time → a.Scalar)
    (readout : ∀ t, FullLedgerReadout a (fun c => w.dissipation c t) (fullDissipation t)) :
    ∀ t, a.le (fullDissipation t) (o.divide (R3CriticalBudget o w) w.epsilon) :=
  ledger_full_readout_bound w.dissipation fullDissipation
    (o.divide (R3CriticalBudget o w) w.epsilon) readout (R3_full_critical_bounds o w).2

theorem R3_derive_critical_control {a : Analysis} (o : LedgerArithmetic a)
    (i : ForcedInput a .wholeSpace) (w : R3StorageWitness i) : R3CriticalControl i w :=
  ⟨R3CriticalBudget o w, (R3_full_critical_bounds o w).1⟩

theorem R3_derive_regime_soundness {a : Analysis} (o : LedgerArithmetic a)
    (m : R3DerivationModel a) (p : R3DerivationPorts m) :
    ForceRegimeSoundness a .wholeSpace (derivationRegimes m) :=
  derivation_regime_soundness o m p (R3_derive_critical_control o)

theorem R3_derive_A {a : Analysis} (o : LedgerArithmetic a)
    (m : R3DerivationModel a) (p : R3RegularDerivationPorts m) : A a :=
  derivation_unforced m p (R3_derive_critical_control o)

theorem R3_derive_master_core {a : Analysis} (o : LedgerArithmetic a)
    (m : R3DerivationModel a) (p : R3DerivationPorts m) :
    DomainMasterCore a .wholeSpace (derivationRegimes m) :=
  derivation_master_core o m p (R3_derive_critical_control o)

theorem R3_derive_master {a : Analysis} (o : LedgerArithmetic a)
    (m : R3DerivationModel a) (p : R3DerivationPorts m)
    (nonempty : ∀ ν, ∃ f, (derivationRegimes m).breakdown ν f) :
    DomainMaster a .wholeSpace (derivationRegimes m) :=
  derivation_master o m p (R3_derive_critical_control o) nonempty

end Fefferman
