import Fefferman.MasterCore
import Fefferman.ScalarLedger

set_option autoImplicit false

namespace Fefferman

structure ForcedInput (a : Analysis) (d : Domain) where
  viscosity : PositiveViscosity a
  initial : Initial a
  force : Force a
  initialAdmissible : admissibleInitial a d initial
  forceAdmissible : admissibleForce a d force

/- A scalar obstruction witness. Its binding to the specified physical input,
   and the necessary bound for every global solution, are separate below. -/
structure NetWorkWitness {a : Analysis} {d : Domain} (i : ForcedInput a d) where
  Time : Type
  initialMass : a.Scalar
  mass : Time → a.Scalar
  work : Time → a.Scalar
  massNonnegative : ∀ t, a.le a.zero (mass t)
  exactBalance : ∀ t, mass t = a.add initialMass (work t)
  workUnbounded : ∀ bound, ∃ t, ¬ a.le (work t) bound

structure DerivationModel (a : Analysis) (d : Domain)
    (Witness : ForcedInput a d → Type 1) where
  regularCriterion : PositiveViscosity a → Force a → Prop
  breakdownCriterion : PositiveViscosity a → Initial a → Force a → Prop
  regularRepresents : (i : ForcedInput a d) → Witness i → Prop
  obstructionRepresents : (i : ForcedInput a d) → NetWorkWitness i → Prop

def derivationRegimes {a : Analysis} {d : Domain}
    {Witness : ForcedInput a d → Type 1} (m : DerivationModel a d Witness) :
    ForceRegimes a d where
  regular := fun ν f => admissibleForce a d f ∧ m.regularCriterion ν f
  breakdown := fun ν f => admissibleForce a d f ∧
    ∃ u₀, admissibleInitial a d u₀ ∧ m.breakdownCriterion ν u₀ f

/- These are the remaining analytic obligations, not supplied theorems.
   No field is named or defined as a proof of the full master statement. -/
structure RegularDerivationPorts {a : Analysis} {d : Domain}
    {Witness : ForcedInput a d → Type 1} (m : DerivationModel a d Witness)
    (Control : (i : ForcedInput a d) → Witness i → Prop) : Prop where
  zeroAdmissible : admissibleForce a d (zeroForce a)
  zeroRegular : ∀ ν, m.regularCriterion ν (zeroForce a)
  realizeRegular : ∀ (i : ForcedInput a d), m.regularCriterion i.viscosity i.force →
    ∃ w : Witness i, m.regularRepresents i w
  regularExit : ∀ i (w : Witness i), m.regularRepresents i w → Control i w →
    hasGlobalSolution a d i.viscosity i.initial i.force

structure ObstructionDerivationPorts {a : Analysis} {d : Domain}
    {Witness : ForcedInput a d → Type 1} (m : DerivationModel a d Witness) : Prop where
  realizeObstruction : ∀ (i : ForcedInput a d), m.breakdownCriterion i.viscosity i.initial i.force →
    ∃ w : NetWorkWitness i, m.obstructionRepresents i w
  globalBoundsObstruction : ∀ i (w : NetWorkWitness i), m.obstructionRepresents i w →
    ∀ s, globalSolution a d i.viscosity i.initial i.force s → ledgerBounded a w.mass

structure DerivationPorts {a : Analysis} {d : Domain}
    {Witness : ForcedInput a d → Type 1} (m : DerivationModel a d Witness)
    (Control : (i : ForcedInput a d) → Witness i → Prop) : Prop where
  regular : RegularDerivationPorts m Control
  obstruction : ObstructionDerivationPorts m

theorem derivation_regular_soundness {a : Analysis} {d : Domain}
    {Witness : ForcedInput a d → Type 1} (m : DerivationModel a d Witness)
    {Control : (i : ForcedInput a d) → Witness i → Prop}
    (p : RegularDerivationPorts m Control) (deriveControl : ∀ i w, Control i w) :
    ∀ ν f, (derivationRegimes m).regular ν f → regularForceAt a d ν f := by
  intro ν f hf
  refine ⟨hf.1, ?_⟩
  intro u₀ hu₀
  let i : ForcedInput a d := ⟨ν, u₀, f, hu₀, hf.1⟩
  cases p.realizeRegular i hf.2 with
  | intro w hw => exact p.regularExit i w hw (deriveControl i w)

theorem derivation_unforced {a : Analysis} {d : Domain}
    {Witness : ForcedInput a d → Type 1} (m : DerivationModel a d Witness)
    {Control : (i : ForcedInput a d) → Witness i → Prop}
    (p : RegularDerivationPorts m Control) (deriveControl : ∀ i w, Control i w) :
    ∀ ν, unforcedGlobalAt a d ν :=
  fun ν => (derivation_regular_soundness m p deriveControl ν (zeroForce a)
    ⟨p.zeroAdmissible, p.zeroRegular ν⟩).2

theorem derivation_obstruction_no_global {a : Analysis} {d : Domain}
    (o : LedgerArithmetic a) {Witness : ForcedInput a d → Type 1}
    {m : DerivationModel a d Witness}
    (p : ObstructionDerivationPorts m) (i : ForcedInput a d)
    (w : NetWorkWitness i) (hw : m.obstructionRepresents i w) :
    ¬ hasGlobalSolution a d i.viscosity i.initial i.force := by
  intro h
  cases h with
  | intro s hs =>
    exact ledger_net_work_excludes_mass_bound o w.initialMass w.mass w.work
      w.exactBalance w.workUnbounded (p.globalBoundsObstruction i w hw s hs)

theorem derivation_regime_soundness {a : Analysis} {d : Domain}
    (o : LedgerArithmetic a) {Witness : ForcedInput a d → Type 1}
    (m : DerivationModel a d Witness) {Control : (i : ForcedInput a d) → Witness i → Prop}
    (p : DerivationPorts m Control) (deriveControl : ∀ i w, Control i w) :
    ForceRegimeSoundness a d (derivationRegimes m) := by
  constructor
  · exact derivation_regular_soundness m p.regular deriveControl
  · intro ν f hf
    refine ⟨hf.1, ?_⟩
    cases hf.2 with
    | intro u₀ hu₀ =>
      refine ⟨u₀, hu₀.1, ?_⟩
      let i : ForcedInput a d := ⟨ν, u₀, f, hu₀.1, hf.1⟩
      cases p.obstruction.realizeObstruction i hu₀.2 with
      | intro w hw => exact derivation_obstruction_no_global o p.obstruction i w hw

theorem derivation_master_core {a : Analysis} {d : Domain}
    (o : LedgerArithmetic a) {Witness : ForcedInput a d → Type 1}
    (m : DerivationModel a d Witness) {Control : (i : ForcedInput a d) → Witness i → Prop}
    (p : DerivationPorts m Control) (deriveControl : ∀ i w, Control i w) :
    DomainMasterCore a d (derivationRegimes m) :=
  ⟨derivation_regime_soundness o m p deriveControl,
   fun ν => ⟨p.regular.zeroAdmissible, p.regular.zeroRegular ν⟩⟩

theorem derivation_master {a : Analysis} {d : Domain}
    (o : LedgerArithmetic a) {Witness : ForcedInput a d → Type 1}
    (m : DerivationModel a d Witness) {Control : (i : ForcedInput a d) → Witness i → Prop}
    (p : DerivationPorts m Control) (deriveControl : ∀ i w, Control i w)
    (nonempty : ∀ ν, ∃ f, (derivationRegimes m).breakdown ν f) :
    DomainMaster a d (derivationRegimes m) :=
  ⟨derivation_master_core o m p deriveControl, nonempty⟩

end Fefferman
