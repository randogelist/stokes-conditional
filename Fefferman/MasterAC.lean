import Master_R3_derivation

set_option autoImplicit false

namespace Fefferman

/- One internal R3 breakdown object.  It deliberately carries no Fefferman
   admissibility proof and no no-global-solution conclusion.  Identification
   of this particular object with the physical Fefferman class is performed
   only by `MasterACProjection`. -/
structure MasterACBreakdownWitness {a : Analysis}
    (m : R3DerivationModel a) (ν : PositiveViscosity a) where
  initial : Initial a
  force : Force a
  criterion : m.breakdownCriterion ν initial force

/- Internal R3 A/C master object.

   It contains neither `A a` nor `C a`, does not mention `hasGlobalSolution`,
   and does not assert that every internal force is a Fefferman force.

   A-side: zero force satisfies the internal regular criterion.
   C-side: every viscosity has an internal breakdown object. -/
structure MasterAC {a : Analysis} (m : R3DerivationModel a) : Prop where
  zeroRegular : ∀ ν, m.regularCriterion ν (zeroForce a)
  breakdown : ∀ ν, Nonempty (MasterACBreakdownWitness m ν)

/- Thin physical projection layer.

   Only the zero force used by A and the actual witness family used by C need
   to be identified with the Fefferman admissible class.  No surjectivity onto
   all Fefferman forces is required.  The realization fields bind the internal
   objects to the same physical ForcedInput before the existing critical and
   obstruction exits are applied. -/
structure MasterACProjection {a : Analysis} (m : R3DerivationModel a) : Prop where
  zeroAdmissible : admissibleForce a .wholeSpace (zeroForce a)
  breakdownInitialAdmissible : ∀ ν (w : MasterACBreakdownWitness m ν),
    admissibleInitial a .wholeSpace w.initial
  breakdownForceAdmissible : ∀ ν (w : MasterACBreakdownWitness m ν),
    admissibleForce a .wholeSpace w.force
  realizeRegular : ∀ (i : ForcedInput a .wholeSpace),
    m.regularCriterion i.viscosity i.force →
      ∃ w : R3StorageWitness i, m.regularRepresents i w
  regularExit : ∀ i (w : R3StorageWitness i),
    m.regularRepresents i w → R3CriticalControl i w →
      hasGlobalSolution a .wholeSpace i.viscosity i.initial i.force
  realizeObstruction : ∀ (i : ForcedInput a .wholeSpace),
    m.breakdownCriterion i.viscosity i.initial i.force →
      ∃ w : NetWorkWitness i, m.obstructionRepresents i w
  globalBoundsObstruction : ∀ i (w : NetWorkWitness i),
    m.obstructionRepresents i w →
      ∀ s, globalSolution a .wholeSpace i.viscosity i.initial i.force s →
        ledgerBounded a w.mass

/- Existing R3 derivation ports provide the same-object realization and exit
   pieces.  Only the two witness-identification maps remain explicit. -/
def masterACProjectionOfDerivationPorts {a : Analysis} {m : R3DerivationModel a}
    (p : R3DerivationPorts m)
    (initialId : ∀ ν (w : MasterACBreakdownWitness m ν),
      admissibleInitial a .wholeSpace w.initial)
    (forceId : ∀ ν (w : MasterACBreakdownWitness m ν),
      admissibleForce a .wholeSpace w.force) : MasterACProjection m where
  zeroAdmissible := p.regular.zeroAdmissible
  breakdownInitialAdmissible := initialId
  breakdownForceAdmissible := forceId
  realizeRegular := p.regular.realizeRegular
  regularExit := p.regular.regularExit
  realizeObstruction := p.obstruction.realizeObstruction
  globalBoundsObstruction := p.obstruction.globalBoundsObstruction

/- An internal MasterAC proof plus physical projection reconstructs the regular
   and obstruction ports.  Zero-force regularity comes from MasterAC itself,
   not from an official A statement. -/
def masterACDerivationPorts {a : Analysis} {m : R3DerivationModel a}
    (h : MasterAC m) (p : MasterACProjection m) : R3DerivationPorts m where
  regular :=
    { zeroAdmissible := p.zeroAdmissible
      zeroRegular := h.zeroRegular
      realizeRegular := p.realizeRegular
      regularExit := p.regularExit }
  obstruction :=
    { realizeObstruction := p.realizeObstruction
      globalBoundsObstruction := p.globalBoundsObstruction }

/- After projection of just the actual C witness family, the internal
   breakdown objects become the previous certified breakdown regimes. -/
theorem masterAC_breakdown_regime_nonempty {a : Analysis} {m : R3DerivationModel a}
    (h : MasterAC m) (p : MasterACProjection m) :
    ∀ ν, ∃ f, (derivationRegimes m).breakdown ν f := by
  intro ν
  rcases h.breakdown ν with ⟨w⟩
  refine ⟨w.force, ?_⟩
  change admissibleForce a .wholeSpace w.force ∧
    ∃ u₀, admissibleInitial a .wholeSpace u₀ ∧
      m.breakdownCriterion ν u₀ w.force
  exact ⟨p.breakdownForceAdmissible ν w, w.initial,
    p.breakdownInitialAdmissible ν w, w.criterion⟩

/- Compatibility constructor from the previous internal regime interface.
   This extracts only the internal criterion witness; admissibility is not
   stored in MasterAC. -/
theorem masterAC_of_derivationPorts_and_regime_nonempty {a : Analysis}
    {m : R3DerivationModel a} (p : R3DerivationPorts m)
    (nonempty : ∀ ν, ∃ f, (derivationRegimes m).breakdown ν f) : MasterAC m := by
  constructor
  · exact p.regular.zeroRegular
  · intro ν
    rcases nonempty ν with ⟨f, hf⟩
    change admissibleForce a .wholeSpace f ∧
      ∃ u₀, admissibleInitial a .wholeSpace u₀ ∧
        m.breakdownCriterion ν u₀ f at hf
    rcases hf with ⟨_, u₀, _, hc⟩
    exact ⟨{
      initial := u₀
      force := f
      criterion := hc
    }⟩

/- A is a thin projection theorem from the internal zero-force branch. -/
theorem MasterAC_implies_A {a : Analysis} (o : LedgerArithmetic a)
    (m : R3DerivationModel a) (h : MasterAC m) (p : MasterACProjection m) : A a := by
  let ports : R3DerivationPorts m := masterACDerivationPorts h p
  exact R3_derive_A o m ports.regular

/- C is a thin projection theorem from the internal physical breakdown family.
   No no-global-solution statement is stored in MasterAC: it is derived through
   the net-work obstruction after the witness is identified as physical. -/
theorem MasterAC_implies_C {a : Analysis} (o : LedgerArithmetic a)
    (m : R3DerivationModel a) (h : MasterAC m) (p : MasterACProjection m) : C a := by
  let ports : R3DerivationPorts m := masterACDerivationPorts h p
  have hm : DomainMaster a .wholeSpace (derivationRegimes m) :=
    R3_derive_master o m ports (masterAC_breakdown_regime_nonempty h p)
  intro ν
  exact master_breakdownAt hm ν

/- Final boundary theorem.  Official Fefferman A/C appear only here. -/
theorem MASTER_AC_IMPLIES_FEFFERMAN_A_AND_C {a : Analysis} (o : LedgerArithmetic a)
    (m : R3DerivationModel a) (h : MasterAC m) (p : MasterACProjection m) :
    A a ∧ C a :=
  ⟨MasterAC_implies_A o m h p, MasterAC_implies_C o m h p⟩

end Fefferman
