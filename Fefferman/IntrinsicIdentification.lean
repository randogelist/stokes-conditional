import Master_r3

set_option autoImplicit false

namespace Fefferman

/- Identification layer for the R3 forced route.

   Intended concrete realization of `intrinsic`:
     bounded accumulated ||A^(-1/4) P f||_2^2,
   equivalently in the standard R3 Stokes realization,
     f in L^2_t H^(-1/2)_sigma.

   The later forced-GP sources supply the Stokes-duality / absorption /
   critical-ledger route.  This module deliberately separates the elementary
   Fefferman-force embedding from the genuinely hard global PDE closure. -/
structure R3FeffermanIntrinsicIdentification (a : Analysis) where
  intrinsic : Force a → Prop
  admissible_to_intrinsic :
    ∀ f, admissibleForce a .wholeSpace f → intrinsic f
  zero_admissible : admissibleForce a .wholeSpace (zeroForce a)

/- This is the remaining global PDE theorem after the force identification:
   every Fefferman-admissible force lying in the intrinsic class has a
   qualifying global Fefferman solution for every admissible datum. -/
structure R3IntrinsicGlobalClosure (a : Analysis)
    (intrinsic : Force a → Prop) : Prop where
  solve :
    ∀ (ν : PositiveViscosity a) (u₀ : Initial a),
      admissibleInitial a .wholeSpace u₀ →
      ∀ f : Force a,
        admissibleForce a .wholeSpace f →
        intrinsic f →
        hasGlobalSolution a .wholeSpace ν u₀ f

theorem R3_intrinsic_closure_regularForceAt {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic)
    (ν : PositiveViscosity a) (f : Force a)
    (hf : admissibleForce a .wholeSpace f) :
    regularForceAt a .wholeSpace ν f := by
  constructor
  · exact hf
  · intro u₀ hu₀
    exact close.solve ν u₀ hu₀ f hf (id.admissible_to_intrinsic f hf)

theorem R3_intrinsic_closure_forcedGlobalAt {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic)
    (ν : PositiveViscosity a) :
    forcedGlobalAt a .wholeSpace ν := by
  intro u₀ hu₀ f hf
  exact close.solve ν u₀ hu₀ f hf (id.admissible_to_intrinsic f hf)

theorem R3_intrinsic_closure_unforcedGlobalAt {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic)
    (ν : PositiveViscosity a) :
    unforcedGlobalAt a .wholeSpace ν := by
  intro u₀ hu₀
  exact close.solve ν u₀ hu₀ (zeroForce a) id.zero_admissible
    (id.admissible_to_intrinsic (zeroForce a) id.zero_admissible)

theorem R3_intrinsic_closure_implies_A {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic) : A a := by
  intro ν
  exact R3_intrinsic_closure_unforcedGlobalAt id close ν

theorem R3_intrinsic_closure_excludes_breakdownAt {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic)
    (ν : PositiveViscosity a) :
    ¬ breakdownAt a .wholeSpace ν := by
  intro hbreak
  rcases (breakdownAt_iff_exists_breakdownForce a .wholeSpace ν).mp hbreak with
    ⟨f, hfbreak⟩
  exact
    (regularForceAt_excludes_breakdownForceAt
      (R3_intrinsic_closure_regularForceAt id close ν f hfbreak.1)) hfbreak

theorem R3_intrinsic_closure_excludes_C_at {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic)
    (ν : PositiveViscosity a) :
    ¬ statementAt a ν .C := by
  exact R3_intrinsic_closure_excludes_breakdownAt id close ν

/- To refute the universally quantified Fefferman C statement abstractly one
   needs one positive viscosity inhabitant.  The real-number realization has
   such inhabitants (for example nu = 1), but the core Analysis signature does
   not build one. -/
theorem R3_intrinsic_closure_excludes_C {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic)
    (ν₀ : PositiveViscosity a) : ¬ C a := by
  intro hC
  exact (R3_intrinsic_closure_excludes_breakdownAt id close ν₀) (hC ν₀)

/- The same result can be routed through the existing v0.7.7 master-core
   theorem.  The regular certificate is simply "Fefferman-admissible and
   intrinsic"; the breakdown certificate is empty.  Its soundness is exactly
   the hard intrinsic global-closure theorem. -/
def R3IntrinsicForceRegimes {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a) : ForceRegimes a .wholeSpace :=
  { regular := fun _ f => admissibleForce a .wholeSpace f ∧ id.intrinsic f
    breakdown := fun _ _ => False }

theorem R3_intrinsic_regime_soundness {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic) :
    ForceRegimeSoundness a .wholeSpace (R3IntrinsicForceRegimes id) := by
  constructor
  · intro ν f hreg
    change admissibleForce a .wholeSpace f ∧ id.intrinsic f at hreg
    constructor
    · exact hreg.1
    · intro u₀ hu₀
      exact close.solve ν u₀ hu₀ f hreg.1 hreg.2
  · intro ν f hbreak
    change False at hbreak
    exact False.elim hbreak

theorem R3_intrinsic_masterCore {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic) :
    DomainMasterCore a .wholeSpace (R3IntrinsicForceRegimes id) := by
  constructor
  · exact R3_intrinsic_regime_soundness id close
  · intro ν
    change admissibleForce a .wholeSpace (zeroForce a) ∧ id.intrinsic (zeroForce a)
    exact ⟨id.zero_admissible,
      id.admissible_to_intrinsic (zeroForce a) id.zero_admissible⟩

theorem R3_intrinsic_regular_cover {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (ν : PositiveViscosity a) :
    ∀ f, admissibleForce a .wholeSpace f →
      (R3IntrinsicForceRegimes id).regular ν f := by
  intro f hf
  change admissibleForce a .wholeSpace f ∧ id.intrinsic f
  exact ⟨hf, id.admissible_to_intrinsic f hf⟩

theorem R3_intrinsic_masterCore_identifies_A_and_excludes_C_at {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic)
    (ν : PositiveViscosity a) :
    statementAt a ν .A ∧ ¬ statementAt a ν .C :=
  R3_masterCore_and_embedding_excludes_C_at
    (R3_intrinsic_masterCore id close) ν (R3_intrinsic_regular_cover id ν)

theorem R3_intrinsic_closure_identifies_Fefferman_R3_side {a : Analysis}
    (id : R3FeffermanIntrinsicIdentification a)
    (close : R3IntrinsicGlobalClosure a id.intrinsic)
    (ν₀ : PositiveViscosity a) : A a ∧ ¬ C a :=
  ⟨R3_intrinsic_closure_implies_A id close,
    R3_intrinsic_closure_excludes_C id close ν₀⟩

end Fefferman
