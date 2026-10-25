import Fefferman.PhysicsVariationalTransport

set_option autoImplicit false

namespace Fefferman

/- Classical variational slice.  `dDt_dL_dV - dL_dQ` is represented using the
   ambient additive operations; no coordinate choice is built into the
   theorem. -/
structure ClassicalMechanicsSlice where
  Config : Type
  Variation : Type
  Scalar : Type
  zero : Scalar
  add : Scalar → Scalar → Scalar
  neg : Scalar → Scalar
  dDt_dL_dV : Config → Scalar
  dL_dQ : Config → Scalar
  firstVariation : Config → Variation → Scalar
  residualPairing : Scalar → Variation → Scalar
  variationFormula : ∀ q η,
    firstVariation q η =
      residualPairing (add (dDt_dL_dV q) (neg (dL_dQ q))) η
  fundamentalLemma : ∀ r,
    (∀ η, residualPairing r η = zero) → r = zero

def ClassicalEulerLagrangeResidual (C : ClassicalMechanicsSlice)
    (q : C.Config) : C.Scalar :=
  C.add (C.dDt_dL_dV q) (C.neg (C.dL_dQ q))

def ClassicalStationary (C : ClassicalMechanicsSlice) (q : C.Config) : Prop :=
  ∀ η, C.firstVariation q η = C.zero

def ClassicalEulerLagrange (C : ClassicalMechanicsSlice) (q : C.Config) : Prop :=
  ClassicalEulerLagrangeResidual C q = C.zero

def classicalFirstVariation (C : ClassicalMechanicsSlice) : PhysicsFirstVariation where
  Config := C.Config
  Variation := C.Variation
  Residual := C.Scalar
  Scalar := C.Scalar
  zeroScalar := C.zero
  zeroResidual := C.zero
  firstVariation := C.firstVariation
  residualPairing := C.residualPairing
  residual := ClassicalEulerLagrangeResidual C
  residualFormula := C.variationFormula
  separates := C.fundamentalLemma

theorem CLASSICAL_STATIONARITY_IMPLIES_EULER_LAGRANGE
    (C : ClassicalMechanicsSlice) (q : C.Config)
    (h : ClassicalStationary C q) : ClassicalEulerLagrange C q := by
  exact PHYSICS_STATIONARITY_IMPLIES_EULER_LAGRANGE
    (classicalFirstVariation C) q h

end Fefferman
