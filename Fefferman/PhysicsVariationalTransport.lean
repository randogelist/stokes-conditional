import Fefferman.MovingFrame

set_option autoImplicit false

namespace Fefferman

/- Representation-independent transport data.  This is the small algebraic
   core used by the physics examples below: states and dual states move
   contragrediently while their evaluation is invariant. -/
structure PhysicsTransport where
  Base : Type
  State : Type
  Dual : Type
  Value : Type
  transport : Base → Base → State → State
  dualTransport : Base → Base → Dual → Dual
  pairing : Dual → State → Value
  transportRefl : ∀ x q, transport x x q = q
  transportComp : ∀ x y z q,
    transport y z (transport x y q) = transport x z q
  dualTransportRefl : ∀ x b, dualTransport x x b = b
  dualTransportComp : ∀ x y z b,
    dualTransport y z (dualTransport x y b) = dualTransport x z b
  pairingInvariant : ∀ x y b q,
    pairing (dualTransport x y b) (transport x y q) = pairing b q

/- State-moving and dual/observable-moving descriptions evaluate to the same
   quantity. -/
theorem PHYSICS_STATE_OBSERVABLE_DUALITY (T : PhysicsTransport)
    (x y : T.Base) (b : T.Dual) (q : T.State) :
    T.pairing (T.dualTransport x y b) (T.transport x y q) = T.pairing b q :=
  T.pairingInvariant x y b q

/- The invariant pairing is conserved along every transport leg. -/
def PhysicsPairingConserved (T : PhysicsTransport) (x : T.Base)
    (b : T.Dual) (q : T.State) : Prop :=
  ∀ y, T.pairing (T.dualTransport x y b) (T.transport x y q) = T.pairing b q

theorem PHYSICS_TRANSPORT_CONSERVES_PAIRING (T : PhysicsTransport)
    (x : T.Base) (b : T.Dual) (q : T.State) :
    PhysicsPairingConserved T x b q := by
  intro y
  exact T.pairingInvariant x y b q

/- Generic first-variation package.  `residualFormula` is the integration-by-
   parts / first-variation identity, while `separates` is the abstract
   fundamental-lemma step. -/
structure PhysicsFirstVariation where
  Config : Type
  Variation : Type
  Residual : Type
  Scalar : Type
  zeroScalar : Scalar
  zeroResidual : Residual
  firstVariation : Config → Variation → Scalar
  residualPairing : Residual → Variation → Scalar
  residual : Config → Residual
  residualFormula : ∀ q η,
    firstVariation q η = residualPairing (residual q) η
  separates : ∀ r,
    (∀ η, residualPairing r η = zeroScalar) → r = zeroResidual

def PhysicsStationary (V : PhysicsFirstVariation) (q : V.Config) : Prop :=
  ∀ η, V.firstVariation q η = V.zeroScalar

def PhysicsEulerLagrange (V : PhysicsFirstVariation) (q : V.Config) : Prop :=
  V.residual q = V.zeroResidual

theorem PHYSICS_STATIONARITY_IMPLIES_EULER_LAGRANGE
    (V : PhysicsFirstVariation) (q : V.Config)
    (h : PhysicsStationary V q) : PhysicsEulerLagrange V q := by
  apply V.separates (V.residual q)
  intro η
  rw [← V.residualFormula q η]
  exact h η

/- Minimal Noether interface: an invariant infinitesimal action variation is
   identified with a charge rate.  Vanishing action variation therefore gives
   conservation of the corresponding charge. -/
structure PhysicsNoetherSystem where
  Config : Type
  Symmetry : Type
  Scalar : Type
  zero : Scalar
  actionVariation : Config → Symmetry → Scalar
  chargeRate : Config → Symmetry → Scalar
  noetherIdentity : ∀ q ξ, chargeRate q ξ = actionVariation q ξ

def PhysicsSymmetryAt (N : PhysicsNoetherSystem) (q : N.Config) : Prop :=
  ∀ ξ, N.actionVariation q ξ = N.zero

def PhysicsChargeConservedAt (N : PhysicsNoetherSystem) (q : N.Config) : Prop :=
  ∀ ξ, N.chargeRate q ξ = N.zero

theorem PHYSICS_NOETHER_CONSERVATION (N : PhysicsNoetherSystem)
    (q : N.Config) (h : PhysicsSymmetryAt N q) :
    PhysicsChargeConservedAt N q := by
  intro ξ
  rw [N.noetherIdentity q ξ]
  exact h ξ

end Fefferman
