import Fefferman.PhysicsClassical

set_option autoImplicit false

namespace Fefferman

/- GP differential realization: ordinary differentiation is represented as a
   signed shift on the coherent ladder. -/
structure GPDerivativeSlice where
  State : Type
  ordinaryDerivative : State → State
  gpShift : State → State
  neg : State → State
  derivativeShift : ∀ q, ordinaryDerivative q = neg (gpShift q)

theorem GP_DERIVATIVE_IS_SHIFT (G : GPDerivativeSlice) (q : G.State) :
    G.ordinaryDerivative q = G.neg (G.gpShift q) :=
  G.derivativeShift q

/- Operator-level quantum realization.  The GP product-rule relation
   X L = L X + I and P = i*hbar L imply the canonical translation relation
   X P = P X + i*hbar I. -/
structure QuantumShiftAlgebra where
  Operator : Type
  compose : Operator → Operator → Operator
  add : Operator → Operator → Operator
  identity : Operator
  X : Operator
  L : Operator
  P : Operator
  ihbarI : Operator
  scaleIhbar : Operator → Operator
  momentum : P = scaleIhbar L
  xScale : ∀ A, compose X (scaleIhbar A) = scaleIhbar (compose X A)
  scaleX : ∀ A, compose (scaleIhbar A) X = scaleIhbar (compose A X)
  scaleAdd : ∀ A B, scaleIhbar (add A B) = add (scaleIhbar A) (scaleIhbar B)
  scaleIdentity : scaleIhbar identity = ihbarI
  gpPositionShift : compose X L = add (compose L X) identity

theorem QUANTUM_CCR_FROM_GP_SHIFT (Q : QuantumShiftAlgebra) :
    Q.compose Q.X Q.P = Q.add (Q.compose Q.P Q.X) Q.ihbarI := by
  rw [Q.momentum]
  rw [Q.xScale Q.L]
  rw [Q.gpPositionShift]
  rw [Q.scaleAdd (Q.compose Q.L Q.X) Q.identity]
  rw [Q.scaleX Q.L, Q.scaleIdentity]

/- The Schrödinger/state-moving and Heisenberg/dual-moving values are exactly
   the same invariant pairing furnished by the transport object. -/
theorem QUANTUM_SCHRODINGER_HEISENBERG_DUALITY
    (T : PhysicsTransport) (x y : T.Base) (observable : T.Dual)
    (state : T.State) :
    T.pairing (T.dualTransport x y observable) (T.transport x y state) =
      T.pairing observable state :=
  PHYSICS_STATE_OBSERVABLE_DUALITY T x y observable state

end Fefferman
