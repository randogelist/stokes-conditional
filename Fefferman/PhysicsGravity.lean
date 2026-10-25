import Fefferman.PhysicsQuantum

set_option autoImplicit false

namespace Fefferman

/- Algebraic Cartan curvature split.  Think F = R + E with E representing the
   tetrad-square / cosmological part.  The theorem below is only the exact
   distributive expansion; it does not assume gravitational field equations. -/
structure CartanActionAlgebra where
  Term : Type
  add : Term → Term → Term
  mul : Term → Term → Term
  R : Term
  E : Term
  F : Term
  curvatureSplit : F = add R E
  mulAdd : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  addMul : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)

def CartanFullAction (C : CartanActionAlgebra) : C.Term := C.mul C.F C.F

def CartanTopologicalTerm (C : CartanActionAlgebra) : C.Term := C.mul C.R C.R

def CartanEinsteinCrossLeft (C : CartanActionAlgebra) : C.Term := C.mul C.E C.R

def CartanEinsteinCrossRight (C : CartanActionAlgebra) : C.Term := C.mul C.R C.E

def CartanCosmologicalTerm (C : CartanActionAlgebra) : C.Term := C.mul C.E C.E

theorem GR_CARTAN_CURVATURE_ACTION_EXPANSION (C : CartanActionAlgebra) :
    CartanFullAction C =
      C.add
        (C.add (CartanTopologicalTerm C) (CartanEinsteinCrossLeft C))
        (C.add (CartanEinsteinCrossRight C) (CartanCosmologicalTerm C)) := by
  unfold CartanFullAction CartanTopologicalTerm CartanEinsteinCrossLeft
    CartanEinsteinCrossRight CartanCosmologicalTerm
  calc
    C.mul C.F C.F = C.mul (C.add C.R C.E) (C.add C.R C.E) :=
      congrArg (fun z => C.mul z z) C.curvatureSplit
    _ = C.add (C.mul (C.add C.R C.E) C.R)
        (C.mul (C.add C.R C.E) C.E) := C.mulAdd (C.add C.R C.E) C.R C.E
    _ = C.add
        (C.add (C.mul C.R C.R) (C.mul C.E C.R))
        (C.add (C.mul C.R C.E) (C.mul C.E C.E)) := by
      rw [C.addMul C.R C.E C.R, C.addMul C.R C.E C.E]

/- Kinematical Cartan reconstruction: a connection is split into a Lorentz
   connection and tetrad, and the metric is reconstructed from the tetrad. -/
structure CartanGravityReconstruction where
  Connection : Type
  LorentzConnection : Type
  Tetrad : Type
  Metric : Type
  split : Connection → LorentzConnection × Tetrad
  metricFromTetrad : Tetrad → Metric

def CartanReconstructedMetric (G : CartanGravityReconstruction)
    (A : G.Connection) : G.Metric :=
  G.metricFromTetrad (G.split A).2

theorem GR_CONNECTION_RECONSTRUCTS_TETRAD_AND_METRIC
    (G : CartanGravityReconstruction) (A : G.Connection) :
    ∃ ω e, G.split A = (ω, e) ∧
      CartanReconstructedMetric G A = G.metricFromTetrad e := by
  cases h : G.split A with
  | mk ω e =>
      refine ⟨ω, e, ?_, ?_⟩
      · rfl
      · simp [CartanReconstructedMetric, h]

/- The final stationary-action to Einstein-equation implication is kept as an
   explicit realization port.  This prevents the algebraic Cartan expansion
   above from being misreported as a completed differential-geometric proof. -/
structure GravityVariationalPort (G : CartanGravityReconstruction) where
  Stationary : G.Connection → Prop
  Einstein : G.Metric → Prop
  stationaryToEinstein : ∀ A,
    Stationary A → Einstein (CartanReconstructedMetric G A)

theorem GR_STATIONARY_ACTION_TO_EINSTEIN
    (G : CartanGravityReconstruction) (P : GravityVariationalPort G)
    (A : G.Connection) (h : P.Stationary A) :
    P.Einstein (CartanReconstructedMetric G A) :=
  P.stationaryToEinstein A h

end Fefferman
