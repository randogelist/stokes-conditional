import Fefferman.SourceGeometry

set_option autoImplicit false

namespace Fefferman

universe u v w

/- Binary congruence from equality elimination, available with Init alone. -/
theorem source_congr_arg_two {X : Sort u} {Y : Sort v} {Z : Sort w}
    (f : X → Y → Z) {x x' : X} {y y' : Y}
    (hx : x = x') (hy : y = y') : f x y = f x' y' := by
  cases hx
  cases hy
  rfl

/- Ordinary bilinearity of vector subtraction. No projection, minimization,
   rank, or PDE estimate is a field of this structure. -/
structure SourceDifference {a : Analysis} (P : SourcePairing a) where
  sub : P.Carrier → P.Carrier → P.Carrier
  pairSubLeft : ∀ x y z, P.pair (sub x y) z =
    a.add (P.pair x z) (a.neg (P.pair y z))
  pairSubRight : ∀ x y z, P.pair x (sub y z) =
    a.add (P.pair x y) (a.neg (P.pair x z))

/- These are the source coefficient/remove/alpha/beta/residual definitions.
   Division is total, so zero and dependent directions are not excluded. -/
def GramCoefficient {a : Analysis} (o : LedgerArithmetic a) (P : SourcePairing a)
    (v x : P.Carrier) : a.Scalar := o.divide (P.pair x v) (P.pair v v)

def GramRemove {a : Analysis} (o : LedgerArithmetic a) {P : SourcePairing a}
    (D : SourceDifference P) (v x : P.Carrier) : P.Carrier :=
  D.sub x (P.scale (GramCoefficient o P v x) v)

def GramBeta {a : Analysis} (o : LedgerArithmetic a) {P : SourcePairing a}
    (D : SourceDifference P) (f n0 n1 : P.Carrier) : a.Scalar :=
  GramCoefficient o P (GramRemove o D n0 n1) (GramRemove o D n0 f)

def GramAlpha {a : Analysis} (o : LedgerArithmetic a) {P : SourcePairing a}
    (D : SourceDifference P) (f n0 n1 : P.Carrier) : a.Scalar :=
  a.add (GramCoefficient o P n0 f)
    (a.neg (a.mul (GramBeta o D f n0 n1) (GramCoefficient o P n0 n1)))

def GramResidual {a : Analysis} {P : SourcePairing a} (D : SourceDifference P)
    (f n0 n1 : P.Carrier) (c0 c1 : a.Scalar) : P.Carrier :=
  D.sub (D.sub f (P.scale c0 n0)) (P.scale c1 n1)

def GramReduced {a : Analysis} (o : LedgerArithmetic a) {P : SourcePairing a}
    (D : SourceDifference P) (f n0 n1 : P.Carrier) : P.Carrier :=
  GramResidual D f n0 n1 (GramAlpha o D f n0 n1) (GramBeta o D f n0 n1)

def GramCapacity {a : Analysis} (o : LedgerArithmetic a) {P : SourcePairing a}
    (D : SourceDifference P) (f n0 n1 : P.Carrier) : a.Scalar :=
  P.pair (GramReduced o D f n0 n1) (GramReduced o D f n0 n1)

def GramNormalEquations {a : Analysis} (P : SourcePairing a)
    (f n0 n1 : P.Carrier) (c0 c1 : a.Scalar) : Prop :=
  P.pair f n0 = a.add (a.mul c0 (P.pair n0 n0)) (a.mul c1 (P.pair n1 n0)) ∧
  P.pair f n1 = a.add (a.mul c0 (P.pair n0 n1)) (a.mul c1 (P.pair n1 n1))

theorem GramRemove_pair_left {a : Analysis} (o : LedgerArithmetic a)
    {P : SourcePairing a} (D : SourceDifference P) (v x y : P.Carrier) :
    P.pair (GramRemove o D v x) y =
      a.add (P.pair x y) (a.neg (a.mul (GramCoefficient o P v x) (P.pair v y))) := by
  simp only [GramRemove, D.pairSubLeft, P.scaleLeft]

theorem GramRemove_pair_right {a : Analysis} (o : LedgerArithmetic a)
    {P : SourcePairing a} (D : SourceDifference P) (x v y : P.Carrier) :
    P.pair x (GramRemove o D v y) =
      a.add (P.pair x y) (a.neg (a.mul (GramCoefficient o P v y) (P.pair x v))) := by
  simp only [GramRemove, D.pairSubRight, P.scaleRight]

theorem GramResidual_pair_left {a : Analysis} {P : SourcePairing a}
    (D : SourceDifference P) (f n0 n1 y : P.Carrier) (c0 c1 : a.Scalar) :
    P.pair (GramResidual D f n0 n1 c0 c1) y =
      a.add (a.add (P.pair f y) (a.neg (a.mul c0 (P.pair n0 y))))
        (a.neg (a.mul c1 (P.pair n1 y))) := by
  simp only [GramResidual, D.pairSubLeft, P.scaleLeft]

theorem GramResidual_pair_right {a : Analysis} {P : SourcePairing a}
    (D : SourceDifference P) (x f n0 n1 : P.Carrier) (c0 c1 : a.Scalar) :
    P.pair x (GramResidual D f n0 n1 c0 c1) =
      a.add (a.add (P.pair x f) (a.neg (a.mul c0 (P.pair x n0))))
        (a.neg (a.mul c1 (P.pair x n1))) := by
  simp only [GramResidual, D.pairSubRight, P.scaleRight]

theorem GramCoefficient_transport {a : Analysis} (o : LedgerArithmetic a)
    {P Q : SourcePairing a} {T : P.Carrier → Q.Carrier}
    (h : SourceIsometry P Q T) (v x : P.Carrier) :
    GramCoefficient o Q (T v) (T x) = GramCoefficient o P v x :=
  source_congr_arg_two o.divide (h x v) (h v v)

theorem GramRemove_pair_transport {a : Analysis} (o : LedgerArithmetic a)
    {P Q : SourcePairing a} (DP : SourceDifference P) (DQ : SourceDifference Q)
    {T : P.Carrier → Q.Carrier} (h : SourceIsometry P Q T)
    (v x w y : P.Carrier) :
    Q.pair (GramRemove o DQ (T v) (T x)) (GramRemove o DQ (T w) (T y)) =
      P.pair (GramRemove o DP v x) (GramRemove o DP w y) := by
  have he : ∀ x y, Q.pair (T x) (T y) = P.pair x y := h
  simp only [GramRemove, GramCoefficient, DQ.pairSubLeft, DQ.pairSubRight,
    Q.scaleLeft, Q.scaleRight, DP.pairSubLeft, DP.pairSubRight,
    P.scaleLeft, P.scaleRight, he]

theorem GramBeta_transport {a : Analysis} (o : LedgerArithmetic a)
    {P Q : SourcePairing a} (DP : SourceDifference P) (DQ : SourceDifference Q)
    {T : P.Carrier → Q.Carrier} (h : SourceIsometry P Q T)
    (f n0 n1 : P.Carrier) :
    GramBeta o DQ (T f) (T n0) (T n1) = GramBeta o DP f n0 n1 :=
  source_congr_arg_two o.divide (GramRemove_pair_transport o DP DQ h n0 f n0 n1)
    (GramRemove_pair_transport o DP DQ h n0 n1 n0 n1)

theorem GramAlpha_transport {a : Analysis} (o : LedgerArithmetic a)
    {P Q : SourcePairing a} (DP : SourceDifference P) (DQ : SourceDifference Q)
    {T : P.Carrier → Q.Carrier} (h : SourceIsometry P Q T)
    (f n0 n1 : P.Carrier) :
    GramAlpha o DQ (T f) (T n0) (T n1) = GramAlpha o DP f n0 n1 :=
  source_congr_arg_two a.add (GramCoefficient_transport o h n0 f)
    (congrArg a.neg (source_congr_arg_two a.mul (GramBeta_transport o DP DQ h f n0 n1)
      (GramCoefficient_transport o h n0 n1)))

theorem GramResidual_pair_transport {a : Analysis}
    {P Q : SourcePairing a} (DP : SourceDifference P) (DQ : SourceDifference Q)
    {T : P.Carrier → Q.Carrier} (h : SourceIsometry P Q T)
    (f n0 n1 g m0 m1 : P.Carrier) (c0 c1 d0 d1 : a.Scalar) :
    Q.pair (GramResidual DQ (T f) (T n0) (T n1) c0 c1)
      (GramResidual DQ (T g) (T m0) (T m1) d0 d1) =
    P.pair (GramResidual DP f n0 n1 c0 c1) (GramResidual DP g m0 m1 d0 d1) := by
  have he : ∀ x y, Q.pair (T x) (T y) = P.pair x y := h
  simp only [GramResidual, DQ.pairSubLeft, DQ.pairSubRight,
    Q.scaleLeft, Q.scaleRight, DP.pairSubLeft, DP.pairSubRight,
    P.scaleLeft, P.scaleRight, he]

/- Direct coefficient proof of NSGG42: no inverse Gram matrix and no
   presumed linearity or surjectivity of the isometry are needed. -/
theorem GramCapacity_transport {a : Analysis} (o : LedgerArithmetic a)
    {P Q : SourcePairing a} (DP : SourceDifference P) (DQ : SourceDifference Q)
    {T : P.Carrier → Q.Carrier} (h : SourceIsometry P Q T)
    (f n0 n1 : P.Carrier) :
    GramCapacity o DQ (T f) (T n0) (T n1) = GramCapacity o DP f n0 n1 := by
  have hc := source_congr_arg_two (GramResidual DQ (T f) (T n0) (T n1))
    (GramAlpha_transport o DP DQ h f n0 n1) (GramBeta_transport o DP DQ h f n0 n1)
  exact (congrArg (fun x => Q.pair x x) hc).trans
    (GramResidual_pair_transport DP DQ h f n0 n1 f n0 n1
      (GramAlpha o DP f n0 n1) (GramBeta o DP f n0 n1)
      (GramAlpha o DP f n0 n1) (GramBeta o DP f n0 n1))

theorem GramNormalEquations_transport {a : Analysis}
    {P Q : SourcePairing a} {T : P.Carrier → Q.Carrier}
    (h : SourceIsometry P Q T) (f n0 n1 : P.Carrier) (c0 c1 : a.Scalar)
    (hn : GramNormalEquations P f n0 n1 c0 c1) :
    GramNormalEquations Q (T f) (T n0) (T n1) c0 c1 := by
  have he : ∀ x y, Q.pair (T x) (T y) = P.pair x y := h
  simpa only [GramNormalEquations, he] using hn

theorem R3_frame_mellin_preserves_capacity {a : Analysis} (o : SourceArithmetic a)
    {P Q R : SourcePairing a} (DP : SourceDifference P) (DR : SourceDifference R)
    (H : R3HeatFrame P Q) (M : R3MellinRealization Q R) (f n0 n1 : P.Carrier) :
    GramCapacity o.toLedgerArithmetic DR (R3FrameMellin o H M f)
      (R3FrameMellin o H M n0) (R3FrameMellin o H M n1) =
    GramCapacity o.toLedgerArithmetic DP f n0 n1 :=
  GramCapacity_transport o.toLedgerArithmetic DP DR
    (R3_frame_mellin_isometry o H M) f n0 n1

end Fefferman
