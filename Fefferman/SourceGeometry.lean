import Fefferman.ScalarLedger

set_option autoImplicit false

namespace Fefferman

/- Ordinary real algebra used by the source normalization proof.
   The real-number instance remains a separate interpretation obligation. -/
structure SourceArithmetic (a : Analysis) extends LedgerArithmetic a where
  mulAssoc : ∀ x y z, a.mul (a.mul x y) z = a.mul x (a.mul y z)
  mulComm : ∀ x y, a.mul x y = a.mul y x
  mulPositive : ∀ {x y}, a.lt a.zero x → a.lt a.zero y → a.lt a.zero (a.mul x y)
  sqrt : a.Scalar → a.Scalar
  inverse : a.Scalar → a.Scalar
  sqrtSquare : ∀ x, a.le a.zero x → a.mul (sqrt x) (sqrt x) = x
  sqrtPositive : ∀ x, a.lt a.zero x → a.lt a.zero (sqrt x)
  inverseMul : ∀ x, a.lt a.zero x → a.mul (inverse x) x = a.one

structure SourcePairing (a : Analysis) where
  Carrier : Type
  pair : Carrier → Carrier → a.Scalar
  scale : a.Scalar → Carrier → Carrier
  scaleLeft : ∀ c x y, pair (scale c x) y = a.mul c (pair x y)
  scaleRight : ∀ c x y, pair x (scale c y) = a.mul c (pair x y)

def SourceIsometry {a : Analysis} (P Q : SourcePairing a)
    (T : P.Carrier → Q.Carrier) : Prop :=
  ∀ x y, Q.pair (T x) (T y) = P.pair x y

/- Source: BKQRHeatFiniteFrame. The actual heat analyzer and its continuum
   pairing theorem are supplied separately from the normalization below. -/
structure R3HeatFrame {a : Analysis} (P Q : SourcePairing a) where
  map : P.Carrier → Q.Carrier
  constant : a.Scalar
  positive : a.lt a.zero constant
  pairing : ∀ x y, Q.pair (map x) (map y) = a.mul constant (P.pair x y)

structure R3MellinRealization {a : Analysis} (Q R : SourcePairing a) where
  map : Q.Carrier → R.Carrier
  pairing : SourceIsometry Q R map

def R3NormalizedHeat {a : Analysis} (o : SourceArithmetic a)
    {P Q : SourcePairing a} (H : R3HeatFrame P Q) (x : P.Carrier) : Q.Carrier :=
  Q.scale (o.inverse (o.sqrt H.constant)) (H.map x)

def R3FrameMellin {a : Analysis} (o : SourceArithmetic a)
    {P Q R : SourcePairing a} (H : R3HeatFrame P Q)
    (M : R3MellinRealization Q R) (x : P.Carrier) : R.Carrier :=
  M.map (R3NormalizedHeat o H x)

theorem source_mul_interchange {a : Analysis} (o : SourceArithmetic a)
    (x y z : a.Scalar) : a.mul x (a.mul y z) = a.mul y (a.mul x z) := by
  rw [← o.mulAssoc x y z, o.mulComm x y, o.mulAssoc y x z]

theorem R3_inverse_sqrt_normalizes {a : Analysis} (o : SourceArithmetic a)
    (K : a.Scalar) (hK : a.lt a.zero K) :
    a.mul (o.inverse (o.sqrt K)) (a.mul (o.inverse (o.sqrt K)) K) = a.one := by
  have hs := o.sqrtPositive K hK
  have he := o.sqrtSquare K (o.ltToLe hK)
  calc
    a.mul (o.inverse (o.sqrt K)) (a.mul (o.inverse (o.sqrt K)) K) =
        a.mul (o.inverse (o.sqrt K))
          (a.mul (o.inverse (o.sqrt K)) (a.mul (o.sqrt K) (o.sqrt K))) :=
      congrArg (fun z => a.mul (o.inverse (o.sqrt K))
        (a.mul (o.inverse (o.sqrt K)) z)) he.symm
    _ = a.one := by
      rw [← o.mulAssoc (o.inverse (o.sqrt K)) (o.sqrt K) (o.sqrt K),
        o.inverseMul (o.sqrt K) hs, o.oneMul (o.sqrt K),
        o.inverseMul (o.sqrt K) hs]

theorem R3_normalized_heat_isometry {a : Analysis} (o : SourceArithmetic a)
    {P Q : SourcePairing a} (H : R3HeatFrame P Q) :
    SourceIsometry P Q (R3NormalizedHeat o H) := by
  intro x y
  change Q.pair
    (Q.scale (o.inverse (o.sqrt H.constant)) (H.map x))
    (Q.scale (o.inverse (o.sqrt H.constant)) (H.map y)) = P.pair x y
  rw [Q.scaleLeft, Q.scaleRight, H.pairing]
  rw [← o.mulAssoc (o.inverse (o.sqrt H.constant)) H.constant (P.pair x y)]
  rw [← o.mulAssoc (o.inverse (o.sqrt H.constant))
    (a.mul (o.inverse (o.sqrt H.constant)) H.constant) (P.pair x y)]
  rw [R3_inverse_sqrt_normalizes o H.constant H.positive, o.oneMul]

theorem R3_frame_mellin_isometry {a : Analysis} (o : SourceArithmetic a)
    {P Q R : SourcePairing a} (H : R3HeatFrame P Q)
    (M : R3MellinRealization Q R) : SourceIsometry P R (R3FrameMellin o H M) := by
  intro x y
  exact (M.pairing (R3NormalizedHeat o H x) (R3NormalizedHeat o H y)).trans
    (R3_normalized_heat_isometry o H x y)

def SourceGram4 {a : Analysis} (P : SourcePairing a)
    (v : Fin 4 → P.Carrier) (i j : Fin 4) : a.Scalar := P.pair (v i) (v j)

theorem R3_frame_mellin_preserves_gram {a : Analysis} (o : SourceArithmetic a)
    {P Q R : SourcePairing a} (H : R3HeatFrame P Q)
    (M : R3MellinRealization Q R) (v : Fin 4 → P.Carrier) (i j : Fin 4) :
    SourceGram4 R (fun k => R3FrameMellin o H M (v k)) i j = SourceGram4 P v i j :=
  R3_frame_mellin_isometry o H M (v i) (v j)

theorem R3_frame_mellin_preserves_mass {a : Analysis} (o : SourceArithmetic a)
    {P Q R : SourcePairing a} (H : R3HeatFrame P Q)
    (M : R3MellinRealization Q R) (x : P.Carrier) :
    R.pair (R3FrameMellin o H M x) (R3FrameMellin o H M x) = P.pair x x :=
  R3_frame_mellin_isometry o H M x x

end Fefferman
