import Fefferman.ReducedCapacity
import Fefferman.R3SourceBranch

set_option autoImplicit false

namespace Fefferman

theorem spectral_prefix_congr (a : Analysis) (n : Nat) (f g : Nat → a.Scalar) :
    (∀ i, i < n → f i = g i) → ledgerPrefix a f n = ledgerPrefix a g n := by
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    exact source_congr_arg_two a.add
      (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))))
      (h n (Nat.lt_succ_self n))

theorem spectral_add_shuffle {a : Analysis} (o : LedgerArithmetic a)
    (w x y z : a.Scalar) :
    a.add (a.add w x) (a.add y z) = a.add (a.add w y) (a.add x z) := by
  calc
    a.add (a.add w x) (a.add y z) = a.add w (a.add x (a.add y z)) := o.addAssoc w x _
    _ = a.add w (a.add (a.add x y) z) := congrArg (a.add w) (o.addAssoc x y z).symm
    _ = a.add w (a.add (a.add y x) z) :=
      congrArg (fun t => a.add w (a.add t z)) (o.addComm x y)
    _ = a.add w (a.add y (a.add x z)) := congrArg (a.add w) (o.addAssoc y x z)
    _ = a.add (a.add w y) (a.add x z) := (o.addAssoc w y _).symm

theorem spectral_prefix_add {a : Analysis} (o : LedgerArithmetic a)
    (f g : Nat → a.Scalar) (n : Nat) :
    ledgerPrefix a (fun i => a.add (f i) (g i)) n =
      a.add (ledgerPrefix a f n) (ledgerPrefix a g n) := by
  induction n with
  | zero => exact (o.addZero a.zero).symm
  | succ n ih =>
    change a.add (ledgerPrefix a (fun i => a.add (f i) (g i)) n) (a.add (f n) (g n)) =
      a.add (a.add (ledgerPrefix a f n) (f n)) (a.add (ledgerPrefix a g n) (g n))
    exact (congrArg (fun x => a.add x (a.add (f n) (g n))) ih).trans
      (spectral_add_shuffle o (ledgerPrefix a f n) (ledgerPrefix a g n) (f n) (g n))

theorem spectral_prefix_zero {a : Analysis} (o : LedgerArithmetic a) (n : Nat) :
    ledgerPrefix a (fun _ => a.zero) n = a.zero := by
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg (fun x => a.add x a.zero) ih).trans (o.addZero a.zero)

theorem spectral_neg_of_add_zero {a : Analysis} (o : LedgerArithmetic a)
    (x y : a.Scalar) (h : a.add x y = a.zero) : y = a.neg x := by
  calc
    y = a.add a.zero y := (ledger_zero_add o y).symm
    _ = a.add (a.add (a.neg x) x) y :=
      congrArg (fun z => a.add z y) (ledger_neg_add o x).symm
    _ = a.add (a.neg x) (a.add x y) := o.addAssoc (a.neg x) x y
    _ = a.add (a.neg x) a.zero := congrArg (a.add (a.neg x)) h
    _ = a.neg x := o.addZero (a.neg x)

theorem spectral_mul_neg {a : Analysis} (o : LedgerArithmetic a) (x y : a.Scalar) :
    a.mul x (a.neg y) = a.neg (a.mul x y) := by
  apply spectral_neg_of_add_zero o (a.mul x y) (a.mul x (a.neg y))
  exact (o.mulAdd x y (a.neg y)).symm.trans
    ((congrArg (a.mul x) (o.addNeg y)).trans (o.mulZero x))

theorem spectral_neg_mul {a : Analysis} (o : SourceArithmetic a) (x y : a.Scalar) :
    a.mul (a.neg x) y = a.neg (a.mul x y) :=
  (o.mulComm (a.neg x) y).trans ((spectral_mul_neg o.toLedgerArithmetic y x).trans
    (congrArg a.neg (o.mulComm y x)))

theorem spectral_prefix_neg {a : Analysis} (o : LedgerArithmetic a)
    (f : Nat → a.Scalar) (n : Nat) :
    ledgerPrefix a (fun i => a.neg (f i)) n = a.neg (ledgerPrefix a f n) := by
  apply spectral_neg_of_add_zero o (ledgerPrefix a f n) _
  calc
    a.add (ledgerPrefix a f n) (ledgerPrefix a (fun i => a.neg (f i)) n) =
        ledgerPrefix a (fun i => a.add (f i) (a.neg (f i))) n :=
      (spectral_prefix_add o f (fun i => a.neg (f i)) n).symm
    _ = ledgerPrefix a (fun _ => a.zero) n :=
      spectral_prefix_congr a n _ _ (fun i _ => o.addNeg (f i))
    _ = a.zero := spectral_prefix_zero o n

abbrev R3FiniteVector (a : Analysis) := Nat → a.Scalar

def R3FiniteDot (a : Analysis) (n : Nat) (x y : R3FiniteVector a) : a.Scalar :=
  ledgerPrefix a (fun i => a.mul (x i) (y i)) n

def R3FiniteScale (a : Analysis) (c : a.Scalar) (x : R3FiniteVector a) : R3FiniteVector a :=
  fun i => a.mul c (x i)

def R3FiniteSub (a : Analysis) (x y : R3FiniteVector a) : R3FiniteVector a :=
  fun i => a.add (x i) (a.neg (y i))

theorem R3_finite_dot_symmetric {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (x y : R3FiniteVector a) : R3FiniteDot a n x y = R3FiniteDot a n y x :=
  spectral_prefix_congr a n _ _ (fun i _ => o.mulComm (x i) (y i))

theorem R3_finite_dot_scale_left {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (c : a.Scalar) (x y : R3FiniteVector a) :
    R3FiniteDot a n (R3FiniteScale a c x) y = a.mul c (R3FiniteDot a n x y) :=
  (spectral_prefix_congr a n _ _ (fun i _ => o.mulAssoc c (x i) (y i))).trans
    (ledger_prefix_scale o.toLedgerArithmetic c (fun i => a.mul (x i) (y i)) n)

theorem R3_finite_dot_scale_right {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (c : a.Scalar) (x y : R3FiniteVector a) :
    R3FiniteDot a n x (R3FiniteScale a c y) = a.mul c (R3FiniteDot a n x y) :=
  (R3_finite_dot_symmetric o n x (R3FiniteScale a c y)).trans
    ((R3_finite_dot_scale_left o n c y x).trans
      (congrArg (a.mul c) (R3_finite_dot_symmetric o n y x)))

def R3FinitePairing {a : Analysis} (o : SourceArithmetic a) (n : Nat) : SourcePairing a where
  Carrier := R3FiniteVector a
  pair := R3FiniteDot a n
  scale := R3FiniteScale a
  scaleLeft := R3_finite_dot_scale_left o n
  scaleRight := R3_finite_dot_scale_right o n

theorem R3_finite_dot_sub_left {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (x y z : R3FiniteVector a) :
    R3FiniteDot a n (R3FiniteSub a x y) z =
      a.add (R3FiniteDot a n x z) (a.neg (R3FiniteDot a n y z)) := by
  have hp : ledgerPrefix a (fun i => a.mul (a.add (x i) (a.neg (y i))) (z i)) n =
      ledgerPrefix a (fun i => a.add (a.mul (x i) (z i)) (a.neg (a.mul (y i) (z i)))) n :=
    spectral_prefix_congr a n _ _ (fun i _ =>
      (o.addMul (x i) (a.neg (y i)) (z i)).trans
        (congrArg (a.add (a.mul (x i) (z i))) (spectral_neg_mul o (y i) (z i))))
  exact hp.trans ((spectral_prefix_add o.toLedgerArithmetic
    (fun i => a.mul (x i) (z i)) (fun i => a.neg (a.mul (y i) (z i))) n).trans
      (congrArg (a.add (R3FiniteDot a n x z))
        (spectral_prefix_neg o.toLedgerArithmetic (fun i => a.mul (y i) (z i)) n)))

theorem R3_finite_dot_sub_right {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (x y z : R3FiniteVector a) :
    R3FiniteDot a n x (R3FiniteSub a y z) =
      a.add (R3FiniteDot a n x y) (a.neg (R3FiniteDot a n x z)) :=
  (R3_finite_dot_symmetric o n x (R3FiniteSub a y z)).trans
    ((R3_finite_dot_sub_left o n y z x).trans
      (source_congr_arg_two a.add (R3_finite_dot_symmetric o n y x)
        (congrArg a.neg (R3_finite_dot_symmetric o n z x))))

def R3FiniteDifference {a : Analysis} (o : SourceArithmetic a) (n : Nat) :
    SourceDifference (R3FinitePairing o n) where
  sub := R3FiniteSub a
  pairSubLeft := R3_finite_dot_sub_left o n
  pairSubRight := R3_finite_dot_sub_right o n

theorem spectral_square_product {a : Analysis} (o : SourceArithmetic a) (x y : a.Scalar) :
    a.mul (a.mul x y) (a.mul x y) = a.mul (a.mul x x) (a.mul y y) :=
  (o.mulAssoc x y (a.mul x y)).trans
    ((congrArg (a.mul x) (source_mul_interchange o y x y)).trans
      (o.mulAssoc x x (a.mul y y)).symm)

def R3FiniteH12Mass (a : Analysis) (n : Nat) (radius u : R3FiniteVector a) : a.Scalar :=
  ledgerPrefix a (fun i => a.mul (a.mul (radius i) (u i)) (u i)) n

def R3FiniteH32Density (a : Analysis) (n : Nat) (radius u : R3FiniteVector a) : a.Scalar :=
  ledgerPrefix a (fun i =>
    a.mul (a.mul (a.mul (a.mul (radius i) (radius i)) (radius i)) (u i)) (u i)) n

def R3H12Embed {a : Analysis} (o : SourceArithmetic a)
    (radius u : R3FiniteVector a) : R3FiniteVector a :=
  fun i => a.mul (o.sqrt (radius i)) (u i)

def R3H32Embed {a : Analysis} (o : SourceArithmetic a)
    (radius u : R3FiniteVector a) : R3FiniteVector a :=
  fun i => a.mul (a.mul (radius i) (o.sqrt (radius i))) (u i)

theorem R3_h12_coordinate_square {a : Analysis} (o : SourceArithmetic a)
    (r u : a.Scalar) (hr : a.le a.zero r) :
    a.mul (a.mul (o.sqrt r) u) (a.mul (o.sqrt r) u) = a.mul (a.mul r u) u :=
  (spectral_square_product o (o.sqrt r) u).trans
    ((congrArg (fun z => a.mul z (a.mul u u)) (o.sqrtSquare r hr)).trans
      (o.mulAssoc r u u).symm)

theorem R3_h32_coordinate_square {a : Analysis} (o : SourceArithmetic a)
    (r u : a.Scalar) (hr : a.le a.zero r) :
    a.mul (a.mul (a.mul r (o.sqrt r)) u) (a.mul (a.mul r (o.sqrt r)) u) =
      a.mul (a.mul (a.mul (a.mul r r) r) u) u := by
  have hw : a.mul (a.mul r (o.sqrt r)) (a.mul r (o.sqrt r)) = a.mul (a.mul r r) r :=
    (spectral_square_product o r (o.sqrt r)).trans
      (congrArg (a.mul (a.mul r r)) (o.sqrtSquare r hr))
  exact (spectral_square_product o (a.mul r (o.sqrt r)) u).trans
    ((congrArg (fun z => a.mul z (a.mul u u)) hw).trans
      (o.mulAssoc (a.mul (a.mul r r) r) u u).symm)

theorem R3_h12_embedding_norm {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (radius u : R3FiniteVector a) (hr : ∀ i, i < n → a.le a.zero (radius i)) :
    R3FiniteDot a n (R3H12Embed o radius u) (R3H12Embed o radius u) =
      R3FiniteH12Mass a n radius u :=
  spectral_prefix_congr a n _ _ (fun i hi => R3_h12_coordinate_square o (radius i) (u i) (hr i hi))

theorem R3_h32_embedding_norm {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (radius u : R3FiniteVector a) (hr : ∀ i, i < n → a.le a.zero (radius i)) :
    R3FiniteDot a n (R3H32Embed o radius u) (R3H32Embed o radius u) =
      R3FiniteH32Density a n radius u :=
  spectral_prefix_congr a n _ _ (fun i hi => R3_h32_coordinate_square o (radius i) (u i) (hr i hi))

/- The source cut_dissipation with lambda_i = radius_i^2. -/
def R3FinitePacketDissipation (a : Analysis) (n : Nat) (radius u : R3FiniteVector a) : a.Scalar :=
  ledgerPrefix a (fun i =>
    a.mul (a.mul (a.mul (radius i) (a.mul (radius i) (radius i))) (u i)) (u i)) n

theorem R3_packet_dissipation_is_h32 {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (radius u : R3FiniteVector a) :
    R3FinitePacketDissipation a n radius u = R3FiniteH32Density a n radius u :=
  spectral_prefix_congr a n _ _ (fun i _ =>
    congrArg (fun z => a.mul (a.mul z (u i)) (u i))
      (o.mulAssoc (radius i) (radius i) (radius i)).symm)

theorem R3_packet_dissipation_is_embedding_norm {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (radius u : R3FiniteVector a) (hr : ∀ i, i < n → a.le a.zero (radius i)) :
    R3FinitePacketDissipation a n radius u =
      R3FiniteDot a n (R3H32Embed o radius u) (R3H32Embed o radius u) :=
  (R3_packet_dissipation_is_h32 o n radius u).trans (R3_h32_embedding_norm o n radius u hr).symm

/- Equality transport of NSR3H22. Primitive is the caller's actual time-
   primitive relation; no integration or differentiation rule is postulated. -/
theorem R3_h32_primitive_transport {a : Analysis} (o : SourceArithmetic a)
    {Time : Type} (n : Nat) (radius : R3FiniteVector a) (u : Time → R3FiniteVector a)
    (hr : ∀ i, i < n → a.le a.zero (radius i))
    (Primitive : (Time → a.Scalar) → (Time → a.Scalar) → Prop)
    (cumulative : Time → a.Scalar)
    (h : Primitive (fun t => R3FinitePacketDissipation a n radius (u t)) cumulative) :
    Primitive (fun t => R3FiniteDot a n (R3H32Embed o radius (u t))
      (R3H32Embed o radius (u t))) cumulative := by
  have he : (fun t => R3FinitePacketDissipation a n radius (u t)) =
      (fun t => R3FiniteDot a n (R3H32Embed o radius (u t)) (R3H32Embed o radius (u t))) :=
    funext (fun t => R3_packet_dissipation_is_embedding_norm o n radius (u t) hr)
  exact he ▸ h

theorem R3_frame_mellin_h12_identification {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) {Q R : SourcePairing a} (H : R3HeatFrame (R3FinitePairing o n) Q)
    (M : R3MellinRealization Q R) (radius u : R3FiniteVector a)
    (hr : ∀ i, i < n → a.le a.zero (radius i)) :
    R.pair (R3FrameMellin o H M (R3H12Embed o radius u))
      (R3FrameMellin o H M (R3H12Embed o radius u)) = R3FiniteH12Mass a n radius u :=
  (R3_frame_mellin_preserves_mass o H M (R3H12Embed o radius u)).trans
    (R3_h12_embedding_norm o n radius u hr)

theorem R3_finite_frame_mellin_capacity {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) {Q R : SourcePairing a} (DR : SourceDifference R)
    (H : R3HeatFrame (R3FinitePairing o n) Q) (M : R3MellinRealization Q R)
    (f n0 n1 : R3FiniteVector a) :
    GramCapacity o.toLedgerArithmetic DR (R3FrameMellin o H M f)
      (R3FrameMellin o H M n0) (R3FrameMellin o H M n1) =
    GramCapacity o.toLedgerArithmetic (R3FiniteDifference o n) f n0 n1 :=
  R3_frame_mellin_preserves_capacity o (R3FiniteDifference o n) DR H M f n0 n1

/- This identifies the existing ledger's exact vector path. The velocity is
   never reconstructed merely from a matching input label. -/
structure R3SpectralBinding {a : Analysis} (o : SourceArithmetic a) (n : Nat)
    (s : R3SourceLedger (R3FinitePairing o n)) where
  radius : R3FiniteVector a
  velocity : s.Time → R3FiniteVector a
  radiusNonnegative : ∀ i, i < n → a.le a.zero (radius i)
  vectorIsEmbed : ∀ t, s.vector t = R3H12Embed o radius (velocity t)

theorem R3_source_mass_is_finite_h12 {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (s : R3SourceLedger (R3FinitePairing o n)) (b : R3SpectralBinding o n s)
    (t : s.Time) : R3SourceMass s t = R3FiniteH12Mass a n b.radius (b.velocity t) :=
  (congrArg (fun x => R3FiniteDot a n x x) (b.vectorIsEmbed t)).trans
    (R3_h12_embedding_norm o n b.radius (b.velocity t) b.radiusNonnegative)

structure R3SpectralResult {a : Analysis} (o : SourceArithmetic a) (n : Nat)
    (s : R3SourceLedger (R3FinitePairing o n)) (b : R3SpectralBinding o n s)
    {Q R : SourcePairing a} (H : R3HeatFrame (R3FinitePairing o n) Q)
    (M : R3MellinRealization Q R) : Prop where
  source : R3SourceResult o s H M
  massIdentification : ∀ t, R3SourceMass s t = R3FiniteH12Mass a n b.radius (b.velocity t)
  transformedIdentification : ∀ t,
    R.pair (R3FrameMellin o H M (s.vector t)) (R3FrameMellin o H M (s.vector t)) =
      R3FiniteH12Mass a n b.radius (b.velocity t)
  h12Bound : ∀ t, a.le (R3FiniteH12Mass a n b.radius (b.velocity t))
    (o.divide (R3SourceCost s) s.nu)
  h32DensityIdentification : ∀ t, R3FinitePacketDissipation a n b.radius (b.velocity t) =
    R3FiniteDot a n (R3H32Embed o b.radius (b.velocity t)) (R3H32Embed o b.radius (b.velocity t))

theorem R3_source_spectral_result {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (s : R3SourceLedger (R3FinitePairing o n)) (b : R3SpectralBinding o n s)
    {Q R : SourcePairing a} (H : R3HeatFrame (R3FinitePairing o n) Q)
    (M : R3MellinRealization Q R) (hs : R3SourceResult o s H M) :
    R3SpectralResult o n s b H M := by
  have hi : ∀ t, R.pair (R3FrameMellin o H M (s.vector t))
      (R3FrameMellin o H M (s.vector t)) = R3FiniteH12Mass a n b.radius (b.velocity t) :=
    fun t => (R3_frame_mellin_preserves_mass o H M (s.vector t)).trans
      (R3_source_mass_is_finite_h12 o n s b t)
  refine ⟨hs, R3_source_mass_is_finite_h12 o n s b, hi, ?_, ?_⟩
  · intro t
    have hb := hs.transformedMassBound t
    rw [hi t] at hb
    exact hb
  · intro t
    exact R3_packet_dissipation_is_embedding_norm o n b.radius (b.velocity t) b.radiusNonnegative

end Fefferman
