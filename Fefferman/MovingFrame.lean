import Fefferman.FiniteSpectral

set_option autoImplicit false

namespace Fefferman

/- Canonical coordinate vector at one finite spectral cutoff.  Coordinates
   outside the cutoff are harmless: every theorem below is stated modulo the
   first `n` coordinates. -/
def R3CanonicalBasis (a : Analysis) (k : Nat) : R3FiniteVector a :=
  fun i => if i = k then a.one else a.zero

def R3CutoffEq {a : Analysis} (n : Nat) (x y : R3FiniteVector a) : Prop :=
  ∀ i, i < n → x i = y i

theorem moving_zero_mul {a : Analysis} (o : SourceArithmetic a) (x : a.Scalar) :
    a.mul a.zero x = a.zero := by
  rw [o.mulComm a.zero x, o.mulZero x]

/- A singleton ledger prefix.  This is the finite-coordinate fact underneath
   the coordinate/Parseval interpretation of the canonical frame. -/
theorem spectral_prefix_singleton {a : Analysis} (o : SourceArithmetic a)
    (k : Nat) (x : a.Scalar) :
    ∀ n, ledgerPrefix a (fun i => if i = k then x else a.zero) n =
      if k < n then x else a.zero := by
  intro n
  induction n with
  | zero =>
      simp [ledgerPrefix]
  | succ n ih =>
      by_cases hlt : k < n
      · have hne : n ≠ k := by
          intro h
          subst k
          exact (Nat.lt_irrefl n hlt)
        have hsucc : k < Nat.succ n := Nat.lt_trans hlt (Nat.lt_succ_self n)
        rw [ledgerPrefix, ih]
        simp [hlt, hsucc, hne, o.addZero]
      · by_cases heq : k = n
        · subst k
          rw [ledgerPrefix, ih]
          have hself : ¬ n < n := Nat.lt_irrefl n
          have hsucc : n < Nat.succ n := Nat.lt_succ_self n
          simp [hself, hsucc, ledger_zero_add o.toLedgerArithmetic]
        · have hsucc : ¬ k < Nat.succ n := by
            intro h
            have hle : k ≤ n := Nat.le_of_lt_succ h
            rcases Nat.lt_or_eq_of_le hle with hkn | hkn
            · exact hlt hkn
            · exact heq hkn
          have hne : n ≠ k := by
            intro h
            exact heq h.symm
          rw [ledgerPrefix, ih]
          simp [hlt, hsucc, hne, o.addZero]

/- Pairing against the canonical coordinate frame reads the actual coordinate.
   No positivity or completeness hypothesis is needed for this finite identity. -/
theorem R3_canonical_basis_coordinate {a : Analysis} (o : SourceArithmetic a)
    (n k : Nat) (x : R3FiniteVector a) (hk : k < n) :
    R3FiniteDot a n (R3CanonicalBasis a k) x = x k := by
  unfold R3FiniteDot
  have hterm : ∀ i, i < n →
      a.mul (R3CanonicalBasis a k i) (x i) =
        if i = k then x k else a.zero := by
    intro i _
    by_cases hik : i = k
    · subst i
      simp [R3CanonicalBasis, o.oneMul]
    · simp [R3CanonicalBasis, hik, moving_zero_mul o]
  rw [spectral_prefix_congr a n _ _ hterm]
  rw [spectral_prefix_singleton o k (x k) n]
  simp [hk]

/- The moving frame is simply the canonical cutoff frame transported through
   the already-constructed normalized heat/Mellin isometry. -/
def R3MovingFrameVector {a : Analysis} (o : SourceArithmetic a) (n : Nat)
    {Q R : SourcePairing a} (H : R3HeatFrame (R3FinitePairing o n) Q)
    (M : R3MellinRealization Q R) (k : Nat) : R.Carrier :=
  R3FrameMellin o H M (R3CanonicalBasis a k)

def R3FrameMellinImage {a : Analysis} (o : SourceArithmetic a) (n : Nat)
    {Q R : SourcePairing a} (H : R3HeatFrame (R3FinitePairing o n) Q)
    (M : R3MellinRealization Q R) (y : R.Carrier) : Prop :=
  ∃ x : R3FiniteVector a, y = R3FrameMellin o H M x

/- Exact moving-coordinate readout. -/
theorem R3_moving_frame_coordinate {a : Analysis} (o : SourceArithmetic a)
    (n k : Nat) {Q R : SourcePairing a}
    (H : R3HeatFrame (R3FinitePairing o n) Q) (M : R3MellinRealization Q R)
    (x : R3FiniteVector a) (hk : k < n) :
    R.pair (R3MovingFrameVector o n H M k) (R3FrameMellin o H M x) = x k := by
  calc
    R.pair (R3MovingFrameVector o n H M k) (R3FrameMellin o H M x) =
        R3FiniteDot a n (R3CanonicalBasis a k) x :=
      R3_frame_mellin_isometry o H M (R3CanonicalBasis a k) x
    _ = x k := R3_canonical_basis_coordinate o n k x hk

/- The transported frame has the Kronecker Gram matrix on the cutoff. -/
theorem R3_moving_frame_gram {a : Analysis} (o : SourceArithmetic a)
    (n i j : Nat) {Q R : SourcePairing a}
    (H : R3HeatFrame (R3FinitePairing o n) Q) (M : R3MellinRealization Q R)
    (hi : i < n) (hj : j < n) :
    R.pair (R3MovingFrameVector o n H M i) (R3MovingFrameVector o n H M j) =
      if i = j then a.one else a.zero := by
  calc
    R.pair (R3MovingFrameVector o n H M i) (R3MovingFrameVector o n H M j) =
        R3CanonicalBasis a j i :=
      R3_moving_frame_coordinate o n i H M (R3CanonicalBasis a j) hi
    _ = if i = j then a.one else a.zero := rfl

/- Exact finite Parseval identity for every vector in the physical/image
   subspace.  This is stronger than preservation of a selected Gram block. -/
theorem R3_moving_frame_parseval {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) {Q R : SourcePairing a}
    (H : R3HeatFrame (R3FinitePairing o n) Q) (M : R3MellinRealization Q R)
    (x : R3FiniteVector a) :
    R.pair (R3FrameMellin o H M x) (R3FrameMellin o H M x) =
      ledgerPrefix a (fun i => a.mul (x i) (x i)) n := by
  exact R3_frame_mellin_isometry o H M x x

/- Completeness on the image, formulated without assuming that the ambient
   target carrier contains no extra GP objects: all cutoff coordinates of an
   image vector are recovered by the moving frame, hence the frame separates
   physical-image vectors modulo cutoff. -/
theorem R3_moving_frame_coordinates_complete {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) {Q R : SourcePairing a}
    (H : R3HeatFrame (R3FinitePairing o n) Q) (M : R3MellinRealization Q R)
    (x y : R3FiniteVector a)
    (h : ∀ k, k < n →
      R.pair (R3MovingFrameVector o n H M k) (R3FrameMellin o H M x) =
      R.pair (R3MovingFrameVector o n H M k) (R3FrameMellin o H M y)) :
    R3CutoffEq n x y := by
  intro k hk
  calc
    x k = R.pair (R3MovingFrameVector o n H M k) (R3FrameMellin o H M x) :=
      (R3_moving_frame_coordinate o n k H M x hk).symm
    _ = R.pair (R3MovingFrameVector o n H M k) (R3FrameMellin o H M y) := h k hk
    _ = y k := R3_moving_frame_coordinate o n k H M y hk

/- Every target vector in the transform image has exact moving-frame
   coordinates and exact Parseval energy. -/
theorem R3_moving_frame_complete_on_image {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) {Q R : SourcePairing a}
    (H : R3HeatFrame (R3FinitePairing o n) Q) (M : R3MellinRealization Q R)
    (y : R.Carrier) (hy : R3FrameMellinImage o n H M y) :
    ∃ x : R3FiniteVector a,
      y = R3FrameMellin o H M x ∧
      (∀ k, k < n → R.pair (R3MovingFrameVector o n H M k) y = x k) ∧
      R.pair y y = ledgerPrefix a (fun i => a.mul (x i) (x i)) n := by
  rcases hy with ⟨x, rfl⟩
  exact ⟨x, rfl, (fun k hk => R3_moving_frame_coordinate o n k H M x hk),
    R3_moving_frame_parseval o n H M x⟩

/- A compact theorem collecting the literal finite-cut moving Parseval-frame
   properties.  “Basis” is meant on the transform image and modulo the cutoff;
   no surjectivity onto unrelated ambient GP objects is asserted. -/
def R3MovingParsevalFrameOnImage {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) {Q R : SourcePairing a}
    (H : R3HeatFrame (R3FinitePairing o n) Q) (M : R3MellinRealization Q R) : Prop :=
  (∀ i j, i < n → j < n →
    R.pair (R3MovingFrameVector o n H M i) (R3MovingFrameVector o n H M j) =
      if i = j then a.one else a.zero) ∧
  (∀ x : R3FiniteVector a, ∀ k, k < n →
    R.pair (R3MovingFrameVector o n H M k) (R3FrameMellin o H M x) = x k) ∧
  (∀ x : R3FiniteVector a,
    R.pair (R3FrameMellin o H M x) (R3FrameMellin o H M x) =
      ledgerPrefix a (fun i => a.mul (x i) (x i)) n) ∧
  (∀ x y : R3FiniteVector a,
    (∀ k, k < n →
      R.pair (R3MovingFrameVector o n H M k) (R3FrameMellin o H M x) =
      R.pair (R3MovingFrameVector o n H M k) (R3FrameMellin o H M y)) →
    R3CutoffEq n x y)

theorem R3_FRAME_MELLIN_IS_MOVING_PARSEVAL_FRAME_ON_IMAGE {a : Analysis}
    (o : SourceArithmetic a) (n : Nat) {Q R : SourcePairing a}
    (H : R3HeatFrame (R3FinitePairing o n) Q) (M : R3MellinRealization Q R) :
    R3MovingParsevalFrameOnImage o n H M := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hi hj
    exact R3_moving_frame_gram o n i j H M hi hj
  · intro x k hk
    exact R3_moving_frame_coordinate o n k H M x hk
  · intro x
    exact R3_moving_frame_parseval o n H M x
  · intro x y h
    exact R3_moving_frame_coordinates_complete o n H M x y h

end Fefferman
