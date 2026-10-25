import Fefferman.SourceGeometry

set_option autoImplicit false

namespace Fefferman

/- Integrated consequences of GPSourceWitness51, on one source path.
   NSSC10 and NSSC21 produce the two balance fields in Rocq; their modal and
   differential proofs remain partly Lean ports. KernelCalculus derives these
   integrated balances from explicit differential witnesses. CanonicalSource
   derives signed payment from the actual-cell local-excess assumptions. -/
structure R3SourceLedger {a : Analysis} (P : SourcePairing a) where
  Time : Type
  origin : Time
  vector : Time → P.Carrier
  storage : Time → a.Scalar
  source : Time → a.Scalar
  dissipation : Time → a.Scalar
  production : Time → a.Scalar
  nu : a.Scalar
  theta : a.Scalar
  paymentMax : a.Scalar
  nuPositive : a.lt a.zero nu
  thetaNonnegative : a.le a.zero theta
  thetaStrict : a.lt theta a.one
  massNonnegative : ∀ t, a.le a.zero (P.pair (vector t) (vector t))
  storageNonnegative : ∀ t, a.le a.zero (storage t)
  dissipationNonnegative : ∀ t, a.le a.zero (dissipation t)
  sourceBalance : ∀ t, a.le (a.add (storage t) (source t))
    (a.add (storage origin) (production t))
  coupledBalance : ∀ t, a.le
    (a.add (a.add (a.mul nu (P.pair (vector t) (vector t))) (storage t))
      (a.mul (a.mul nu nu) (dissipation t)))
    (a.add (a.add (a.mul nu (P.pair (vector origin) (vector origin))) (storage origin))
      (production t))
  signedPayment : ∀ t, a.le (production t)
    (a.add paymentMax (a.mul theta (a.mul (a.mul nu nu) (dissipation t))))
  grid : Nat → Time
  gridOrigin : grid 0 = origin
  sourceAtOrigin : source origin = a.zero
  sourceGridMonotone : ∀ n, a.le (source (grid n)) (source (grid (n + 1)))

def R3SourceMass {a : Analysis} {P : SourcePairing a} (s : R3SourceLedger P)
    (t : s.Time) : a.Scalar := P.pair (s.vector t) (s.vector t)

def R3SourceCost {a : Analysis} {P : SourcePairing a} (s : R3SourceLedger P) : a.Scalar :=
  a.add (a.add (a.mul s.nu (R3SourceMass s s.origin)) (s.storage s.origin)) s.paymentMax

def R3SourceGap {a : Analysis} {P : SourcePairing a} (s : R3SourceLedger P) : a.Scalar :=
  a.mul (a.add a.one (a.neg s.theta)) (a.mul s.nu s.nu)

def R3SourceDissipationBudget {a : Analysis} (o : SourceArithmetic a)
    {P : SourcePairing a} (s : R3SourceLedger P) : a.Scalar :=
  o.divide (R3SourceCost s) (R3SourceGap s)

def R3SourcePrefixBudget {a : Analysis} (o : SourceArithmetic a)
    {P : SourcePairing a} (s : R3SourceLedger P) : a.Scalar :=
  a.add (a.add (s.storage s.origin) s.paymentMax)
    (a.mul (a.mul s.theta (a.mul s.nu s.nu)) (R3SourceDissipationBudget o s))

def R3SourceCell {a : Analysis} {P : SourcePairing a}
    (s : R3SourceLedger P) (n : Nat) : a.Scalar :=
  a.add (s.source (s.grid (n + 1))) (a.neg (s.source (s.grid n)))

theorem source_absorb_retained_term {a : Analysis} (o : LedgerArithmetic a)
    (other value theta budget : a.Scalar)
    (h : a.le (a.add other value) (a.add budget (a.mul theta value))) :
    a.le (a.add other (a.mul (a.add a.one (a.neg theta)) value)) budget := by
  apply o.addLeCancelRight (z := a.mul theta value)
  rw [o.addAssoc, ledger_retention_split o theta value]
  exact h

theorem R3_signed_payment_absorbs {a : Analysis} (o : SourceArithmetic a)
    {P : SourcePairing a} (s : R3SourceLedger P) (t : s.Time) :
    a.le (a.add (a.add (a.mul s.nu (R3SourceMass s t)) (s.storage t))
      (a.mul (R3SourceGap s) (s.dissipation t))) (R3SourceCost s) := by
  have h := o.leTrans (s.coupledBalance t)
    (o.addLeAdd (o.leRefl
      (a.add (a.mul s.nu (R3SourceMass s s.origin)) (s.storage s.origin)))
      (s.signedPayment t))
  rw [← o.addAssoc
    (a.add (a.mul s.nu (R3SourceMass s s.origin)) (s.storage s.origin))
    s.paymentMax (a.mul s.theta (a.mul (a.mul s.nu s.nu) (s.dissipation t)))] at h
  have h1 := source_absorb_retained_term o.toLedgerArithmetic
    (a.add (a.mul s.nu (R3SourceMass s t)) (s.storage t))
    (a.mul (a.mul s.nu s.nu) (s.dissipation t)) s.theta (R3SourceCost s) h
  change a.le _ (R3SourceCost s)
  rw [R3SourceGap, o.mulAssoc]
  exact h1

theorem R3_source_gap_positive {a : Analysis} (o : SourceArithmetic a)
    {P : SourcePairing a} (s : R3SourceLedger P) : a.lt a.zero (R3SourceGap s) :=
  o.mulPositive (o.subPositive s.thetaStrict) (o.mulPositive s.nuPositive s.nuPositive)

theorem R3_source_critical_bounds {a : Analysis} (o : SourceArithmetic a)
    {P : SourcePairing a} (s : R3SourceLedger P) (t : s.Time) :
    a.le (R3SourceMass s t) (o.divide (R3SourceCost s) s.nu) ∧
    a.le (s.dissipation t) (R3SourceDissipationBudget o s) := by
  have h := R3_signed_payment_absorbs o s t
  have hgap := R3_source_gap_positive o s
  have hm := o.mulNonneg (o.ltToLe s.nuPositive) (s.massNonnegative t)
  have hother : a.le a.zero (a.add (a.mul s.nu (R3SourceMass s t)) (s.storage t)) := by
    have hh := o.addLeAdd hm (s.storageNonnegative t)
    rw [o.addZero a.zero] at hh
    exact hh
  constructor
  · apply ledger_unscale o.toLedgerArithmetic s.nuPositive
    exact o.leTrans
      (ledger_drop_right o.toLedgerArithmetic (a.mul s.nu (R3SourceMass s t))
        (s.storageNonnegative t))
      (o.leTrans (ledger_drop_right o.toLedgerArithmetic
        (a.add (a.mul s.nu (R3SourceMass s t)) (s.storage t))
        (o.mulNonneg (o.ltToLe hgap) (s.dissipationNonnegative t))) h)
  · exact ledger_unscale o.toLedgerArithmetic hgap
      (o.leTrans (ledger_drop_left o.toLedgerArithmetic
        (a.mul (R3SourceGap s) (s.dissipation t)) hother) h)

theorem R3_source_cumulative_bound {a : Analysis} (o : SourceArithmetic a)
    {P : SourcePairing a} (s : R3SourceLedger P) (t : s.Time) :
    a.le (s.source t) (R3SourcePrefixBudget o s) := by
  have h := o.leTrans
    (ledger_drop_left o.toLedgerArithmetic (s.source t) (s.storageNonnegative t))
    (s.sourceBalance t)
  have hp := s.signedPayment t
  rw [← o.mulAssoc s.theta (a.mul s.nu s.nu) (s.dissipation t)] at hp
  have hc := o.mulNonneg s.thetaNonnegative
    (o.mulNonneg (o.ltToLe s.nuPositive) (o.ltToLe s.nuPositive))
  have hd := o.mulLeLeft hc (R3_source_critical_bounds o s t).2
  have hf := o.leTrans hp (o.addLeAdd (o.leRefl s.paymentMax) hd)
  have hs := o.leTrans h (o.addLeAdd (o.leRefl (s.storage s.origin)) hf)
  rw [← o.addAssoc] at hs
  exact hs

theorem R3_source_cell_nonnegative {a : Analysis} (o : SourceArithmetic a)
    {P : SourcePairing a} (s : R3SourceLedger P) (n : Nat) :
    a.le a.zero (R3SourceCell s n) := by
  have h := o.addLeAdd (s.sourceGridMonotone n)
    (o.leRefl (a.neg (s.source (s.grid n))))
  rw [o.addNeg] at h
  exact h

theorem R3_source_prefix_is_cumulative {a : Analysis} (o : SourceArithmetic a)
    {P : SourcePairing a} (s : R3SourceLedger P) (n : Nat) :
    ledgerPrefix a (R3SourceCell s) n = s.source (s.grid n) := by
  induction n with
  | zero =>
    change a.zero = s.source (s.grid 0)
    rw [s.gridOrigin, s.sourceAtOrigin]
  | succ n ih =>
    change a.add (ledgerPrefix a (R3SourceCell s) n)
      (a.add (s.source (s.grid (n + 1))) (a.neg (s.source (s.grid n)))) =
        s.source (s.grid (n + 1))
    rw [ih, ← o.addAssoc, ledger_add_rotate o.toLedgerArithmetic,
      o.addNeg, ledger_zero_add o.toLedgerArithmetic]

structure R3SourceResult {a : Analysis} (o : SourceArithmetic a)
    {P Q R : SourcePairing a} (s : R3SourceLedger P)
    (H : R3HeatFrame P Q) (M : R3MellinRealization Q R) : Prop where
  isometry : SourceIsometry P R (R3FrameMellin o H M)
  sourceCellsNonnegative : ∀ n, a.le a.zero (R3SourceCell s n)
  sourcePrefixBound : ∀ n,
    a.le (ledgerPrefix a (R3SourceCell s) n) (R3SourcePrefixBudget o s)
  transformedMassBound : ∀ t, a.le
    (R.pair (R3FrameMellin o H M (s.vector t)) (R3FrameMellin o H M (s.vector t)))
    (o.divide (R3SourceCost s) s.nu)
  dissipationBound : ∀ t,
    a.le (s.dissipation t) (R3SourceDissipationBudget o s)

theorem R3_source_result {a : Analysis} (o : SourceArithmetic a)
    {P Q R : SourcePairing a} (s : R3SourceLedger P)
    (H : R3HeatFrame P Q) (M : R3MellinRealization Q R) : R3SourceResult o s H M := by
  refine ⟨R3_frame_mellin_isometry o H M, R3_source_cell_nonnegative o s, ?_, ?_, ?_⟩
  · intro n
    rw [R3_source_prefix_is_cumulative o s n]
    exact R3_source_cumulative_bound o s (s.grid n)
  · intro t
    rw [R3_frame_mellin_preserves_mass o H M]
    exact (R3_source_critical_bounds o s t).1
  · intro t
    exact (R3_source_critical_bounds o s t).2

end Fefferman
