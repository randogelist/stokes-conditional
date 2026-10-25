import Fefferman.KernelCalculus

set_option autoImplicit false

namespace Fefferman

def KernelSourceCell {a : Analysis} {P : SourcePairing a}
    (s : KernelSourcePath P) (n : Nat) : a.Scalar :=
  KSub a (s.source (s.grid (n+1))) (s.source (s.grid n))

def KernelSourceExcess {a : Analysis} {P : SourcePairing a}
    (s : KernelSourcePath P) (theta : a.Scalar) (t : s.Time) : a.Scalar :=
  KSub a (s.production t) (a.mul theta (a.mul (a.mul s.nu s.nu) (s.dissipation t)))

theorem kernel_source_cells_nonnegative {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} (s : KernelSourcePath P) (n : Nat) :
    a.le a.zero (KernelSourceCell s n) := k_sub_nonneg o (s.sourceGridMonotone n)

theorem kernel_source_cells_telescope {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} (s : KernelSourcePath P) (n : Nat) :
    ledgerPrefix a (KernelSourceCell s) n = s.source (s.grid n) := by
  have h := k_prefix_telescope o (fun k => s.source (s.grid k)) n
  rw [s.gridOrigin, s.sourceInitial, k_sub_zero o] at h
  exact h

theorem kernel_source_excess_initial {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} (s : KernelSourcePath P) (theta : a.Scalar) :
    KernelSourceExcess s theta (s.grid 0) = a.zero := by
  rw [s.gridOrigin, KernelSourceExcess, s.productionInitial, s.dissipationInitial,
    o.mulZero, o.mulZero, k_sub_self o]

/- Source v0.59: boundary and paid sequences are definitions, not freely
   supplied budgets. The local excess defect and total paid budget remain the
   source's explicit physical hypotheses. -/
structure CanonicalSourceRenewal {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} (s : KernelSourcePath P) (theta : a.Scalar) where
  internal : Nat → a.Scalar
  uv : Nat → a.Scalar
  budget : a.Scalar
  internalNonnegative : ∀ n, a.le a.zero (internal n)
  uvNonnegative : ∀ n, a.le a.zero (uv n)
  internalGap : ∀ n, a.le (KScale o 121 (internal n)) (KScale o 25 (KernelSourceCell s n))
  uvRetention : ∀ n, a.le (KScale o 5 (uv n))
    (KScale o 4 (KSub a (KernelSourceCell s n) (internal n)))
  paidBound : ∀ n, a.le
    (ledgerPrefix a (fun k => CanonicalPaid a (KernelSourceCell s (k+1)) (internal k) (uv k)) n) budget
  before : s.Time → s.Time → Prop
  beforeRefl : ∀ t, before t t
  gridOrdered : ∀ n, before (s.grid n) (s.grid (n+1))
  cover : ∀ t, ∃ n, before (s.grid n) t ∧ before t (s.grid (n+1))
  localExcess : ∀ n t, before (s.grid n) t → before t (s.grid (n+1)) →
    a.le (KScale o 605 (KSub a (KernelSourceExcess s theta t)
      (KernelSourceExcess s theta (s.grid n))))
      (KSub a (KScale o 605 (KernelSourceCell s (n+1))) (KScale o 509 (KernelSourceCell s n)))

noncomputable def canonicalSourcePaid {a : Analysis} {o : KernelArithmetic a}
    {P : SourcePairing a} {s : KernelSourcePath P} {theta : a.Scalar}
    (c : CanonicalSourceRenewal o s theta) (n : Nat) : a.Scalar :=
  CanonicalPaid a (KernelSourceCell s (n+1)) (c.internal n) (c.uv n)

theorem canonical_source_boundary {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {s : KernelSourcePath P} {theta : a.Scalar}
    (c : CanonicalSourceRenewal o s theta) (n : Nat) :
    a.le a.zero (KSub a (KernelSourceCell s n) (c.internal n)) :=
  canonical_boundary_nonnegative o _ _ (c.internalNonnegative n)
    (kernel_source_cells_nonnegative o s n) (c.internalGap n)

theorem canonical_source_gp509 {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {s : KernelSourcePath P} {theta : a.Scalar}
    (c : CanonicalSourceRenewal o s theta) :
    GP509Certificate o (KernelSourceCell s) (canonicalSourcePaid c) :=
  canonical_firewall o _ _ _ (kernel_source_cells_nonnegative o s) c.internalGap c.uvRetention

theorem canonical_source_budget_nonnegative {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {s : KernelSourcePath P} {theta : a.Scalar}
    (c : CanonicalSourceRenewal o s theta) : a.le a.zero c.budget := c.paidBound 0

theorem canonical_source_m7 {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {s : KernelSourcePath P} {theta : a.Scalar}
    (c : CanonicalSourceRenewal o s theta) : KernelM7 a (KernelSourceCell s) :=
  kernel_gp509_m7 o (canonical_source_gp509 o c)
    ⟨c.budget, canonical_source_budget_nonnegative o c, c.paidBound⟩

/- Local defect <= paid cell follows from the DERIVED 509 recurrence. -/
theorem canonical_local_excess_paid {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {s : KernelSourcePath P} {theta : a.Scalar}
    (c : CanonicalSourceRenewal o s theta) (n : Nat) (t : s.Time)
    (hlo : c.before (s.grid n) t) (hhi : c.before t (s.grid (n+1))) :
    a.le (KSub a (KernelSourceExcess s theta t) (KernelSourceExcess s theta (s.grid n)))
      (canonicalSourcePaid c n) := by
  have hr := (canonical_source_gp509 o c).step n
  rw [o.addComm] at hr
  have hd := k_le_add_to_sub_le o hr
  exact k_scale_cancel o 605 (by decide) (o.leTrans (c.localExcess n t hlo hhi) hd)

theorem canonical_grid_excess_bound {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {s : KernelSourcePath P} {theta : a.Scalar}
    (c : CanonicalSourceRenewal o s theta) (n : Nat) :
    a.le (KernelSourceExcess s theta (s.grid n)) (ledgerPrefix a (canonicalSourcePaid c) n) := by
  induction n with
  | zero =>
    rw [kernel_source_excess_initial o]
    exact o.leRefl a.zero
  | succ n ih =>
    have hl := canonical_local_excess_paid o c n (s.grid (n+1))
      (c.gridOrdered n) (c.beforeRefl (s.grid (n+1)))
    have hp := o.addLeAdd ih hl
    rw [k_add_sub o] at hp
    exact hp

theorem canonical_global_excess_bound {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {s : KernelSourcePath P} {theta : a.Scalar}
    (c : CanonicalSourceRenewal o s theta) (t : s.Time) :
    a.le (KernelSourceExcess s theta t) c.budget := by
  rcases c.cover t with ⟨n, hlo, hhi⟩
  have hp := o.addLeAdd (canonical_grid_excess_bound o c n)
    (canonical_local_excess_paid o c n t hlo hhi)
  rw [k_add_sub o] at hp
  exact o.leTrans hp (c.paidBound (n+1))

theorem canonical_source_signed_budget {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {s : KernelSourcePath P} {theta : a.Scalar}
    (c : CanonicalSourceRenewal o s theta) (t : s.Time) :
    a.le (s.production t) (a.add (a.add (KernelSourceCell s 0) c.budget)
      (a.mul theta (a.mul (a.mul s.nu s.nu) (s.dissipation t)))) := by
  have h := k_sub_le_to_le_add o (canonical_global_excess_bound o c t)
  exact o.leTrans h (o.addLeAdd
    (ledger_drop_left o.toLedgerArithmetic c.budget (kernel_source_cells_nonnegative o s 0))
    (o.leRefl _))

def canonical_source_ledger {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} (s : KernelSourcePath P) (theta : a.Scalar)
    (ht0 : a.le a.zero theta) (ht1 : a.lt theta a.one)
    (c : CanonicalSourceRenewal o s theta) : R3SourceLedger P where
  Time := s.Time
  origin := s.origin
  vector := s.vector
  storage := s.storage
  source := s.source
  dissipation := s.dissipation
  production := s.production
  nu := s.nu
  theta := theta
  paymentMax := a.add (KernelSourceCell s 0) c.budget
  nuPositive := s.nuPositive
  thetaNonnegative := ht0
  thetaStrict := ht1
  massNonnegative := s.massNonnegative
  storageNonnegative := s.storageNonnegative
  dissipationNonnegative := s.dissipationNonnegative
  sourceBalance := s.sourceBalance
  coupledBalance := kernel_source_coupled_balance o s
  signedPayment := canonical_source_signed_budget o c
  grid := s.grid
  gridOrigin := s.gridOrigin
  sourceAtOrigin := s.sourceInitial
  sourceGridMonotone := s.sourceGridMonotone

theorem canonical_source_critical {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} (s : KernelSourcePath P) (theta : a.Scalar)
    (ht0 : a.le a.zero theta) (ht1 : a.lt theta a.one)
    (c : CanonicalSourceRenewal o s theta) :
    KernelCriticalControl a (fun t => P.pair (s.vector t) (s.vector t)) s.dissipation := by
  let L := canonical_source_ledger o s theta ht0 ht1 c
  have hq := k_add_nonneg o (kernel_source_cells_nonnegative o s 0) (canonical_source_budget_nonnegative o c)
  have hk : a.le a.zero (R3SourceCost L) :=
    k_add_nonneg o (k_add_nonneg o
      (o.mulNonneg (o.ltToLe s.nuPositive) (s.massNonnegative s.origin)) (s.storageNonnegative s.origin)) hq
  refine ⟨⟨o.divide (R3SourceCost L) s.nu, R3SourceDissipationBudget o.toSourceArithmetic L,
    k_div_nonneg o hk s.nuPositive,
    k_div_nonneg o hk (R3_source_gap_positive o.toSourceArithmetic L), ?_, ?_⟩⟩
  · exact fun t => (R3_source_critical_bounds o.toSourceArithmetic L t).1
  · exact fun t => (R3_source_critical_bounds o.toSourceArithmetic L t).2

theorem canonical_source_sampled_critical {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} (s : KernelSourcePath P) (theta : a.Scalar)
    (ht0 : a.le a.zero theta) (ht1 : a.lt theta a.one)
    (c : CanonicalSourceRenewal o s theta) (grid : Nat → s.Time) :
    KernelBounded a (fun n => P.pair (s.vector (grid n)) (s.vector (grid n))) ∧
    KernelBounded a (fun n => s.dissipation (grid n)) := by
  rcases (canonical_source_critical o s theta ht0 ht1 c).bounds with ⟨m, d, hm, hd, hmass, hdiss⟩
  exact ⟨⟨m, hm, fun n => hmass (grid n)⟩, ⟨d, hd, fun n => hdiss (grid n)⟩⟩

end Fefferman
