import Fefferman.KernelCalculus
import Fefferman.KernelCapacity

set_option autoImplicit false

namespace Fefferman

structure KernelSettlementData (a : Analysis) (Time : Type) where
  x : Time → a.Scalar
  xRate : Time → a.Scalar
  dissipation : Time → a.Scalar
  action : Time → a.Scalar
  normSquared : Time → a.Scalar
  debit : Time → a.Scalar
  actionPrimitive : Time → a.Scalar
  debitPrimitive : Time → a.Scalar
  factor : Time → a.Scalar
  c : a.Scalar
  alpha : a.Scalar
  beta : a.Scalar
  gamma : a.Scalar
  floor : a.Scalar
  grid : Nat → Time

def KernelGrowth {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    (s : KernelSettlementData a Time) : a.Scalar := KScale o 2 (a.mul s.c s.beta)

def KernelCharge {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    (s : KernelSettlementData a Time) : a.Scalar := KScale o 2 (a.mul s.c s.gamma)

/- Physical normalized-source inputs from NSPS. The differential growth
   conclusion and the storage/payment conclusions are absent from the fields. -/
structure KernelPhysicalSettlement {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} (C : KernelCalculus a Time) (s : KernelSettlementData a Time) : Prop where
  cNonnegative : a.le a.zero s.c
  betaNonnegative : a.le a.zero s.beta
  gammaNonnegative : a.le a.zero s.gamma
  xNonnegative : ∀ t, a.le a.zero (s.x t)
  dissipationNonnegative : ∀ t, a.le a.zero (s.dissipation t)
  actionNonnegative : ∀ t, a.le a.zero (s.action t)
  debitNonnegative : ∀ t, a.le a.zero (s.debit t)
  normalizedSource : ∀ t, a.le (s.action t) (a.mul s.c (s.normSquared t))
  sourceControl : ∀ t, a.le (s.normSquared t)
    (a.add (a.add (a.mul s.alpha (s.dissipation t)) (a.mul s.beta (s.x t)))
      (a.mul s.gamma (s.debit t)))
  absorption : a.le (KScale o 2 (a.mul s.c s.alpha)) a.one
  energy : ∀ t, a.le (a.add (s.xRate t) (s.dissipation t)) (s.action t)
  xDerivative : C.Derivative s.x s.xRate
  actionIntegral : KernelPrimitive C s.action s.actionPrimitive
  debitIntegral : KernelPrimitive C s.debit s.debitPrimitive
  factorInitial : s.factor C.origin = a.one
  factorDerivative : C.Derivative s.factor
    (fun t => a.neg (a.mul (KernelGrowth o s) (s.factor t)))

/- These are the real integrating factor/time-grid interpretation obligations.
   The source realizes the factor as an exponential. It is not constructed
   from abstract Analysis by this core-only port. -/
structure KernelTimeExhaustion {a : Analysis} {Time : Type}
    (C : KernelCalculus a Time) (s : KernelSettlementData a Time) : Prop where
  floorPositive : a.lt a.zero s.floor
  factorAboveFloor : ∀ t, a.le s.floor (s.factor t)
  factorBelowOne : ∀ t, a.le (s.factor t) a.one
  gridOrigin : s.grid 0 = C.origin
  gridOrdered : ∀ n, C.before (s.grid n) (s.grid (n+1))

def KernelDebitBudget {a : Analysis} {Time : Type} (s : KernelSettlementData a Time) : Prop :=
  KernelBounded a (fun n => s.debitPrimitive (s.grid n))

def KernelPaidCell {a : Analysis} {Time : Type} (s : KernelSettlementData a Time) (n : Nat) : a.Scalar :=
  KSub a (s.actionPrimitive (s.grid (n+1))) (s.actionPrimitive (s.grid n))

theorem kernel_settlement_growth_nonnegative {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} {C : KernelCalculus a Time} {s : KernelSettlementData a Time}
    (h : KernelPhysicalSettlement o C s) : a.le a.zero (KernelGrowth o s) :=
  o.mulNonneg (o.natNonneg 2) (o.mulNonneg h.cNonnegative h.betaNonnegative)

theorem kernel_settlement_charge_nonnegative {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} {C : KernelCalculus a Time} {s : KernelSettlementData a Time}
    (h : KernelPhysicalSettlement o C s) : a.le a.zero (KernelCharge o s) :=
  o.mulNonneg (o.natNonneg 2) (o.mulNonneg h.cNonnegative h.gammaNonnegative)

theorem kernel_normalized_source_growth {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} {C : KernelCalculus a Time} {s : KernelSettlementData a Time}
    (h : KernelPhysicalSettlement o C s) (t : Time) :
    a.le (a.add (s.xRate t) (s.action t))
      (a.add (a.mul (KernelGrowth o s) (s.x t)) (a.mul (KernelCharge o s) (s.debit t))) := by
  have hn := k_scale_le o 2
    (o.leTrans (h.normalizedSource t) (o.mulLeLeft h.cNonnegative (h.sourceControl t)))
  have ha := k_mul_le_right o (h.dissipationNonnegative t) h.absorption
  rw [o.oneMul] at ha
  have hn' : a.le (KScale o 2 (s.action t))
      (a.add (a.add (a.mul (KScale o 2 (a.mul s.c s.alpha)) (s.dissipation t))
        (a.mul (KernelGrowth o s) (s.x t))) (a.mul (KernelCharge o s) (s.debit t))) := by
    simpa only [KScale, KernelGrowth, KernelCharge, o.mulAdd, o.mulAssoc] using hn
  have htwo := o.leTrans hn'
    (o.addLeAdd (o.addLeAdd ha (o.leRefl (a.mul (KernelGrowth o s) (s.x t))))
      (o.leRefl (a.mul (KernelCharge o s) (s.debit t))))
  have he := o.addLeAdd (h.energy t) (o.leRefl (s.action t))
  rw [ledger_add_rotate o.toLedgerArithmetic, ← k_scale_two o] at he
  have hh := o.leTrans he htwo
  apply o.addLeCancelRight (z := s.dissipation t)
  simpa only [o.addAssoc, o.addComm, k_add_left_comm o] using hh

def KernelSuppliedTotal {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    (s : KernelSettlementData a Time) (t : Time) : a.Scalar :=
  KSub a (a.mul (s.factor t) (a.add (s.x t) (s.actionPrimitive t)))
    (a.mul (KernelCharge o s) (s.debitPrimitive t))

def KernelSuppliedRate {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    (s : KernelSettlementData a Time) (t : Time) : a.Scalar :=
  KSub a
    (a.add (a.mul (a.neg (a.mul (KernelGrowth o s) (s.factor t)))
      (a.add (s.x t) (s.actionPrimitive t)))
      (a.mul (s.factor t) (a.add (s.xRate t) (s.action t))))
    (a.mul (KernelCharge o s) (s.debit t))

theorem kernel_supplied_derivative {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} {C : KernelCalculus a Time} {s : KernelSettlementData a Time}
    (h : KernelPhysicalSettlement o C s) :
    C.Derivative (KernelSuppliedTotal o s) (KernelSuppliedRate o s) :=
  C.sub _ _ _ _
    (C.product _ _ _ _ h.factorDerivative (C.add _ _ _ _ h.xDerivative h.actionIntegral.derivative))
    (C.scale _ _ _ h.debitIntegral.derivative)

theorem kernel_supplied_rate_nonpositive {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} {C : KernelCalculus a Time} {s : KernelSettlementData a Time}
    (h : KernelPhysicalSettlement o C s) (e : KernelTimeExhaustion C s) (t : Time) :
    a.le (KernelSuppliedRate o s t) a.zero := by
  have hw := o.leTrans (o.ltToLe e.floorPositive) (e.factorAboveFloor t)
  have hg := kernel_settlement_growth_nonnegative o h
  have hc := kernel_settlement_charge_nonnegative o h
  have hA := kernel_primitive_nonnegative C h.actionIntegral h.actionNonnegative t
  have hx := ledger_drop_right o.toLedgerArithmetic (s.x t) hA
  have hdebit := k_mul_le_right o (o.mulNonneg hc (h.debitNonnegative t)) (e.factorBelowOne t)
  rw [o.oneMul] at hdebit
  have hweight := o.mulLeLeft hw (kernel_normalized_source_growth o h t)
  rw [o.mulAdd (s.factor t) (a.mul (KernelGrowth o s) (s.x t))
    (a.mul (KernelCharge o s) (s.debit t))] at hweight
  have hmain := o.mulLeLeft hw (o.mulLeLeft hg hx)
  have ht := o.leTrans hweight (o.addLeAdd hmain hdebit)
  have ht' : a.le (a.mul (s.factor t) (a.add (s.xRate t) (s.action t)))
      (a.add (a.mul (a.mul (KernelGrowth o s) (s.factor t))
        (a.add (s.x t) (s.actionPrimitive t))) (a.mul (KernelCharge o s) (s.debit t))) := by
    simpa only [o.mulAssoc, o.mulComm, source_mul_interchange o.toSourceArithmetic] using ht
  have hp := k_sub_nonpos o (k_le_add_to_sub_le o ht')
  simpa only [KernelSuppliedRate, KSub, spectral_neg_mul o.toSourceArithmetic,
    o.addAssoc, o.addComm, k_add_left_comm o] using hp

theorem kernel_supplied_storage_bound {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} {C : KernelCalculus a Time} {s : KernelSettlementData a Time}
    (h : KernelPhysicalSettlement o C s) (e : KernelTimeExhaustion C s) (t : Time) :
    a.le (a.mul s.floor (s.actionPrimitive t))
      (a.add (s.x C.origin) (a.mul (KernelCharge o s) (s.debitPrimitive t))) := by
  have ht := C.nonpositive _ _ (kernel_supplied_derivative o h)
    (kernel_supplied_rate_nonpositive o h e) C.origin t (C.originBefore t)
  have hi : KernelSuppliedTotal o s C.origin = s.x C.origin := by
    rw [KernelSuppliedTotal, h.factorInitial, h.actionIntegral.initial,
      h.debitIntegral.initial, o.addZero, o.oneMul, o.mulZero, k_sub_zero o]
  rw [hi] at ht
  have hu := k_sub_le_to_le_add o ht
  have hA := kernel_primitive_nonnegative C h.actionIntegral h.actionNonnegative t
  have hw := o.leTrans (o.ltToLe e.floorPositive) (e.factorAboveFloor t)
  have hl := o.leTrans (k_mul_le_right o hA (e.factorAboveFloor t))
    (o.mulLeLeft hw (ledger_drop_left o.toLedgerArithmetic (s.actionPrimitive t) (h.xNonnegative t)))
  exact o.leTrans hl hu

theorem kernel_paid_cell_nonnegative {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} {C : KernelCalculus a Time} {s : KernelSettlementData a Time}
    (h : KernelPhysicalSettlement o C s) (e : KernelTimeExhaustion C s) (n : Nat) :
    a.le a.zero (KernelPaidCell s n) :=
  k_sub_nonneg o (C.nonnegative _ _ h.actionIntegral.derivative h.actionNonnegative
    _ _ (e.gridOrdered n))

theorem kernel_paid_cells_telescope {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} {C : KernelCalculus a Time} {s : KernelSettlementData a Time}
    (h : KernelPhysicalSettlement o C s) (e : KernelTimeExhaustion C s) (n : Nat) :
    ledgerPrefix a (KernelPaidCell s) n = s.actionPrimitive (s.grid n) := by
  unfold KernelPaidCell
  rw [k_prefix_telescope o (fun k => s.actionPrimitive (s.grid k)) n,
    e.gridOrigin, h.actionIntegral.initial, k_sub_zero o]

theorem kernel_settlement_paid_bound {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} {C : KernelCalculus a Time} {s : KernelSettlementData a Time}
    (h : KernelPhysicalSettlement o C s) (e : KernelTimeExhaustion C s)
    (budget : KernelDebitBudget s) : KernelBounded a (ledgerPrefix a (KernelPaidCell s)) := by
  rcases budget with ⟨b, hb, hbudget⟩
  have hc := kernel_settlement_charge_nonnegative o h
  refine ⟨o.divide (a.add (s.x C.origin) (a.mul (KernelCharge o s) b)) s.floor,
    k_div_nonneg o (k_add_nonneg o (h.xNonnegative C.origin) (o.mulNonneg hc hb)) e.floorPositive, ?_⟩
  intro n
  rw [kernel_paid_cells_telescope o h e]
  exact ledger_unscale o.toLedgerArithmetic e.floorPositive
    (o.leTrans (kernel_supplied_storage_bound o h e (s.grid n))
      (o.addLeAdd (o.leRefl (s.x C.origin)) (o.mulLeLeft hc (hbudget n))))

theorem kernel_settlement_m7 {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} {C : KernelCalculus a Time} {s : KernelSettlementData a Time}
    {mass : Nat → a.Scalar} (renewal : GP509Certificate o mass (KernelPaidCell s))
    (h : KernelPhysicalSettlement o C s) (e : KernelTimeExhaustion C s)
    (budget : KernelDebitBudget s) : KernelM7 a mass :=
  kernel_gp509_m7 o renewal (kernel_settlement_paid_bound o h e budget)

end Fefferman
