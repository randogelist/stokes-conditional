import Fefferman.KernelAlgebra

set_option autoImplicit false

namespace Fefferman

def KernelBounded {I : Type} (a : Analysis) (f : I → a.Scalar) : Prop :=
  ∃ b, a.le a.zero b ∧ ∀ i, a.le (f i) b

def KernelM7 (a : Analysis) (mass : Nat → a.Scalar) : Prop :=
  KernelBounded a (ledgerPrefix a mass)

structure GP509Certificate {a : Analysis} (o : KernelArithmetic a)
    (mass paid : Nat → a.Scalar) : Prop where
  massNonneg : ∀ n, a.le a.zero (mass n)
  paidNonneg : ∀ n, a.le a.zero (paid n)
  step : ∀ n, a.le (KScale o 605 (mass (n+1)))
    (a.add (KScale o 509 (mass n)) (KScale o 605 (paid n)))

/- NSQF20: the 509/605 coefficient is derived from 25/121 and 4/5. -/
theorem kernel_firewall_509 {a : Analysis} (o : KernelArithmetic a)
    (parent internal boundary uv child paid : a.Scalar)
    (split : parent = a.add internal boundary)
    (hi : a.le (KScale o 121 internal) (KScale o 25 parent))
    (hu : a.le (KScale o 5 uv) (KScale o 4 boundary))
    (hc : a.le child (a.add (a.add internal uv) paid)) :
    a.le (KScale o 605 child) (a.add (KScale o 509 parent) (KScale o 605 paid)) := by
  have huv : a.le (KScale o 605 uv) (KScale o 484 boundary) := by
    simpa only [k_scale_comp o] using k_scale_le o 121 hu
  have hid : a.add (KScale o 605 internal) (KScale o 484 boundary) =
      a.add (KScale o 121 internal) (KScale o 484 parent) := by
    rw [split, k_scale_add o]
    exact (congrArg (fun x => a.add x (KScale o 484 boundary))
      (k_scale_nat_add o 121 484 internal)).trans
        (o.addAssoc (KScale o 121 internal) (KScale o 484 internal) (KScale o 484 boundary))
  have hsum : a.le (a.add (KScale o 605 internal) (KScale o 605 uv))
      (KScale o 509 parent) := by
    have hp := o.addLeAdd (o.leRefl (KScale o 605 internal)) huv
    rw [hid] at hp
    have hq := o.leTrans hp (o.addLeAdd hi (o.leRefl (KScale o 484 parent)))
    rw [← k_scale_nat_add o 25 484 parent] at hq
    exact hq
  have hs := k_scale_le o 605 hc
  rw [k_scale_add o, k_scale_add o] at hs
  exact o.leTrans hs (o.addLeAdd hsum (o.leRefl (KScale o 605 paid)))

/- General finite storage telescope, used by both source branches. -/
theorem kernel_storage_telescope {a : Analysis} (o : KernelArithmetic a)
    (state cost paid : Nat → a.Scalar)
    (step : ∀ n, a.le (a.add (state (n+1)) (cost n)) (a.add (state n) (paid n)))
    (n : Nat) : a.le (a.add (state n) (ledgerPrefix a cost n))
      (a.add (state 0) (ledgerPrefix a paid n)) := by
  induction n with
  | zero => exact o.leRefl (a.add (state 0) a.zero)
  | succ n ih =>
    have hs := o.addLeAdd (step n) (o.leRefl (ledgerPrefix a cost n))
    rw [ledger_add_rotate o.toLedgerArithmetic (state (n+1)) (cost n),
      ledger_add_rotate o.toLedgerArithmetic (state n) (paid n)] at hs
    have ht := o.leTrans hs (o.addLeAdd ih (o.leRefl (paid n)))
    rw [o.addAssoc (state (n+1)), o.addAssoc (state 0)] at ht
    exact ht

theorem kernel_gp509_step_gap {a : Analysis} (o : KernelArithmetic a)
    {mass paid : Nat → a.Scalar} (h : GP509Certificate o mass paid) (n : Nat) :
    a.le (a.add (KScale o 605 (mass (n+1))) (KScale o 96 (mass n)))
      (a.add (KScale o 605 (mass n)) (KScale o 605 (paid n))) := by
  have hp := o.addLeAdd (h.step n) (o.leRefl (KScale o 96 (mass n)))
  rw [ledger_add_rotate o.toLedgerArithmetic (KScale o 509 (mass n)),
    ← k_scale_nat_add o 509 96 (mass n)] at hp
  exact hp

theorem kernel_gp509_invariant {a : Analysis} (o : KernelArithmetic a)
    {mass paid : Nat → a.Scalar} (h : GP509Certificate o mass paid) (n : Nat) :
    a.le (a.add (KScale o 605 (mass n)) (KScale o 96 (ledgerPrefix a mass n)))
      (a.add (KScale o 605 (mass 0)) (KScale o 605 (ledgerPrefix a paid n))) := by
  have hp := kernel_storage_telescope o (fun i => KScale o 605 (mass i))
    (fun i => KScale o 96 (mass i)) (fun i => KScale o 605 (paid i))
    (kernel_gp509_step_gap o h) n
  simpa only [KScale, ledger_prefix_scale o.toLedgerArithmetic] using hp

theorem kernel_gp509_prefix {a : Analysis} (o : KernelArithmetic a)
    {mass paid : Nat → a.Scalar} (h : GP509Certificate o mass paid)
    (b : a.Scalar) (hp : ∀ n, a.le (ledgerPrefix a paid n) b) (n : Nat) :
    a.le (ledgerPrefix a mass n) (o.divide (KScale o 605 (a.add (mass 0) b)) (o.nat 96)) := by
  have hn := o.mulNonneg (o.natNonneg 605) (h.massNonneg n)
  have hd := ledger_drop_left o.toLedgerArithmetic (KScale o 96 (ledgerPrefix a mass n)) hn
  have ht := o.leTrans hd (kernel_gp509_invariant o h n)
  have hb := o.leTrans ht (o.addLeAdd (o.leRefl (KScale o 605 (mass 0))) (k_scale_le o 605 (hp n)))
  rw [← k_scale_add o 605] at hb
  exact ledger_unscale o.toLedgerArithmetic (o.natPositive 96 (by decide)) hb

theorem kernel_gp509_m7 {a : Analysis} (o : KernelArithmetic a)
    {mass paid : Nat → a.Scalar} (h : GP509Certificate o mass paid)
    (hp : KernelBounded a (ledgerPrefix a paid)) : KernelM7 a mass := by
  rcases hp with ⟨b, hb, hp⟩
  refine ⟨o.divide (KScale o 605 (a.add (mass 0) b)) (o.nat 96), ?_, kernel_gp509_prefix o h b hp⟩
  exact k_div_nonneg o (o.mulNonneg (o.natNonneg 605) (k_add_nonneg o (h.massNonneg 0) hb))
    (o.natPositive 96 (by decide))

structure KernelPaymentLedger {a : Analysis} (o : KernelArithmetic a)
    (paid credit debit : Nat → a.Scalar) (charge budget : a.Scalar) : Prop where
  chargeNonneg : a.le a.zero charge
  budgetNonneg : a.le a.zero budget
  creditNonneg : ∀ n, a.le a.zero (credit n)
  debitNonneg : ∀ n, a.le a.zero (debit n)
  debitBound : ∀ n, a.le (ledgerPrefix a debit n) budget
  step : ∀ n, a.le (a.add (credit (n+1)) (paid n))
    (a.add (credit n) (a.mul charge (debit n)))

theorem kernel_payment_telescope {a : Analysis} (o : KernelArithmetic a)
    {paid credit debit : Nat → a.Scalar} {charge budget : a.Scalar}
    (h : KernelPaymentLedger o paid credit debit charge budget) (n : Nat) :
    a.le (a.add (credit n) (ledgerPrefix a paid n))
      (a.add (credit 0) (a.mul charge (ledgerPrefix a debit n))) := by
  have hp := kernel_storage_telescope o credit paid (fun i => a.mul charge (debit i)) h.step n
  rw [ledger_prefix_scale o.toLedgerArithmetic] at hp
  exact hp

theorem kernel_payment_bound {a : Analysis} (o : KernelArithmetic a)
    {paid credit debit : Nat → a.Scalar} {charge budget : a.Scalar}
    (h : KernelPaymentLedger o paid credit debit charge budget) :
    KernelBounded a (ledgerPrefix a paid) := by
  refine ⟨a.add (credit 0) (a.mul charge budget),
    k_add_nonneg o (h.creditNonneg 0) (o.mulNonneg h.chargeNonneg h.budgetNonneg), ?_⟩
  intro n
  exact o.leTrans (ledger_drop_left o.toLedgerArithmetic (ledgerPrefix a paid n) (h.creditNonneg n))
    (o.leTrans (kernel_payment_telescope o h n)
      (o.addLeAdd (o.leRefl (credit 0)) (o.mulLeLeft h.chargeNonneg (h.debitBound n))))

theorem kernel_payment_to_m7 {a : Analysis} (o : KernelArithmetic a)
    {mass paid credit debit : Nat → a.Scalar} {charge budget : a.Scalar}
    (hr : GP509Certificate o mass paid)
    (hp : KernelPaymentLedger o paid credit debit charge budget) : KernelM7 a mass :=
  kernel_gp509_m7 o hr (kernel_payment_bound o hp)

noncomputable def CanonicalPaid (a : Analysis) (child internal uv : a.Scalar) : a.Scalar :=
  KPositivePart a (KSub a child (a.add internal uv))

theorem canonical_paid_nonneg {a : Analysis} (o : KernelArithmetic a)
    (child internal uv : a.Scalar) : a.le a.zero (CanonicalPaid a child internal uv) :=
  k_positive_nonneg o _

theorem canonical_paid_routes {a : Analysis} (o : KernelArithmetic a)
    (child internal uv : a.Scalar) :
    a.le child (a.add (a.add internal uv) (CanonicalPaid a child internal uv)) := by
  have h := k_sub_le_to_le_add o (k_le_positive o (KSub a child (a.add internal uv)))
  rw [o.addComm] at h
  exact h

theorem canonical_paid_minimal {a : Analysis} (o : KernelArithmetic a)
    (child internal uv paid : a.Scalar) (hp : a.le a.zero paid)
    (hr : a.le child (a.add (a.add internal uv) paid)) :
    a.le (CanonicalPaid a child internal uv) paid := by
  apply k_positive_le o hp
  apply k_le_add_to_sub_le o
  simpa only [o.addComm] using hr

theorem canonical_boundary_nonnegative {a : Analysis} (o : KernelArithmetic a)
    (parent internal : a.Scalar) (hi0 : a.le a.zero internal)
    (hp0 : a.le a.zero parent)
    (hi : a.le (KScale o 121 internal) (KScale o 25 parent)) :
    a.le a.zero (KSub a parent internal) := by
  have hm : a.le (KScale o 25 parent) (KScale o 121 parent) := by
    have h : a.le (KScale o 25 parent)
        (a.add (KScale o 25 parent) (KScale o 96 parent)) :=
      ledger_drop_right o.toLedgerArithmetic (KScale o 25 parent)
        (o.mulNonneg (o.natNonneg 96) hp0)
    rw [← k_scale_nat_add o 25 96 parent] at h
    exact h
  exact k_sub_nonneg o (k_scale_cancel o 121 (by decide) (o.leTrans hi hm))

theorem canonical_firewall {a : Analysis} (o : KernelArithmetic a)
    (mass internal uv : Nat → a.Scalar)
    (hm : ∀ n, a.le a.zero (mass n))
    (hi : ∀ n, a.le (KScale o 121 (internal n)) (KScale o 25 (mass n)))
    (hu : ∀ n, a.le (KScale o 5 (uv n)) (KScale o 4 (KSub a (mass n) (internal n)))) :
    GP509Certificate o mass (fun n => CanonicalPaid a (mass (n+1)) (internal n) (uv n)) := by
  refine ⟨hm, fun n => canonical_paid_nonneg o _ _ _, ?_⟩
  intro n
  exact kernel_firewall_509 o (mass n) (internal n) (KSub a (mass n) (internal n))
    (uv n) (mass (n+1)) (CanonicalPaid a (mass (n+1)) (internal n) (uv n))
    (k_add_sub o (internal n) (mass n)).symm (hi n) (hu n) (canonical_paid_routes o _ _ _)

end Fefferman
