import Fefferman.KernelRenewal

set_option autoImplicit false

namespace Fefferman

def KernelEffectiveViscosity (a : Analysis) (nu sigma : a.Scalar) : a.Scalar :=
  a.mul (KSub a a.one sigma) nu

structure KernelCriticalBalance {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    (nu sigma initial : a.Scalar) (mass diss action : Time → a.Scalar) : Prop where
  nuPositive : a.lt a.zero nu
  sigmaNonnegative : a.le a.zero sigma
  sigmaBelowOne : a.lt sigma a.one
  initialNonnegative : a.le a.zero initial
  massNonnegative : ∀ t, a.le a.zero (mass t)
  dissNonnegative : ∀ t, a.le a.zero (diss t)
  actionNonnegative : ∀ t, a.le a.zero (action t)
  balance : ∀ t, a.le (a.add (mass t) (a.mul (KernelEffectiveViscosity a nu sigma) (diss t)))
    (a.add initial (action t))

structure KernelCriticalControl (a : Analysis) {Time : Type}
    (mass diss : Time → a.Scalar) : Prop where
  bounds : ∃ m d, a.le a.zero m ∧ a.le a.zero d ∧
    (∀ t, a.le (mass t) m) ∧ (∀ t, a.le (diss t) d)

def KernelActionRealization (a : Analysis) {Time : Type}
    (mass : Nat → a.Scalar) (action : Time → a.Scalar) : Prop :=
  ∀ t, ∃ n, a.le (action t) (ledgerPrefix a mass n)

theorem kernel_m7_bounds_action {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    {mass : Nat → a.Scalar} {action : Time → a.Scalar}
    (hm : KernelM7 a mass) (hr : KernelActionRealization a mass action) :
    KernelBounded a action := by
  rcases hm with ⟨b, hb, hp⟩
  refine ⟨b, hb, ?_⟩
  intro t
  rcases hr t with ⟨n, hn⟩
  exact o.leTrans hn (hp n)

theorem kernel_effective_viscosity_positive {a : Analysis} (o : KernelArithmetic a)
    {nu sigma : a.Scalar} (hn : a.lt a.zero nu) (hs : a.lt sigma a.one) :
    a.lt a.zero (KernelEffectiveViscosity a nu sigma) :=
  o.mulPositive (o.subPositive hs) hn

theorem kernel_action_to_critical {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    {nu sigma initial : a.Scalar} {mass diss action : Time → a.Scalar}
    (h : KernelCriticalBalance o nu sigma initial mass diss action)
    (ha : KernelBounded a action) : KernelCriticalControl a mass diss := by
  rcases ha with ⟨b, hb, hab⟩
  have he := kernel_effective_viscosity_positive o h.nuPositive h.sigmaBelowOne
  have hk := k_add_nonneg o h.initialNonnegative hb
  refine ⟨⟨a.add initial b, o.divide (a.add initial b) (KernelEffectiveViscosity a nu sigma),
    hk, k_div_nonneg o hk he, ?_, ?_⟩⟩
  · intro t
    exact o.leTrans (ledger_drop_right o.toLedgerArithmetic (mass t)
      (o.mulNonneg (o.ltToLe he) (h.dissNonnegative t)))
      (o.leTrans (h.balance t) (o.addLeAdd (o.leRefl initial) (hab t)))
  · intro t
    apply ledger_unscale o.toLedgerArithmetic he
    exact o.leTrans (ledger_drop_left o.toLedgerArithmetic
      (a.mul (KernelEffectiveViscosity a nu sigma) (diss t)) (h.massNonnegative t))
      (o.leTrans (h.balance t) (o.addLeAdd (o.leRefl initial) (hab t)))

theorem kernel_m7_to_critical {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    {seq : Nat → a.Scalar} {nu sigma initial : a.Scalar}
    {mass diss action : Time → a.Scalar} (hm : KernelM7 a seq)
    (hr : KernelActionRealization a seq action)
    (hb : KernelCriticalBalance o nu sigma initial mass diss action) :
    KernelCriticalControl a mass diss :=
  kernel_action_to_critical o hb (kernel_m7_bounds_action o hm hr)

theorem kernel_critical_split {a : Analysis} {Time : Type}
    {mass diss : Time → a.Scalar} (h : KernelCriticalControl a mass diss) :
    KernelBounded a mass ∧ KernelBounded a diss := by
  rcases h.bounds with ⟨m, d, hm, hd, hmass, hdiss⟩
  exact ⟨⟨m, hm, hmass⟩, ⟨d, hd, hdiss⟩⟩

structure KernelSerrinInterpolation (a : Analysis) {Time : Type}
    (constant : a.Scalar) (mass diss serrin : Time → a.Scalar) : Prop where
  constantNonnegative : a.le a.zero constant
  serrinNonnegative : ∀ t, a.le a.zero (serrin t)
  interpolation : ∀ m, a.le a.zero m → (∀ t, a.le (mass t) m) →
    ∀ t, a.le (serrin t) (a.mul (a.mul constant m) (diss t))

theorem kernel_critical_to_serrin {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    {constant : a.Scalar} {mass diss serrin : Time → a.Scalar}
    (hc : KernelCriticalControl a mass diss)
    (hi : KernelSerrinInterpolation a constant mass diss serrin) :
    KernelBounded a serrin := by
  rcases hc.bounds with ⟨m, d, hm, hd, hmass, hdiss⟩
  have hcm := o.mulNonneg hi.constantNonnegative hm
  refine ⟨a.mul (a.mul constant m) d, o.mulNonneg hcm hd, ?_⟩
  intro t
  exact o.leTrans (hi.interpolation m hm hmass t) (o.mulLeLeft hcm (hdiss t))

theorem kernel_renewal_payment_to_serrin {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    {seq paid credit debit : Nat → a.Scalar} {charge budget nu sigma initial constant : a.Scalar}
    {mass diss action serrin : Time → a.Scalar}
    (hr : GP509Certificate o seq paid)
    (hp : KernelPaymentLedger o paid credit debit charge budget)
    (ha : KernelActionRealization a seq action)
    (hb : KernelCriticalBalance o nu sigma initial mass diss action)
    (hi : KernelSerrinInterpolation a constant mass diss serrin) : KernelBounded a serrin :=
  kernel_critical_to_serrin o (kernel_m7_to_critical o (kernel_payment_to_m7 o hr hp) ha hb) hi

/- A single bound is kept across the entire cutoff family. -/
theorem kernel_uniform_family_serrin {a : Analysis} (o : KernelArithmetic a) {Index Time : Type}
    (epsilon budget constant : a.Scalar)
    (mass diss serrin : Index → Time → a.Scalar)
    (he : a.lt a.zero epsilon) (hb : a.le a.zero budget) (hc : a.le a.zero constant)
    (hm : ∀ i t, a.le a.zero (mass i t)) (hd : ∀ i t, a.le a.zero (diss i t))
    (balance : ∀ i t, a.le (a.add (mass i t) (a.mul epsilon (diss i t))) budget)
    (interp : ∀ i m, a.le a.zero m → (∀ t, a.le (mass i t) m) →
      ∀ t, a.le (serrin i t) (a.mul (a.mul constant m) (diss i t))) :
    ∃ bound, a.le a.zero bound ∧ ∀ i t, a.le (serrin i t) bound := by
  have hmass : ∀ i t, a.le (mass i t) budget := fun i t =>
    o.leTrans (ledger_drop_right o.toLedgerArithmetic (mass i t)
      (o.mulNonneg (o.ltToLe he) (hd i t))) (balance i t)
  have hdiss : ∀ i t, a.le (diss i t) (o.divide budget epsilon) := fun i t =>
    ledger_unscale o.toLedgerArithmetic he
      (o.leTrans (ledger_drop_left o.toLedgerArithmetic (a.mul epsilon (diss i t)) (hm i t)) (balance i t))
  have hcb := o.mulNonneg hc hb
  refine ⟨a.mul (a.mul constant budget) (o.divide budget epsilon),
    o.mulNonneg hcb (k_div_nonneg o hb he), ?_⟩
  intro i t
  exact o.leTrans (interp i budget hb (hmass i) t) (o.mulLeLeft hcb (hdiss i t))

end Fefferman
