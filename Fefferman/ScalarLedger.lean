import Fefferman.Analysis

set_option autoImplicit false

namespace Fefferman

/- Ordinary scalar algebra/order laws needed by the port. No NSE estimate is
   a field of this record. A real-analysis interpretation must supply them. -/
structure LedgerArithmetic (a : Analysis) where
  divide : a.Scalar → a.Scalar → a.Scalar
  leRefl : ∀ x, a.le x x
  leTrans : ∀ {x y z}, a.le x y → a.le y z → a.le x z
  ltToLe : ∀ {x y}, a.lt x y → a.le x y
  addComm : ∀ x y, a.add x y = a.add y x
  addAssoc : ∀ x y z, a.add (a.add x y) z = a.add x (a.add y z)
  addZero : ∀ x, a.add x a.zero = x
  addNeg : ∀ x, a.add x (a.neg x) = a.zero
  addLeAdd : ∀ {x y z w}, a.le x y → a.le z w →
    a.le (a.add x z) (a.add y w)
  addLeCancelRight : ∀ {x y z}, a.le (a.add x z) (a.add y z) → a.le x y
  mulZero : ∀ x, a.mul x a.zero = a.zero
  oneMul : ∀ x, a.mul a.one x = x
  mulAdd : ∀ x y z, a.mul x (a.add y z) = a.add (a.mul x y) (a.mul x z)
  addMul : ∀ x y z, a.mul (a.add x y) z = a.add (a.mul x z) (a.mul y z)
  mulNonneg : ∀ {x y}, a.le a.zero x → a.le a.zero y → a.le a.zero (a.mul x y)
  mulLeLeft : ∀ {c x y}, a.le a.zero c → a.le x y → a.le (a.mul c x) (a.mul c y)
  mulLeCancelLeft : ∀ {c x y}, a.lt a.zero c →
    a.le (a.mul c x) (a.mul c y) → a.le x y
  mulDivide : ∀ c b, a.lt a.zero c → a.mul c (divide b c) = b
  subPositive : ∀ {x y}, a.lt x y → a.lt a.zero (a.add y (a.neg x))

def ledgerBounded {I : Type} (a : Analysis) (value : I → a.Scalar) : Prop :=
  ∃ bound, ∀ i, a.le (value i) bound

def ledgerPrefix (a : Analysis) (value : Nat → a.Scalar) : Nat → a.Scalar
  | 0 => a.zero
  | n + 1 => a.add (ledgerPrefix a value n) (value n)

structure FullLedgerReadout {I : Type} (a : Analysis)
    (finite : I → a.Scalar) (full : a.Scalar) : Prop where
  upper : ∀ i, a.le (finite i) full
  least : ∀ b, (∀ i, a.le (finite i) b) → a.le full b

theorem ledger_zero_add {a : Analysis} (o : LedgerArithmetic a) (x : a.Scalar) :
    a.add a.zero x = x :=
  (o.addComm a.zero x).trans (o.addZero x)

theorem ledger_neg_add {a : Analysis} (o : LedgerArithmetic a) (x : a.Scalar) :
    a.add (a.neg x) x = a.zero :=
  (o.addComm (a.neg x) x).trans (o.addNeg x)

theorem ledger_add_rotate {a : Analysis} (o : LedgerArithmetic a)
    (x y z : a.Scalar) : a.add (a.add x y) z = a.add (a.add x z) y := by
  rw [o.addAssoc x y z, o.addComm y z, ← o.addAssoc x z y]

theorem ledger_drop_right {a : Analysis} (o : LedgerArithmetic a)
    (x : a.Scalar) {y : a.Scalar} (hy : a.le a.zero y) :
    a.le x (a.add x y) := by
  have h := o.addLeAdd (o.leRefl x) hy
  rw [o.addZero x] at h
  exact h

theorem ledger_drop_left {a : Analysis} (o : LedgerArithmetic a)
    {x : a.Scalar} (y : a.Scalar) (hx : a.le a.zero x) :
    a.le y (a.add x y) := by
  have h := ledger_drop_right o y hx
  rw [o.addComm y x] at h
  exact h

theorem ledger_unscale {a : Analysis} (o : LedgerArithmetic a)
    {c x bound : a.Scalar} (hc : a.lt a.zero c)
    (h : a.le (a.mul c x) bound) : a.le x (o.divide bound c) := by
  apply o.mulLeCancelLeft hc
  rw [o.mulDivide c bound hc]
  exact h

theorem ledger_retention_split {a : Analysis} (o : LedgerArithmetic a)
    (gamma value : a.Scalar) :
    a.add (a.mul (a.add a.one (a.neg gamma)) value) (a.mul gamma value) = value := by
  rw [← o.addMul (a.add a.one (a.neg gamma)) gamma value]
  rw [o.addAssoc a.one (a.neg gamma) gamma, ledger_neg_add o gamma]
  rw [o.addZero a.one, o.oneMul value]

theorem ledger_strict_absorption {a : Analysis} (o : LedgerArithmetic a)
    {gamma value budget : a.Scalar} (hg : a.lt gamma a.one)
    (h : a.le value (a.add (a.mul gamma value) budget)) :
    a.le value (o.divide budget (a.add a.one (a.neg gamma))) := by
  have hs : a.le
      (a.add (a.mul (a.add a.one (a.neg gamma)) value) (a.mul gamma value))
      (a.add budget (a.mul gamma value)) := by
    rw [ledger_retention_split o gamma value, o.addComm budget (a.mul gamma value)]
    exact h
  exact ledger_unscale o (o.subPositive hg) (o.addLeCancelRight hs)

/- Exact storage + paid low/heat terms + strict high-output absorption. -/
theorem ledger_storage_bound {a : Analysis} (o : LedgerArithmetic a)
    (storage initial crowd low high heat seed lowMax highMax heatMax gamma : a.Scalar)
    (hstorage : a.le a.zero storage) (hseed : a.le initial seed)
    (hbalance : a.add storage crowd = a.add (a.add (a.add initial low) high) heat)
    (hlow : a.le low lowMax) (hheat : a.le heat heatMax)
    (hhigh : a.le high (a.add (a.mul gamma crowd) highMax))
    (hgamma : a.lt gamma a.one) :
    a.le crowd (o.divide (a.add (a.add (a.add seed lowMax) highMax) heatMax)
      (a.add a.one (a.neg gamma))) := by
  have hdrop := ledger_drop_left o crowd hstorage
  rw [hbalance] at hdrop
  have hpay := o.addLeAdd (o.addLeAdd (o.addLeAdd hseed hlow) hhigh) hheat
  have h := o.leTrans hdrop hpay
  have hreorder :
      a.add (a.add (a.add seed lowMax) (a.add (a.mul gamma crowd) highMax)) heatMax =
      a.add (a.mul gamma crowd) (a.add (a.add (a.add seed lowMax) highMax) heatMax) := by
    rw [← o.addAssoc (a.add seed lowMax) (a.mul gamma crowd) highMax]
    rw [ledger_add_rotate o (a.add seed lowMax) (a.mul gamma crowd) highMax]
    rw [ledger_add_rotate o (a.add (a.add seed lowMax) highMax) (a.mul gamma crowd) heatMax]
    exact o.addComm (a.add (a.add (a.add seed lowMax) highMax) heatMax) (a.mul gamma crowd)
  rw [hreorder] at h
  exact ledger_strict_absorption o hgamma h

theorem ledger_prefix_scale {a : Analysis} (o : LedgerArithmetic a)
    (c : a.Scalar) (mass : Nat → a.Scalar) (n : Nat) :
    ledgerPrefix a (fun k => a.mul c (mass k)) n = a.mul c (ledgerPrefix a mass n) := by
  induction n with
  | zero => exact (o.mulZero c).symm
  | succ n ih =>
    change a.add (ledgerPrefix a (fun k => a.mul c (mass k)) n) (a.mul c (mass n)) =
      a.mul c (a.add (ledgerPrefix a mass n) (mass n))
    rw [ih, o.mulAdd c (ledgerPrefix a mass n) (mass n)]

theorem ledger_renewal_step_from_retention {a : Analysis} (o : LedgerArithmetic a)
    (gamma : a.Scalar) (mass paid : Nat → a.Scalar)
    (step : ∀ n, a.le (mass (n + 1)) (a.add (a.mul gamma (mass n)) (paid n))) :
    ∀ n, a.le (a.add (mass (n + 1)) (a.mul (a.add a.one (a.neg gamma)) (mass n)))
      (a.add (mass n) (paid n)) := by
  intro n
  have h := o.addLeAdd (step n) (o.leRefl (a.mul (a.add a.one (a.neg gamma)) (mass n)))
  rw [ledger_add_rotate o (a.mul gamma (mass n)) (paid n)
    (a.mul (a.add a.one (a.neg gamma)) (mass n))] at h
  rw [o.addComm (a.mul gamma (mass n)) (a.mul (a.add a.one (a.neg gamma)) (mass n)),
    ledger_retention_split o gamma (mass n)] at h
  exact h

/- Denominator-free renewal invariant. For GP509 the retained gap is 96/605. -/
theorem ledger_renewal_invariant {a : Analysis} (o : LedgerArithmetic a)
    (gap : a.Scalar) (mass paid : Nat → a.Scalar)
    (step : ∀ n, a.le (a.add (mass (n + 1)) (a.mul gap (mass n)))
      (a.add (mass n) (paid n))) (n : Nat) :
    a.le (a.add (mass n) (ledgerPrefix a (fun k => a.mul gap (mass k)) n))
      (a.add (mass 0) (ledgerPrefix a paid n)) := by
  induction n with
  | zero => exact o.leRefl (a.add (mass 0) a.zero)
  | succ n ih =>
    have hs := o.addLeAdd (step n)
      (o.leRefl (ledgerPrefix a (fun k => a.mul gap (mass k)) n))
    rw [ledger_add_rotate o (mass (n + 1)) (a.mul gap (mass n))
      (ledgerPrefix a (fun k => a.mul gap (mass k)) n)] at hs
    rw [ledger_add_rotate o (mass n) (paid n)
      (ledgerPrefix a (fun k => a.mul gap (mass k)) n)] at hs
    have h := o.leTrans hs (o.addLeAdd ih (o.leRefl (paid n)))
    rw [o.addAssoc (mass (n + 1)) (ledgerPrefix a (fun k => a.mul gap (mass k)) n)
      (a.mul gap (mass n)), o.addAssoc (mass 0) (ledgerPrefix a paid n) (paid n)] at h
    exact h

theorem ledger_renewal_prefix_bound {a : Analysis} (o : LedgerArithmetic a)
    (gap : a.Scalar) (mass paid : Nat → a.Scalar) (seed paidMax : a.Scalar)
    (hgap : a.lt a.zero gap) (hmass : ∀ n, a.le a.zero (mass n))
    (hseed : a.le (mass 0) seed)
    (step : ∀ n, a.le (a.add (mass (n + 1)) (a.mul gap (mass n)))
      (a.add (mass n) (paid n)))
    (hpaid : ∀ n, a.le (ledgerPrefix a paid n) paidMax) (n : Nat) :
    a.le (ledgerPrefix a mass n) (o.divide (a.add seed paidMax) gap) := by
  have hdrop := ledger_drop_left o
    (ledgerPrefix a (fun k => a.mul gap (mass k)) n) (hmass n)
  have h := o.leTrans hdrop (ledger_renewal_invariant o gap mass paid step n)
  have hb := o.leTrans h (o.addLeAdd hseed (hpaid n))
  rw [ledger_prefix_scale o gap mass n] at hb
  exact ledger_unscale o hgap hb

theorem ledger_action_from_cofinal_samples {a : Analysis} (o : LedgerArithmetic a)
    {Time : Type} (before : Time → Time → Prop) (cut : Nat → Time)
    (action : Time → a.Scalar) (prefixValue : Nat → a.Scalar) (bound : a.Scalar)
    (cofinal : ∀ t, ∃ n, before t (cut n))
    (monotone : ∀ t s, before t s → a.le (action t) (action s))
    (samples : ∀ n, a.le (action (cut n)) (prefixValue n))
    (bounded : ∀ n, a.le (prefixValue n) bound) : ∀ t, a.le (action t) bound := by
  intro t
  cases cofinal t with
  | intro n hn => exact o.leTrans (monotone t (cut n) hn) (o.leTrans (samples n) (bounded n))

theorem ledger_forced_energy_bound {a : Analysis} (o : LedgerArithmetic a)
    (mass dissipation initial internal forcing internalMax forceMax epsilon : a.Scalar)
    (he : a.lt a.zero epsilon) (hm : a.le a.zero mass) (hd : a.le a.zero dissipation)
    (hb : a.le (a.add mass (a.mul epsilon dissipation))
      (a.add initial (a.add internal forcing)))
    (hi : a.le internal internalMax) (hf : a.le forcing forceMax) :
    a.le mass (a.add initial (a.add internalMax forceMax)) ∧
    a.le dissipation (o.divide (a.add initial (a.add internalMax forceMax)) epsilon) := by
  have h := o.leTrans hb (o.addLeAdd (o.leRefl initial) (o.addLeAdd hi hf))
  constructor
  · exact o.leTrans (ledger_drop_right o mass (o.mulNonneg (o.ltToLe he) hd)) h
  · exact ledger_unscale o he (o.leTrans (ledger_drop_left o (a.mul epsilon dissipation) hm) h)

theorem ledger_full_readout_bound {a : Analysis} {I Time : Type}
    (finite : I → Time → a.Scalar) (full : Time → a.Scalar) (bound : a.Scalar)
    (readout : ∀ t, FullLedgerReadout a (fun i => finite i t) (full t))
    (uniform : ∀ i t, a.le (finite i t) bound) : ∀ t, a.le (full t) bound :=
  fun t => (readout t).least bound (fun i => uniform i t)

theorem ledger_net_work_excludes_mass_bound {a : Analysis} (o : LedgerArithmetic a)
    {Time : Type} (initial : a.Scalar) (mass work : Time → a.Scalar)
    (balance : ∀ t, mass t = a.add initial (work t))
    (unbounded : ∀ bound, ∃ t, ¬ a.le (work t) bound) : ¬ ledgerBounded a mass := by
  intro h
  cases h with
  | intro bound hbound =>
    cases unbounded (a.add bound (a.neg initial)) with
    | intro t ht =>
      have hb := o.addLeAdd (hbound t) (o.leRefl (a.neg initial))
      rw [balance t, ledger_add_rotate o initial (work t) (a.neg initial),
        o.addNeg initial, ledger_zero_add o (work t)] at hb
      exact ht hb

end Fefferman
