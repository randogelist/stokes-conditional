import Fefferman.KernelCritical

set_option autoImplicit false

namespace Fefferman

/- Ordinary differential calculus on one time domain. The physical real-time
   interpretation is explicit; no NSE rate inequality is a calculus field. -/
structure KernelCalculus (a : Analysis) (Time : Type) where
  origin : Time
  before : Time → Time → Prop
  beforeRefl : ∀ t, before t t
  originBefore : ∀ t, before origin t
  Derivative : (Time → a.Scalar) → (Time → a.Scalar) → Prop
  constant : ∀ c, Derivative (fun _ => c) (fun _ => a.zero)
  add : ∀ F G f g, Derivative F f → Derivative G g →
    Derivative (fun t => a.add (F t) (G t)) (fun t => a.add (f t) (g t))
  sub : ∀ F G f g, Derivative F f → Derivative G g →
    Derivative (fun t => KSub a (F t) (G t)) (fun t => KSub a (f t) (g t))
  scale : ∀ c F f, Derivative F f →
    Derivative (fun t => a.mul c (F t)) (fun t => a.mul c (f t))
  product : ∀ F G f g, Derivative F f → Derivative G g →
    Derivative (fun t => a.mul (F t) (G t))
      (fun t => a.add (a.mul (f t) (G t)) (a.mul (F t) (g t)))
  nonnegative : ∀ F f, Derivative F f → (∀ t, a.le a.zero (f t)) →
    ∀ s t, before s t → a.le (F s) (F t)
  nonpositive : ∀ F f, Derivative F f → (∀ t, a.le (f t) a.zero) →
    ∀ s t, before s t → a.le (F t) (F s)

structure KernelPrimitive {a : Analysis} {Time : Type} (C : KernelCalculus a Time)
    (rate value : Time → a.Scalar) : Prop where
  initial : value C.origin = a.zero
  derivative : C.Derivative value rate

theorem kernel_primitive_scale {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    (C : KernelCalculus a Time) (c : a.Scalar) {rate value : Time → a.Scalar}
    (h : KernelPrimitive C rate value) :
    KernelPrimitive C (fun t => a.mul c (rate t)) (fun t => a.mul c (value t)) := by
  refine ⟨?_, C.scale c value rate h.derivative⟩
  rw [h.initial, o.mulZero]

theorem kernel_primitive_sub {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    (C : KernelCalculus a Time) {f g F G : Time → a.Scalar}
    (hF : KernelPrimitive C f F) (hG : KernelPrimitive C g G) :
    KernelPrimitive C (fun t => KSub a (f t) (g t)) (fun t => KSub a (F t) (G t)) := by
  refine ⟨?_, C.sub F G f g hF.derivative hG.derivative⟩
  rw [hF.initial, hG.initial, k_sub_self o]

theorem kernel_primitive_nonnegative {a : Analysis} {Time : Type}
    (C : KernelCalculus a Time) {f F : Time → a.Scalar}
    (h : KernelPrimitive C f F) (hn : ∀ t, a.le a.zero (f t)) : ∀ t, a.le a.zero (F t) := by
  intro t
  have hp := C.nonnegative F f h.derivative hn C.origin t (C.originBefore t)
  rw [h.initial] at hp
  exact hp

/- NSCT comparison and the source integrated balance from derivative data. -/
theorem kernel_integrated_balance {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    (C : KernelCalculus a Time) (F f G g H h : Time → a.Scalar)
    (hF : C.Derivative F f) (hG : KernelPrimitive C g G) (hH : KernelPrimitive C h H)
    (rate : ∀ t, a.le (a.add (f t) (g t)) (h t)) :
    ∀ t, a.le (a.add (F t) (G t)) (a.add (F C.origin) (H t)) := by
  have deriv := C.sub (fun t => a.add (F t) (G t)) H
    (fun t => a.add (f t) (g t)) h (C.add F G f g hF hG.derivative) hH.derivative
  intro t
  have hp := C.nonpositive _ _ deriv (fun s => k_sub_nonpos o (rate s))
    C.origin t (C.originBefore t)
  change a.le (KSub a (a.add (F t) (G t)) (H t))
    (KSub a (a.add (F C.origin) (G C.origin)) (H C.origin)) at hp
  rw [hG.initial, hH.initial, o.addZero, k_sub_zero o] at hp
  exact k_sub_le_to_le_add o hp

theorem kernel_primitive_comparison {a : Analysis} (o : KernelArithmetic a) {Time : Type}
    (C : KernelCalculus a Time) {f g F G : Time → a.Scalar}
    (hF : KernelPrimitive C f F) (hG : KernelPrimitive C g G)
    (h : ∀ t, a.le (f t) (g t)) : ∀ t, a.le (F t) (G t) := by
  have hd := kernel_primitive_sub o C hF hG
  intro t
  have hp := C.nonpositive _ _ hd.derivative (fun s => k_sub_nonpos o (h s))
    C.origin t (C.originBefore t)
  rw [hd.initial] at hp
  exact k_le_of_sub_nonpos o hp

/- Unpaid source path. No signed-production budget or critical bound is a
   field. The source rates below construct its two integrated inequalities. -/
structure KernelSourcePath {a : Analysis} (P : SourcePairing a) where
  Time : Type
  origin : Time
  vector : Time → P.Carrier
  storage : Time → a.Scalar
  source : Time → a.Scalar
  dissipation : Time → a.Scalar
  production : Time → a.Scalar
  nu : a.Scalar
  nuPositive : a.lt a.zero nu
  massNonnegative : ∀ t, a.le a.zero (P.pair (vector t) (vector t))
  storageNonnegative : ∀ t, a.le a.zero (storage t)
  dissipationNonnegative : ∀ t, a.le a.zero (dissipation t)
  sourceBalance : ∀ t, a.le (a.add (storage t) (source t))
    (a.add (storage origin) (production t))
  criticalBalance : ∀ t, a.le
    (a.add (a.mul nu (P.pair (vector t) (vector t))) (a.mul (a.mul nu nu) (dissipation t)))
    (a.add (a.mul nu (P.pair (vector origin) (vector origin))) (source t))
  sourceInitial : source origin = a.zero
  dissipationInitial : dissipation origin = a.zero
  productionInitial : production origin = a.zero
  grid : Nat → Time
  gridOrigin : grid 0 = origin
  sourceGridMonotone : ∀ n, a.le (source (grid n)) (source (grid (n+1)))

structure KernelSourceRates {a : Analysis} (o : KernelArithmetic a) (P : SourcePairing a)
    (Time : Type) (C : KernelCalculus a Time) where
  vector : Time → P.Carrier
  storage : Time → a.Scalar
  source : Time → a.Scalar
  dissipation : Time → a.Scalar
  production : Time → a.Scalar
  massRate : Time → a.Scalar
  sourceRate : Time → a.Scalar
  dissipationRate : Time → a.Scalar
  productionRate : Time → a.Scalar
  damping : Time → a.Scalar
  nu : a.Scalar
  nuPositive : a.lt a.zero nu
  massNonnegative : ∀ t, a.le a.zero (P.pair (vector t) (vector t))
  storageNonnegative : ∀ t, a.le a.zero (storage t)
  sourceRateNonnegative : ∀ t, a.le a.zero (sourceRate t)
  dissipationRateNonnegative : ∀ t, a.le a.zero (dissipationRate t)
  massDerivative : C.Derivative (fun t => P.pair (vector t) (vector t)) massRate
  storageDerivative : C.Derivative storage (fun t => KSub a (productionRate t) (damping t))
  sourcePrimitive : KernelPrimitive C sourceRate source
  dissipationPrimitive : KernelPrimitive C dissipationRate dissipation
  productionPrimitive : KernelPrimitive C productionRate production
  dampingFundsSource : ∀ t, a.le (sourceRate t) (damping t)
  criticalAbsorption : ∀ t, a.le
    (a.add (a.mul nu (massRate t)) (a.mul (a.mul nu nu) (dissipationRate t))) (sourceRate t)
  grid : Nat → Time
  gridOrigin : grid 0 = C.origin
  gridOrdered : ∀ n, C.before (grid n) (grid (n+1))

theorem kernel_source_rates_integrate {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {Time : Type} {C : KernelCalculus a Time}
    (s : KernelSourceRates o P Time C) : ∀ t,
    a.le (a.add (s.storage t) (s.source t)) (a.add (s.storage C.origin) (s.production t)) :=
  kernel_integrated_balance o C _ _ _ _ _ _ s.storageDerivative
    s.sourcePrimitive s.productionPrimitive (fun t => k_sub_add_le o (s.productionRate t) (s.dampingFundsSource t))

theorem kernel_source_rates_critical {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {Time : Type} {C : KernelCalculus a Time}
    (s : KernelSourceRates o P Time C) : ∀ t, a.le
    (a.add (a.mul s.nu (P.pair (s.vector t) (s.vector t)))
      (a.mul (a.mul s.nu s.nu) (s.dissipation t)))
    (a.add (a.mul s.nu (P.pair (s.vector C.origin) (s.vector C.origin))) (s.source t)) :=
  kernel_integrated_balance o C _ _ _ _ _ _
    (C.scale s.nu _ _ s.massDerivative)
    (kernel_primitive_scale o C (a.mul s.nu s.nu) s.dissipationPrimitive)
    s.sourcePrimitive s.criticalAbsorption

def kernel_source_path_of_rates {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} {Time : Type} {C : KernelCalculus a Time}
    (s : KernelSourceRates o P Time C) : KernelSourcePath P where
  Time := Time
  origin := C.origin
  vector := s.vector
  storage := s.storage
  source := s.source
  dissipation := s.dissipation
  production := s.production
  nu := s.nu
  nuPositive := s.nuPositive
  massNonnegative := s.massNonnegative
  storageNonnegative := s.storageNonnegative
  dissipationNonnegative := kernel_primitive_nonnegative C s.dissipationPrimitive s.dissipationRateNonnegative
  sourceBalance := kernel_source_rates_integrate o s
  criticalBalance := kernel_source_rates_critical o s
  sourceInitial := s.sourcePrimitive.initial
  dissipationInitial := s.dissipationPrimitive.initial
  productionInitial := s.productionPrimitive.initial
  grid := s.grid
  gridOrigin := s.gridOrigin
  sourceGridMonotone := fun n => C.nonnegative _ _ s.sourcePrimitive.derivative
    s.sourceRateNonnegative _ _ (s.gridOrdered n)

theorem kernel_source_coupled_balance {a : Analysis} (o : KernelArithmetic a)
    {P : SourcePairing a} (s : KernelSourcePath P) (t : s.Time) :
    a.le (a.add (a.add (a.mul s.nu (P.pair (s.vector t) (s.vector t))) (s.storage t))
      (a.mul (a.mul s.nu s.nu) (s.dissipation t)))
    (a.add (a.add (a.mul s.nu (P.pair (s.vector s.origin) (s.vector s.origin))) (s.storage s.origin))
      (s.production t)) := by
  have hc := o.addLeAdd (s.criticalBalance t) (o.leRefl (s.storage t))
  rw [ledger_add_rotate o.toLedgerArithmetic _ _ (s.storage t),
    o.addAssoc _ (s.source t) (s.storage t), o.addComm (s.source t) (s.storage t)] at hc
  have hp := o.leTrans hc (o.addLeAdd
    (o.leRefl (a.mul s.nu (P.pair (s.vector s.origin) (s.vector s.origin)))) (s.sourceBalance t))
  rw [← o.addAssoc] at hp
  exact hp

end Fefferman
