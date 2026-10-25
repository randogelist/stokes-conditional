import Fefferman.KernelCapacity
import Fefferman.KernelCalculus

set_option autoImplicit false

namespace Fefferman

/- The SAME packet measure scales source, current and detector capacity.
   Their finite Young bound is derived by square completion, not supplied. -/
theorem kernel_weighted_packet_young {a : Analysis} (o : KernelArithmetic a)
    (measure source detector : Nat → a.Scalar) (n : Nat) (nu : a.Scalar)
    (hm : ∀ i, i < n → a.le a.zero (measure i)) :
    a.le (KScale o 2 (a.mul nu (KernelWeightedDot a measure source detector n)))
      (a.add (KernelWeightedDot a measure source source n)
        (a.mul (a.mul nu nu) (KernelWeightedDot a measure detector detector n))) := by
  have hp := k_prefix_mono o n _ _ (fun i hi =>
    o.mulLeLeft (hm i hi) (kernel_pointwise_dual_bound o (source i) (detector i) nu))
  rw [kernel_weighted_dual_identity o] at hp
  exact k_sub_le_to_le_add o hp

theorem kernel_weighted_packet_absorption {a : Analysis} (o : KernelArithmetic a)
    (measure source detector : Nat → a.Scalar) (n : Nat) (nu dissipation massRate : a.Scalar)
    (hm : ∀ i, i < n → a.le a.zero (measure i))
    (capacity : a.le (KernelWeightedDot a measure detector detector n) dissipation)
    (modalEnergy : a.add massRate (KScale o 2 (a.mul nu dissipation)) =
      KScale o 2 (KernelWeightedDot a measure source detector n)) :
    a.le (a.add (a.mul nu massRate) (a.mul (a.mul nu nu) dissipation))
      (KernelWeightedDot a measure source source n) := by
  have hy := kernel_weighted_packet_young o measure source detector n nu hm
  have hd := o.mulLeLeft (o.squareNonneg nu) capacity
  have hu := o.leTrans hy (o.addLeAdd
    (o.leRefl (KernelWeightedDot a measure source source n)) hd)
  have he := congrArg (a.mul nu) modalEnergy
  have he' : a.add (a.add (a.mul nu massRate) (a.mul (a.mul nu nu) dissipation))
      (a.mul (a.mul nu nu) dissipation) =
      KScale o 2 (a.mul nu (KernelWeightedDot a measure source detector n)) := by
    simpa only [k_scale_two o, o.mulAdd, o.mulAssoc, o.addAssoc] using he
  apply o.addLeCancelRight (z := a.mul (a.mul nu nu) dissipation)
  rw [he']
  exact hu

theorem kernel_weighted_packet_damping {a : Analysis} (o : KernelArithmetic a)
    (measure source damping : Nat → a.Scalar) (n : Nat)
    (h : ∀ i, i < n → a.le (a.mul (measure i) (a.mul (source i) (source i))) (damping i)) :
    a.le (KernelWeightedDot a measure source source n) (ledgerPrefix a damping n) :=
  k_prefix_mono o n _ _ h

/- This replaces criticalAbsorption by a modal energy identity and an actual
   finite capacity allocation on each time slice. Constructing those modal
   and packet bindings from the source census is a separately indexed port. -/
theorem kernel_packet_integrated_critical {a : Analysis} (o : KernelArithmetic a)
    {Time : Type} (C : KernelCalculus a Time)
    (mass massRate dissipation dissipationRate sourceIntegral : Time → a.Scalar)
    (measure source detector : Time → Nat → a.Scalar) (n : Nat) (nu : a.Scalar)
    (hmass : C.Derivative mass massRate)
    (hdiss : KernelPrimitive C dissipationRate dissipation)
    (hsource : KernelPrimitive C
      (fun t => KernelWeightedDot a (measure t) (source t) (source t) n) sourceIntegral)
    (hm : ∀ t i, i < n → a.le a.zero (measure t i))
    (hc : ∀ t, a.le (KernelWeightedDot a (measure t) (detector t) (detector t) n) (dissipationRate t))
    (he : ∀ t, a.add (massRate t) (KScale o 2 (a.mul nu (dissipationRate t))) =
      KScale o 2 (KernelWeightedDot a (measure t) (source t) (detector t) n)) :
    ∀ t, a.le (a.add (a.mul nu (mass t)) (a.mul (a.mul nu nu) (dissipation t)))
      (a.add (a.mul nu (mass C.origin)) (sourceIntegral t)) :=
  kernel_integrated_balance o C _ _ _ _ _ _ (C.scale nu mass massRate hmass)
    (kernel_primitive_scale o C (a.mul nu nu) hdiss) hsource
    (fun t => kernel_weighted_packet_absorption o (measure t) (source t) (detector t) n
      nu (dissipationRate t) (massRate t) (hm t) (hc t) (he t))

end Fefferman
