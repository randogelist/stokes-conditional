import Fefferman.KernelCapacity
import Fefferman.ProjectRoutes

set_option autoImplicit false

namespace Fefferman

/- B15's two distinct physical entrances, with the original finite-prefix
   formulas. Neither contains the uniform physical-prefix conclusion. -/
structure KernelPrefixRealization (a : Analysis)
    (physical population : Nat → a.Scalar) (realization : a.Scalar) : Prop where
  nonnegative : a.le a.zero realization
  binding : ∀ n, a.le (physical n) (a.mul realization (ledgerPrefix a population n))

structure KernelUniformRenewal (a : Analysis) (population paid : Nat → a.Scalar)
    (rho budget : a.Scalar) : Prop where
  strictLoss : a.lt rho a.one
  populationNonnegative : ∀ n, a.le a.zero (population n)
  renewal : ∀ n, a.le (population (n+1)) (a.add (a.mul rho (population n)) (paid n))
  paidPrefix : ∀ n, a.le (ledgerPrefix a paid n) budget

theorem kernel_generic_renewal_m7 {a : Analysis} (o : KernelArithmetic a)
    {population paid : Nat → a.Scalar} {rho budget : a.Scalar}
    (h : KernelUniformRenewal a population paid rho budget) : KernelM7 a population := by
  have hgap := o.subPositive h.strictLoss
  have hbudget : a.le a.zero budget := h.paidPrefix 0
  refine ⟨o.divide (a.add (population 0) budget) (KSub a a.one rho),
    k_div_nonneg o (k_add_nonneg o (h.populationNonnegative 0) hbudget) hgap, ?_⟩
  exact ledger_renewal_prefix_bound o.toLedgerArithmetic _ population paid (population 0) budget
    hgap h.populationNonnegative (o.leRefl _)
    (ledger_renewal_step_from_retention o.toLedgerArithmetic rho population paid h.renewal) h.paidPrefix

theorem kernel_covariance_physical_prefix {a : Analysis} (o : KernelArithmetic a)
    {physical population paid : Nat → a.Scalar} {rho budget realization : a.Scalar}
    (binding : KernelPrefixRealization a physical population realization)
    (payment : KernelUniformRenewal a population paid rho budget) : KernelBounded a physical := by
  rcases kernel_generic_renewal_m7 o payment with ⟨b, hb, hp⟩
  exact ⟨a.mul realization b, o.mulNonneg binding.nonnegative hb,
    fun n => o.leTrans (binding.binding n) (o.mulLeLeft binding.nonnegative (hp n))⟩

theorem kernel_convex_shared_budget {a : Analysis} (o : KernelArithmetic a)
    (weight cost : Nat → a.Scalar) (m : Nat) (bound : a.Scalar)
    (hw : ∀ i, i < m → a.le a.zero (weight i))
    (hs : ledgerPrefix a weight m = a.one)
    (hc : ∀ i, i < m → a.le (cost i) bound) :
    a.le (ledgerPrefix a (fun i => a.mul (weight i) (cost i)) m) bound := by
  have h := k_prefix_mono o m _ _ (fun i hi => o.mulLeLeft (hw i hi) (hc i hi))
  have he : ledgerPrefix a (fun i => a.mul (weight i) bound) m = bound := by
    calc
      _ = ledgerPrefix a (fun i => a.mul bound (weight i)) m :=
        spectral_prefix_congr a m _ _ (fun i _ => o.mulComm _ _)
      _ = _ := by rw [ledger_prefix_scale o.toLedgerArithmetic, hs, k_mul_one o]
  rw [he] at h
  exact h

theorem kernel_positive_carrier_partition {a : Analysis} (o : KernelArithmetic a)
    (base remainder : a.Scalar) (channel : Nat → a.Scalar) (n : Nat) (bound : a.Scalar)
    (hs : base = a.add remainder (ledgerPrefix a channel n))
    (hr : a.le a.zero remainder) (hb : a.le base bound) :
    a.le (ledgerPrefix a channel n) bound := by
  rw [hs] at hb
  exact o.leTrans (ledger_drop_left o.toLedgerArithmetic _ hr) hb

theorem kernel_gradient_square_payment {a : Analysis} (o : KernelArithmetic a)
    (gradient : Nat → a.Scalar) (n : Nat) (ceiling energy nu : a.Scalar)
    (hn : a.le a.zero nu) (hm : a.le a.zero ceiling)
    (hg : ∀ i, i < n → a.le a.zero (gradient i) ∧ a.le (gradient i) ceiling)
    (he : a.le (a.mul nu (ledgerPrefix a gradient n)) energy) :
    a.le (a.mul nu (ledgerPrefix a (fun i => a.mul (gradient i) (gradient i)) n))
      (a.mul ceiling energy) := by
  have hp := k_prefix_mono o n _ _ (fun i hi => k_mul_le_right o (hg i hi).1 (hg i hi).2)
  rw [ledger_prefix_scale o.toLedgerArithmetic] at hp
  have hh := o.mulLeLeft hn hp
  have he' := o.mulLeLeft hm he
  have hs : a.le (a.mul nu (a.mul ceiling (ledgerPrefix a gradient n))) (a.mul ceiling energy) := by
    simpa only [source_mul_interchange o.toSourceArithmetic] using he'
  exact o.leTrans hh hs

theorem kernel_action_from_gradient_payment {a : Analysis} (o : KernelArithmetic a)
    (action gradient : Nat → a.Scalar) (n : Nat) (constant ceiling energy nu : a.Scalar)
    (hn : a.le a.zero nu) (hc : a.le a.zero constant) (hm : a.le a.zero ceiling)
    (hg : ∀ i, i < n → a.le a.zero (gradient i) ∧ a.le (gradient i) ceiling)
    (ha : ∀ i, i < n → a.le (action i) (a.mul constant (a.mul (gradient i) (gradient i))))
    (he : a.le (a.mul nu (ledgerPrefix a gradient n)) energy) :
    a.le (a.mul nu (ledgerPrefix a action n)) (a.mul (a.mul constant ceiling) energy) := by
  have hp := k_prefix_mono o n _ _ ha
  rw [ledger_prefix_scale o.toLedgerArithmetic] at hp
  have hq := o.mulLeLeft hc (kernel_gradient_square_payment o gradient n ceiling energy nu hn hm hg he)
  have hq' : a.le (a.mul nu (a.mul constant (ledgerPrefix a (fun i => a.mul (gradient i) (gradient i)) n)))
      (a.mul (a.mul constant ceiling) energy) := by
    simpa only [o.mulAssoc, o.mulComm, source_mul_interchange o.toSourceArithmetic] using hq
  exact o.leTrans (o.mulLeLeft hn hp) hq'

theorem kernel_single_ledger_payment {a : Analysis} (o : KernelArithmetic a)
    (paid credit : Nat → a.Scalar) (charge : a.Scalar) (n : Nat)
    (h : ∀ i, i < n → a.le (paid i) (a.mul charge (KSub a (credit (i+1)) (credit i)))) :
    a.le (ledgerPrefix a paid n) (a.mul charge (KSub a (credit n) (credit 0))) := by
  have hp := k_prefix_mono o n _ _ h
  rw [ledger_prefix_scale o.toLedgerArithmetic, k_prefix_telescope o] at hp
  exact hp

structure KernelCovarianceData (a : Analysis) where
  physical : Nat → a.Scalar
  population : Nat → a.Scalar
  paid : Nat → a.Scalar
  rho : a.Scalar
  budget : a.Scalar
  realization : a.Scalar

def reconstructedCovariance (a : Analysis) (d : Domain)
    (serrin : UnforcedInput a d → KernelCovarianceData a → Prop) : CovarianceObservables a d where
  Object := fun _ => KernelCovarianceData a
  physicalPrefixRealization := fun _ c => KernelPrefixRealization a c.physical c.population c.realization
  uniformRenewalPayment := fun _ c => KernelUniformRenewal a c.population c.paid c.rho c.budget
  uniformGPBound := fun _ c => KernelBounded a c.physical
  serrin := serrin

theorem reconstructed_covariance_port {a : Analysis} (o : KernelArithmetic a) (d : Domain)
    (serrin : UnforcedInput a d → KernelCovarianceData a → Prop) :
    CovarianceLeanPort (reconstructedCovariance a d serrin) :=
  ⟨fun _ _ binding payment => kernel_covariance_physical_prefix o binding payment⟩

theorem A_from_reconstructed_covariance {a : Analysis} (o : KernelArithmetic a)
    (serrin : UnforcedInput a .wholeSpace → KernelCovarianceData a → Prop)
    (ends : CovarianceEndpointPorts (reconstructedCovariance a .wholeSpace serrin)) : A a :=
  A_from_COVARIANCE _ (reconstructed_covariance_port o .wholeSpace serrin) ends

theorem B_from_reconstructed_covariance {a : Analysis} (o : KernelArithmetic a)
    (serrin : UnforcedInput a .periodic → KernelCovarianceData a → Prop)
    (ends : CovarianceEndpointPorts (reconstructedCovariance a .periodic serrin)) : B a :=
  B_from_periodic_COVARIANCE _ (reconstructed_covariance_port o .periodic serrin) ends

end Fefferman
