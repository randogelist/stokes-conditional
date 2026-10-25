import NSE.PrefixPayment
import NSE.CriticalBalance
import NSE.Completion

/-!
The M7 injection uses the actual finite modal energy and actual primitives
of its source and dissipation. Uniform payment bounds produce countable
readouts by real completeness. Spatial realization and the physical time
integral are not introduced as conclusions of this module.
-/

namespace NSE

open Set Filter
open scoped Topology

/-- The modal law and ordinary derivative primitives on the same interval.
The source `b` includes any viscous remainder needed by a nonspectral basis. -/
structure CriticalRealization (T nu : ℝ) (lam : ℕ → ℝ)
    (a b : ℝ → ℕ → ℝ) (D C : ℕ → ℝ → ℝ) (X0 : ℝ) : Prop where
  time_pos : 0 < T
  viscosity_pos : 0 < nu
  weight_nonneg : ∀ i, 0 ≤ lam i
  modal : ∀ t ∈ Ico 0 T, ∀ i,
    HasDerivAt (fun s => a s i) (-nu * (lam i)^2 * a t i - b t i) t
  dissipation_derivative : ∀ N t, t ∈ Ico 0 T →
    HasDerivAt (D N) (criticalDissipation lam a N t) t
  action_derivative : ∀ N t, t ∈ Ico 0 T →
    HasDerivAt (C N) (criticalSourceDensity nu lam a b N t) t
  dissipation_zero : ∀ N, D N 0 = 0
  action_zero : ∀ N, C N 0 = 0
  seed_bound : ∀ N, criticalEnergy lam a N 0 ≤ X0

/-- The exact completed critical energy of this coefficient trajectory. -/
noncomputable def criticalMassReadout (lam : ℕ → ℝ) (a : ℝ → ℕ → ℝ)
    (t : ℝ) : ℝ := prefixTotal (fun N => criticalEnergy lam a N t)

/-- The exact completed cutoff dissipation primitive of this trajectory. -/
noncomputable def dissipationReadout (D : ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  prefixTotal (fun N => D N t)

theorem CriticalRealization.seed_nonneg {T nu : ℝ} {lam : ℕ → ℝ}
    {a b : ℝ → ℕ → ℝ} {D C : ℕ → ℝ → ℝ} {X0 : ℝ}
    (hreal : CriticalRealization T nu lam a b D C X0) : 0 ≤ X0 := by
  simpa [criticalEnergy] using hreal.seed_bound 0

theorem CriticalRealization.balance {T nu : ℝ} {lam : ℕ → ℝ}
    {a b : ℝ → ℕ → ℝ} {D C : ℕ → ℝ → ℝ} {X0 : ℝ}
    (hreal : CriticalRealization T nu lam a b D C X0) (N : ℕ)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    criticalEnergy lam a N t + nu * D N t ≤ criticalEnergy lam a N 0 + C N t := by
  exact critical_balance_of_modal nu T lam a b N (D N) (C N)
    hreal.viscosity_pos hreal.weight_nonneg
    (fun s hs i _ => hreal.modal s hs i)
    (hreal.dissipation_derivative N) (hreal.action_derivative N)
    (hreal.dissipation_zero N) (hreal.action_zero N) t ht

theorem CriticalRealization.cumulativeAction {T nu : ℝ} {lam : ℕ → ℝ}
    {a b : ℝ → ℕ → ℝ} {D C : ℕ → ℝ → ℝ} {X0 : ℝ}
    (hreal : CriticalRealization T nu lam a b D C X0) :
    CumulativeAction T C := by
  refine ⟨hreal.action_zero, ?_⟩
  intro N s t hs hst ht
  have hmono := primitive_monotone_on_halfopen
    (fun r hr0 hrT => hreal.action_derivative N r ⟨hr0, hrT⟩)
    (fun r _ _ => criticalSourceDensity_nonneg nu lam a b
      hreal.viscosity_pos hreal.weight_nonneg N r)
  exact hmono ⟨hs, lt_of_le_of_lt hst ht⟩ ⟨le_trans hs hst, ht⟩ hst

theorem CriticalRealization.dissipation_nonneg {T nu : ℝ} {lam : ℕ → ℝ}
    {a b : ℝ → ℕ → ℝ} {D C : ℕ → ℝ → ℝ} {X0 : ℝ}
    (hreal : CriticalRealization T nu lam a b D C X0) (N : ℕ)
    {t : ℝ} (ht : t ∈ Ico 0 T) : 0 ≤ D N t := by
  exact primitive_nonneg_on_halfopen (hreal.dissipation_zero N)
    (fun r hr0 hrT => hreal.dissipation_derivative N r ⟨hr0, hrT⟩)
    (fun r _ _ => criticalDissipation_nonneg lam a hreal.weight_nonneg N r) ht.1 ht.2

theorem CriticalRealization.dissipation_cutoff_monotone {T nu : ℝ} {lam : ℕ → ℝ}
    {a b : ℝ → ℕ → ℝ} {D C : ℕ → ℝ → ℝ} {X0 : ℝ}
    (hreal : CriticalRealization T nu lam a b D C X0)
    {t : ℝ} (ht : t ∈ Ico 0 T) : Monotone (fun N => D N t) := by
  exact cumulative_cutoff_monotone hreal.dissipation_zero
    (fun N r hr0 hrT => hreal.dissipation_derivative N r ⟨hr0, hrT⟩)
    (fun r _ _ => criticalDissipation_monotone lam a hreal.weight_nonneg r) ht.1 ht.2

/-- All conclusions retain the given trajectory and its given primitives.
Neither the mass nor the dissipation total is an arbitrary bounded function. -/
structure M7Injection (T nu : ℝ) (lam : ℕ → ℝ)
    (a : ℝ → ℕ → ℝ) (D C : ℕ → ℝ → ℝ) (X0 Seed Paid theta : ℝ) : Prop where
  cumulative_action : CumulativeAction T C
  mass_nonneg : ∀ N n, 0 ≤ actionMass C (canonicalCut T) N n
  sequence_m7 : ∀ N, GPSequenceM7 (actionMass C (canonicalCut T) N)
  action_bound : ∀ N t, t ∈ Ico 0 T → C N t ≤ actionBudget Seed Paid theta
  critical_balance : ∀ N t, t ∈ Ico 0 T →
    criticalEnergy lam a N t + nu * D N t ≤ criticalEnergy lam a N 0 + C N t
  energy_bound : ∀ N t, t ∈ Ico 0 T →
    criticalEnergy lam a N t ≤ X0 + actionBudget Seed Paid theta
  dissipation_bound : ∀ N t, t ∈ Ico 0 T →
    0 ≤ D N t ∧ D N t ≤ (X0 + actionBudget Seed Paid theta) / nu
  energy_total : ∀ t, t ∈ Ico 0 T →
    IsPrefixTotal (fun N => criticalEnergy lam a N t) (criticalMassReadout lam a t)
  energy_total_bound : ∀ t, t ∈ Ico 0 T →
    0 ≤ criticalMassReadout lam a t ∧
      criticalMassReadout lam a t ≤ X0 + actionBudget Seed Paid theta
  energy_limit : ∀ t, t ∈ Ico 0 T →
    Tendsto (fun N => criticalEnergy lam a N t) atTop (𝓝 (criticalMassReadout lam a t))
  dissipation_cutoff_monotone : ∀ t, t ∈ Ico 0 T → Monotone (fun N => D N t)
  dissipation_total : ∀ t, t ∈ Ico 0 T →
    IsPrefixTotal (fun N => D N t) (dissipationReadout D t)
  dissipation_total_bound : ∀ t, t ∈ Ico 0 T →
    0 ≤ dissipationReadout D t ∧
      dissipationReadout D t ≤ (X0 + actionBudget Seed Paid theta) / nu
  dissipation_limit : ∀ t, t ∈ Ico 0 T →
    Tendsto (fun N => D N t) atTop (𝓝 (dissipationReadout D t))

/-- Actual primitives and subcritical prefix payment imply the complete
M7 injection, including both countable cutoff limits. -/
theorem criticalRealization_injects {T nu : ℝ} {lam : ℕ → ℝ}
    {a b : ℝ → ℕ → ℝ} {D C : ℕ → ℝ → ℝ} {X0 Seed Paid theta : ℝ}
    (hreal : CriticalRealization T nu lam a b D C X0)
    (hpay : PrefixPayment (actionMass C (canonicalCut T)) Seed Paid theta) :
    M7Injection T nu lam a D C X0 Seed Paid theta := by
  have hgrid := canonicalCut_grid hreal.time_pos
  have hC := hreal.cumulativeAction
  have hmass := actionMass_nonneg hgrid hC
  have haction : ∀ N t, t ∈ Ico 0 T → C N t ≤ actionBudget Seed Paid theta := by
    intro N t ht
    exact actionPayment_bound hgrid hC hpay N ht
  have henergy : ∀ N t, t ∈ Ico 0 T →
      criticalEnergy lam a N t ≤ X0 + actionBudget Seed Paid theta := by
    intro N t ht
    have hb := hreal.balance N ht
    have hs := hreal.seed_bound N
    have hc := haction N t ht
    have hd := mul_nonneg hreal.viscosity_pos.le (hreal.dissipation_nonneg N ht)
    linarith
  have hdiss : ∀ N t, t ∈ Ico 0 T →
      0 ≤ D N t ∧ D N t ≤ (X0 + actionBudget Seed Paid theta) / nu := by
    intro N t ht
    refine ⟨hreal.dissipation_nonneg N ht, ?_⟩
    apply (le_div_iff₀ hreal.viscosity_pos).2
    have hb := hreal.balance N ht
    have hs := hreal.seed_bound N
    have hc := haction N t ht
    have he := criticalEnergy_nonneg lam a hreal.weight_nonneg N t
    nlinarith
  have henergyTotal : ∀ t, t ∈ Ico 0 T →
      0 ≤ criticalMassReadout lam a t ∧
      criticalMassReadout lam a t ≤ X0 + actionBudget Seed Paid theta ∧
      IsPrefixTotal (fun N => criticalEnergy lam a N t) (criticalMassReadout lam a t) ∧
      Tendsto (fun N => criticalEnergy lam a N t) atTop (𝓝 (criticalMassReadout lam a t)) := by
    intro t ht
    exact bounded_monotone_completion
      (criticalEnergy_nonneg lam a hreal.weight_nonneg 0 t)
      (criticalEnergy_monotone lam a hreal.weight_nonneg t)
      (fun N => henergy N t ht)
  have hdissTotal : ∀ t, t ∈ Ico 0 T →
      0 ≤ dissipationReadout D t ∧
      dissipationReadout D t ≤ (X0 + actionBudget Seed Paid theta) / nu ∧
      IsPrefixTotal (fun N => D N t) (dissipationReadout D t) ∧
      Tendsto (fun N => D N t) atTop (𝓝 (dissipationReadout D t)) := by
    intro t ht
    exact bounded_monotone_completion (hdiss 0 t ht).1
      (hreal.dissipation_cutoff_monotone ht) (fun N => (hdiss N t ht).2)
  refine ⟨hC, hmass, prefixPayment_m7 hmass hpay, haction,
    (fun N t ht => hreal.balance N ht), henergy, hdiss, ?_, ?_, ?_,
    (fun t ht => hreal.dissipation_cutoff_monotone ht), ?_, ?_, ?_⟩
  · intro t ht
    exact (henergyTotal t ht).2.2.1
  · intro t ht
    exact ⟨(henergyTotal t ht).1, (henergyTotal t ht).2.1⟩
  · intro t ht
    exact (henergyTotal t ht).2.2.2
  · intro t ht
    exact (hdissTotal t ht).2.2.1
  · intro t ht
    exact ⟨(hdissTotal t ht).1, (hdissTotal t ht).2.1⟩
  · intro t ht
    exact (hdissTotal t ht).2.2.2

/-- An actual viscous coefficient need not equal the reference diagonal
coefficient. The difference is retained in the effective source, and the
action primitive must correspond to this full source. -/
theorem criticalRealization_of_operator {T nu : ℝ} {lam : ℕ → ℝ}
    {a viscous bNonlin : ℝ → ℕ → ℝ} {D C : ℕ → ℝ → ℝ} {X0 : ℝ}
    (hT : 0 < T) (hnu : 0 < nu) (hlam : ∀ i, 0 ≤ lam i)
    (hmodal : ∀ t ∈ Ico 0 T, ∀ i,
      HasDerivAt (fun s => a s i) (-nu * viscous t i - bNonlin t i) t)
    (hD : ∀ N t, t ∈ Ico 0 T →
      HasDerivAt (D N) (criticalDissipation lam a N t) t)
    (hC : ∀ N t, t ∈ Ico 0 T →
      HasDerivAt (C N)
        (criticalSourceDensity nu lam a (effectiveSource nu lam a viscous bNonlin) N t) t)
    (hD0 : ∀ N, D N 0 = 0) (hC0 : ∀ N, C N 0 = 0)
    (hseed : ∀ N, criticalEnergy lam a N 0 ≤ X0) :
    CriticalRealization T nu lam a (effectiveSource nu lam a viscous bNonlin) D C X0 := by
  refine ⟨hT, hnu, hlam, ?_, hD, hC, hD0, hC0, hseed⟩
  intro t ht i
  exact effectiveSource_modal_derivative nu lam a viscous bNonlin t i (hmodal t ht i)

/-- The general operator form injects into M7 with the same primitive and
its payment bound. No diagonalization assumption is used. -/
theorem operator_injects {T nu : ℝ} {lam : ℕ → ℝ}
    {a viscous bNonlin : ℝ → ℕ → ℝ} {D C : ℕ → ℝ → ℝ}
    {X0 Seed Paid theta : ℝ}
    (hT : 0 < T) (hnu : 0 < nu) (hlam : ∀ i, 0 ≤ lam i)
    (hmodal : ∀ t ∈ Ico 0 T, ∀ i,
      HasDerivAt (fun s => a s i) (-nu * viscous t i - bNonlin t i) t)
    (hD : ∀ N t, t ∈ Ico 0 T →
      HasDerivAt (D N) (criticalDissipation lam a N t) t)
    (hC : ∀ N t, t ∈ Ico 0 T →
      HasDerivAt (C N)
        (criticalSourceDensity nu lam a (effectiveSource nu lam a viscous bNonlin) N t) t)
    (hD0 : ∀ N, D N 0 = 0) (hC0 : ∀ N, C N 0 = 0)
    (hseed : ∀ N, criticalEnergy lam a N 0 ≤ X0)
    (hpay : PrefixPayment (actionMass C (canonicalCut T)) Seed Paid theta) :
    M7Injection T nu lam a D C X0 Seed Paid theta :=
  criticalRealization_injects
    (criticalRealization_of_operator hT hnu hlam hmodal hD hC hD0 hC0 hseed) hpay

#print axioms CriticalRealization.balance
#print axioms CriticalRealization.dissipation_cutoff_monotone
#print axioms criticalRealization_injects
#print axioms criticalRealization_of_operator
#print axioms operator_injects

end NSE
