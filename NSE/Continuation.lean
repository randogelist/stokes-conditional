import NSE.Representation
import NSE.Injection
import NSE.Serrin

/-! Same-trajectory composition. The physical realization and analytic exit
are explicit inputs; all scalar budgets and countable bounds are derived. -/

noncomputable section
open MeasureTheory Set
open NSE.Representation

namespace NSE

def pathCoefficients {H : Type*} (r : CoordinateRealization H) (u : ℝ → H) :
    ℝ → ℕ → ℝ := fun t => (r.equivalence (u t)).val

/-- Identification with the actual completed modal readouts. No bound is
assumed here: the M7 injection supplies both bounds used below. -/
structure SamePathNormRealization {H : Type*} (u : ℝ → H)
    (lam : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (D : ℕ → ℝ → ℝ)
    (e d h l : H → ℝ) (T Csq : ℝ) : Prop where
  constant_nonneg : 0 ≤ Csq
  mass_identity : ∀ t, t ∈ Ico 0 T → e (u t) = criticalMassReadout lam a t
  dissipation_identity : ∀ t, t ∈ Ico 0 T →
    (∫ s, d (u s) ∂serrinTimeMeasure t) = dissipationReadout D t
  dissipation_integrable : ∀ t, t ∈ Ico 0 T →
    Integrable (fun s => d (u s)) (serrinTimeMeasure t)
  fourth_power_measurable : ∀ t, t ∈ Ico 0 T →
    AEStronglyMeasurable (fun s => l (u s) ^ 2) (serrinTimeMeasure t)
  norm_control : ∀ t, t ∈ Ico 0 T →
    0 ≤ d (u t) ∧ 0 ≤ h (u t) ∧ 0 ≤ l (u t) ∧
    h (u t) ^ 2 ≤ e (u t) * d (u t) ∧ l (u t) ≤ Csq * h (u t)

theorem M7Injection.toSerrinBinding {H : Type*} {u : ℝ → H}
    {T nu X0 Seed Paid theta Csq : ℝ} {lam : ℕ → ℝ}
    {a : ℝ → ℕ → ℝ} {D C : ℕ → ℝ → ℝ} {e d h l : H → ℝ}
    (hi : M7Injection T nu lam a D C X0 Seed Paid theta)
    (hn : SamePathNormRealization u lam a D e d h l T Csq)
    (hnu : 0 < nu) (hM : 0 ≤ X0 + actionBudget Seed Paid theta) :
    SerrinReadoutBinding u e d h l T nu (X0 + actionBudget Seed Paid theta) Csq := by
  refine ⟨hnu, hM, hn.constant_nonneg, ?_, ?_, ?_, ?_⟩
  · intro t ht0 htT
    exact hn.dissipation_integrable t ⟨ht0, htT⟩
  · intro t ht0 htT
    exact hn.fourth_power_measurable t ⟨ht0, htT⟩
  · intro t ht0 htT
    have hm : ∀ᵐ s ∂serrinTimeMeasure t, s ∈ Ioc (0 : ℝ) t :=
      ae_restrict_mem measurableSet_Ioc
    filter_upwards [hm] with s hs
    have hsT : s ∈ Ico 0 T := ⟨hs.1.le, lt_of_le_of_lt hs.2 htT⟩
    have he := hi.energy_total_bound s hsT
    rw [← hn.mass_identity s hsT] at he
    obtain ⟨hd, hh, hl, hint, hsob⟩ := hn.norm_control s hsT
    exact ⟨he.1, hd, hh, hl, he.2, hint, hsob⟩
  · intro t ht0 htT
    rw [hn.dissipation_identity t ⟨ht0, htT⟩]
    exact (hi.dissipation_total_bound t ⟨ht0, htT⟩).2

/-- The reconstructed GP and BKQR paths both recover the same physical u. -/
theorem same_path_representation {H : Type*} (r : CoordinateRealization H)
    (g : Gauge) (p : RaisingProfile) (u : ℝ → H) :
    (∀ t, gpDecode g ((encGPEquiv g) (encodePath r u t)).val = pathCoefficients r u t) ∧
    (∀ t, shellDecode p.toShellProfile ((encBKQREquiv p) (encodePath r u t)).val =
      pathCoefficients r u t) ∧
    (∀ t, shellEnergy ((encBKQREquiv p) (encodePath r u t)).val = r.physicalEnergy (u t)) := by
  constructor
  · intro t
    exact gpDecode_encode g _
  constructor
  · intro t
    exact shellDecode_encode p.toShellProfile _
  · intro t
    exact (shell_energy_exact p.toShellProfile _).trans (r.isometry (u t))

/-- One endpoint T, one physical trajectory u, its encoded NSE and its own
source/dissipation primitives. The exit contract is the supplied PDE theorem. -/
theorem lh_encoding_m7_serrin_continuation {H Test Obs : Type*}
    (r : CoordinateRealization H) (weak : WeakNSEData H Test)
    (observe : Obs → H → ℝ) (kineticDiss : ℝ → ℝ) (u : ℝ → H)
    (T nu : ℝ) (lam : ℕ → ℝ) (b : ℝ → ℕ → ℝ)
    (D C : ℕ → ℝ → ℝ) (X0 Seed Paid theta Csq : ℝ)
    (e d h l : H → ℝ) (ActualSerrin46 Continues : (ℝ → H) → Prop)
    (hLH : LHNSE r.physicalEnergy weak observe kineticDiss nu T u)
    (hreal : CriticalRealization T nu lam (pathCoefficients r u) b D C X0)
    (hpay : PrefixPayment (actionMass C (canonicalCut T)) Seed Paid theta)
    (hnorm : SamePathNormRealization u lam (pathCoefficients r u) D e d h l T Csq)
    (hexit : SerrinExitContract u l T ActualSerrin46 Continues) :
    LHNSE (fun a : EncodedState => energy a.val) (encodedWeakData r weak)
      (encodedObservations r observe) kineticDiss nu T (encodePath r u) ∧
    M7Injection T nu lam (pathCoefficients r u) D C X0 Seed Paid theta ∧
    (∀ t, t ∈ Ico 0 T → serrinObservable (fun s => l (u s)) t ≤
      Csq ^ 2 * (X0 + actionBudget Seed Paid theta) ^ 2 / nu) ∧
    ActualSerrin46 u ∧ Continues u := by
  have hi := criticalRealization_injects hreal hpay
  have hM := add_nonneg hreal.seed_nonneg
    (actionBudget_nonneg hpay.seed_nonneg hpay.paid_nonneg hpay.theta_lt)
  have hb := hi.toSerrinBinding hnorm hreal.viscosity_pos hM
  refine ⟨(lh_nse_transport r weak observe kineticDiss nu T u).mpr hLH, hi, ?_, ?_⟩
  · intro t ht
    exact samePathSerrinBound hb t ht.1 ht.2
  · exact samePathSerrinContinuation hb hexit

/-- Continuation at every positive finite endpoint follows when the explicit
conditions above have been established at every such endpoint. Constants
are allowed to depend on T; no uniformity as T tends to infinity is needed. -/
theorem every_finite_endpoint {H : Type*} (u : ℝ → H)
    (Conditions : ℝ → Prop) (ContinuesBeyond : (ℝ → H) → ℝ → Prop)
    (bridge : ∀ T, 0 < T → Conditions T → ContinuesBeyond u T)
    (conditions : ∀ T, 0 < T → Conditions T) :
    ∀ T, 0 < T → ContinuesBeyond u T := by
  intro T hT
  exact bridge T hT (conditions T hT)

end NSE
