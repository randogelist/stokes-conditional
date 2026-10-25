import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative Serrin readout bound

The integrations in this file are mathlib's actual real Bochner integrals;
the time specialization uses Lebesgue measure restricted to `(0,t]`.
The scalar readouts represent **squared** measurements. Their identification
with physical Sobolev/L6 norms is supplied by an application, not asserted by
their names. The same-path continuation contract remains explicit.
-/

noncomputable section

open MeasureTheory

namespace NSE

/-- Pointwise control of four squared readouts. `Csq` is the square of the
ordinary Sobolev embedding constant. -/
def SquaredNormControl (e d h l Csq M : ℝ) : Prop :=
  0 ≤ e ∧ 0 ≤ d ∧ 0 ≤ h ∧ 0 ≤ l ∧ e ≤ M ∧
    h ^ 2 ≤ e * d ∧ l ≤ Csq * h

theorem squaredNormInterpolation {e d h l Csq M : ℝ}
    (hCsq : 0 ≤ Csq) (control : SquaredNormControl e d h l Csq M) :
    l ^ 2 ≤ Csq ^ 2 * M * d := by
  rcases control with ⟨_he, hd, hh, hl, heM, hinterp, hsob⟩
  have hCh : 0 ≤ Csq * h := mul_nonneg hCsq hh
  have hprod : 0 ≤ (Csq * h - l) * (Csq * h + l) :=
    mul_nonneg (sub_nonneg.mpr hsob) (add_nonneg hCh hl)
  have hsquare : l ^ 2 ≤ (Csq * h) ^ 2 := by nlinarith
  have hscaled : Csq ^ 2 * h ^ 2 ≤ Csq ^ 2 * (e * d) :=
    mul_le_mul_of_nonneg_left hinterp (sq_nonneg Csq)
  have hed : e * d ≤ M * d := mul_le_mul_of_nonneg_right heM hd
  have hscaledCap : Csq ^ 2 * (e * d) ≤ Csq ^ 2 * (M * d) :=
    mul_le_mul_of_nonneg_left hed (sq_nonneg Csq)
  nlinarith

/-- Local integrability of the fourth-power readout follows from measurable
domination by the integrable critical dissipation. It need not be assumed
as a separate local Serrin hypothesis. -/
theorem fourthPowerIntegrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (e d h l : α → ℝ) {Csq M : ℝ}
    (hCsq : 0 ≤ Csq) (hd : Integrable d μ)
    (hl : AEStronglyMeasurable (fun x => l x ^ 2) μ)
    (hcontrol : ∀ᵐ x ∂μ, SquaredNormControl (e x) (d x) (h x) (l x) Csq M) :
    Integrable (fun x => l x ^ 2) μ := by
  apply (hd.const_mul (Csq ^ 2 * M)).mono' hl
  filter_upwards [hcontrol] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (l x))] using
    (squaredNormInterpolation hCsq hx)

/-- Actual integral estimate on an arbitrary measure space. Integrability
of both comparison functions is explicit, so undefined/nonintegrable
Bochner integrals cannot be used to manufacture the inequality. -/
theorem integratedSerrinBound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (e d h l : α → ℝ) {Csq M ν : ℝ}
    (hCsq : 0 ≤ Csq) (hM : 0 ≤ M)
    (hd : Integrable d μ) (hl : Integrable (fun x => l x ^ 2) μ)
    (hcontrol : ∀ᵐ x ∂μ, SquaredNormControl (e x) (d x) (h x) (l x) Csq M)
    (hdiss : (∫ x, d x ∂μ) ≤ M / ν) :
    (∫ x, l x ^ 2 ∂μ) ≤ Csq ^ 2 * M ^ 2 / ν := by
  have hK : 0 ≤ Csq ^ 2 * M := mul_nonneg (sq_nonneg Csq) hM
  have hpoint : ∀ᵐ x ∂μ, l x ^ 2 ≤ (Csq ^ 2 * M) * d x := by
    filter_upwards [hcontrol] with x hx
    exact squaredNormInterpolation hCsq hx
  calc
    (∫ x, l x ^ 2 ∂μ) ≤ ∫ x, (Csq ^ 2 * M) * d x ∂μ :=
      integral_mono_ae hl (hd.const_mul (Csq ^ 2 * M)) hpoint
    _ = (Csq ^ 2 * M) * (∫ x, d x ∂μ) := integral_const_mul _ _
    _ ≤ (Csq ^ 2 * M) * (M / ν) := mul_le_mul_of_nonneg_left hdiss hK
    _ = Csq ^ 2 * M ^ 2 / ν := by ring

/-- Lebesgue measure on the actual time interval `(0,t]`. -/
def serrinTimeMeasure (t : ℝ) : Measure ℝ :=
  volume.restrict (Set.Ioc 0 t)

/-- The fourth-power time observable for a squared `L6` readout. -/
def serrinObservable (l : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s, l s ^ 2 ∂serrinTimeMeasure t

theorem timeSerrinBound (e d h l : ℝ → ℝ) (t : ℝ) {Csq M ν : ℝ}
    (hCsq : 0 ≤ Csq) (hM : 0 ≤ M)
    (hd : Integrable d (serrinTimeMeasure t))
    (hl : Integrable (fun s => l s ^ 2) (serrinTimeMeasure t))
    (hcontrol : ∀ᵐ s ∂serrinTimeMeasure t,
      SquaredNormControl (e s) (d s) (h s) (l s) Csq M)
    (hdiss : (∫ s, d s ∂serrinTimeMeasure t) ≤ M / ν) :
    serrinObservable l t ≤ Csq ^ 2 * M ^ 2 / ν :=
  integratedSerrinBound (serrinTimeMeasure t) e d h l
    hCsq hM hd hl hcontrol hdiss

/-- Uniformity uses one finite bound for every endpoint strictly before
`T`; it does not choose a fresh constant at each endpoint. -/
def UniformSerrinObservable (l : ℝ → ℝ) (T : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → t < T → serrinObservable l t ≤ B

/-- All four readouts are evaluations on the SAME path. This binding uses
actual Lebesgue integrability and cumulative dissipation; it contains no
claim that the supplied measurement functions are already physical norms.
The common cap `M` is typically supplied by the completed M7 critical bound. -/
structure SerrinReadoutBinding {State : Type*} (u : ℝ → State)
    (e d h l : State → ℝ) (T ν M Csq : ℝ) : Prop where
  viscosity_pos : 0 < ν
  cap_nonneg : 0 ≤ M
  constant_nonneg : 0 ≤ Csq
  dissipation_integrable : ∀ t : ℝ, 0 ≤ t → t < T →
    Integrable (fun s => d (u s)) (serrinTimeMeasure t)
  fourth_power_measurable : ∀ t : ℝ, 0 ≤ t → t < T →
    AEStronglyMeasurable (fun s => l (u s) ^ 2) (serrinTimeMeasure t)
  pointwise_control : ∀ t : ℝ, 0 ≤ t → t < T →
    ∀ᵐ s ∂serrinTimeMeasure t,
      SquaredNormControl (e (u s)) (d (u s)) (h (u s)) (l (u s)) Csq M
  cumulative_dissipation : ∀ t : ℝ, 0 ≤ t → t < T →
    (∫ s, d (u s) ∂serrinTimeMeasure t) ≤ M / ν

theorem SerrinReadoutBinding.fourth_power_integrable
    {State : Type*} {u : ℝ → State} {e d h l : State → ℝ} {T ν M Csq : ℝ}
    (binding : SerrinReadoutBinding u e d h l T ν M Csq)
    (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
    Integrable (fun s => l (u s) ^ 2) (serrinTimeMeasure t) :=
  fourthPowerIntegrable (serrinTimeMeasure t) (fun s => e (u s))
    (fun s => d (u s)) (fun s => h (u s)) (fun s => l (u s))
    binding.constant_nonneg (binding.dissipation_integrable t ht0 htT)
    (binding.fourth_power_measurable t ht0 htT)
    (binding.pointwise_control t ht0 htT)

theorem samePathSerrinBound {State : Type*} {u : ℝ → State}
    {e d h l : State → ℝ} {T ν M Csq : ℝ}
    (binding : SerrinReadoutBinding u e d h l T ν M Csq)
    (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
    serrinObservable (fun s => l (u s)) t ≤ Csq ^ 2 * M ^ 2 / ν :=
  timeSerrinBound (fun s => e (u s)) (fun s => d (u s))
    (fun s => h (u s)) (fun s => l (u s)) t
    binding.constant_nonneg binding.cap_nonneg
    (binding.dissipation_integrable t ht0 htT)
    (binding.fourth_power_integrable t ht0 htT)
    (binding.pointwise_control t ht0 htT)
    (binding.cumulative_dissipation t ht0 htT)

theorem samePathUniformSerrinObservable {State : Type*} {u : ℝ → State}
    {e d h l : State → ℝ} {T ν M Csq : ℝ}
    (binding : SerrinReadoutBinding u e d h l T ν M Csq) :
    UniformSerrinObservable (fun s => l (u s)) T := by
  refine ⟨Csq ^ 2 * M ^ 2 / ν, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (sq_nonneg Csq) (sq_nonneg M))
      (le_of_lt binding.viscosity_pos)
  · exact samePathSerrinBound binding

/-- The analytic exit remains an explicit hypothesis. It must identify
this exact same-path observable with the desired physical Serrin class
and supply that class's continuation theorem. This record does not prove
either physical assertion merely by naming it. -/
structure SerrinExitContract {State : Type*} (u : ℝ → State)
    (l : State → ℝ) (T : ℝ)
    (ActualSerrin46 Continues : (ℝ → State) → Prop) : Prop where
  actual_norm_and_limit_identification :
    UniformSerrinObservable (fun s => l (u s)) T → ActualSerrin46 u
  continuation_principle : ActualSerrin46 u → Continues u

theorem samePathSerrinContinuation {State : Type*} {u : ℝ → State}
    {e d h l : State → ℝ} {T ν M Csq : ℝ}
    {ActualSerrin46 Continues : (ℝ → State) → Prop}
    (binding : SerrinReadoutBinding u e d h l T ν M Csq)
    (exit : SerrinExitContract u l T ActualSerrin46 Continues) :
    ActualSerrin46 u ∧ Continues u := by
  have hS := exit.actual_norm_and_limit_identification
    (samePathUniformSerrinObservable binding)
  exact ⟨hS, exit.continuation_principle hS⟩

#print axioms squaredNormInterpolation
#print axioms fourthPowerIntegrable
#print axioms integratedSerrinBound
#print axioms samePathSerrinContinuation

end NSE
