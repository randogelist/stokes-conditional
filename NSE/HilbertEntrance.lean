import NSE.Representation
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Countable Hilbert entrance derived from an orthonormal basis with dense
span. The physical realization of the Hilbert space remains an explicit input. -/

noncomputable section
open scoped BigOperators ENNReal lp

namespace NSE.HilbertEntrance

open Representation

theorem mem_l2_iff_square_summable (a : Seq) :
    Memℓp a 2 ↔ SquareSummable a := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  norm_num [SquareSummable, Real.norm_eq_abs, Real.rpow_two, sq_abs]

def l2EncodedEquiv : ℓ²(ℕ, ℝ) ≃ EncodedState where
  toFun a := ⟨a.val, (mem_l2_iff_square_summable a.val).mp a.property⟩
  invFun a := ⟨a.val, (mem_l2_iff_square_summable a.val).mpr a.property⟩
  left_inv _a := rfl
  right_inv _a := rfl

theorem l2_energy (a : ℓ²(ℕ, ℝ)) : energy a.val = ‖a‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) a
  norm_num [Real.norm_eq_abs, Real.rpow_two, sq_abs] at h
  exact h.symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact analysis/synthesis and energy preservation are derived from the
Hilbert basis, with coefficient values fixed to actual inner products. -/
def basisRealization (b : HilbertBasis ℕ ℝ H) : CoordinateRealization H where
  equivalence := b.repr.toEquiv.trans l2EncodedEquiv
  physicalEnergy := fun u => ‖u‖ ^ 2
  isometry := by
    intro u
    change energy (b.repr u).val = ‖u‖ ^ 2
    rw [l2_energy, b.repr.norm_map]

theorem basis_coefficients (b : HilbertBasis ℕ ℝ H) (u : H) (i : ℕ) :
    ((basisRealization b).equivalence u).val i = inner ℝ (b i) u :=
  b.repr_apply_apply u i

theorem basis_synthesis (b : HilbertBasis ℕ ℝ H) (a : EncodedState) :
    HasSum (fun i => a.val i • b i) ((basisRealization b).equivalence.symm a) :=
  b.hasSum_repr_symm (l2EncodedEquiv.symm a)

theorem basis_energy (b : HilbertBasis ℕ ℝ H) (u : H) :
    (∑' i, (inner ℝ (b i) u) ^ 2) = ‖u‖ ^ 2 := by
  have h := (basisRealization b).isometry u
  change energy ((basisRealization b).equivalence u).val = ‖u‖ ^ 2 at h
  simpa only [energy, basis_coefficients] using h

theorem basis_distance (b : HilbertBasis ℕ ℝ H) (u v : H) :
    squaredDistance ((basisRealization b).equivalence u).val
      ((basisRealization b).equivalence v).val = ‖u - v‖ ^ 2 := by
  have he : (fun i => ((basisRealization b).equivalence u).val i -
      ((basisRealization b).equivalence v).val i) =
      ((basisRealization b).equivalence (u - v)).val := by
    funext i
    simp only [basis_coefficients, inner_sub_right]
  rw [squaredDistance, he]
  exact (basisRealization b).isometry (u - v)

variable [CompleteSpace H]

/-- The only static Hilbert entrance data are an orthonormal sequence and its
dense span. No coordinate bijection or Parseval identity is assumed. -/
def orthonormalRealization (v : ℕ → H) (hv : Orthonormal ℝ v)
    (hdense : ⊤ ≤ (Submodule.span ℝ (Set.range v)).topologicalClosure) :
    CoordinateRealization H :=
  basisRealization (HilbertBasis.mk hv hdense)

theorem orthonormal_coefficients (v : ℕ → H) (hv : Orthonormal ℝ v)
    (hdense : ⊤ ≤ (Submodule.span ℝ (Set.range v)).topologicalClosure)
    (u : H) (i : ℕ) :
    ((orthonormalRealization v hv hdense).equivalence u).val i = inner ℝ (v i) u := by
  simp only [orthonormalRealization, basis_coefficients, HilbertBasis.coe_mk]

theorem orthonormal_energy (v : ℕ → H) (hv : Orthonormal ℝ v)
    (hdense : ⊤ ≤ (Submodule.span ℝ (Set.range v)).topologicalClosure) (u : H) :
    (∑' i, (inner ℝ (v i) u) ^ 2) = ‖u‖ ^ 2 := by
  simpa only [HilbertBasis.coe_mk] using basis_energy (HilbertBasis.mk hv hdense) u


/-- Same-path Leray--Hopf/NSE transport with the entrance supplied only as
Hilbert-space structure, an orthonormal family, and dense span. -/
theorem orthonormal_lh_nse_transport {Test Obs : Type*}
    (v : ℕ → H) (hv : Orthonormal ℝ v)
    (hdense : ⊤ ≤ (Submodule.span ℝ (Set.range v)).topologicalClosure)
    (d : WeakNSEData H Test) (observe : Obs → H → ℝ) (diss : ℝ → ℝ)
    (ν T : ℝ) (u : ℝ → H) :
    let r := orthonormalRealization v hv hdense
    LHNSE (fun a : EncodedState => energy a.val) (encodedWeakData r d)
      (encodedObservations r observe) diss ν T (encodePath r u) ↔
    LHNSE (fun w : H => ‖w‖ ^ 2) d observe diss ν T u :=
  lh_nse_transport (orthonormalRealization v hv hdense) d observe diss ν T u

end NSE.HilbertEntrance
