import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Countable critical readouts

The canonical value is the real supremum of the range of every finite
prefix. Boundedness is used to prove its specification; it is not a field
asserting that a desired limit exists. Monotonicity upgrades the supremum
to convergence of the entire sequence. No spatial Sobolev or time-integral
identification is made in this module.
-/

namespace NSE

open Set Filter
open scoped Topology BigOperators

/-- The exact least-upper-bound relation used by the countable readouts. -/
def IsPrefixTotal (f : ℕ → ℝ) (L : ℝ) : Prop :=
  (∀ n, f n ≤ L) ∧ ∀ C, (∀ n, f n ≤ C) → L ≤ C

/-- A concrete real supremum, supplied by the complete order on `ℝ`. -/
noncomputable def prefixTotal (f : ℕ → ℝ) : ℝ := sSup (Set.range f)

theorem prefixTotal_spec {f : ℕ → ℝ} (hf : BddAbove (Set.range f)) :
    IsPrefixTotal f (prefixTotal f) := by
  constructor
  · intro n
    exact le_csSup hf (Set.mem_range_self n)
  · intro C hC
    apply csSup_le (Set.range_nonempty f)
    rintro x ⟨n, rfl⟩
    exact hC n

theorem prefixTotal_unique {f : ℕ → ℝ} {L K : ℝ}
    (hL : IsPrefixTotal f L) (hK : IsPrefixTotal f K) : L = K :=
  le_antisymm (hL.2 K hK.1) (hK.2 L hL.1)

theorem prefixTotal_le {f : ℕ → ℝ} {C : ℝ} (hC : ∀ n, f n ≤ C) :
    prefixTotal f ≤ C := by
  apply csSup_le (Set.range_nonempty f)
  rintro x ⟨n, rfl⟩
  exact hC n

theorem le_prefixTotal {f : ℕ → ℝ} (hf : BddAbove (Set.range f)) (n : ℕ) :
    f n ≤ prefixTotal f :=
  (prefixTotal_spec hf).1 n

theorem prefixTotal_nonneg {f : ℕ → ℝ} (hf : BddAbove (Set.range f))
    (hzero : 0 ≤ f 0) : 0 ≤ prefixTotal f :=
  le_trans hzero (le_prefixTotal hf 0)

theorem bounded_prefixTotal {f : ℕ → ℝ} {C : ℝ}
    (hzero : 0 ≤ f 0) (hC : ∀ n, f n ≤ C) :
    0 ≤ prefixTotal f ∧ prefixTotal f ≤ C ∧ IsPrefixTotal f (prefixTotal f) := by
  have hf : BddAbove (Set.range f) := ⟨C, by
    rintro x ⟨n, rfl⟩
    exact hC n⟩
  exact ⟨prefixTotal_nonneg hf hzero, prefixTotal_le hC, prefixTotal_spec hf⟩

/-- A monotone sequence converges to any value satisfying the exact LUB
relation. This does not assert that a nonmonotone prefix family converges. -/
theorem monotone_tendsto_of_prefixTotal {f : ℕ → ℝ} {L : ℝ}
    (hmono : Monotone f) (hL : IsPrefixTotal f L) :
    Tendsto f atTop (𝓝 L) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hex : ∃ n, a < f n := by
      by_contra h
      have hupper : ∀ n, f n ≤ a := by
        intro n
        exact le_of_not_gt (fun hn => h ⟨n, hn⟩)
      exact (not_le_of_gt ha) (hL.2 a hupper)
    obtain ⟨n, hn⟩ := hex
    exact eventually_atTop.2 ⟨n, fun m hnm => lt_of_lt_of_le hn (hmono hnm)⟩
  · intro b hb
    exact Filter.Eventually.of_forall fun n => lt_of_le_of_lt (hL.1 n) hb

theorem monotone_tendsto_prefixTotal {f : ℕ → ℝ}
    (hmono : Monotone f) (hf : BddAbove (Set.range f)) :
    Tendsto f atTop (𝓝 (prefixTotal f)) :=
  monotone_tendsto_of_prefixTotal hmono (prefixTotal_spec hf)

theorem bounded_monotone_completion {f : ℕ → ℝ} {C : ℝ}
    (hzero : 0 ≤ f 0) (hmono : Monotone f) (hC : ∀ n, f n ≤ C) :
    0 ≤ prefixTotal f ∧ prefixTotal f ≤ C ∧
      IsPrefixTotal f (prefixTotal f) ∧ Tendsto f atTop (𝓝 (prefixTotal f)) := by
  obtain ⟨h0, hbound, hspec⟩ := bounded_prefixTotal hzero hC
  exact ⟨h0, hbound, hspec, monotone_tendsto_of_prefixTotal hmono hspec⟩

/-- Ordinary derivatives with nonnegative density give monotonicity on the
actual half-open time interval. The endpoint `T` is not used. -/
theorem primitive_monotone_on_halfopen {T : ℝ} {F f : ℝ → ℝ}
    (hderiv : ∀ t, 0 ≤ t → t < T → HasDerivAt F (f t) t)
    (hnonneg : ∀ t, 0 ≤ t → t < T → 0 ≤ f t) :
    MonotoneOn F (Set.Ico 0 T) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 T)
  · intro t ht
    exact (hderiv t ht.1 ht.2).continuousAt.continuousWithinAt
  · intro t ht
    have hmem : t ∈ Set.Ico 0 T := interior_subset ht
    exact (hderiv t hmem.1 hmem.2).hasDerivWithinAt
  · intro t ht
    have hmem : t ∈ Set.Ico 0 T := interior_subset ht
    exact hnonneg t hmem.1 hmem.2

theorem primitive_nonneg_on_halfopen {T : ℝ} {F f : ℝ → ℝ}
    (hzero : F 0 = 0)
    (hderiv : ∀ t, 0 ≤ t → t < T → HasDerivAt F (f t) t)
    (hnonneg : ∀ t, 0 ≤ t → t < T → 0 ≤ f t)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) : 0 ≤ F t := by
  have h := primitive_monotone_on_halfopen hderiv hnonneg
    ⟨le_rfl, lt_of_le_of_lt ht0 htT⟩ ⟨ht0, htT⟩ ht0
  simpa only [hzero] using h

/-- Cutoff monotonicity is derived from the difference of the genuine
primitives, with their common initial value, rather than postulated. -/
theorem cumulative_cutoff_monotone {T : ℝ} {D density : ℕ → ℝ → ℝ}
    (hzero : ∀ N, D N 0 = 0)
    (hderiv : ∀ N t, 0 ≤ t → t < T → HasDerivAt (D N) (density N t) t)
    (hincreasing : ∀ t, 0 ≤ t → t < T → Monotone (fun N => density N t))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    Monotone (fun N => D N t) := by
  intro N K hNK
  have hdiff : 0 ≤ D K t - D N t :=
    primitive_nonneg_on_halfopen
      (F := fun s => D K s - D N s)
      (f := fun s => density K s - density N s)
      (by simp [hzero])
      (fun s hs0 hsT => (hderiv K s hs0 hsT).sub (hderiv N s hs0 hsT))
      (fun s hs0 hsT => sub_nonneg.mpr (hincreasing s hs0 hsT hNK)) ht0 htT
  exact sub_nonneg.mp hdiff

/-- A cutoff-independent cap, together with ordinary primitive identities,
constructs the infinite cumulative dissipation and its actual cutoff limit. -/
theorem cumulative_completion {T C t : ℝ} {D density : ℕ → ℝ → ℝ}
    (hzero : ∀ N, D N 0 = 0)
    (hderiv : ∀ N s, 0 ≤ s → s < T → HasDerivAt (D N) (density N s) s)
    (hnonneg : ∀ N s, 0 ≤ s → s < T → 0 ≤ density N s)
    (hincreasing : ∀ s, 0 ≤ s → s < T → Monotone (fun N => density N s))
    (ht0 : 0 ≤ t) (htT : t < T) (hC : ∀ N, D N t ≤ C) :
    0 ≤ prefixTotal (fun N => D N t) ∧ prefixTotal (fun N => D N t) ≤ C ∧
      IsPrefixTotal (fun N => D N t) (prefixTotal (fun N => D N t)) ∧
      Tendsto (fun N => D N t) atTop (𝓝 (prefixTotal (fun N => D N t))) := by
  exact bounded_monotone_completion
    (primitive_nonneg_on_halfopen (hzero 0) (hderiv 0) (hnonneg 0) ht0 htT)
    (cumulative_cutoff_monotone hzero hderiv hincreasing ht0 htT) hC

/-- Weighted squared coefficients below a spatial cutoff. -/
def weightedPrefix (w a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, w i * (a i) ^ 2

@[simp] theorem weightedPrefix_zero (w a : ℕ → ℝ) : weightedPrefix w a 0 = 0 := by
  simp [weightedPrefix]

theorem weightedPrefix_succ (w a : ℕ → ℝ) (N : ℕ) :
    weightedPrefix w a (N + 1) = weightedPrefix w a N + w N * (a N) ^ 2 := by
  simp [weightedPrefix, Finset.sum_range_succ]

theorem weightedPrefix_nonneg {w a : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (N : ℕ) :
    0 ≤ weightedPrefix w a N := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i) (sq_nonneg (a i))

theorem weightedPrefix_monotone {w a : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) :
    Monotone (weightedPrefix w a) := by
  intro N K hNK
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNK)
  intro i hi hnot
  exact mul_nonneg (hw i) (sq_nonneg (a i))

def WeightedTotal (w a : ℕ → ℝ) (L : ℝ) : Prop :=
  IsPrefixTotal (weightedPrefix w a) L

noncomputable def weightedTotal (w a : ℕ → ℝ) : ℝ := prefixTotal (weightedPrefix w a)

theorem weighted_completion {w a : ℕ → ℝ} {C : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hC : ∀ N, weightedPrefix w a N ≤ C) :
    0 ≤ weightedTotal w a ∧ weightedTotal w a ≤ C ∧
      WeightedTotal w a (weightedTotal w a) ∧
      Tendsto (weightedPrefix w a) atTop (𝓝 (weightedTotal w a)) := by
  apply bounded_monotone_completion
  · simp
  · exact weightedPrefix_monotone hw
  · exact hC

/-- The same weighted square energy is the ordinary square energy of the
rescaled coefficient vector, including weights equal to zero. -/
noncomputable def weightedVector (w a : ℕ → ℝ) (i : ℕ) : ℝ := Real.sqrt (w i) * a i

theorem weightedPrefix_eq_squarePrefix {w a : ℕ → ℝ}
    (hw : ∀ i, 0 ≤ w i) (N : ℕ) :
    weightedPrefix w a N = weightedPrefix (fun _ => 1) (weightedVector w a) N := by
  apply Finset.sum_congr rfl
  intro i hi
  simp only [weightedVector, one_mul, mul_pow, Real.sq_sqrt (hw i)]

theorem weighted_square_completion {w a : ℕ → ℝ} {C : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hC : ∀ N, weightedPrefix w a N ≤ C) :
    WeightedTotal (fun _ => 1) (weightedVector w a) (weightedTotal w a) ∧
      Tendsto (weightedPrefix (fun _ => 1) (weightedVector w a))
        atTop (𝓝 (weightedTotal w a)) := by
  have heq : weightedPrefix (fun _ => 1) (weightedVector w a) = weightedPrefix w a := by
    funext N
    exact (weightedPrefix_eq_squarePrefix hw N).symm
  obtain ⟨_, _, htotal, hlim⟩ := weighted_completion hw hC
  change IsPrefixTotal (weightedPrefix (fun _ => 1) (weightedVector w a))
    (weightedTotal w a) ∧ _
  rw [heq]
  exact ⟨htotal, hlim⟩

/-- The same total is the sum in mathlib's native infinite-sum API. -/
theorem weighted_hasSum {w a : ℕ → ℝ} {C : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hC : ∀ N, weightedPrefix w a N ≤ C) :
    HasSum (fun i => w i * (a i) ^ 2) (weightedTotal w a) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun i => mul_nonneg (hw i) (sq_nonneg (a i))) _).2
  exact (weighted_completion hw hC).2.2.2

theorem weighted_tsum {w a : ℕ → ℝ} {C : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hC : ∀ N, weightedPrefix w a N ≤ C) :
    (∑' i, w i * (a i) ^ 2) = weightedTotal w a :=
  (weighted_hasSum hw hC).tsum_eq

theorem weighted_square_hasSum {w a : ℕ → ℝ} {C : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hC : ∀ N, weightedPrefix w a N ≤ C) :
    HasSum (fun i => (weightedVector w a i) ^ 2) (weightedTotal w a) := by
  have heq : (fun i => (weightedVector w a i) ^ 2) =
      (fun i => w i * (a i) ^ 2) := by
    funext i
    simp only [weightedVector, mul_pow, Real.sq_sqrt (hw i)]
  rw [heq]
  exact weighted_hasSum hw hC

/-- Bounded weighted energy constructs membership in mathlib's actual
`ℓ²` coefficient space after the canonical square-root rescaling. -/
theorem weightedVector_memℓp {w a : ℕ → ℝ} {C : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hC : ∀ N, weightedPrefix w a N ≤ C) :
    Memℓp (weightedVector w a) 2 := by
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    using (weighted_square_hasSum hw hC).summable

end NSE
