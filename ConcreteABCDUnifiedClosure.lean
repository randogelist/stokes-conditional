import Mathlib
import Fefferman.Analysis
import Fefferman.Statements

open scoped Topology

namespace Fefferman
namespace ConcreteReal

abbrev RSpace := Fin 3 → ℝ
abbrev RVector := Fin 3 → ℝ
abbrev RInitial := RSpace → RVector
abbrev RVelocity := RSpace → ℝ → RVector
abbrev RForce := RVelocity
abbrev RPressure := RSpace → ℝ → ℝ

def normSq3 (v : RVector) : ℝ :=
  v 0 * v 0 + v 1 * v 1 + v 2 * v 2

noncomputable def euclideanNorm3 (v : RVector) : ℝ :=
  Real.sqrt (normSq3 v)

def basisDirection (j : Fin 3) : RSpace :=
  fun i => if i = j then 1 else 0

noncomputable def spatialDerivative
    (j : Fin 3) (f : RSpace → ℝ) (x : RSpace) : ℝ :=
  (fderiv ℝ f x) (basisDirection j)

noncomputable def timeDerivative (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

def smoothSpatialReal (f : RSpace → ℝ) : Prop :=
  ContDiff ℝ ⊤ f

def smoothClosedHalfSpaceReal (f : RSpace → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => f z.1 z.2)
    {z : RSpace × ℝ | 0 ≤ z.2}

def squareIntegrableReal (u : RSpace → RVector) : Prop :=
  MeasureTheory.Integrable (fun x => normSq3 (u x))

noncomputable def integralNormSqReal (u : RSpace → RVector) : ℝ :=
  ∫ x, normSq3 (u x)

@[reducible] noncomputable def realAnalysis : Analysis where
  Scalar := ℝ
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := fun x => -x
  le := (· ≤ ·)
  lt := (· < ·)
  norm3 := euclideanNorm3
  dx := spatialDerivative
  dt := timeDerivative
  smoothSpatial := smoothSpatialReal
  smoothClosedHalfSpace := smoothClosedHalfSpaceReal
  squareIntegrable := squareIntegrableReal
  integralNormSq := integralNormSqReal

def integerShift (k : Fin 3 → ℤ) (x : RSpace) : RSpace :=
  fun j => x j + (k j : ℝ)

def scaleSpace (lam : ℝ) (x : RSpace) : RSpace :=
  fun j => lam * x j

def rescaleTime (lam t₀ t : ℝ) : ℝ :=
  lam ^ 2 * (t - t₀)

def rescaleForce (lam t₀ : ℝ) (f : RForce) : RForce :=
  fun x t i =>
    lam ^ 3 * f (scaleSpace lam x) (rescaleTime lam t₀ t) i

noncomputable def integerPeriodizeForce (f : RForce) : RForce :=
  fun x t i =>
    ∑' k : (Fin 3 → ℤ), f (integerShift k x) t i

noncomputable def corollary106PeriodicForce
    (lam t₀ : ℝ) (f : RForce) : RForce :=
  integerPeriodizeForce (rescaleForce lam t₀ f)

theorem rescaleForce_apply
    (lam t₀ : ℝ) (f : RForce) (x : RSpace) (t : ℝ) (i : Fin 3) :
    rescaleForce lam t₀ f x t i =
      lam ^ 3 * f (scaleSpace lam x) (rescaleTime lam t₀ t) i := by
  rfl

theorem corollary106PeriodicForce_apply
    (lam t₀ : ℝ) (f : RForce) (x : RSpace) (t : ℝ) (i : Fin 3) :
    corollary106PeriodicForce lam t₀ f x t i =
      ∑' k : (Fin 3 → ℤ),
        rescaleForce lam t₀ f (integerShift k x) t i := by
  rfl

theorem real_zeroForce_apply
    (x : Space realAnalysis) (t : realAnalysis.Scalar) (i : Fin 3) :
    zeroForce realAnalysis x t i = realAnalysis.zero := by
  rfl

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.rescaleForce_apply
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForce_apply
#print axioms Fefferman.ConcreteReal.real_zeroForce_apply


namespace Fefferman
namespace ConcreteReal

abbrev Lattice3 := Fin 3 → ℤ

def latticeUnit (j : Fin 3) : Lattice3 :=
  fun i => if i = j then 1 else 0

def latticeTranslate (j : Fin 3) (k : Lattice3) : Lattice3 :=
  fun i => k i + latticeUnit j i

def latticeTranslateBack (j : Fin 3) (k : Lattice3) : Lattice3 :=
  fun i => k i - latticeUnit j i

def latticeTranslateEquiv (j : Fin 3) : Lattice3 ≃ Lattice3 where
  toFun := latticeTranslate j
  invFun := latticeTranslateBack j
  left_inv := by
    intro k
    funext i
    by_cases h : i = j
    · simp [latticeTranslate, latticeTranslateBack, latticeUnit, h]
    · simp [latticeTranslate, latticeTranslateBack, latticeUnit, h]
  right_inv := by
    intro k
    funext i
    by_cases h : i = j
    · simp [latticeTranslate, latticeTranslateBack, latticeUnit, h]
    · simp [latticeTranslate, latticeTranslateBack, latticeUnit, h]

theorem integerShift_latticeTranslate
    (j : Fin 3) (k : Lattice3) (x : RSpace) :
    integerShift (latticeTranslate j k) x =
      integerShift k (unitShift realAnalysis x j) := by
  funext i
  by_cases h : i = j
  · subst i
    simp [integerShift, latticeTranslate, latticeUnit, unitShift, realAnalysis]
    ring
  · simp [integerShift, latticeTranslate, latticeUnit, unitShift, realAnalysis, h]

theorem integerPeriodizeForce_unitShift
    (f : RForce) (x : RSpace) (t : ℝ) (j i : Fin 3) :
    integerPeriodizeForce f (unitShift realAnalysis x j) t i =
      integerPeriodizeForce f x t i := by
  change
    (∑' k : Lattice3,
      f (integerShift k (unitShift realAnalysis x j)) t i) =
    (∑' k : Lattice3, f (integerShift k x) t i)
  calc
    (∑' k : Lattice3,
      f (integerShift k (unitShift realAnalysis x j)) t i)
        =
      ∑' k : Lattice3,
        f (integerShift (latticeTranslate j k) x) t i := by
          apply tsum_congr
          intro k
          rw [integerShift_latticeTranslate]
    _ =
      ∑' k : Lattice3, f (integerShift k x) t i := by
        exact
          Equiv.tsum_eq
            (latticeTranslateEquiv j)
            (fun k : Lattice3 => f (integerShift k x) t i)

theorem integerPeriodizeForce_periodic (f : RForce) :
    vectorPeriodic realAnalysis (integerPeriodizeForce f) := by
  intro x t ht j
  funext i
  exact integerPeriodizeForce_unitShift f x t j i

theorem corollary106PeriodicForce_periodic
    (lam t₀ : ℝ) (f : RForce) :
    vectorPeriodic realAnalysis
      (corollary106PeriodicForce lam t₀ f) := by
  exact integerPeriodizeForce_periodic (rescaleForce lam t₀ f)

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.integerShift_latticeTranslate
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_unitShift
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_periodic
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForce_periodic


namespace Fefferman
namespace ConcreteReal

def InOpenCube (rho : ℝ) (x : RSpace) : Prop :=
  ∀ j : Fin 3, |x j| < rho

def SpatialCubeSupported (rho : ℝ) (f : RForce) : Prop :=
  ∀ (x : RSpace) (t : ℝ) (i : Fin 3),
    f x t i ≠ 0 → InOpenCube rho x

theorem integerShift_unique_of_openCube
    (rho : ℝ)
    (hrho : 2 * rho < 1)
    {x : RSpace}
    {k l : Lattice3}
    (hk : InOpenCube rho (integerShift k x))
    (hl : InOpenCube rho (integerShift l x)) :
    k = l := by
  funext j
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · have hstepZ : k j + 1 ≤ l j := by
      omega
    have hstepR : (k j : ℝ) + 1 ≤ (l j : ℝ) := by
      exact_mod_cast hstepZ
    have hklo :
        -rho < x j + (k j : ℝ) := by
      simpa [integerShift] using (abs_lt.mp (hk j)).1
    have hlhi :
        x j + (l j : ℝ) < rho := by
      simpa [integerShift] using (abs_lt.mp (hl j)).2
    have hdiff :
        (l j : ℝ) - (k j : ℝ) < 2 * rho := by
      linarith
    linarith
  · have hstepZ : l j + 1 ≤ k j := by
      omega
    have hstepR : (l j : ℝ) + 1 ≤ (k j : ℝ) := by
      exact_mod_cast hstepZ
    have hllo :
        -rho < x j + (l j : ℝ) := by
      simpa [integerShift] using (abs_lt.mp (hl j)).1
    have hkhi :
        x j + (k j : ℝ) < rho := by
      simpa [integerShift] using (abs_lt.mp (hk j)).2
    have hdiff :
        (k j : ℝ) - (l j : ℝ) < 2 * rho := by
      linarith
    linarith

theorem active_translate_unique
    (rho : ℝ)
    (hrho : 2 * rho < 1)
    {f : RForce}
    (hf : SpatialCubeSupported rho f)
    {x : RSpace}
    {t : ℝ}
    {i : Fin 3}
    {k l : Lattice3}
    (hk : f (integerShift k x) t i ≠ 0)
    (hl : f (integerShift l x) t i ≠ 0) :
    k = l := by
  exact
    integerShift_unique_of_openCube
      rho hrho
      (hf (integerShift k x) t i hk)
      (hf (integerShift l x) t i hl)

theorem integerPeriodizeForce_eq_active
    (rho : ℝ)
    (hrho : 2 * rho < 1)
    {f : RForce}
    (hf : SpatialCubeSupported rho f)
    {x : RSpace}
    {t : ℝ}
    {i : Fin 3}
    {k : Lattice3}
    (hk : f (integerShift k x) t i ≠ 0) :
    integerPeriodizeForce f x t i =
      f (integerShift k x) t i := by
  change
    (∑' l : Lattice3, f (integerShift l x) t i) =
      f (integerShift k x) t i
  apply tsum_eq_single k
  intro l hlk
  by_contra hnonzero
  have hEq :
      l = k :=
    active_translate_unique
      rho hrho hf hnonzero hk
  exact hlk hEq

theorem integerPeriodizeForce_eq_zero_of_no_active
    {f : RForce}
    {x : RSpace}
    {t : ℝ}
    {i : Fin 3}
    (hzero :
      ∀ k : Lattice3,
        f (integerShift k x) t i = 0) :
    integerPeriodizeForce f x t i = 0 := by
  change
    (∑' k : Lattice3, f (integerShift k x) t i) = 0
  simp [hzero]

theorem active_translate_subsingleton
    (rho : ℝ)
    (hrho : 2 * rho < 1)
    {f : RForce}
    (hf : SpatialCubeSupported rho f)
    (x : RSpace)
    (t : ℝ)
    (i : Fin 3) :
    Set.Subsingleton
      {k : Lattice3 | f (integerShift k x) t i ≠ 0} := by
  intro k hk l hl
  exact
    active_translate_unique
      rho hrho hf hk hl

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.integerShift_unique_of_openCube
#print axioms Fefferman.ConcreteReal.active_translate_unique
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_eq_active
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_eq_zero_of_no_active
#print axioms Fefferman.ConcreteReal.active_translate_subsingleton


namespace Fefferman
namespace ConcreteReal

def CloseSpace (eps : ℝ) (x y : RSpace) : Prop :=
  ∀ j : Fin 3, |y j - x j| < eps

theorem inOpenCube_mono
    {rho sigma : ℝ}
    (hrs : rho ≤ sigma)
    {x : RSpace}
    (hx : InOpenCube rho x) :
    InOpenCube sigma x := by
  intro j
  exact lt_of_lt_of_le (hx j) hrs

theorem integerShift_closeSpace
    {eps : ℝ}
    {x y : RSpace}
    (k : Lattice3)
    (hxy : CloseSpace eps x y) :
    CloseSpace eps (integerShift k x) (integerShift k y) := by
  intro j
  have hsub :
      integerShift k y j - integerShift k x j =
        y j - x j := by
    simp [integerShift]
  rw [hsub]
  exact hxy j

theorem inOpenCube_of_close_with_buffer
    {sigma eps : ℝ}
    {x y : RSpace}
    (hbuffer : ∀ j : Fin 3, |x j| + eps < sigma)
    (hxy : CloseSpace eps x y) :
    InOpenCube sigma y := by
  intro j
  calc
    |y j|
        = |x j + (y j - x j)| := by
            congr 1
            ring
    _ ≤ |x j| + |y j - x j| := by
          simpa only [Real.norm_eq_abs] using
            (norm_add_le (x j) (y j - x j))
    _ < |x j| + eps := by
          linarith [hxy j]
    _ < sigma := hbuffer j

def cubeSlack (sigma : ℝ) (x : RSpace) : ℝ :=
  min (sigma - |x 0|)
    (min (sigma - |x 1|) (sigma - |x 2|))

theorem cubeSlack_pos
    {sigma : ℝ}
    {x : RSpace}
    (hx : InOpenCube sigma x) :
    0 < cubeSlack sigma x := by
  have h0 : 0 < sigma - |x 0| := sub_pos.mpr (hx 0)
  have h1 : 0 < sigma - |x 1| := sub_pos.mpr (hx 1)
  have h2 : 0 < sigma - |x 2| := sub_pos.mpr (hx 2)
  unfold cubeSlack
  exact
    (lt_min_iff).2
      ⟨h0, (lt_min_iff).2 ⟨h1, h2⟩⟩

theorem cubeSlack_le_slack
    (sigma : ℝ)
    (x : RSpace)
    (j : Fin 3) :
    cubeSlack sigma x ≤ sigma - |x j| := by
  fin_cases j <;> simp [cubeSlack]

theorem exists_positive_cube_buffer
    {sigma : ℝ}
    {x : RSpace}
    (hx : InOpenCube sigma x) :
    ∃ eps : ℝ,
      0 < eps ∧
      ∀ j : Fin 3, |x j| + eps < sigma := by
  let delta := cubeSlack sigma x
  have hdelta : 0 < delta := by
    exact cubeSlack_pos hx
  refine ⟨delta / 2, by linarith, ?_⟩
  intro j
  have hle :
      delta ≤ sigma - |x j| := by
    exact cubeSlack_le_slack sigma x j
  linarith

theorem integerPeriodizeForce_eq_translate_on_box
    (rho sigma eps : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hf : SpatialCubeSupported rho f)
    {x y : RSpace}
    {k : Lattice3}
    (hbuffer :
      ∀ j : Fin 3,
        |integerShift k x j| + eps < sigma)
    (hxy : CloseSpace eps x y) :
    ∀ (t : ℝ) (i : Fin 3),
      integerPeriodizeForce f y t i =
        f (integerShift k y) t i := by
  intro t i
  have hcloseShift :
      CloseSpace eps
        (integerShift k x)
        (integerShift k y) :=
    integerShift_closeSpace k hxy
  have hkSigma :
      InOpenCube sigma (integerShift k y) :=
    inOpenCube_of_close_with_buffer hbuffer hcloseShift
  change
    (∑' l : Lattice3, f (integerShift l y) t i) =
      f (integerShift k y) t i
  apply tsum_eq_single k
  intro l hlk
  by_contra hnonzero
  have hlRho :
      InOpenCube rho (integerShift l y) :=
    hf (integerShift l y) t i hnonzero
  have hlSigma :
      InOpenCube sigma (integerShift l y) :=
    inOpenCube_mono (le_of_lt hrs) hlRho
  have heq :
      l = k :=
    integerShift_unique_of_openCube
      sigma hsigma hlSigma hkSigma
  exact hlk heq

theorem integerPeriodizeForce_eq_zero_on_buffer_gap
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    {f : RForce}
    (hf : SpatialCubeSupported rho f)
    {x y : RSpace}
    (hno :
      ∀ k : Lattice3,
        ¬ InOpenCube sigma (integerShift k x))
    (hxy : CloseSpace (sigma - rho) x y) :
    ∀ (t : ℝ) (i : Fin 3),
      integerPeriodizeForce f y t i = 0 := by
  classical
  intro t i
  apply integerPeriodizeForce_eq_zero_of_no_active
  intro k
  by_contra hnonzero
  have hyRho :
      InOpenCube rho (integerShift k y) :=
    hf (integerShift k y) t i hnonzero
  have hex :
      ∃ j : Fin 3,
        sigma ≤ |integerShift k x j| := by
    simpa only [InOpenCube, not_forall, not_lt] using hno k
  rcases hex with ⟨j, hxj⟩
  have hcloseShift :
      CloseSpace (sigma - rho)
        (integerShift k x)
        (integerShift k y) :=
    integerShift_closeSpace k hxy
  have htri :
      |integerShift k x j| ≤
        |integerShift k y j| +
          |integerShift k y j - integerShift k x j| := by
    calc
      |integerShift k x j|
          =
        |integerShift k y j +
          (integerShift k x j - integerShift k y j)| := by
            congr 1
            ring
      _ ≤
        |integerShift k y j| +
          |integerShift k x j - integerShift k y j| := by
            simpa only [Real.norm_eq_abs] using
              (norm_add_le
                (integerShift k y j)
                (integerShift k x j - integerShift k y j))
      _ =
        |integerShift k y j| +
          |integerShift k y j - integerShift k x j| := by
            rw [abs_sub_comm]
  have hygt :
      rho < |integerShift k y j| := by
    linarith [hcloseShift j]
  exact (not_lt_of_ge (le_of_lt hygt)) (hyRho j)

theorem integerPeriodizeForce_local_single_or_zero
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hf : SpatialCubeSupported rho f)
    (x : RSpace) :
    ∃ eps : ℝ,
      0 < eps ∧
      ((∃ k : Lattice3,
          ∀ y : RSpace,
            CloseSpace eps x y →
            ∀ (t : ℝ) (i : Fin 3),
              integerPeriodizeForce f y t i =
                f (integerShift k y) t i)
       ∨
       (∀ y : RSpace,
          CloseSpace eps x y →
          ∀ (t : ℝ) (i : Fin 3),
            integerPeriodizeForce f y t i = 0)) := by
  classical
  by_cases hk :
      ∃ k : Lattice3,
        InOpenCube sigma (integerShift k x)
  · rcases hk with ⟨k, hkSigma⟩
    rcases exists_positive_cube_buffer hkSigma with
      ⟨eps, heps, hbuffer⟩
    refine ⟨eps, heps, Or.inl ⟨k, ?_⟩⟩
    intro y hxy
    exact
      integerPeriodizeForce_eq_translate_on_box
        rho sigma eps hrs hsigma hf hbuffer hxy
  · have hgap : 0 < sigma - rho := sub_pos.mpr hrs
    have hno :
        ∀ k : Lattice3,
          ¬ InOpenCube sigma (integerShift k x) := by
      intro k hkmem
      exact hk ⟨k, hkmem⟩
    refine ⟨sigma - rho, hgap, Or.inr ?_⟩
    intro y hxy
    exact
      integerPeriodizeForce_eq_zero_on_buffer_gap
        rho sigma hrs hf hno hxy

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.exists_positive_cube_buffer
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_eq_translate_on_box
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_eq_zero_on_buffer_gap
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_local_single_or_zero


namespace Fefferman
namespace ConcreteReal

def SpaceBox (eps : ℝ) (x : RSpace) : Set RSpace :=
  {y | CloseSpace eps x y}

theorem isOpen_spaceBox
    (eps : ℝ)
    (x : RSpace) :
    IsOpen (SpaceBox eps x) := by
  have hcoord :
      ∀ j : Fin 3,
        IsOpen {y : RSpace | |y j - x j| < eps} := by
    intro j
    exact
      isOpen_lt
        (((continuous_apply j).sub continuous_const).abs)
        continuous_const
  have hEq :
      SpaceBox eps x =
        ⋂ j : Fin 3, {y : RSpace | |y j - x j| < eps} := by
    ext y
    simp [SpaceBox, CloseSpace]
  rw [hEq]
  exact isOpen_iInter_of_finite hcoord

def SpaceTimeBox
    (eps : ℝ)
    (x : RSpace) :
    Set (RSpace × ℝ) :=
  Prod.fst ⁻¹' SpaceBox eps x

theorem isOpen_spaceTimeBox
    (eps : ℝ)
    (x : RSpace) :
    IsOpen (SpaceTimeBox eps x) := by
  exact (isOpen_spaceBox eps x).preimage continuous_fst

theorem self_mem_spaceTimeBox
    {eps : ℝ}
    (heps : 0 < eps)
    (x : RSpace)
    (t : ℝ) :
    (x, t) ∈ SpaceTimeBox eps x := by
  change CloseSpace eps x x
  intro j
  simpa using heps

theorem eventually_closeSpace
    {eps : ℝ}
    (heps : 0 < eps)
    (x : RSpace)
    (t : ℝ) :
    ∀ᶠ z : RSpace × ℝ in 𝓝 (x, t),
      CloseSpace eps x z.1 := by
  have hnhds :
      SpaceTimeBox eps x ∈ 𝓝 (x, t) :=
    (isOpen_spaceTimeBox eps x).mem_nhds
      (self_mem_spaceTimeBox heps x t)
  filter_upwards [hnhds] with z hz
  exact hz

def latticeAsSpace (k : Lattice3) : RSpace :=
  fun j => (k j : ℝ)

theorem integerShift_eq_add
    (k : Lattice3)
    (x : RSpace) :
    integerShift k x = x + latticeAsSpace k := by
  funext j
  rfl

def spaceTimeIntegerShift
    (k : Lattice3)
    (z : RSpace × ℝ) :
    RSpace × ℝ :=
  (z.1 + latticeAsSpace k, z.2)

theorem spaceTimeIntegerShift_contDiff
    (k : Lattice3) :
    ContDiff ℝ ⊤ (spaceTimeIntegerShift k) := by
  exact
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd

def GloballySmoothForce (f : RForce) : Prop :=
  ∀ i : Fin 3,
    ContDiff ℝ ⊤
      (fun z : RSpace × ℝ => f z.1 z.2 i)

theorem translatedForceComponent_contDiff
    {f : RForce}
    (hf : GloballySmoothForce f)
    (k : Lattice3)
    (i : Fin 3) :
    ContDiff ℝ ⊤
      (fun z : RSpace × ℝ =>
        f (integerShift k z.1) z.2 i) := by
  have hcomp :
      ContDiff ℝ ⊤
        (fun z : RSpace × ℝ =>
          f (z.1 + latticeAsSpace k) z.2 i) := by
    exact
      (hf i).comp (spaceTimeIntegerShift_contDiff k)
  simpa only [integerShift_eq_add] using hcomp

theorem integerPeriodizeForce_component_contDiff
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (hsmooth : GloballySmoothForce f)
    (i : Fin 3) :
    ContDiff ℝ ⊤
      (fun z : RSpace × ℝ =>
        integerPeriodizeForce f z.1 z.2 i) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases
      integerPeriodizeForce_local_single_or_zero
        rho sigma hrs hsigma hsupp z.1 with
    ⟨eps, heps, hlocal⟩
  rcases hlocal with hcopy | hzero
  · rcases hcopy with ⟨k, hk⟩
    have hsource :
        ContDiffAt ℝ ⊤
          (fun w : RSpace × ℝ =>
            f (integerShift k w.1) w.2 i) z :=
      (translatedForceComponent_contDiff hsmooth k i).contDiffAt
    apply hsource.congr_of_eventuallyEq
    filter_upwards
      [eventually_closeSpace heps z.1 z.2] with w hw
    exact hk w.1 hw w.2 i
  · have hconst :
        ContDiffAt ℝ ⊤
          (fun _ : RSpace × ℝ => (0 : ℝ)) z :=
      contDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards
      [eventually_closeSpace heps z.1 z.2] with w hw
    exact hzero w.1 hw w.2 i

theorem integerPeriodizeForce_globallySmooth
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (hsmooth : GloballySmoothForce f) :
    GloballySmoothForce (integerPeriodizeForce f) := by
  intro i
  exact
    integerPeriodizeForce_component_contDiff
      rho sigma hrs hsigma hsupp hsmooth i

theorem globallySmoothForce_vectorSmooth
    {f : RForce}
    (hf : GloballySmoothForce f) :
    vectorSmooth realAnalysis f := by
  intro i
  change
    ContDiffOn ℝ ⊤
      (fun z : RSpace × ℝ => f z.1 z.2 i)
      {z : RSpace × ℝ | 0 ≤ z.2}
  exact (hf i).contDiffOn

theorem integerPeriodizeForce_vectorSmooth
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (hsmooth : GloballySmoothForce f) :
    vectorSmooth realAnalysis (integerPeriodizeForce f) := by
  exact
    globallySmoothForce_vectorSmooth
      (integerPeriodizeForce_globallySmooth
        rho sigma hrs hsigma hsupp hsmooth)

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.isOpen_spaceBox
#print axioms Fefferman.ConcreteReal.eventually_closeSpace
#print axioms Fefferman.ConcreteReal.spaceTimeIntegerShift_contDiff
#print axioms Fefferman.ConcreteReal.translatedForceComponent_contDiff
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_component_contDiff
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_globallySmooth
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_vectorSmooth


namespace Fefferman
namespace ConcreteReal

theorem eventually_closeSpace_spatial
    {eps : ℝ}
    (heps : 0 < eps)
    (x : RSpace) :
    ∀ᶠ y : RSpace in 𝓝 x,
      CloseSpace eps x y := by
  have hmem :
      SpaceBox eps x ∈ 𝓝 x :=
    (isOpen_spaceBox eps x).mem_nhds (by
      change CloseSpace eps x x
      intro j
      simpa using heps)
  filter_upwards [hmem] with y hy
  exact hy

theorem integerPeriodizeForce_spatial_fderiv_local
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (x : RSpace)
    (t : ℝ)
    (i : Fin 3) :
    (∃ k : Lattice3,
      fderiv ℝ
          (fun y : RSpace => integerPeriodizeForce f y t i) x
        =
      fderiv ℝ
          (fun y : RSpace => f (integerShift k y) t i) x)
    ∨
    fderiv ℝ
        (fun y : RSpace => integerPeriodizeForce f y t i) x
      = 0 := by
  rcases
      integerPeriodizeForce_local_single_or_zero
        rho sigma hrs hsigma hsupp x with
    ⟨eps, heps, hlocal⟩
  rcases hlocal with hcopy | hzero
  · rcases hcopy with ⟨k, hk⟩
    left
    refine ⟨k, ?_⟩
    have heq :
        (fun y : RSpace =>
          integerPeriodizeForce f y t i)
          =ᶠ[𝓝 x]
        (fun y : RSpace =>
          f (integerShift k y) t i) := by
      filter_upwards
        [eventually_closeSpace_spatial heps x] with y hy
      exact hk y hy t i
    exact heq.fderiv_eq
  · right
    have heq :
        (fun y : RSpace =>
          integerPeriodizeForce f y t i)
          =ᶠ[𝓝 x]
        (fun _ : RSpace => (0 : ℝ)) := by
      filter_upwards
        [eventually_closeSpace_spatial heps x] with y hy
      exact hzero y hy t i
    have hfd :
        fderiv ℝ
            (fun y : RSpace =>
              integerPeriodizeForce f y t i) x
          =
        fderiv ℝ
            (fun _ : RSpace => (0 : ℝ)) x :=
      heq.fderiv_eq
    simpa using hfd

theorem fderiv_add_lattice
    (k : Lattice3)
    (x : RSpace) :
    fderiv ℝ
      (fun y : RSpace => y + latticeAsSpace k) x
      =
    ContinuousLinearMap.id ℝ RSpace := by
  rw [fderiv_add_const]
  simp

theorem translatedSpatialDerivative_eq
    (k : Lattice3)
    (j : Fin 3)
    {g : RSpace → ℝ}
    (x : RSpace)
    (hg :
      DifferentiableAt ℝ g (integerShift k x)) :
    spatialDerivative j
        (fun y : RSpace => g (integerShift k y)) x
      =
    spatialDerivative j g (integerShift k x) := by
  unfold spatialDerivative
  have hfun :
      (fun y : RSpace => g (integerShift k y))
        =
      g ∘ (fun y : RSpace => y + latticeAsSpace k) := by
    funext y
    simp [Function.comp_apply, integerShift_eq_add]
  rw [hfun]
  have hg' :
      DifferentiableAt ℝ g (x + latticeAsSpace k) := by
    simpa only [integerShift_eq_add] using hg
  have hshift :
      DifferentiableAt ℝ
        (fun y : RSpace => y + latticeAsSpace k) x := by
    fun_prop
  have hcomp :
      fderiv ℝ
          (g ∘ (fun y : RSpace => y + latticeAsSpace k)) x
        =
      (fderiv ℝ g (x + latticeAsSpace k)).comp
        (fderiv ℝ
          (fun y : RSpace => y + latticeAsSpace k) x) :=
    fderiv_comp x hg' hshift
  rw [hcomp, fderiv_add_lattice]
  simp [integerShift_eq_add]

theorem integerPeriodizeForce_spatialDerivative_local
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (x : RSpace)
    (t : ℝ)
    (i j : Fin 3) :
    (∃ k : Lattice3,
      spatialDerivative j
          (fun y : RSpace =>
            integerPeriodizeForce f y t i) x
        =
      spatialDerivative j
          (fun y : RSpace =>
            f (integerShift k y) t i) x)
    ∨
    spatialDerivative j
        (fun y : RSpace =>
          integerPeriodizeForce f y t i) x
      = 0 := by
  rcases
      integerPeriodizeForce_spatial_fderiv_local
        rho sigma hrs hsigma hsupp x t i with
    ⟨k, hk⟩ | hzero
  · left
    refine ⟨k, ?_⟩
    exact
      congrArg
        (fun L : RSpace →L[ℝ] ℝ =>
          L (basisDirection j))
        hk
  · right
    have h :=
      congrArg
        (fun L : RSpace →L[ℝ] ℝ =>
          L (basisDirection j))
        hzero
    simpa [spatialDerivative] using h

theorem integerPeriodizeForce_timeDerivative_local
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (x : RSpace)
    (t : ℝ)
    (i : Fin 3) :
    (∃ k : Lattice3,
      timeDerivative
          (fun s : ℝ =>
            integerPeriodizeForce f x s i) t
        =
      timeDerivative
          (fun s : ℝ =>
            f (integerShift k x) s i) t)
    ∨
    timeDerivative
        (fun s : ℝ =>
          integerPeriodizeForce f x s i) t
      = 0 := by
  rcases
      integerPeriodizeForce_local_single_or_zero
        rho sigma hrs hsigma hsupp x with
    ⟨eps, heps, hlocal⟩
  have hself : CloseSpace eps x x := by
    intro j
    simpa using heps
  rcases hlocal with hcopy | hzero
  · rcases hcopy with ⟨k, hk⟩
    left
    refine ⟨k, ?_⟩
    unfold timeDerivative
    have hfun :
        (fun s : ℝ =>
          integerPeriodizeForce f x s i)
          =
        (fun s : ℝ =>
          f (integerShift k x) s i) := by
      funext s
      exact hk x hself s i
    rw [hfun]
  · right
    unfold timeDerivative
    have hfun :
        (fun s : ℝ =>
          integerPeriodizeForce f x s i)
          =
        (fun _ : ℝ => (0 : ℝ)) := by
      funext s
      exact hzero x hself s i
    rw [hfun]
    simp

theorem globallySmoothForce_spatialSlice_differentiableAt
    {f : RForce}
    (hf : GloballySmoothForce f)
    (x : RSpace)
    (t : ℝ)
    (i : Fin 3) :
    DifferentiableAt ℝ
      (fun y : RSpace => f y t i) x := by
  have hpair :
      ContDiff ℝ ⊤
        (fun y : RSpace => (y, t)) :=
    contDiff_id.prodMk contDiff_const
  have hc :
      ContDiff ℝ ⊤
        (fun y : RSpace => f y t i) := by
    exact (hf i).comp hpair
  exact (hc.differentiable (by simp)).differentiableAt

theorem integerPeriodizeForce_spatialDerivative_source_local
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (hsmooth : GloballySmoothForce f)
    (x : RSpace)
    (t : ℝ)
    (i j : Fin 3) :
    (∃ k : Lattice3,
      spatialDerivative j
          (fun y : RSpace =>
            integerPeriodizeForce f y t i) x
        =
      spatialDerivative j
          (fun y : RSpace => f y t i)
          (integerShift k x))
    ∨
    spatialDerivative j
        (fun y : RSpace =>
          integerPeriodizeForce f y t i) x
      = 0 := by
  rcases
      integerPeriodizeForce_spatialDerivative_local
        rho sigma hrs hsigma hsupp x t i j with
    ⟨k, hk⟩ | hzero
  · left
    refine ⟨k, hk.trans ?_⟩
    exact
      translatedSpatialDerivative_eq
        k j x
        (globallySmoothForce_spatialSlice_differentiableAt
          hsmooth (integerShift k x) t i)
  · exact Or.inr hzero

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.eventually_closeSpace_spatial
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_spatial_fderiv_local
#print axioms Fefferman.ConcreteReal.fderiv_add_lattice
#print axioms Fefferman.ConcreteReal.translatedSpatialDerivative_eq
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_spatialDerivative_local
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_timeDerivative_local
#print axioms Fefferman.ConcreteReal.globallySmoothForce_spatialSlice_differentiableAt
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_spatialDerivative_source_local


namespace Fefferman
namespace ConcreteReal

theorem vectorDt_eq_on_set
    {U : Set RSpace}
    {v w : RVelocity}
    (hvw :
      ∀ x : RSpace, x ∈ U →
        ∀ t : ℝ, ∀ i : Fin 3,
          v x t i = w x t i) :
    ∀ x : RSpace, x ∈ U →
      ∀ t : ℝ, ∀ i : Fin 3,
        vectorDt realAnalysis v x t i =
          vectorDt realAnalysis w x t i := by
  intro x hx t i
  change
    deriv (fun s : ℝ => v x s i) t =
      deriv (fun s : ℝ => w x s i) t
  have hfun :
      (fun s : ℝ => v x s i) =
        (fun s : ℝ => w x s i) := by
    funext s
    exact hvw x hx s i
  rw [hfun]

theorem repeat_vectorDt_eq_on_set
    {U : Set RSpace}
    {v w : RVelocity}
    (hvw :
      ∀ x : RSpace, x ∈ U →
        ∀ t : ℝ, ∀ i : Fin 3,
          v x t i = w x t i) :
    ∀ m : Nat,
      ∀ x : RSpace, x ∈ U →
        ∀ t : ℝ, ∀ i : Fin 3,
          repeatOp (vectorDt realAnalysis) m v x t i =
            repeatOp (vectorDt realAnalysis) m w x t i := by
  intro m
  induction m with
  | zero =>
      intro x hx t i
      exact hvw x hx t i
  | succ m ih =>
      exact
        vectorDt_eq_on_set
          (U := U)
          (v := repeatOp (vectorDt realAnalysis) m v)
          (w := repeatOp (vectorDt realAnalysis) m w)
          (ih)

theorem vectorDx_eq_on_open
    {U : Set RSpace}
    (hU : IsOpen U)
    {v w : RInitial}
    (hvw :
      ∀ x : RSpace, x ∈ U →
        ∀ i : Fin 3, v x i = w x i)
    (j : Fin 3) :
    ∀ x : RSpace, x ∈ U →
      ∀ i : Fin 3,
        vectorDx realAnalysis j v x i =
          vectorDx realAnalysis j w x i := by
  intro x hx i
  change
    (fderiv ℝ (fun y : RSpace => v y i) x)
        (basisDirection j)
      =
    (fderiv ℝ (fun y : RSpace => w y i) x)
        (basisDirection j)
  have hnhds : U ∈ 𝓝 x :=
    hU.mem_nhds hx
  have heq :
      (fun y : RSpace => v y i)
        =ᶠ[𝓝 x]
      (fun y : RSpace => w y i) := by
    filter_upwards [hnhds] with y hy
    exact hvw y hy i
  exact
    congrArg
      (fun L : RSpace →L[ℝ] ℝ =>
        L (basisDirection j))
      heq.fderiv_eq

theorem repeat_vectorDx_eq_on_open
    {U : Set RSpace}
    (hU : IsOpen U)
    {v w : RInitial}
    (hvw :
      ∀ x : RSpace, x ∈ U →
        ∀ i : Fin 3, v x i = w x i)
    (j : Fin 3) :
    ∀ n : Nat,
      ∀ x : RSpace, x ∈ U →
        ∀ i : Fin 3,
          repeatOp (vectorDx realAnalysis j) n v x i =
            repeatOp (vectorDx realAnalysis j) n w x i := by
  intro n
  induction n with
  | zero =>
      intro x hx i
      exact hvw x hx i
  | succ n ih =>
      exact
        vectorDx_eq_on_open
          hU
          (v := repeatOp (vectorDx realAnalysis j) n v)
          (w := repeatOp (vectorDx realAnalysis j) n w)
          ih
          j

theorem spatialJet_eq_on_open
    {U : Set RSpace}
    (hU : IsOpen U)
    {v w : RInitial}
    (hvw :
      ∀ x : RSpace, x ∈ U →
        ∀ i : Fin 3, v x i = w x i)
    (alpha : MultiIndex) :
    ∀ x : RSpace, x ∈ U →
      ∀ i : Fin 3,
        spatialJet realAnalysis alpha v x i =
          spatialJet realAnalysis alpha w x i := by
  have h2 :=
    repeat_vectorDx_eq_on_open
      hU hvw (2 : Fin 3) (alpha 2)
  have h1 :=
    repeat_vectorDx_eq_on_open
      hU h2 (1 : Fin 3) (alpha 1)
  have h0 :=
    repeat_vectorDx_eq_on_open
      hU h1 (0 : Fin 3) (alpha 0)
  simpa [spatialJet] using h0

theorem mixedJet_eq_on_open
    {U : Set RSpace}
    (hU : IsOpen U)
    {f g : RForce}
    (hfg :
      ∀ x : RSpace, x ∈ U →
        ∀ t : ℝ, ∀ i : Fin 3,
          f x t i = g x t i)
    (alpha : MultiIndex)
    (m : Nat) :
    ∀ x : RSpace, x ∈ U →
      ∀ t : ℝ,
        mixedJet realAnalysis alpha m f x t =
          mixedJet realAnalysis alpha m g x t := by
  have ht :=
    repeat_vectorDt_eq_on_set
      (U := U) hfg m
  intro x hx t
  funext i
  unfold mixedJet
  exact
    spatialJet_eq_on_open
      hU
      (v := fun y =>
        repeatOp (vectorDt realAnalysis) m f y t)
      (w := fun y =>
        repeatOp (vectorDt realAnalysis) m g y t)
      (by
        intro y hy q
        exact ht y hy t q)
      alpha x hx i

def zeroRInitial : RInitial :=
  fun _ _ => 0

def zeroRForce : RForce :=
  fun _ _ _ => 0

theorem zeroRForce_eq_projectZero :
    zeroRForce = zeroForce realAnalysis := by
  rfl

theorem vectorDt_zeroRForce :
    vectorDt realAnalysis zeroRForce = zeroRForce := by
  funext x t i
  change deriv (fun _ : ℝ => (0 : ℝ)) t = 0
  simp

theorem repeat_vectorDt_zeroRForce
    (m : Nat) :
    repeatOp (vectorDt realAnalysis) m zeroRForce =
      zeroRForce := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [repeatOp, ih]
      exact vectorDt_zeroRForce

theorem vectorDx_zeroRInitial
    (j : Fin 3) :
    vectorDx realAnalysis j zeroRInitial =
      zeroRInitial := by
  funext x i
  change RSpace at x
  change
    (fderiv ℝ
      (fun _ : RSpace => (0 : ℝ)) x)
        (basisDirection j) = 0
  have hfd :
      fderiv ℝ
          (fun _ : RSpace => (0 : ℝ)) x
        =
      (0 : RSpace →L[ℝ] ℝ) :=
    fderiv_const_apply (𝕜 := ℝ) (x := x) (0 : ℝ)
  rw [hfd]
  rfl

theorem repeat_vectorDx_zeroRInitial
    (j : Fin 3)
    (n : Nat) :
    repeatOp (vectorDx realAnalysis j) n zeroRInitial =
      zeroRInitial := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [repeatOp, ih]
      exact vectorDx_zeroRInitial j

theorem spatialJet_zeroRInitial
    (alpha : MultiIndex) :
    spatialJet realAnalysis alpha zeroRInitial =
      zeroRInitial := by
  unfold spatialJet
  rw [repeat_vectorDx_zeroRInitial]
  rw [repeat_vectorDx_zeroRInitial]
  rw [repeat_vectorDx_zeroRInitial]

theorem mixedJet_zeroRForce
    (alpha : MultiIndex)
    (m : Nat)
    (x : RSpace)
    (t : ℝ) :
    mixedJet realAnalysis alpha m zeroRForce x t =
      fun _ : Fin 3 => realAnalysis.zero := by
  unfold mixedJet
  rw [repeat_vectorDt_zeroRForce]
  change spatialJet realAnalysis alpha zeroRInitial x =
    (fun _ : Fin 3 => realAnalysis.zero)
  rw [spatialJet_zeroRInitial]
  rfl

def translatedForce
    (k : Lattice3)
    (f : RForce) :
    RForce :=
  fun x t i => f (integerShift k x) t i

theorem integerPeriodizeForce_mixedJet_local_single_or_zero
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (alpha : MultiIndex)
    (m : Nat)
    (x : RSpace)
    (t : ℝ) :
    (∃ k : Lattice3,
      mixedJet realAnalysis alpha m
          (integerPeriodizeForce f) x t
        =
      mixedJet realAnalysis alpha m
          (translatedForce k f) x t)
    ∨
    mixedJet realAnalysis alpha m
        (integerPeriodizeForce f) x t
      =
    (fun _ : Fin 3 => realAnalysis.zero) := by
  rcases
      integerPeriodizeForce_local_single_or_zero
        rho sigma hrs hsigma hsupp x with
    ⟨eps, heps, hlocal⟩
  have hx : x ∈ SpaceBox eps x := by
    change CloseSpace eps x x
    intro j
    simpa using heps
  rcases hlocal with hcopy | hzero
  · rcases hcopy with ⟨k, hk⟩
    left
    refine ⟨k, ?_⟩
    exact
      mixedJet_eq_on_open
        (isOpen_spaceBox eps x)
        (f := integerPeriodizeForce f)
        (g := translatedForce k f)
        (by
          intro y hy s i
          exact hk y hy s i)
        alpha m x hx t
  · right
    have hEq :
        mixedJet realAnalysis alpha m
            (integerPeriodizeForce f) x t
          =
        mixedJet realAnalysis alpha m
            zeroRForce x t := by
      exact
        mixedJet_eq_on_open
          (isOpen_spaceBox eps x)
          (f := integerPeriodizeForce f)
          (g := zeroRForce)
          (by
            intro y hy s i
            exact hzero y hy s i)
          alpha m x hx t
    exact hEq.trans (mixedJet_zeroRForce alpha m x t)

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.vectorDt_eq_on_set
#print axioms Fefferman.ConcreteReal.repeat_vectorDt_eq_on_set
#print axioms Fefferman.ConcreteReal.vectorDx_eq_on_open
#print axioms Fefferman.ConcreteReal.repeat_vectorDx_eq_on_open
#print axioms Fefferman.ConcreteReal.spatialJet_eq_on_open
#print axioms Fefferman.ConcreteReal.mixedJet_eq_on_open
#print axioms Fefferman.ConcreteReal.mixedJet_zeroRForce
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_mixedJet_local_single_or_zero


namespace Fefferman
namespace ConcreteReal

def MixedJetTranslationLaw (f : RForce) : Prop :=
  ∀ (k : Lattice3)
    (alpha : MultiIndex)
    (m : Nat)
    (x : RSpace)
    (t : ℝ),
      mixedJet realAnalysis alpha m
          (translatedForce k f) x t
        =
      mixedJet realAnalysis alpha m
          f (integerShift k x) t

theorem integerPeriodizeForce_clause09_of_translationLaw
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (h09 : clause09 realAnalysis f)
    (htrans : MixedJetTranslationLaw f) :
    clause09 realAnalysis (integerPeriodizeForce f) := by
  intro alpha m K
  rcases h09 alpha m K with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro x t ht
  rcases
      integerPeriodizeForce_mixedJet_local_single_or_zero
        rho sigma hrs hsigma hsupp alpha m x t with
    ⟨k, hk⟩ | hzero
  · rw [hk, htrans k alpha m x t]
    exact hbound (integerShift k x) t ht
  · rw [hzero]
    change
      realAnalysis.le
        (realAnalysis.mul
          (realAnalysis.norm3
            (fun _ : Fin 3 => realAnalysis.zero))
          (scalarPow realAnalysis
            (realAnalysis.add realAnalysis.one t) K))
        C
    change (0 : ℝ) < C at hC
    have hC0 : (0 : ℝ) ≤ C := le_of_lt hC
    simpa [realAnalysis, euclideanNorm3, normSq3] using hC0

theorem integerPeriodizeForce_admissible_periodic
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (hsmooth : GloballySmoothForce f)
    (h09 : clause09 realAnalysis f)
    (htrans : MixedJetTranslationLaw f) :
    admissibleForce realAnalysis Domain.periodic
      (integerPeriodizeForce f) := by
  exact
    ⟨integerPeriodizeForce_vectorSmooth
        rho sigma hrs hsigma hsupp hsmooth,
      integerPeriodizeForce_periodic f,
      integerPeriodizeForce_clause09_of_translationLaw
        rho sigma hrs hsigma hsupp h09 htrans⟩

theorem corollary106PeriodicForce_clause09
    (rho sigma lam t0 : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp :
      SpatialCubeSupported rho
        (rescaleForce lam t0 f))
    (h09 :
      clause09 realAnalysis
        (rescaleForce lam t0 f))
    (htrans :
      MixedJetTranslationLaw
        (rescaleForce lam t0 f)) :
    clause09 realAnalysis
      (corollary106PeriodicForce lam t0 f) := by
  exact
    integerPeriodizeForce_clause09_of_translationLaw
      rho sigma hrs hsigma hsupp h09 htrans

theorem corollary106PeriodicForce_admissible
    (rho sigma lam t0 : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp :
      SpatialCubeSupported rho
        (rescaleForce lam t0 f))
    (hsmooth :
      GloballySmoothForce
        (rescaleForce lam t0 f))
    (h09 :
      clause09 realAnalysis
        (rescaleForce lam t0 f))
    (htrans :
      MixedJetTranslationLaw
        (rescaleForce lam t0 f)) :
    admissibleForce realAnalysis Domain.periodic
      (corollary106PeriodicForce lam t0 f) := by
  exact
    integerPeriodizeForce_admissible_periodic
      rho sigma hrs hsigma
      hsupp hsmooth h09 htrans

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_clause09_of_translationLaw
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_admissible_periodic
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForce_clause09
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForce_admissible


namespace Fefferman
namespace ConcreteReal

def translatedInitial
    (k : Lattice3)
    (v : RInitial) :
    RInitial :=
  fun x i => v (integerShift k x) i

theorem vectorDx_translatedInitial
    (k : Lattice3)
    (j : Fin 3)
    (v : RInitial) :
    vectorDx realAnalysis j (translatedInitial k v)
      =
    translatedInitial k (vectorDx realAnalysis j v) := by
  funext x i
  change RSpace at x
  unfold vectorDx translatedInitial
  change
    (fderiv ℝ
      (fun y : RSpace =>
        v (y + latticeAsSpace k) i) x)
        (basisDirection j)
      =
    (fderiv ℝ
      (fun y : RSpace => v y i)
      (x + latticeAsSpace k))
        (basisDirection j)
  have hfd :
      fderiv ℝ
          (fun y : RSpace =>
            (fun z : RSpace => v z i)
              (y + latticeAsSpace k)) x
        =
      fderiv ℝ
          (fun y : RSpace => v y i)
          (x + latticeAsSpace k) :=
    fderiv_comp_add_right
      (𝕜 := ℝ)
      (f := fun y : RSpace => v y i)
      (x := x)
      (latticeAsSpace k)
  exact
    congrArg
      (fun L : RSpace →L[ℝ] ℝ =>
        L (basisDirection j))
      hfd

theorem repeat_vectorDx_translatedInitial
    (k : Lattice3)
    (j : Fin 3)
    (n : Nat)
    (v : RInitial) :
    repeatOp (vectorDx realAnalysis j) n
        (translatedInitial k v)
      =
    translatedInitial k
      (repeatOp (vectorDx realAnalysis j) n v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [repeatOp, ih]
      exact vectorDx_translatedInitial k j
        (repeatOp (vectorDx realAnalysis j) n v)

theorem spatialJet_translatedInitial
    (k : Lattice3)
    (alpha : MultiIndex)
    (v : RInitial) :
    spatialJet realAnalysis alpha
        (translatedInitial k v)
      =
    translatedInitial k
      (spatialJet realAnalysis alpha v) := by
  unfold spatialJet
  rw [repeat_vectorDx_translatedInitial]
  rw [repeat_vectorDx_translatedInitial]
  rw [repeat_vectorDx_translatedInitial]

theorem vectorDt_translatedForce
    (k : Lattice3)
    (f : RForce) :
    vectorDt realAnalysis (translatedForce k f)
      =
    translatedForce k (vectorDt realAnalysis f) := by
  rfl

theorem repeat_vectorDt_translatedForce
    (k : Lattice3)
    (m : Nat)
    (f : RForce) :
    repeatOp (vectorDt realAnalysis) m
        (translatedForce k f)
      =
    translatedForce k
      (repeatOp (vectorDt realAnalysis) m f) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [repeatOp, ih]
      exact vectorDt_translatedForce k
        (repeatOp (vectorDt realAnalysis) m f)

theorem mixedJet_translatedForce
    (k : Lattice3)
    (alpha : MultiIndex)
    (m : Nat)
    (f : RForce)
    (x : RSpace)
    (t : ℝ) :
    mixedJet realAnalysis alpha m
        (translatedForce k f) x t
      =
    mixedJet realAnalysis alpha m
        f (integerShift k x) t := by
  unfold mixedJet
  rw [repeat_vectorDt_translatedForce]
  let v : RInitial :=
    fun y =>
      repeatOp (vectorDt realAnalysis) m f y t
  change
    spatialJet realAnalysis alpha
        (translatedInitial k v) x
      =
    spatialJet realAnalysis alpha
        v (integerShift k x)
  have h :=
    congrFun
      (spatialJet_translatedInitial k alpha v)
      x
  exact h

theorem mixedJetTranslationLaw
    (f : RForce) :
    MixedJetTranslationLaw f := by
  intro k alpha m x t
  exact mixedJet_translatedForce k alpha m f x t

theorem integerPeriodizeForce_clause09
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (h09 : clause09 realAnalysis f) :
    clause09 realAnalysis (integerPeriodizeForce f) := by
  exact
    integerPeriodizeForce_clause09_of_translationLaw
      rho sigma hrs hsigma
      hsupp h09 (mixedJetTranslationLaw f)

theorem integerPeriodizeForce_admissible_periodic_closed
    (rho sigma : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    (hsmooth : GloballySmoothForce f)
    (h09 : clause09 realAnalysis f) :
    admissibleForce realAnalysis Domain.periodic
      (integerPeriodizeForce f) := by
  exact
    integerPeriodizeForce_admissible_periodic
      rho sigma hrs hsigma
      hsupp hsmooth h09
      (mixedJetTranslationLaw f)

theorem corollary106PeriodicForce_clause09_closed
    (rho sigma lam t0 : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp :
      SpatialCubeSupported rho
        (rescaleForce lam t0 f))
    (h09 :
      clause09 realAnalysis
        (rescaleForce lam t0 f)) :
    clause09 realAnalysis
      (corollary106PeriodicForce lam t0 f) := by
  exact
    corollary106PeriodicForce_clause09
      rho sigma lam t0 hrs hsigma
      hsupp h09
      (mixedJetTranslationLaw
        (rescaleForce lam t0 f))

theorem corollary106PeriodicForce_admissible_closed
    (rho sigma lam t0 : ℝ)
    (hrs : rho < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp :
      SpatialCubeSupported rho
        (rescaleForce lam t0 f))
    (hsmooth :
      GloballySmoothForce
        (rescaleForce lam t0 f))
    (h09 :
      clause09 realAnalysis
        (rescaleForce lam t0 f)) :
    admissibleForce realAnalysis Domain.periodic
      (corollary106PeriodicForce lam t0 f) := by
  exact
    corollary106PeriodicForce_admissible
      rho sigma lam t0 hrs hsigma
      hsupp hsmooth h09
      (mixedJetTranslationLaw
        (rescaleForce lam t0 f))

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.vectorDx_translatedInitial
#print axioms Fefferman.ConcreteReal.repeat_vectorDx_translatedInitial
#print axioms Fefferman.ConcreteReal.spatialJet_translatedInitial
#print axioms Fefferman.ConcreteReal.vectorDt_translatedForce
#print axioms Fefferman.ConcreteReal.repeat_vectorDt_translatedForce
#print axioms Fefferman.ConcreteReal.mixedJet_translatedForce
#print axioms Fefferman.ConcreteReal.mixedJetTranslationLaw
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_clause09
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_admissible_periodic_closed
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForce_clause09_closed
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForce_admissible_closed


namespace Fefferman
namespace ConcreteReal

/-!
GENERATION 1.
Parabolic spatial rescaling transports strict cube support exactly from
radius R to radius R / lam when lam > 0.
-/

theorem rescaleForce_spatialCubeSupported
    {R lam t0 : ℝ}
    (hlam : 0 < lam)
    {f : RForce}
    (hsupp : SpatialCubeSupported R f) :
    SpatialCubeSupported (R / lam)
      (rescaleForce lam t0 f) := by
  intro x t i hne
  have hfne :
      f (scaleSpace lam x)
          (rescaleTime lam t0 t) i ≠ 0 := by
    intro hz
    apply hne
    simp [rescaleForce, hz]
  have hcube :=
    hsupp (scaleSpace lam x)
      (rescaleTime lam t0 t) i hfne
  intro j
  have hj :
      |lam * x j| < R := by
    simpa [scaleSpace] using hcube j
  have hmul :
      |x j| * lam < R := by
    simpa [abs_mul, abs_of_pos hlam, mul_comm] using hj
  exact (lt_div_iff₀ hlam).2 hmul

/-!
GENERATION 2.
The affine parabolic space-time rescaling is C-infinity, hence global
smoothness of the source force is preserved by `rescaleForce`.
-/

theorem rescaleSpaceTime_contDiff
    (lam t0 : ℝ) :
    ContDiff ℝ ⊤
      (fun z : RSpace × ℝ =>
        (scaleSpace lam z.1,
          rescaleTime lam t0 z.2)) := by
  unfold scaleSpace rescaleTime
  fun_prop

theorem rescaleForce_globallySmooth
    (lam t0 : ℝ)
    {f : RForce}
    (hsmooth : GloballySmoothForce f) :
    GloballySmoothForce
      (rescaleForce lam t0 f) := by
  intro i
  have hcomp :
      ContDiff ℝ ⊤
        (fun z : RSpace × ℝ =>
          f (scaleSpace lam z.1)
            (rescaleTime lam t0 z.2) i) :=
    (hsmooth i).comp
      (rescaleSpaceTime_contDiff lam t0)
  have hscale :
      ContDiff ℝ ⊤
        (fun _ : RSpace × ℝ => lam ^ 3) :=
    contDiff_const
  have hmul := hscale.mul hcomp
  simpa [rescaleForce] using hmul

/-!
GENERATION 3.
Eliminate the rescaled-support and rescaled-smoothness hypotheses from the
final periodic admissibility theorem.  The only force-side analytic property
still assumed *after rescaling* is official `clause09`.
-/

theorem corollary106PeriodicForce_admissible_from_source
    (R sigma lam t0 : ℝ)
    (hlam : 0 < lam)
    (hRsigma : R / lam < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported R f)
    (hsmooth : GloballySmoothForce f)
    (h09 :
      clause09 realAnalysis
        (rescaleForce lam t0 f)) :
    admissibleForce realAnalysis Domain.periodic
      (corollary106PeriodicForce lam t0 f) := by
  exact
    corollary106PeriodicForce_admissible_closed
      (R / lam) sigma lam t0
      hRsigma hsigma
      (rescaleForce_spatialCubeSupported
        hlam hsupp)
      (rescaleForce_globallySmooth
        lam t0 hsmooth)
      h09

/-!
GENERATION 4.
A concrete nonzero value of a cube-supported source survives literal
periodization.  This is useful later for the nonzero Case-III classification.
-/

def zeroLattice : Lattice3 :=
  fun _ => 0

theorem integerShift_zeroLattice
    (x : RSpace) :
    integerShift zeroLattice x = x := by
  funext j
  simp [integerShift, zeroLattice]

theorem integerPeriodizeForce_nonzero_at_source_point
    (rho : ℝ)
    (hrho : 2 * rho < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported rho f)
    {x : RSpace}
    {t : ℝ}
    {i : Fin 3}
    (hne : f x t i ≠ 0) :
    integerPeriodizeForce f x t i ≠ 0 := by
  have hactive :
      f (integerShift zeroLattice x) t i ≠ 0 := by
    simpa [integerShift_zeroLattice] using hne
  have heq :
      integerPeriodizeForce f x t i =
        f (integerShift zeroLattice x) t i :=
    integerPeriodizeForce_eq_active
      rho hrho hsupp hactive
  rw [integerShift_zeroLattice] at heq
  rw [heq]
  exact hne

theorem corollary106PeriodicForce_nonzero_at_rescaled_source_point
    (rho lam t0 : ℝ)
    (hrho : 2 * rho < 1)
    {f : RForce}
    (hsupp :
      SpatialCubeSupported rho
        (rescaleForce lam t0 f))
    {x : RSpace}
    {t : ℝ}
    {i : Fin 3}
    (hne :
      rescaleForce lam t0 f x t i ≠ 0) :
    corollary106PeriodicForce lam t0 f x t i ≠ 0 := by
  exact
    integerPeriodizeForce_nonzero_at_source_point
      rho hrho hsupp hne

/-!
A compact source-ready interface after the four generations above.
Support and smoothness are now stated before rescaling; only the rapid-decay
port remains on the rescaled force.
-/

structure Corollary106SourceForceReady
    (R sigma lam t0 : ℝ)
    (f : RForce) : Prop where
  lamPos : 0 < lam
  supportFits : R / lam < sigma
  sigmaFits : 2 * sigma < 1
  sourceSupport : SpatialCubeSupported R f
  sourceSmooth : GloballySmoothForce f
  rescaledClause09 :
    clause09 realAnalysis
      (rescaleForce lam t0 f)

theorem Corollary106SourceForceReady.admissible
    {R sigma lam t0 : ℝ}
    {f : RForce}
    (h :
      Corollary106SourceForceReady
        R sigma lam t0 f) :
    admissibleForce realAnalysis Domain.periodic
      (corollary106PeriodicForce lam t0 f) := by
  exact
    corollary106PeriodicForce_admissible_from_source
      R sigma lam t0
      h.lamPos h.supportFits h.sigmaFits
      h.sourceSupport h.sourceSmooth
      h.rescaledClause09

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.rescaleForce_spatialCubeSupported
#print axioms Fefferman.ConcreteReal.rescaleSpaceTime_contDiff
#print axioms Fefferman.ConcreteReal.rescaleForce_globallySmooth
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForce_admissible_from_source
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_nonzero_at_source_point
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForce_nonzero_at_rescaled_source_point
#print axioms Fefferman.ConcreteReal.Corollary106SourceForceReady.admissible


namespace Fefferman
namespace ConcreteReal

/-!
SOURCE-FIDELITY CORRECTION.

Corollary 10.6 uses the parabolic force formula only for t >= t0 and extends
it by zero for t < t0.  Keep `rescaleForce` as the raw analytic formula and
make the delayed/zero-extended object explicit here.
-/

noncomputable def delayedRescaleForce
    (lam t0 : ℝ)
    (f : RForce) :
    RForce :=
  fun x t i =>
    if t < t0 then
      (0 : ℝ)
    else
      rescaleForce lam t0 f x t i

noncomputable def corollary106PeriodicForceFaithful
    (lam t0 : ℝ)
    (f : RForce) :
    RForce :=
  integerPeriodizeForce
    (delayedRescaleForce lam t0 f)

theorem delayedRescaleForce_of_lt
    (lam t0 : ℝ)
    (f : RForce)
    (x : RSpace)
    (t : ℝ)
    (i : Fin 3)
    (ht : t < t0) :
    delayedRescaleForce lam t0 f x t i = 0 := by
  simp [delayedRescaleForce, ht]

theorem delayedRescaleForce_of_ge
    (lam t0 : ℝ)
    (f : RForce)
    (x : RSpace)
    (t : ℝ)
    (i : Fin 3)
    (ht : t0 ≤ t) :
    delayedRescaleForce lam t0 f x t i =
      rescaleForce lam t0 f x t i := by
  simp [delayedRescaleForce, not_lt.mpr ht]

/-!
GENERATION 1.
Spatial support survives the source-faithful zero extension.
-/

theorem delayedRescaleForce_spatialCubeSupported
    {R lam t0 : ℝ}
    (hlam : 0 < lam)
    {f : RForce}
    (hsupp : SpatialCubeSupported R f) :
    SpatialCubeSupported (R / lam)
      (delayedRescaleForce lam t0 f) := by
  intro x t i hne
  have hnot : ¬ t < t0 := by
    intro hlt
    have hz :
        delayedRescaleForce lam t0 f x t i = 0 :=
      delayedRescaleForce_of_lt
        lam t0 f x t i hlt
    exact hne hz
  have hraw :
      rescaleForce lam t0 f x t i ≠ 0 := by
    simpa [delayedRescaleForce, hnot] using hne
  exact
    (rescaleForce_spatialCubeSupported
      hlam hsupp) x t i hraw

/-!
GENERATION 2.
Formal time-support transport.  This is independent of smoothness.
-/

def TimeSupported
    (a b : ℝ)
    (f : RForce) : Prop :=
  ∀ (x : RSpace) (t : ℝ) (i : Fin 3),
    t < a ∨ b < t →
      f x t i = 0

theorem delayedRescaleForce_timeSupported
    {T lam t0 : ℝ}
    (hlam : 0 < lam)
    (hT : 0 ≤ T)
    {f : RForce}
    (htime : TimeSupported 0 T f) :
    TimeSupported
      t0
      (t0 + T / (lam ^ 2))
      (delayedRescaleForce lam t0 f) := by
  intro x t i hout
  rcases hout with hlt | hgt
  · exact
      delayedRescaleForce_of_lt
        lam t0 f x t i hlt
  · have hsq : 0 < lam ^ 2 := pow_pos hlam 2
    have hquot : 0 ≤ T / (lam ^ 2) :=
      div_nonneg hT (le_of_lt hsq)
    have hnot : ¬ t < t0 := by
      intro htt
      linarith
    have hdt :
        T / (lam ^ 2) < t - t0 := by
      linarith
    have hsprod :
        T < (t - t0) * (lam ^ 2) :=
      (div_lt_iff₀ hsq).1 hdt
    have hs :
        T < rescaleTime lam t0 t := by
      simpa [rescaleTime, mul_comm] using hsprod
    have hz :
        f (scaleSpace lam x)
            (rescaleTime lam t0 t) i = 0 :=
      htime
        (scaleSpace lam x)
        (rescaleTime lam t0 t)
        i
        (Or.inr hs)
    simp [delayedRescaleForce, hnot,
      rescaleForce, hz]

theorem integerPeriodizeForce_timeSupported
    {a b : ℝ}
    {f : RForce}
    (htime : TimeSupported a b f) :
    TimeSupported a b
      (integerPeriodizeForce f) := by
  intro x t i hout
  unfold integerPeriodizeForce
  have hz :
      ∀ k : Lattice3,
        f (integerShift k x) t i = 0 := by
    intro k
    exact
      htime (integerShift k x) t i hout
  simp [hz]

theorem corollary106PeriodicForceFaithful_timeSupported
    {T lam t0 : ℝ}
    (hlam : 0 < lam)
    (hT : 0 ≤ T)
    {f : RForce}
    (htime : TimeSupported 0 T f) :
    TimeSupported
      t0
      (t0 + T / (lam ^ 2))
      (corollary106PeriodicForceFaithful
        lam t0 f) := by
  exact
    integerPeriodizeForce_timeSupported
      (delayedRescaleForce_timeSupported
        hlam hT htime)

/-!
GENERATION 3.
Smoothness across the t=t0 splice follows from a genuine initial zero-gap.
The source is represented on all real times in the concrete model, so the
zero-gap hypothesis states that it vanishes strictly before some eps > 0.
-/

def InitialGapZero
    (eps : ℝ)
    (f : RForce) : Prop :=
  ∀ (x : RSpace) (t : ℝ) (i : Fin 3),
    t < eps →
      f x t i = 0

def TimeBox
    (eps center : ℝ) :
    Set (RSpace × ℝ) :=
  {z | |z.2 - center| < eps}

theorem isOpen_timeBox
    (eps center : ℝ) :
    IsOpen (TimeBox eps center) := by
  exact
    isOpen_lt
      ((continuous_snd.sub continuous_const).abs)
      continuous_const

theorem self_mem_timeBox
    {eps center : ℝ}
    (heps : 0 < eps)
    (x : RSpace) :
    (x, center) ∈ TimeBox eps center := by
  change |center - center| < eps
  simpa using heps

theorem delayedRescaleForce_globallySmooth
    {lam t0 eps : ℝ}
    (hlam : 0 < lam)
    (heps : 0 < eps)
    {f : RForce}
    (hsmooth : GloballySmoothForce f)
    (hgap : InitialGapZero eps f) :
    GloballySmoothForce
      (delayedRescaleForce lam t0 f) := by
  intro i
  rw [contDiff_iff_contDiffAt]
  intro z
  have hraw :
      ContDiffAt ℝ ⊤
        (fun w : RSpace × ℝ =>
          rescaleForce lam t0 f
            w.1 w.2 i) z :=
    (rescaleForce_globallySmooth
      lam t0 hsmooth i).contDiffAt
  rcases lt_trichotomy z.2 t0 with
    hlt | heq | hgt
  · have hopen :
        IsOpen
          {w : RSpace × ℝ |
            w.2 < t0} :=
      isOpen_lt continuous_snd continuous_const
    have hnhds :
        {w : RSpace × ℝ |
          w.2 < t0} ∈ 𝓝 z :=
      hopen.mem_nhds hlt
    have hconst :
        ContDiffAt ℝ ⊤
          (fun _ : RSpace × ℝ =>
            (0 : ℝ)) z :=
      contDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [hnhds] with w hw
    simp [delayedRescaleForce, hw]
  · have hsq : 0 < lam ^ 2 :=
      pow_pos hlam 2
    have hdelta :
        0 < eps / (lam ^ 2) :=
      div_pos heps hsq
    have hzmem :
        z ∈ TimeBox
          (eps / (lam ^ 2)) t0 := by
      change
        |z.2 - t0| <
          eps / (lam ^ 2)
      rw [heq]
      simpa using hdelta
    have hnhds :
        TimeBox (eps / (lam ^ 2)) t0
          ∈ 𝓝 z :=
      (isOpen_timeBox
        (eps / (lam ^ 2)) t0).mem_nhds
        hzmem
    have hconst :
        ContDiffAt ℝ ⊤
          (fun _ : RSpace × ℝ =>
            (0 : ℝ)) z :=
      contDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [hnhds] with w hw
    by_cases hwlt : w.2 < t0
    · simp [delayedRescaleForce, hwlt]
    · have hupper :
          w.2 - t0 <
            eps / (lam ^ 2) :=
        (abs_lt.mp hw).2
      have hsprod :
          (w.2 - t0) * (lam ^ 2)
            < eps :=
        (lt_div_iff₀ hsq).1 hupper
      have hs :
          rescaleTime lam t0 w.2
            < eps := by
        simpa [rescaleTime, mul_comm]
          using hsprod
      have hz :
          f (scaleSpace lam w.1)
              (rescaleTime lam t0 w.2)
              i = 0 :=
        hgap
          (scaleSpace lam w.1)
          (rescaleTime lam t0 w.2)
          i hs
      simp [delayedRescaleForce,
        hwlt, rescaleForce, hz]
  · have hopen :
        IsOpen
          {w : RSpace × ℝ |
            t0 < w.2} :=
      isOpen_lt continuous_const continuous_snd
    have hnhds :
        {w : RSpace × ℝ |
          t0 < w.2} ∈ 𝓝 z :=
      hopen.mem_nhds hgt
    apply hraw.congr_of_eventuallyEq
    filter_upwards [hnhds] with w hw
    have hnot : ¬ w.2 < t0 :=
      not_lt.mpr (le_of_lt hw)
    simp [delayedRescaleForce, hnot]

/-!
GENERATION 4.
Periodicity and official force admissibility for the source-faithful object.
Support and smoothness are now inherited from source-side hypotheses; the only
remaining force-side analytic port is `clause09` for the delayed rescaling.
-/

theorem corollary106PeriodicForceFaithful_periodic
    (lam t0 : ℝ)
    (f : RForce) :
    vectorPeriodic realAnalysis
      (corollary106PeriodicForceFaithful
        lam t0 f) := by
  exact
    integerPeriodizeForce_periodic
      (delayedRescaleForce lam t0 f)

theorem corollary106PeriodicForceFaithful_admissible
    (R sigma lam t0 eps : ℝ)
    (hlam : 0 < lam)
    (heps : 0 < eps)
    (hRsigma : R / lam < sigma)
    (hsigma : 2 * sigma < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported R f)
    (hsmooth : GloballySmoothForce f)
    (hgap : InitialGapZero eps f)
    (h09 :
      clause09 realAnalysis
        (delayedRescaleForce lam t0 f)) :
    admissibleForce realAnalysis Domain.periodic
      (corollary106PeriodicForceFaithful
        lam t0 f) := by
  exact
    integerPeriodizeForce_admissible_periodic_closed
      (R / lam) sigma
      hRsigma hsigma
      (delayedRescaleForce_spatialCubeSupported
        hlam hsupp)
      (delayedRescaleForce_globallySmooth
        hlam heps hsmooth hgap)
      h09

/-!
GENERATION 5.
An explicit active source value after t0 remains nonzero after the faithful
zero extension and after literal periodization.
-/

theorem delayedRescaleForce_nonzero_of_raw
    (lam t0 : ℝ)
    (f : RForce)
    {x : RSpace}
    {t : ℝ}
    {i : Fin 3}
    (ht : t0 ≤ t)
    (hne :
      rescaleForce lam t0 f x t i ≠ 0) :
    delayedRescaleForce lam t0 f x t i ≠ 0 := by
  simpa [delayedRescaleForce,
    not_lt.mpr ht] using hne

theorem corollary106PeriodicForceFaithful_nonzero
    (R lam t0 : ℝ)
    (hlam : 0 < lam)
    (hwidth : 2 * (R / lam) < 1)
    {f : RForce}
    (hsupp : SpatialCubeSupported R f)
    {x : RSpace}
    {t : ℝ}
    {i : Fin 3}
    (ht : t0 ≤ t)
    (hne :
      rescaleForce lam t0 f x t i ≠ 0) :
    corollary106PeriodicForceFaithful
        lam t0 f x t i ≠ 0 := by
  exact
    integerPeriodizeForce_nonzero_at_source_point
      (R / lam)
      hwidth
      (delayedRescaleForce_spatialCubeSupported
        hlam hsupp)
      (delayedRescaleForce_nonzero_of_raw
        lam t0 f ht hne)

structure Corollary106FaithfulForceReady
    (R sigma lam t0 eps : ℝ)
    (f : RForce) : Prop where
  lamPos : 0 < lam
  gapPos : 0 < eps
  supportFits : R / lam < sigma
  sigmaFits : 2 * sigma < 1
  sourceSupport : SpatialCubeSupported R f
  sourceSmooth : GloballySmoothForce f
  initialGap : InitialGapZero eps f
  delayedClause09 :
    clause09 realAnalysis
      (delayedRescaleForce lam t0 f)

theorem Corollary106FaithfulForceReady.admissible
    {R sigma lam t0 eps : ℝ}
    {f : RForce}
    (h :
      Corollary106FaithfulForceReady
        R sigma lam t0 eps f) :
    admissibleForce realAnalysis Domain.periodic
      (corollary106PeriodicForceFaithful
        lam t0 f) := by
  exact
    corollary106PeriodicForceFaithful_admissible
      R sigma lam t0 eps
      h.lamPos h.gapPos
      h.supportFits h.sigmaFits
      h.sourceSupport h.sourceSmooth
      h.initialGap h.delayedClause09

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.delayedRescaleForce_spatialCubeSupported
#print axioms Fefferman.ConcreteReal.delayedRescaleForce_timeSupported
#print axioms Fefferman.ConcreteReal.integerPeriodizeForce_timeSupported
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForceFaithful_timeSupported
#print axioms Fefferman.ConcreteReal.delayedRescaleForce_globallySmooth
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForceFaithful_periodic
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForceFaithful_admissible
#print axioms Fefferman.ConcreteReal.corollary106PeriodicForceFaithful_nonzero
#print axioms Fefferman.ConcreteReal.Corollary106FaithfulForceReady.admissible


namespace Fefferman
namespace ConcreteReal

/-!
A-TIER B CLOSURE
================

The aim is to eliminate every auxiliary/interface obligation around the
periodic zero-force alternative B, leaving exactly one concrete semantic PDE
endpoint.

The endpoint is deliberately stated directly in the official project language.
-/

def PeriodicZeroForceGlobalRegularity : Prop :=
  ∀ (ν : PositiveViscosity realAnalysis)
    (u₀ : Initial realAnalysis),
      admissibleInitial realAnalysis Domain.periodic u₀ →
      hasGlobalSolution realAnalysis Domain.periodic
        ν u₀ (zeroForce realAnalysis)

/-!
Generation 1: the concrete zero force is genuinely globally smooth.
-/

theorem zeroRForce_globallySmooth :
    GloballySmoothForce zeroRForce := by
  intro i
  simpa [zeroRForce] using
    (contDiff_const :
      ContDiff ℝ ⊤
        (fun _ : RSpace × ℝ => (0 : ℝ)))

theorem zeroRForce_vectorSmooth :
    vectorSmooth realAnalysis zeroRForce := by
  exact
    globallySmoothForce_vectorSmooth
      zeroRForce_globallySmooth

/-!
Generation 2: exact periodicity of the zero force.
-/

theorem zeroRForce_periodic :
    vectorPeriodic realAnalysis zeroRForce := by
  intro x t ht j
  rfl

/-!
Generation 3: all official rapid-decay inequalities are trivial because all
mixed jets of the zero force are exactly zero.
-/

theorem zeroRForce_clause09 :
    clause09 realAnalysis zeroRForce := by
  intro alpha m K
  refine ⟨(1 : ℝ), by norm_num, ?_⟩
  intro x t ht
  rw [mixedJet_zeroRForce]
  simp [realAnalysis, euclideanNorm3, normSq3]

/-!
Generation 4: official periodic force admissibility for zero force.
-/

theorem zeroRForce_admissible_periodic :
    admissibleForce realAnalysis Domain.periodic
      zeroRForce := by
  exact
    ⟨zeroRForce_vectorSmooth,
      zeroRForce_periodic,
      zeroRForce_clause09⟩

theorem projectZeroForce_admissible_periodic :
    admissibleForce realAnalysis Domain.periodic
      (zeroForce realAnalysis) := by
  simpa [zeroRForce_eq_projectZero] using
    zeroRForce_admissible_periodic

/-!
Generation 5: a compact physical B-port.  Its zero-force admissibility field is
not a research assumption: it is filled by the theorem above.  The only
load-bearing field is `globalZeroForce`.
-/

structure PeriodicBPhysicalPort : Prop where
  zeroAdmissible :
    admissibleForce realAnalysis Domain.periodic
      (zeroForce realAnalysis)
  globalZeroForce :
    PeriodicZeroForceGlobalRegularity

theorem periodicBPhysicalPort_of_endpoint
    (h : PeriodicZeroForceGlobalRegularity) :
    PeriodicBPhysicalPort := by
  exact
    ⟨projectZeroForce_admissible_periodic, h⟩

theorem periodicBPhysicalPort_iff_endpoint :
    PeriodicBPhysicalPort ↔
      PeriodicZeroForceGlobalRegularity := by
  constructor
  · intro h
    exact h.globalZeroForce
  · exact periodicBPhysicalPort_of_endpoint

/-!
Generation 6: exact closure against the project's Fefferman B proposition.

The definitions are unfolded explicitly so this is not a new analytic
assumption.  If the source statement is exactly the expected semantic B form,
these two directions close definitionally/simp-normal form.
-/

theorem periodicZeroForceGlobalRegularity_implies_B
    (h : PeriodicZeroForceGlobalRegularity) :
    B realAnalysis := by
  simpa [PeriodicZeroForceGlobalRegularity,
    B, statement, statementAt, unforcedGlobalAt] using h

theorem B_implies_periodicZeroForceGlobalRegularity
    (h : B realAnalysis) :
    PeriodicZeroForceGlobalRegularity := by
  simpa [PeriodicZeroForceGlobalRegularity,
    B, statement, statementAt, unforcedGlobalAt] using h

theorem PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B :
    PeriodicZeroForceGlobalRegularity ↔
      B realAnalysis := by
  constructor
  · exact periodicZeroForceGlobalRegularity_implies_B
  · exact B_implies_periodicZeroForceGlobalRegularity

theorem PERIODIC_B_PHYSICAL_PORT_IFF_B :
    PeriodicBPhysicalPort ↔
      B realAnalysis := by
  rw [periodicBPhysicalPort_iff_endpoint]
  exact PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B

/-!
No-hypothesis A-tier atlas: every non-PDE interface surrounding B is discharged,
and B is equivalent to one concrete semantic endpoint.
-/

theorem PERIODIC_B_A_TIER_CLOSURE_ATLAS :
    admissibleForce realAnalysis Domain.periodic
        (zeroForce realAnalysis)
    ∧
    (PeriodicBPhysicalPort ↔ B realAnalysis)
    ∧
    (PeriodicZeroForceGlobalRegularity ↔ B realAnalysis) := by
  exact
    ⟨projectZeroForce_admissible_periodic,
      PERIODIC_B_PHYSICAL_PORT_IFF_B,
      PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B⟩

end ConcreteReal
end Fefferman

#print Fefferman.Case
#print Fefferman.statementAt
#print Fefferman.B
#print axioms Fefferman.ConcreteReal.zeroRForce_globallySmooth
#print axioms Fefferman.ConcreteReal.zeroRForce_clause09
#print axioms Fefferman.ConcreteReal.projectZeroForce_admissible_periodic
#print axioms Fefferman.ConcreteReal.periodicBPhysicalPort_iff_endpoint
#print axioms Fefferman.ConcreteReal.PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B
#print axioms Fefferman.ConcreteReal.PERIODIC_B_PHYSICAL_PORT_IFF_B
#print axioms Fefferman.ConcreteReal.PERIODIC_B_A_TIER_CLOSURE_ATLAS


namespace Fefferman
namespace ConcreteReal

/-!
A-TIER D CLOSURE
================

Direct physical/semantic formulation of Fefferman alternative D in the
concrete Real analysis regime.  No T3 derivation model is used here.
-/

def PeriodicForcedBreakdownAt
    (ν : PositiveViscosity realAnalysis) : Prop :=
  ∃ (u₀ : Initial realAnalysis)
    (f : Force realAnalysis),
      admissibleInitial realAnalysis Domain.periodic u₀
      ∧ admissibleForce realAnalysis Domain.periodic f
      ∧ ¬ hasGlobalSolution realAnalysis Domain.periodic
          ν u₀ f

def PeriodicForcedBreakdown : Prop :=
  ∀ ν : PositiveViscosity realAnalysis,
    PeriodicForcedBreakdownAt ν

/-!
A compact physical D port.  Its sole load-bearing field is the actual
periodic breakdown family itself.
-/

structure PeriodicDPhysicalPort : Prop where
  breakdown : PeriodicForcedBreakdown

theorem periodicDPhysicalPort_iff_endpoint :
    PeriodicDPhysicalPort ↔
      PeriodicForcedBreakdown := by
  constructor
  · intro h
    exact h.breakdown
  · intro h
    exact ⟨h⟩

/-!
Exact identification with the project's `breakdownAt`.
-/

theorem periodicForcedBreakdownAt_iff_breakdownAt
    (ν : PositiveViscosity realAnalysis) :
    PeriodicForcedBreakdownAt ν ↔
      breakdownAt realAnalysis Domain.periodic ν := by
  simp [PeriodicForcedBreakdownAt, breakdownAt]

theorem periodicForcedBreakdown_implies_D
    (h : PeriodicForcedBreakdown) :
    D realAnalysis := by
  simpa [PeriodicForcedBreakdown,
    D, statement, statementAt,
    periodicForcedBreakdownAt_iff_breakdownAt] using h

theorem D_implies_periodicForcedBreakdown
    (h : D realAnalysis) :
    PeriodicForcedBreakdown := by
  simpa [PeriodicForcedBreakdown,
    D, statement, statementAt,
    periodicForcedBreakdownAt_iff_breakdownAt] using h

theorem PERIODIC_FORCED_BREAKDOWN_IFF_D :
    PeriodicForcedBreakdown ↔
      D realAnalysis := by
  constructor
  · exact periodicForcedBreakdown_implies_D
  · exact D_implies_periodicForcedBreakdown

theorem PERIODIC_D_PHYSICAL_PORT_IFF_D :
    PeriodicDPhysicalPort ↔
      D realAnalysis := by
  rw [periodicDPhysicalPort_iff_endpoint]
  exact PERIODIC_FORCED_BREAKDOWN_IFF_D

/-!
The stronger zero-initial specialization used by the Corollary-10.6 route.
It is intentionally only an implication to D, not claimed equivalent to D.
-/

def PeriodicZeroInitialForcedBreakdown : Prop :=
  ∀ ν : PositiveViscosity realAnalysis,
    ∃ f : Force realAnalysis,
      admissibleInitial realAnalysis Domain.periodic zeroRInitial
      ∧ admissibleForce realAnalysis Domain.periodic f
      ∧ ¬ hasGlobalSolution realAnalysis Domain.periodic
          ν zeroRInitial f

theorem periodicZeroInitialForcedBreakdown_implies_endpoint
    (h : PeriodicZeroInitialForcedBreakdown) :
    PeriodicForcedBreakdown := by
  intro ν
  rcases h ν with
    ⟨f, hu0, hf, hnoglobal⟩
  exact
    ⟨zeroRInitial, f,
      hu0, hf, hnoglobal⟩

theorem periodicZeroInitialForcedBreakdown_implies_D
    (h : PeriodicZeroInitialForcedBreakdown) :
    D realAnalysis := by
  exact
    periodicForcedBreakdown_implies_D
      (periodicZeroInitialForcedBreakdown_implies_endpoint h)

/-!
Source-faithful Corollary-10.6 bridge:
all force construction work is separated from the final semantic no-global
field.
-/

structure PeriodicCorollary106SemanticPort : Type where
  force :
    ∀ ν : PositiveViscosity realAnalysis,
      Force realAnalysis
  initialAdmissible :
    ∀ ν : PositiveViscosity realAnalysis,
      admissibleInitial realAnalysis Domain.periodic
        zeroRInitial
  forceAdmissible :
    ∀ ν : PositiveViscosity realAnalysis,
      admissibleForce realAnalysis Domain.periodic
        (force ν)
  noGlobal :
    ∀ ν : PositiveViscosity realAnalysis,
      ¬ hasGlobalSolution realAnalysis Domain.periodic
          ν zeroRInitial (force ν)

theorem PeriodicCorollary106SemanticPort.toZeroInitialBreakdown
    (p : PeriodicCorollary106SemanticPort) :
    PeriodicZeroInitialForcedBreakdown := by
  intro ν
  exact
    ⟨p.force ν,
      p.initialAdmissible ν,
      p.forceAdmissible ν,
      p.noGlobal ν⟩

theorem PeriodicCorollary106SemanticPort.implies_D
    (p : PeriodicCorollary106SemanticPort) :
    D realAnalysis := by
  exact
    periodicZeroInitialForcedBreakdown_implies_D
      p.toZeroInitialBreakdown

/-!
A-tier atlas:
the exact D proposition is equivalent to one direct physical endpoint.
The stronger zero-initial Corollary-10.6 route is exhibited separately.
-/

theorem PERIODIC_D_A_TIER_CLOSURE_ATLAS :
    (PeriodicDPhysicalPort ↔ D realAnalysis)
    ∧
    (PeriodicForcedBreakdown ↔ D realAnalysis)
    ∧
    (PeriodicZeroInitialForcedBreakdown →
      D realAnalysis)
    ∧
    (PeriodicCorollary106SemanticPort →
      D realAnalysis) := by
  exact
    ⟨PERIODIC_D_PHYSICAL_PORT_IFF_D,
      PERIODIC_FORCED_BREAKDOWN_IFF_D,
      periodicZeroInitialForcedBreakdown_implies_D,
      PeriodicCorollary106SemanticPort.implies_D⟩

end ConcreteReal
end Fefferman

#print Fefferman.breakdownAt
#print Fefferman.D
#print axioms Fefferman.ConcreteReal.periodicForcedBreakdownAt_iff_breakdownAt
#print axioms Fefferman.ConcreteReal.PERIODIC_FORCED_BREAKDOWN_IFF_D
#print axioms Fefferman.ConcreteReal.PERIODIC_D_PHYSICAL_PORT_IFF_D
#print axioms Fefferman.ConcreteReal.periodicZeroInitialForcedBreakdown_implies_D
#print axioms Fefferman.ConcreteReal.PeriodicCorollary106SemanticPort.implies_D
#print axioms Fefferman.ConcreteReal.PERIODIC_D_A_TIER_CLOSURE_ATLAS


namespace Fefferman
namespace ConcreteReal

/-!
A-TIER C CLOSURE
================

Direct physical/semantic formulation of Fefferman alternative C in the
concrete Real analysis regime.  No R3 derivation model is used in the endpoint.
-/

def WholeSpaceForcedBreakdownAt
    (ν : PositiveViscosity realAnalysis) : Prop :=
  ∃ (u₀ : Initial realAnalysis)
    (f : Force realAnalysis),
      admissibleInitial realAnalysis Domain.wholeSpace u₀
      ∧ admissibleForce realAnalysis Domain.wholeSpace f
      ∧ ¬ hasGlobalSolution realAnalysis Domain.wholeSpace
          ν u₀ f

def WholeSpaceForcedBreakdown : Prop :=
  ∀ ν : PositiveViscosity realAnalysis,
    WholeSpaceForcedBreakdownAt ν

structure WholeSpaceCPhysicalPort : Prop where
  breakdown : WholeSpaceForcedBreakdown

theorem wholeSpaceCPhysicalPort_iff_endpoint :
    WholeSpaceCPhysicalPort ↔
      WholeSpaceForcedBreakdown := by
  constructor
  · intro h
    exact h.breakdown
  · intro h
    exact ⟨h⟩

theorem wholeSpaceForcedBreakdownAt_iff_breakdownAt
    (ν : PositiveViscosity realAnalysis) :
    WholeSpaceForcedBreakdownAt ν ↔
      breakdownAt realAnalysis Domain.wholeSpace ν := by
  simp [WholeSpaceForcedBreakdownAt, breakdownAt]

theorem wholeSpaceForcedBreakdown_implies_C
    (h : WholeSpaceForcedBreakdown) :
    C realAnalysis := by
  simpa [WholeSpaceForcedBreakdown,
    C, statement, statementAt,
    wholeSpaceForcedBreakdownAt_iff_breakdownAt] using h

theorem C_implies_wholeSpaceForcedBreakdown
    (h : C realAnalysis) :
    WholeSpaceForcedBreakdown := by
  simpa [WholeSpaceForcedBreakdown,
    C, statement, statementAt,
    wholeSpaceForcedBreakdownAt_iff_breakdownAt] using h

theorem WHOLESPACE_FORCED_BREAKDOWN_IFF_C :
    WholeSpaceForcedBreakdown ↔
      C realAnalysis := by
  constructor
  · exact wholeSpaceForcedBreakdown_implies_C
  · exact C_implies_wholeSpaceForcedBreakdown

theorem WHOLESPACE_C_PHYSICAL_PORT_IFF_C :
    WholeSpaceCPhysicalPort ↔
      C realAnalysis := by
  rw [wholeSpaceCPhysicalPort_iff_endpoint]
  exact WHOLESPACE_FORCED_BREAKDOWN_IFF_C

/-!
The stronger zero-initial specialization corresponding to the source
whole-space construction.
-/

def WholeSpaceZeroInitialForcedBreakdown : Prop :=
  ∀ ν : PositiveViscosity realAnalysis,
    ∃ f : Force realAnalysis,
      admissibleInitial realAnalysis Domain.wholeSpace zeroRInitial
      ∧ admissibleForce realAnalysis Domain.wholeSpace f
      ∧ ¬ hasGlobalSolution realAnalysis Domain.wholeSpace
          ν zeroRInitial f

theorem wholeSpaceZeroInitialForcedBreakdown_implies_endpoint
    (h : WholeSpaceZeroInitialForcedBreakdown) :
    WholeSpaceForcedBreakdown := by
  intro ν
  rcases h ν with
    ⟨f, hu0, hf, hnoglobal⟩
  exact
    ⟨zeroRInitial, f,
      hu0, hf, hnoglobal⟩

theorem wholeSpaceZeroInitialForcedBreakdown_implies_C
    (h : WholeSpaceZeroInitialForcedBreakdown) :
    C realAnalysis := by
  exact
    wholeSpaceForcedBreakdown_implies_C
      (wholeSpaceZeroInitialForcedBreakdown_implies_endpoint h)

/-!
Source semantic port: actual whole-space force family plus admissibility and
no-global proof.  Type-valued because it carries force data.
-/

structure WholeSpaceSourceSemanticPort : Type where
  force :
    ∀ ν : PositiveViscosity realAnalysis,
      Force realAnalysis
  initialAdmissible :
    ∀ ν : PositiveViscosity realAnalysis,
      admissibleInitial realAnalysis Domain.wholeSpace
        zeroRInitial
  forceAdmissible :
    ∀ ν : PositiveViscosity realAnalysis,
      admissibleForce realAnalysis Domain.wholeSpace
        (force ν)
  noGlobal :
    ∀ ν : PositiveViscosity realAnalysis,
      ¬ hasGlobalSolution realAnalysis Domain.wholeSpace
          ν zeroRInitial (force ν)

theorem WholeSpaceSourceSemanticPort.toZeroInitialBreakdown
    (p : WholeSpaceSourceSemanticPort) :
    WholeSpaceZeroInitialForcedBreakdown := by
  intro ν
  exact
    ⟨p.force ν,
      p.initialAdmissible ν,
      p.forceAdmissible ν,
      p.noGlobal ν⟩

theorem WholeSpaceSourceSemanticPort.implies_C
    (p : WholeSpaceSourceSemanticPort) :
    C realAnalysis := by
  exact
    wholeSpaceZeroInitialForcedBreakdown_implies_C
      p.toZeroInitialBreakdown

theorem WHOLESPACE_C_A_TIER_CLOSURE_ATLAS :
    (WholeSpaceCPhysicalPort ↔ C realAnalysis)
    ∧
    (WholeSpaceForcedBreakdown ↔ C realAnalysis)
    ∧
    (WholeSpaceZeroInitialForcedBreakdown →
      C realAnalysis)
    ∧
    (WholeSpaceSourceSemanticPort →
      C realAnalysis) := by
  exact
    ⟨WHOLESPACE_C_PHYSICAL_PORT_IFF_C,
      WHOLESPACE_FORCED_BREAKDOWN_IFF_C,
      wholeSpaceZeroInitialForcedBreakdown_implies_C,
      WholeSpaceSourceSemanticPort.implies_C⟩

end ConcreteReal
end Fefferman

#print Fefferman.breakdownAt
#print Fefferman.C
#print axioms Fefferman.ConcreteReal.wholeSpaceForcedBreakdownAt_iff_breakdownAt
#print axioms Fefferman.ConcreteReal.WHOLESPACE_FORCED_BREAKDOWN_IFF_C
#print axioms Fefferman.ConcreteReal.WHOLESPACE_C_PHYSICAL_PORT_IFF_C
#print axioms Fefferman.ConcreteReal.wholeSpaceZeroInitialForcedBreakdown_implies_C
#print axioms Fefferman.ConcreteReal.WholeSpaceSourceSemanticPort.implies_C
#print axioms Fefferman.ConcreteReal.WHOLESPACE_C_A_TIER_CLOSURE_ATLAS


namespace Fefferman
namespace ConcreteReal

/-!
A-TIER A CLOSURE
================

Direct semantic formulation of Fefferman alternative A in the concrete Real
analysis regime.  The derivation-model route is not part of the endpoint.
-/

def WholeSpaceZeroForceGlobalRegularity : Prop :=
  ∀ (ν : PositiveViscosity realAnalysis)
    (u₀ : Initial realAnalysis),
      admissibleInitial realAnalysis Domain.wholeSpace u₀ →
      hasGlobalSolution realAnalysis Domain.wholeSpace
        ν u₀ (zeroForce realAnalysis)

structure WholeSpaceAPhysicalPort : Prop where
  globalZeroForce :
    WholeSpaceZeroForceGlobalRegularity

theorem wholeSpaceAPhysicalPort_iff_endpoint :
    WholeSpaceAPhysicalPort ↔
      WholeSpaceZeroForceGlobalRegularity := by
  constructor
  · intro h
    exact h.globalZeroForce
  · intro h
    exact ⟨h⟩

theorem wholeSpaceZeroForceGlobalRegularity_implies_A
    (h : WholeSpaceZeroForceGlobalRegularity) :
    A realAnalysis := by
  simpa [WholeSpaceZeroForceGlobalRegularity,
    A, statement, statementAt, unforcedGlobalAt] using h

theorem A_implies_wholeSpaceZeroForceGlobalRegularity
    (h : A realAnalysis) :
    WholeSpaceZeroForceGlobalRegularity := by
  simpa [WholeSpaceZeroForceGlobalRegularity,
    A, statement, statementAt, unforcedGlobalAt] using h

theorem WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A :
    WholeSpaceZeroForceGlobalRegularity ↔
      A realAnalysis := by
  constructor
  · exact wholeSpaceZeroForceGlobalRegularity_implies_A
  · exact A_implies_wholeSpaceZeroForceGlobalRegularity

theorem WHOLESPACE_A_PHYSICAL_PORT_IFF_A :
    WholeSpaceAPhysicalPort ↔
      A realAnalysis := by
  rw [wholeSpaceAPhysicalPort_iff_endpoint]
  exact WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A

/-!
No-hypothesis A-tier atlas: Fefferman A is reduced to exactly one concrete
whole-space zero-force semantic PDE endpoint.
-/

theorem WHOLESPACE_A_A_TIER_CLOSURE_ATLAS :
    (WholeSpaceAPhysicalPort ↔ A realAnalysis)
    ∧
    (WholeSpaceZeroForceGlobalRegularity ↔
      A realAnalysis) := by
  exact
    ⟨WHOLESPACE_A_PHYSICAL_PORT_IFF_A,
      WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A⟩

end ConcreteReal
end Fefferman

#print Fefferman.A
#print Fefferman.unforcedGlobalAt
#print axioms Fefferman.ConcreteReal.wholeSpaceAPhysicalPort_iff_endpoint
#print axioms Fefferman.ConcreteReal.WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A
#print axioms Fefferman.ConcreteReal.WHOLESPACE_A_PHYSICAL_PORT_IFF_A
#print axioms Fefferman.ConcreteReal.WHOLESPACE_A_A_TIER_CLOSURE_ATLAS


namespace Fefferman
namespace ConcreteReal

/-!
UNIFIED A-TIER ABCD CLOSURE
===========================

No new analytic statement is introduced here.  This layer only packages the
four already-isolated concrete semantic endpoints and proves their exact
equivalence to Fefferman A/B/C/D.
-/

/-- Concrete regularity pair: whole-space A endpoint plus periodic B endpoint. -/
def MasterABSemantic : Prop :=
  WholeSpaceZeroForceGlobalRegularity
  ∧ PeriodicZeroForceGlobalRegularity

/-- Concrete forced-breakdown pair: whole-space C endpoint plus periodic D endpoint. -/
def MasterCDSemantic : Prop :=
  WholeSpaceForcedBreakdown
  ∧ PeriodicForcedBreakdown

/-- All four direct physical/semantic endpoints at once. -/
def ABCDPhysicalEndpoints : Prop :=
  WholeSpaceZeroForceGlobalRegularity
  ∧ PeriodicZeroForceGlobalRegularity
  ∧ WholeSpaceForcedBreakdown
  ∧ PeriodicForcedBreakdown

structure ABCDPhysicalPort : Prop where
  wholeSpaceRegular :
    WholeSpaceZeroForceGlobalRegularity
  periodicRegular :
    PeriodicZeroForceGlobalRegularity
  wholeSpaceBreakdown :
    WholeSpaceForcedBreakdown
  periodicBreakdown :
    PeriodicForcedBreakdown

theorem masterABSemantic_iff_A_and_B :
    MasterABSemantic ↔
      (A realAnalysis ∧ B realAnalysis) := by
  unfold MasterABSemantic
  rw [WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A]
  rw [PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B]

theorem masterCDSemantic_iff_C_and_D :
    MasterCDSemantic ↔
      (C realAnalysis ∧ D realAnalysis) := by
  unfold MasterCDSemantic
  rw [WHOLESPACE_FORCED_BREAKDOWN_IFF_C]
  rw [PERIODIC_FORCED_BREAKDOWN_IFF_D]

theorem abcdPhysicalEndpoints_iff_ABCD :
    ABCDPhysicalEndpoints ↔
      (A realAnalysis
      ∧ B realAnalysis
      ∧ C realAnalysis
      ∧ D realAnalysis) := by
  unfold ABCDPhysicalEndpoints
  rw [WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A]
  rw [PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B]
  rw [WHOLESPACE_FORCED_BREAKDOWN_IFF_C]
  rw [PERIODIC_FORCED_BREAKDOWN_IFF_D]

theorem abcdPhysicalPort_iff_endpoints :
    ABCDPhysicalPort ↔
      ABCDPhysicalEndpoints := by
  constructor
  · intro h
    exact
      ⟨h.wholeSpaceRegular,
       h.periodicRegular,
       h.wholeSpaceBreakdown,
       h.periodicBreakdown⟩
  · intro h
    exact
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem ABCD_PHYSICAL_PORT_IFF_FEFFERMAN_ABCD :
    ABCDPhysicalPort ↔
      (A realAnalysis
      ∧ B realAnalysis
      ∧ C realAnalysis
      ∧ D realAnalysis) := by
  rw [abcdPhysicalPort_iff_endpoints]
  exact abcdPhysicalEndpoints_iff_ABCD

/-!
MasterCD is now exactly the C/D semantic pair.  In particular, any future
MasterAC -> MasterCD construction only has to manufacture the two direct
breakdown families; C and D then follow by this theorem.
-/

theorem MASTER_CD_SEMANTIC_IMPLIES_C_AND_D
    (h : MasterCDSemantic) :
    C realAnalysis ∧ D realAnalysis := by
  exact masterCDSemantic_iff_C_and_D.mp h

theorem C_AND_D_IMPLIES_MASTER_CD_SEMANTIC
    (h : C realAnalysis ∧ D realAnalysis) :
    MasterCDSemantic := by
  exact masterCDSemantic_iff_C_and_D.mpr h

theorem MASTER_CD_SEMANTIC_IFF_C_AND_D :
    MasterCDSemantic ↔
      (C realAnalysis ∧ D realAnalysis) :=
  masterCDSemantic_iff_C_and_D

/-!
Unified no-hypothesis A-tier atlas.
This is a closure/equivalence theorem collection, not an unconditional proof
of any open NSE endpoint.
-/

theorem FEFFERMAN_ABCD_A_TIER_UNIFIED_CLOSURE_ATLAS :
    (WholeSpaceZeroForceGlobalRegularity ↔ A realAnalysis)
    ∧
    (PeriodicZeroForceGlobalRegularity ↔ B realAnalysis)
    ∧
    (WholeSpaceForcedBreakdown ↔ C realAnalysis)
    ∧
    (PeriodicForcedBreakdown ↔ D realAnalysis)
    ∧
    (MasterABSemantic ↔
      (A realAnalysis ∧ B realAnalysis))
    ∧
    (MasterCDSemantic ↔
      (C realAnalysis ∧ D realAnalysis))
    ∧
    (ABCDPhysicalEndpoints ↔
      (A realAnalysis
      ∧ B realAnalysis
      ∧ C realAnalysis
      ∧ D realAnalysis))
    ∧
    (ABCDPhysicalPort ↔
      (A realAnalysis
      ∧ B realAnalysis
      ∧ C realAnalysis
      ∧ D realAnalysis)) := by
  exact
    ⟨WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A,
     PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B,
     WHOLESPACE_FORCED_BREAKDOWN_IFF_C,
     PERIODIC_FORCED_BREAKDOWN_IFF_D,
     masterABSemantic_iff_A_and_B,
     masterCDSemantic_iff_C_and_D,
     abcdPhysicalEndpoints_iff_ABCD,
     ABCD_PHYSICAL_PORT_IFF_FEFFERMAN_ABCD⟩

end ConcreteReal
end Fefferman

#print axioms Fefferman.ConcreteReal.masterABSemantic_iff_A_and_B
#print axioms Fefferman.ConcreteReal.masterCDSemantic_iff_C_and_D
#print axioms Fefferman.ConcreteReal.abcdPhysicalEndpoints_iff_ABCD
#print axioms Fefferman.ConcreteReal.ABCD_PHYSICAL_PORT_IFF_FEFFERMAN_ABCD
#print axioms Fefferman.ConcreteReal.MASTER_CD_SEMANTIC_IFF_C_AND_D
#print axioms Fefferman.ConcreteReal.FEFFERMAN_ABCD_A_TIER_UNIFIED_CLOSURE_ATLAS
