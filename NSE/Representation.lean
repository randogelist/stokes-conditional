import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Exact countable representation. The physical Hilbert realization and the
interpretation of the supplied weak equation remain explicit inputs. -/

noncomputable section

open scoped BigOperators

namespace NSE.Representation

abbrev Seq := ℕ → ℝ
abbrev Shell := ℕ → ℕ → ℝ

def SquareSummable (a : Seq) : Prop := Summable (fun i => a i ^ 2)
abbrev EncodedState := {a : Seq // SquareSummable a}

def energy (a : Seq) : ℝ := ∑' i, a i ^ 2

def squaredDistance (a b : Seq) : ℝ := energy (fun i => a i - b i)

structure Gauge where
  weight : Seq
  nonzero : ∀ i, weight i ≠ 0

def gpEncode (g : Gauge) (a : Seq) : Seq := fun i => g.weight i * a i
def gpDecode (g : Gauge) (p : Seq) : Seq := fun i => p i / g.weight i
abbrev GPState (g : Gauge) := {p : Seq // SquareSummable (gpDecode g p)}

@[simp] theorem gpDecode_encode (g : Gauge) (a : Seq) :
    gpDecode g (gpEncode g a) = a := by
  funext i
  simp [gpDecode, gpEncode, g.nonzero i]

@[simp] theorem gpEncode_decode (g : Gauge) (p : Seq) :
    gpEncode g (gpDecode g p) = p := by
  funext i
  dsimp [gpDecode, gpEncode]
  field_simp [g.nonzero i]

def encGPEquiv (g : Gauge) : EncodedState ≃ GPState g where
  toFun a := ⟨gpEncode g a.val, by simpa using a.property⟩
  invFun p := ⟨gpDecode g p.val, p.property⟩
  left_inv a := by apply Subtype.ext; exact gpDecode_encode g a.val
  right_inv p := by apply Subtype.ext; exact gpEncode_decode g p.val

@[simp] theorem gp_energy_exact (g : Gauge) (a : Seq) :
    energy (gpDecode g (gpEncode g a)) = energy a := by simp

@[simp] theorem gp_distance_exact (g : Gauge) (a b : Seq) :
    squaredDistance (gpDecode g (gpEncode g a))
      (gpDecode g (gpEncode g b)) = squaredDistance a b := by simp

/-- A supplied normalized shell profile. Canonical profiles can instantiate
this record; the normalization is never silently assumed for an arbitrary array. -/
structure ShellProfile where
  weight : Shell
  zero_nonzero : ∀ i, weight 0 i ≠ 0
  column_summable : ∀ i, Summable (fun n => weight n i ^ 2)
  partition : ∀ i, (∑' n, weight n i ^ 2) = 1

/-- Raising data express the original adjacent shell compatibility equation. -/
structure RaisingProfile extends ShellProfile where
  spectral : Seq
  clock : Seq
  clock_nonzero : ∀ n, clock n ≠ 0
  raising : ∀ n i, spectral i * weight n i = clock n * weight (n + 1) i

def shellEncode (p : ShellProfile) (a : Seq) : Shell :=
  fun n i => p.weight n i * a i

def shellDecode (p : ShellProfile) (U : Shell) : Seq :=
  fun i => U 0 i / p.weight 0 i

def Compatible (p : RaisingProfile) (U : Shell) : Prop :=
  ∀ n i, p.spectral i * U n i = p.clock n * U (n + 1) i

def columnEnergy (U : Shell) (i : ℕ) : ℝ := ∑' n, U n i ^ 2

def shellEnergy (U : Shell) : ℝ := ∑' i, columnEnergy U i

/-- Actual countable column energies; this is independent of reconstruction. -/
def ShellSquareSummable (U : Shell) : Prop :=
  (∀ i, Summable (fun n => U n i ^ 2)) ∧ Summable (columnEnergy U)


/-- The column formulation equals ordinary square summability on the whole
countable product, so no infinite tail is omitted. -/
theorem shell_square_summable_product_iff (U : Shell) :
    ShellSquareSummable U ↔ Summable (fun p : ℕ × ℕ => U p.2 p.1 ^ 2) := by
  exact (summable_prod_of_nonneg (fun p : ℕ × ℕ => sq_nonneg (U p.2 p.1))).symm

theorem shell_energy_product (U : Shell) (h : ShellSquareSummable U) :
    shellEnergy U = ∑' p : ℕ × ℕ, U p.2 p.1 ^ 2 := by
  exact ((shell_square_summable_product_iff U).mp h).tsum_prod.symm

def BKQRState (p : RaisingProfile) :=
  {U : Shell // Compatible p U ∧ ShellSquareSummable U}

@[simp] theorem shellDecode_encode (p : ShellProfile) (a : Seq) :
    shellDecode p (shellEncode p a) = a := by
  funext i
  simp [shellDecode, shellEncode, p.zero_nonzero i]

theorem shellEncode_compatible (p : RaisingProfile) (a : Seq) :
    Compatible p (shellEncode p.toShellProfile a) := by
  intro n i
  dsimp [shellEncode]
  rw [← mul_assoc, p.raising n i, mul_assoc]

theorem compatible_factorization (p : RaisingProfile) (U : Shell)
    (h : Compatible p U) : U = shellEncode p.toShellProfile (shellDecode p.toShellProfile U) := by
  funext n i
  induction n with
  | zero =>
    dsimp [shellEncode, shellDecode]
    field_simp [p.zero_nonzero i]
  | succ n ih =>
    apply (mul_left_cancel₀ (p.clock_nonzero n))
    have hr := p.raising n i
    have hc := h n i
    simp only [shellEncode] at ih ⊢
    rw [← hc, ih, ← mul_assoc, hr, mul_assoc]

theorem shell_representative_unique (p : ShellProfile) (a b : Seq)
    (h : shellEncode p a = shellEncode p b) : a = b := by
  simpa using congrArg (shellDecode p) h

theorem shell_column_energy (p : ShellProfile) (a : Seq) (i : ℕ) :
    columnEnergy (shellEncode p a) i = a i ^ 2 := by
  simp [columnEnergy, shellEncode, mul_pow, tsum_mul_right, p.partition i]

theorem shell_column_summable (p : ShellProfile) (a : Seq) (i : ℕ) :
    Summable (fun n => shellEncode p a n i ^ 2) := by
  simpa [shellEncode, mul_pow] using (p.column_summable i).mul_right (a i ^ 2)

theorem shell_square_summable_iff (p : ShellProfile) (a : Seq) :
    ShellSquareSummable (shellEncode p a) ↔ SquareSummable a := by
  constructor
  · intro h
    simpa [SquareSummable, funext (shell_column_energy p a)] using h.2
  · intro h
    exact ⟨shell_column_summable p a, by
      simpa [SquareSummable, funext (shell_column_energy p a)] using h⟩

theorem shell_energy_exact (p : ShellProfile) (a : Seq) :
    shellEnergy (shellEncode p a) = energy a := by
  simp [shellEnergy, energy, shell_column_energy]


def shellSquaredDistance (U V : Shell) : ℝ :=
  shellEnergy (fun n i => U n i - V n i)

theorem shell_distance_exact (p : ShellProfile) (a b : Seq) :
    shellSquaredDistance (shellEncode p a) (shellEncode p b) = squaredDistance a b := by
  have he : (fun n i => shellEncode p a n i - shellEncode p b n i) =
      shellEncode p (fun i => a i - b i) := by
    funext n i
    simp only [shellEncode]
    ring
  rw [shellSquaredDistance, he, shell_energy_exact]
  rfl

theorem exact_bkqr_state_classification (p : RaisingProfile) (U : Shell) :
    (Compatible p U ∧ ShellSquareSummable U) ↔
      ∃ a, SquareSummable a ∧ U = shellEncode p.toShellProfile a := by
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨shellDecode p.toShellProfile U, ?_, compatible_factorization p U hc⟩
    apply (shell_square_summable_iff p.toShellProfile _).mp
    rw [← compatible_factorization p U hc]
    exact hs
  · rintro ⟨a, ha, rfl⟩
    exact ⟨shellEncode_compatible p a,
      (shell_square_summable_iff p.toShellProfile a).mpr ha⟩

def encBKQREquiv (p : RaisingProfile) : EncodedState ≃ BKQRState p where
  toFun a := ⟨shellEncode p.toShellProfile a.val, shellEncode_compatible p a.val,
    (shell_square_summable_iff p.toShellProfile a.val).mpr a.property⟩
  invFun U := ⟨shellDecode p.toShellProfile U.val, by
    apply (shell_square_summable_iff p.toShellProfile _).mp
    rw [← compatible_factorization p U.val U.property.1]
    exact U.property.2⟩
  left_inv a := by apply Subtype.ext; exact shellDecode_encode p.toShellProfile a.val
  right_inv U := by apply Subtype.ext; exact (compatible_factorization p U.val U.property.1).symm

def gpBKQREquiv (g : Gauge) (p : RaisingProfile) : GPState g ≃ BKQRState p :=
  (encGPEquiv g).symm.trans (encBKQREquiv p)

theorem gp_bkqr_energy_exact (g : Gauge) (p : RaisingProfile) (a : GPState g) :
    shellEnergy (gpBKQREquiv g p a).val = energy (gpDecode g a.val) :=
  shell_energy_exact p.toShellProfile _

/-- Physical entrance. The isometry is an explicit theorem of the chosen
physical realization, not a consequence of an arbitrary set bijection. -/
structure CoordinateRealization (H : Type*) where
  equivalence : H ≃ EncodedState
  physicalEnergy : H → ℝ
  isometry : ∀ u, energy (equivalence u).val = physicalEnergy u

def encodePath {H : Type*} (r : CoordinateRealization H) (u : ℝ → H) : ℝ → EncodedState :=
  fun t => r.equivalence (u t)

def decodePath {H : Type*} (r : CoordinateRealization H) (a : ℝ → EncodedState) : ℝ → H :=
  fun t => r.equivalence.symm (a t)

@[simp] theorem decode_encode_path {H : Type*} (r : CoordinateRealization H) (u : ℝ → H) :
    decodePath r (encodePath r u) = u := by
  funext t
  simp [decodePath, encodePath]

@[simp] theorem encode_path_energy {H : Type*} (r : CoordinateRealization H)
    (u : ℝ → H) (t : ℝ) : energy (encodePath r u t).val = r.physicalEnergy (u t) :=
  r.isometry (u t)

/-- Scalar weak NSE data. The three time integrands, initial term and time
integration operator are explicit; this record does not assert a physical R³ instance. -/
structure WeakNSEData (H Test : Type*) where
  integral : ℝ → ℝ → (ℝ → ℝ) → ℝ
  temporal : Test → ℝ → H → ℝ
  viscous : Test → ℝ → H → ℝ
  convection : Test → ℝ → H → H → ℝ
  initial : Test → H → ℝ

def WeakNSE {H Test : Type*} (d : WeakNSEData H Test) (ν T : ℝ)
    (u : ℝ → H) : Prop :=
  ∀ φ, d.integral 0 T (fun t => d.temporal φ t (u t)) +
    ν * d.integral 0 T (fun t => d.viscous φ t (u t)) +
    d.integral 0 T (fun t => d.convection φ t (u t) (u t)) +
    d.initial φ (u 0) = 0

def encodedWeakData {H Test : Type*} (r : CoordinateRealization H)
    (d : WeakNSEData H Test) : WeakNSEData EncodedState Test where
  integral := d.integral
  temporal := fun φ t a => d.temporal φ t (r.equivalence.symm a)
  viscous := fun φ t a => d.viscous φ t (r.equivalence.symm a)
  convection := fun φ t a b => d.convection φ t (r.equivalence.symm a) (r.equivalence.symm b)
  initial := fun φ a => d.initial φ (r.equivalence.symm a)

theorem weak_nse_transport {H Test : Type*} (r : CoordinateRealization H)
    (d : WeakNSEData H Test) (ν T : ℝ) (u : ℝ → H) :
    WeakNSE (encodedWeakData r d) ν T (encodePath r u) ↔ WeakNSE d ν T u := by
  simp [WeakNSE, encodedWeakData, encodePath]

def EnergyLedger {H : Type*} (e : H → ℝ) (integral : ℝ → ℝ → (ℝ → ℝ) → ℝ)
    (diss : ℝ → ℝ) (ν T : ℝ) (u : ℝ → H) : Prop :=
  ∀ t, 0 ≤ t → t ≤ T → e (u t) + 2 * ν * integral 0 t diss ≤ e (u 0)

theorem energy_ledger_transport {H : Type*} (r : CoordinateRealization H)
    (integral : ℝ → ℝ → (ℝ → ℝ) → ℝ) (diss : ℝ → ℝ)
    (ν T : ℝ) (u : ℝ → H) :
    EnergyLedger (fun a : EncodedState => energy a.val) integral diss ν T (encodePath r u) ↔
      EnergyLedger r.physicalEnergy integral diss ν T u := by
  simp [EnergyLedger, encode_path_energy]



/-- Abstract Leray--Hopf entrance. Weak tests, observations, the time integral,
and spatial energy must be instantiated by a physical realization. -/
structure LHNSE {H Test Obs : Type*} (e : H → ℝ) (d : WeakNSEData H Test)
    (observe : Obs → H → ℝ) (diss : ℝ → ℝ) (ν T : ℝ) (u : ℝ → H) : Prop where
  viscosity_pos : 0 < ν
  time_pos : 0 < T
  weak_continuous : ∀ j, ContinuousOn (fun t => observe j (u t)) (Set.Icc 0 T)
  energy_bounded : ∃ M, ∀ t ∈ Set.Icc 0 T, e (u t) ≤ M
  weak_equation : WeakNSE d ν T u
  energy_ledger : EnergyLedger e d.integral diss ν T u
  dissipation_nonnegative : ∀ t ∈ Set.Icc 0 T, 0 ≤ diss t

def encodedObservations {H Obs : Type*} (r : CoordinateRealization H)
    (observe : Obs → H → ℝ) : Obs → EncodedState → ℝ :=
  fun j a => observe j (r.equivalence.symm a)

theorem lh_nse_transport {H Test Obs : Type*} (r : CoordinateRealization H)
    (d : WeakNSEData H Test) (observe : Obs → H → ℝ) (diss : ℝ → ℝ)
    (ν T : ℝ) (u : ℝ → H) :
    LHNSE (fun a : EncodedState => energy a.val) (encodedWeakData r d)
      (encodedObservations r observe) diss ν T (encodePath r u) ↔
    LHNSE r.physicalEnergy d observe diss ν T u := by
  constructor
  · intro h
    refine ⟨h.viscosity_pos, h.time_pos, ?_, ?_, ?_, ?_, h.dissipation_nonnegative⟩
    · simpa [encodedObservations, encodePath] using h.weak_continuous
    · simpa only [encode_path_energy] using h.energy_bounded
    · exact (weak_nse_transport r d ν T u).mp h.weak_equation
    · exact (energy_ledger_transport r d.integral diss ν T u).mp h.energy_ledger
  · intro h
    refine ⟨h.viscosity_pos, h.time_pos, ?_, ?_, ?_, ?_, h.dissipation_nonnegative⟩
    · simpa [encodedObservations, encodePath] using h.weak_continuous
    · simpa only [encode_path_energy] using h.energy_bounded
    · exact (weak_nse_transport r d ν T u).mpr h.weak_equation
    · exact (energy_ledger_transport r d.integral diss ν T u).mpr h.energy_ledger

/-! Canonical BKQR profile from the original q-coefficient recurrence. -/

open Filter Topology

def qCoefficient (q x : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => x * q ^ n * qCoefficient q x n / (1 - q ^ (n + 1))

def qClock (q : ℝ) (n : ℕ) : ℝ := (q ^ n)⁻¹ - q

theorem q_denominator_pos {q : ℝ} (hq : 0 < q ∧ q < 1) (n : ℕ) :
    0 < 1 - q ^ (n + 1) := by
  have hp := pow_lt_one₀ hq.1.le hq.2 (Nat.succ_ne_zero n)
  change q ^ (n + 1) < 1 at hp
  linarith

theorem qCoefficient_nonneg {q x : ℝ} (hq : 0 < q ∧ q < 1) (hx : 0 ≤ x)
    (n : ℕ) : 0 ≤ qCoefficient q x n := by
  induction n with
  | zero => norm_num [qCoefficient]
  | succ n ih =>
    exact div_nonneg (mul_nonneg (mul_nonneg hx (pow_nonneg hq.1.le n)) ih)
      (q_denominator_pos hq n).le

theorem qCoefficient_summable {q x : ℝ} (hq : 0 < q ∧ q < 1) (hx : 0 ≤ x) :
    Summable (qCoefficient q x) := by
  have hp : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq.1.le hq.2
  have hps : Tendsto (fun n : ℕ => q ^ (n + 1)) atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using hp.mul_const q
  have hd : Tendsto (fun n : ℕ => 1 - q ^ (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hps
  have hr : Tendsto (fun n : ℕ => x * q ^ n / (1 - q ^ (n + 1))) atTop (𝓝 0) := by
    convert (hp.const_mul x).div hd (by norm_num : (1 : ℝ) ≠ 0) using 1
    · rfl
    · norm_num
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [hr.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (qCoefficient_nonneg hq hx (n + 1)),
    abs_of_nonneg (qCoefficient_nonneg hq hx n)]
  calc
    qCoefficient q x (n + 1) =
      (x * q ^ n / (1 - q ^ (n + 1))) * qCoefficient q x n := by
        simp only [qCoefficient]; ring
    _ ≤ 1 / 2 * qCoefficient q x n :=
      mul_le_mul_of_nonneg_right hn.le (qCoefficient_nonneg hq hx n)

def qNormalizer (q x : ℝ) : ℝ := ∑' n, qCoefficient q x n

theorem qNormalizer_ge_one {q x : ℝ} (hq : 0 < q ∧ q < 1) (hx : 0 ≤ x) :
    1 ≤ qNormalizer q x := by
  have h := (qCoefficient_summable hq hx).sum_le_tsum ({0} : Finset ℕ)
    (fun n _ => qCoefficient_nonneg hq hx n)
  simpa [qNormalizer, qCoefficient] using h

def qProbability (q x : ℝ) (n : ℕ) : ℝ := qCoefficient q x n / qNormalizer q x

def qWeight (q x : ℝ) (n : ℕ) : ℝ := Real.sqrt (qProbability q x n)

theorem qProbability_nonneg {q x : ℝ} (hq : 0 < q ∧ q < 1) (hx : 0 ≤ x)
    (n : ℕ) : 0 ≤ qProbability q x n :=
  div_nonneg (qCoefficient_nonneg hq hx n) (by linarith [qNormalizer_ge_one hq hx])

theorem qWeight_square {q x : ℝ} (hq : 0 < q ∧ q < 1) (hx : 0 ≤ x)
    (n : ℕ) : qWeight q x n ^ 2 = qProbability q x n :=
  Real.sq_sqrt (qProbability_nonneg hq hx n)

theorem qWeight_summable_square {q x : ℝ} (hq : 0 < q ∧ q < 1) (hx : 0 ≤ x) :
    Summable (fun n => qWeight q x n ^ 2) := by
  simp_rw [qWeight_square hq hx]
  exact (qCoefficient_summable hq hx).div_const _

theorem qWeight_partition {q x : ℝ} (hq : 0 < q ∧ q < 1) (hx : 0 ≤ x) :
    (∑' n, qWeight q x n ^ 2) = 1 := by
  simp_rw [qWeight_square hq hx]
  simp_rw [qProbability]
  rw [tsum_div_const]
  exact div_self (by linarith [qNormalizer_ge_one hq hx] : qNormalizer q x ≠ 0)

theorem qWeight_zero_pos {q x : ℝ} (hq : 0 < q ∧ q < 1) (hx : 0 ≤ x) :
    0 < qWeight q x 0 := by
  apply Real.sqrt_pos.2
  simp only [qProbability, qCoefficient]
  exact div_pos (by norm_num) (by linarith [qNormalizer_ge_one hq hx])

theorem qClock_pos {q : ℝ} (hq : 0 < q ∧ q < 1) (n : ℕ) : 0 < qClock q n := by
  have hp : 0 < q ^ n := pow_pos hq.1 n
  have hd := q_denominator_pos hq n
  have he : qClock q n * q ^ n = 1 - q ^ (n + 1) := by
    simp only [qClock, sub_mul, inv_mul_cancel₀ (ne_of_gt hp), pow_succ]
    ring
  nlinarith

theorem qCoefficient_raising {q x : ℝ} (hq : 0 < q ∧ q < 1) (n : ℕ) :
    x * qCoefficient q x n = qClock q n * qCoefficient q x (n + 1) := by
  have hp : q ^ n ≠ 0 := ne_of_gt (pow_pos hq.1 n)
  have hd : 1 - q ^ (n + 1) ≠ 0 := ne_of_gt (q_denominator_pos hq n)
  change x * qCoefficient q x n =
    qClock q n * (x * q ^ n * qCoefficient q x n / (1 - q ^ (n + 1)))
  rw [← mul_div_assoc]
  apply (eq_div_iff hd).mpr
  dsimp [qClock]
  rw [pow_succ]
  field_simp [hp]

theorem qWeight_raising {q x : ℝ} (hq : 0 < q ∧ q < 1) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt x * qWeight q x n = Real.sqrt (qClock q n) * qWeight q x (n + 1) := by
  have hp : x * qProbability q x n = qClock q n * qProbability q x (n + 1) := by
    dsimp [qProbability]
    have hr := qCoefficient_raising (x := x) hq n
    linear_combination hr / qNormalizer q x
  have he : (Real.sqrt x * qWeight q x n) ^ 2 =
      (Real.sqrt (qClock q n) * qWeight q x (n + 1)) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt (qClock_pos hq n).le,
      qWeight_square hq hx]
    exact hp
  have hl : 0 ≤ Real.sqrt x * qWeight q x n :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hr : 0 ≤ Real.sqrt (qClock q n) * qWeight q x (n + 1) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

/-- Literal canonical BKQR weights ψ(q, h lamᵢ², n), normalized by the actual
infinite coefficient sum. Summability and normalization are proved above. -/
def canonicalBKQR (q h : ℝ) (lam : Seq) (hq : 0 < q ∧ q < 1) (hh : 0 < h)
    (hLam : ∀ i, 0 ≤ lam i) : RaisingProfile where
  weight := fun n i => qWeight q (h * lam i ^ 2) n
  zero_nonzero := fun i => ne_of_gt (qWeight_zero_pos hq (mul_nonneg hh.le (sq_nonneg _)))
  column_summable := fun i => qWeight_summable_square hq (mul_nonneg hh.le (sq_nonneg _))
  partition := fun i => qWeight_partition hq (mul_nonneg hh.le (sq_nonneg _))
  spectral := fun i => Real.sqrt h * lam i
  clock := fun n => Real.sqrt (qClock q n)
  clock_nonzero := fun n => ne_of_gt (Real.sqrt_pos.2 (qClock_pos hq n))
  raising := by
    intro n i
    have hr := qWeight_raising hq (mul_nonneg hh.le (sq_nonneg (lam i))) n
    have he : Real.sqrt (h * lam i ^ 2) = Real.sqrt h * lam i := by
      rw [Real.sqrt_mul hh.le, Real.sqrt_sq (hLam i)]
    simpa only [he] using hr

end NSE.Representation
