import NSE.Continuation
import NSE.LHLedger

/-!
# Same-path NSE operator anchor

The viscous and nonlinear coefficients below are evaluations of the SAME
weak data and trajectory appearing in the abstract LH entrance. The weak
viscous field is the positive weak viscous operator, as in the `+ν*viscous`
term of `WeakNSE`. A raw Laplacian readout therefore needs its own sign
conversion when a physical instance is supplied.

The ordinary modal derivative law is an explicit analytic premise. It is
not inferred from an abstract weak time-integral equation. No countable
basis is assumed to diagonalize the physical viscous operator: its full
remainder is retained in the effective source and the paid action.
-/

noncomputable section

open Set NSE.Representation

namespace NSE

def nseViscous {H Test : Type*} (weak : WeakNSEData H Test)
    (mode : ℕ → Test) (u : ℝ → H) : ℝ → ℕ → ℝ :=
  fun t i => weak.viscous (mode i) t (u t)

def nseNonlinear {H Test : Type*} (weak : WeakNSEData H Test)
    (mode : ℕ → Test) (u : ℝ → H) : ℝ → ℕ → ℝ :=
  fun t i => weak.convection (mode i) t (u t) (u t)

def nseFullSource {H Test : Type*} (r : CoordinateRealization H)
    (weak : WeakNSEData H Test) (mode : ℕ → Test) (u : ℝ → H)
    (ν : ℝ) (lam : ℕ → ℝ) : ℝ → ℕ → ℝ :=
  effectiveSource ν lam (pathCoefficients r u)
    (nseViscous weak mode u) (nseNonlinear weak mode u)

/-- The coefficient equation refers to the exact weak-operator evaluations
above. Its validity for the chosen modes is required, not silently derived. -/
def NSEModalEquation {H Test : Type*} (r : CoordinateRealization H)
    (weak : WeakNSEData H Test) (mode : ℕ → Test) (u : ℝ → H)
    (T ν : ℝ) : Prop :=
  ∀ t ∈ Ico 0 T, ∀ i,
    HasDerivAt (fun s => pathCoefficients r u s i)
      (-ν * nseViscous weak mode u t i - nseNonlinear weak mode u t i) t

theorem nseFullSource_modal_identity {H Test : Type*}
    (r : CoordinateRealization H) (weak : WeakNSEData H Test)
    (mode : ℕ → Test) (u : ℝ → H) (ν : ℝ) (lam : ℕ → ℝ) (t : ℝ) (i : ℕ) :
    -ν * (lam i) ^ 2 * pathCoefficients r u t i -
      nseFullSource r weak mode u ν lam t i =
      -ν * weak.viscous (mode i) t (u t) -
        weak.convection (mode i) t (u t) (u t) :=
  effectiveSource_modal_identity ν lam (pathCoefficients r u)
    (nseViscous weak mode u) (nseNonlinear weak mode u) t i

theorem criticalRealization_of_nse {H Test : Type*}
    (r : CoordinateRealization H) (weak : WeakNSEData H Test)
    (mode : ℕ → Test) (u : ℝ → H)
    {T ν : ℝ} {lam : ℕ → ℝ} {D C : ℕ → ℝ → ℝ} {X0 : ℝ}
    (hT : 0 < T) (hν : 0 < ν) (hlam : ∀ i, 0 ≤ lam i)
    (hmodal : NSEModalEquation r weak mode u T ν)
    (hD : ∀ N t, t ∈ Ico 0 T →
      HasDerivAt (D N) (criticalDissipation lam (pathCoefficients r u) N t) t)
    (hC : ∀ N t, t ∈ Ico 0 T →
      HasDerivAt (C N) (criticalSourceDensity ν lam (pathCoefficients r u)
        (nseFullSource r weak mode u ν lam) N t) t)
    (hD0 : ∀ N, D N 0 = 0) (hC0 : ∀ N, C N 0 = 0)
    (hseed : ∀ N, criticalEnergy lam (pathCoefficients r u) N 0 ≤ X0) :
    CriticalRealization T ν lam (pathCoefficients r u)
      (nseFullSource r weak mode u ν lam) D C X0 :=
  criticalRealization_of_operator hT hν hlam hmodal hD hC hD0 hC0 hseed

/-- Both inverse readouts recover the same coefficient trajectory, and
the independently defined countable shell energy equals its physical
energy under the supplied coordinate realization. -/
def SamePathRepresentation {H : Type*} (r : CoordinateRealization H)
    (g : Gauge) (p : RaisingProfile) (u : ℝ → H) : Prop :=
  (∀ t, gpDecode g ((encGPEquiv g) (encodePath r u t)).val = pathCoefficients r u t) ∧
  (∀ t, shellDecode p.toShellProfile ((encBKQREquiv p) (encodePath r u t)).val =
    pathCoefficients r u t) ∧
  (∀ t, shellEnergy ((encBKQREquiv p) (encodePath r u t)).val = r.physicalEnergy (u t))

theorem samePathRepresentation_canonical {H : Type*}
    (r : CoordinateRealization H) (g : Gauge) (u : ℝ → H)
    (q step : ℝ) (lam : ℕ → ℝ) (hq : 0 < q ∧ q < 1) (hstep : 0 < step)
    (hlam : ∀ i, 0 ≤ lam i) :
    SamePathRepresentation r g (canonicalBKQR q step lam hq hstep hlam) u :=
  same_path_representation r g (canonicalBKQR q step lam hq hstep hlam) u

/-- Full conditional endpoint with an arbitrary invertible GP gauge and
the constructed canonical BKQR profile. Every nonlinear/action coefficient
is tied to the given weak data and the given trajectory. -/
theorem nse_lh_gp_bkqr_m7_serrin_continuation {H Test Obs : Type*}
    (r : CoordinateRealization H) (weak : WeakNSEData H Test)
    (observe : Obs → H → ℝ) (kineticDiss : ℝ → ℝ) (u : ℝ → H)
    (mode : ℕ → Test) (g : Gauge) (q step : ℝ)
    (hq : 0 < q ∧ q < 1) (hstep : 0 < step)
    (T ν : ℝ) (lam : ℕ → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (D C : ℕ → ℝ → ℝ) (X0 Seed Paid theta Csq : ℝ)
    (e d h l : H → ℝ) (ActualSerrin46 Continues : (ℝ → H) → Prop)
    (hLH : LHNSE r.physicalEnergy weak observe kineticDiss ν T u)
    (hmodal : NSEModalEquation r weak mode u T ν)
    (hD : ∀ N t, t ∈ Ico 0 T →
      HasDerivAt (D N) (criticalDissipation lam (pathCoefficients r u) N t) t)
    (hC : ∀ N t, t ∈ Ico 0 T →
      HasDerivAt (C N) (criticalSourceDensity ν lam (pathCoefficients r u)
        (nseFullSource r weak mode u ν lam) N t) t)
    (hD0 : ∀ N, D N 0 = 0) (hC0 : ∀ N, C N 0 = 0)
    (hseed : ∀ N, criticalEnergy lam (pathCoefficients r u) N 0 ≤ X0)
    (hpay : PrefixPayment (actionMass C (canonicalCut T)) Seed Paid theta)
    (hnorm : SamePathNormRealization u lam (pathCoefficients r u) D e d h l T Csq)
    (hexit : SerrinExitContract u l T ActualSerrin46 Continues) :
    SamePathRepresentation r g (canonicalBKQR q step lam hq hstep hlam) u ∧
    LHNSE (fun a : EncodedState => energy a.val) (encodedWeakData r weak)
      (encodedObservations r observe) kineticDiss ν T (encodePath r u) ∧
    M7Injection T ν lam (pathCoefficients r u) D C X0 Seed Paid theta ∧
    (∀ t, t ∈ Ico 0 T → serrinObservable (fun s => l (u s)) t ≤
      Csq ^ 2 * (X0 + actionBudget Seed Paid theta) ^ 2 / ν) ∧
    ActualSerrin46 u ∧ Continues u := by
  refine ⟨samePathRepresentation_canonical r g u q step lam hq hstep hlam, ?_⟩
  exact lh_encoding_m7_serrin_continuation r weak observe kineticDiss u T ν lam
    (nseFullSource r weak mode u ν lam) D C X0 Seed Paid theta Csq
    e d h l ActualSerrin46 Continues hLH
    (criticalRealization_of_nse r weak mode u hLH.time_pos hLH.viscosity_pos
      hlam hmodal hD hC hD0 hC0 hseed) hpay hnorm hexit

/-- Same endpoint with payment constructed from the same LH expenditure
ledger. The prefix charge and its strict coefficient remain assumptions;
the initial energy itself has no smallness threshold in this theorem. -/
theorem nse_lh_ledger_gp_bkqr_m7_serrin_continuation {H Test Obs : Type*}
    (r : CoordinateRealization H) (weak : WeakNSEData H Test)
    (observe : Obs → H → ℝ) (kineticDiss : ℝ → ℝ) (u : ℝ → H)
    (mode : ℕ → Test) (g : Gauge) (q step : ℝ)
    (hq : 0 < q ∧ q < 1) (hstep : 0 < step)
    (T ν : ℝ) (lam : ℕ → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (D C : ℕ → ℝ → ℝ) (X0 Seed P0 κ theta Csq : ℝ)
    (e d h l : H → ℝ) (ActualSerrin46 Continues : (ℝ → H) → Prop)
    (hLH : LHNSE r.physicalEnergy weak observe kineticDiss ν T u)
    (hmodal : NSEModalEquation r weak mode u T ν)
    (hD : ∀ N t, t ∈ Ico 0 T →
      HasDerivAt (D N) (criticalDissipation lam (pathCoefficients r u) N t) t)
    (hC : ∀ N t, t ∈ Ico 0 T →
      HasDerivAt (C N) (criticalSourceDensity ν lam (pathCoefficients r u)
        (nseFullSource r weak mode u ν lam) N t) t)
    (hD0 : ∀ N, D N 0 = 0) (hC0 : ∀ N, C N 0 = 0)
    (hcriticalSeed : ∀ N, criticalEnergy lam (pathCoefficients r u) N 0 ≤ X0)
    (hSeed : 0 ≤ Seed) (hP0 : 0 ≤ P0) (hκ : 0 ≤ κ)
    (htheta0 : 0 ≤ theta) (htheta : theta < 96 / 605)
    (hfirstCell : ∀ N, actionMass C (canonicalCut T) N 0 ≤ Seed)
    (hcharge : ∀ N k,
      massPrefix (renewalDebt (actionMass C (canonicalCut T) N)) k ≤
        P0 + κ * lhDissipationLedger weak kineticDiss ν (canonicalCut T k) +
          theta * massPrefix (actionMass C (canonicalCut T) N) k)
    (hnorm : SamePathNormRealization u lam (pathCoefficients r u) D e d h l T Csq)
    (hexit : SerrinExitContract u l T ActualSerrin46 Continues) :
    SamePathRepresentation r g (canonicalBKQR q step lam hq hstep hlam) u ∧
    LHNSE (fun a : EncodedState => energy a.val) (encodedWeakData r weak)
      (encodedObservations r observe) kineticDiss ν T (encodePath r u) ∧
    M7Injection T ν lam (pathCoefficients r u) D C X0 Seed
      (P0 + κ * r.physicalEnergy (u 0)) theta ∧
    (∀ t, t ∈ Ico 0 T → serrinObservable (fun s => l (u s)) t ≤
      Csq ^ 2 * (X0 + actionBudget Seed (P0 + κ * r.physicalEnergy (u 0)) theta) ^ 2 / ν) ∧
    ActualSerrin46 u ∧ Continues u := by
  exact nse_lh_gp_bkqr_m7_serrin_continuation r weak observe kineticDiss u mode g
    q step hq hstep T ν lam hlam D C X0 Seed (P0 + κ * r.physicalEnergy (u 0))
    theta Csq e d h l ActualSerrin46 Continues hLH hmodal hD hC hD0 hC0 hcriticalSeed
    (lhLedger_prefixPayment r hLH hSeed hP0 hκ htheta0 htheta hfirstCell hcharge)
    hnorm hexit

#print axioms nseFullSource_modal_identity
#print axioms criticalRealization_of_nse
#print axioms nse_lh_gp_bkqr_m7_serrin_continuation
#print axioms nse_lh_ledger_gp_bkqr_m7_serrin_continuation

end NSE
