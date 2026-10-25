import NSE.Representation
import NSE.PrefixPayment

/-!
Same-path Leray--Hopf ledger specialization of the prefix payment theorem.
The physical realization and the prefix charge are explicit inputs.  The
upper bound for the specified path's dissipation ledger is derived here;
it does not require a positivity axiom for the supplied integral operator.
-/

namespace NSE

noncomputable section

open Representation

theorem realized_physicalEnergy_nonneg {H : Type*}
    (r : CoordinateRealization H) (v : H) : 0 ≤ r.physicalEnergy v := by
  rw [← r.isometry v]
  exact tsum_nonneg (fun i => sq_nonneg ((r.equivalence v).val i))

def lhDissipationLedger {H Test : Type*} (d : WeakNSEData H Test)
    (kineticDiss : ℝ → ℝ) (ν t : ℝ) : ℝ :=
  2 * ν * d.integral 0 t kineticDiss

theorem lhDissipationLedger_bound {H Test Obs : Type*}
    (r : CoordinateRealization H)
    {d : WeakNSEData H Test} {observe : Obs → H → ℝ}
    {kineticDiss : ℝ → ℝ} {ν T : ℝ} {u : ℝ → H}
    (hLH : LHNSE r.physicalEnergy d observe kineticDiss ν T u)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    lhDissipationLedger d kineticDiss ν t ≤ r.physicalEnergy (u 0) := by
  have hledger := hLH.energy_ledger t ht0 htT
  have henergy := realized_physicalEnergy_nonneg r (u t)
  unfold lhDissipationLedger
  linarith

/-- The charge uses the same weak integral, dissipation, viscosity and path
as the supplied LH model.  An additive allowance P₀ is permitted to be zero. -/
theorem lhLedger_prefixPayment {H Test Obs : Type*}
    (r : CoordinateRealization H)
    {d : WeakNSEData H Test} {observe : Obs → H → ℝ}
    {kineticDiss : ℝ → ℝ} {ν T : ℝ} {u : ℝ → H}
    (hLH : LHNSE r.physicalEnergy d observe kineticDiss ν T u)
    {C : ℕ → ℝ → ℝ} {Seed P₀ κ θ : ℝ}
    (hSeed : 0 ≤ Seed) (hP₀ : 0 ≤ P₀) (hκ : 0 ≤ κ)
    (hθ₀ : 0 ≤ θ) (hθ : θ < 96 / 605)
    (hseed : ∀ eps, actionMass C (canonicalCut T) eps 0 ≤ Seed)
    (hcharge : ∀ eps n,
      massPrefix (renewalDebt (actionMass C (canonicalCut T) eps)) n ≤
        P₀ + κ * lhDissipationLedger d kineticDiss ν (canonicalCut T n) +
          θ * massPrefix (actionMass C (canonicalCut T) eps) n) :
    PrefixPayment (actionMass C (canonicalCut T)) Seed
      (P₀ + κ * r.physicalEnergy (u 0)) θ := by
  exact ledgerPrefixPayment
    (L := fun _ t => lhDissipationLedger d kineticDiss ν t)
    (canonicalCut_grid hLH.time_pos) hSeed hP₀ hκ
    (realized_physicalEnergy_nonneg r (u 0)) hθ₀ hθ hseed
    (fun _ _ ht => lhDissipationLedger_bound r hLH ht.1 ht.2.le) hcharge

theorem lhLedger_action_bound {H Test Obs : Type*}
    (r : CoordinateRealization H)
    {d : WeakNSEData H Test} {observe : Obs → H → ℝ}
    {kineticDiss : ℝ → ℝ} {ν T : ℝ} {u : ℝ → H}
    (hLH : LHNSE r.physicalEnergy d observe kineticDiss ν T u)
    {C : ℕ → ℝ → ℝ} {Seed P₀ κ θ : ℝ}
    (hC : CumulativeAction T C)
    (hSeed : 0 ≤ Seed) (hP₀ : 0 ≤ P₀) (hκ : 0 ≤ κ)
    (hθ₀ : 0 ≤ θ) (hθ : θ < 96 / 605)
    (hseed : ∀ eps, actionMass C (canonicalCut T) eps 0 ≤ Seed)
    (hcharge : ∀ eps n,
      massPrefix (renewalDebt (actionMass C (canonicalCut T) eps)) n ≤
        P₀ + κ * lhDissipationLedger d kineticDiss ν (canonicalCut T n) +
          θ * massPrefix (actionMass C (canonicalCut T) eps) n)
    (eps : ℕ) {t : ℝ} (ht : 0 ≤ t ∧ t < T) :
    C eps t ≤ actionBudget Seed (P₀ + κ * r.physicalEnergy (u 0)) θ := by
  exact actionPayment_bound (canonicalCut_grid hLH.time_pos) hC
    (lhLedger_prefixPayment r hLH hSeed hP₀ hκ hθ₀ hθ hseed hcharge) eps ht

theorem lhLedger_m7 {H Test Obs : Type*}
    (r : CoordinateRealization H)
    {d : WeakNSEData H Test} {observe : Obs → H → ℝ}
    {kineticDiss : ℝ → ℝ} {ν T : ℝ} {u : ℝ → H}
    (hLH : LHNSE r.physicalEnergy d observe kineticDiss ν T u)
    {C : ℕ → ℝ → ℝ} {Seed P₀ κ θ : ℝ}
    (hC : CumulativeAction T C)
    (hSeed : 0 ≤ Seed) (hP₀ : 0 ≤ P₀) (hκ : 0 ≤ κ)
    (hθ₀ : 0 ≤ θ) (hθ : θ < 96 / 605)
    (hseed : ∀ eps, actionMass C (canonicalCut T) eps 0 ≤ Seed)
    (hcharge : ∀ eps n,
      massPrefix (renewalDebt (actionMass C (canonicalCut T) eps)) n ≤
        P₀ + κ * lhDissipationLedger d kineticDiss ν (canonicalCut T n) +
          θ * massPrefix (actionMass C (canonicalCut T) eps) n)
    (eps : ℕ) : GPSequenceM7 (actionMass C (canonicalCut T) eps) := by
  exact prefixPayment_m7 (actionMass_nonneg (canonicalCut_grid hLH.time_pos) hC)
    (lhLedger_prefixPayment r hLH hSeed hP₀ hκ hθ₀ hθ hseed hcharge) eps

end

end NSE

#print axioms NSE.realized_physicalEnergy_nonneg
#print axioms NSE.lhDissipationLedger_bound
#print axioms NSE.lhLedger_prefixPayment
#print axioms NSE.lhLedger_action_bound
#print axioms NSE.lhLedger_m7
