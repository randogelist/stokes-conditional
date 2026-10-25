import Master_T3_details
import Fefferman.KernelCovariance

set_option autoImplicit false

namespace Fefferman

theorem T3_triad_support_commutes (k p q : T3Wave) (h : T3Triad k p q) : T3Triad k q p := by
  have hpq : T3WaveAdd p q = T3WaveAdd q p := by
    funext j
    exact Int.add_comm (p j) (q j)
  exact h.trans hpq

theorem T3_fourier_mul_shuffle (F : T3FourierAlgebra) (a b c d : F.Coefficient) :
    F.mul (F.mul a b) (F.mul c d) = F.mul (F.mul a c) (F.mul b d) := by
  rw [F.mulAssoc a b (F.mul c d), ← F.mulAssoc b c d, F.mulComm b c,
    F.mulAssoc c b d, ← F.mulAssoc a c (F.mul b d)]

theorem T3_term_product_evaluates (F : T3FourierAlgebra)
    (p q : T3FourierTerm F) (x : F.Point) :
    T3TermEval F (T3TermProduct F p q) x = F.mul (T3TermEval F p x) (T3TermEval F q x) := by
  change F.mul (F.mul p.2 q.2) (F.character (T3WaveAdd p.1 q.1) x) =
    F.mul (F.mul p.2 (F.character p.1 x)) (F.mul q.2 (F.character q.1 x))
  rw [← F.characterProduct p.1 q.1 x]
  exact (T3_fourier_mul_shuffle F p.2 (F.character p.1 x) q.2 (F.character q.1 x)).symm

theorem T3_polynomial_eval_append (F : T3FourierAlgebra)
    (p q : List (T3FourierTerm F)) (x : F.Point) :
    T3PolynomialEval F (p ++ q) x = F.add (T3PolynomialEval F p x) (T3PolynomialEval F q x) := by
  induction p with
  | nil => exact (F.zeroAdd (T3PolynomialEval F q x)).symm
  | cons term rest ih =>
    change F.add (T3TermEval F term x) (T3PolynomialEval F (rest ++ q) x) =
      F.add (F.add (T3TermEval F term x) (T3PolynomialEval F rest x)) (T3PolynomialEval F q x)
    rw [ih, F.addAssoc (T3TermEval F term x) (T3PolynomialEval F rest x) (T3PolynomialEval F q x)]

theorem T3_polynomial_eval_multiply_one (F : T3FourierAlgebra)
    (p : T3FourierTerm F) (q : List (T3FourierTerm F)) (x : F.Point) :
    T3PolynomialEval F (q.map (T3TermProduct F p)) x =
      F.mul (T3TermEval F p x) (T3PolynomialEval F q x) := by
  induction q with
  | nil => exact (F.mulZero (T3TermEval F p x)).symm
  | cons term rest ih =>
    change F.add (T3TermEval F (T3TermProduct F p term) x)
      (T3PolynomialEval F (rest.map (T3TermProduct F p)) x) =
      F.mul (T3TermEval F p x) (F.add (T3TermEval F term x) (T3PolynomialEval F rest x))
    rw [T3_term_product_evaluates F p term x, ih,
      F.mulAdd (T3TermEval F p x) (T3TermEval F term x) (T3PolynomialEval F rest x)]

theorem T3_finite_product_is_convolution (F : T3FourierAlgebra)
    (p q : List (T3FourierTerm F)) (x : F.Point) :
    T3PolynomialEval F (T3ProductTerms F p q) x =
      F.mul (T3PolynomialEval F p x) (T3PolynomialEval F q x) := by
  induction p with
  | nil => exact (F.zeroMul (T3PolynomialEval F q x)).symm
  | cons term rest ih =>
    change T3PolynomialEval F
      (q.map (T3TermProduct F term) ++ T3ProductTerms F rest q) x =
      F.mul (F.add (T3TermEval F term x) (T3PolynomialEval F rest x)) (T3PolynomialEval F q x)
    rw [T3_polynomial_eval_append, T3_polynomial_eval_multiply_one, ih,
      F.addMul (T3TermEval F term x) (T3PolynomialEval F rest x) (T3PolynomialEval F q x)]

theorem T3_renewal_prefix_bound {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .periodic} (w : T3RenewalWitness i) :
    ∀ c n, a.le (ledgerPrefix a (w.sequence c) n) (T3ActionBudget o w) := by
  intro c n
  exact ledger_renewal_prefix_bound o w.gap (w.sequence c) (w.paid c) w.seedMax w.paidMax
    w.gapPositive (w.sequenceNonnegative c) (w.sequenceSeedBound c)
    (w.renewalStep c) (w.paidPrefixBound c) n

theorem T3_renewal_gives_action_bound {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .periodic} (w : T3RenewalWitness i) :
    ∀ c t, a.le (w.action c t) (T3ActionBudget o w) := by
  intro c
  exact ledger_action_from_cofinal_samples o w.before w.cutTime (w.action c)
    (ledgerPrefix a (w.sequence c)) (T3ActionBudget o w) w.cofinal
    (w.actionMonotone c) (w.sampleRealization c) (T3_renewal_prefix_bound o w c)

theorem T3_action_gives_finite_critical_bounds {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .periodic} (w : T3RenewalWitness i) : ∀ c t,
    a.le (w.mass c t) (T3CriticalBudget o w) ∧
    a.le (w.dissipation c t) (o.divide (T3CriticalBudget o w) w.epsilon) := by
  intro c t
  exact ledger_forced_energy_bound o (w.mass c t) (w.dissipation c t) w.initialMass
    (w.action c t) (w.forceCost c t) (T3ActionBudget o w) w.forceMax w.epsilon
    w.positiveDissipation (w.massNonnegative c t) (w.dissipationNonnegative c t)
    (w.criticalBalance c t) (T3_renewal_gives_action_bound o w c t) (w.forcingBound c t)

theorem T3_full_critical_bounds {a : Analysis} (o : LedgerArithmetic a)
    {i : ForcedInput a .periodic} (w : T3RenewalWitness i) :
    (∀ t, a.le (w.fullMass t) (T3CriticalBudget o w)) ∧
    (∀ t, a.le (w.fullDissipation t) (o.divide (T3CriticalBudget o w) w.epsilon)) :=
  ⟨ledger_full_readout_bound w.mass w.fullMass (T3CriticalBudget o w) w.massReadout
      (fun c t => (T3_action_gives_finite_critical_bounds o w c t).1),
   ledger_full_readout_bound w.dissipation w.fullDissipation
      (o.divide (T3CriticalBudget o w) w.epsilon) w.dissipationReadout
      (fun c t => (T3_action_gives_finite_critical_bounds o w c t).2)⟩

theorem T3_derive_critical_control {a : Analysis} (o : LedgerArithmetic a)
    (i : ForcedInput a .periodic) (w : T3RenewalWitness i) : T3CriticalControl i w :=
  ⟨⟨T3CriticalBudget o w, (T3_full_critical_bounds o w).1⟩,
   ⟨o.divide (T3CriticalBudget o w) w.epsilon, (T3_full_critical_bounds o w).2⟩⟩

theorem T3_derive_regime_soundness {a : Analysis} (o : LedgerArithmetic a)
    (m : T3DerivationModel a) (p : T3DerivationPorts m) :
    ForceRegimeSoundness a .periodic (derivationRegimes m) :=
  derivation_regime_soundness o m p (T3_derive_critical_control o)

theorem T3_derive_B {a : Analysis} (o : LedgerArithmetic a)
    (m : T3DerivationModel a) (p : T3RegularDerivationPorts m) : B a :=
  derivation_unforced m p (T3_derive_critical_control o)

theorem T3_derive_master_core {a : Analysis} (o : LedgerArithmetic a)
    (m : T3DerivationModel a) (p : T3DerivationPorts m) :
    DomainMasterCore a .periodic (derivationRegimes m) :=
  derivation_master_core o m p (T3_derive_critical_control o)

theorem T3_derive_master {a : Analysis} (o : LedgerArithmetic a)
    (m : T3DerivationModel a) (p : T3DerivationPorts m)
    (nonempty : ∀ ν, ∃ f, (derivationRegimes m).breakdown ν f) :
    DomainMaster a .periodic (derivationRegimes m) :=
  derivation_master o m p (T3_derive_critical_control o) nonempty

end Fefferman
