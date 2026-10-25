import Master_T3_derivation
import Fefferman.T3IntegralBranch
import Fefferman.ProjectRoutes

set_option autoImplicit false

namespace Fefferman

/- MT3 collects finite integral/completion and periodic renewal/covariance
   branches. Connecting these branches physically is a separate theorem. -/
structure T3EstablishedResults (a : Analysis) : Prop where
  integral : ∀ (F : T3FourierAlgebra) (C : T3IntegralCalculus F)
    (r : T3RealReadout a F) (m : T3ModeSymbols F) (p : T3CompletionPort a F C r m),
    T3IntegralResult F C r m p
  renewal : ∀ (o : LedgerArithmetic a) (i : ForcedInput a .periodic)
    (w : T3RenewalWitness i), T3CriticalControl i w
  covariance : ∀ (g : CovarianceObservables a .periodic) (port : CovarianceLeanPort g)
    (i : UnforcedInput a .periodic) (obj : g.Object i),
    g.physicalPrefixRealization i obj → g.uniformRenewalPayment i obj → g.uniformGPBound i obj

theorem MT3 (a : Analysis) : T3EstablishedResults a := by
  constructor
  · intro F C r m p
    exact T3_integral_result F C r m p
  · intro o i w
    exact T3_derive_critical_control o i w
  · intro g port i obj hreal hpay
    exact port.prefixBound i obj hreal hpay

/- Historical positive-classification target; it is not the definition of MT3. -/
abbrev MasterTheoremB (a : Analysis) (r : ForceRegimes a .periodic) :=
  DomainMaster a .periodic r

theorem B_of_periodic_masterCore {a : Analysis} {r : ForceRegimes a .periodic}
    (h : DomainMasterCore a .periodic r) : B a :=
  fun ν => masterCore_unforcedAt h ν

theorem periodic_masterCore_and_embedding_excludes_D_at {a : Analysis}
    {r : ForceRegimes a .periodic} (h : DomainMasterCore a .periodic r)
    (ν : PositiveViscosity a)
    (cover : ∀ f, admissibleForce a .periodic f → r.regular ν f) :
    statementAt a ν .B ∧ ¬ statementAt a ν .D :=
  ⟨masterCore_unforcedAt h ν, masterCore_no_breakdownAt_of_all_regular h ν cover⟩

/- The periodic covariance bridge is derived with an explicitly periodic
   endpoint contract. R3 QUATROS data are not silently moved to this domain. -/
structure T3ReconstructedResults (a : Analysis) : Prop where
  checkedCollection : T3EstablishedResults a
  covarianceInternal : ∀ (o : KernelArithmetic a)
    (serrin : UnforcedInput a .periodic → KernelCovarianceData a → Prop),
    CovarianceLeanPort (reconstructedCovariance a .periodic serrin)

theorem MT3_reconstructed (a : Analysis) : T3ReconstructedResults a :=
  ⟨MT3 a, fun o serrin => reconstructed_covariance_port o .periodic serrin⟩

end Fefferman
