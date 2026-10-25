import Master_R3_derivation
import Fefferman.R3SourceBranch
import Fefferman.FiniteSpectral
import Fefferman.ProjectRoutes

set_option autoImplicit false

namespace Fefferman

/- MR3 collects the established source branches with their original inputs.
   It does not assert that their separate objects are the same NSE trajectory.
   Each field is filled by a theorem below, not supplied by the caller. -/
structure R3EstablishedResults (a : Analysis) : Prop where
  sourceFrame : ∀ (o : SourceArithmetic a) (P Q R : SourcePairing a)
    (s : R3SourceLedger P) (H : R3HeatFrame P Q) (M : R3MellinRealization Q R),
    R3SourceResult o s H M
  storage : ∀ (o : LedgerArithmetic a) (i : ForcedInput a .wholeSpace)
    (w : R3StorageWitness i), R3CriticalControl i w
  quatros : ∀ (L : LocalTheory a .wholeSpace) (q : QuatrosObservables L)
    (port : QuatrosLeanPort q) (i : UnforcedInput a .wholeSpace) (u : L.Trajectory i),
    QuatrosPhysicalInsertionFor q i u → QuatrosFullStages q i u
  maotaotros : ∀ (m : MaotaotrosObservables a) (port : MaotaotrosLeanPort m)
    (i : UnforcedInput a .wholeSpace) (e : m.Entrance i),
    m.criticalH12 i e ∧ m.criticalH32 i e
  covariance : ∀ (g : CovarianceObservables a .wholeSpace) (port : CovarianceLeanPort g)
    (i : UnforcedInput a .wholeSpace) (obj : g.Object i),
    g.physicalPrefixRealization i obj → g.uniformRenewalPayment i obj → g.uniformGPBound i obj

theorem MR3 (a : Analysis) : R3EstablishedResults a := by
  constructor
  · intro o P Q R s H M
    exact R3_source_result o s H M
  · intro o i w
    exact R3_derive_critical_control o i w
  · intro L q port i u h
    exact QUATROS_internal_stages q port i u h
  · intro m port i e
    exact port.critical i e
  · intro g port i obj hreal hpay
    exact port.prefixBound i obj hreal hpay

/- Historical positive-classification target, retained for compatibility.
   This contract includes breakdown nonemptiness and is NOT the definition of MR3. -/
abbrev MasterTheoremA (a : Analysis) (r : ForceRegimes a .wholeSpace) :=
  DomainMaster a .wholeSpace r

theorem A_of_R3_masterCore {a : Analysis} {r : ForceRegimes a .wholeSpace}
    (h : DomainMasterCore a .wholeSpace r) : A a :=
  fun ν => masterCore_unforcedAt h ν

theorem R3_masterCore_and_embedding_excludes_C_at {a : Analysis}
    {r : ForceRegimes a .wholeSpace} (h : DomainMasterCore a .wholeSpace r)
    (ν : PositiveViscosity a)
    (cover : ∀ f, admissibleForce a .wholeSpace f → r.regular ν f) :
    statementAt a ν .A ∧ ¬ statementAt a ν .C :=
  ⟨masterCore_unforcedAt h ν, masterCore_no_breakdownAt_of_all_regular h ν cover⟩

theorem MR3_finite_spectral {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (s : R3SourceLedger (R3FinitePairing o n)) (b : R3SpectralBinding o n s)
    {Q R : SourcePairing a} (H : R3HeatFrame (R3FinitePairing o n) Q)
    (M : R3MellinRealization Q R) : R3SpectralResult o n s b H M :=
  R3_source_spectral_result o n s b H M
    ((MR3 a).sourceFrame o (R3FinitePairing o n) Q R s H M)

theorem MR3_finite_source_and_capacity {a : Analysis} (o : SourceArithmetic a)
    (n : Nat) (s : R3SourceLedger (R3FinitePairing o n)) (b : R3SpectralBinding o n s)
    {Q R : SourcePairing a} (DR : SourceDifference R)
    (H : R3HeatFrame (R3FinitePairing o n) Q) (M : R3MellinRealization Q R) :
    R3SpectralResult o n s b H M ∧
    ∀ f n0 n1, GramCapacity o.toLedgerArithmetic DR
      (R3FrameMellin o H M f) (R3FrameMellin o H M n0) (R3FrameMellin o H M n1) =
      GramCapacity o.toLedgerArithmetic (R3FiniteDifference o n) f n0 n1 :=
  ⟨MR3_finite_spectral o n s b H M,
    R3_finite_frame_mellin_capacity o n DR H M⟩

/- The checked historical collection is retained. The new extension fills
   internal port records for concrete source-derived observables. -/
structure R3ReconstructedResults (a : Analysis) : Prop where
  checkedCollection : R3EstablishedResults a
  quatrosInternal : ∀ (o : KernelArithmetic a) (L : LocalTheory a .wholeSpace)
    (data : KernelQuatrosAssignment L), QuatrosLeanPort (reconstructedQuatros o L data)
  maotaotrosInternal : ∀ (o : KernelArithmetic a) (P : SourcePairing a)
    (readout : P.Carrier → Initial a) (Time : Type) (calculus : KernelCalculus a Time),
    MaotaotrosLeanPort (reconstructedMaotaotros o P readout Time calculus)
  covarianceInternal : ∀ (o : KernelArithmetic a)
    (serrin : UnforcedInput a .wholeSpace → KernelCovarianceData a → Prop),
    CovarianceLeanPort (reconstructedCovariance a .wholeSpace serrin)

theorem MR3_reconstructed (a : Analysis) : R3ReconstructedResults a :=
  ⟨MR3 a, fun o L data => reconstructed_quatros_port o L data,
    fun o P readout Time calculus => reconstructed_maotaotros_port o P readout Time calculus,
    fun o serrin => reconstructed_covariance_port o .wholeSpace serrin⟩

end Fefferman
