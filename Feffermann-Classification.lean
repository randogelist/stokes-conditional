import Master_r3
import Fefferman.MasterAC
import Master_T3
import Fefferman.Logic
import Fefferman.ProjectRoutes
import Fefferman.Obstructions
import Fefferman.IntrinsicIdentification

set_option autoImplicit false

namespace Fefferman

/- Legacy positive-classification targets. Their C/D nonemptiness premises
   are not part of the source assemblies MR3 and MT3. -/
theorem MA_implies_A_and_C {a : Analysis} {r : ForceRegimes a .wholeSpace}
    (h : MasterTheoremA a r) : A a ∧ C a :=
  ⟨A_of_R3_masterCore h.core, fun ν => master_breakdownAt h ν⟩

theorem MB_implies_B_and_D {a : Analysis} {r : ForceRegimes a .periodic}
    (h : MasterTheoremB a r) : B a ∧ D a :=
  ⟨B_of_periodic_masterCore h.core, fun ν => master_breakdownAt h ν⟩

theorem R3_derivation_implies_A_and_C {a : Analysis} (o : LedgerArithmetic a)
    (m : R3DerivationModel a) (p : R3DerivationPorts m)
    (nonempty : ∀ ν, ∃ f, (derivationRegimes m).breakdown ν f) : A a ∧ C a :=
  MA_implies_A_and_C (R3_derive_master o m p nonempty)

theorem T3_derivation_implies_B_and_D {a : Analysis} (o : LedgerArithmetic a)
    (m : T3DerivationModel a) (p : T3DerivationPorts m)
    (nonempty : ∀ ν, ∃ f, (derivationRegimes m).breakdown ν f) : B a ∧ D a :=
  MB_implies_B_and_D (T3_derive_master o m p nonempty)

/- Source assemblies feed classification through the same input and trajectory
   ports as the original branches. No equality of private branch objects is used. -/
theorem A_from_MR3_QUATROS {a : Analysis} (h : R3EstablishedResults a)
    (L : LocalTheory a .wholeSpace) (localPorts : LocalTheoryPorts L)
    (q : QuatrosObservables L) (port : QuatrosLeanPort q) (ends : QuatrosEndpointPorts q) :
    A a := by
  apply A_of_continuation L localPorts
  intro i u hraw
  exact ends.classicalExit i u hraw
    (h.quatros L q port i u (ends.insert i u hraw)).serrin

theorem A_from_MR3_MAOTAOTROS {a : Analysis} (h : R3EstablishedResults a)
    (m : MaotaotrosObservables a) (port : MaotaotrosLeanPort m)
    (ends : MaotaotrosEndpointPorts m) : A a := by
  apply unforced_from_inputs
  intro i
  have hc := h.maotaotros m port i (ends.enter i)
  exact ends.close i (ends.enter i) hc.1 hc.2

theorem A_from_MR3_storage {a : Analysis} (h : R3EstablishedResults a)
    (o : LedgerArithmetic a) (m : R3DerivationModel a)
    (p : R3RegularDerivationPorts m) : A a :=
  derivation_unforced m p (fun i w => h.storage o i w)

theorem B_from_MT3_renewal {a : Analysis} (h : T3EstablishedResults a)
    (o : LedgerArithmetic a) (m : T3DerivationModel a)
    (p : T3RegularDerivationPorts m) : B a :=
  derivation_unforced m p (fun i w => h.renewal o i w)

theorem B_from_MT3_periodic_covariance {a : Analysis} (h : T3EstablishedResults a)
    (g : CovarianceObservables a .periodic) (port : CovarianceLeanPort g)
    (ends : CovarianceEndpointPorts g) : B a := by
  apply unforced_from_inputs
  intro i
  have hb := h.covariance g port i (ends.object i) (ends.realization i) (ends.payment i)
  exact ends.regularity i (ends.object i) (ends.sobolev i (ends.object i) hb)

end Fefferman
