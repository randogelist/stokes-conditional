import Fefferman.KernelBirth
import Fefferman.KernelStorage
import Fefferman.KernelPackets
import Fefferman.CanonicalSource
import Fefferman.ProjectRoutes

set_option autoImplicit false

namespace Fefferman

/- A single assignment is used throughout a QUATROS trajectory. Physical
   identification of its observables with that trajectory is an endpoint
   insertion obligation, as in the Rocq source. -/
structure KernelQuatrosData (a : Analysis) where
  Time : Type
  calculus : KernelCalculus a Time
  settlement : KernelSettlementData a Time
  frames : Nat → KernelBirthFrame a
  renewalMass : Nat → a.Scalar
  sigma : a.Scalar
  initialEnergy : a.Scalar
  interpolationConstant : a.Scalar
  criticalMass : Time → a.Scalar
  criticalDissipation : Time → a.Scalar
  criticalAction : Time → a.Scalar
  serrin : Time → a.Scalar

abbrev KernelQuatrosAssignment {a : Analysis} (L : LocalTheory a .wholeSpace) :=
  (i : UnforcedInput a .wholeSpace) → L.Trajectory i → KernelQuatrosData a

def reconstructedQuatros {a : Analysis} (o : KernelArithmetic a)
    (L : LocalTheory a .wholeSpace) (data : KernelQuatrosAssignment L) : QuatrosObservables L where
  birthFractions := fun i u => ∀ n, KernelBirthWitness o ((data i u).frames n)
    ((data i u).renewalMass n) ((data i u).renewalMass (n+1)) (KernelPaidCell (data i u).settlement n)
  physicalSettlement := fun i u =>
    KernelPhysicalSettlement o (data i u).calculus (data i u).settlement
  timeExhaustion := fun i u => KernelTimeExhaustion (data i u).calculus (data i u).settlement
  boundedStorage := fun i u => KernelDebitBudget (data i u).settlement
  m7ActionRealization := fun i u => KernelActionRealization a
    (data i u).renewalMass (data i u).criticalAction
  criticalEnergyBalance := fun i u => KernelCriticalBalance o i.viscosity.val
    (data i u).sigma (data i u).initialEnergy (data i u).criticalMass
    (data i u).criticalDissipation (data i u).criticalAction
  serrinInterpolation := fun i u => KernelSerrinInterpolation a (data i u).interpolationConstant
    (data i u).criticalMass (data i u).criticalDissipation (data i u).serrin
  commonCapacity := fun i u => ∀ n, KernelCommonCapacity ((data i u).frames n)
  gp509 := fun i u => GP509Certificate o (data i u).renewalMass (KernelPaidCell (data i u).settlement)
  m7 := fun i u => KernelM7 a (data i u).renewalMass
  criticalEnergy := fun i u => KernelCriticalControl a (data i u).criticalMass (data i u).criticalDissipation
  serrin46 := fun i u => KernelBounded a (data i u).serrin

/- All FIVE internal fields are theorem bodies. This is an instance for the
   explicit observables above, not an assertion that arbitrary observables
   satisfy the original abstract port record. -/
theorem reconstructed_quatros_port {a : Analysis} (o : KernelArithmetic a)
    (L : LocalTheory a .wholeSpace) (data : KernelQuatrosAssignment L) :
    QuatrosLeanPort (reconstructedQuatros o L data) := by
  constructor
  · intro i u h n
    exact kernel_birth_capacity o (h n)
  · intro i u h
    exact kernel_birth_gp509 o (data i u).frames (data i u).renewalMass
      (KernelPaidCell (data i u).settlement) h
  · intro i u birth settlement exhaustion budget
    exact kernel_settlement_m7 o
      (kernel_birth_gp509 o (data i u).frames (data i u).renewalMass
        (KernelPaidCell (data i u).settlement) birth)
      settlement exhaustion budget
  · intro i u hm ha hb
    exact kernel_m7_to_critical o hm ha hb
  · intro i u hc hi
    exact kernel_critical_to_serrin o hc hi

theorem reconstructed_quatros_stages {a : Analysis} (o : KernelArithmetic a)
    (L : LocalTheory a .wholeSpace) (data : KernelQuatrosAssignment L)
    (i : UnforcedInput a .wholeSpace) (u : L.Trajectory i)
    (h : QuatrosPhysicalInsertionFor (reconstructedQuatros o L data) i u) :
    QuatrosFullStages (reconstructedQuatros o L data) i u :=
  QUATROS_internal_stages _ (reconstructed_quatros_port o L data) i u h

theorem reconstructed_quatros_continuation {a : Analysis} (o : KernelArithmetic a)
    (L : LocalTheory a .wholeSpace) (data : KernelQuatrosAssignment L)
    (ends : QuatrosEndpointPorts (reconstructedQuatros o L data))
    (i : UnforcedInput a .wholeSpace) (u : L.Trajectory i) (hraw : L.raw i u) :
    L.continues i u :=
  QUATROS_same_solution_continuation _ (reconstructed_quatros_port o L data) ends i u hraw

theorem A_from_reconstructed_quatros {a : Analysis} (o : KernelArithmetic a)
    (L : LocalTheory a .wholeSpace) (localPorts : LocalTheoryPorts L)
    (data : KernelQuatrosAssignment L)
    (ends : QuatrosEndpointPorts (reconstructedQuatros o L data)) : A a :=
  A_from_QUATROS L localPorts _ (reconstructed_quatros_port o L data) ends

/- No critical bound, signed-payment budget, or integrated source balance is
   an entrance field: those are derived. Modal/packet differential witnesses,
   the canonical paid-prefix bound and local excess estimate are retained. -/
structure KernelMaotaotrosEntrance {a : Analysis} (o : KernelArithmetic a)
    (P : SourcePairing a) (readout : P.Carrier → Initial a)
    (Time : Type) (calculus : KernelCalculus a Time) (i : UnforcedInput a .wholeSpace) where
  rates : KernelSourceRates o P Time calculus
  theta : a.Scalar
  thetaNonnegative : a.le a.zero theta
  thetaBelowOne : a.lt theta a.one
  renewal : CanonicalSourceRenewal o (kernel_source_path_of_rates o rates) theta
  sameInitial : readout (rates.vector calculus.origin) = i.initial
  sameViscosity : rates.nu = i.viscosity.val

def reconstructedMaotaotros {a : Analysis} (o : KernelArithmetic a)
    (P : SourcePairing a) (readout : P.Carrier → Initial a)
    (Time : Type) (calculus : KernelCalculus a Time) : MaotaotrosObservables a where
  Entrance := KernelMaotaotrosEntrance o P readout Time calculus
  criticalH12 := fun _ e => KernelBounded a (fun t => P.pair (e.rates.vector t) (e.rates.vector t))
  criticalH32 := fun _ e => KernelBounded a e.rates.dissipation

theorem reconstructed_maotaotros_port {a : Analysis} (o : KernelArithmetic a)
    (P : SourcePairing a) (readout : P.Carrier → Initial a)
    (Time : Type) (calculus : KernelCalculus a Time) :
    MaotaotrosLeanPort (reconstructedMaotaotros o P readout Time calculus) := by
  constructor
  intro i e
  exact kernel_critical_split
    (canonical_source_critical o (kernel_source_path_of_rates o e.rates) e.theta
      e.thetaNonnegative e.thetaBelowOne e.renewal)

theorem reconstructed_maotaotros_critical {a : Analysis} (o : KernelArithmetic a)
    (P : SourcePairing a) (readout : P.Carrier → Initial a)
    (Time : Type) (calculus : KernelCalculus a Time) (i : UnforcedInput a .wholeSpace)
    (e : KernelMaotaotrosEntrance o P readout Time calculus i) :
    KernelBounded a (fun t => P.pair (e.rates.vector t) (e.rates.vector t)) ∧
      KernelBounded a e.rates.dissipation :=
  (reconstructed_maotaotros_port o P readout Time calculus).critical i e

theorem A_from_reconstructed_maotaotros {a : Analysis} (o : KernelArithmetic a)
    (P : SourcePairing a) (readout : P.Carrier → Initial a)
    (Time : Type) (calculus : KernelCalculus a Time)
    (ends : MaotaotrosEndpointPorts (reconstructedMaotaotros o P readout Time calculus)) : A a :=
  A_from_MAOTAOTROS _ (reconstructed_maotaotros_port o P readout Time calculus) ends

end Fefferman
