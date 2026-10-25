import Fefferman.Continuation

set_option autoImplicit false

namespace Fefferman

abbrev TrajectoryPredicate {a : Analysis} {d : Domain} (L : LocalTheory a d) :=
  (i : UnforcedInput a d) → L.Trajectory i → Prop

/- QUATROS is attached here specifically to R^3. No transfer to the torus is
   inferred from its source filename or from the existence of an atlas node. -/
structure QuatrosObservables {a : Analysis} (L : LocalTheory a .wholeSpace) where
  birthFractions : TrajectoryPredicate L
  physicalSettlement : TrajectoryPredicate L
  timeExhaustion : TrajectoryPredicate L
  boundedStorage : TrajectoryPredicate L
  m7ActionRealization : TrajectoryPredicate L
  criticalEnergyBalance : TrajectoryPredicate L
  serrinInterpolation : TrajectoryPredicate L
  commonCapacity : TrajectoryPredicate L
  gp509 : TrajectoryPredicate L
  m7 : TrajectoryPredicate L
  criticalEnergy : TrajectoryPredicate L
  serrin46 : TrajectoryPredicate L

/- Mirrors the contents of QuatrosPhysicalInsertionFor. boundedStorage includes
   a nonnegative budget and a uniform bound along the time exhaustion. -/
structure QuatrosPhysicalInsertionFor {a : Analysis}
    {L : LocalTheory a .wholeSpace} (q : QuatrosObservables L)
    (i : UnforcedInput a .wholeSpace) (u : L.Trajectory i) : Prop where
  birth : q.birthFractions i u
  settlement : q.physicalSettlement i u
  exhaustion : q.timeExhaustion i u
  storage : q.boundedStorage i u
  actionRealization : q.m7ActionRealization i u
  balance : q.criticalEnergyBalance i u
  interpolation : q.serrinInterpolation i u

/- PORT OBLIGATIONS: these fields must be proved in Lean from the ported Rocq
   mathematics with genuine observable definitions. The source ZIP is not an
   imported Lean theorem. ReconstructedRoutes supplies an instance for its
   explicit source-derived observables; arbitrary observables still need a port. -/
structure QuatrosLeanPort {a : Analysis} {L : LocalTheory a .wholeSpace}
    (q : QuatrosObservables L) : Prop where
  birthToCapacity : ∀ i u, q.birthFractions i u → q.commonCapacity i u
  birthToGP509 : ∀ i u, q.birthFractions i u → q.gp509 i u
  settlementToM7 : ∀ i u, q.birthFractions i u → q.physicalSettlement i u →
    q.timeExhaustion i u → q.boundedStorage i u → q.m7 i u
  m7ToCritical : ∀ i u, q.m7 i u → q.m7ActionRealization i u →
    q.criticalEnergyBalance i u → q.criticalEnergy i u
  criticalToSerrin : ∀ i u, q.criticalEnergy i u → q.serrinInterpolation i u →
    q.serrin46 i u

structure QuatrosEndpointPorts {a : Analysis} {L : LocalTheory a .wholeSpace}
    (q : QuatrosObservables L) : Prop where
  insert : ∀ i u, L.raw i u → QuatrosPhysicalInsertionFor q i u
  classicalExit : ∀ i u, L.raw i u → q.serrin46 i u → L.continues i u

structure QuatrosFullStages {a : Analysis} {L : LocalTheory a .wholeSpace}
    (q : QuatrosObservables L) (i : UnforcedInput a .wholeSpace)
    (u : L.Trajectory i) : Prop where
  capacity : q.commonCapacity i u
  gp509 : q.gp509 i u
  m7 : q.m7 i u
  critical : q.criticalEnergy i u
  serrin : q.serrin46 i u

theorem QUATROS_internal_stages {a : Analysis} {L : LocalTheory a .wholeSpace}
    (q : QuatrosObservables L) (port : QuatrosLeanPort q)
    (i : UnforcedInput a .wholeSpace) (u : L.Trajectory i)
    (h : QuatrosPhysicalInsertionFor q i u) : QuatrosFullStages q i u := by
  have hm7 := port.settlementToM7 i u h.birth h.settlement h.exhaustion h.storage
  have hcritical := port.m7ToCritical i u hm7 h.actionRealization h.balance
  exact {
    capacity := port.birthToCapacity i u h.birth
    gp509 := port.birthToGP509 i u h.birth
    m7 := hm7
    critical := hcritical
    serrin := port.criticalToSerrin i u hcritical h.interpolation
  }

theorem QUATROS_same_solution_continuation {a : Analysis}
    {L : LocalTheory a .wholeSpace} (q : QuatrosObservables L)
    (port : QuatrosLeanPort q) (ends : QuatrosEndpointPorts q)
    (i : UnforcedInput a .wholeSpace) (u : L.Trajectory i)
    (hraw : L.raw i u) : L.continues i u := by
  have hs := QUATROS_internal_stages q port i u (ends.insert i u hraw)
  exact ends.classicalExit i u hraw hs.serrin

theorem A_from_QUATROS {a : Analysis} (L : LocalTheory a .wholeSpace)
    (localPorts : LocalTheoryPorts L) (q : QuatrosObservables L)
    (port : QuatrosLeanPort q) (ends : QuatrosEndpointPorts q) : A a :=
  A_of_continuation L localPorts (QUATROS_same_solution_continuation q port ends)

/- MAOTAOTROS preserves its initial datum and its entrance object. The attached
   source does not identify its trajectory with a QUATROS trajectory. -/
structure MaotaotrosObservables (a : Analysis) where
  Entrance : UnforcedInput a .wholeSpace → Type
  criticalH12 : (i : UnforcedInput a .wholeSpace) → Entrance i → Prop
  criticalH32 : (i : UnforcedInput a .wholeSpace) → Entrance i → Prop

structure MaotaotrosLeanPort {a : Analysis} (m : MaotaotrosObservables a) : Prop where
  critical : ∀ i e, m.criticalH12 i e ∧ m.criticalH32 i e

structure MaotaotrosEndpointPorts {a : Analysis} (m : MaotaotrosObservables a) where
  enter : (i : UnforcedInput a .wholeSpace) → m.Entrance i
  close : ∀ i e, m.criticalH12 i e → m.criticalH32 i e → inputSolved i

theorem MAOTAOTROS_same_input_closure {a : Analysis} (m : MaotaotrosObservables a)
    (port : MaotaotrosLeanPort m) (ends : MaotaotrosEndpointPorts m)
    (i : UnforcedInput a .wholeSpace) : inputSolved i := by
  have hc := port.critical i (ends.enter i)
  exact ends.close i (ends.enter i) hc.1 hc.2

theorem A_from_MAOTAOTROS {a : Analysis} (m : MaotaotrosObservables a)
    (port : MaotaotrosLeanPort m) (ends : MaotaotrosEndpointPorts m) : A a :=
  unforced_from_inputs (MAOTAOTROS_same_input_closure m port ends)

/- Covariance prefix estimates need BOTH physical realization and renewal
   payment. A domain-specific binding is required even though its algebra can
   be abstracted over either domain. -/
structure CovarianceObservables (a : Analysis) (d : Domain) where
  Object : UnforcedInput a d → Type
  physicalPrefixRealization : (i : UnforcedInput a d) → Object i → Prop
  uniformRenewalPayment : (i : UnforcedInput a d) → Object i → Prop
  uniformGPBound : (i : UnforcedInput a d) → Object i → Prop
  serrin : (i : UnforcedInput a d) → Object i → Prop

structure CovarianceLeanPort {a : Analysis} {d : Domain}
    (g : CovarianceObservables a d) : Prop where
  prefixBound : ∀ i o, g.physicalPrefixRealization i o →
    g.uniformRenewalPayment i o → g.uniformGPBound i o

structure CovarianceEndpointPorts {a : Analysis} {d : Domain}
    (g : CovarianceObservables a d) where
  object : (i : UnforcedInput a d) → g.Object i
  realization : ∀ i, g.physicalPrefixRealization i (object i)
  payment : ∀ i, g.uniformRenewalPayment i (object i)
  sobolev : ∀ i o, g.uniformGPBound i o → g.serrin i o
  regularity : ∀ i o, g.serrin i o → inputSolved i

theorem COVARIANCE_same_input_closure {a : Analysis} {d : Domain}
    (g : CovarianceObservables a d) (port : CovarianceLeanPort g)
    (ends : CovarianceEndpointPorts g) (i : UnforcedInput a d) : inputSolved i := by
  have hb := port.prefixBound i (ends.object i) (ends.realization i) (ends.payment i)
  exact ends.regularity i (ends.object i) (ends.sobolev i (ends.object i) hb)

theorem A_from_COVARIANCE {a : Analysis} (g : CovarianceObservables a .wholeSpace)
    (port : CovarianceLeanPort g) (ends : CovarianceEndpointPorts g) : A a :=
  unforced_from_inputs (COVARIANCE_same_input_closure g port ends)

theorem B_from_periodic_COVARIANCE {a : Analysis}
    (g : CovarianceObservables a .periodic) (port : CovarianceLeanPort g)
    (ends : CovarianceEndpointPorts g) : B a :=
  unforced_from_inputs (COVARIANCE_same_input_closure g port ends)

end Fefferman
