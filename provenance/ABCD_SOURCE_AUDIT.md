# Source audit: Fefferman A–D baseline and concrete closure

Audit scope: the supplied `FEF_NSE_CLASSIFICATION_LEAN_v0_7_7` (source 01), `FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0` (source 15), and the recovered `FEF_NSE_MASTERAC_TWO_LAYER_LEAN_v0_11_0` historical base. This is source inspection, not a fresh compiler receipt.

## Recommended composition

Use recovered `FEF_NSE_MASTERAC_TWO_LAYER_LEAN_v0_11_0` as the canonical core, retaining its public module identities, and add source 15's `ConcreteABCDUnifiedClosure.lean` as the concrete Mathlib extension. Source 15 is the newest supplied explicit A–D endpoint atlas. Its historical runner requires exactly this recovered v0_11_0 base; this dependency is now available rather than reconstructed from the older attachment.

The recovered base is a strict extension of source 01: all 36 old Lean paths remain, 33 are byte-identical, and the other three are `Audit.lean`, `Types.lean`, and `Feffermann-Classification.lean`. The latter changes only by importing `Fefferman.MasterAC` and `Fefferman.IntrinsicIdentification`. Ten new modules add intrinsic-force identification, MasterAC, moving frames, five physics modules and the two public layers. No old mathematical proof source was changed.

Source counts from the files:

| Source | Lean modules | Theorem declarations | Printed axiom requests |
|---|---:|---:|---:|
| Attached core v0_7_7 | 36 | 323 | 323 |
| Recovered core v0_11_0 | 46 | 366 | 362 |
| Concrete extension v0_25_0 | 1 | 141 | 99 |

A new audit should request every theorem rather than treating the historical printed requests as full coverage.

## Exact A–D content

Core `Fefferman/Statements.lean` defines `statement a c := ∀ ν : PositiveViscosity a, statementAt a ν c`:

| Case | Project proposition | Outstanding physical result |
|---|---|---|
| A | Every admissible whole-space initial datum has a qualifying global solution with zero force, for every positive viscosity. | `ConcreteReal.WholeSpaceZeroForceGlobalRegularity` |
| B | Every admissible periodic initial datum has a qualifying global solution with zero force, for every positive viscosity. | `ConcreteReal.PeriodicZeroForceGlobalRegularity` |
| C | For every positive viscosity, some admissible whole-space initial datum and admissible force have no qualifying global solution. | `ConcreteReal.WholeSpaceForcedBreakdown` |
| D | For every positive viscosity, some admissible periodic initial datum and admissible force have no qualifying global solution. | `ConcreteReal.PeriodicForcedBreakdown` |

The source definitions include momentum, divergence, initial trace, smoothness, whole-space decay and finite uniform-in-time energy, and periodic velocity/pressure as appropriate. C/D quantify over absence of every qualifying global pair, not failure of a selected trajectory.

The strongest unified source-15 theorem is `Fefferman.ConcreteReal.FEFFERMAN_ABCD_A_TIER_UNIFIED_CLOSURE_ATLAS` (line 3058). Its conclusion is the conjunction of eight **equivalences**:

1. `WholeSpaceZeroForceGlobalRegularity ↔ A realAnalysis`.
2. `PeriodicZeroForceGlobalRegularity ↔ B realAnalysis`.
3. `WholeSpaceForcedBreakdown ↔ C realAnalysis`.
4. `PeriodicForcedBreakdown ↔ D realAnalysis`.
5. `MasterABSemantic ↔ (A realAnalysis ∧ B realAnalysis)`.
6. `MasterCDSemantic ↔ (C realAnalysis ∧ D realAnalysis)`.
7. `ABCDPhysicalEndpoints ↔ (A realAnalysis ∧ B realAnalysis ∧ C realAnalysis ∧ D realAnalysis)`.
8. `ABCDPhysicalPort ↔ (A realAnalysis ∧ B realAnalysis ∧ C realAnalysis ∧ D realAnalysis)`.

`ABCDPhysicalPort` (line 2972) has four proof fields containing the four endpoints themselves. It is not a constructed PDE solution or breakdown witness. `MASTER_CD_SEMANTIC_IFF_C_AND_D` (line 3047) is an exact packaging equivalence. Neither theorem supplies any of the four endpoints.

The package README expressly says “No new PDE theorem is claimed.” Its runner reports `UNCONDITIONAL_A=OPEN`, `UNCONDITIONAL_B=OPEN`, `UNCONDITIONAL_C=OPEN`, `UNCONDITIONAL_D=OPEN`. Preserve this scope even if CI succeeds. The historical filename's “A_TIER_UNIFIED_CLOSURE” is a source identity, not independent evidence that the PDE problem was solved.

## Substantial concrete extension retained from source 15

`realAnalysis` (line 46) supplies real scalars, `Fin 3 → ℝ` space, directional `fderiv`, time `deriv`, `ContDiff`, `ContDiffOn`, and the measure integral of the explicit Euclidean norm squared.

The module also contains actual periodization and force-side proofs: integer-lattice translation equivariance, uniqueness of an active translate in a narrow support cube, local single-copy-or-zero representations, smoothness, spatial/time derivative locality, mixed-jet translation, periodicity, admissibility transfers, delayed rescaling support/smoothness, and nonzero transfer. These are separate from no-global-solution claims.

`corollary106PeriodicForceFaithful_admissible` (line 2228) still assumes positivity/width constraints, source support, source global smoothness, an initial zero gap, and `clause09 realAnalysis (delayedRescaleForce lam t0 f)`. `Corollary106FaithfulForceReady` (line 2296) packages exactly those requirements; its `.admissible` theorem does not construct them.

`PeriodicCorollary106SemanticPort` (line 2626) contains an actual force family, initial/force admissibility, and the open `noGlobal` proof field. Its `.implies_D` is conditional on that record. `WholeSpaceSourceSemanticPort` (line 2799) has the analogous C requirements. No instance of either is provided. The zero-initial breakdown routes are stronger sufficient conditions, not equivalences to C/D.

## Core branch identities and conditional theorem collections

Preserve these exact public module names: `Master_r3`, `Master_T3`, `Master_R3_details`, `Master_R3_derivation`, `Master_T3_details`, `Master_T3_derivation`, `Feffermann-Classification`. Do not normalize the spelling/capitalization silently.

`MR3 : R3EstablishedResults a` and `MT3 : T3EstablishedResults a` are assembled collections of conditional theorems. They are not the stronger legacy `MasterTheoremA`/`MasterTheoremB` targets.

- `MR3_reconstructed` additionally constructs internal QUATROS, MAOTAOTROS and covariance port proofs for their explicit observables.
- `MT3_reconstructed` additionally constructs the periodic covariance internal port.
- `A_from_MR3_QUATROS` retains local theory, same-trajectory physical insertion and classical exit.
- `A_from_MR3_MAOTAOTROS` retains entrance and same-input closure calibration.
- `A_from_MR3_storage` retains real arithmetic/physical regular-derivation ports.
- `B_from_MT3_renewal` retains periodic renewal witnesses/regular-derivation ports.
- `B_from_MT3_periodic_covariance` retains physical realization, payment and Sobolev/regularity exits.
- `CanonicalSourceRenewal.paidBound` and `.localExcess` remain source hypotheses.

`MasterTheoremA` is `DomainMaster a .wholeSpace r`; `MasterTheoremB` is its periodic version. `DomainMaster` requires sound force certificates, zero-force regular membership, and a breakdown certificate at every viscosity. `MA_implies_A_and_C` and `MB_implies_B_and_D` do not construct these requirements.

The exact source `BRANCH_IDENTIFICATIONS.tsv` keeps distinct objects for R3 signed source, heat/Mellin, QUATROS, MAOTAOTROS, covariance, T3 integrals/completion/renewal, C/D witnesses, finite spectral ledger and reduced capacity. Same datum/index does not imply equality of branch trajectories, norms or physical realizations. Retain these distinctions in any merged repository.

## Semantic and build qualifications

1. **Boundary derivative issue to review.** Core `Analysis.lean` and `SEMANTICS.txt` describe the time derivative at zero as within the closed positive half-line. Source 15 implements `timeDerivative f t := deriv f t`, the ambient two-sided derivative, while smoothness is only `ContDiffOn` the nonnegative half-space. Arbitrary negative-time extensions can therefore affect the concrete PDE clause at zero. The supplied equivalence proofs establish equivalence with the project's own definitions, not a separately checked equivalence with a boundary-correct official formulation. Preserve the source; track this as a semantic obligation or introduce a separately named corrected realization with explicit transfer proofs.
2. **Compilation evidence is historical.** Source 01 embedded metadata says new v0_7_7 compilation pending and records v0_6_1 as user-reported passed; current session memory separately reports later native Windows passes. The recovered v0_11_0 retains old release notes, so those are not a fresh compiler result. Source 15 supplies no CI log or immutable compiler/Mathlib manifest. Fresh CI should be the new authority.
3. **Mathlib pin absent.** Source 15 imports all of Mathlib but supplies no Lake manifest or exact Mathlib commit; its runner searches a user's local cached Mathlib. Pin Lean and a compatible Mathlib revision for CI rather than assuming the ambient cache identifies reproducibly.
4. **Axiom absence does not discharge hypotheses.** Endpoint proof fields and analytic ports can carry all unresolved mathematics without adding a global `axiom`. Audit theorem types as well as `#print axioms` output.
5. **Rocq provenance is not a Lean import.** Source 01's indices reference historical archives and 2,239 declarations, but those index rows do not constitute Lean proof terms or an automatic semantic bridge.

## Recovered v0_11_0 additions

`LayerA_Mathematics` imports `Feffermann-Classification` and `Fefferman.MovingFrame`; it does not import physics. `LayerB_Physics` imports Layer A and `Fefferman.PhysicsUnification`. Preserve this one-way dependency firewall.

`MasterACBreakdownWitness` contains a datum, force and internal criterion proof. `MasterAC` supplies internal zero-force regularity and nonempty internal breakdown witnesses. `MasterACProjection` separately requires admissibility and same-input regular/obstruction realization plus analytic exits. The result

```lean
MASTER_AC_IMPLIES_FEFFERMAN_A_AND_C
  (o : LedgerArithmetic a) (m : R3DerivationModel a)
  (h : MasterAC m) (p : MasterACProjection m) : A a ∧ C a
```

is conditional on constructing both `h` and `p`; no concrete instance is supplied in this base.

`IntrinsicIdentification.lean` provides a different conditional route. `R3FeffermanIntrinsicIdentification` embeds admissible forces in an abstract intrinsic class. `R3IntrinsicGlobalClosure.solve` is the explicit unsupplied hard PDE premise. Together with one positive viscosity, `R3_intrinsic_closure_identifies_Fefferman_R3_side` yields `A a ∧ ¬ C a`. Thus the positive-C MasterAC route and all-forces-regular intrinsic route are alternative conditional programs. A repository must not treat all their unresolved assumptions as jointly established.

## Recovered concrete branches: exact containment

The seven recovered concrete Lean files are **exact byte prefixes** of the attached `ConcreteABCDUnifiedClosure.lean`, with no edits to their existing content and no distinct declaration missing from v0_25_0:

| Historical package | Historical module | Bytes retained as prefix |
|---|---|---:|
| Translation closed v0_20_26_PASSFIX | `ConcretePeriodizationTranslationClosed` | 47,664 |
| Source rescaling v0_20_27 | `ConcreteSourceRescaling` | 53,325 |
| Delayed rescaling v0_20_29_PASSFIX | `ConcreteCorollary106Delayed` | 64,859 |
| Periodic B v0_21_1_FIX1 | `ConcretePeriodicBAClosure` | 70,040 |
| Periodic D v0_22_2_FIX2 | `ConcretePeriodicDAClosure` | 75,600 |
| Whole-space C v0_23_0 | `ConcreteWholeSpaceCAClosure` | 80,879 |
| Whole-space A v0_24_0 | `ConcreteWholeSpaceAAClosure` | 83,440 |

Compile only the maximal v0_25_0 concrete source. Importing the original predecessor files together would redeclare identical names in `Fefferman.ConcreteReal`. Preserve predecessor files as provenance archives outside the active import graph. If historical import paths are desired, compatibility modules may contain only `import ConcreteABCDUnifiedClosure`; they must not repeat the old bodies.

The recovered core v0_11_0 has no `Fefferman.ConcreteReal` namespace declarations, so its mathematical/physics modules can coexist with the maximal concrete extension without this duplicate-name issue. The independent forcing classifier and any additional construction modules still need their own namespace/import and compilation checks.
