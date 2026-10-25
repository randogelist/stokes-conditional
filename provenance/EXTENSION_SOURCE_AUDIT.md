# Source audit: force classification and GP Diamond extensions

Scope: byte comparison and source inspection of the supplied packages 02–14, with comparison to baseline 01 and overlay 15. This report does not certify compilation. No files in the supplied source trees were modified.

## Recommended source selection

- Lean semantic/master baseline: `FEF_NSE_CLASSIFICATION_LEAN_v0_7_7` (package 01).
- Concrete real-valued A–D overlay: `FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0` (package 15). Its first imports are Mathlib, Fefferman.Analysis and Fefferman.Statements: it requires the baseline but is not a replacement for its source tree.
- Lean force exponent classification: `NSE_FORCING_REGULARITY_CLASSES_LEAN_v0_1_4` (package 12), compiled as a separate extension module, with its limited semantics explicitly documented.
- Most developed supplied Rocq Diamond branch: `NSE_R3_FORCED_GP_DIAMOND_UNIFORM_ACTION_COST_v0_22_0` (package 14).
- Independent trajectory-relative force-classification branch: `NSE_GP_FORCING_CLASSIFICATION_v0_1_1` (package 11), retained alongside the Diamond branch because it contains additional source modules.

## Byte comparison

Package 14 contains 52 `.v` files. Every `.v` file from packages 02–09 and package 13 exists under the same basename with identical bytes in package 14. There are respectively 33, 34, 35, 36, 37, 38, 39, 40 and 51 Rocq source files in those predecessors. Their only differing same-name files are `_CoqProject`, `build_order.txt`, `SHA256SUMS.txt`, and `run.ps1`; therefore retaining v0_22_0 plus provenance preserves all mathematical sources on this branch.

Packages 10 and 11 each contain 40 `.v` files. Their common-name `.v` files are byte-identical. The v0_1_1 classification source differs from v0_1_0 by adding two explicit `Require Import` lines (finite algebra and source storage dynamics), without changing its mathematical body. The embedded STATUS text still says V0_1_0; this is stale metadata, not evidence that v0_1_1 is older.

Package 11 has these ten source filenames absent from package 14:

- `awpi_nse_gp_source_storage_dynamics_v0_51_0.v`
- `awpi_nse_gp_forcing_classification_v0_1_1.v`
- `awpi_nse_gp_source_m7_energy_join_v0_51_0.v`
- `awpi_nse_gp_unforced_lh_operator_compatibility_v0_1_0.v`
- `awpi_nse_gp_pair_source_calculus_v0_51_0.v`
- `awpi_nse_gp_unforced_lh_ae_integrated_m7_bridge_v0_1_2.v`
- `awpi_nse_gp_fixed_allocation_v0_51_0.v`
- `awpi_nse_gp_signed_source_closure_v0_51_0.v`
- `awpi_nse_gp_unforced_lh_ae_source_entrance_v0_1_1.v`
- `awpi_nse_gp_unforced_operator_class_v0_1_0.v`

The 30 common source files between 11 and 14 are identical. A consolidated archival Rocq tree can therefore retain the 62 unique `.v` sources (52 + 10), provided the two branch build orders and original identities remain explicit. Alternatively retain the two original trees; avoid treating archive inclusion as a Lean port.

## Strongest Diamond result and premises

File: package14 `NSE_R3_FORCED_GP_DIAMOND_UNIFORM_ACTION_COST.v`.

`UAC00_UNIFORM_GK_ENVELOPE_GIVES_COMMON_PAID_PREFIX` (line 43) proves a common paid-prefix budget from uniform GK cost and initial-drift envelopes. `UAC10_GK_ENVELOPES_PLUS_INITIAL_MASS_GIVE_UNIFORM_ROUTE_BUDGET` (line 111) assembles three such channel envelopes plus common initial mass/action bounds into `UniformRouteBudget`.

`UAC22_ACTION_COST_COUPLING_CONTROLS_FULL_CRITICAL_READOUT` (line 230) is the strongest supplied uniform action-cost endpoint:

```
0 <= M0max
(forall c, initial_mass c <= M0max)
UniformRouteBudget Cut dstar route A0max Bs Bf Br
FiniteCutActionCostRouteRealization
UniformFiniteCutCriticalBalance
(forall t, FullCriticalLimitReadout Cut (fun c => critical_mass c t) (full_mass t))
→ exists B, forall t, full_mass t <= B.
```

Its constructive bound in UAC20 is `M0max + 4*A0max + Bs + Bf + Br`. The action prefix pays `action_cost`, then the critical energy balance adds initial mass separately. It should not be replaced by the earlier mass-to-prefix coupling without justification.

The source does not construct the actual PDE route family, prove uniform payment bounds for that family, derive the critical balance from actual solutions, or establish the full critical readout. Those are hypotheses. It also does not by itself conclude Fefferman global smooth existence or admissible breakdown.

## Intrinsic force class

File: package14 `NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.v`.

- `IF01_GLOBAL_STOKES_FORCE_ABSORPTION` (line 36) derives a Young-type force-work bound assuming `FractionalStokesRealization`.
- `IF02_INTRINSIC_FORCE_SIZE_IS_LEAST_UNIFORM_COEFFICIENT` (line 74) identifies its least coefficient within that supplied geometry.
- `IntrinsicCriticalForceClassA` (line 119) is boundedness of an accumulated intrinsic force-size function; `accumulate_until` is an arbitrary supplied operation in this theorem layer.
- `IF10_INTRINSIC_FORCE_CLASS_PLUS_INTERNAL_LEDGER_GIVES_REGULARITY` (line 127) concludes `UniformCriticalEnergy`, assuming `ForcedCriticalEnergyBalance`, bounded internal cost, and the intrinsic class. Despite the declaration name, it does not directly conclude classical smooth NSE regularity.
- `IF20_CLASSICAL_HMINUSHALF_IS_OPTIONAL_READOUT` (line 162) simply applies a supplied `ClassicalHMinusHalfReadout` equality. It does not construct that equality.

`README_INTRINSIC_FORCE_CLASS.txt` explicitly retains deriving the integrated forced balance from the PDE/time integration as an analytic interface. Classical H^{-1/2} naming is optional within the abstract ledger proof, but a physical realization of the intrinsic operators and accumulated cost is still needed for the actual NSE endpoint.

## Breakdown/classification semantics

File: package14 `NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.v`.

`ForcedRegularClassA` is the conjunction of two bounded scalar ledgers. `FD02_CLASS_A_GIVES_UNIFORM_CRITICAL_ENERGY` proves a bound from the supplied forced energy balance. `ForcedBreakdownClassB` combines an exact scalar net-work balance with unbounded-above net work. `FD13_CLASS_B_EXCLUDES_PHYSICAL_REGULARITY` requires a separate implication `PhysicalRegular -> CriticalMassBounded` (line 171). It is not a constructed smooth admissible force/datum yielding a Fefferman C or D counterexample.

The letters “Class A” and “Class B” in these Rocq definitions denote force-ledger classes, not Fefferman's alternatives A and B. Keep this distinction visible in documentation.

File: package11 `awpi_nse_gp_forcing_classification_v0_1_1.v`.

`GPRegularitySafeForcing51` (line 136) is trajectory-relative: it assumes the internal signed production budget, a relative external forcing budget, and `theta_i + theta_f < 1`. `GFC21_SAFE_FORCING_GIVES_CRITICAL_BOUNDS` (line 266) combines this with `ForcedIntegratedGPLedger51` (line 213). Neither ordinary smoothness of f nor time-integrability alone is asserted sufficient. The source explicitly marks these claim boundaries at lines 346–349. Literal zero forcing has zero external GP budget, but `GFC12_ZERO_FORCE_IS_SAFE_WHEN_INTERNAL_MARGIN_IS_SUBUNIT` still assumes the internal subunit budget; zero forcing does not solve that internal obligation.

## Lean exponent classification is a different layer

File: package12 `NSEForcingRegularityClasses.lean`.

This imports Mathlib and defines the scalar function `s + 3/2 - 2/q` (line 14), its zero set, and scalar threshold predicates. Its algebraic results include:

- `CRITICAL_FORCING_SCALING_LINE` (line 53),
- `L2_LH_TRICHOTOMY_SMOOTH_CRITICAL_ROUGH` (line 105),
- `EXACT_CRITICAL_IFF_SCALING_ZERO` (line 115),
- `POWER_TAIL_TRICHOTOMY` (line 149).

The power-tail thresholds are definitions, and their threshold iff theorems are `rfl`; there is no actual Fourier/Sobolev membership or integrability proof here. The source explicitly excludes solution-regularity and solution-breakdown claims (lines 169 and 173). `ActualSobolevSpaceRealizationFrontier : Prop := True` (line 177) is a status marker only and must not count as a proved analytic realization. Its comment “Lean mirror of the GP-independent Rocq forcing classification” should not be read as a full port of package11's trajectory-relative GP ledger theorem chain.

## Connection to baseline semantic force regimes

Package01 `Fefferman/ForceRegimes.lean` defines `regularForceAt` as an admissible force plus existence of a qualifying global solution for every admissible datum, and `breakdownForceAt` as an admissible force plus some datum with no qualifying global solution. `ForceRegimeSoundness` retains the two semantic implications as fields. `admissibleForce_regular_or_breakdown` is classical excluded middle, explicitly not an effective classifier.

Accordingly, scalar exponent classes, intrinsic force norms, GP budgets, or unbounded ledgers need actual realization and the appropriate soundness/continuation or obstruction theorem before being inserted into this semantic interface. Failure of a sufficient upper-bound criterion does not establish breakdown.

The supplied baseline preserves exact branch identities in `BRANCH_IDENTIFICATIONS.tsv` and records conditional cross-branch interfaces in `CROSS_BRANCH_PORTS.tsv`: R3 signed source, R3 heat/Mellin, QUATROS, MAOTAOTROS, covariance, T3 integrals/completion, C/D witnesses, finite spectral ledger, and reduced capacity. These should remain tracked independently; merging source files does not discharge their same-trajectory and physical realization obligations.

## CI implications

- Build the core baseline and concrete Mathlib overlay as Lean targets; audit their actual theorem axioms.
- Include the standalone exponent classification in Lean CI, with an audit target for its substantive theorems.
- Preserve the strongest Rocq branches as source/provenance, clearly marked unported unless a dedicated Rocq CI job is actually added and passed.
- Do not use filenames containing `A_TIER` or `UNIFIED_CLOSURE`, STATUS strings, `True` markers, source checksums, or historical user-reported passes as evidence that new combined CI has passed or that Fefferman A–D physical endpoints have been proved.


## Recovered anchors and existing GitHub branch — updated selection

Subsequent recovery supplied `branch_review/NSE_CLAY_FEFFERMAN_ABCD_DIAMOND_v0_27_6` and the existing GitHub `stokes-conditional` source trees under `existing_review`. The following updates supersede the earlier recommendation of package14 as the most developed available Diamond archive.

### Recovered Rocq v0_27_6

The recovered anchor contains 77 `.v` sources. It includes all 52 package14 sources byte-for-byte and adds 25 sources, including the explicit Fefferman framework and A/B/C/D fronts, a storage bridge, integrated storage/payment modules, and periodic Fourier geometry. The independent package11 still contributes ten additional source filenames; all shared filenames remain byte-identical.

`NSE_CLAY_FEFFERMAN_FRAMEWORK.v` develops a substantive contraction:

- `R3StorageTerminalWitness d f` records finite-cut shell evolutions, storage paths, same-time/cofinal cuts, evolution bindings, exact integrated storage, initial-storage bounds, lower-output payments, strict high-output absorption and full critical readout.
- `FW40_STORAGE_TERMINAL_WITNESS_GIVES_UNIFORM_CRITICAL_BOUND` calls `NSRA99_STORAGE_REPLENISHMENT_TO_EXISTING_M7_TERMINAL` to derive the critical bound from those witness fields. This removes a separately assumed abstract storage-to-critical implication, conditional on the detailed witness.
- `ConcreteR3StorageDiamondClosure` still assumes actual witness existence for each admissible datum and intrinsic force, plus a classical critical-to-smooth exit.
- `A10_R3_CONCRETE_STORAGE_DIAMOND_GIVES_FEFFERMAN_A` is conditional on that closure.
- `B10_T3_DOMAIN_DIAMOND_GIVES_FEFFERMAN_B` remains conditional on `T3_DOMAIN_DIAMOND`; finite periodic plane-wave geometry and product/convolution identities are established by imported sources.
- `C20_R3_CONCRETE_STORAGE_DIAMOND_PLUS_CLAY_FORCE_EMBEDDING_EXCLUDES_FEFFERMAN_C` concludes **not C**, assuming the concrete R3 closure and embedding of all admissible forces into the intrinsic class.
- `D20_T3_DOMAIN_DIAMOND_PLUS_CLAY_FORCE_EMBEDDING_EXCLUDES_FEFFERMAN_D` concludes **not D**, assuming the periodic closure and force embedding.

In particular, the filenames for the C/D fronts do not mean that counterexamples are constructed. The branch proves conditional exclusions and necessary conditions on any counterexample. The top-level `FORMAL_SUMMARY.txt` explicitly retains `R3_STORAGE_WITNESS_REALIZATION=OPEN_RESEARCH_INTERFACE` and `R3_CRITICAL_TO_SMOOTH_EXIT=OPEN_CLASSICAL_INTERFACE`; its internal title still says v0.27.3, a stale summary label inside the recovered v0_27_6 package.

### Existing Rocq LH→GP→BKQR→M7→Serrin branch

`NSE_LH_GP_BKQR_M7_SERRIN_v0_1_0` contains 116 `.v` sources. Fourteen share basenames with recovered v0_27_6, all byte-identical; 102 are additional. The union of recovered v0_27_6, package11 and this existing Rocq branch contains **189 unique `.v` filenames, with no same-name byte conflicts**. Preserve original tree provenance and build orders even if deduplicating a source archive.

This branch should remain represented in the repository. The 116-module Rocq chain and the compact Lean chain below are separate formalizations: the Lean port does not trust Rocq binaries and is not a declaration-for-declaration port of all 116 modules.

### Existing compact Lean chain

`existing_review/NSE_LH_GP_BKQR_M7_SERRIN_LEAN_v0_1_0 (2)/NSE_LH_GP_BKQR_M7_SERRIN_LEAN_v0_1_0` contains eleven mathematical/audit Lean modules under `NSE/`, plus `lakefile.lean`. All local imports are within `NSE`; its declarations use `NSE`/`NSE.Representation`/`NSE.HilbertEntrance`, disjoint from the Fefferman namespace and module paths. It can be retained without renaming and built as a separate `lean_lib NSE` in the consolidated project.

The existing package pins:

```
Lean: leanprover/lean4:v4.33.0
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d
```

Its `lake-manifest.json` pins transitive package revisions. Reuse this complete dependency lock when consolidating, rather than merely pinning a branch name. Compilation in the combined project still must be run; source compatibility and historical logs do not substitute for it.

Useful modules and exact role:

| Module | Contribution | Retained boundary |
| --- | --- | --- |
| `NSE.Representation` | Countable Enc↔GP↔BKQR equivalences; canonical infinite normalized q-profile; exact weak-equation transport | Physical Hilbert/PDE model is supplied |
| `NSE.HilbertEntrance` | Parseval, analysis/synthesis and coordinate realization from actual Mathlib Hilbert basis or dense orthonormal family | Concrete solenoidal R3/torus space is not instantiated |
| `NSE.CriticalBalance` | Finite modal critical balance from ordinary derivatives, including zero-capacity algebra | Modal laws and primitives are inputs |
| `NSE.PrefixPayment` | M7 debt telescope; explicit `(Seed+Paid)/(96/605-theta)` budget; strict-margin counterexample | Uniform cumulative charge is an assumption, not implied by LH energy alone |
| `NSE.Completion` | Actual real supremum totals, monotone cutoff convergence, l2 membership | Spatial/time integral identification is separate |
| `NSE.Injection` | Critical realization produces finite and countable critical bounds | Actual PDE realization and source/dissipation primitives remain supplied |
| `NSE.Serrin` | Genuine Mathlib Lebesgue integral estimates and derived local fourth-power integrability | Physical Sobolev readouts and Serrin exit contract remain explicit |
| `NSE.Continuation` | Same-trajectory composition from representation through M7 and Serrin | SamePathNormRealization and same-solution exit are supplied |
| `NSE.LHLedger` | Derives LH dissipation-ledger upper bound by initial energy; specializes cumulative payment | Prefix charge still needs proof |
| `NSE.NSEAnchor` | Uses the same weak viscous/nonlinear readouts and trajectory; preserves full nonspectral viscous remainder | Ordinary modal derivative law is not inferred from the weak equation |
| `NSE.Audit` | Audits every custom NSE declaration, rejects unsafe/custom axioms, permits only propext/choice/Quot.sound transitively | Does not establish physical equivalence of the mathematical statement |

Main conditional endpoints:

```
NSE.nse_lh_gp_bkqr_m7_serrin_continuation
NSE.nse_lh_ledger_gp_bkqr_m7_serrin_continuation
```

`NSE.Audit` imports the entire chain plus HilbertEntrance. Its standalone run `lake env lean NSE/Audit.lean` executes an all-custom-declaration audit, logs `ALL_CUSTOM_AXIOMS=PASS`, and prints endpoint axiom dependencies. Preserve it and include it in consolidated CI. The package also requests `lake env leanchecker NSE` and `lake env leanchecker --fresh NSE.Audit`; only report these as passed after observing the new CI result.

These eleven modules are a meaningful stronger countable/analytic realization layer than the abstract Fefferman scalar adapters. They can coexist safely with the Fefferman baseline by namespace separation. They do not automatically discharge the Fefferman physical ports: a bridge must instantiate their exact same trajectory and readouts into Fefferman's actual admissibility/global-solution definitions. No such bridge is justified solely by shared names.

Updated maximum-source recommendation: compile the strongest available Fefferman Lean baseline and concrete A–D overlay, package12's exponent module, and all eleven existing NSE modules; retain recovered v0_27_6, package11, and the 116-module Rocq branch with exact provenance. Keep each formalization's theorem premises and positive/negative endpoint direction explicit.
