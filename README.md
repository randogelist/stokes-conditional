# NSE 3D — Fefferman A, B, C, D

This branch consolidates the strongest recoverable Fefferman classification and forcing extensions from the supplied project archives and identified project branches. It builds **59 active Lean modules** with Lean **4.33.0** and a fixed Mathlib revision, and preserves **26 source archives** and **190 distinct Rocq reference files**.

The mathematical result is a conditional theorem architecture and an endpoint-equivalence atlas. **No unconditional physical Fefferman A, B, C, or D endpoint is established by this consolidation.** CI success means that the actual statements compile and pass the declared axiom audit. It does not discharge their hypotheses or establish independent equivalence with the official PDE problem.

## Active source anchors

| Component | Recovered identity | Active source |
|---|---|---|
| Core classification, R³/T³ branches, MasterAC, mathematical/physics layers | `FEF_NSE_MASTERAC_TWO_LAYER_LEAN_v0_11_0` | `Fefferman/`, `Master_*`, `LayerA_Mathematics.lean`, `LayerB_Physics.lean` |
| Concrete real analysis, periodization, delayed rescaling, A–D endpoint atlas | `FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0` | `ConcreteABCDUnifiedClosure.lean` |
| Scalar force-exponent classifications | `NSE_FORCING_REGULARITY_CLASSES_LEAN_v0_1_4` | `NSEForcingRegularityClasses.lean` |
| Same-trajectory LH → GP/BKQR → M7 → Serrin → continuation | `NSE_LH_GP_BKQR_M7_SERRIN_LEAN_v0_1_0` | `NSE/` |

The original public names `Master_r3`, `Master_T3`, `Master_R3_details`, `Master_R3_derivation`, `Master_T3_details`, `Master_T3_derivation`, and `Feffermann-Classification` are retained exactly. Historical names containing `A_TIER` are source identities, not new certification claims.

The v0.11.0 core contains all 36 modules of the attached v0.7.7 core and adds 10 modules. All seven recovered concrete predecessors through A/v0.24.0 are exact byte prefixes of the unified v0.25.0 module. They are archived rather than imported twice. Active mathematical source bytes are preserved; build integration and audits are new.

## Endpoint map

All names below are in `Fefferman.ConcreteReal`.

| Fefferman case | Project endpoint | Physical status |
|---|---|---|
| A | `WholeSpaceZeroForceGlobalRegularity` | Open |
| B | `PeriodicZeroForceGlobalRegularity` | Open |
| C | `WholeSpaceForcedBreakdown` | Open |
| D | `PeriodicForcedBreakdown` | Open |

`FEFFERMAN_ABCD_A_TIER_UNIFIED_CLOSURE_ATLAS` collects equivalences between these endpoints and `Fefferman.A/B/C/D realAnalysis`. `ABCDPhysicalPort` has proof fields for the endpoints themselves; no instance is supplied. The C/D semantic ports retain an explicit `noGlobal` hypothesis. Their existence is not a constructed counterexample.

`MASTER_AC_IMPLIES_FEFFERMAN_A_AND_C` is conditional on its internal `MasterAC` and projection data. The separate intrinsic global-closure route implies A and ¬C under different hypotheses. Neither branch supplies a universal physical instance, and they must not be combined by dropping their premises.

The forcing classifier proves partitions of scalar exponent regions. Its `ActualSobolevSpaceRealizationFrontier := True` is a historical status marker, not an analytic realization theorem. Rocq labels such as `ForcedRegularClassA` and `ForcedBreakdownClassB` are forcing-ledger classes, not the Fefferman case letters.

## Build and CI

The workflow in [`.github/workflows/lean.yml`](.github/workflows/lean.yml) installs Lean on Linux and Windows runners, retrieves the compatible Mathlib cache, compiles every active module, and audits every project declaration by its originating module. It permits only `propext`, `Classical.choice`, and `Quot.sound` as axioms. Custom axioms, proof escapes, unsafe declarations, and unexpected axioms fail verification.

Mathlib is fixed at `db584cd6d46c92f209a44c0f1c829460d327499d` (v4.33.0); transitive revisions are locked in `lake-manifest.json`. The mathematical Layer A dependency closure is checked for physics imports. The reference Rocq collection is preserved for provenance; this Lean CI does not compile Rocq or certify a complete Rocq-to-Lean translation.

With Python 3 and elan installed:

```sh
elan toolchain install leanprover/lean4:v4.33.0
python scripts/verify.py --fetch-cache
```

On Windows, run `run.cmd`. For source and infrastructure checks without Lean:

```sh
python -m unittest discover -s scripts -p "test_*.py"
python scripts/verify.py --prepare-only
```

Lake reuses unchanged artifacts when its dependency traces remain valid. CI caches are separated by operating system, architecture, compiler, and dependencies. Windows `.olean` files are not reused as Linux proofs. Each successful verification produces `artifacts/anchor-receipt.json`, recording compiler, platform, source/dependency hashes, declaration counts, artifact hashes, and explicit open endpoint status. The workflow uploads the receipt and logs. Source preparation alone never creates a PASS receipt.

## Semantic frontier

The concrete `timeDerivative` is the ambient `deriv`, while smoothness is `ContDiffOn` on the closed positive half-space and the core documentation calls for a half-line derivative. At t = 0 an identification theorem or a corrected realization is still needed. The existing endpoint equivalences are internal to the implemented `realAnalysis`.

The `NSE` branch still requires physical norm realization, modal/ledger laws, payment estimates, and a same-trajectory analytic continuation interface. Sharing a repository does not construct an identification between its abstract trajectory and the concrete Fefferman solution object.

See [semantic review](provenance/SEMANTIC_REVIEW.md), [A–D source audit](provenance/ABCD_SOURCE_AUDIT.md), and [extension audit](provenance/EXTENSION_SOURCE_AUDIT.md). The reference problem is [Fefferman's official Clay statement](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf).

## Provenance

[`provenance/sources.json`](provenance/sources.json) records archive identities and SHA-256 digests. [`provenance/active_source_origins.json`](provenance/active_source_origins.json) maps each active source to exact archive members. The original archives are in `provenance/archives/`; readable Rocq sources and their origin map are in `reference/rocq/` and `provenance/rocq_origins.json`.

The GitHub source branch was recovered from `randogelist/stokes-conditional` at commit `4b370556eb008ba8a03f7019875f9595b094738f`. Original root archives and the main branch are retained. This consolidation is developed on `nse-fefferman-abcd-consolidated`.
