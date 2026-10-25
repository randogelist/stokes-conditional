# The generalized Fefferman classification

This document identifies the most general classification framework already present in the recovered sources. **It adds documentation, not a Lean theorem or a physical construction. The unconditional physical endpoints A, B, C and D remain OPEN.** The terminology below distinguishes a classification interface, conditional derivation theorems, and concrete endpoint equivalences.

Read the accompanying [generalized Fefferman preprint](../paper/generalized_fefferman_preprint.pdf) for the manuscript presentation and its claim-status distinctions.

## General object and scope

The broadest existing classification interface is `ForceRegimes a d` together with `ForceRegimeSoundness a d r` in [ForceRegimes.lean](../Fefferman/ForceRegimes.lean). Its parameters are an analytic interpretation `a : Analysis`, a domain `d : Domain`, a positive viscosity, and a force. `Domain` has exactly two constructors, `wholeSpace` and `periodic`; spatial dimension remains three. [Analysis.lean](../Fefferman/Analysis.lean) supplies the abstract scalar, derivative, smoothness and integral interfaces. An arbitrary interpretation of those interfaces is not automatically real Navier–Stokes analysis.

The certificate interface is:

```lean
structure ForceRegimes (a : Analysis) (d : Domain) where
  regular : PositiveViscosity a → Force a → Prop
  breakdown : PositiveViscosity a → Force a → Prop
```

`ForceRegimeSoundness` separately requires that each regular certificate implies `regularForceAt`, and each breakdown certificate implies `breakdownForceAt`. Thus choosing criteria is distinct from proving their physical meaning. These objects generalize the four endpoint labels by retaining the force as an argument.

## Exact semantic dichotomy

Fix `a`, `d`, a positive viscosity `ν`, and a force `f`. Write $I_d(u_0)$ for `admissibleInitial`, $F_d(f)$ for `admissibleForce`, and

$$
G_d(\nu,u_0,f)
:=\exists s,\ \operatorname{globalSolution}(a,d,\nu,u_0,f,s).
$$

The definitions in [Statements.lean](../Fefferman/Statements.lean) and [ForceRegimes.lean](../Fefferman/ForceRegimes.lean) give

$$
\begin{aligned}
R_d(\nu,f)&:=F_d(f)\land
  \forall u_0,\ I_d(u_0)\to G_d(\nu,u_0,f),\\
B_d(\nu,f)&:=F_d(f)\land
  \exists u_0,\ I_d(u_0)\land\neg G_d(\nu,u_0,f).
\end{aligned}
$$

Here $B_d$ abbreviates the semantic breakdown predicate, not Fefferman case B. A qualifying global solution includes the project's momentum, incompressibility, initial trace, smoothness, and domain-specific energy or periodicity conditions. Decay requirements belong to initial-data and force admissibility. Breakdown excludes every qualifying global pair; failure of one selected trajectory is insufficient.

For admissible `f`, `admissibleForce_regular_or_breakdown` proves $R_d(\nu,f)\lor B_d(\nu,f)$. Its proof applies classical excluded middle to

$$
P:=\forall u_0,\ I_d(u_0)\to G_d(\nu,u_0,f).
$$

If $P$, regularity follows. If not, classical quantifier negation supplies an admissible $u_0$ with no qualifying solution. `regularForceAt_excludes_breakdownForceAt` proves disjointness: the regular assertion applied to that same datum contradicts the breakdown assertion. This is a classical dichotomy, not an algorithm deciding which alternative holds.

## Certificates and the generalized list

For selected criteria `r`, `unresolvedForceAt r ν f` means

$$
F_d(f)\land\neg r.\mathrm{regular}(\nu,f)
       \land\neg r.\mathrm{breakdown}(\nu,f).
$$

`admissibleForce_certificate_trichotomy` proves that every admissible force has a regular certificate, a breakdown certificate, or neither. The proof applies excluded middle successively to the two certificate predicates. Under `ForceRegimeSoundness`, `certified_regimes_disjoint` excludes simultaneous certificates. “Unresolved” records incompleteness of the chosen criteria; it is not a third physical truth value.

| Domain | Regular certificate | Breakdown certificate | Unresolved |
|---|---|---|---|
| Whole space | Global solution for every admissible datum | Some admissible datum has none | Neither criterion certified |
| Periodic | Global periodic solution for every admissible datum | Some admissible periodic datum has none | Neither criterion certified |

No completeness theorem equates arbitrary certificate predicates with the semantic predicates. Weak existence, uniqueness and nonuniqueness are not additional outcomes of this six-cell list. The preserved [force-regime inventory](../provenance/historical_core/FORCE_REGIMES.tsv) records this same separation.

## Force families: manuscript notation

For a family $\mathcal C\subseteq\{f:F_d(f)\}$, the preprint introduces

$$
\begin{aligned}
\mathsf{AllRegular}_{d,\nu}(\mathcal C)
  &\iff \forall f\in\mathcal C,\ R_d(\nu,f),\\
\mathsf{SomeBreakdown}_{d,\nu}(\mathcal C)
  &\iff \exists f\in\mathcal C,\ B_d(\nu,f).
\end{aligned}
$$

These are **manuscript notation, not additional exported Lean objects**. Semantic dichotomy and disjointness give the editorial corollary $\mathsf{AllRegular}_{d,\nu}(\mathcal C)\iff\neg\mathsf{SomeBreakdown}_{d,\nu}(\mathcal C)$: apply the dichotomy to each member of the admissible family. The singleton zero-force family recovers unforced regularity when zero force is admissible; the full admissible family gives all-forces regularity versus existence of a breakdown force.

## Recovering the four endpoint quantifiers

[Statements.lean](../Fefferman/Statements.lean) defines the project endpoints as follows; every displayed viscosity quantifier ranges over `PositiveViscosity a`:

| Case | Exact quantifier pattern |
|---|---|
| A | $\forall\nu\,\forall u_0,\ I_{\mathbb R^3}(u_0)\to G_{\mathbb R^3}(\nu,u_0,0)$ |
| B | $\forall\nu\,\forall u_0,\ I_{\mathrm{per}}(u_0)\to G_{\mathrm{per}}(\nu,u_0,0)$ |
| C | $\forall\nu\,\exists u_0,\ I_{\mathbb R^3}(u_0)\land\exists f,\ F_{\mathbb R^3}(f)\land\neg G_{\mathbb R^3}(\nu,u_0,f)$ |
| D | $\forall\nu\,\exists u_0,\ I_{\mathrm{per}}(u_0)\land\exists f,\ F_{\mathrm{per}}(f)\land\neg G_{\mathrm{per}}(\nu,u_0,f)$ |

Consequently, sound zero-force certificates for every viscosity imply A or B. Sound breakdown-force certificates with a witness for every viscosity imply C or D. `breakdownAt_iff_exists_breakdownForce` makes the existential force specialization explicit.

Zero-force admissibility matters in an abstract `Analysis`. A/B do not separately assume it; `regularForceAt` includes force admissibility. Identifying zero-force semantic regularity with A/B, or deriving forced breakdown from unforced failure, therefore needs `ZeroForceAdmissible`. [Logic.lean](../Fefferman/Logic.lean) retains that hypothesis. At fixed viscosity, breakdown is equivalent to failure of *all-admissible-force* global solvability, not failure of zero-force solvability. Failure of universally quantified A supplies a breakdown witness at **some** viscosity; it does not supply C's witness at **every** viscosity without further mathematics. A is not identified with ¬C, nor B with ¬D.

The abstract positive-viscosity type can be empty. Universal endpoint statements are then vacuous. To refute universally quantified C or D from a pointwise exclusion requires a positive-viscosity inhabitant. The real interpretation has one, for example viscosity one; abstract theorems must retain the requirement where needed.

## Master contracts and derivation interfaces

[MasterCore.lean](../Fefferman/MasterCore.lean) defines `DomainMasterCore a d r` as soundness plus zero-force regular membership at every viscosity. `DomainMaster a d r` adds breakdown nonemptiness at every viscosity. It is the strongest named master contract here, but imposes more conditions than the general taxonomy: an all-regular force regime cannot satisfy its positive-breakdown requirement when positive viscosities exist.

`MasterTheoremA` in [Master_r3.lean](../Master_r3.lean) specializes `DomainMaster` to whole space; `MasterTheoremB` in [Master_T3.lean](../Master_T3.lean) specializes it to periodic space. `MA_implies_A_and_C` and `MB_implies_B_and_D` in [Feffermann-Classification.lean](../Feffermann-Classification.lean) prove their respective conditional consequences. Conversely, `masterCore_no_breakdownAt_of_all_regular` excludes breakdown when every admissible force has a regular certificate.

The broadest construction interface is `DerivationModel a d Witness` in [DerivationSupport.lean](../Fefferman/DerivationSupport.lean). It separates criteria from same-input witness representations. `DerivationPorts` supplies realization and analytic exits; `derivation_regime_soundness` also consumes the control theorem. `derivation_master` additionally requires breakdown nonemptiness. The R3 storage and T3 renewal witness families specialize this interface.

[MasterAC.lean](../Fefferman/MasterAC.lean) is narrower: an internal whole-space regularity/breakdown object plus a separate `MasterACProjection`. The independent [intrinsic-force route](../Fefferman/IntrinsicIdentification.lean), under its unsupplied global-closure premise, instead yields A and ¬C. Those conditional programs cannot be combined by assuming their physical premises have already been established.

## Forcing extensions and their source status

The following constructions can supply criteria or intermediate estimates. Each still needs its physical realization and the appropriate solution or obstruction exit before entering `ForceRegimeSoundness`.

| Extension | Exact source and result | Certification scope and retained premise |
|---|---|---|
| Relative GP budget | [Forcing classification](../reference/rocq/awpi_nse_gp_forcing_classification_v0_1_1.v): `GPRelativeForcingBudget51`, `GFC21_SAFE_FORCING_GIVES_CRITICAL_BOUNDS` | **Rocq reference.** External work obeys $F(t)\le Q_f+\theta_f\nu^2D(t)$; internal/external margins satisfy $\theta_i+\theta_f<1$. The same-trajectory integrated ledger remains supplied. |
| Intrinsic work envelope | [Force envelope](../reference/rocq/NSE_R3_FORCED_GP_DIAMOND_FORCE_ENVELOPE.v): `FE03_FORCE_SIZE_EXACTLY_CLASSIFIES_UNIFORM_CRITICAL_WORK`; [intrinsic class](../reference/rocq/NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.v): `IntrinsicCriticalForceClassA` | **Rocq references.** The least work coefficient depends on `CriticalDualGeometry`; accumulated intrinsic cost and internal-ledger bounds feed a critical-energy estimate, not an unconditional smooth-solution theorem. |
| Storage and uniform action cost | [Framework](../reference/rocq/NSE_CLAY_FEFFERMAN_FRAMEWORK.v): `R3StorageTerminalWitness`, `FW40_STORAGE_TERMINAL_WITNESS_GIVES_UNIFORM_CRITICAL_BOUND`; [UAC](../reference/rocq/NSE_R3_FORCED_GP_DIAMOND_UNIFORM_ACTION_COST.v): `UAC22_ACTION_COST_COUPLING_CONTROLS_FULL_CRITICAL_READOUT` | **Rocq references.** Witness realization, uniform route budgets, finite-cut balance, full readout and the physical smoothness exit retain their distinct roles. |
| Lean storage/continuation interfaces | [R3 storage](../Master_R3_details.lean), [derivation](../Fefferman/DerivationSupport.lean), [same-path NSE anchor](../NSE/NSEAnchor.lean) | **Lean audited source anchor.** Conditional control/continuation statements are checked; no complete identification with every concrete Fefferman input is supplied. |
| Scalar exponents | [Exponent module](../NSEForcingRegularityClasses.lean): `CRITICAL_FORCING_SCALING_LINE`, `L2_LH_TRICHOTOMY_SMOOTH_CRITICAL_ROUGH` | **Lean audited source anchor.** Partitions the scalar regions for $s+3/2-2/q$; actual Sobolev membership and PDE soundness are separate. |

The [extension audit](../provenance/EXTENSION_SOURCE_AUDIT.md) records the boundaries in detail. Rocq force-ledger labels `ClassA`/`ClassB` are not Fefferman A/B. Failure of a sufficient budget criterion does not establish breakdown.

## Concrete atlas, sources and verification

[ConcreteABCDUnifiedClosure.lean](../ConcreteABCDUnifiedClosure.lean) provides `realAnalysis`, force-construction results and `FEFFERMAN_ABCD_A_TIER_UNIFIED_CLOSURE_ATLAS`. The atlas packages equivalences with four direct endpoint definitions. `ABCDPhysicalPort` contains proofs of those endpoints as fields; no instance is supplied. The [semantic review](../provenance/SEMANTIC_REVIEW.md) also records the ambient-time-derivative versus half-line issue at time zero. Internal endpoint equivalence does not settle that identification.

The canonical source identities are `FEF_NSE_MASTERAC_TWO_LAYER_LEAN_v0_11_0` and `FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0`. [Source origins](../provenance/active_source_origins.json), [archive hashes](../provenance/sources.json), and the [A–D audit](../provenance/ABCD_SOURCE_AUDIT.md) preserve their provenance. The independent exponent classifier and `NSE` continuation branch retain their own analytic realization obligations; sharing a repository does not prove cross-branch physical identity.

The current build covers **59 active Lean modules**. The [CI workflow](../.github/workflows/lean.yml) compiles and audits their actual declarations; a successful receipt certifies that scoped result, including its hypotheses. Preserved Rocq sources are references and are **not newly certified by this Lean CI**. Neither source inclusion, a preprint claim, nor a historical package name discharges an open physical endpoint.
