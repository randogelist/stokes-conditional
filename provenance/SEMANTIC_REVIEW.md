# Semantic review of the recovered Fefferman A–D baseline

The active sources support a conditional theorem library and a concrete endpoint atlas. A successful build certifies those exact Lean statements. It does not establish any unconditional physical A, B, C, or D endpoint.

## Material limitations

1. **Boundary-time differentiation requires repair or an equivalence proof.** `Fefferman/Analysis.lean` documents differentiation within the nonnegative half-line. `ConcreteABCDUnifiedClosure.lean:30` instead defines `timeDerivative f t := deriv f t`, while `smoothClosedHalfSpaceReal` only requires `ContDiffOn` on `t ≥ 0`. Ambient differentiability at zero does not follow from this within-set smoothness. For example, a function equal to `t` for nonnegative times and zero for negative times is smooth on the closed right half-line but not differentiable at zero in the ambient line. Totalized `deriv` returns zero there, while its right derivative is one. The file's endpoint equivalences are exact for its own `realAnalysis`; an independently proved identification with the intended half-line PDE is still required. Options for future work are a `derivWithin` realization or a smooth-extension interface with proved restriction invariance. Preserve the recovered source unchanged in this import.

2. **The unified atlas repackages endpoint propositions.** `ABCDPhysicalPort` has four proof fields: whole-space regularity, periodic regularity, whole-space forced breakdown, and periodic forced breakdown. `FEFFERMAN_ABCD_A_TIER_UNIFIED_CLOSURE_ATLAS` proves equivalences between this packaging and the corresponding project propositions. No inhabitant of the four-field record is constructed. Likewise, `WholeSpaceAPhysicalPort.globalZeroForce` and `PeriodicBPhysicalPort.globalZeroForce` retain the regularity endpoint. Zero-force smoothness, periodicity, and decay are genuinely discharged, but they do not discharge global solution existence.

3. **The C/D source interfaces retain the breakdown proof.** `WholeSpaceSourceSemanticPort.noGlobal` and `PeriodicCorollary106SemanticPort.noGlobal` explicitly require nonexistence of a qualifying global solution for the supplied force family, at every positive viscosity. The constructors and `implies_C`/`implies_D` theorems correctly consume these assumptions. Force rescaling and periodization do not by themselves prove this field. The delayed-rescaling force interfaces also retain their stated decay assumptions; source smoothness/support should not be reported as all force admissibility.

4. **Abstract ports are not physical realizations.** `Analysis` is an analytic signature with unconstrained scalar operations and predicates. Generic theorems over it become physical results only after a valid analytic realization and every named hypothesis are supplied. `MasterAC` additionally needs `MasterACProjection`, whose regular-solution and obstruction exits remain explicit. The separately included `NSE.*` branch needs its modal realization, payment, same-path norm identification, and `SerrinExitContract`; the latter consumes the PDE continuation theorem. No theorem in this import identifies that branch with all concrete `Fefferman` endpoints automatically.

5. **A–D is an atlas of alternatives.** The conjunction `ABCDPhysicalEndpoints` is a bookkeeping target, not the official criterion for solving the problem. The official statement asks for one alternative. Conditional branches that imply forced breakdown and branches that imply its negation must retain their different hypotheses and cannot be combined as simultaneously instantiated physical facts.

## Alignments worth retaining

`Fin 3` fixes the spatial dimension; positive viscosity and all its quantifiers remain explicit. Whole-space energy includes an integrability condition and one uniform bound over all nonnegative times, avoiding the totalized-integral pitfall. The periodic branch includes periodic pressure, matching the official erratum. Breakdown is absence of every qualifying global solution, not merely failure of one chosen trajectory.

## Reporting gate

Separate: source recovery; successful compilation; theorem axiom audit; endpoint semantic equivalence; and discharge of the physical endpoint premises. This import can complete the first three while the last two remain open. The scalar forcing-exponent partition is a classification of exponents, not a solution-regularity theorem.

Primary comparison source: Charles L. Fefferman, [Existence and Smoothness of the Navier–Stokes Equation](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf), pages 1–2 and appended errata, accessed 2026-10-25. It specifies nonnegative-time fields, four alternatives, and periodic pressure in the erratum. The source-code findings above are independent inspection of the recovered files.
