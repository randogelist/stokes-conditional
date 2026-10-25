# Generalized Fefferman preprint

**A Domain-Indexed Framework for Generalized Fefferman Force Classification**

Research draft 0.1, 25 October 2026. This is a source synthesis and verification report, not a proof of an unconditional physical Fefferman endpoint.

- [Read the PDF](generalized_fefferman_preprint.pdf).
- [Edit the LaTeX source](generalized_fefferman_preprint.tex).
- [Inspect the claim-to-source map](claims.json).
- [Read the concise repository synthesis](../docs/GENERALIZED_FEFFERMAN_CLASSIFICATION.md).

The paper distinguishes existing Lean-source results, inspected Rocq-source results, and manuscript-only deductions. Its historical CI evidence applies to source commit `26bc074c2b8ebf57fa0fabcf9b8263673de9d80b`; the documentation addition does not change the Lean sources or their assumptions.

## Build

Use a TeX Live installation with pdfLaTeX, Latin Modern, AMS packages, booktabs, geometry, microtype, xurl, hyperref, fancyhdr, and enumitem:

```sh
make -C paper
```

Alternatively, run pdfLaTeX twice from this directory with `-interaction=nonstopmode -halt-on-error -no-shell-escape`. Building this PDF does not compile Lean. Lean verification remains governed by the repository workflow and `scripts/verify.py`.

The repository handle identifies the source project. No individual author, academic affiliation, peer review, journal submission, or preprint-server deposit is claimed.
