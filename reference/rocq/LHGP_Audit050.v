From Stdlib Require Import Reals.
Require Import LHGP_TimeBorel LHGP_BorelArithmetic LHGP_Quantization.
Require Import LHGP_GradientPath LHGP_DissipationBorel.
Require Import LHGP_SimpleApproximation LHGP_Completion050.

(* Inspect the definitions as well as all logical assumptions. In particular,
   TimeBorel is generated from genuine relative-open sets, simple functions
   have finite range, and the time-integral AE law is an explicit premise. *)
Print TimeOpen.
Print TimeBorel.
Print ScalarBorelOn.
Print CanonicalFiniteGradientDomain.
Print TotalGradientGraphPath.
Print FiniteBorelOn.
Print StronglyMeasurableOn.
Print Quantize.
Print AEIntegralTransport.
Print MeasurableGradientEnergy.

Check DISSIPATION_SUBLEVEL_TIME_CLOSED.
Check CANONICAL_FINITE_GRADIENT_DOMAIN_BOREL.
Check GRADIENT_PATH_FROM_POINTWISE_PROBES.
Check HILBERT_BOREL_COORDINATES_STRONGLY_MEASURABLE.
Check CANONICAL_GRADIENT_EXISTS_UNIQUE.
Check CANONICAL_GRADIENT_COORDINATES_BOREL.
Check CANONICAL_GRADIENT_STRONGLY_MEASURABLE.
Check CANONICAL_GRADIENT_ENERGY_BOREL.
Check CANONICAL_GRADIENT_ENERGY_AGREES.
Check LHGP_LEDGER_MEASURABLE_GRADIENT.
Check LHGP_HILBERT_MEASURABLE_GRADIENT.
Check LHGP_STRONGLY_MEASURABLE_TRAJECTORY_EQUIVALENCE.

Print Assumptions DISSIPATION_SUBLEVEL_TIME_CLOSED.
Print Assumptions CANONICAL_FINITE_GRADIENT_DOMAIN_BOREL.
Print Assumptions GRADIENT_PATH_FROM_POINTWISE_PROBES.
Print Assumptions HILBERT_BOREL_COORDINATES_STRONGLY_MEASURABLE.
Print Assumptions CANONICAL_GRADIENT_EXISTS_UNIQUE.
Print Assumptions CANONICAL_GRADIENT_COORDINATES_BOREL.
Print Assumptions CANONICAL_GRADIENT_STRONGLY_MEASURABLE.
Print Assumptions CANONICAL_GRADIENT_ENERGY_BOREL.
Print Assumptions CANONICAL_GRADIENT_ENERGY_AGREES.
Print Assumptions LHGP_LEDGER_MEASURABLE_GRADIENT.
Print Assumptions LHGP_HILBERT_MEASURABLE_GRADIENT.
Print Assumptions LHGP_STRONGLY_MEASURABLE_TRAJECTORY_EQUIVALENCE.
