From Stdlib Require Import Reals.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport LHGP_Audit.
Require Import LHGP_Hilbert LHGP_Bilinear LHGP_Realization.

(* The complete types below expose every analytic input. Print Assumptions
   separately reports transitive logical foundations, not theorem premises.
   In the Hilbert API, HNorm and HDist are squared quantities. *)
Print HilbertData.
Print OrthonormalBasis.
Print HComplete.
Print HCauchy.
Print HConverges.

Check HFinite_tail_distance.
Check HAnalysis_bessel.
Check HAnalysis_reconstruction.
Check HAnalysis_parseval.
Check HSynthesis_exists.
Check HGP_surjective_unique.
Check quadratic_stability_bound.
Check HAnalysis_linear_readout.
Check LHGP_HILBERT_QUADRATIC_READOUT.
Check LHGP_WEIGHTED_HILBERT_QUADRATIC_READOUT.
Check LHGP_COMPLETE_READOUT_REALIZATION.
Check LHGP_HILBERT_DISTANCE_ENERGY.
Check LHGP_HILBERT_STRONG_INITIAL_TRACE.
Check LHGP_WEIGHTED_ENERGY_STRONG_INITIAL_TRACE_EXACT.

Print Assumptions HFinite_tail_distance.
Print Assumptions HAnalysis_bessel.
Print Assumptions HAnalysis_reconstruction.
Print Assumptions HAnalysis_parseval.
Print Assumptions HSynthesis_exists.
Print Assumptions HGP_surjective_unique.
Print Assumptions quadratic_stability_bound.
Print Assumptions HAnalysis_linear_readout.
Print Assumptions LHGP_HILBERT_QUADRATIC_READOUT.
Print Assumptions LHGP_WEIGHTED_HILBERT_QUADRATIC_READOUT.
Print Assumptions LHGP_COMPLETE_READOUT_REALIZATION.
Print Assumptions LHGP_HILBERT_DISTANCE_ENERGY.
Print Assumptions LHGP_HILBERT_STRONG_INITIAL_TRACE.
Print Assumptions LHGP_WEIGHTED_ENERGY_STRONG_INITIAL_TRACE_EXACT.
