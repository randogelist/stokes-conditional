From Stdlib Require Import Reals.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport LHGP_Audit.
Require Import LHGP_Hilbert LHGP_Bilinear LHGP_Realization LHGP_Audit020.
Require Import LHGP_Dual LHGP_WeakTopology LHGP_PathSynthesis.
Require Import LHGP_Gradient LHGP_Evolution LHGP_Equivalence.

(* Print the analytic premises and the logical foundations separately.
   Print Assumptions does not display universally quantified model inputs. *)
Print DualTestModel.
Print ProbeLinear.
Print ProbeRepresents.
Print VarValue.
Print GradientModel.
Print GradientEnergyAt.
Print GPDissipationValue.
Print EvolutionTests.
Print TimeData.
Print IntegralNonnegative.
Print HilbertWeakForm.
Print GPWeakForm.
Print EnergySchedule.
Print HilbertEnergyLedger.
Print GPEnergyLedger.
Print HilbertLHModel.
Print GPLHModel.

Check VarUpper_square_bound.
Check DUAL_FINITE_VARIATIONAL_IFF_RIESZ.
Check DUAL_VARIATIONAL_VALUE_IFF_GRADIENT.
Check DUAL_VARIATIONAL_REALIZATION_UNIQUE.
Check HCoordinates_and_norm_bound_weak.
Check HWeakContinuous_GP_exact.
Check HGP_PATH_SURJECTIVE_UNIQUE.
Check HGP_PATH_PREFIX_BOUND_IFF.
Check GRADIENT_DISSIPATION_EXACT.
Check EVOLUTION_WEAK_FORM_EXACT.
Check LHGP_ENERGY_LEDGER_EXACT.
Check LHGP_CONTINUITY_AND_BOUND_EXACT.
Check LHGP_REALIZED_TRAJECTORY_EQUIVALENCE.
Check LHGP_ENCODING_TRAJECTORY_EQUIVALENCE.
Check LHGP_TRAJECTORY_EQUIVALENCE.
Check LHGP_INITIAL_NORM_BOUND.
Check LHGP_HILBERT_MODEL_STRONG_INITIAL.
Check LHGP_GP_MODEL_STRONG_INITIAL.

Print Assumptions DUAL_FINITE_VARIATIONAL_IFF_RIESZ.
Print Assumptions DUAL_VARIATIONAL_VALUE_IFF_GRADIENT.
Print Assumptions DUAL_VARIATIONAL_REALIZATION_UNIQUE.
Print Assumptions HCoordinates_and_norm_bound_weak.
Print Assumptions HWeakContinuous_GP_exact.
Print Assumptions HGP_PATH_SURJECTIVE_UNIQUE.
Print Assumptions GRADIENT_DISSIPATION_EXACT.
Print Assumptions EVOLUTION_WEAK_FORM_EXACT.
Print Assumptions LHGP_ENERGY_LEDGER_EXACT.
Print Assumptions LHGP_ENCODING_TRAJECTORY_EQUIVALENCE.
Print Assumptions LHGP_TRAJECTORY_EQUIVALENCE.
Print Assumptions LHGP_HILBERT_MODEL_STRONG_INITIAL.
Print Assumptions LHGP_GP_MODEL_STRONG_INITIAL.
