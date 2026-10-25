From Stdlib Require Import Reals.
Require Import LHGP_ClosedSubspace LHGP_OrthogonalProjection LHGP_FiniteFrames.
Require Import LHGP_DenseTestBasis LHGP_R3SmoothTests LHGP_ProjectedGradient.
Require Import LHGP_Completion060.

(* Full definitions and theorem types distinguish the derived construction
   from the spatial L2 and density inputs that remain to be instantiated. *)
Print ClosedLinearSubspace.
Print Annihilator.
Print SubspaceHilbert.
Print IsOrthogonalProjection.
Print CountablyDense.
Print HInfiniteDimension.
Print R3Point.
Print R3SmoothTest.
Print R3VectorEmbedding.
Print R3TensorTestMap.
Print R3TensorDivergence.
Print R3RawDivergence.
Print ProjectedDivergence.

Check AnnihilatorComplete.
Check CLOSED_SUBSPACE_MINIMIZER.
Check CLOSED_SUBSPACE_PROJECTION_MAP_EXISTS.
Check ORTHOGONAL_PROJECTION_PAIRING.
Check ORTHOGONAL_PROJECTION_CONTRACTION.
Check DENSE_TEST_BASIS_EXISTS.
Check DENSE_TEST_BASIS_COVERS_INPUT.
Check DenseTestsDualModel.
Check R3_TEST_ACTUAL_PARTIAL.
Check R3_TEST_ALL_ITERATED_PARTIALS_SUPPORTED.
Check R3_TEST_ANNIHILATOR_COMPLETE.
Check R3_RAW_DIVERGENCE_COVERS_ALL_TESTS.
Check PROJECTED_GRADIENT_GRAPH_EXACT.
Check PROJECTED_GP_DISSIPATION_EXACT.
Check R3_DENSE_TEST_PROJECTED_ASSEMBLY.
Check SUBSPACE_ONB_RECONSTRUCTION_FROM_AMBIENT_DENSITY.

Print Assumptions AnnihilatorComplete.
Print Assumptions CLOSED_SUBSPACE_MINIMIZER.
Print Assumptions CLOSED_SUBSPACE_PROJECTION_MAP_EXISTS.
Print Assumptions ORTHOGONAL_PROJECTION_PAIRING.
Print Assumptions DENSE_TEST_BASIS_EXISTS.
Print Assumptions DENSE_TEST_BASIS_COVERS_INPUT.
Print Assumptions DenseTestsDualModel.
Print Assumptions R3_TEST_ACTUAL_PARTIAL.
Print Assumptions R3_RAW_DIVERGENCE_COVERS_ALL_TESTS.
Print Assumptions PROJECTED_DIVERGENCE_CONSTRUCTED.
Print Assumptions PROJECTED_GP_DISSIPATION_EXACT.
Print Assumptions R3_DENSE_TEST_PROJECTED_ASSEMBLY.
Print Assumptions SUBSPACE_ONB_RECONSTRUCTION_FROM_AMBIENT_DENSITY.
