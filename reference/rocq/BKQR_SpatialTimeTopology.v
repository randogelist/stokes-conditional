(* Time-integrated errors of literal spatial Fourier polynomials.  The
   equivalence below is proved from actual spatial Parseval and Riemann time
   integration, not assumed as a coefficient-space realization interface. *)
From Stdlib Require Import Reals Lra Psatz Lia Logic.FunctionalExtensionality.
Require Import BKQR_CountableRange BKQR_TimeIntegrals BKQR_BilinearKernel.
Require Import BKQR_FourierConvection BKQR_NSEFourierKernel BKQR_TorusAtoms.
Require Import BKQR_SpatialPolynomials BKQR_NonlinearTimeSource BKQR_SourceStability.
Require Import BKQR_FourierSourceStability.

Module BKQR_SPATIAL_TIME_TOPOLOGY.
Import GP_COUNTABLE_RANGE BKQR_TIME_INTEGRALS BKQR_BILINEAR_KERNEL.
Import BKQR_FOURIER_CONVECTION BKQR_NSE_FOURIER_KERNEL BKQR_TORUS_ATOMS.
Import BKQR_SPATIAL_POLYNOMIALS BKQR_NONLINEAR_TIME_SOURCE BKQR_SOURCE_STABILITY.
Import BKQR_FOURIER_SOURCE_STABILITY.
Open Scope R_scope.

Theorem SPATIAL_POLYNOMIAL_DIFFERENCE : forall x y N p a,
  csub(vector_polynomial x N p a)(vector_polynomial y N p a)=
  vector_polynomial (fun i=>x i-y i) N p a.
Proof.
  intros x y N p a. unfold vector_polynomial,scalar_polynomial.
  rewrite complex_sum_subtract. apply complex_sum_ext. intros m Hm.
  unfold mode_vector,vector_from_scalars,csub,cadd,cscale,cmul,cre,cim.
  cbn. f_equal; ring.
Qed.

Definition spatial_polynomial_error (x y:nat->R) (N:nat) : R :=
  vector_energy(fun p a=>csub(vector_polynomial x N p a)(vector_polynomial y N p a)).

Theorem SPATIAL_POLYNOMIAL_ERROR_PARSEVAL : forall x y N,
  spatial_polynomial_error x y N=physical_prefix (fun i=>x i-y i) (6*N)%nat.
Proof.
  intros x y N. rewrite <-SPATIAL_VECTOR_PARSEVAL.
  unfold spatial_polynomial_error,vector_energy. apply gp_sum_ext. intros a Ha.
  apply scalar_energy_ext. intro p. apply SPATIAL_POLYNOMIAL_DIFFERENCE.
Qed.

Lemma spatial_error_continuous : forall u v a b,
  CoordinateContinuous u a b ->CoordinateContinuous v a b ->forall N,
  ClosedContinuous(fun t=>spatial_polynomial_error (u t)(v t)N)a b.
Proof.
  intros u v a b Hu Hv N.
  assert (Heq:(fun t=>spatial_polynomial_error (u t)(v t)N)=
    (fun t=>energy_integrand (6*N)%nat (path_difference u v)t)).
  { apply functional_extensionality. intro t.
    unfold energy_integrand,path_difference. apply SPATIAL_POLYNOMIAL_ERROR_PARSEVAL. }
  rewrite Heq. apply energy_integrand_continuous. apply difference_continuous; assumption.
Qed.

Definition spatial_time_error u v a b (Hab:a<=b)
  (Hu:CoordinateContinuous u a b)(Hv:CoordinateContinuous v a b) N : R :=
  integral a b Hab (fun t=>spatial_polynomial_error (u t)(v t)N)
    (spatial_error_continuous u v a b Hu Hv N).

Theorem SPATIAL_TIME_ERROR_IS_COEFFICIENT_TIME_PREFIX :
  forall u v a b Hab Hu Hv N,
  spatial_time_error u v a b Hab Hu Hv N=
  time_prefix (fun _=>1)(path_difference u v)a b Hab
    (difference_continuous u v a b Hu Hv)(6*N)%nat.
Proof.
  intros u v a b Hab Hu Hv N. unfold spatial_time_error.
  pose (Huv:=difference_continuous u v a b Hu Hv).
  pose (HE:=energy_integrand_continuous a b (path_difference u v) Huv (6*N)%nat).
  transitivity (integral a b Hab
    (energy_integrand (6*N)%nat (path_difference u v)) HE).
  - apply integral_ext. intros t Ht. unfold energy_integrand,path_difference.
    apply SPATIAL_POLYNOMIAL_ERROR_PARSEVAL.
  - apply energy_integral_formula.
Qed.

Definition SpatialTimeErrorBound u v a b Hab Hu Hv D : Prop :=
  forall N,spatial_time_error u v a b Hab Hu Hv N<=D.

Theorem SPATIAL_TIME_ERROR_BOUND_IFF_TIME_BOUND :
  forall u v a b Hab Hu Hv D,
  SpatialTimeErrorBound u v a b Hab Hu Hv D <->
  TimeBound (fun _=>1)(path_difference u v)a b Hab
    (difference_continuous u v a b Hu Hv)D.
Proof.
  intros u v a b Hab Hu Hv D. split.
  - intros H N. specialize(H N). rewrite SPATIAL_TIME_ERROR_IS_COEFFICIENT_TIME_PREFIX in H.
    eapply Rle_trans; [|exact H]. unfold time_prefix. apply gp_sum_prefix_le.
    + intro i. apply time_mode_nonnegative. intro j. lra.
    + lia.
  - intros H N. rewrite SPATIAL_TIME_ERROR_IS_COEFFICIENT_TIME_PREFIX. apply H.
Qed.

Definition StrongSpatialTimeL2 (us:nat->R->nat->R)(u:R->nat->R)a b Hab
  (Hus:forall n,CoordinateContinuous(us n)a b)(Hu:CoordinateContinuous u a b) : Prop :=
  forall eps,0<eps ->exists J,forall n,(J<=n)%nat ->
    SpatialTimeErrorBound (us n)u a b Hab(Hus n)Hu eps.

Theorem STRONG_SPATIAL_TIME_L2_IFF_STRONG_TIME_L2 :
  forall us u a b Hab Hus Hu,
  StrongSpatialTimeL2 us u a b Hab Hus Hu <->StrongTimeL2 us u a b Hab Hus Hu.
Proof.
  intros us u a b Hab Hus Hu. split; intros H eps Heps;
    destruct(H eps Heps)as[J HJ];exists J;intros n Hn.
  - apply (proj1(SPATIAL_TIME_ERROR_BOUND_IFF_TIME_BOUND
      (us n)u a b Hab(Hus n)Hu eps)). apply HJ. exact Hn.
  - apply (proj2(SPATIAL_TIME_ERROR_BOUND_IFF_TIME_BOUND
      (us n)u a b Hab(Hus n)Hu eps)). apply HJ. exact Hn.
Qed.

Theorem STRONG_SPATIAL_TIME_L2_PRESERVES_NONLINEAR_SOURCE :
  forall K C us u a b Hab Hus Hu eta Heta E Ls L,
  SchurBound K C ->
  (forall n t,a<=t<=b ->PhysicalBound(us n t)E) ->
  (forall t,a<=t<=b ->PhysicalBound(u t)E) ->
  StrongSpatialTimeL2 us u a b Hab Hus Hu ->
  (forall n,SeqLimit(tested_source K(us n)a b Hab(Hus n)eta Heta)(Ls n)) ->
  SeqLimit(tested_source K u a b Hab Hu eta Heta)L ->SeqLimit Ls L.
Proof.
  intros K C us u a b Hab Hus Hu eta Heta E Ls L HK Husc Huc Hstrong Hsources Hsource.
  apply(STRONG_TIME_L2_PRESERVES_NONLINEAR_SOURCE
    K C us u a b Hab Hus Hu eta Heta E Ls L);try assumption.
  apply(proj1(STRONG_SPATIAL_TIME_L2_IFF_STRONG_TIME_L2 us u a b Hab Hus Hu)).
  exact Hstrong.
Qed.

Theorem STRONG_SPATIAL_TIME_L2_PRESERVES_CONSTRUCTED_FOURIER_SOURCE :
  forall us u a b Hab Hus Hu E
    (Husc:forall n t,a<=t<=b ->PhysicalBound(us n t)E)
    (Huc:forall t,a<=t<=b ->PhysicalBound(u t)E),
  StrongSpatialTimeL2 us u a b Hab Hus Hu ->forall eta Heta i,
  SeqLimit
    (fun n=>concrete_source_value(us n)a b Hab(Hus n)eta Heta E(Husc n)i)
    (concrete_source_value u a b Hab Hu eta Heta E Huc i).
Proof.
  intros us u a b Hab Hus Hu E Husc Huc Hstrong eta Heta i.
  apply BKFS50_STRONG_TIME_L2_PRESERVES_CONSTRUCTED_FOURIER_SOURCE.
  apply(proj1(STRONG_SPATIAL_TIME_L2_IFF_STRONG_TIME_L2 us u a b Hab Hus Hu)).
  exact Hstrong.
Qed.

Theorem ENERGY_CAP_CONSTRUCTS_STRONG_SPATIAL_TIME_APPROXIMATION :
  forall u a b Hab Hu E,
  (forall t,a<=t<=b ->PhysicalBound(u t)E) ->
  StrongSpatialTimeL2 (complete_mode_cutoff u)u a b Hab
    (complete_mode_cutoff_continuous u a b Hu)Hu.
Proof.
  intros u a b Hab Hu E Hcap.
  apply(proj2(STRONG_SPATIAL_TIME_L2_IFF_STRONG_TIME_L2
    (complete_mode_cutoff u)u a b Hab(complete_mode_cutoff_continuous u a b Hu)Hu)).
  apply(BKFS51_ENERGY_CAP_CONSTRUCTS_STRONG_TIME_L2_APPROXIMATION u a b Hab Hu E Hcap).
Qed.

Print Assumptions SPATIAL_POLYNOMIAL_ERROR_PARSEVAL.
Print Assumptions SPATIAL_TIME_ERROR_IS_COEFFICIENT_TIME_PREFIX.
Print Assumptions STRONG_SPATIAL_TIME_L2_IFF_STRONG_TIME_L2.
Print Assumptions STRONG_SPATIAL_TIME_L2_PRESERVES_NONLINEAR_SOURCE.
Print Assumptions STRONG_SPATIAL_TIME_L2_PRESERVES_CONSTRUCTED_FOURIER_SOURCE.
Print Assumptions ENERGY_CAP_CONSTRUCTS_STRONG_SPATIAL_TIME_APPROXIMATION.
End BKQR_SPATIAL_TIME_TOPOLOGY.
