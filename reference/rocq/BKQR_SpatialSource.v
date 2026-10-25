From Stdlib Require Import Reals Lra Psatz Lia Logic.FunctionalExtensionality.
Require Import BKQR_CountableRange BKQR_TimeIntegrals BKQR_BilinearKernel.
Require Import BKQR_NonlinearTimeSource BKQR_FourierIndices BKQR_FourierConvection.
Require Import BKQR_FourierSchur BKQR_NSEFourierKernel BKQR_NSEFourierClassification.
Require Import BKQR_TorusAtoms BKQR_SpatialPolynomials BKQR_FourierSourceStability.

Module BKQR_SPATIAL_SOURCE.
Import GP_COUNTABLE_RANGE BKQR_TIME_INTEGRALS BKQR_BILINEAR_KERNEL.
Import BKQR_FOURIER_INDICES BKQR_FOURIER_CONVECTION BKQR_FOURIER_SCHUR.
Import BKQR_NSE_FOURIER_KERNEL BKQR_NSE_FOURIER_CLASSIFICATION.
Import BKQR_TORUS_ATOMS BKQR_SPATIAL_POLYNOMIALS BKQR_FOURIER_SOURCE_STABILITY.
Module T := BKQR_NONLINEAR_TIME_SOURCE.
Open Scope R_scope.

Lemma complex_sum_scale : forall N c f,
  complex_sum N (fun p=>cscale c(f p))=cscale c(complex_sum N f).
Proof.
  intros. unfold complex_sum,cscale,cre,cim; cbn. rewrite !gp_sum_scale. reflexivity.
Qed.

Lemma scalar_polynomial_add : forall N a b p,
  scalar_polynomial N (fun n=>cadd(a n)(b n)) p=
  cadd(scalar_polynomial N a p)(scalar_polynomial N b p).
Proof.
  intros. unfold scalar_polynomial. rewrite <-complex_sum_plus.
  apply complex_sum_ext. intros n Hn. unfold cmul,cadd,cre,cim; cbn; f_equal; ring.
Qed.

Lemma scalar_polynomial_scale : forall N c a p,
  scalar_polynomial N (fun n=>cscale c(a n)) p=cscale c(scalar_polynomial N a p).
Proof.
  intros. unfold scalar_polynomial. rewrite <-complex_sum_scale.
  apply complex_sum_ext. intros n Hn. unfold cmul,cscale,cre,cim; cbn; f_equal; ring.
Qed.

Lemma dot_polynomial : forall m x N p,
  complex_dot m(vector_polynomial x N p)=
  scalar_polynomial N(fun n=>complex_dot m(mode_vector x n)) p.
Proof.
  intros. unfold complex_dot,csum3,vector_polynomial.
  rewrite !scalar_polynomial_add,!scalar_polynomial_scale. reflexivity.
Qed.

Lemma leray_polynomial : forall m x N p r,
  leray_apply m(vector_polynomial x N p)r=
  scalar_polynomial N(fun n=>leray_apply m(mode_vector x n)r)p.
Proof.
  intros. unfold leray_apply,csum3,vector_polynomial.
  rewrite !scalar_polynomial_add,!scalar_polynomial_scale. reflexivity.
Qed.

Definition spatial_convection_integrand (i N:nat) (x:nat->R) (r:nat) (p:R3) : C2 :=
  cmul (projected_convection (decode_mode i)
    (vector_polynomial x N p) (vector_polynomial x N p) r)
    (cconj(torus_atom (decode_mode i) p)).

Definition spatial_source (i N:nat) (x:nat->R) : R :=
  scalar_tag (fun r=>Mean3(spatial_convection_integrand i N x r)) (decode_tag i).

Lemma spatial_convection_integrable : forall i N x r,
  IsMean3 (spatial_convection_integrand i N x r)
    (complex_sum N(fun p=>complex_sum N(fun q=>
      if mode_eq_dec(mode_add(mode_decode p)(mode_decode q))(decode_mode i)
      then projected_convection (decode_mode i)(mode_vector x p)(mode_vector x q)r
      else czero))).
Proof.
  intros i N x r.
  pose proof (SPATIAL_POLYNOMIAL_PRODUCT_COEFFICIENT N N
    (fun n=>complex_dot (decode_mode i)(mode_vector x n))
    (fun n=>leray_apply (decode_mode i)(mode_vector x n)r) (decode_mode i)) as H.
  pose proof (ISMEAN3_CMUL_L _ ci _ H) as HI.
  assert (Hfun:forall p,
    cmul ci(cmul(cmul
      (scalar_polynomial N(fun n=>complex_dot (decode_mode i)(mode_vector x n))p)
      (scalar_polynomial N(fun n=>leray_apply (decode_mode i)(mode_vector x n)r)p))
      (cconj(torus_atom (decode_mode i)p)))=
    spatial_convection_integrand i N x r p).
  { intro p. unfold spatial_convection_integrand,projected_convection.
    rewrite dot_polynomial,leray_polynomial.
    unfold cmul,cre,cim; cbn; f_equal; ring. }
  eapply ISMEAN3_EXT; [exact Hfun|].
  rewrite complex_sum_cmul_left in HI.
  assert (Heq:complex_sum N(fun p=>cmul ci(complex_sum N(fun q=>
    if mode_eq_dec(mode_add(mode_decode p)(mode_decode q))(decode_mode i)
    then cmul (complex_dot (decode_mode i)(mode_vector x p))
      (leray_apply (decode_mode i)(mode_vector x q)r) else czero)))=
    complex_sum N(fun p=>complex_sum N(fun q=>
      if mode_eq_dec(mode_add(mode_decode p)(mode_decode q))(decode_mode i)
      then projected_convection (decode_mode i)(mode_vector x p)(mode_vector x q)r
      else czero))).
  { apply complex_sum_ext. intros p Hp. rewrite complex_sum_cmul_left.
    apply complex_sum_ext. intros q Hq.
    destruct(mode_eq_dec(mode_add(mode_decode p)(mode_decode q))(decode_mode i));
      [reflexivity|]. unfold cmul,ci,czero,cre,cim; cbn; f_equal; ring. }
  rewrite <-Heq. exact HI.
Qed.

Theorem BKSP10_ACTUAL_SPATIAL_SOURCE_IS_CONCRETE_CONVOLUTION : forall i N x,
  spatial_source i N x=finite_vector_convolution i N x.
Proof.
  intros i N x. unfold spatial_source,scalar_tag,finite_vector_convolution.
  rewrite (MEAN3_VALUE _ _ (spatial_convection_integrable i N x (tag_axis(decode_tag i)))).
  destruct(Nat.eq_dec(tag_phase(decode_tag i))O) as [Hre|Him];
    cbn [complex_sum cre cim]; apply gp_sum_ext; intros p Hp;
    apply gp_sum_ext; intros q Hq; unfold pair_readout;
    destruct(mode_eq_dec(mode_add(mode_decode p)(mode_decode q))(decode_mode i));
    [unfold scalar_tag; rewrite Hre; reflexivity|reflexivity|
     unfold scalar_tag; destruct(Nat.eq_dec(tag_phase(decode_tag i))O); [contradiction|reflexivity]|
     reflexivity].
Qed.

Lemma spatial_source_continuous : forall u a b,
  CoordinateContinuous u a b -> forall i N,
  ClosedContinuous (fun t=>spatial_source i N(u t)) a b.
Proof.
  intros u a b Hu i N.
  assert (Heq:(fun t=>spatial_source i N(u t))=(fun t=>finite_vector_convolution i N(u t))).
  { apply functional_extensionality. intro t. apply BKSP10_ACTUAL_SPATIAL_SOURCE_IS_CONCRETE_CONVOLUTION. }
  rewrite Heq. apply finite_vector_convolution_continuous. exact Hu.
Qed.

Definition spatial_tested_source u a b Hab Hu eta Heta i N : R :=
  integral a b Hab (fun t=>eta t*spatial_source i N(u t))
    (T.continuous_product a b _ _ Heta (spatial_source_continuous u a b Hu i N)).

Theorem BKSP20_SPATIAL_AND_VECTOR_TESTED_SOURCES_AGREE :
  forall u a b Hab Hu eta Heta i N,
  spatial_tested_source u a b Hab Hu eta Heta i N=
  vector_tested_source u a b Hab Hu eta Heta i N.
Proof.
  intros. unfold spatial_tested_source,vector_tested_source. apply integral_ext.
  intros. rewrite BKSP10_ACTUAL_SPATIAL_SOURCE_IS_CONCRETE_CONVOLUTION. reflexivity.
Qed.

Theorem BKSP30_ACTUAL_SPATIAL_PRODUCT_LIMIT_IS_CONSTRUCTED_SOURCE :
  forall u a b Hab Hu eta Heta E
    (Hcap:forall t,a<=t<=b ->PhysicalBound(u t)E) i,
  SeqLimit (spatial_tested_source u a b Hab Hu eta Heta i)
    (concrete_source_value u a b Hab Hu eta Heta E Hcap i).
Proof.
  intros u a b Hab Hu eta Heta E Hcap i.
  destruct (BKNSE11_CONCRETE_FOURIER_SOURCE_LIMIT_EXISTS u a b E Hab Hu Hcap eta Heta i)
    as [L [HL HV]].
  assert (Heq:L=concrete_source_value u a b Hab Hu eta Heta E Hcap i).
  { eapply UL_sequence; [exact HL|apply concrete_source_value_spec]. }
  rewrite <-Heq. apply (limit_ext (vector_tested_source u a b Hab Hu eta Heta i)).
  - intro N. symmetry. apply BKSP20_SPATIAL_AND_VECTOR_TESTED_SOURCES_AGREE.
  - exact HV.
Qed.

Print Assumptions BKSP10_ACTUAL_SPATIAL_SOURCE_IS_CONCRETE_CONVOLUTION.
Print Assumptions BKSP30_ACTUAL_SPATIAL_PRODUCT_LIMIT_IS_CONSTRUCTED_SOURCE.
End BKQR_SPATIAL_SOURCE.
