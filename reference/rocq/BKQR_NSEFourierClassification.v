From Stdlib Require Import Reals Lra Psatz Logic.FunctionalExtensionality.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_ClassificationAudit.
Require Import BKQR_TimeIntegrals BKQR_WeakBalance BKQR_EnergyPaths.
Require Import BKQR_BilinearKernel BKQR_NonlinearTimeSource BKQR_QuadraticTransport.
Require Import BKQR_SourceConstruction BKQR_NonlinearClassification.
Require Import BKQR_FourierIndices BKQR_FourierBlocks BKQR_FourierConvection.
Require Import BKQR_FourierSchur BKQR_NSEFourierKernel.

Module BKQR_NSE_FOURIER_CLASSIFICATION.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_TIME_INTEGRALS.
Import BKQR_WEAK_BALANCE BKQR_ENERGY_PATHS BKQR_BILINEAR_KERNEL.
Import BKQR_QUADRATIC_TRANSPORT BKQR_SOURCE_CONSTRUCTION.
Import BKQR_FOURIER_INDICES BKQR_FOURIER_BLOCKS BKQR_FOURIER_CONVECTION.
Import BKQR_FOURIER_SCHUR BKQR_NSE_FOURIER_KERNEL.
Module N := BKQR_NONLINEAR_TIME_SOURCE.
Module C := BKQR_CLASSIFICATION.
Module Q := BKQR_NONLINEAR_CLASSIFICATION.
Open Scope R_scope.

Lemma finite_vector_convolution_continuous : forall u a b,
  CoordinateContinuous u a b -> forall i n,
  ClosedContinuous (fun t=>finite_vector_convolution i n (u t)) a b.
Proof.
  intros u a b Hu i n.
  assert (Heq : (fun t=>finite_vector_convolution i n (u t))=
    (fun t=>N.quadratic_integrand (indexed_convection_kernel i) (6*n)%nat u t)).
  { apply functional_extensionality. intro t.
    symmetry. apply BKNF20_FULL_SCALAR_CUT_IS_VECTOR_CONVOLUTION. }
  rewrite Heq. apply N.quadratic_integrand_continuous. exact Hu.
Qed.

Definition vector_tested_source u a b Hab Hu eta Heta i n : R :=
  integral a b Hab (fun t=>eta t*finite_vector_convolution i n (u t))
    (N.continuous_product a b _ _ Heta
      (finite_vector_convolution_continuous u a b Hu i n)).

Theorem BKNSE10_TESTED_VECTOR_CONVOLUTION_IS_SAME_SOURCE :
  forall u a b Hab Hu eta Heta i n,
  vector_tested_source u a b Hab Hu eta Heta i n=
  N.tested_source (indexed_convection_kernel i) u a b Hab Hu eta Heta (6*n)%nat.
Proof.
  intros. unfold vector_tested_source,N.tested_source. apply integral_ext.
  intros t Ht. unfold N.tested_integrand,N.quadratic_integrand.
  rewrite BKNF20_FULL_SCALAR_CUT_IS_VECTOR_CONVOLUTION. reflexivity.
Qed.

Theorem BKNSE11_CONCRETE_FOURIER_SOURCE_LIMIT_EXISTS :
  forall u a b E (Hab:a<=b) (Hu:CoordinateContinuous u a b),
  (forall t,a<=t<=b -> PhysicalBound (u t) E) ->
  forall eta (Heta:ClosedContinuous eta a b) i,
  exists L,
    SeqLimit (N.tested_source (indexed_convection_kernel i) u a b Hab Hu eta Heta) L /\
    SeqLimit (vector_tested_source u a b Hab Hu eta Heta i) L.
Proof.
  intros u a b E Hab Hu Hcap eta Heta i.
  destruct (N.TESTED_SOURCE_LIMIT_EXISTS (indexed_convection_kernel i)
    (indexed_convection_bound i) u a b Hab Hu eta Heta E
    (BKFS40_INDEXED_CONVECTION_HAS_DERIVED_SCHUR_BOUND i) Hcap) as [L HL].
  exists L. split; [exact HL|].
  apply (limit_ext (fun n=>N.tested_source (indexed_convection_kernel i)
    u a b Hab Hu eta Heta (6*n)%nat) _ L).
  - intro n. symmetry. apply BKNSE10_TESTED_VECTOR_CONVOLUTION_IS_SAME_SOURCE.
  - apply BKFB40_BLOCK_SUBSEQUENCE_PRESERVES_LIMIT. exact HL.
Qed.

Theorem BKNSE12_CONCRETE_FOURIER_SOURCE_LIMIT_BOUND :
  forall u a b E (Hab:a<=b) (Hu:CoordinateContinuous u a b),
  (forall t,a<=t<=b -> PhysicalBound (u t) E) ->
  forall eta (Heta:ClosedContinuous eta a b) i L A,
  SeqLimit (vector_tested_source u a b Hab Hu eta Heta i) L ->
  0<=A -> (forall t,a<=t<=b -> Rabs(eta t)<=A) ->
  Rabs L<=A*indexed_convection_bound i*E*(b-a).
Proof.
  intros u a b E Hab Hu Hcap eta Heta i L A HL HA HetaA.
  destruct (BKNSE11_CONCRETE_FOURIER_SOURCE_LIMIT_EXISTS u a b E Hab Hu Hcap
    eta Heta i) as [F [HF Hvector]].
  assert (Heq:L=F) by (eapply UL_sequence; eassumption).
  subst L. apply (N.TESTED_SOURCE_LIMIT_BOUND (indexed_convection_kernel i)
    (indexed_convection_bound i) u a b Hab Hu eta Heta E A F).
  - apply BKFS40_INDEXED_CONVECTION_HAS_DERIVED_SCHUR_BOUND.
  - exact Hcap.
  - exact HA.
  - exact HetaA.
  - exact HF.
Qed.

Theorem BKNSE20_ENERGY_PATH_CONSTRUCTS_CONVECTION_SOURCE :
  forall nu T Start u v0 E0 (HT:0<=T) (Hu:CoordinateContinuous u 0 T),
  0<=nu -> SpectralEnergyPath stokes_frequency nu T Start u v0 E0 ->
  forall eta (Heta:ClosedContinuous eta 0 T) i,
  exists L,
    SeqLimit (N.tested_source (indexed_convection_kernel i) u 0 T HT Hu eta Heta) L /\
    SeqLimit (vector_tested_source u 0 T HT Hu eta Heta i) L.
Proof.
  intros nu T Start u v0 E0 HT Hu Hnu Hpath.
  apply (BKNSE11_CONCRETE_FOURIER_SOURCE_LIMIT_EXISTS u 0 T E0 HT Hu).
  exact (BKEP10_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP stokes_frequency nu T
    Start u v0 E0 Hnu Hpath).
Qed.

(* The scalar equation uses +B on the left: its source prefix tends to
   minus the linear residual. No freely supplied forcing is used here. *)
Theorem BKNSE30_EXACT_FOURIER_QUADRATIC_ENERGY_PATH_CLASSIFICATION :
  forall q h nu T (Hq:0<q<1) (Hh:0<h) (HT:0<=T) Start U,
  ShellCoordinateContinuous U 0 T ->
  (forall t,0<=t<=T -> C.BKQRCompatible q h stokes_frequency (U t)) ->
  forall v0 E0,
  let psi:=C.bkqr_weights q h stokes_frequency Hq Hh in
  NativeQuadraticEnergyPath indexed_convection_kernel psi stokes_frequency
    (C.bkqr_ell q h) nu T Start U (gp_encode psi v0) E0 <->
  SpectralQuadraticEnergyPath indexed_convection_kernel stokes_frequency
    nu T Start (fun t=>reconstruct psi (U t)) v0 E0.
Proof.
  intros q h nu T Hq Hh HT Start U HU Hcomp v0 E0. cbv zeta.
  apply Q.BKQN12_EXACT_CANONICAL_QUADRATIC_ENERGY_PATH_CLASSIFICATION.
  - apply BKNF10_STOKES_FREQUENCY_NONNEGATIVE.
  - exact HT.
  - exact HU.
  - exact Hcomp.
Qed.

Theorem BKNSE40_NATIVE_ENERGY_PATH_HAS_CONCRETE_CONVECTION_SOURCE :
  forall q h nu T (Hq:0<q<1) (Hh:0<h) (HT:0<=T) Start U v0 E0,
  0<=nu ->
  forall Hpath:NativeEnergyPath stokes_frequency (C.bkqr_ell q h) nu T Start U
    (gp_encode (C.bkqr_weights q h stokes_frequency Hq Hh) v0) E0,
  let psi:=C.bkqr_weights q h stokes_frequency Hq Hh in
  let u:=fun t=>reconstruct psi (U t) in
  let HU:=proj1 Hpath in
  let Hu:=reconstruct_path_continuous psi U 0 T HU in
  forall eta k i,exists L,
    SeqLimit (coordinate_source indexed_convection_kernel u 0 T HT Hu eta i) L /\
    SeqLimit (native_source indexed_convection_kernel psi U 0 T HT HU eta k i)
      (psi k i*L).
Proof.
  intros q h nu T Hq Hh HT Start U v0 E0 Hnu Hpath.
  apply (Q.BKQN40_CANONICAL_ENERGY_PATH_HAS_OWN_NONLINEAR_SOURCE
    q h nu T stokes_frequency indexed_convection_kernel indexed_convection_bound
    Hq Hh HT Start U v0 E0).
  - apply BKNF10_STOKES_FREQUENCY_NONNEGATIVE.
  - exact Hnu.
  - apply BKFS40_INDEXED_CONVECTION_HAS_DERIVED_SCHUR_BOUND.
Qed.

Check BKNSE20_ENERGY_PATH_CONSTRUCTS_CONVECTION_SOURCE.
Check BKNSE30_EXACT_FOURIER_QUADRATIC_ENERGY_PATH_CLASSIFICATION.
Check BKNSE40_NATIVE_ENERGY_PATH_HAS_CONCRETE_CONVECTION_SOURCE.
Print Assumptions BKNSE10_TESTED_VECTOR_CONVOLUTION_IS_SAME_SOURCE.
Print Assumptions BKNSE12_CONCRETE_FOURIER_SOURCE_LIMIT_BOUND.
Print Assumptions BKNSE20_ENERGY_PATH_CONSTRUCTS_CONVECTION_SOURCE.
Print Assumptions BKNSE30_EXACT_FOURIER_QUADRATIC_ENERGY_PATH_CLASSIFICATION.
Print Assumptions BKNSE40_NATIVE_ENERGY_PATH_HAS_CONCRETE_CONVECTION_SOURCE.
End BKQR_NSE_FOURIER_CLASSIFICATION.
