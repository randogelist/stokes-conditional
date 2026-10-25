From Stdlib Require Import Reals Lra Psatz Lia.
Require Import BKQR_CountableRange BKQR_BilinearKernel BKQR_FourierIndices.
Require Import BKQR_FourierBlocks BKQR_FourierConvection BKQR_FourierSchur.

(* Literal Fourier coefficients of the projected divergence-form quadratic
   term on the 2*pi periodic lattice. The finite scalar cuts below are
   identified with finite complex-vector convolution, not merely assigned
   a physical name. Spatial function realization remains separate. *)
Module BKQR_NSE_FOURIER_KERNEL.
Import GP_COUNTABLE_RANGE BKQR_BILINEAR_KERNEL BKQR_FOURIER_INDICES.
Import BKQR_FOURIER_BLOCKS BKQR_FOURIER_CONVECTION BKQR_FOURIER_SCHUR.
Open Scope R_scope.

Definition stokes_frequency (i:nat) : R := sqrt (mode_norm2 (decode_mode i)).

Theorem BKNF10_STOKES_FREQUENCY_NONNEGATIVE : forall i,0<=stokes_frequency i.
Proof. intro i. apply sqrt_pos. Qed.

Theorem BKNF11_ACTUAL_STOKES_SYMBOL : forall i,
  stokes_frequency i*stokes_frequency i=mode_norm2 (decode_mode i).
Proof. intro i. apply sqrt_sqrt. apply mode_norm2_nonnegative. Qed.

Definition mode_vector (x:nat->R) (p:nat) : ComplexVector :=
  vector_from_scalars (fun tag=>x (6*p+tag)%nat).

Definition pair_readout (i p q:nat) (x:nat->R) : R :=
  if mode_eq_dec (mode_add (mode_decode p) (mode_decode q)) (decode_mode i)
  then scalar_tag (projected_convection (decode_mode i)
    (mode_vector x p) (mode_vector x q)) (decode_tag i)
  else 0.

Definition finite_vector_convolution (i N:nat) (x:nat->R) : R :=
  gp_sum N (fun p=>gp_sum N (fun q=>pair_readout i p q x)).

Lemma indexed_kernel_on_blocks : forall i p q s t,
  (s<6)%nat -> (t<6)%nat ->
  indexed_convection_kernel i (6*p+s)%nat (6*q+t)%nat =
  if mode_eq_dec (mode_add (mode_decode p) (mode_decode q)) (decode_mode i)
  then convection_coefficient (decode_mode i) (decode_tag i) s t else 0.
Proof.
  intros i p q s t Hs Ht. unfold indexed_convection_kernel,mode_matched_kernel.
  rewrite !decode_mode_block, !decode_tag_block by assumption. reflexivity.
Qed.

Lemma complete_pair_block_identity : forall i p q x,
  gp_sum 6 (fun s=>gp_sum 6 (fun t=>
    indexed_convection_kernel i (6*p+s)%nat (6*q+t)%nat *
      x (6*p+s)%nat*x (6*q+t)%nat))=pair_readout i p q x.
Proof.
  intros i p q x.
  transitivity (gp_sum 6 (fun s=>gp_sum 6 (fun t=>
    (if mode_eq_dec (mode_add (mode_decode p) (mode_decode q)) (decode_mode i)
     then convection_coefficient (decode_mode i) (decode_tag i) s t else 0)*
      x (6*p+s)%nat*x (6*q+t)%nat))).
  - apply gp_sum_ext. intros s Hs. apply gp_sum_ext. intros t Ht.
    rewrite indexed_kernel_on_blocks by assumption. reflexivity.
  - unfold pair_readout. destruct (mode_eq_dec
      (mode_add (mode_decode p) (mode_decode q)) (decode_mode i)).
    + symmetry. apply CONVECTION_REALIFICATION. apply decode_tag_bound.
    + transitivity (gp_sum 6 (fun _=>0)); [|apply sum_zero].
      apply gp_sum_ext. intros s Hs.
      transitivity (gp_sum 6 (fun _=>0)); [|apply sum_zero].
      apply gp_sum_ext. intros t Ht. ring.
Qed.

Theorem BKNF20_FULL_SCALAR_CUT_IS_VECTOR_CONVOLUTION : forall i N x,
  quadratic_form (indexed_convection_kernel i) (6*N)%nat x=
  finite_vector_convolution i N x.
Proof.
  intros i N x. unfold quadratic_form,bilinear_form,bilinear_rectangle.
  rewrite BKFB20_EXACT_DOUBLE_BLOCK_SUM. unfold finite_vector_convolution.
  apply gp_sum_ext. intros p Hp. apply gp_sum_ext. intros q Hq.
  apply complete_pair_block_identity.
Qed.

Definition BlockSolenoidal (x:nat->R) (N:nat) : Prop :=
  forall p,(p<N)%nat -> complex_dot (mode_decode p) (mode_vector x p)=czero.

Definition advective_pair_readout (i p q:nat) (x:nat->R) : R :=
  if mode_eq_dec (mode_add (mode_decode p) (mode_decode q)) (decode_mode i)
  then scalar_tag (advective_convection (decode_mode i) (mode_decode q)
    (mode_vector x p) (mode_vector x q)) (decode_tag i)
  else 0.

Definition finite_advective_convolution (i N:nat) (x:nat->R) : R :=
  gp_sum N (fun p=>gp_sum N (fun q=>advective_pair_readout i p q x)).

Theorem BKNF21_SOLENOIDAL_ADVECTIVE_CONVOLUTION_IDENTITY : forall i N x,
  BlockSolenoidal x N ->
  quadratic_form (indexed_convection_kernel i) (6*N)%nat x=
  finite_advective_convolution i N x.
Proof.
  intros i N x Hdiv. rewrite BKNF20_FULL_SCALAR_CUT_IS_VECTOR_CONVOLUTION.
  unfold finite_vector_convolution,finite_advective_convolution.
  apply gp_sum_ext. intros p Hp. apply gp_sum_ext. intros q Hq.
  unfold pair_readout,advective_pair_readout. destruct (mode_eq_dec
    (mode_add (mode_decode p) (mode_decode q)) (decode_mode i)) as [Htriad|Hno];
    [|reflexivity].
  unfold scalar_tag. rewrite (CONVECTION_DERIVATIVE_MOVES_TO_OUTPUT
    (decode_mode i) (mode_decode p) (mode_decode q)
    (mode_vector x p) (mode_vector x q) Htriad (Hdiv p Hp)). reflexivity.
Qed.

Print Assumptions BKNF11_ACTUAL_STOKES_SYMBOL.
Print Assumptions BKNF20_FULL_SCALAR_CUT_IS_VECTOR_CONVOLUTION.
Print Assumptions BKNF21_SOLENOIDAL_ADVECTIVE_CONVOLUTION_IDENTITY.
End BKQR_NSE_FOURIER_KERNEL.
