From Stdlib Require Import Reals Lra Psatz Lia ZArith Field.
Require Import BKQR_CountableRange BKQR_ScalarProfile BKQR_ShellCoordinates.
Require Import BKQR_ClassificationAudit BKQR_FourierIndices BKQR_FourierConvection.
Require Import BKQR_NSEFourierKernel BKQR_FourierBlocks.

(* Concrete Fourier constraints on the six real coordinates of each lattice
   mode.  The spectral/BKQR transport is exact; no spatial L2 realization is
   presumed.  Zero mean is an additional, separate condition. *)
Module BKQR_FOURIER_ADMISSIBILITY.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_FOURIER_INDICES.
Import BKQR_FOURIER_CONVECTION BKQR_NSE_FOURIER_KERNEL BKQR_FOURIER_BLOCKS.
Module S := BKQR_SCALAR_PROFILE.
Module C := BKQR_CLASSIFICATION.
Open Scope R_scope.

Definition cconj (z:C2) : C2 := (cre z,-cim z).
Definition fourier_coefficient (x:nat->R) (m:Z3) : ComplexVector :=
  vector_from_scalars (fun tag=>x (encode_index m tag)).

Definition FourierReality (x:nat->R) : Prop :=
  forall m a, (a<3)%nat ->
    fourier_coefficient x (mode_neg m) a=cconj (fourier_coefficient x m a).
Definition FourierSolenoidal (x:nat->R) : Prop :=
  forall m, complex_dot m (fourier_coefficient x m)=czero.
Definition FourierZeroMean (x:nat->R) : Prop :=
  forall a, (a<3)%nat -> fourier_coefficient x mode_zero a=czero.
Definition FourierAdmissible (x:nat->R) : Prop :=
  FourierReality x /\ FourierSolenoidal x.

Definition NativeReality (U:nat->nat->R) : Prop := forall k, FourierReality (U k).
Definition NativeSolenoidal (U:nat->nat->R) : Prop := forall k, FourierSolenoidal (U k).
Definition NativeZeroMean (U:nat->nat->R) : Prop := forall k, FourierZeroMean (U k).
Definition NativeAdmissible (U:nat->nat->R) : Prop := NativeReality U /\ NativeSolenoidal U.

Lemma fourier_coefficient_on_block : forall x p a,
  fourier_coefficient x (mode_decode p) a=mode_vector x p a.
Proof.
  intros x p a. unfold fourier_coefficient,mode_vector,vector_from_scalars.
  rewrite !encode_mode_block. reflexivity.
Qed.

Theorem FOURIER_SOLENOIDAL_IMPLIES_BLOCK_SOLENOIDAL : forall x,
  FourierSolenoidal x -> forall N, BlockSolenoidal x N.
Proof.
  intros x Hdiv N p Hp. rewrite <- (Hdiv (mode_decode p)).
  unfold complex_dot,csum3. rewrite !fourier_coefficient_on_block. reflexivity.
Qed.

Lemma mode_neg_involutive : forall m, mode_neg (mode_neg m)=m.
Proof.
  intros [x y z]. unfold mode_neg,mode_sub,mode_zero. cbn. f_equal; lia.
Qed.

Lemma wave_neg : forall m a, wave (mode_neg m) a= -wave m a.
Proof.
  intros m [|[|a]]; unfold wave,mode_neg,mode_sub,mode_zero; cbn;
    rewrite opp_IZR; reflexivity.
Qed.

Theorem MODE_NORM2_NEGATION_INVARIANT : forall m,
  mode_norm2 (mode_neg m)=mode_norm2 m.
Proof. intro m. unfold mode_norm2. rewrite !wave_neg. ring. Qed.

Lemma stokes_frequency_encoded : forall m tag, (tag<6)%nat ->
  stokes_frequency (encode_index m tag)=sqrt (mode_norm2 m).
Proof.
  intros m tag Htag. unfold stokes_frequency. rewrite decode_mode_encode by exact Htag.
  reflexivity.
Qed.

Theorem STOKES_FREQUENCY_NEGATION_INVARIANT : forall m s t,
  (s<6)%nat -> (t<6)%nat ->
  stokes_frequency (encode_index (mode_neg m) s)=stokes_frequency (encode_index m t).
Proof.
  intros m s t Hs Ht. rewrite !stokes_frequency_encoded by assumption.
  rewrite MODE_NORM2_NEGATION_INVARIANT. reflexivity.
Qed.

(* Equality of normalizers follows from uniqueness of least upper bounds.
   Different proofs of positivity do not require a proof-irrelevance axiom. *)
Lemma scalar_normalizer_witness_independent : forall q x Hq Hq' Hx Hx',
  S.normalizer q x Hq Hx=S.normalizer q x Hq' Hx'.
Proof.
  intros q x Hq Hq' Hx Hx'.
  pose proof (proj1 (S.SCALAR_NORMALIZER_SPEC q x Hq Hx)) as HA.
  pose proof (proj1 (S.SCALAR_NORMALIZER_SPEC q x Hq' Hx')) as HB.
  apply Rle_antisym.
  - apply (proj2 HA). exact (proj1 HB).
  - apply (proj2 HB). exact (proj1 HA).
Qed.

Lemma scalar_profile_equal_arguments : forall q x y Hq Hx Hy,
  x=y -> forall k, S.psi q x Hq Hx k=S.psi q y Hq Hy k.
Proof.
  intros q x y Hq Hx Hy Hxy k. subst y. unfold S.psi,S.probability.
  rewrite (scalar_normalizer_witness_independent q x Hq Hq Hx Hy). reflexivity.
Qed.

Lemma cscale_conjugate : forall a z, cscale a (cconj z)=cconj (cscale a z).
Proof. intros a [r i]. unfold cscale,cconj,cre,cim. cbn. f_equal; ring. Qed.

Lemma cscale_zero : forall a, cscale a czero=czero.
Proof. intro a. unfold cscale,czero,cre,cim. cbn. f_equal; ring. Qed.

Lemma complex_dot_scale : forall m a u,
  complex_dot m (fun r=>cscale a (u r))=cscale a (complex_dot m u).
Proof.
  intros m a u. unfold complex_dot,csum3,cadd,cscale,cre,cim. cbn. f_equal; ring.
Qed.

Lemma complex_dot_ext : forall m u v,
  (forall a,(a<3)%nat -> u a=v a) -> complex_dot m u=complex_dot m v.
Proof.
  intros m u v H. unfold complex_dot,csum3.
  rewrite (H 0%nat), (H 1%nat), (H 2%nat) by lia. reflexivity.
Qed.

Lemma fourier_coefficient_ext : forall x y,
  (forall i,x i=y i) -> forall m a, fourier_coefficient x m a=fourier_coefficient y m a.
Proof.
  intros x y H m a. unfold fourier_coefficient,vector_from_scalars.
  rewrite !H. reflexivity.
Qed.

Lemma FourierReality_ext : forall x y,
  (forall i,x i=y i) -> FourierReality x -> FourierReality y.
Proof.
  intros x y H Hreal m a Ha.
  rewrite <- (fourier_coefficient_ext x y H (mode_neg m) a).
  rewrite <- (fourier_coefficient_ext x y H m a). apply Hreal. exact Ha.
Qed.

Lemma FourierSolenoidal_ext : forall x y,
  (forall i,x i=y i) -> FourierSolenoidal x -> FourierSolenoidal y.
Proof.
  intros x y H Hdiv m. rewrite <- (Hdiv m).
  apply complex_dot_ext. intros a Ha. symmetry. apply fourier_coefficient_ext. exact H.
Qed.

Lemma FourierZeroMean_ext : forall x y,
  (forall i,x i=y i) -> FourierZeroMean x -> FourierZeroMean y.
Proof.
  intros x y H Hz a Ha. rewrite <- (fourier_coefficient_ext x y H mode_zero a).
  apply Hz. exact Ha.
Qed.

Section CanonicalWeights.
Variables q h:R.
Hypothesis Hq:0<q<1.
Hypothesis Hh:0<h.
Let psi := C.bkqr_weights q h stokes_frequency Hq Hh.

Definition mode_weight k m := psi k (encode_index m 0%nat).

Lemma bkqr_weights_same_frequency : forall k i j,
  stokes_frequency i=stokes_frequency j -> psi k i=psi k j.
Proof.
  intros k i j Hfreq. unfold psi,C.bkqr_weights.
  apply scalar_profile_equal_arguments. unfold C.spectral_argument. rewrite Hfreq.
  reflexivity.
Qed.

Theorem BKFA10_MODE_WEIGHT_INDEPENDENT_OF_TAG : forall k m tag,
  (tag<6)%nat -> psi k (encode_index m tag)=mode_weight k m.
Proof.
  intros k m tag Htag. unfold mode_weight. apply bkqr_weights_same_frequency.
  rewrite !stokes_frequency_encoded by lia. reflexivity.
Qed.

Theorem BKFA11_MODE_WEIGHT_NEGATION_INVARIANT : forall k m,
  mode_weight k (mode_neg m)=mode_weight k m.
Proof.
  intros k m. unfold mode_weight. apply bkqr_weights_same_frequency.
  apply STOKES_FREQUENCY_NEGATION_INVARIANT; lia.
Qed.

Lemma mode_weight_zero_nonzero : forall m, mode_weight 0%nat m<>0.
Proof. intro m. apply C.BKCL02_ZERO_WEIGHT_NONZERO. Qed.

Theorem BKFA20_ENCODED_COEFFICIENT_FACTOR : forall x k m a,
  (a<3)%nat ->
  fourier_coefficient (gp_encode psi x k) m a=
    cscale (mode_weight k m) (fourier_coefficient x m a).
Proof.
  intros x k m a Ha.
  cbv [fourier_coefficient vector_from_scalars gp_encode cscale cre cim fst snd].
  rewrite !BKFA10_MODE_WEIGHT_INDEPENDENT_OF_TAG by lia. reflexivity.
Qed.

Theorem BKFA21_DECODED_COEFFICIENT_FACTOR : forall U m a,
  (a<3)%nat ->
  fourier_coefficient (reconstruct psi U) m a=
    cscale (/mode_weight 0%nat m) (fourier_coefficient (U 0%nat) m a).
Proof.
  intros U m a Ha.
  cbv [fourier_coefficient vector_from_scalars reconstruct cscale cre cim fst snd].
  rewrite !BKFA10_MODE_WEIGHT_INDEPENDENT_OF_TAG by lia.
  unfold Rdiv. f_equal; ring.
Qed.

Theorem BKFA30_ENCODING_PRESERVES_REALITY : forall x,
  FourierReality x -> NativeReality (gp_encode psi x).
Proof.
  intros x Hreal k m a Ha. rewrite !BKFA20_ENCODED_COEFFICIENT_FACTOR by exact Ha.
  rewrite BKFA11_MODE_WEIGHT_NEGATION_INVARIANT, (Hreal m a Ha).
  apply cscale_conjugate.
Qed.

Theorem BKFA31_RECONSTRUCTION_PRESERVES_REALITY : forall U,
  NativeReality U -> FourierReality (reconstruct psi U).
Proof.
  intros U Hreal m a Ha. rewrite !BKFA21_DECODED_COEFFICIENT_FACTOR by exact Ha.
  rewrite BKFA11_MODE_WEIGHT_NEGATION_INVARIANT, (Hreal 0%nat m a Ha).
  apply cscale_conjugate.
Qed.

Theorem BKFA32_ENCODING_PRESERVES_SOLENOIDALITY : forall x,
  FourierSolenoidal x -> NativeSolenoidal (gp_encode psi x).
Proof.
  intros x Hdiv k m.
  transitivity (complex_dot m (fun a=>cscale (mode_weight k m)
    (fourier_coefficient x m a))).
  - apply complex_dot_ext. intros a Ha. apply BKFA20_ENCODED_COEFFICIENT_FACTOR. exact Ha.
  - rewrite complex_dot_scale,Hdiv,cscale_zero. reflexivity.
Qed.

Theorem BKFA33_RECONSTRUCTION_PRESERVES_SOLENOIDALITY : forall U,
  NativeSolenoidal U -> FourierSolenoidal (reconstruct psi U).
Proof.
  intros U Hdiv m.
  transitivity (complex_dot m (fun a=>cscale (/mode_weight 0%nat m)
    (fourier_coefficient (U 0%nat) m a))).
  - apply complex_dot_ext. intros a Ha. apply BKFA21_DECODED_COEFFICIENT_FACTOR. exact Ha.
  - rewrite complex_dot_scale,Hdiv,cscale_zero. reflexivity.
Qed.

Theorem BKFA34_ENCODING_PRESERVES_ZERO_MEAN : forall x,
  FourierZeroMean x -> NativeZeroMean (gp_encode psi x).
Proof.
  intros x Hz k a Ha. rewrite BKFA20_ENCODED_COEFFICIENT_FACTOR by exact Ha.
  rewrite (Hz a Ha),cscale_zero. reflexivity.
Qed.

Theorem BKFA35_RECONSTRUCTION_PRESERVES_ZERO_MEAN : forall U,
  NativeZeroMean U -> FourierZeroMean (reconstruct psi U).
Proof.
  intros U Hz a Ha. rewrite BKFA21_DECODED_COEFFICIENT_FACTOR by exact Ha.
  rewrite (Hz 0%nat a Ha),cscale_zero. reflexivity.
Qed.

Lemma compatible_factorization : forall U,
  C.BKQRCompatible q h stokes_frequency U ->
  forall k i,U k i=gp_encode psi (reconstruct psi U) k i.
Proof.
  intros U HU.
  exact (proj1 (C.BKCL11_RECONSTRUCTION_AND_UNIQUENESS q h stokes_frequency
    Hq Hh BKNF10_STOKES_FREQUENCY_NONNEGATIVE U HU)).
Qed.

Theorem BKFA40_REALITY_ON_COMPATIBLE_RANGE : forall U,
  C.BKQRCompatible q h stokes_frequency U ->
  (FourierReality (reconstruct psi U) <-> NativeReality U).
Proof.
  intros U HU. split.
  - intros Hreal k. eapply FourierReality_ext.
    + intro i. symmetry. apply compatible_factorization. exact HU.
    + exact (BKFA30_ENCODING_PRESERVES_REALITY (reconstruct psi U) Hreal k).
  - apply BKFA31_RECONSTRUCTION_PRESERVES_REALITY.
Qed.

Theorem BKFA41_SOLENOIDALITY_ON_COMPATIBLE_RANGE : forall U,
  C.BKQRCompatible q h stokes_frequency U ->
  (FourierSolenoidal (reconstruct psi U) <-> NativeSolenoidal U).
Proof.
  intros U HU. split.
  - intros Hdiv k. eapply FourierSolenoidal_ext.
    + intro i. symmetry. apply compatible_factorization. exact HU.
    + exact (BKFA32_ENCODING_PRESERVES_SOLENOIDALITY (reconstruct psi U) Hdiv k).
  - apply BKFA33_RECONSTRUCTION_PRESERVES_SOLENOIDALITY.
Qed.

Theorem BKFA42_ZERO_MEAN_ON_COMPATIBLE_RANGE : forall U,
  C.BKQRCompatible q h stokes_frequency U ->
  (FourierZeroMean (reconstruct psi U) <-> NativeZeroMean U).
Proof.
  intros U HU. split.
  - intros Hz k. eapply FourierZeroMean_ext.
    + intro i. symmetry. apply compatible_factorization. exact HU.
    + exact (BKFA34_ENCODING_PRESERVES_ZERO_MEAN (reconstruct psi U) Hz k).
  - apply BKFA35_RECONSTRUCTION_PRESERVES_ZERO_MEAN.
Qed.

Theorem BKFA50_ADMISSIBILITY_ON_COMPATIBLE_RANGE : forall U,
  C.BKQRCompatible q h stokes_frequency U ->
  (FourierAdmissible (reconstruct psi U) <-> NativeAdmissible U).
Proof.
  intros U HU. unfold FourierAdmissible,NativeAdmissible.
  rewrite (BKFA40_REALITY_ON_COMPATIBLE_RANGE U HU),
    (BKFA41_SOLENOIDALITY_ON_COMPATIBLE_RANGE U HU). reflexivity.
Qed.

Theorem BKFA51_ENCODING_ADMISSIBILITY : forall x,
  FourierAdmissible x <-> NativeAdmissible (gp_encode psi x).
Proof.
  intro x. split.
  - intros [Hr Hd]. split.
    + apply BKFA30_ENCODING_PRESERVES_REALITY. exact Hr.
    + apply BKFA32_ENCODING_PRESERVES_SOLENOIDALITY. exact Hd.
  - intros [Hr Hd]. split.
    + eapply FourierReality_ext with (x:=reconstruct psi (gp_encode psi x)).
      * intro i. apply BKSC02_RECONSTRUCT_ENCODE. apply C.BKCL02_ZERO_WEIGHT_NONZERO.
      * apply BKFA31_RECONSTRUCTION_PRESERVES_REALITY. exact Hr.
    + eapply FourierSolenoidal_ext with (x:=reconstruct psi (gp_encode psi x)).
      * intro i. apply BKSC02_RECONSTRUCT_ENCODE. apply C.BKCL02_ZERO_WEIGHT_NONZERO.
      * apply BKFA33_RECONSTRUCTION_PRESERVES_SOLENOIDALITY. exact Hd.
Qed.

End CanonicalWeights.

Print Assumptions MODE_NORM2_NEGATION_INVARIANT.
Print Assumptions BKFA11_MODE_WEIGHT_NEGATION_INVARIANT.
Print Assumptions BKFA50_ADMISSIBILITY_ON_COMPATIBLE_RANGE.
Print Assumptions BKFA51_ENCODING_ADMISSIBILITY.
End BKQR_FOURIER_ADMISSIBILITY.
