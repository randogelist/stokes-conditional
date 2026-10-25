(* Composes the full R3 smooth-test construction with the BKQR shell bridge.
   The ambient Hilbert carriers, embeddings, evolution tests, and time data
   remain explicit. This does not construct physical Lebesgue L2(R3). *)
From Stdlib Require Import Reals.
Require Import LHGP_Hilbert LHGP_ClosedSubspace LHGP_OrthogonalProjection.
Require Import LHGP_DenseTestBasis LHGP_R3SmoothTests LHGP_Completion060.
Require Import LHGP_Completion070 BKQR_CountableRange BKQR_ClassificationAudit.
Require Import BKQR_LHGP_ForwardBridge.
Module BKQR_LHGP_R3_BRIDGE.
Module B := GP_COUNTABLE_RANGE.
Module C := BKQR_CLASSIFICATION.
Import BKQR_LHGP_FORWARD_BRIDGE.
Open Scope R_scope.
Theorem BKLF40_CANONICAL_R3_FORWARD_CONTAINMENT :
  forall (q step : R) (lambda : nat -> R)
    (Hq : 0 < q < 1) (Hstep : 0 < step)
    (Hlambda : forall i, 0 <= lambda i)
    (v k : HilbertData) (E : R3VectorEmbedding v)
    (J : R3TensorTest -> HCarrier k)
    (JDense : forall G eps, 0 < eps ->
      exists z, HDist k G (J z) < eps)
    (d : nat -> HCarrier v),
  HComplete v -> CountablyDense v d ->
  HInfiniteDimension (SubspaceHilbert (R3TestAnnihilator v E)) ->
  exists P : HCarrier v -> HCarrier v,
  exists HP : forall x,
    IsOrthogonalProjection (R3TestAnnihilator v E) x (P x),
  exists basis : OrthonormalBasis
    (SubspaceHilbert (R3TestAnnihilator v E)),
  forall tests td nu T u u0,
    RawForwardLHModel v k (R3TestAnnihilator v E) R3TensorTest
      J (R3ForwardRawDiv v E) tests td nu T u u0 ->
    NativeForwardLHModel (SubspaceHilbert (R3TestAnnihilator v E))
      k basis
      (ProjectedForwardGradient v k (R3TestAnnihilator v E)
        R3TensorTest J (R3ForwardRawDiv v E) JDense P HP)
      tests td nu T (C.bkqr_weights q step lambda Hq Hstep)
      lambda (C.bkqr_ell q step)
      (fun t => B.gp_encode (C.bkqr_weights q step lambda Hq Hstep)
        (HAnalysis basis (u t)))
      (B.gp_encode (C.bkqr_weights q step lambda Hq Hstep)
        (HAnalysis basis u0)).
Proof.
  intros q step lambda Hq Hstep Hlambda v k E J JDense d HC HD HI.
  destruct (R3_TEST_ANNIHILATOR_PROJECTION v E HC) as [P HP].
  destruct (SUBSPACE_ONB_RECONSTRUCTION_FROM_AMBIENT_DENSITY v
    (R3TestAnnihilator v E) d HC HD HI) as [basis Hreconstruction].
  exists P, HP, basis; intros tests td nu T u u0 Hraw.
  apply (BKLF30_CANONICAL_HILBERT_FORWARD_CONTAINMENT
    q step lambda Hq Hstep Hlambda
    (SubspaceHilbert (R3TestAnnihilator v E)) k basis
    (SubspaceComplete v (R3TestAnnihilator v E) HC)
    (ProjectedForwardGradient v k (R3TestAnnihilator v E)
      R3TensorTest J (R3ForwardRawDiv v E) JDense P HP)
    tests td nu T u u0).
  exact (RAW_FORWARD_SOURCE_TRANSPORT v k (R3TestAnnihilator v E)
    R3TensorTest J (R3ForwardRawDiv v E) JDense P HP
    tests td nu T u u0 Hraw).
Qed.

Print Assumptions BKLF40_CANONICAL_R3_FORWARD_CONTAINMENT.
End BKQR_LHGP_R3_BRIDGE.
