From Stdlib Require Import Reals List Lra Psatz.
Require Import LHGP_Hilbert LHGP_Dual LHGP_Gradient.
Require Import LHGP_ClosedSubspace LHGP_OrthogonalProjection LHGP_DenseTestBasis.
Require Import LHGP_R3SmoothTests LHGP_ProjectedGradient.

Import ListNotations.
Open Scope R_scope.

Definition R3VectorTest := Axis3 -> R3SmoothTest.
Definition R3TensorTest := Axis3 -> Axis3 -> R3SmoothTest.
Definition R3VectorAdd (f g : R3VectorTest) : R3VectorTest :=
  fun a => R3TestAdd (f a) (g a).
Definition R3VectorScale c (f : R3VectorTest) : R3VectorTest :=
  fun a => R3TestScale c (f a).
Definition R3GradientTest (f : R3SmoothTest) : R3VectorTest :=
  fun a => R3TestDerivative a f.
Definition R3TensorDivergence (f : R3TensorTest) : R3VectorTest := fun i =>
  R3TestAdd (R3TestAdd
    (R3TestDerivative R3AxisX (f i R3AxisX))
    (R3TestDerivative R3AxisY (f i R3AxisY)))
    (R3TestDerivative R3AxisZ (f i R3AxisZ)).

Theorem R3_GRADIENT_IS_ACTUAL_PARTIAL : forall f a p,
  derivable_pt_lim (fun t => R3TestValue f (R3Shift p a t)) 0
    (R3TestValue (R3GradientTest f a) p).
Proof. apply R3_TEST_ACTUAL_PARTIAL. Qed.

Theorem R3_TENSOR_DIVERGENCE_EXACT : forall f i p,
  R3TestValue (R3TensorDivergence f i) p =
    R3Jet (f i R3AxisX) [R3AxisX] p +
    R3Jet (f i R3AxisY) [R3AxisY] p +
    R3Jet (f i R3AxisZ) [R3AxisZ] p.
Proof. reflexivity. Qed.

(* These are explicit spatial-L2 interpretation inputs, not a constructed
   Lebesgue space. R3Embed must send actual smooth vector fields to their
   ambient L2 classes. The inner product's Lebesgue meaning and density
   are still to be instantiated. Auxiliary jet/radius witnesses are ignored
   by field extensionality; no Hilbert norm is put on raw proof records. *)
Record R3VectorEmbedding (h : HilbertData) := {
  R3Embed : R3VectorTest -> HCarrier h;
  R3Embed_ext : forall f g,
    (forall a p, R3TestValue (f a) p = R3TestValue (g a) p) -> R3Embed f = R3Embed g;
  R3Embed_add : forall f g, R3Embed (R3VectorAdd f g) = HAdd h (R3Embed f) (R3Embed g);
  R3Embed_scale : forall c f, R3Embed (R3VectorScale c f) = HScale h c (R3Embed f)
}.

Definition R3TestAnnihilator h (E : R3VectorEmbedding h) : ClosedLinearSubspace h :=
  AnnihilatorSubspace h (fun q => R3Embed h E (R3GradientTest q)).

Theorem R3_TEST_ANNIHILATOR_MEMBERSHIP : forall h E u,
  (subspace_predicate (R3TestAnnihilator h E) u <->
   forall q : R3SmoothTest, HInner h u (R3Embed h E (R3GradientTest q)) = 0).
Proof. reflexivity. Qed.

Theorem R3_TEST_ANNIHILATOR_COMPLETE : forall h E,
  HComplete h -> HComplete (SubspaceHilbert (R3TestAnnihilator h E)).
Proof. intros h E HC; apply SubspaceComplete; exact HC. Qed.

Theorem R3_TEST_ANNIHILATOR_PROJECTION : forall h E,
  HComplete h -> exists P : HCarrier h -> HCarrier h,
    forall u, IsOrthogonalProjection (R3TestAnnihilator h E) u (P u).
Proof. intros h E HC; apply CLOSED_SUBSPACE_PROJECTION_MAP_EXISTS; exact HC. Qed.

(* The full physical tensor test domain is retained. Jet linearity makes
   divergence linear. Surjectivity states exactly the all-test coverage
   needed by a physical instance; it is not inferred from L2 density. *)
Record R3TensorTestMap (j : HilbertData) := {
  R3TensorOf : HCarrier j -> R3TensorTest;
  R3Tensor_add : forall x y i a w p,
    R3Jet (R3TensorOf (HAdd j x y) i a) w p =
      R3Jet (R3TensorOf x i a) w p + R3Jet (R3TensorOf y i a) w p;
  R3Tensor_scale : forall c x i a w p,
    R3Jet (R3TensorOf (HScale j c x) i a) w p = c * R3Jet (R3TensorOf x i a) w p;
  R3Tensor_all_tests : forall f : R3TensorTest, exists z : HCarrier j,
    forall i a w p, R3Jet (R3TensorOf z i a) w p = R3Jet (f i a) w p
}.

Definition R3RawDivergence h j (E : R3VectorEmbedding h) (F : R3TensorTestMap j)
    (z : HCarrier j) : HCarrier h :=
  R3Embed h E (R3TensorDivergence (R3TensorOf j F z)).

Theorem R3_RAW_DIVERGENCE_ADD : forall h j E F x y,
  R3RawDivergence h j E F (HAdd j x y) =
    HAdd h (R3RawDivergence h j E F x) (R3RawDivergence h j E F y).
Proof.
  intros h j E F x y; unfold R3RawDivergence.
  rewrite <- R3Embed_add; apply R3Embed_ext; intros i p.
  unfold R3VectorAdd; rewrite R3_TEST_ADD_VALUE.
  rewrite !R3_TENSOR_DIVERGENCE_EXACT, !R3Tensor_add; ring.
Qed.

Theorem R3_RAW_DIVERGENCE_SCALE : forall h j E F c x,
  R3RawDivergence h j E F (HScale j c x) =
    HScale h c (R3RawDivergence h j E F x).
Proof.
  intros h j E F c x; unfold R3RawDivergence.
  rewrite <- R3Embed_scale; apply R3Embed_ext; intros i p.
  unfold R3VectorScale; rewrite R3_TEST_SCALE_VALUE.
  rewrite !R3_TENSOR_DIVERGENCE_EXACT, !R3Tensor_scale; ring.
Qed.

Theorem R3_RAW_DIVERGENCE_COVERS_ALL_TESTS : forall h j E F f,
  exists z, R3RawDivergence h j E F z = R3Embed h E (R3TensorDivergence f).
Proof.
  intros h j E F f; destruct (R3Tensor_all_tests j F f) as [z Hz].
  exists z; unfold R3RawDivergence; apply R3Embed_ext; intros i p.
  rewrite !R3_TENSOR_DIVERGENCE_EXACT, !Hz; reflexivity.
Qed.

Theorem R3_PROJECTED_DIVERGENCE_CONSTRUCTED : forall h
    (E : R3VectorEmbedding h) (m : DualTestModel) (F : R3TensorTestMap (DTest m)),
  HComplete h -> inhabited (ProjectedDivergence h (R3TestAnnihilator h E) m
    (R3RawDivergence h (DTest m) E F)).
Proof.
  intros h E m F HC; apply PROJECTED_DIVERGENCE_CONSTRUCTED.
  - exact HC.
  - apply R3_RAW_DIVERGENCE_ADD.
  - apply R3_RAW_DIVERGENCE_SCALE.
Qed.

(* The dual model is now built from density and infinite dimension, rather
   than requiring an ONB with smooth lifts as an unexplained input. These
   hypotheses concern fixed spaces, not an individual LH trajectory. *)
Section DensePhysicalTestAssembly.
Variables h k j : HilbertData.
Variable E : R3VectorEmbedding h.
Variable F : R3TensorTestMap j.
Variable J : HCarrier j -> HCarrier k.
Hypothesis J_inner : forall x y, HInner k (J x) (J y) = HInner j x y.
Hypothesis J_add : forall x y, J (HAdd j x y) = HAdd k (J x) (J y).
Hypothesis J_scale : forall c x, J (HScale j c x) = HScale k c (J x).
Variable d : nat -> HCarrier j.
Hypothesis HD : CountablyDense k (fun n => J (d n)).
Hypothesis HI : HInfiniteDimension k.
Hypothesis HC : HComplete h.
Hypothesis KC : HComplete k.

Definition R3AssembledDual : DualTestModel :=
  DenseTestsDualModel k j J J_inner J_add J_scale d HD HI KC.

Theorem R3_DENSE_TEST_PROJECTED_ASSEMBLY :
  inhabited (ProjectedDivergence h (R3TestAnnihilator h E) R3AssembledDual
    (R3RawDivergence h j E F)).
Proof. apply R3_PROJECTED_DIVERGENCE_CONSTRUCTED; exact HC. Qed.

End DensePhysicalTestAssembly.

Theorem SUBSPACE_PROJECTED_SEQUENCE_DENSE : forall h (s : ClosedLinearSubspace h)
    P (HP : forall x, IsOrthogonalProjection s x (P x)) d,
  CountablyDense h d -> CountablyDense (SubspaceHilbert s)
    (fun n => exist _ (P (d n)) (proj1 (HP (d n)))).
Proof.
  intros h s P HP d HD x eps Heps.
  destruct (HD (SubspaceInclude s x) eps Heps) as [n Hn].
  exists n; change (HDist h (SubspaceInclude s x) (P (d n)) < eps).
  pose proof (ORTHOGONAL_PROJECTION_CONTRACTION h s P HP
    (SubspaceInclude s x) (d n)) as Hcontract.
  rewrite (ORTHOGONAL_PROJECTION_FIXED h s P HP (SubspaceInclude s x)
    (SubspaceInclude_member h s x)) in Hcontract; lra.
Qed.

Theorem SUBSPACE_ONB_RECONSTRUCTION_FROM_AMBIENT_DENSITY :
  forall h (s : ClosedLinearSubspace h) d,
  HComplete h -> CountablyDense h d -> HInfiniteDimension (SubspaceHilbert s) ->
  exists b : OrthonormalBasis (SubspaceHilbert s), forall x,
    HConverges (SubspaceHilbert s) (HFinite b (HAnalysis b x)) x.
Proof.
  intros h s d HC HD HI.
  destruct (CLOSED_SUBSPACE_PROJECTION_MAP_EXISTS h s HC) as [P HP].
  set (ds := fun n => exist (subspace_predicate s) (P (d n)) (proj1 (HP (d n)))).
  assert (Hds : CountablyDense (SubspaceHilbert s) ds).
  { apply SUBSPACE_PROJECTED_SEQUENCE_DENSE; exact HD. }
  pose (b := DenseTestONB (SubspaceHilbert s) (SubspaceHilbert s)
    (fun x => x) (fun x y => eq_refl) (fun x y => eq_refl)
    (fun c x => eq_refl) ds Hds HI).
  exists b; intro x; apply HAnalysis_reconstruction; apply SubspaceComplete; exact HC.
Qed.

Print Assumptions R3_GRADIENT_IS_ACTUAL_PARTIAL.
Print Assumptions R3_TEST_ANNIHILATOR_COMPLETE.
Print Assumptions R3_TEST_ANNIHILATOR_PROJECTION.
Print Assumptions R3_RAW_DIVERGENCE_COVERS_ALL_TESTS.
Print Assumptions R3_DENSE_TEST_PROJECTED_ASSEMBLY.
Print Assumptions SUBSPACE_ONB_RECONSTRUCTION_FROM_AMBIENT_DENSITY.
