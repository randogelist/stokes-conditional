From Stdlib Require Import Reals Lra Psatz.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Realization LHGP_WeakTopology.
Require Import LHGP_Evolution LHGP_Equivalence LHGP_NativeDiagonal.
Require Import LHGP_ClosedSubspace LHGP_OrthogonalProjection LHGP_DenseTestBasis.
Require Import LHGP_R3SmoothTests LHGP_Completion060.
Require Import LHGP_ForwardGradient LHGP_ForwardReadouts.
Require Import LHGP_InitialEnergy LHGP_ForwardContainment.

Open Scope R_scope.

(* The forward construction takes ALL tests directly. Test need not carry
   a Hilbert structure, a quotient, linear operations, or an ONB. Only its
   image is dense in the gradient target. That target need not be complete.
   The velocity projection is supplied here with its proved specification;
   the existence theorem below constructs it from ambient completeness. *)
Section ProjectedForwardConstruction.
Variables v k : HilbertData.
Variable s : ClosedLinearSubspace v.
Variable Test : Type.
Variable embed : Test -> HCarrier k.
Variable rawDiv : Test -> HCarrier v.
Hypothesis dense : forall G eps, 0 < eps ->
  exists z, HDist k G (embed z) < eps.
Variable P : HCarrier v -> HCarrier v.
Hypothesis HP : forall x, IsOrthogonalProjection s x (P x).

Definition ProjectedForwardGradient : ForwardGradientData (SubspaceHilbert s) k.
Proof.
  refine (@Build_ForwardGradientData (SubspaceHilbert s) k Test embed _ dense).
  intro z; exists (P (rawDiv z)); exact (proj1 (HP (rawDiv z))).
Defined.

Definition RawWeakGradient (u : HCarrier (SubspaceHilbert s))
    (G : HCarrier k) : Prop :=
  forall z, - HInner v (SubspaceInclude s u) (rawDiv z) =
    HInner k G (embed z).

Theorem PROJECTED_FORWARD_PAIRING : forall u z,
  HInner (SubspaceHilbert s) u
    (FGDiv (SubspaceHilbert s) k ProjectedForwardGradient z) =
  HInner v (SubspaceInclude s u) (rawDiv z).
Proof.
  intros u z; change (HInner v (SubspaceInclude s u) (P (rawDiv z)) =
    HInner v (SubspaceInclude s u) (rawDiv z)).
  apply (ORTHOGONAL_PROJECTION_PAIRING v s P HP).
  apply SubspaceInclude_member.
Qed.

Theorem PROJECTED_FORWARD_KNOWN_GRADIENT : forall u G,
  RawWeakGradient u G ->
  WeakGradientForward (SubspaceHilbert s) k ProjectedForwardGradient u G.
Proof.
  intros u G HG z; unfold RawWeakGradient in HG.
  rewrite PROJECTED_FORWARD_PAIRING; apply HG.
Qed.

(* The raw source class contains no GP readout. Its weak gradient is stated
   by ambient pairings on the original full test carrier. TimeData is still
   an explicit integration interpretation, not a constructed Lebesgue space. *)
Definition RawForwardEnergyLedger (td : TimeData) (nu T : R)
    (u : R -> HCarrier (SubspaceHilbert s)) : Prop :=
  exists (E D : R -> R) (GoodD : R -> Prop),
    EnergySchedule0 td nu T E D GoodD /\
    (forall t, E t = HNorm (SubspaceHilbert s) (u t)) /\
    (forall t, 0 <= t <= T -> GoodD t ->
      exists G, RawWeakGradient (u t) G /\ HNorm k G = D t).

Definition RawForwardLHModel (tests : EvolutionTests (SubspaceHilbert s))
    (td : TimeData) (nu T : R)
    (u : R -> HCarrier (SubspaceHilbert s))
    (u0 : HCarrier (SubspaceHilbert s)) : Prop :=
  0 < nu /\ 0 < T /\ u 0 = u0 /\
  HWeakContinuous (SubspaceHilbert s) u T /\
  (exists M, forall t, 0 <= t <= T -> HNorm (SubspaceHilbert s) (u t) <= M) /\
  HilbertWeakForm (SubspaceHilbert s) tests td nu T u u0 /\
  RawForwardEnergyLedger td nu T u.

Theorem RAW_FORWARD_ENERGY_LEDGER_TRANSPORT : forall td nu T u,
  RawForwardEnergyLedger td nu T u ->
  HilbertForwardEnergyLedger (SubspaceHilbert s) k ProjectedForwardGradient
    td nu T u.
Proof.
  intros td nu T u [E [D [GoodD [HS [HE HG]]]]].
  exists E, D, GoodD; split; [exact HS |]; split; [exact HE |].
  intros t Ht Hgood; destruct (HG t Ht Hgood) as [G [Hweak Hnorm]].
  exists G; split; [apply PROJECTED_FORWARD_KNOWN_GRADIENT; exact Hweak | exact Hnorm].
Qed.

Theorem RAW_FORWARD_SOURCE_TRANSPORT : forall tests td nu T u u0,
  RawForwardLHModel tests td nu T u u0 ->
  HilbertForwardLHModel (SubspaceHilbert s) k ProjectedForwardGradient
    tests td nu T u u0.
Proof.
  intros tests td nu T u u0 [Hnu [HT [H0 [HC [HB [HW HE]]]]]].
  split; [exact Hnu |]; split; [exact HT |]; split; [exact H0 |].
  split; [exact HC |]; split; [exact HB |]; split; [exact HW |].
  apply RAW_FORWARD_ENERGY_LEDGER_TRANSPORT; exact HE.
Qed.

Theorem RAW_FORWARD_GP_CONTAINMENT : forall
    (b : OrthonormalBasis (SubspaceHilbert s)),
  HComplete v -> forall tests td nu T g u u0,
  GPNonzero g -> RawForwardLHModel tests td nu T u u0 ->
  GPForwardLHModel (SubspaceHilbert s) k b ProjectedForwardGradient
    tests td nu T g (fun t => HGPEncode b g (u t)) (HGPEncode b g u0).
Proof.
  intros b HC tests td nu T g u u0 Hg Hu.
  apply (LHGP_FORWARD_ENCODING_CONTAINMENT (SubspaceHilbert s) k b
    (SubspaceComplete v s HC) ProjectedForwardGradient tests td nu T g u u0 Hg).
  apply RAW_FORWARD_SOURCE_TRANSPORT; exact Hu.
Qed.

End ProjectedForwardConstruction.

(* R3 specialization uses the literal full smooth tensor-test type and the
   actual derivative expression from v060. E and J still need their physical
   Lebesgue L2 interpretation; naming these maps does not supply it. *)
Section FullR3Tests.
Variables v k : HilbertData.
Variable E : R3VectorEmbedding v.
Variable J : R3TensorTest -> HCarrier k.
Hypothesis JDense : forall G eps, 0 < eps -> exists z, HDist k G (J z) < eps.

Definition R3ForwardRawDiv (z : R3TensorTest) : HCarrier v :=
  R3Embed v E (R3TensorDivergence z).

Theorem R3_FULL_TEST_FORWARD_GRADIENT_CONSTRUCTED : HComplete v ->
  exists P : HCarrier v -> HCarrier v,
  exists HP : forall x, IsOrthogonalProjection (R3TestAnnihilator v E) x (P x),
  forall u G,
    (forall z : R3TensorTest,
      - HInner v (SubspaceInclude (R3TestAnnihilator v E) u)
          (R3Embed v E (R3TensorDivergence z)) = HInner k G (J z)) ->
    WeakGradientForward (SubspaceHilbert (R3TestAnnihilator v E)) k
      (ProjectedForwardGradient v k (R3TestAnnihilator v E)
        R3TensorTest J R3ForwardRawDiv JDense P HP) u G.
Proof.
  intro HC; destruct (R3_TEST_ANNIHILATOR_PROJECTION v E HC) as [P HP].
  exists P, HP; intros u G HG.
  apply PROJECTED_FORWARD_KNOWN_GRADIENT; exact HG.
Qed.

(* One projection and one basis serve every source trajectory. The native
   conclusion concerns the literal real diagonal gp_metric completion only;
   it does not assert the infinite complex/bilateral KQ binding. *)
Theorem R3_FULL_TEST_FORWARD_CONTAINMENT : forall d,
  HComplete v -> CountablyDense v d ->
  HInfiniteDimension (SubspaceHilbert (R3TestAnnihilator v E)) ->
  exists P : HCarrier v -> HCarrier v,
  exists HP : forall x, IsOrthogonalProjection (R3TestAnnihilator v E) x (P x),
  exists b : OrthonormalBasis (SubspaceHilbert (R3TestAnnihilator v E)),
  forall tests td nu T g u u0,
    GPNonzero g ->
    RawForwardLHModel v k (R3TestAnnihilator v E) R3TensorTest
      J R3ForwardRawDiv tests td nu T u u0 ->
    GPForwardLHModel (SubspaceHilbert (R3TestAnnihilator v E)) k b
      (ProjectedForwardGradient v k (R3TestAnnihilator v E)
        R3TensorTest J R3ForwardRawDiv JDense P HP)
      tests td nu T g (fun t => HGPEncode b g (u t)) (HGPEncode b g u0) /\
    (forall t, NativeDiagonalEnergy g (HGPEncode b g (u t))
      (HNorm (SubspaceHilbert (R3TestAnnihilator v E)) (u t))) /\
    (forall w, (forall t, seq_eq (HGPEncode b g (w t)) (HGPEncode b g (u t))) ->
      forall t, w t = u t).
Proof.
  intros d HC HD HI.
  destruct (R3_TEST_ANNIHILATOR_PROJECTION v E HC) as [P HP].
  destruct (SUBSPACE_ONB_RECONSTRUCTION_FROM_AMBIENT_DENSITY v
    (R3TestAnnihilator v E) d HC HD HI) as [b Hb].
  exists P, HP, b; intros tests td nu T g u u0 Hg Hu.
  split.
  - apply RAW_FORWARD_GP_CONTAINMENT; assumption.
  - split.
    + intro t; apply NATIVE_DIAGONAL_ENERGY_VALUE_EXACT.
      apply HGP_energy_exact; [apply SubspaceComplete; exact HC | exact Hg].
    + intros w Hw t; apply (HGP_injective
        (SubspaceHilbert (R3TestAnnihilator v E)) b g); [exact Hg | apply Hw].
Qed.

End FullR3Tests.

Print Assumptions PROJECTED_FORWARD_PAIRING.
Print Assumptions PROJECTED_FORWARD_KNOWN_GRADIENT.
Print Assumptions RAW_FORWARD_GP_CONTAINMENT.
Print Assumptions R3_FULL_TEST_FORWARD_GRADIENT_CONSTRUCTED.
Print Assumptions R3_FULL_TEST_FORWARD_CONTAINMENT.
