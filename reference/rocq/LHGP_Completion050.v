From Stdlib Require Import Reals Lra Psatz.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Realization LHGP_Dual LHGP_Gradient.
Require Import LHGP_WeakTopology LHGP_PathSynthesis LHGP_Evolution LHGP_Equivalence.
Require Import LHGP_TimeBorel LHGP_BorelArithmetic LHGP_GradientPath.
Require Import LHGP_DissipationBorel LHGP_SimpleApproximation.

Open Scope R_scope.

(* This law is an explicit additional obligation on TimeData. Neither the
   name TIntegral nor TFullMeasure establishes a Lebesgue interpretation.
   The law transfers integrability and integrals between representatives
   equal on the supplied full-measure set, on every subinterval. *)
Definition AEIntegralTransport (td : TimeData) (T : R) : Prop :=
  forall (A : R -> Prop) (f g : R -> R),
    TFullMeasure td T A ->
    (forall r, InInterval T r -> A r -> f r = g r) ->
    forall s t, 0 <= s <= t -> t <= T -> TIntegrable td s t f ->
      TIntegrable td s t g /\ TIntegral td s t f = TIntegral td s t g.

Definition CanonicalGradientPath h (gm : GradientModel h)
    (u : R -> HCarrier h)
    (G : R -> HCarrier (DTarget (GDual h gm))) : Prop :=
  TotalGradientGraphPath h gm u (CanonicalFiniteGradientDomain h gm u) G.

Theorem CANONICAL_GRADIENT_EXISTS_UNIQUE : forall h (gm : GradientModel h) u,
  exists G, CanonicalGradientPath h gm u G /\
    forall K, CanonicalGradientPath h gm u K -> forall t, K t = G t.
Proof.
  intros h gm u.
  destruct (GRADIENT_PATH_FROM_POINTWISE_PROBES h gm u
    (CanonicalFiniteGradientDomain h gm u)) as [G [HG [HN [HZ HU]]]].
  - intros t Ht; apply (proj1
      (CANONICAL_FINITE_GRADIENT_DOMAIN_IFF_GRADIENT h gm u t)); exact Ht.
  - exists G; split; assumption.
Qed.

Theorem CANONICAL_GRADIENT_COORDINATES_BOREL : forall h (gm : GradientModel h)
    u G T,
  HWeakContinuous h u T -> CanonicalGradientPath h gm u G ->
  forall i, ScalarBorelOn T
    (fun t => HAnalysis (DBasis (GDual h gm)) (G t) i).
Proof.
  intros h gm u G T HC HG i.
  pose proof (GRADIENT_GRAPH_AS_TOTAL_PATH h gm u
    (CanonicalFiniteGradientDomain h gm u) G HG) as Hpath.
  pose proof (GRADIENT_PATH_COORDINATE_MASK h gm u
    (CanonicalFiniteGradientDomain h gm u)
    (fun t => HNorm (DTarget (GDual h gm)) (G t)) G Hpath) as Hmask.
  apply (SCALAR_BOREL_ZERO_PATCH T (CanonicalFiniteGradientDomain h gm u)
    (fun t => GradientProbe h gm (u t) (DTestBasis (GDual h gm) i))).
  - apply CANONICAL_FINITE_GRADIENT_DOMAIN_BOREL; exact HC.
  - apply SCALAR_CONTINUOUS_BOREL.
    eapply ScalarContinuousOn_ext with
      (f := fun t => (-1) * HInner h (u t)
        (GDiv h gm (DTestBasis (GDual h gm) i))).
    + intros t Ht; unfold GradientProbe; ring.
    + apply ScalarContinuousOn_scale; apply HC.
  - intros t Ht Ha; exact (proj1 (Hmask t i) Ha).
  - intros t Ht Ha; exact (proj2 (Hmask t i) Ha).
Qed.

Theorem CANONICAL_GRADIENT_STRONGLY_MEASURABLE : forall h (gm : GradientModel h)
    u G T,
  HWeakContinuous h u T -> CanonicalGradientPath h gm u G ->
  StronglyMeasurableOn (DTarget (GDual h gm)) T G.
Proof.
  intros h gm u G T HC HG.
  apply (HILBERT_BOREL_COORDINATES_STRONGLY_MEASURABLE
    (DTarget (GDual h gm)) (DBasis (GDual h gm))
    (DComplete (GDual h gm)) T G).
  apply CANONICAL_GRADIENT_COORDINATES_BOREL with (u := u); assumption.
Qed.

Theorem CANONICAL_GRADIENT_ENERGY_BOREL : forall h (gm : GradientModel h)
    u G T,
  HWeakContinuous h u T -> CanonicalGradientPath h gm u G ->
  ScalarBorelOn T (fun t => HNorm (DTarget (GDual h gm)) (G t)).
Proof.
  intros h gm u G T HC HG.
  apply (SCALAR_BOREL_POINTWISE_LIMIT T
    (fun n t => energy_prefix (HAnalysis (DBasis (GDual h gm)) (G t)) n)).
  - intro n; apply SCALAR_BOREL_ENERGY_PREFIX.
    apply CANONICAL_GRADIENT_COORDINATES_BOREL with (u := u); assumption.
  - intros t Ht eps Heps.
    destruct (EnergyValue_prefix_converges
      (HAnalysis (DBasis (GDual h gm)) (G t))
      (HNorm (DTarget (GDual h gm)) (G t))
      (HAnalysis_parseval (DTarget (GDual h gm)) (DBasis (GDual h gm))
        (DComplete (GDual h gm)) (G t)) eps Heps) as [N HN].
    exists N; intros n Hn; specialize (HN n Hn).
    rewrite Rabs_left1; lra.
Qed.

Theorem CANONICAL_GRADIENT_ENERGY_AGREES : forall h (gm : GradientModel h)
    u G t D,
  CanonicalGradientPath h gm u G -> GradientEnergyAt h gm (u t) D ->
  HNorm (DTarget (GDual h gm)) (G t) = D.
Proof.
  intros h gm u G t D HG [K [HK Hnorm]].
  assert (Ha : CanonicalFiniteGradientDomain h gm u t).
  { apply (proj2 (CANONICAL_FINITE_GRADIENT_DOMAIN_IFF_GRADIENT h gm u t)).
    exists K; exact HK. }
  assert (Heq : G t = K).
  { apply (ProbeRepresents_unique (GDual h gm) (GradientProbe h gm (u t)));
      [apply (proj1 (HG t)); exact Ha | exact HK]. }
  rewrite Heq; exact Hnorm.
Qed.

(* This certificate is deliberately independent of the old scalar D's
   exceptional-time values. Its canonical squared norm need only equal D
   on GoodD; the explicit AE law justifies the new integral ledger. *)
Definition MeasurableGradientEnergy h (gm : GradientModel h)
    (td : TimeData) nu T (u : R -> HCarrier h)
    (G : R -> HCarrier (DTarget (GDual h gm))) : Prop :=
  CanonicalGradientPath h gm u G /\
  StronglyMeasurableOn (DTarget (GDual h gm)) T G /\
  ScalarBorelOn T (fun t => HNorm (DTarget (GDual h gm)) (G t)) /\
  exists GoodD GoodStart : R -> Prop,
    TFullMeasure td T GoodD /\ TFullMeasure td T GoodStart /\
    (forall t, InInterval T t -> GoodD t ->
      ProbeRepresents (GDual h gm) (GradientProbe h gm (u t)) (G t)) /\
    (forall s t, 0 <= s <= t -> t <= T -> TIntegrable td s t
      (fun r => HNorm (DTarget (GDual h gm)) (G r))) /\
    RestartEnergyInequality nu T GoodStart (TIntegral td)
      (fun t => HNorm h (u t))
      (fun t => HNorm (DTarget (GDual h gm)) (G t)).

Theorem LHGP_LEDGER_MEASURABLE_GRADIENT : forall h (gm : GradientModel h)
    td nu T u,
  AEIntegralTransport td T -> HWeakContinuous h u T ->
  HilbertEnergyLedger h gm td nu T u ->
  exists G, MeasurableGradientEnergy h gm td nu T u G.
Proof.
  intros h gm td nu T u HAE HC
    [E [D [GoodD [GoodStart [HS [HE HD]]]]]].
  destruct HS as [HfullD [HfullS [Hnonneg [Hzero [Hint HR]]]]].
  destruct (CANONICAL_GRADIENT_EXISTS_UNIQUE h gm u) as [G [HG Hunique]].
  assert (Hagree : forall t, InInterval T t -> GoodD t ->
    D t = HNorm (DTarget (GDual h gm)) (G t)).
  { intros t Ht Hgood; symmetry.
    apply (CANONICAL_GRADIENT_ENERGY_AGREES h gm u G t (D t) HG).
    apply HD; assumption. }
  assert (Htransfer : forall s t, 0 <= s <= t -> t <= T ->
    TIntegrable td s t (fun r => HNorm (DTarget (GDual h gm)) (G r)) /\
    TIntegral td s t D =
      TIntegral td s t (fun r => HNorm (DTarget (GDual h gm)) (G r))).
  { intros s t Hst Ht; apply (HAE GoodD D _ HfullD Hagree s t Hst Ht).
    apply Hint; assumption. }
  exists G; split; [exact HG |]; split.
  - apply CANONICAL_GRADIENT_STRONGLY_MEASURABLE with (u := u); assumption.
  - split.
    + apply CANONICAL_GRADIENT_ENERGY_BOREL with (u := u); assumption.
    + exists GoodD, GoodStart; split; [exact HfullD |]; split; [exact HfullS |].
      split.
      * intros t Ht Hgood; apply (proj1 (HG t)).
        apply (proj2 (CANONICAL_FINITE_GRADIENT_DOMAIN_IFF_ENERGY_VALUE h gm u t)).
        exists (D t); apply HD; assumption.
      * split.
        -- intros s t Hst Ht; exact (proj1 (Htransfer s t Hst Ht)).
        -- intros s t Hst Ht Hstart.
           pose proof (HR s t Hst Ht Hstart) as Hr.
           rewrite (HE t), (HE s), (proj2 (Htransfer s t Hst Ht)) in Hr.
           exact Hr.
Qed.

Theorem LHGP_HILBERT_MEASURABLE_GRADIENT : forall h gm tests td nu T u u0,
  AEIntegralTransport td T -> HilbertLHModel h gm tests td nu T u u0 ->
  exists G, MeasurableGradientEnergy h gm td nu T u G.
Proof.
  intros h gm tests td nu T u u0 HAE
    [Hnu [HT [H0 [HC [HB [HW HL]]]]]].
  apply LHGP_LEDGER_MEASURABLE_GRADIENT; assumption.
Qed.

(* The equivalence retains the independently stated v030 classes and adds
   a derived measurable gradient on the Hilbert side. No new premise about
   the particular trajectory or an already measurable gradient is added. *)
Theorem LHGP_STRONGLY_MEASURABLE_TRAJECTORY_EQUIVALENCE :
  forall h (b : OrthonormalBasis h), HComplete h ->
  forall gm tests td nu T g, GPNonzero g -> AEIntegralTransport td T ->
  forall p u0,
  (GPLHModel h b gm tests td nu T g p (HGPEncode b g u0) <->
   exists u G,
    HilbertLHModel h gm tests td nu T u u0 /\
    HGPPathRealizes h b g u p /\
    MeasurableGradientEnergy h gm td nu T u G /\
    (forall v, HGPPathRealizes h b g v p -> forall t, v t = u t)).
Proof.
  intros h b Hcomplete gm tests td nu T g Hg HAE p u0; split.
  - intro HP.
    destruct (proj1 (LHGP_TRAJECTORY_EQUIVALENCE h b Hcomplete gm tests td
      nu T g Hg p u0) HP) as [u [HL [Hu HU]]].
    destruct (LHGP_HILBERT_MEASURABLE_GRADIENT h gm tests td nu T u u0 HAE HL)
      as [G HG].
    exists u, G; exact (conj HL (conj Hu (conj HG HU))).
  - intros [u [G [HL [Hu [HG HU]]]]].
    apply (proj2 (LHGP_TRAJECTORY_EQUIVALENCE h b Hcomplete gm tests td
      nu T g Hg p u0)); exists u; exact (conj HL (conj Hu HU)).
Qed.

Print Assumptions CANONICAL_GRADIENT_EXISTS_UNIQUE.
Print Assumptions CANONICAL_GRADIENT_STRONGLY_MEASURABLE.
Print Assumptions CANONICAL_GRADIENT_ENERGY_BOREL.
Print Assumptions LHGP_LEDGER_MEASURABLE_GRADIENT.
Print Assumptions LHGP_STRONGLY_MEASURABLE_TRAJECTORY_EQUIVALENCE.
