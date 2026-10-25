From Stdlib Require Import Reals Lra Psatz.
Require Import LHGP_Coordinates LHGP_Readouts.

Open Scope R_scope.

(* This module transports coefficient trajectories and scalar energy ledgers.
   Time integrals and the good-start set are explicit data. No Lebesgue
   interpretation, full-measure assertion, or physical NSE realization is
   silently attached to these data. *)

Definition CoefficientPath := R -> Seq.
Definition path_eq (a b : CoefficientPath) : Prop :=
  forall t i, a t i = b t i.
Definition encode_path (g : Seq) (a : CoefficientPath) : CoefficientPath :=
  fun t => encode g (a t).
Definition decode_path (g : Seq) (p : CoefficientPath) : CoefficientPath :=
  fun t => decode g (p t).

Lemma path_decode_encode : forall g, GPNonzero g -> forall a,
  path_eq (decode_path g (encode_path g a)) a.
Proof.
  intros g Hg a t i.
  unfold decode_path, encode_path, decode, encode.
  field. apply Hg.
Qed.

Lemma path_encode_decode : forall g, GPNonzero g -> forall p,
  path_eq (encode_path g (decode_path g p)) p.
Proof.
  intros g Hg p t i.
  unfold decode_path, encode_path, decode, encode.
  field. apply Hg.
Qed.

Lemma path_encoding_injective : forall g, GPNonzero g -> forall a b,
  path_eq (encode_path g a) (encode_path g b) -> path_eq a b.
Proof.
  intros g Hg a b H t i.
  specialize (H t i).
  unfold encode_path, encode in H.
  apply (Rmult_eq_reg_l (g i)); [exact H | apply Hg].
Qed.

(* Local extensionality proofs avoid functional extensionality for paths. *)
Lemma transport_prefix_ext : forall f h,
  seq_eq f h -> forall n, prefix f n = prefix h n.
Proof.
  intros f h H n; induction n as [|n IH]; simpl; [reflexivity|].
  rewrite IH, (H n). reflexivity.
Qed.

Lemma transport_energy_ext : forall a b,
  seq_eq a b -> forall n, energy_prefix a n = energy_prefix b n.
Proof.
  intros a b H n. unfold energy_prefix.
  apply transport_prefix_ext. intro i. rewrite (H i). reflexivity.
Qed.

Definition UniformEnergyBound (a : CoefficientPath) (T B : R) : Prop :=
  forall t, 0 <= t <= T -> forall n, energy_prefix (a t) n <= B.

Definition GPEnergyBound g p T B :=
  UniformEnergyBound (decode_path g p) T B.

Lemma uniform_energy_ext : forall a b T B,
  path_eq a b -> (UniformEnergyBound a T B <-> UniformEnergyBound b T B).
Proof.
  intros a b T B H. unfold UniformEnergyBound.
  split; intros HB t Ht n.
  - rewrite <- (transport_energy_ext (a t) (b t) (H t) n). apply HB; exact Ht.
  - rewrite (transport_energy_ext (a t) (b t) (H t) n). apply HB; exact Ht.
Qed.

Theorem LHGP_UNIFORM_ENERGY_SAME_BOUND : forall g,
  GPNonzero g -> forall a T B,
  GPEnergyBound g (encode_path g a) T B <-> UniformEnergyBound a T B.
Proof.
  intros g Hg a T B. unfold GPEnergyBound.
  apply uniform_energy_ext. apply path_decode_encode; exact Hg.
Qed.

Definition EnergyTrace (a : CoefficientPath) (E : R -> R) : Prop :=
  forall t, EnergyValue (a t) (E t).

Definition GPEnergyTrace g p E := EnergyTrace (decode_path g p) E.

Lemma energy_value_ext_for_transport : forall a b E,
  seq_eq a b -> (EnergyValue a E <-> EnergyValue b E).
Proof.
  intros a b E H. unfold EnergyValue.
  split; intros [HU HL]; split.
  - intro n. rewrite <- (transport_energy_ext a b H n). apply HU.
  - intros B HB. apply HL. intro n. rewrite (transport_energy_ext a b H n). apply HB.
  - intro n. rewrite (transport_energy_ext a b H n). apply HU.
  - intros B HB. apply HL. intro n. rewrite <- (transport_energy_ext a b H n). apply HB.
Qed.

Theorem LHGP_ENERGY_TRACE_EXACT : forall g,
  GPNonzero g -> forall a E,
  GPEnergyTrace g (encode_path g a) E <-> EnergyTrace a E.
Proof.
  intros g Hg a E. unfold GPEnergyTrace, EnergyTrace.
  split; intros H t.
  - apply (proj1 (energy_value_ext_for_transport
      (decode_path g (encode_path g a) t) (a t) (E t)
      (path_decode_encode g Hg a t))). apply H.
  - apply (proj2 (energy_value_ext_for_transport
      (decode_path g (encode_path g a) t) (a t) (E t)
      (path_decode_encode g Hg a t))). apply H.
Qed.

Definition coefficient_difference (a b : Seq) : Seq := fun i => a i - b i.

(* A squared-l2 initial trace, expressed entirely by all finite prefixes.
   The bound is uniform in the prefix; pointwise coordinate convergence alone
   would not suffice. *)
Definition StrongInitialTrace (a : CoefficientPath) (a0 : Seq) : Prop :=
  forall eps, 0 < eps -> exists delta, 0 < delta /\
    forall t, 0 <= t < delta -> forall n,
      energy_prefix (coefficient_difference (a t) a0) n < eps.

Definition GPStrongInitialTrace g p p0 :=
  StrongInitialTrace (decode_path g p) (decode g p0).

Lemma strong_trace_ext : forall a b a0 b0,
  path_eq a b -> seq_eq a0 b0 ->
  (StrongInitialTrace a a0 <-> StrongInitialTrace b b0).
Proof.
  intros a b a0 b0 H H0.
  assert (Hd : forall t n,
    energy_prefix (coefficient_difference (a t) a0) n =
    energy_prefix (coefficient_difference (b t) b0) n).
  { intros t n. apply transport_energy_ext. intro i.
    unfold coefficient_difference. rewrite (H t i), (H0 i). reflexivity. }
  unfold StrongInitialTrace. split; intros HC eps Heps;
    destruct (HC eps Heps) as [delta [Hdelta HB]];
    exists delta; split; [exact Hdelta | | exact Hdelta |].
  - intros t Ht n. rewrite <- (Hd t n). apply HB; exact Ht.
  - intros t Ht n. rewrite (Hd t n). apply HB; exact Ht.
Qed.

Theorem LHGP_STRONG_INITIAL_TRACE_EXACT : forall g,
  GPNonzero g -> forall a a0,
  GPStrongInitialTrace g (encode_path g a) (encode g a0) <->
  StrongInitialTrace a a0.
Proof.
  intros g Hg a a0. unfold GPStrongInitialTrace.
  apply strong_trace_ext.
  - apply path_decode_encode; exact Hg.
  - intro i. unfold decode, encode. field. apply Hg.
Qed.

Definition TimeIntegral := R -> R -> (R -> R) -> R.

Definition RestartEnergyInequality (nu T : R) (GoodStart : R -> Prop)
  (I : TimeIntegral) (E D : R -> R) : Prop :=
  forall s t, 0 <= s <= t -> t <= T -> (s = 0 \/ GoodStart s) ->
    E t + 2 * nu * I s t D <= E s.

Definition energy_defect (nu : R) (I : TimeIntegral)
  (E D : R -> R) (s t : R) := E s - E t - 2 * nu * I s t D.

Theorem LHGP_DEFECT_NONNEGATIVE_IFF_ENERGY_INEQUALITY :
  forall nu T GoodStart I E D,
  RestartEnergyInequality nu T GoodStart I E D <->
  (forall s t, 0 <= s <= t -> t <= T -> (s = 0 \/ GoodStart s) ->
    0 <= energy_defect nu I E D s t).
Proof.
  intros nu T GoodStart I E D.
  unfold RestartEnergyInequality, energy_defect.
  split; intros H s t Hst Ht Hs; specialize (H s t Hst Ht Hs); lra.
Qed.

Theorem LHGP_INITIAL_DISSIPATION_BUDGET : forall nu T GoodStart I a E D t,
  0 < nu -> EnergyTrace a E ->
  RestartEnergyInequality nu T GoodStart I E D ->
  0 <= t <= T -> 2 * nu * I 0 t D <= E 0.
Proof.
  intros nu T GoodStart I a E D t Hnu HE HI Ht.
  assert (HEt : 0 <= E t).
  { destruct (HE t) as [HU HL]. specialize (HU O).
    change (0 <= E t) in HU. exact HU. }
  specialize (HI 0 t). assert (Hs : 0 <= 0 <= t) by lra.
  specialize (HI Hs (proj2 Ht) (or_introl eq_refl)). lra.
Qed.

Definition CoefficientEnergyLedger (a : CoefficientPath)
  (nu T : R) (GoodStart : R -> Prop) (I : TimeIntegral) (E D : R -> R) :=
  EnergyTrace a E /\ RestartEnergyInequality nu T GoodStart I E D.

Definition GPEnergyLedger g p nu T GoodStart I E D :=
  GPEnergyTrace g p E /\ RestartEnergyInequality nu T GoodStart I E D.

Theorem LHGP_RESTART_LEDGER_EXACT : forall g,
  GPNonzero g -> forall a nu T GoodStart I E D,
  GPEnergyLedger g (encode_path g a) nu T GoodStart I E D <->
  CoefficientEnergyLedger a nu T GoodStart I E D.
Proof.
  intros g Hg a nu T GoodStart I E D.
  unfold GPEnergyLedger, CoefficientEnergyLedger.
  rewrite (LHGP_ENERGY_TRACE_EXACT g Hg a E). reflexivity.
Qed.

(* The coefficients of the time/Laplacian tests and the quadratic convection
   kernel are supplied explicitly. This is the weak-readout identity, before
   identifying its profiles and scalar integral with physical test functions
   and Lebesgue integration. Convergence of every readout is required. *)
Section WeakReadout.
  Context {Test : Type}.
  Variable time_profile : Test -> R -> Seq.
  Variable laplacian_profile : Test -> R -> Seq.
  Variable initial_profile : Test -> Seq.
  Variable convection_kernel : Test -> R -> nat -> nat -> R.
  Variable integrate_time : (R -> R) -> R.
  Variable viscosity : R.

  Definition WeakReadoutIdentity (a : CoefficientPath) (a0 : Seq) : Prop :=
    forall test, exists lt lv nl : R -> R, exists initial : R,
      (forall t, linear_limit (a t) (time_profile test t) (lt t)) /\
      (forall t, linear_limit (a t) (laplacian_profile test t) (lv t)) /\
      (forall t, quadratic_limit (a t) (convection_kernel test t) (nl t)) /\
      linear_limit a0 (initial_profile test) initial /\
      integrate_time lt + viscosity * integrate_time lv +
        integrate_time nl + initial = 0.

  Lemma weak_readout_morphism : forall a b a0 b0,
    path_eq a b -> seq_eq a0 b0 ->
    WeakReadoutIdentity a a0 -> WeakReadoutIdentity b b0.
  Proof.
    intros a b a0 b0 H H0 HW test.
    destruct (HW test) as [lt [lv [nl [initial [Ht [Hv [Hn [Hi Hb]]]]]]]].
    exists lt, lv, nl, initial. split.
    - intro t. apply (proj1 (linear_limit_ext (a t) (b t)
        (time_profile test t) (lt t) (H t))). apply Ht.
    - split.
      + intro t. apply (proj1 (linear_limit_ext (a t) (b t)
          (laplacian_profile test t) (lv t) (H t))). apply Hv.
      + split.
        * intro t. apply (proj1 (quadratic_limit_ext (a t) (b t)
            (convection_kernel test t) (nl t) (H t))). apply Hn.
        * split.
          -- apply (proj1 (linear_limit_ext a0 b0
               (initial_profile test) initial H0)). exact Hi.
          -- exact Hb.
  Qed.

  Lemma weak_readout_ext : forall a b a0 b0,
    path_eq a b -> seq_eq a0 b0 ->
    (WeakReadoutIdentity a a0 <-> WeakReadoutIdentity b b0).
  Proof.
    intros a b a0 b0 H H0. split.
    - apply weak_readout_morphism; assumption.
    - apply weak_readout_morphism.
      + intros t i. symmetry. apply H.
      + intro i. symmetry. apply H0.
  Qed.

  Definition GPWeakReadoutIdentity g p p0 :=
    WeakReadoutIdentity (decode_path g p) (decode g p0).

  Theorem LHGP_WEAK_READOUT_IDENTITY_EXACT : forall g,
    GPNonzero g -> forall a a0,
    GPWeakReadoutIdentity g (encode_path g a) (encode g a0) <->
    WeakReadoutIdentity a a0.
  Proof.
    intros g Hg a a0. unfold GPWeakReadoutIdentity.
    apply weak_readout_ext.
    - apply path_decode_encode; exact Hg.
    - apply decode_encode; exact Hg.
  Qed.
End WeakReadout.

(* A reusable theorem for any coefficient-path property, including a future
   concrete weak-NSE predicate. Its extensionality is an explicit premise.
   This does not itself identify a coefficient predicate with physical LH. *)
Definition PathPropertyExtensional (C : CoefficientPath -> Prop) :=
  forall a b, path_eq a b -> (C a <-> C b).

Definition GPImageProperty (g : Seq) (C : CoefficientPath -> Prop)
  (p : CoefficientPath) :=
  exists a, C a /\ path_eq (encode_path g a) p.

Theorem LHGP_IMAGE_IFF_DECODED_PROPERTY : forall g,
  GPNonzero g -> forall C,
  PathPropertyExtensional C -> forall p,
  GPImageProperty g C p <-> C (decode_path g p).
Proof.
  intros g Hg C HC p. split.
  - intros [a [Ha Henc]].
    assert (Hdec : path_eq a (decode_path g p)).
    { intros t i. unfold decode_path, decode.
      rewrite <- (Henc t i). unfold encode_path, encode.
      field. apply Hg. }
    apply (proj1 (HC a (decode_path g p) Hdec)). exact Ha.
  - intro H. exists (decode_path g p). split; [exact H |].
    apply path_encode_decode; exact Hg.
Qed.

Theorem LHGP_ENCODING_PRESERVES_ANY_EXTENSIONAL_PROPERTY : forall g,
  GPNonzero g -> forall C,
  PathPropertyExtensional C -> forall a,
  GPImageProperty g C (encode_path g a) <-> C a.
Proof.
  intros g Hg C HC a.
  rewrite (LHGP_IMAGE_IFF_DECODED_PROPERTY g Hg C HC).
  apply HC. apply path_decode_encode; exact Hg.
Qed.
