From Stdlib Require Import Reals Lra Psatz Lia List Classical_Prop Field.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.
Require Import LHGP_TimeBorel LHGP_Quantization.

Import ListNotations.
Open Scope R_scope.

(* Simple means an actual finite range and Borel inverse images of every
   value. Strong measurability is proved by explicit simple approximants,
   not installed as a model field or inferred by an assumed Pettis theorem. *)
Definition FiniteBorelOn (A : Type) (T : R) (f : R -> A) : Prop :=
  (exists values : list A,
    forall t, InInterval T t -> In (f t) values) /\
  (forall v, TimeBorel T (fun t => f t = v)).

Definition HSimpleOn (h : HilbertData) (T : R)
    (f : R -> HCarrier h) : Prop := FiniteBorelOn (HCarrier h) T f.

Definition StronglyMeasurableOn (h : HilbertData) (T : R)
    (f : R -> HCarrier h) : Prop :=
  exists s : nat -> R -> HCarrier h,
    (forall n, HSimpleOn h T (s n)) /\
    (forall t, InInterval T t -> HConverges h (fun n => s n t) (f t)).

Lemma TimeBorel_constant_predicate : forall T (P : Prop),
  TimeBorel T (fun _ => P).
Proof.
  intros T P; destruct (classic P) as [HP | Hnot].
  - eapply TB_ext with (A := fun _ => True); [apply TimeBorel_all |].
    intros t Ht; tauto.
  - eapply TB_ext with (A := fun _ => False); [apply TimeBorel_empty |].
    intros t Ht; tauto.
Qed.

Lemma TimeBorel_finite_exists : forall (A : Type) T (values : list A)
    (P : A -> R -> Prop),
  (forall v, In v values -> TimeBorel T (P v)) ->
  TimeBorel T (fun t => exists v, In v values /\ P v t).
Proof.
  intros A T values; induction values as [|a values IH]; intros P HP.
  - eapply TB_ext with (A := fun _ => False); [apply TimeBorel_empty |].
    intros t Ht; split; [tauto | intros [v [Hv _]]; contradiction].
  - eapply TB_ext with
      (A := fun t => P a t \/ exists v, In v values /\ P v t).
    + apply TimeBorel_union.
      * apply HP; left; reflexivity.
      * apply IH; intros v Hv; apply HP; right; exact Hv.
    + intros t Ht; simpl; split.
      * intros [Ha | [v [Hv HPv]]].
        -- exists a; split; [left; reflexivity | exact Ha].
        -- exists v; split; [right; exact Hv | exact HPv].
      * intros [v [[Heq | Hv] HPv]].
        -- subst v; left; exact HPv.
        -- right; exists v; split; assumption.
Qed.

Lemma FiniteBorelOn_constant : forall (A : Type) T (a : A),
  FiniteBorelOn A T (fun _ => a).
Proof.
  intros A T a; split.
  - exists [a]; intros t Ht; left; reflexivity.
  - intro v; apply TimeBorel_constant_predicate.
Qed.

Lemma FiniteBorelOn_binary : forall (A B C : Type) T
    (F : A -> B -> C) (f : R -> A) (g : R -> B),
  FiniteBorelOn A T f -> FiniteBorelOn B T g ->
  FiniteBorelOn C T (fun t => F (f t) (g t)).
Proof.
  intros A B C T F f g [[xs Hx] Hf] [[ys Hy] Hg]; split.
  - exists (flat_map (fun x => map (F x) ys) xs).
    intros t Ht; apply in_flat_map.
    exists (f t); split; [apply Hx; exact Ht |].
    apply in_map; apply Hy; exact Ht.
  - intro v; eapply TB_ext with (A := fun t => exists x, In x xs /\
      exists y, In y ys /\ (f t = x /\ g t = y /\ F x y = v)).
    + apply TimeBorel_finite_exists; intros x Hxin.
      apply TimeBorel_finite_exists; intros y Hyin.
      apply TimeBorel_intersection; [apply Hf |].
      apply TimeBorel_intersection; [apply Hg |].
      apply TimeBorel_constant_predicate.
    + intros t Ht; split.
      * intros [x [_ [y [_ [Hfx [Hgy HF]]]]]].
        rewrite Hfx, Hgy; exact HF.
      * intro HF; exists (f t); split; [apply Hx; exact Ht |].
        exists (g t); split; [apply Hy; exact Ht |].
        repeat split; assumption.
Qed.

Lemma FiniteBorelOn_map : forall (A B : Type) T
    (F : A -> B) (f : R -> A),
  FiniteBorelOn A T f -> FiniteBorelOn B T (fun t => F (f t)).
Proof.
  intros A B T F f Hf.
  exact (FiniteBorelOn_binary A unit B T (fun a _ => F a) f
    (fun _ => tt) Hf (FiniteBorelOn_constant unit T tt)).
Qed.

Lemma HFINITE_DISTANCE_DECOMPOSITION : forall h (b : OrthonormalBasis h) x a n,
  HDist h (HFinite b a n) x =
    energy_prefix (fun i => a i - HAnalysis b x i) n +
    HDist h (HFinite b (HAnalysis b x) n) x.
Proof.
  intros h b x a n.
  rewrite (HDist_sym h (HFinite b (HAnalysis b x) n) x), HAnalysis_residual.
  unfold HDist; rewrite HFinite_norm, HFinite_inner.
  unfold energy_prefix, HAnalysis.
  assert (Hprefix : prefix (fun i => a i * a i) n -
    2 * prefix (fun i => a i * HInner h (HBasis h b i) x) n =
    prefix (fun i => (a i - HInner h x (HBasis h b i)) *
      (a i - HInner h x (HBasis h b i))) n -
    prefix (fun i => HInner h x (HBasis h b i) *
      HInner h x (HBasis h b i)) n).
  { induction n as [|n IH]; simpl; [ring |].
    rewrite (HInner_sym h (HBasis h b n) x); nra. }
  lra.
Qed.

Lemma HAnalysis_uniform_bound : forall h (b : OrthonormalBasis h) x i,
  Rabs (HAnalysis b x i) <= HNorm h x + 1.
Proof.
  intros h b x i.
  pose proof (HInner_cauchy_schwarz h x (HBasis h b i)) as Hcs.
  rewrite HBasis_norm in Hcs.
  pose proof (HNorm_nonnegative h x) as Hpos.
  unfold HAnalysis; apply Rabs_le; split; nra.
Qed.

Definition HQuantizedApproximation (h : HilbertData) (b : OrthonormalBasis h)
    (f : R -> HCarrier h) (m : nat) (t : R) : HCarrier h :=
  HFinite b (fun i => Quantize m (HAnalysis b (f t) i)) (S m).

Lemma QuantFiber_TimeBorel : forall T f m k,
  ScalarBorelOn T f -> TimeBorel T (fun t => QuantFiber m k (f t)).
Proof.
  intros T f m k Hf; unfold QuantFiber.
  apply TimeBorel_union.
  - apply TimeBorel_intersection.
    + apply TimeBorel_constant_predicate.
    + apply Hf.
  - apply TimeBorel_union.
    + apply TimeBorel_intersection.
      * apply TimeBorel_constant_predicate.
      * apply TimeBorel_scalar_ge; exact Hf.
    + apply TimeBorel_intersection.
      * apply TimeBorel_constant_predicate.
      * apply TimeBorel_intersection.
        -- apply TimeBorel_scalar_ge; exact Hf.
        -- apply Hf.
Qed.

Theorem QUANTIZED_SCALAR_SIMPLE : forall T f m,
  ScalarBorelOn T f -> FiniteBorelOn R T (fun t => Quantize m (f t)).
Proof.
  intros T f m Hf; split.
  - exists (QuantValues m); intros t Ht; apply QUANTIZE_IN_VALUES.
  - intro v; destruct (classic (exists k : Z, v = IZR k / QuantDen m))
      as [[k Hk] | Hnot].
    + subst v; eapply TB_ext with (A := fun t => QuantFiber m k (f t)).
      * apply QuantFiber_TimeBorel; exact Hf.
      * intros t Ht; symmetry; apply QUANTIZE_VALUE_FIBER.
    + eapply TB_ext with (A := fun _ => False); [apply TimeBorel_empty |].
      intros t Ht; split; [tauto |].
      intro Hq; apply Hnot; exists (QuantIndex m (f t)).
      rewrite <- Hq; reflexivity.
Qed.

Theorem HFINITE_SIMPLE : forall h (b : OrthonormalBasis h) T a n,
  (forall i, FiniteBorelOn R T (fun t => a t i)) ->
  HSimpleOn h T (fun t => HFinite b (a t) n).
Proof.
  intros h b T a n Ha; unfold HSimpleOn; induction n as [|n IH]; simpl.
  - apply FiniteBorelOn_constant.
  - apply FiniteBorelOn_binary; [exact IH |].
    exact (FiniteBorelOn_map R (HCarrier h) T
      (fun r => HScale h r (HBasis h b n)) (fun t => a t n) (Ha n)).
Qed.

Theorem HQUANTIZED_APPROXIMATION_SIMPLE : forall h (b : OrthonormalBasis h) T f m,
  (forall i, ScalarBorelOn T (fun t => HAnalysis b (f t) i)) ->
  HSimpleOn h T (HQuantizedApproximation h b f m).
Proof.
  intros h b T f m Hf; unfold HQuantizedApproximation.
  apply HFINITE_SIMPLE; intro i; apply QUANTIZED_SCALAR_SIMPLE; apply Hf.
Qed.

Lemma energy_prefix_uniform_bound : forall a n C,
  (forall i, (i < n)%nat -> a i * a i <= C) ->
  energy_prefix a n <= INR n * C.
Proof.
  intros a n C; induction n as [|n IH]; intro Ha.
  - unfold energy_prefix; simpl; lra.
  - assert (Hprev : forall i, (i < n)%nat -> a i * a i <= C).
    { intros i Hi; apply Ha; lia. }
    specialize (IH Hprev); specialize (Ha n ltac:(lia)).
    unfold energy_prefix in *; simpl prefix; rewrite S_INR; nra.
Qed.

Theorem HQUANTIZED_APPROXIMATION_ERROR : forall h (b : OrthonormalBasis h) f m t,
  HNorm h (f t) + 1 <= QuantDen m ->
  HDist h (HQuantizedApproximation h b f m t) (f t) <=
    1 / QuantDen m +
    HDist h (HFinite b (HAnalysis b (f t)) (S m)) (f t).
Proof.
  intros h b f m t Hbound; unfold HQuantizedApproximation.
  rewrite HFINITE_DISTANCE_DECOMPOSITION.
  assert (Herr : energy_prefix
    (fun i => Quantize m (HAnalysis b (f t) i) - HAnalysis b (f t) i) (S m)
    <= INR (S m) * ((1 / QuantDen m) * (1 / QuantDen m))).
  { apply energy_prefix_uniform_bound; intros i Hi.
    apply QUANTIZE_SQUARE_ERROR.
    eapply Rle_trans; [apply HAnalysis_uniform_bound | exact Hbound]. }
  assert (Hcancel : INR (S m) * ((1 / QuantDen m) * (1 / QuantDen m))
    = 1 / QuantDen m).
  { change (QuantDen m * ((1 / QuantDen m) * (1 / QuantDen m)) = 1 / QuantDen m).
    field; pose proof (QuantDen_positive m); lra. }
  rewrite Hcancel in Herr; lra.
Qed.

Theorem HQUANTIZED_APPROXIMATION_CONVERGES : forall h (b : OrthonormalBasis h),
  HComplete h -> forall f t,
  HConverges h (fun m => HQuantizedApproximation h b f m t) (f t).
Proof.
  intros h b Hcomplete f t eps Heps.
  destruct (HAnalysis_reconstruction h b Hcomplete (f t) (eps / 2) ltac:(lra))
    as [Nr HNr].
  destruct (INR_unbounded (HNorm h (f t) + 1)) as [Nb HNb].
  destruct (TimeGap_arbitrarily_small (eps / 2) ltac:(lra)) as [Ne HNe].
  exists (Nat.max Nr (Nat.max Nb Ne)); intros m Hm.
  assert (Hrec : HDist h (HFinite b (HAnalysis b (f t)) (S m)) (f t) < eps / 2).
  { apply HNr; lia. }
  assert (Hbound : HNorm h (f t) + 1 <= QuantDen m).
  { unfold QuantDen; pose proof (le_INR Nb (S m) ltac:(lia)); lra. }
  pose proof (HQUANTIZED_APPROXIMATION_ERROR h b f m t Hbound) as Herr.
  assert (Hgap : 1 / QuantDen m <= TimeGap Ne).
  { unfold QuantDen, TimeGap; unfold Rdiv; rewrite Rmult_1_l.
    apply Rinv_le_contravar; [apply lt_0_INR; lia | apply le_INR; lia]. }
  lra.
Qed.

Theorem HILBERT_BOREL_COORDINATES_STRONGLY_MEASURABLE :
  forall h (b : OrthonormalBasis h), HComplete h -> forall T f,
  (forall i, ScalarBorelOn T (fun t => HAnalysis b (f t) i)) ->
  StronglyMeasurableOn h T f.
Proof.
  intros h b Hcomplete T f Hf.
  exists (HQuantizedApproximation h b f); split.
  - intro m; apply HQUANTIZED_APPROXIMATION_SIMPLE; exact Hf.
  - intros t Ht; apply HQUANTIZED_APPROXIMATION_CONVERGES; exact Hcomplete.
Qed.

Print Assumptions HFINITE_DISTANCE_DECOMPOSITION.
Print Assumptions QUANTIZED_SCALAR_SIMPLE.
Print Assumptions HQUANTIZED_APPROXIMATION_ERROR.
Print Assumptions HQUANTIZED_APPROXIMATION_CONVERGES.
Print Assumptions HILBERT_BOREL_COORDINATES_STRONGLY_MEASURABLE.
