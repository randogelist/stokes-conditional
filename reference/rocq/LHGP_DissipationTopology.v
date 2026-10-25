From Stdlib Require Import Reals Lra Psatz Lia Arith.Compare_dec.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.
Require Import LHGP_Dual LHGP_Gradient LHGP_WeakTopology.

Open Scope R_scope.

(* Finite sublevels are meaningful even before a finite dissipation value
   has been proved to exist. The dual representation theorem subsequently
   constructs a gradient from any such finite sublevel. Weak closedness
   below is proved from the individual divergence probes, not assumed as
   an extra field of GradientModel. *)

Definition HWeakSequential (h : HilbertData)
  (u : nat -> HCarrier h) (x : HCarrier h) : Prop :=
  forall y, SeqLimit (fun n => HInner h (u n) y) (HInner h x y).

Definition DissipationSublevel h (gm : GradientModel h)
  (x : HCarrier h) (M : R) : Prop :=
  VarUpper (GDual h gm) (GradientProbe h gm x) M.

Definition InfiniteDissipation h (gm : GradientModel h) (x : HCarrier h) : Prop :=
  forall M, ~ DissipationSublevel h gm x M.

Lemma SeqLimit_affine : forall f l c d,
  SeqLimit f l -> SeqLimit (fun n => c * f n + d) (c * l + d).
Proof.
  intros f l c d Hlim eps Heps.
  pose proof (Rabs_pos c) as Hc.
  assert (Hdenom : 0 < Rabs c + 1) by lra.
  assert (Hsmall : 0 < eps / (Rabs c + 1)).
  { apply Rdiv_lt_0_compat; assumption. }
  destruct (Hlim _ Hsmall) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  replace (c * f n + d - (c * l + d)) with (c * (f n - l)) by ring.
  rewrite Rabs_mult.
  assert (Hproduct : Rabs (f n - l) * (Rabs c + 1) < eps).
  { assert (Hm : Rabs (f n - l) * (Rabs c + 1) <
      (eps / (Rabs c + 1)) * (Rabs c + 1)).
    { apply Rmult_lt_compat_r; assumption. }
    replace ((eps / (Rabs c + 1)) * (Rabs c + 1)) with eps in Hm
      by (field; lra).
    exact Hm. }
  pose proof (Rabs_pos (f n - l)). nra.
Qed.

Lemma SeqLimit_neg : forall f l,
  SeqLimit f l -> SeqLimit (fun n => - f n) (- l).
Proof.
  intros f l Hlim eps Heps.
  destruct (Hlim eps Heps) as [N HN].
  exists N. intros n Hn.
  replace (- f n - - l) with (- (f n - l)) by ring.
  rewrite Rabs_Ropp. apply HN. exact Hn.
Qed.

(* Arbitrarily late approximate upper bounds suffice; no globally bounded
   sequence or finite limit inferior is postulated by this definition. *)
Lemma SeqLimit_upper_frequent : forall f l M,
  SeqLimit f l ->
  (forall eps, 0 < eps -> forall N : nat,
    exists n, (N <= n)%nat /\ f n <= M + eps) ->
  l <= M.
Proof.
  intros f l M Hlim Hfrequent.
  destruct (Rle_dec l M) as [Hle | Hnot]; [exact Hle |].
  assert (Heps : 0 < (l - M) / 3) by lra.
  destruct (Hlim _ Heps) as [N HN].
  destruct (Hfrequent _ Heps N) as [n [Hn Hbound]].
  specialize (HN n Hn).
  destruct (Rabs_def2 _ _ HN) as [Hupper Hlower]. lra.
Qed.

Lemma SeqLimit_upper_eventual : forall f l M,
  SeqLimit f l ->
  (exists N, forall n, (N <= n)%nat -> f n <= M) ->
  l <= M.
Proof.
  intros f l M Hlim [N0 Hbound].
  eapply SeqLimit_upper_frequent; [exact Hlim |].
  intros eps Heps N. exists (Nat.max N N0). split; [lia |].
  specialize (Hbound (Nat.max N N0) ltac:(lia)). lra.
Qed.

Theorem HStrongSequential_to_weak : forall h u x,
  HConverges h u x -> HWeakSequential h u x.
Proof.
  intros h u x Hstrong y eps Heps.
  pose proof (HNorm_nonnegative h y) as Hy.
  assert (Hdenom : 0 < HNorm h y + 1) by lra.
  assert (Hdelta : 0 < eps * eps / (HNorm h y + 1)).
  { apply Rdiv_lt_0_compat; [nra | exact Hdenom]. }
  destruct (Hstrong _ Hdelta) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  pose proof (HInner_distance_bound h (u n) x y) as Hbound.
  pose proof (HDist_nonnegative h (u n) x) as Hd.
  assert (Hproduct : HDist h (u n) x * (HNorm h y + 1) < eps * eps).
  { assert (Hm : HDist h (u n) x * (HNorm h y + 1) <
      (eps * eps / (HNorm h y + 1)) * (HNorm h y + 1)).
    { apply Rmult_lt_compat_r; assumption. }
    replace ((eps * eps / (HNorm h y + 1)) * (HNorm h y + 1))
      with (eps * eps) in Hm by (field; lra).
    exact Hm. }
  apply Rabs_def1; nra.
Qed.

Theorem DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND : forall h
  (gm : GradientModel h) x M,
  (DissipationSublevel h gm x M <->
   exists G : HCarrier (DTarget (GDual h gm)),
     ProbeRepresents (GDual h gm) (GradientProbe h gm x) G /\
     HNorm (DTarget (GDual h gm)) G <= M).
Proof.
  intros h gm x M. split.
  - intro HU.
    pose proof (GRADIENT_PROBE_LINEAR h gm x) as Hlinear.
    destruct (VarUpper_representation (GDual h gm) (GradientProbe h gm x)
      M Hlinear HU) as [G HG].
    exists G. split; [exact HG |].
    destruct (ProbeRepresents_value (GDual h gm) (GradientProbe h gm x)
      G Hlinear HG) as [_ Hleast].
    apply Hleast. exact HU.
  - intros [G [HG Hnorm]] z.
    pose proof (ProbeRepresents_upper (GDual h gm) (GradientProbe h gm x)
      G HG z) as Hupper.
    lra.
Qed.

Theorem DISSIPATION_INFINITE_IFF_NO_GRADIENT : forall h
  (gm : GradientModel h) x,
  (InfiniteDissipation h gm x <->
   ~ exists G, ProbeRepresents (GDual h gm) (GradientProbe h gm x) G).
Proof.
  intros h gm x. split.
  - intros Hinfinite [G HG].
    apply (Hinfinite (HNorm (DTarget (GDual h gm)) G)).
    apply (proj2 (DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND h gm x _)).
    exists G. split; [exact HG | lra].
  - intros Hnograd M HM. apply Hnograd.
    destruct (proj1 (DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND h gm x M) HM)
      as [G [HG _]].
    exists G. exact HG.
Qed.

Lemma DissipationSublevel_monotone : forall h (gm : GradientModel h) x M K,
  DissipationSublevel h gm x M -> M <= K -> DissipationSublevel h gm x K.
Proof. intros h gm x M K HM Hle z. specialize (HM z). lra. Qed.

Lemma DissipationSublevel_nonnegative : forall h (gm : GradientModel h) x M,
  DissipationSublevel h gm x M -> 0 <= M.
Proof.
  intros h gm x M HM.
  eapply VarUpper_nonnegative; [apply GRADIENT_PROBE_LINEAR | exact HM].
Qed.

Theorem VarUpper_frequent_closed : forall m
  (F : HCarrier (DTest m) -> R) (Fn : nat -> HCarrier (DTest m) -> R) M,
  (forall z, SeqLimit (fun n => Fn n z) (F z)) ->
  (forall eps, 0 < eps -> forall N : nat,
    exists n, (N <= n)%nat /\ VarUpper m (Fn n) (M + eps)) ->
  VarUpper m F M.
Proof.
  intros m F Fn M Hconv Hfreq z.
  eapply SeqLimit_upper_frequent
    with (f := fun n => 2 * Fn n z - HNorm (DTest m) z).
  - apply SeqLimit_affine. apply Hconv.
  - intros eps Heps N. destruct (Hfreq eps Heps N) as [n [Hn Hbound]].
    exists n. split; [exact Hn | apply Hbound].
Qed.

Lemma GradientProbe_weak_limit : forall h (gm : GradientModel h) u x,
  HWeakSequential h u x -> forall z,
  SeqLimit (fun n => GradientProbe h gm (u n) z) (GradientProbe h gm x z).
Proof.
  intros h gm u x Hweak z. unfold GradientProbe.
  apply SeqLimit_neg. apply Hweak.
Qed.

Theorem DISSIPATION_SUBLEVEL_WEAK_LIMINF : forall h (gm : GradientModel h)
  u x M,
  HWeakSequential h u x ->
  (forall eps, 0 < eps -> forall N : nat,
    exists n, (N <= n)%nat /\ DissipationSublevel h gm (u n) (M + eps)) ->
  DissipationSublevel h gm x M.
Proof.
  intros h gm u x M Hweak Hfreq.
  eapply VarUpper_frequent_closed; [| exact Hfreq].
  apply GradientProbe_weak_limit. exact Hweak.
Qed.

Theorem DISSIPATION_SUBLEVEL_WEAK_CLOSED : forall h (gm : GradientModel h)
  u x M,
  HWeakSequential h u x ->
  (forall n, DissipationSublevel h gm (u n) M) ->
  DissipationSublevel h gm x M.
Proof.
  intros h gm u x M Hweak Hbound.
  eapply DISSIPATION_SUBLEVEL_WEAK_LIMINF; [exact Hweak |].
  intros eps Heps N. exists N. split; [lia |].
  eapply DissipationSublevel_monotone; [apply Hbound | lra].
Qed.

Theorem DISSIPATION_SUBLEVEL_STRONG_CLOSED : forall h (gm : GradientModel h)
  u x M,
  HConverges h u x ->
  (forall n, DissipationSublevel h gm (u n) M) ->
  DissipationSublevel h gm x M.
Proof.
  intros h gm u x M Hstrong Hbound.
  eapply DISSIPATION_SUBLEVEL_WEAK_CLOSED; [| exact Hbound].
  apply HStrongSequential_to_weak. exact Hstrong.
Qed.

Theorem WEAK_LIMIT_BOUNDED_GRADIENTS : forall h (gm : GradientModel h)
  u x M,
  HWeakSequential h u x ->
  (forall n, exists G,
    ProbeRepresents (GDual h gm) (GradientProbe h gm (u n)) G /\
    HNorm (DTarget (GDual h gm)) G <= M) ->
  exists G, ProbeRepresents (GDual h gm) (GradientProbe h gm x) G /\
    HNorm (DTarget (GDual h gm)) G <= M.
Proof.
  intros h gm u x M Hweak Hbound.
  apply (proj1 (DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND h gm x M)).
  eapply DISSIPATION_SUBLEVEL_WEAK_CLOSED; [exact Hweak |].
  intro n. apply (proj2 (DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND h gm (u n) M)).
  apply Hbound.
Qed.

Theorem GRADIENT_GRAPH_WEAK_CLOSED : forall h (gm : GradientModel h)
  u x (Gs : nat -> HCarrier (DTarget (GDual h gm))) G,
  HWeakSequential h u x ->
  HWeakSequential (DTarget (GDual h gm)) Gs G ->
  (forall n, ProbeRepresents (GDual h gm) (GradientProbe h gm (u n)) (Gs n)) ->
  ProbeRepresents (GDual h gm) (GradientProbe h gm x) G.
Proof.
  intros h gm u x Gs G Hu HG Hgraph z.
  pose proof (GradientProbe_weak_limit h gm u x Hu z) as Hleft.
  pose proof (HG (DEmbed (GDual h gm) z)) as Hright.
  assert (Hright_probe : SeqLimit (fun n => GradientProbe h gm (u n) z)
    (HInner (DTarget (GDual h gm)) G (DEmbed (GDual h gm) z))).
  { apply (proj2 (SeqLimit_ext
      (fun n => GradientProbe h gm (u n) z)
      (fun n => HInner (DTarget (GDual h gm)) (Gs n) (DEmbed (GDual h gm) z))
      _ (fun n => Hgraph n z))).
    exact Hright. }
  eapply SeqLimit_unique; [exact Hleft | exact Hright_probe].
Qed.

Theorem GRADIENT_GRAPH_STRONG_CLOSED : forall h (gm : GradientModel h)
  u x (Gs : nat -> HCarrier (DTarget (GDual h gm))) G,
  HConverges h u x -> HConverges (DTarget (GDual h gm)) Gs G ->
  (forall n, ProbeRepresents (GDual h gm) (GradientProbe h gm (u n)) (Gs n)) ->
  ProbeRepresents (GDual h gm) (GradientProbe h gm x) G.
Proof.
  intros h gm u x Gs G Hu HG Hgraph.
  eapply GRADIENT_GRAPH_WEAK_CLOSED;
    [apply HStrongSequential_to_weak; exact Hu |
     apply HStrongSequential_to_weak; exact HG | exact Hgraph].
Qed.

Theorem GRADIENT_ENERGY_WEAK_LIMINF : forall h (gm : GradientModel h)
  u x (Dn : Seq) M,
  HWeakSequential h u x ->
  (forall n, GradientEnergyAt h gm (u n) (Dn n)) ->
  (forall eps, 0 < eps -> forall N : nat,
    exists n, (N <= n)%nat /\ Dn n <= M + eps) ->
  exists D, GradientEnergyAt h gm x D /\ D <= M.
Proof.
  intros h gm u x Dn M Hweak Hvalues Hfreq.
  assert (Hlimit : DissipationSublevel h gm x M).
  { eapply DISSIPATION_SUBLEVEL_WEAK_LIMINF; [exact Hweak |].
    intros eps Heps N. destruct (Hfreq eps Heps N) as [n [Hn HDn]].
    exists n. split; [exact Hn |].
    destruct (Hvalues n) as [Gn [HGn Hnorm]].
    apply (proj2 (DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND h gm (u n) (M + eps))).
    exists Gn. split; [exact HGn | rewrite Hnorm; exact HDn]. }
  destruct (proj1 (DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND h gm x M) Hlimit)
    as [G [HG Hnorm]].
  exists (HNorm (DTarget (GDual h gm)) G). split; [| exact Hnorm].
  exists G. split; [exact HG | reflexivity].
Qed.

Theorem GP_DISSIPATION_SUBLEVEL_EXACT : forall h (b : OrthonormalBasis h),
  HComplete h -> forall (gm : GradientModel h) g p x M,
  GPNonzero g -> seq_eq (HGPEncode b g x) p ->
  (GPDissipationUpper h b gm g p M <-> DissipationSublevel h gm x M).
Proof.
  intros h b Hcomplete gm g p x M Hg Henc.
  apply GRADIENT_DISSIPATION_UPPER_EXACT; assumption.
Qed.

Theorem GP_DISSIPATION_SUBLEVEL_WEAK_CLOSED : forall h (b : OrthonormalBasis h),
  HComplete h -> forall (gm : GradientModel h) g u x M,
  GPNonzero g -> HWeakSequential h u x ->
  (forall n, GPDissipationUpper h b gm g (HGPEncode b g (u n)) M) ->
  GPDissipationUpper h b gm g (HGPEncode b g x) M.
Proof.
  intros h b Hcomplete gm g u x M Hg Hweak Hbound.
  apply (proj2 (GP_DISSIPATION_SUBLEVEL_EXACT h b Hcomplete gm g
    (HGPEncode b g x) x M Hg (seq_eq_refl _))).
  eapply DISSIPATION_SUBLEVEL_WEAK_CLOSED; [exact Hweak |].
  intro n. apply (proj1 (GP_DISSIPATION_SUBLEVEL_EXACT h b Hcomplete gm g
    (HGPEncode b g (u n)) (u n) M Hg (seq_eq_refl _))).
  apply Hbound.
Qed.

Print Assumptions DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND.
Print Assumptions DISSIPATION_SUBLEVEL_WEAK_LIMINF.
Print Assumptions GRADIENT_GRAPH_WEAK_CLOSED.
Print Assumptions GP_DISSIPATION_SUBLEVEL_WEAK_CLOSED.
