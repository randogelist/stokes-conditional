From Stdlib Require Import Reals Lra Psatz Lia Arith.Compare_dec.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Realization.

Open Scope R_scope.

(* Weak time continuity is proved from continuous individual coordinates and
   a common energy bound. No continuity of arbitrary infinite probes is
   assumed in that direction. Concrete physical L2 is a later realization. *)

Definition ScalarContinuousOn (T : R) (f : R -> R) : Prop :=
  forall t, 0 <= t <= T -> forall eps, 0 < eps ->
  exists delta, 0 < delta /\ forall s,
    0 <= s <= T -> Rabs (s - t) < delta -> Rabs (f s - f t) < eps.

Definition CoordinatesContinuous (a : CoefficientPath) (T : R) : Prop :=
  forall i, ScalarContinuousOn T (fun t => a t i).

Definition HWeakContinuous (h : HilbertData) (u : R -> HCarrier h) (T : R) : Prop :=
  forall y, ScalarContinuousOn T (fun t => HInner h (u t) y).

Definition HCoordinatesContinuous {h : HilbertData} (b : OrthonormalBasis h)
  (u : R -> HCarrier h) (T : R) : Prop :=
  CoordinatesContinuous (fun t => HAnalysis b (u t)) T.

Lemma ScalarContinuousOn_ext : forall T f g,
  (forall t, 0 <= t <= T -> f t = g t) ->
  ScalarContinuousOn T f -> ScalarContinuousOn T g.
Proof.
  intros T f g Heq Hf t Ht eps Heps.
  destruct (Hf t Ht eps Heps) as [delta [Hdelta Hbound]].
  exists delta; split; [exact Hdelta |].
  intros s Hs Hst. rewrite <- (Heq s Hs), <- (Heq t Ht).
  apply Hbound; assumption.
Qed.

Lemma ScalarContinuousOn_constant : forall T c,
  ScalarContinuousOn T (fun _ => c).
Proof.
  intros T c t Ht eps Heps. exists 1; split; [lra |].
  intros s Hs Hst. replace (c - c) with 0 by ring.
  rewrite Rabs_R0. exact Heps.
Qed.

Lemma ScalarContinuousOn_add : forall T f g,
  ScalarContinuousOn T f -> ScalarContinuousOn T g ->
  ScalarContinuousOn T (fun t => f t + g t).
Proof.
  intros T f g Hf Hg t Ht eps Heps.
  destruct (Hf t Ht (eps / 2) ltac:(lra)) as [df [Hdf Hfbound]].
  destruct (Hg t Ht (eps / 2) ltac:(lra)) as [dg [Hdg Hgbound]].
  exists (Rmin df dg); split; [apply Rmin_pos; assumption |].
  intros s Hs Hst.
  pose proof (Rmin_l df dg) as Hminf.
  pose proof (Rmin_r df dg) as Hming.
  specialize (Hfbound s Hs ltac:(lra)).
  specialize (Hgbound s Hs ltac:(lra)).
  replace (f s + g s - (f t + g t)) with
    ((f s - f t) + (g s - g t)) by ring.
  eapply Rle_lt_trans; [apply Rabs_triang | lra].
Qed.

Lemma ScalarContinuousOn_scale : forall T c f,
  ScalarContinuousOn T f -> ScalarContinuousOn T (fun t => c * f t).
Proof.
  intros T c f Hf t Ht eps Heps.
  pose proof (Rabs_pos c) as Hc.
  assert (Hdenom : 0 < Rabs c + 1) by lra.
  assert (Hsmall : 0 < eps / (Rabs c + 1)).
  { apply Rdiv_lt_0_compat; assumption. }
  destruct (Hf t Ht _ Hsmall) as [delta [Hdelta Hbound]].
  exists delta; split; [exact Hdelta |].
  intros s Hs Hst. specialize (Hbound s Hs Hst).
  replace (c * f s - c * f t) with (c * (f s - f t)) by ring.
  rewrite Rabs_mult.
  assert (Hproduct : Rabs (f s - f t) * (Rabs c + 1) < eps).
  { assert (Hm : Rabs (f s - f t) * (Rabs c + 1) <
      (eps / (Rabs c + 1)) * (Rabs c + 1)).
    { apply Rmult_lt_compat_r; assumption. }
    replace ((eps / (Rabs c + 1)) * (Rabs c + 1)) with eps in Hm
      by (field; lra).
    exact Hm. }
  pose proof (Rabs_pos (f s - f t)). nra.
Qed.

Lemma ScalarContinuousOn_prefix : forall T (f : R -> Seq),
  (forall i, ScalarContinuousOn T (fun t => f t i)) ->
  forall n, ScalarContinuousOn T (fun t => prefix (f t) n).
Proof.
  intros T f Hf n. induction n as [|n IH]; simpl.
  - apply ScalarContinuousOn_constant.
  - apply ScalarContinuousOn_add; [exact IH | apply Hf].
Qed.

Lemma CoordinatesContinuous_ext : forall a c T,
  (forall t, 0 <= t <= T -> seq_eq (a t) (c t)) ->
  (CoordinatesContinuous a T <-> CoordinatesContinuous c T).
Proof.
  intros a c T Heq. split; intros HC i.
  - eapply ScalarContinuousOn_ext; [intros t Ht; apply Heq; exact Ht | apply HC].
  - eapply ScalarContinuousOn_ext;
      [intros t Ht; symmetry; apply Heq; exact Ht | apply HC].
Qed.

Theorem HWeakContinuous_to_coordinates : forall h (b : OrthonormalBasis h) u T,
  HWeakContinuous h u T -> HCoordinatesContinuous b u T.
Proof. intros h b u T Hweak i. apply (Hweak (HBasis h b i)). Qed.

Lemma HCoordinates_finite_test_continuous : forall h (b : OrthonormalBasis h)
  u T a n,
  HCoordinatesContinuous b u T ->
  ScalarContinuousOn T (fun t => HInner h (u t) (HFinite b a n)).
Proof.
  intros h b u T a n HC.
  assert (Hfinite : forall t,
    prefix (fun i => a i * HAnalysis b (u t) i) n =
    HInner h (u t) (HFinite b a n)).
  { intro t. rewrite HInner_sym, HFinite_inner.
    apply prefix_ext. intro i. unfold HAnalysis.
    rewrite (HInner_sym h (HBasis h b i) (u t)). reflexivity. }
  eapply ScalarContinuousOn_ext; [intros t Ht; apply Hfinite |].
  apply ScalarContinuousOn_prefix. intro i.
  apply ScalarContinuousOn_scale. apply HC.
Qed.

Lemma HInner_small_test_error : forall h (x y z : HCarrier h) M eps,
  0 <= M -> HNorm h x <= M -> 0 < eps ->
  HDist h y z < eps * eps / (M + 1) ->
  Rabs (HInner h x y - HInner h x z) < eps.
Proof.
  intros h x y z M eps HM Hx Heps Hsmall.
  pose proof (HInner_distance_bound h y z x) as Hcs.
  rewrite (HInner_sym h y x), (HInner_sym h z x) in Hcs.
  pose proof (HDist_nonnegative h y z) as Hd.
  assert (Hproduct : HDist h y z * (M + 1) < eps * eps).
  { assert (Hm : HDist h y z * (M + 1) <
      (eps * eps / (M + 1)) * (M + 1)).
    { apply Rmult_lt_compat_r; [lra | exact Hsmall]. }
    replace ((eps * eps / (M + 1)) * (M + 1)) with (eps * eps)
      in Hm by (field; lra).
    exact Hm. }
  assert (Hcap : HDist h y z * HNorm h x <= HDist h y z * M).
  { apply Rmult_le_compat_l; assumption. }
  apply Rabs_def1; nra.
Qed.

Lemma weak_abs_three : forall A B C D : R,
  Rabs (A - D) <= Rabs (A - B) + Rabs (B - C) + Rabs (C - D).
Proof.
  intros A B C D.
  pose proof (Rabs_triang (A - B) (B - C)) as H1.
  pose proof (Rabs_triang ((A - B) + (B - C)) (C - D)) as H2.
  replace ((A - B) + (B - C) + (C - D)) with (A - D) in H2 by ring.
  lra.
Qed.

Theorem HCoordinates_and_norm_bound_weak : forall h (b : OrthonormalBasis h),
  HComplete h -> forall u T M,
  HCoordinatesContinuous b u T ->
  (forall t, 0 <= t <= T -> HNorm h (u t) <= M) ->
  HWeakContinuous h u T.
Proof.
  intros h b Hcomplete u T M HC HB y t Ht eps Heps.
  assert (HM : 0 <= M).
  { specialize (HB t Ht). pose proof (HNorm_nonnegative h (u t)). lra. }
  assert (Heps3 : 0 < eps / 3) by lra.
  assert (Hdelta : 0 < (eps / 3) * (eps / 3) / (M + 1)).
  { apply Rdiv_lt_0_compat; nra. }
  destruct (HAnalysis_reconstruction h b Hcomplete y _ Hdelta) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  set (yN := HFinite b (HAnalysis b y) N).
  assert (Happrox : HDist h y yN < (eps / 3) * (eps / 3) / (M + 1)).
  { unfold yN. rewrite HDist_sym. exact HN. }
  assert (Htail : forall r, 0 <= r <= T ->
    Rabs (HInner h (u r) y - HInner h (u r) yN) < eps / 3).
  { intros r Hr. eapply HInner_small_test_error;
      [exact HM | apply HB; exact Hr | exact Heps3 | exact Happrox]. }
  pose proof (HCoordinates_finite_test_continuous h b u T (HAnalysis b y) N HC)
    as Hfinite.
  destruct (Hfinite t Ht _ Heps3) as [delta [Hdelta0 Hbound]].
  exists delta; split; [exact Hdelta0 |].
  intros s Hs Hst. specialize (Hbound s Hs Hst).
  change (Rabs (HInner h (u s) yN - HInner h (u t) yN) < eps / 3) in Hbound.
  pose proof (Htail s Hs) as Htails.
  pose proof (Htail t Ht) as Htailt.
  pose proof (weak_abs_three
    (HInner h (u s) y) (HInner h (u s) yN)
    (HInner h (u t) yN) (HInner h (u t) y)) as Hthree.
  rewrite (Rabs_minus_sym (HInner h (u t) yN) (HInner h (u t) y)) in Hthree.
  lra.
Qed.

Theorem HCoordinates_and_bound_weak : forall h (b : OrthonormalBasis h),
  HComplete h -> forall u T M,
  HCoordinatesContinuous b u T ->
  UniformEnergyBound (fun t => HAnalysis b (u t)) T M ->
  HWeakContinuous h u T.
Proof.
  intros h b Hcomplete u T M HC HB.
  eapply HCoordinates_and_norm_bound_weak; [exact Hcomplete | exact HC |].
  intros t Ht.
  destruct (HAnalysis_parseval h b Hcomplete (u t)) as [_ Hleast].
  apply Hleast. apply HB. exact Ht.
Qed.

(* The existential readout is only required at times in the interval. This
   avoids imposing requirements on an arbitrary path outside [0,T]. *)
Definition CoefficientWeakContinuous (a : CoefficientPath) (T : R) : Prop :=
  forall f, CoordinateL2 f -> exists r : R -> R,
    (forall t, 0 <= t <= T -> linear_limit (a t) f (r t)) /\
    ScalarContinuousOn T r.

Definition GPWeakContinuous (g : Seq) (p : CoefficientPath) (T : R) : Prop :=
  CoefficientWeakContinuous (decode_path g p) T.

Lemma weak_linear_limit_test_ext : forall a f k l,
  seq_eq f k -> (linear_limit a f l <-> linear_limit a k l).
Proof.
  intros a f k l Heq. unfold linear_limit.
  apply SeqLimit_ext. intro n. apply linear_prefix_test_ext. exact Heq.
Qed.

Lemma CoefficientWeakContinuous_ext : forall a c T,
  (forall t, 0 <= t <= T -> seq_eq (a t) (c t)) ->
  (CoefficientWeakContinuous a T <-> CoefficientWeakContinuous c T).
Proof.
  intros a c T Heq. split; intros HC f Hf;
    destruct (HC f Hf) as [r [Hr Hcont]]; exists r; split; try exact Hcont.
  - intros t Ht. apply (proj1 (linear_limit_ext _ _ f (r t) (Heq t Ht))).
    apply Hr. exact Ht.
  - intros t Ht. apply (proj2 (linear_limit_ext _ _ f (r t) (Heq t Ht))).
    apply Hr. exact Ht.
Qed.

Theorem HWeakContinuous_readouts_exact : forall h (b : OrthonormalBasis h),
  HComplete h -> forall u T,
  (HWeakContinuous h u T <->
   CoefficientWeakContinuous (fun t => HAnalysis b (u t)) T).
Proof.
  intros h b Hcomplete u T. split.
  - intros Hweak f Hf.
    destruct (HSynthesis_exists h b Hcomplete f Hf) as [y [Hy _]].
    exists (fun t => HInner h (u t) y). split.
    + intros t Ht. apply (proj1 (weak_linear_limit_test_ext _ _ _ _ Hy)).
      apply HAnalysis_linear_readout. exact Hcomplete.
    + apply Hweak.
  - intros HC y.
    destruct (HC (HAnalysis b y) (HAnalysis_L2 h b y)) as [r [Hr Hcont]].
    eapply ScalarContinuousOn_ext; [| exact Hcont].
    intros t Ht. eapply linear_limit_unique; [apply Hr; exact Ht |].
    apply HAnalysis_linear_readout. exact Hcomplete.
Qed.

Theorem HWeakContinuous_GP_exact : forall h (b : OrthonormalBasis h),
  HComplete h -> forall g, GPNonzero g -> forall u T,
  (HWeakContinuous h u T <->
   GPWeakContinuous g (fun t => HGPEncode b g (u t)) T).
Proof.
  intros h b Hcomplete g Hg u T.
  rewrite (HWeakContinuous_readouts_exact h b Hcomplete u T).
  unfold GPWeakContinuous.
  apply CoefficientWeakContinuous_ext. intros t Ht.
  apply seq_eq_sym. apply decode_encode. exact Hg.
Qed.

Theorem HWeak_energy_initial_trace : forall h (u : R -> HCarrier h) T,
  0 < T -> HWeakContinuous h u T ->
  (forall t, 0 <= t <= T -> HNorm h (u t) <= HNorm h (u 0)) ->
  EnergyInitialTrace (fun t => HDist h (u t) (u 0)).
Proof.
  intros h u T HT Hweak Henergy eps Heps.
  destruct (Hweak (u 0) 0 ltac:(lra) (eps / 4) ltac:(lra))
    as [delta [Hdelta Hbound]].
  exists (Rmin T delta); split; [apply Rmin_pos; assumption |].
  intros t Ht.
  pose proof (Rmin_l T delta) as HminT.
  pose proof (Rmin_r T delta) as Hmindelta.
  assert (HtI : 0 <= t <= T) by lra.
  specialize (Henergy t HtI).
  assert (Hclose : Rabs (t - 0) < delta).
  { replace (t - 0) with t by ring. rewrite Rabs_right by lra. lra. }
  specialize (Hbound t HtI Hclose).
  destruct (Rabs_def2 _ _ Hbound) as [Hupper Hlower].
  unfold HDist, HNorm in *. lra.
Qed.

Print Assumptions HCoordinates_and_bound_weak.
Print Assumptions HWeakContinuous_GP_exact.
Print Assumptions HWeak_energy_initial_trace.
