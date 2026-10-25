From Stdlib Require Import Reals RiemannInt Rtopology Rcomplete Lra Psatz Lia Field.
Require Import BKQR_CountableRange BKQR_TimeIntegrals BKQR_BilinearKernel.

(* The tested nonlinear source is constructed from actual Riemann integrals
   of finite quadratic polynomials. Uniform energy bounds pay the integrated
   high-mode tails; a proved Schur/Young estimate then gives Cauchy convergence.
   No pointwise weak continuity of an infinite quadratic map is asserted.
   SchurBound remains an explicit condition on the chosen concrete kernel;
   no identification with the physical Navier--Stokes kernel is made here. *)
Module BKQR_NONLINEAR_TIME_SOURCE.
Import GP_COUNTABLE_RANGE BKQR_TIME_INTEGRALS BKQR_BILINEAR_KERNEL.
Open Scope R_scope.

Lemma continuous_product : forall a b f g,
  ClosedContinuous f a b -> ClosedContinuous g a b ->
  ClosedContinuous (fun t => f t*g t) a b.
Proof.
  intros a b f g Hf Hg t Ht. apply continuity_pt_mult;
    [apply Hf|apply Hg]; exact Ht.
Qed.

Lemma continuous_minus : forall a b f g,
  ClosedContinuous f a b -> ClosedContinuous g a b ->
  ClosedContinuous (fun t => f t-g t) a b.
Proof.
  intros a b f g Hf Hg t Ht. apply continuity_pt_minus;
    [apply Hf|apply Hg]; exact Ht.
Qed.

Lemma integral_order : forall a b Hab f g Hf Hg,
  (forall t, a <= t <= b -> f t <= g t) ->
  integral a b Hab f Hf <= integral a b Hab g Hg.
Proof.
  intros a b Hab f g Hf Hg Horder. unfold integral.
  apply RiemannInt_P19; [exact Hab|]. intros. apply Horder. lra.
Qed.

Lemma integral_minus : forall a b Hab f g Hf Hg Hminus,
  integral a b Hab (fun t => f t-g t) Hminus =
  integral a b Hab f Hf-integral a b Hab g Hg.
Proof.
  intros a b Hab f g Hf Hg Hminus.
  pose proof (continuous_plus a b f (fun t => (-1)*g t) Hf
    (continuous_scale a b (-1) g Hg)) as Hlinear.
  transitivity (integral a b Hab (fun t => f t+(-1)*g t) Hlinear).
  - apply integral_ext. intros. ring.
  - rewrite (integral_linear a b Hab f g (-1) Hf Hg Hlinear). ring.
Qed.

Lemma integral_absolute_bound : forall a b Hab f g Hf Hg,
  (forall t, a <= t <= b -> Rabs (f t) <= g t) ->
  Rabs (integral a b Hab f Hf) <= integral a b Hab g Hg.
Proof.
  intros a b Hab f g Hf Hg Hbound.
  assert (Hupper : integral a b Hab f Hf <= integral a b Hab g Hg).
  { apply integral_order. intros t Ht.
    pose proof (Rle_abs (f t)). specialize (Hbound t Ht). lra. }
  pose proof (continuous_scale a b (-1) f Hf) as Hneg.
  assert (Hlower : integral a b Hab (fun t => (-1)*f t) Hneg <=
    integral a b Hab g Hg).
  { apply integral_order. intros t Ht.
    pose proof (Rle_abs (-f t)) as Habs. rewrite Rabs_Ropp in Habs.
    specialize (Hbound t Ht). lra. }
  rewrite (integral_scale a b Hab f (-1) Hf Hneg) in Hlower. apply Rabs_le. lra.
Qed.

Lemma continuous_has_absolute_bound : forall a b (Hab:a<=b) f,
  ClosedContinuous f a b ->
  exists A, 0 <= A /\ forall t, a <= t <= b -> Rabs (f t) <= A.
Proof.
  intros a b Hab f Hf.
  assert (Habs : ClosedContinuous (fun t => Rabs (f t)) a b).
  { intros t Ht. apply (continuity_pt_comp f Rabs t).
    - apply Hf. exact Ht.
    - apply Rcontinuity_abs. }
  destruct (continuity_ab_maj (fun t => Rabs (f t)) a b Hab Habs)
    as [tmax [Hmax Htmax]].
  exists (Rabs (f tmax)). split; [apply Rabs_pos|exact Hmax].
Qed.

Definition energy_integrand N (u : R -> nat -> R) t := physical_prefix (u t) N.

Lemma energy_integrand_continuous : forall a b u,
  CoordinateContinuous u a b -> forall N,
  ClosedContinuous (energy_integrand N u) a b.
Proof.
  intros a b u Hu N. unfold energy_integrand, physical_prefix.
  apply continuous_gp_sum. intro i. apply continuous_product; apply Hu.
Qed.

Lemma energy_integral_formula : forall a b Hab u Hu N Henergy,
  integral a b Hab (energy_integrand N u) Henergy =
    time_prefix (fun _ => 1) u a b Hab Hu N.
Proof.
  intros a b Hab u Hu N Henergy.
  pose proof (continuous_gp_sum a b N
    (fun i t => 1*(u t i*u t i))
    (fun i => continuous_weighted_square a b 1 (fun t => u t i) (Hu i)))
    as Hprefix.
  rewrite (TIME_PREFIX_IS_RIEMANN_INTEGRAL (fun _ => 1) u a b Hab Hu N Hprefix).
  apply integral_ext. intros t Ht. unfold energy_integrand, physical_prefix.
  apply gp_sum_ext. intros. ring.
Qed.

Lemma uniform_energy_bounds_time_prefix : forall a b Hab u Hu E,
  (forall t, a <= t <= b -> PhysicalBound (u t) E) ->
  TimeBound (fun _ => 1) u a b Hab Hu (E*(b-a)).
Proof.
  intros a b Hab u Hu E Hcap N.
  pose proof (energy_integrand_continuous a b u Hu N) as Henergy.
  rewrite <- (energy_integral_formula a b Hab u Hu N Henergy).
  rewrite <- (integral_constant a b Hab E (continuous_const a b E)).
  apply integral_order. intros t Ht. apply Hcap. exact Ht.
Qed.

Lemma integral_affine_energy_tail :
  forall a b Hab u Hu N M alpha beta Haffine,
  integral a b Hab
    (fun t => alpha+beta*(energy_integrand M u t-energy_integrand N u t))
    Haffine = alpha*(b-a)+beta*(time_prefix (fun _=>1) u a b Hab Hu M-
      time_prefix (fun _=>1) u a b Hab Hu N).
Proof.
  intros a b Hab u Hu N M alpha beta Haffine.
  pose proof (energy_integrand_continuous a b u Hu M) as HM.
  pose proof (energy_integrand_continuous a b u Hu N) as HN.
  pose proof (continuous_minus a b (energy_integrand M u) (energy_integrand N u)
    HM HN) as Hdiff.
  rewrite (integral_linear a b Hab (fun _=>alpha)
    (fun t=>energy_integrand M u t-energy_integrand N u t) beta
    (continuous_const a b alpha) Hdiff Haffine).
  rewrite integral_constant.
  rewrite (integral_minus a b Hab (energy_integrand M u)
    (energy_integrand N u) HM HN Hdiff).
  rewrite (energy_integral_formula a b Hab u Hu M HM).
  rewrite (energy_integral_formula a b Hab u Hu N HN). reflexivity.
Qed.

(* Young's free parameter and the actual integrated tail give a Cauchy
   sequence.  No continuity of an infinite quadratic map is used. *)
Lemma young_tail_cauchy : forall (f p : nat -> R) P B D,
  0 <= B -> 0 <= D -> SeqLimit p P -> (forall N, p N <= P) ->
  (forall delta, 0 < delta -> forall N M, (N <= M)%nat ->
    Rabs (f M-f N) <= B*delta+(D/delta)*(p M-p N)) ->
  Cauchy_crit f.
Proof.
  intros f p P B D HB HD Hlim Hupper Hdiff eps Heps.
  set (delta := eps/(4*(B+1))).
  assert (Hdelta : 0 < delta).
  { unfold delta. apply Rdiv_lt_0_compat; nra. }
  assert (Hdeq : 4*(B+1)*delta=eps).
  { unfold delta. field. lra. }
  assert (HBsmall : B*delta < eps/4) by nra.
  set (K := D/delta).
  assert (HK : 0 <= K).
  { unfold K, Rdiv. apply Rmult_le_pos; [exact HD|].
    left. apply Rinv_0_lt_compat. exact Hdelta. }
  set (gamma := eps/(4*(K+1))).
  assert (Hgamma : 0 < gamma).
  { unfold gamma. apply Rdiv_lt_0_compat; nra. }
  assert (Hgeq : 4*(K+1)*gamma=eps).
  { unfold gamma. field. lra. }
  assert (HKsmall : K*gamma < eps/4) by nra.
  destruct (Hlim gamma Hgamma) as [J HJ].
  assert (Hordered : forall N M, (J <= N)%nat -> (N <= M)%nat ->
    Rabs (f M-f N) < eps).
  { intros N M HJN HNM.
    specialize (HJ N HJN). apply Rabs_def2 in HJ. destruct HJ as [HJ1 HJ2].
    pose proof (Hupper M) as HM.
    specialize (Hdiff delta Hdelta N M HNM).
    change (Rabs (f M-f N) <= B*delta+K*(p M-p N)) in Hdiff.
    assert (Htail : p M-p N < gamma) by lra.
    assert (Hpaid : K*(p M-p N) <= K*gamma).
    { apply Rmult_le_compat_l; [exact HK|lra]. }
    lra. }
  exists J. intros n m Hn Hm. unfold Rdist.
  destruct (Nat.le_ge_cases m n) as [Hmn|Hnm].
  - apply Hordered; assumption.
  - rewrite Rabs_minus_sym. apply Hordered; assumption.
Qed.

Lemma cauchy_seq_limit : forall f, Cauchy_crit f -> { L : R | SeqLimit f L }.
Proof.
  intros f Hc. destruct (R_complete f Hc) as [L HL]. exists L.
  exact HL.
Qed.

Definition quadratic_integrand (K : nat -> nat -> R) N
  (u : R -> nat -> R) t := quadratic_form K N (u t).

Lemma quadratic_integrand_continuous : forall K u a b,
  CoordinateContinuous u a b -> forall N,
  ClosedContinuous (quadratic_integrand K N u) a b.
Proof.
  intros K u a b Hu N.
  unfold quadratic_integrand, quadratic_form, bilinear_form, bilinear_rectangle.
  apply continuous_gp_sum. intro j. apply continuous_gp_sum. intro k.
  apply continuous_product.
  - apply continuous_scale. apply Hu.
  - apply Hu.
Qed.

Definition tested_integrand K u (eta : R -> R) N t :=
  eta t*quadratic_integrand K N u t.

Lemma tested_integrand_continuous : forall K u a b,
  CoordinateContinuous u a b -> forall eta,
  ClosedContinuous eta a b -> forall N,
  ClosedContinuous (tested_integrand K u eta N) a b.
Proof.
  intros K u a b Hu eta Heta N. apply continuous_product; [exact Heta|].
  apply quadratic_integrand_continuous. exact Hu.
Qed.

Definition tested_source K u a b Hab Hu eta Heta N : R :=
  integral a b Hab (tested_integrand K u eta N)
    (tested_integrand_continuous K u a b Hu eta Heta N).

Lemma tested_source_ext : forall K u v a b Hab Hu Hv eta Heta,
  (forall t i, a <= t <= b -> u t i=v t i) -> forall N,
  tested_source K u a b Hab Hu eta Heta N=
  tested_source K v a b Hab Hv eta Heta N.
Proof.
  intros K u v a b Hab Hu Hv eta Heta Heq N. unfold tested_source.
  apply integral_ext. intros t Ht.
  unfold tested_integrand, quadratic_integrand, quadratic_form,
    bilinear_form, bilinear_rectangle.
  f_equal. apply gp_sum_ext. intros j Hj. apply gp_sum_ext. intros k Hk.
  rewrite (Heq t j Ht), (Heq t k Ht). reflexivity.
Qed.

Lemma tested_source_scale_test : forall K u a b Hab Hu eta Heta c Hscaled N,
  tested_source K u a b Hab Hu (fun t => c*eta t) Hscaled N=
  c*tested_source K u a b Hab Hu eta Heta N.
Proof.
  intros K u a b Hab Hu eta Heta c Hscaled N.
  unfold tested_source.
  pose proof (continuous_scale a b c (tested_integrand K u eta N)
    (tested_integrand_continuous K u a b Hu eta Heta N)) as Hwhole.
  transitivity (integral a b Hab
    (fun t=>c*tested_integrand K u eta N t) Hwhole).
  - apply integral_ext. intros. unfold tested_integrand. ring.
  - apply integral_scale.
Qed.

Lemma tested_source_linear_test :
  forall K u a b Hab Hu eta theta Heta Htheta c Hlinear N,
  tested_source K u a b Hab Hu (fun t=>eta t+c*theta t) Hlinear N=
  tested_source K u a b Hab Hu eta Heta N+
    c*tested_source K u a b Hab Hu theta Htheta N.
Proof.
  intros K u a b Hab Hu eta theta Heta Htheta c Hlinear N.
  unfold tested_source.
  pose proof (tested_integrand_continuous K u a b Hu eta Heta N) as HF.
  pose proof (tested_integrand_continuous K u a b Hu theta Htheta N) as HG.
  pose proof (continuous_plus a b (tested_integrand K u eta N)
    (fun t=>c*tested_integrand K u theta N t) HF
    (continuous_scale a b c (tested_integrand K u theta N) HG)) as Hwhole.
  transitivity (integral a b Hab
    (fun t=>tested_integrand K u eta N t+c*tested_integrand K u theta N t)
    Hwhole).
  - apply integral_ext. intros. unfold tested_integrand. ring.
  - apply integral_linear.
Qed.

Theorem TESTED_SOURCE_PREFIX_BOUND : forall K C u a b Hab Hu eta Heta E A,
  SchurBound K C ->
  (forall t, a <= t <= b -> PhysicalBound (u t) E) ->
  0 <= A -> (forall t, a <= t <= b -> Rabs (eta t) <= A) -> forall N,
  Rabs (tested_source K u a b Hab Hu eta Heta N) <= A*C*E*(b-a).
Proof.
  intros K C u a b Hab Hu eta Heta E A HK Hcap HA Hetab N.
  pose proof (proj1 HK) as HC.
  unfold tested_source.
  rewrite <- (integral_constant a b Hab (A*C*E) (continuous_const a b (A*C*E))).
  apply integral_absolute_bound. intros t Ht.
  unfold tested_integrand, quadratic_integrand. rewrite Rabs_mult.
  pose proof (quadratic_form_bound K C HK N (u t)) as HQ.
  pose proof (Hcap t Ht N) as HE.
  assert (HQE : Rabs (quadratic_form K N (u t)) <= C*E) by nra.
  replace (A*C*E) with (A*(C*E)) by ring.
  apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|apply Hetab; exact Ht|exact HQE].
Qed.

Lemma sequence_absolute_bound : forall f L A,
  SeqLimit f L -> (forall N, Rabs (f N) <= A) -> Rabs L <= A.
Proof.
  intros f L A Hlim Hbound.
  assert (Hupper : L <= A).
  { apply (limit_upper_bound f L A Hlim). intro N.
    pose proof (Rle_abs (f N)). specialize (Hbound N). lra. }
  assert (Hlower : (-1)*L <= A).
  { apply (limit_upper_bound (fun N=>(-1)*f N) ((-1)*L) A
      (limit_scale f L (-1) Hlim)). intro N.
    pose proof (Rle_abs (-(f N))) as Habs. rewrite Rabs_Ropp in Habs.
    specialize (Hbound N). lra. }
  apply Rabs_le. lra.
Qed.

Theorem TESTED_SOURCE_LIMIT_UNIQUE : forall K u a b Hab Hu eta Heta L R,
  SeqLimit (tested_source K u a b Hab Hu eta Heta) L ->
  SeqLimit (tested_source K u a b Hab Hu eta Heta) R -> L=R.
Proof. intros. eapply UL_sequence; eassumption. Qed.

Theorem TESTED_SOURCE_LIMIT_BOUND : forall K C u a b Hab Hu eta Heta E A L,
  SchurBound K C ->
  (forall t, a <= t <= b -> PhysicalBound (u t) E) ->
  0 <= A -> (forall t, a <= t <= b -> Rabs (eta t) <= A) ->
  SeqLimit (tested_source K u a b Hab Hu eta Heta) L ->
  Rabs L <= A*C*E*(b-a).
Proof.
  intros K C u a b Hab Hu eta Heta E A L HK Hcap HA Hetab Hlim.
  apply (sequence_absolute_bound
    (tested_source K u a b Hab Hu eta Heta) L (A*C*E*(b-a)) Hlim).
  apply TESTED_SOURCE_PREFIX_BOUND; assumption.
Qed.

Theorem TESTED_SOURCE_LIMIT_LINEAR_TEST :
  forall K u a b Hab Hu eta theta Heta Htheta c Hlinear L M,
  SeqLimit (tested_source K u a b Hab Hu eta Heta) L ->
  SeqLimit (tested_source K u a b Hab Hu theta Htheta) M ->
  SeqLimit (tested_source K u a b Hab Hu (fun t=>eta t+c*theta t) Hlinear)
    (L+c*M).
Proof.
  intros K u a b Hab Hu eta theta Heta Htheta c Hlinear L M HL HM.
  eapply limit_ext.
  - intro N. symmetry. apply tested_source_linear_test.
  - apply limit_plus; [exact HL|]. apply limit_scale. exact HM.
Qed.

Theorem TESTED_SOURCE_LIMIT_SCALE_TEST :
  forall K u a b Hab Hu eta Heta c Hscaled L,
  SeqLimit (tested_source K u a b Hab Hu eta Heta) L ->
  SeqLimit (tested_source K u a b Hab Hu (fun t=>c*eta t) Hscaled) (c*L).
Proof.
  intros K u a b Hab Hu eta Heta c Hscaled L HL.
  eapply limit_ext.
  - intro N. symmetry. apply tested_source_scale_test.
  - apply limit_scale. exact HL.
Qed.

Theorem TESTED_SOURCE_LIMIT_EXT : forall K u v a b Hab Hu Hv eta Heta L,
  (forall t i, a <= t <= b -> u t i=v t i) ->
  SeqLimit (tested_source K u a b Hab Hu eta Heta) L ->
  SeqLimit (tested_source K v a b Hab Hv eta Heta) L.
Proof.
  intros K u v a b Hab Hu Hv eta Heta L Heq Hlim.
  apply (limit_ext (tested_source K u a b Hab Hu eta Heta)
    (tested_source K v a b Hab Hv eta Heta) L).
  - apply tested_source_ext. exact Heq.
  - exact Hlim.
Qed.

Lemma tested_source_difference_bound :
  forall K C u a b Hab Hu eta Heta E A,
  SchurBound K C ->
  (forall t, a <= t <= b -> PhysicalBound (u t) E) ->
  0 <= A -> (forall t, a <= t <= b -> Rabs (eta t) <= A) ->
  forall delta, 0 < delta -> forall N M, (N <= M)%nat ->
  Rabs (tested_source K u a b Hab Hu eta Heta M-
    tested_source K u a b Hab Hu eta Heta N) <=
  (2*A*C*E*(b-a))*delta+(2*A*C/delta)*
    (time_prefix (fun _=>1) u a b Hab Hu M-time_prefix (fun _=>1) u a b Hab Hu N).
Proof.
  intros K C u a b Hab Hu eta Heta E A HK Hcap HA Hetab delta Hdelta N M HNM.
  pose proof (tested_integrand_continuous K u a b Hu eta Heta M) as HM.
  pose proof (tested_integrand_continuous K u a b Hu eta Heta N) as HN.
  pose proof (continuous_minus a b (tested_integrand K u eta M)
    (tested_integrand K u eta N) HM HN) as Hdiff.
  pose proof (energy_integrand_continuous a b u Hu M) as HEM.
  pose proof (energy_integrand_continuous a b u Hu N) as HEN.
  pose proof (continuous_minus a b (energy_integrand M u) (energy_integrand N u)
    HEM HEN) as HEdiff.
  set (alpha := 2*A*C*delta*E).
  set (beta := 2*A*C/delta).
  pose proof (continuous_plus a b (fun _=>alpha)
    (fun t=>beta*(energy_integrand M u t-energy_integrand N u t))
    (continuous_const a b alpha)
    (continuous_scale a b beta
      (fun t=>energy_integrand M u t-energy_integrand N u t) HEdiff)) as Hg.
  assert (Hpoint : forall t, a <= t <= b ->
    Rabs (tested_integrand K u eta M t-tested_integrand K u eta N t) <=
    alpha+beta*(energy_integrand M u t-energy_integrand N u t)).
  { intros t Ht. unfold tested_integrand, quadratic_integrand.
    replace (eta t*quadratic_form K M (u t)-eta t*quadratic_form K N (u t))
      with (eta t*(quadratic_form K M (u t)-quadratic_form K N (u t))) by ring.
    rewrite Rabs_mult.
    pose proof (quadratic_form_difference_bound K C HK N M (u t) E delta
      HNM (Hcap t Ht M) Hdelta) as HQ.
    eapply Rle_trans.
    - apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|apply Hetab; exact Ht|exact HQ].
    - right. unfold alpha, beta, energy_integrand, Rdiv. ring. }
  pose proof (integral_absolute_bound a b Hab
    (fun t=>tested_integrand K u eta M t-tested_integrand K u eta N t)
    (fun t=>alpha+beta*(energy_integrand M u t-energy_integrand N u t))
    Hdiff Hg Hpoint) as Hbound.
  rewrite (integral_minus a b Hab (tested_integrand K u eta M)
    (tested_integrand K u eta N) HM HN Hdiff) in Hbound.
  rewrite (integral_affine_energy_tail a b Hab u Hu N M alpha beta Hg) in Hbound.
  rewrite (integral_proof_independent a b Hab Hab (tested_integrand K u eta M)
    HM (tested_integrand_continuous K u a b Hu eta Heta M)) in Hbound.
  rewrite (integral_proof_independent a b Hab Hab (tested_integrand K u eta N)
    HN (tested_integrand_continuous K u a b Hu eta Heta N)) in Hbound.
  unfold tested_source.
  eapply Rle_trans; [exact Hbound|]. right. unfold alpha, beta, Rdiv. ring.
Qed.

Theorem TESTED_SOURCE_CAUCHY : forall K C u a b Hab Hu eta Heta E,
  SchurBound K C ->
  (forall t, a <= t <= b -> PhysicalBound (u t) E) ->
  Cauchy_crit (tested_source K u a b Hab Hu eta Heta).
Proof.
  intros K C u a b Hab Hu eta Heta E HK Hcap.
  destruct (continuous_has_absolute_bound a b Hab eta Heta) as [A [HA Hetab]].
  assert (HE : 0 <= E).
  { pose proof (Hcap a (ltac:(lra)) O) as H. exact H. }
  pose proof (proj1 HK) as HC.
  assert (Hfinite : exists D, TimeBound (fun _=>1) u a b Hab Hu D).
  { exists (E*(b-a)). apply uniform_energy_bounds_time_prefix. exact Hcap. }
  destruct (time_total_exists (fun _=>1) u a b Hab Hu Hfinite) as [P HP].
  apply (young_tail_cauchy (tested_source K u a b Hab Hu eta Heta)
    (fun N=>time_prefix (fun _=>1) u a b Hab Hu N) P
    (2*A*C*E*(b-a)) (2*A*C)).
  - repeat apply Rmult_le_pos; lra.
  - repeat apply Rmult_le_pos; lra.
  - apply TIME_PREFIX_CONVERGES_TO_TOTAL; [intro i; lra|exact HP].
  - exact (proj1 HP).
  - intros delta Hdelta N M HNM.
    apply tested_source_difference_bound; assumption.
Qed.

(* The real value is constructed by Stdlib completeness.  All hypotheses
   are energy/kernel bounds; nonlinear convergence is a proved conclusion. *)
Definition tested_source_limit K C u a b Hab Hu eta Heta E
  (HK : SchurBound K C)
  (Hcap : forall t, a <= t <= b -> PhysicalBound (u t) E) :
  { L : R | SeqLimit (tested_source K u a b Hab Hu eta Heta) L } :=
  cauchy_seq_limit (tested_source K u a b Hab Hu eta Heta)
    (TESTED_SOURCE_CAUCHY K C u a b Hab Hu eta Heta E HK Hcap).

Theorem TESTED_SOURCE_LIMIT_EXISTS : forall K C u a b Hab Hu eta Heta E,
  SchurBound K C ->
  (forall t, a <= t <= b -> PhysicalBound (u t) E) ->
  exists L, SeqLimit (tested_source K u a b Hab Hu eta Heta) L.
Proof.
  intros K C u a b Hab Hu eta Heta E HK Hcap.
  destruct (tested_source_limit K C u a b Hab Hu eta Heta E HK Hcap) as [L HL].
  exists L. exact HL.
Qed.

Print Assumptions TESTED_SOURCE_CAUCHY.
Print Assumptions tested_source_limit.
Print Assumptions TESTED_SOURCE_LIMIT_BOUND.
Print Assumptions TESTED_SOURCE_LIMIT_LINEAR_TEST.
End BKQR_NONLINEAR_TIME_SOURCE.
