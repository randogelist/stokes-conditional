(* Actual space-time spectral cutoff estimates.  Squared errors are finite
   sums of Riemann integrals, with their countable total constructed as a
   least upper bound.  The omitted-mode identity is proved; no convergence
   or integral estimate is supplied as an opaque assumption.  A fixed
   finite-energy path needs no spectral coercivity for strong cutoffs.
   Explicit dissipation rates and uniform families use the stated frequency
   condition.  A physical Fourier/Lebesgue realization is still separate. *)
From Stdlib Require Import Reals RiemannInt Arith Lra Psatz Lia Field Classical.
Require Import BKQR_CountableRange BKQR_ShellCoordinates
  BKQR_TimeIntegrals BKQR_EnergyPaths.

Module BKQR_SPECTRAL_TIME_TAIL.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES
  BKQR_TIME_INTEGRALS BKQR_ENERGY_PATHS.
Open Scope R_scope.

Definition omitted_time_prefix w u a b Hab Hu J N : R :=
  gp_sum N (fun i => if lt_dec i J then 0
    else time_mode w u a b Hab Hu i).

(* Scalar coefficient control, independent of integration or a PDE. *)
Lemma coefficient_tail_dominance : forall (q c : nat -> R) J L D,
  (forall i, 0 <= q i) -> (forall i, 0 <= c i) -> 0 < L ->
  (forall i, (J <= i)%nat -> L <= c i) ->
  (forall N, gp_sum N (fun i => c i*q i) <= D) ->
  forall N, gp_sum N (fun i => if lt_dec i J then 0 else q i) <= D/L.
Proof.
  intros q c J L D Hq Hc HL Hcoercive HD N.
  assert (Hscaled : L * gp_sum N
    (fun i => if lt_dec i J then 0 else q i) <= D).
  { rewrite <- gp_sum_scale. eapply Rle_trans; [|apply HD].
    apply gp_sum_le. intros i Hi. destruct (lt_dec i J) as [Hij|Hij].
    - pose proof (Hq i). pose proof (Hc i). nra.
    - apply Rmult_le_compat_r; [apply Hq|apply Hcoercive; lia]. }
  assert (Heq : L*(D/L)=D) by (field; lra). nra.
Qed.

(* Any coordinate-continuity witness on the multiplier path gives the same
   integral. The multiplier identity is proved by actual integral scaling. *)
Lemma time_mode_multiply_identity : forall w lambda u a b Hab
  (Hu : CoordinateContinuous u a b)
  (Hmul : CoordinateContinuous (multiply_path lambda u) a b) i,
  time_mode w (multiply_path lambda u) a b Hab Hmul i =
  (lambda i*lambda i)*time_mode w u a b Hab Hu i.
Proof.
  intros w lambda u a b Hab Hu Hmul i.
  unfold time_mode.
  set (f := fun t => w i*(u t i*u t i)).
  pose proof (continuous_weighted_square a b (w i)
    (fun t=>u t i) (Hu i)) as Hf.
  pose proof (continuous_scale a b (lambda i*lambda i) f Hf) as Hscaled.
  transitivity (integral a b Hab
    (fun t=>(lambda i*lambda i)*f t) Hscaled).
  - apply integral_ext. intros t Ht.
    unfold multiply_path, spectral_multiply, f. ring.
  - apply integral_scale.
Qed.

Lemma dissipation_controls_weighted_time_prefix : forall lambda u a b Hab Hu D,
  DissipationTotal lambda u a b Hab D -> forall N,
  gp_sum N (fun i => (lambda i*lambda i)*
    time_mode (fun _=>1) u a b Hab Hu i) <= D.
Proof.
  intros lambda u a b Hab Hu D [Hmul [Hbound Hleast]] N.
  transitivity (time_prefix (fun _=>1) (multiply_path lambda u)
    a b Hab Hmul N); [|apply Hbound].
  apply Req_le. unfold time_prefix. apply gp_sum_ext. intros i Hi.
  symmetry. apply time_mode_multiply_identity.
Qed.

Theorem coercive_omitted_time_bound : forall lambda u a b Hab Hu J L D,
  0 < L -> (forall i, (J <= i)%nat -> L <= lambda i*lambda i) ->
  DissipationTotal lambda u a b Hab D -> forall N,
  omitted_time_prefix (fun _=>1) u a b Hab Hu J N <= D/L.
Proof.
  intros lambda u a b Hab Hu J L D HL Hcoercive HD N.
  unfold omitted_time_prefix.
  apply coefficient_tail_dominance with
    (c:=fun i=>lambda i*lambda i).
  - intro i. apply time_mode_nonnegative. intro j. lra.
  - intro i. nra.
  - exact HL.
  - exact Hcoercive.
  - apply dissipation_controls_weighted_time_prefix. exact HD.
Qed.

Lemma dissipation_total_unique : forall lambda u a b Hab D F,
  DissipationTotal lambda u a b Hab D ->
  DissipationTotal lambda u a b Hab F -> D=F.
Proof.
  intros lambda u a b Hab D F [HD [HDupper HDleast]]
    [HF [HFupper HFleast]].
  assert (Hprefix : forall N,
    time_prefix (fun _=>1) (multiply_path lambda u) a b Hab HD N =
    time_prefix (fun _=>1) (multiply_path lambda u) a b Hab HF N).
  { intro N. apply time_prefix_ext. intros. reflexivity. }
  assert (HDF : D <= F).
  { apply HDleast. intro N. rewrite Hprefix. apply HFupper. }
  assert (HFD : F <= D).
  { apply HFleast. intro N. rewrite <- Hprefix. apply HDupper. }
  lra.
Qed.

Theorem spectral_energy_dissipation_budget :
  forall lambda nu T Start u v0 E0 (HT : 0 <= T),
  0 < nu -> SpectralEnergyPath lambda nu T Start u v0 E0 ->
  exists D, DissipationTotal lambda u 0 T HT D /\
    0 <= D /\ D <= E0/(2*nu).
Proof.
  intros lambda nu T Start u v0 E0 HT Hnu
    [Hcontinuous [Hinitial [Hinitialtotal Henergy]]].
  destruct (Henergy 0 T HT (Rle_refl 0) (Rle_refl T)
    (or_introl eq_refl)) as [Es [Et [D [Hs [Ht [HD Hineq]]]]]].
  assert (HEs : Es=E0) by (eapply physical_total_unique; eassumption).
  subst Es. exists D. split; [exact HD|]. split.
  - apply (dissipation_total_nonnegative lambda u 0 T HT D). exact HD.
  - pose proof (proj1 Ht O) as HEtnonnegative.
    change (0 <= Et) in HEtnonnegative.
    assert (Heq : (2*nu)*(E0/(2*nu))=E0) by (field; lra).
    nra.
Qed.

Corollary spectral_energy_any_dissipation_budget :
  forall lambda nu T Start u v0 E0 (HT : 0 <= T) D,
  0 < nu -> SpectralEnergyPath lambda nu T Start u v0 E0 ->
  DissipationTotal lambda u 0 T HT D -> D <= E0/(2*nu).
Proof.
  intros lambda nu T Start u v0 E0 HT D Hnu Hpath HD.
  destruct (spectral_energy_dissipation_budget lambda nu T Start u v0 E0
    HT Hnu Hpath) as [F [HF [HFnonnegative HFbound]]].
  assert (Heq : D=F) by (eapply dissipation_total_unique; eassumption).
  rewrite Heq. exact HFbound.
Qed.

Theorem spectral_energy_coercive_tail_budget :
  forall lambda nu T Start u v0 E0 (HT : 0 <= T)
    (Hu : CoordinateContinuous u 0 T) J L,
  0 < nu -> 0 < L ->
  SpectralEnergyPath lambda nu T Start u v0 E0 ->
  (forall i, (J <= i)%nat -> L <= lambda i*lambda i) ->
  forall N, omitted_time_prefix (fun _=>1) u 0 T HT Hu J N <=
    E0/(2*nu*L).
Proof.
  intros lambda nu T Start u v0 E0 HT Hu J L Hnu HL Hpath Hcoercive N.
  destruct (spectral_energy_dissipation_budget lambda nu T Start u v0 E0
    HT Hnu Hpath) as [D [HD [HDnonnegative HDbound]]].
  pose proof (coercive_omitted_time_bound lambda u 0 T HT Hu J L D
    HL Hcoercive HD N) as Htail.
  assert (Hquot : D/L <= (E0/(2*nu))/L).
  { unfold Rdiv. apply Rmult_le_compat_r.
    - left. apply Rinv_0_lt_compat. exact HL.
    - exact HDbound. }
  assert (Heq : (E0/(2*nu))/L = E0/(2*nu*L)) by (field; split; lra).
  rewrite Heq in Hquot. lra.
Qed.

Print Assumptions time_mode_multiply_identity.
Print Assumptions coercive_omitted_time_bound.
Print Assumptions spectral_energy_coercive_tail_budget.

Definition spectral_cutoff (J : nat) (u : R -> nat -> R) (t : R) (i : nat) : R :=
  if lt_dec i J then u t i else 0.

Definition cutoff_error (J : nat) (u : R -> nat -> R) (t : R) (i : nat) : R :=
  spectral_cutoff J u t i-u t i.

Lemma spectral_cutoff_continuous : forall J u a b,
  CoordinateContinuous u a b -> CoordinateContinuous (spectral_cutoff J u) a b.
Proof.
  intros J u a b Hu i. unfold spectral_cutoff.
  destruct (lt_dec i J); [apply Hu|apply continuous_const].
Qed.

Lemma cutoff_error_continuous : forall J u a b,
  CoordinateContinuous u a b -> CoordinateContinuous (cutoff_error J u) a b.
Proof.
  intros J u a b Hu i t Ht. unfold cutoff_error.
  apply continuity_pt_minus.
  - exact (spectral_cutoff_continuous J u a b Hu i t Ht).
  - apply Hu. exact Ht.
Qed.

Lemma cutoff_error_time_mode : forall w u a b Hab Hu J Herr i,
  time_mode w (cutoff_error J u) a b Hab Herr i =
  if lt_dec i J then 0 else time_mode w u a b Hab Hu i.
Proof.
  intros w u a b Hab Hu J Herr i. destruct (lt_dec i J) as [Hi|Hi].
  - unfold time_mode.
    transitivity (integral a b Hab (fun _ => 0) (continuous_const a b 0)).
    + apply integral_ext. intros t Ht. unfold cutoff_error, spectral_cutoff.
      destruct (lt_dec i J); [ring|contradiction].
    + rewrite integral_constant. ring.
  - unfold time_mode. apply integral_ext. intros t Ht.
    unfold cutoff_error, spectral_cutoff.
    destruct (lt_dec i J); [contradiction|ring].
Qed.

Theorem BKST10_CUTOFF_ERROR_IS_ACTUAL_OMITTED_TIME_ENERGY :
  forall w u a b Hab Hu J Herr N,
  time_prefix w (cutoff_error J u) a b Hab Herr N =
    omitted_time_prefix w u a b Hab Hu J N.
Proof.
  intros. unfold time_prefix, omitted_time_prefix.
  apply gp_sum_ext. intros i Hi. apply cutoff_error_time_mode.
Qed.

Lemma removed_prefix_below : forall f J N,
  (N <= J)%nat -> gp_sum N (fun i => if lt_dec i J then 0 else f i)=0.
Proof.
  intros f J N. induction N as [|N IH]; intro HNJ; simpl; [reflexivity|].
  rewrite IH by lia. destruct (lt_dec N J); [ring|lia].
Qed.

Lemma removed_prefix_gap : forall f J N,
  (J <= N)%nat -> gp_sum N (fun i => if lt_dec i J then 0 else f i)=
    gp_sum N f-gp_sum J f.
Proof.
  intros f J N HJN. induction HJN as [|N HJN IH].
  - rewrite removed_prefix_below by lia. ring.
  - simpl. destruct (lt_dec N J); [lia|]. rewrite IH. ring.
Qed.

Lemma removed_prefix_bound : forall f M J N,
  (forall L, gp_sum L f <= M) ->
  gp_sum N (fun i => if lt_dec i J then 0 else f i) <= M-gp_sum J f.
Proof.
  intros f M J N Hbound. destruct (Nat.le_ge_cases N J) as [HNJ|HJN].
  - rewrite removed_prefix_below by exact HNJ. specialize (Hbound J). lra.
  - rewrite removed_prefix_gap by exact HJN. specialize (Hbound N). lra.
Qed.

Theorem BKST11_CUTOFF_TIME_TAIL_FROM_TOTAL : forall w u a b Hab Hu J M,
  TimeTotal w u a b Hab Hu M ->
  TimeBound w (cutoff_error J u) a b Hab
    (cutoff_error_continuous J u a b Hu)
    (M-time_prefix w u a b Hab Hu J).
Proof.
  intros w u a b Hab Hu J M HM N.
  rewrite (BKST10_CUTOFF_ERROR_IS_ACTUAL_OMITTED_TIME_ENERGY
    w u a b Hab Hu J (cutoff_error_continuous J u a b Hu) N).
  unfold omitted_time_prefix, time_prefix. apply removed_prefix_bound.
  exact (proj1 HM).
Qed.

Definition StrongTimeCutoffs w u a b Hab (Hu : CoordinateContinuous u a b) : Prop :=
  forall eps, 0 < eps -> exists J0 : nat,
  forall J, (J0 <= J)%nat -> forall N,
  time_prefix w (cutoff_error J u) a b Hab
    (cutoff_error_continuous J u a b Hu) N < eps.

Theorem BKST12_FINITE_TIME_TOTAL_GIVES_STRONG_CUTOFFS :
  forall w u a b Hab Hu M,
  (forall i, 0 <= w i) -> TimeTotal w u a b Hab Hu M ->
  StrongTimeCutoffs w u a b Hab Hu.
Proof.
  intros w u a b Hab Hu M Hw HM eps Heps.
  destruct (TIME_PREFIX_CONVERGES_TO_TOTAL w u a b Hab Hu M Hw HM eps Heps)
    as [J0 HJ0]. exists J0. intros J HJ N.
  specialize (HJ0 J HJ). apply Rabs_def2 in HJ0. destruct HJ0.
  pose proof (BKST11_CUTOFF_TIME_TAIL_FROM_TOTAL w u a b Hab Hu J M HM N).
  lra.
Qed.

Lemma integral_order : forall a b Hab f g Hf Hg,
  (forall t, a <= t <= b -> f t <= g t) ->
  integral a b Hab f Hf <= integral a b Hab g Hg.
Proof.
  intros a b Hab f g Hf Hg Horder. unfold integral.
  apply RiemannInt_P19; [exact Hab|]. intros t Ht. apply Horder. lra.
Qed.

Theorem BKST13_POINTWISE_CAP_CONTROLS_TIME_ENERGY : forall u a b Hab Hu E,
  (forall t, a <= t <= b -> PhysicalBound (u t) E) ->
  TimeBound (fun _ => 1) u a b Hab Hu (E*(b-a)).
Proof.
  intros u a b Hab Hu E Hcap N.
  assert (Hprefix : ClosedContinuous
    (fun t => gp_sum N (fun i => 1*(u t i*u t i))) a b).
  { apply continuous_gp_sum. intro i. apply continuous_weighted_square. apply Hu. }
  rewrite (TIME_PREFIX_IS_RIEMANN_INTEGRAL
    (fun _=>1) u a b Hab Hu N Hprefix).
  rewrite <- (integral_constant a b Hab E (continuous_const a b E)).
  apply integral_order. intros t Ht.
  replace (gp_sum N (fun i => 1*(u t i*u t i))) with
    (physical_prefix (u t) N).
  - apply Hcap. exact Ht.
  - unfold physical_prefix. apply gp_sum_ext. intros i Hi. ring.
Qed.

Theorem BKST14_POINTWISE_CAP_GIVES_STRONG_TIME_CUTOFFS : forall u a b Hab Hu E,
  (forall t, a <= t <= b -> PhysicalBound (u t) E) ->
  StrongTimeCutoffs (fun _ => 1) u a b Hab Hu.
Proof.
  intros u a b Hab Hu E Hcap.
  destruct (time_total_exists (fun _=>1) u a b Hab Hu) as [M HM].
  - exists (E*(b-a)). apply BKST13_POINTWISE_CAP_CONTROLS_TIME_ENERGY. exact Hcap.
  - apply BKST12_FINITE_TIME_TOTAL_GIVES_STRONG_CUTOFFS with (M:=M).
    + intro i. lra.
    + exact HM.
Qed.

Theorem BKST20_DISSIPATION_CONTROLS_ACTUAL_CUTOFF_ERROR :
  forall lambda u a b Hab Hu J L D,
  0 < L -> (forall i, (J <= i)%nat -> L <= lambda i*lambda i) ->
  DissipationTotal lambda u a b Hab D ->
  TimeBound (fun _ => 1) (cutoff_error J u) a b Hab
    (cutoff_error_continuous J u a b Hu) (D/L).
Proof.
  intros lambda u a b Hab Hu J L D HL Hcoercive HD N.
  rewrite (BKST10_CUTOFF_ERROR_IS_ACTUAL_OMITTED_TIME_ENERGY
    (fun _=>1) u a b Hab Hu J (cutoff_error_continuous J u a b Hu) N).
  apply coercive_omitted_time_bound with (lambda := lambda); assumption.
Qed.

Theorem BKST15_ENERGY_PATH_GIVES_STRONG_TIME_CUTOFFS :
  forall lambda nu T Start u v0 E0 (HT : 0 <= T)
    (Hu : CoordinateContinuous u 0 T),
  0 <= nu -> SpectralEnergyPath lambda nu T Start u v0 E0 ->
  StrongTimeCutoffs (fun _=>1) u 0 T HT Hu.
Proof.
  intros lambda nu T Start u v0 E0 HT Hu Hnu Hpath.
  apply BKST14_POINTWISE_CAP_GIVES_STRONG_TIME_CUTOFFS with (E:=E0).
  exact (BKEP10_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP
    lambda nu T Start u v0 E0 Hnu Hpath).
Qed.

Theorem BKST21_ENERGY_PATH_CONTROLS_ACTUAL_CUTOFF_ERROR :
  forall lambda nu T Start u v0 E0 (HT : 0 <= T)
    (Hu : CoordinateContinuous u 0 T) J L,
  0 < nu -> 0 < L -> SpectralEnergyPath lambda nu T Start u v0 E0 ->
  (forall i, (J <= i)%nat -> L <= lambda i*lambda i) ->
  TimeBound (fun _=>1) (cutoff_error J u) 0 T HT
    (cutoff_error_continuous J u 0 T Hu) (E0/(2*nu*L)).
Proof.
  intros lambda nu T Start u v0 E0 HT Hu J L Hnu HL Hpath Hcoercive N.
  rewrite (BKST10_CUTOFF_ERROR_IS_ACTUAL_OMITTED_TIME_ENERGY
    (fun _=>1) u 0 T HT Hu J (cutoff_error_continuous J u 0 T Hu) N).
  apply spectral_energy_coercive_tail_budget with
    (lambda:=lambda) (Start:=Start) (v0:=v0); assumption.
Qed.

Definition SpectrallyCoercive (lambda : nat -> R) : Prop :=
  forall L, 0 < L -> exists J0 : nat,
    forall i, (J0 <= i)%nat -> L <= lambda i*lambda i.

(* One index works for every trajectory with the common dissipation budget.
   The cutoff index is independent of its coordinates and of the output
   prefix.  Coercivity is a concrete condition on the frequency sequence. *)
Theorem BKST22_UNIFORM_DISSIPATION_CUTOFF_CONVERGENCE :
  forall lambda a b (Hab : a <= b) D,
  0 <= D -> SpectrallyCoercive lambda ->
  forall eps, 0 < eps -> exists J0 : nat,
  forall u (Hu : CoordinateContinuous u a b) D' J,
  (J0 <= J)%nat -> DissipationTotal lambda u a b Hab D' -> D' <= D ->
  forall N, time_prefix (fun _=>1) (cutoff_error J u) a b Hab
    (cutoff_error_continuous J u a b Hu) N < eps.
Proof.
  intros lambda a b Hab D HD Hcoercive eps Heps.
  assert (HL : 0 < (D+1)/eps) by (apply Rdiv_lt_0_compat; lra).
  destruct (Hcoercive ((D+1)/eps) HL) as [J0 HJ0].
  exists J0. intros u Hu D' J HJ HD' HDcap N.
  assert (Htail : forall i, (J <= i)%nat -> (D+1)/eps <= lambda i*lambda i).
  { intros i Hi. apply HJ0. lia. }
  pose proof (BKST20_DISSIPATION_CONTROLS_ACTUAL_CUTOFF_ERROR
    lambda u a b Hab Hu J ((D+1)/eps) D' HL Htail HD' N) as Hbound.
  assert (Heq : (D'/((D+1)/eps))*((D+1)/eps)=D') by (field; lra).
  assert (Hepsprod : eps*((D+1)/eps)=D+1) by (field; lra).
  assert (Hsmall : D'/((D+1)/eps)<eps) by nra. lra.
Qed.

Print Assumptions BKST10_CUTOFF_ERROR_IS_ACTUAL_OMITTED_TIME_ENERGY.
Print Assumptions BKST12_FINITE_TIME_TOTAL_GIVES_STRONG_CUTOFFS.
Print Assumptions BKST13_POINTWISE_CAP_CONTROLS_TIME_ENERGY.
Print Assumptions BKST14_POINTWISE_CAP_GIVES_STRONG_TIME_CUTOFFS.
Print Assumptions BKST15_ENERGY_PATH_GIVES_STRONG_TIME_CUTOFFS.
Print Assumptions BKST20_DISSIPATION_CONTROLS_ACTUAL_CUTOFF_ERROR.
Print Assumptions BKST21_ENERGY_PATH_CONTROLS_ACTUAL_CUTOFF_ERROR.
Print Assumptions BKST22_UNIFORM_DISSIPATION_CUTOFF_CONVERGENCE.
End BKQR_SPECTRAL_TIME_TAIL.
