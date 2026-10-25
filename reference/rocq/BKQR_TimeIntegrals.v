From Stdlib Require Import Reals RiemannInt Lra Psatz Lia Classical.
Require Import BKQR_CountableRange.

(* Actual Riemann integration of continuous scalar spectral coordinates.
   Countable nonnegative totals are least upper bounds of finite integrated
   prefixes.  No integral is supplied as an abstract operation or premise.
   Continuity at interval endpoints is ordinary two-sided continuity of an
   R-domain representative.  Relative endpoint continuity needs a continuous
   extension adapter.  Identification with a physical Fourier realization
   and its Lebesgue dissipation is outside this module. *)
Module BKQR_TIME_INTEGRALS.
Import GP_COUNTABLE_RANGE.
Open Scope R_scope.

Definition ClosedContinuous (f : R -> R) (a b : R) : Prop :=
  forall t, a <= t <= b -> continuity_pt f t.
Definition CoordinateContinuous (u : R -> nat -> R) (a b : R) : Prop :=
  forall i, ClosedContinuous (fun t => u t i) a b.
Definition ShellCoordinateContinuous (U : R -> nat -> nat -> R)
  (a b : R) : Prop :=
  forall k i, ClosedContinuous (fun t => U t k i) a b.

Lemma continuous_const : forall a b c,
  ClosedContinuous (fun _ => c) a b.
Proof.
  intros a b c t Ht. apply continuity_pt_const. intros x y. reflexivity.
Qed.

Lemma continuous_plus : forall a b f g,
  ClosedContinuous f a b -> ClosedContinuous g a b ->
  ClosedContinuous (fun t => f t + g t) a b.
Proof.
  intros a b f g Hf Hg t Ht.
  apply continuity_pt_plus; [apply Hf|apply Hg]; exact Ht.
Qed.

Lemma continuous_scale : forall a b c f,
  ClosedContinuous f a b -> ClosedContinuous (fun t => c * f t) a b.
Proof.
  intros a b c f Hf t Ht. apply continuity_pt_scal. apply Hf. exact Ht.
Qed.

Lemma continuous_weighted_square : forall a b c f,
  ClosedContinuous f a b ->
  ClosedContinuous (fun t => c * (f t * f t)) a b.
Proof.
  intros a b c f Hf. apply continuous_scale. intros t Ht.
  apply continuity_pt_mult; apply Hf; exact Ht.
Qed.

Lemma continuous_gp_sum : forall a b N (f : nat -> R -> R),
  (forall i, ClosedContinuous (f i) a b) ->
  ClosedContinuous (fun t => gp_sum N (fun i => f i t)) a b.
Proof.
  intros a b N. induction N as [|N IH]; intros f Hf; simpl.
  - apply continuous_const.
  - apply continuous_plus; [apply IH|apply Hf]. exact Hf.
Qed.

Definition integral a b (Hab : a <= b) f
  (Hf : ClosedContinuous f a b) : R :=
  RiemannInt (@continuity_implies_RiemannInt f a b Hab Hf).

Lemma integral_ext : forall a b Hab f g Hf Hg,
  (forall t, a <= t <= b -> f t = g t) ->
  integral a b Hab f Hf = integral a b Hab g Hg.
Proof.
  intros a b Hab f g Hf Hg Heq. unfold integral.
  apply RiemannInt_P18; [exact Hab|]. intros t Ht. apply Heq. lra.
Qed.

Lemma integral_proof_independent : forall a b Hab Hab' f Hf Hf',
  integral a b Hab f Hf = integral a b Hab' f Hf'.
Proof. intros. unfold integral. apply RiemannInt_P5. Qed.

Lemma integral_constant : forall a b Hab c Hc,
  integral a b Hab (fun _ => c) Hc = c * (b-a).
Proof. intros. unfold integral. apply RiemannInt_P15. Qed.

Lemma integral_linear : forall a b Hab f g c Hf Hg Hsum,
  integral a b Hab (fun t => f t + c * g t) Hsum =
  integral a b Hab f Hf + c * integral a b Hab g Hg.
Proof. intros. unfold integral. apply RiemannInt_P13. Qed.

Lemma integral_scale : forall a b Hab f c Hf Hscaled,
  integral a b Hab (fun t => c * f t) Hscaled =
  c * integral a b Hab f Hf.
Proof.
  intros a b Hab f c Hf Hscaled.
  pose proof (continuous_plus a b (fun _ => 0) (fun t => c*f t)
    (continuous_const a b 0) Hscaled) as Hsum.
  transitivity (integral a b Hab (fun t => 0+c*f t) Hsum).
  - apply integral_ext. intros. ring.
  - rewrite (integral_linear a b Hab (fun _ => 0) f c
      (continuous_const a b 0) Hf Hsum).
    rewrite integral_constant. ring.
Qed.

Lemma integral_nonnegative : forall a b Hab f Hf,
  (forall t, a <= t <= b -> 0 <= f t) ->
  0 <= integral a b Hab f Hf.
Proof.
  intros a b Hab f Hf Hpos. unfold integral.
  pose proof (@RiemannInt_P19 (fct_cte 0) f a b
    (RiemannInt_P14 a b 0)
    (@continuity_implies_RiemannInt f a b Hab Hf) Hab) as H.
  assert (Horder : forall t, a < t < b -> fct_cte 0 t <= f t).
  { intros t Ht. apply Hpos. lra. }
  specialize (H Horder). rewrite RiemannInt_P15 in H. lra.
Qed.

Lemma integral_gp_sum : forall a b Hab N (f : nat -> R -> R)
  (Hf : forall i, ClosedContinuous (f i) a b) Hsum,
  integral a b Hab (fun t => gp_sum N (fun i => f i t)) Hsum =
  gp_sum N (fun i => integral a b Hab (f i) (Hf i)).
Proof.
  intros a b Hab N. induction N as [|N IH]; intros f Hf Hsum.
  - simpl. rewrite integral_constant. ring.
  - pose proof (continuous_gp_sum a b N f Hf) as Hprefix.
    pose proof (continuous_plus a b
      (fun t => gp_sum N (fun i => f i t)) (fun t => 1*f N t)
      Hprefix (continuous_scale a b 1 (f N) (Hf N))) as Hlinear.
    transitivity (integral a b Hab
      (fun t => gp_sum N (fun i => f i t)+1*f N t) Hlinear).
    + apply integral_ext. intros. simpl. ring.
    + rewrite (integral_linear a b Hab
        (fun t => gp_sum N (fun i => f i t)) (f N) 1
        Hprefix (Hf N) Hlinear).
      rewrite (IH f Hf Hprefix). simpl. ring.
Qed.

Definition time_mode (w : nat -> R) (u : R -> nat -> R)
  a b (Hab : a <= b) (Hu : CoordinateContinuous u a b) i : R :=
  integral a b Hab (fun t => w i * (u t i * u t i))
    (continuous_weighted_square a b (w i) (fun t => u t i) (Hu i)).

Definition time_prefix w u a b Hab Hu N : R :=
  gp_sum N (fun i => time_mode w u a b Hab Hu i).

Definition shell_time_mode (w : nat -> R) (U : R -> nat -> nat -> R)
  a b (Hab : a <= b) (HU : ShellCoordinateContinuous U a b) k i : R :=
  integral a b Hab (fun t => w i * (U t k i * U t k i))
    (continuous_weighted_square a b (w i) (fun t => U t k i) (HU k i)).

Definition shell_time_rectangle w U a b Hab HU K N : R :=
  gp_sum N (fun i => gp_sum K
    (fun k => shell_time_mode w U a b Hab HU k i)).

Lemma time_mode_nonnegative : forall w u a b Hab Hu,
  (forall i, 0 <= w i) -> forall i, 0 <= time_mode w u a b Hab Hu i.
Proof.
  intros w u a b Hab Hu Hw i. unfold time_mode.
  apply integral_nonnegative. intros. apply Rmult_le_pos; [apply Hw|nra].
Qed.

Lemma time_mode_ext : forall w u v a b Hab Hu Hv,
  (forall t i, a <= t <= b -> u t i = v t i) ->
  forall i, time_mode w u a b Hab Hu i = time_mode w v a b Hab Hv i.
Proof.
  intros w u v a b Hab Hu Hv Heq i. unfold time_mode.
  apply integral_ext. intros t Ht. rewrite Heq by exact Ht. reflexivity.
Qed.

Lemma time_prefix_ext : forall w u v a b Hab Hu Hv,
  (forall t i, a <= t <= b -> u t i = v t i) ->
  forall N, time_prefix w u a b Hab Hu N = time_prefix w v a b Hab Hv N.
Proof.
  intros w u v a b Hab Hu Hv Heq N. unfold time_prefix.
  apply gp_sum_ext. intros i Hi. apply time_mode_ext. exact Heq.
Qed.

Lemma shell_time_rectangle_ext : forall w U V a b Hab HU HV,
  (forall t k i, a <= t <= b -> U t k i = V t k i) ->
  forall K N, shell_time_rectangle w U a b Hab HU K N =
    shell_time_rectangle w V a b Hab HV K N.
Proof.
  intros w U V a b Hab HU HV Heq K N. unfold shell_time_rectangle.
  apply gp_sum_ext. intros i Hi. apply gp_sum_ext. intros k Hk.
  unfold shell_time_mode. apply integral_ext. intros t Ht.
  rewrite Heq by exact Ht. reflexivity.
Qed.

Theorem TIME_PREFIX_IS_RIEMANN_INTEGRAL : forall w u a b Hab Hu N Hprefix,
  time_prefix w u a b Hab Hu N =
  integral a b Hab (fun t => gp_sum N (fun i => w i*(u t i*u t i))) Hprefix.
Proof.
  intros w u a b Hab Hu N Hprefix. unfold time_prefix, time_mode.
  symmetry. apply integral_gp_sum.
Qed.

Theorem TIME_RECTANGLE_IS_RIEMANN_INTEGRAL :
  forall w U a b Hab HU K N Hrectangle,
  shell_time_rectangle w U a b Hab HU K N =
  integral a b Hab
    (fun t => gp_sum N (fun i => gp_sum K (fun k => w i*(U t k i*U t k i))))
    Hrectangle.
Proof.
  intros w U a b Hab HU K N Hrectangle.
  assert (Hinner : forall i, ClosedContinuous
    (fun t => gp_sum K (fun k => w i*(U t k i*U t k i))) a b).
  { intro i. apply continuous_gp_sum. intro k.
    apply continuous_weighted_square. apply HU. }
  rewrite (integral_gp_sum a b Hab N
    (fun i t => gp_sum K (fun k => w i*(U t k i*U t k i))) Hinner Hrectangle).
  unfold shell_time_rectangle. apply gp_sum_ext. intros i Hi.
  unfold shell_time_mode. symmetry. apply integral_gp_sum.
Qed.

Lemma shell_encode_continuous : forall psi u a b,
  CoordinateContinuous u a b ->
  ShellCoordinateContinuous (fun t k i => psi k i * u t i) a b.
Proof.
  intros psi u a b Hu k i. apply continuous_scale. apply Hu.
Qed.

Lemma shell_time_mode_factor : forall psi w u U a b Hab Hu HU,
  (forall t k i, a <= t <= b -> U t k i = psi k i * u t i) ->
  forall k i, shell_time_mode w U a b Hab HU k i =
    (psi k i * psi k i) * time_mode w u a b Hab Hu i.
Proof.
  intros psi w u U a b Hab Hu HU Hfactor k i.
  unfold shell_time_mode, time_mode.
  set (f := fun t => w i*(u t i*u t i)).
  pose proof (continuous_weighted_square a b (w i)
    (fun t => u t i) (Hu i)) as Hf.
  pose proof (continuous_scale a b (psi k i*psi k i) f Hf) as Hscaled.
  transitivity (integral a b Hab
    (fun t => (psi k i*psi k i)*f t) Hscaled).
  - apply integral_ext. intros t Ht. rewrite Hfactor by exact Ht.
    unfold f. ring.
  - apply integral_scale.
Qed.

Lemma shell_time_rectangle_formula : forall psi w u U a b Hab Hu HU,
  (forall t k i, a <= t <= b -> U t k i = psi k i*u t i) ->
  forall K N, shell_time_rectangle w U a b Hab HU K N =
    gp_sum N (fun i => time_mode w u a b Hab Hu i *
      gp_sum K (fun k => psi k i*psi k i)).
Proof.
  intros psi w u U a b Hab Hu HU Hfactor K N.
  unfold shell_time_rectangle. apply gp_sum_ext. intros i Hi.
  rewrite <- gp_sum_scale. apply gp_sum_ext. intros k Hk.
  rewrite (shell_time_mode_factor psi w u U a b Hab Hu HU Hfactor k i).
  ring.
Qed.

Lemma shell_time_rectangle_limit : forall psi w u U a b Hab Hu HU,
  ScalarPartition psi ->
  (forall t k i, a <= t <= b -> U t k i = psi k i*u t i) ->
  forall N, SeqLimit (fun K => shell_time_rectangle w U a b Hab HU K N)
    (time_prefix w u a b Hab Hu N).
Proof.
  intros psi w u U a b Hab Hu HU Hpart Hfactor N.
  eapply limit_ext.
  - intro K. symmetry. apply (shell_time_rectangle_formula
      psi w u U a b Hab Hu HU Hfactor).
  - unfold time_prefix. apply limit_gp_sum. intro i.
    pose proof (limit_scale
      (fun K => gp_sum K (fun k => psi k i*psi k i)) 1
      (time_mode w u a b Hab Hu i) (Hpart i)) as H.
    rewrite Rmult_1_r in H. exact H.
Qed.

Definition TimeBound w u a b Hab Hu E : Prop :=
  forall N, time_prefix w u a b Hab Hu N <= E.
Definition ShellTimeBound w U a b Hab HU E : Prop :=
  forall K N, shell_time_rectangle w U a b Hab HU K N <= E.

Theorem TIME_PARTITION_PRESERVES_ALL_BOUNDS :
  forall psi w u U a b Hab Hu HU,
  ScalarPartition psi -> (forall i, 0 <= w i) ->
  (forall t k i, a <= t <= b -> U t k i = psi k i*u t i) ->
  forall E, TimeBound w u a b Hab Hu E <-> ShellTimeBound w U a b Hab HU E.
Proof.
  intros psi w u U a b Hab Hu HU Hpart Hw Hfactor E. split.
  - intros Hbound K N.
    rewrite (shell_time_rectangle_formula psi w u U a b Hab Hu HU Hfactor).
    eapply Rle_trans; [|apply Hbound]. unfold time_prefix.
    apply gp_sum_le. intros i Hi.
    pose proof (partition_prefix_bounds psi Hpart K i).
    pose proof (time_mode_nonnegative w u a b Hab Hu Hw i). nra.
  - intros Hbound N. eapply limit_upper_bound.
    + apply (shell_time_rectangle_limit psi w u U a b Hab Hu HU Hpart Hfactor).
    + intro K. apply Hbound.
Qed.

Definition TimeTotal w u a b Hab Hu M : Prop :=
  TimeBound w u a b Hab Hu M /\
  forall E, TimeBound w u a b Hab Hu E -> M <= E.
Definition ShellTimeTotal w U a b Hab HU M : Prop :=
  ShellTimeBound w U a b Hab HU M /\
  forall E, ShellTimeBound w U a b Hab HU E -> M <= E.

Theorem TIME_PARTITION_PRESERVES_TOTAL :
  forall psi w u U a b Hab Hu HU,
  ScalarPartition psi -> (forall i, 0 <= w i) ->
  (forall t k i, a <= t <= b -> U t k i = psi k i*u t i) ->
  forall M, TimeTotal w u a b Hab Hu M <-> ShellTimeTotal w U a b Hab HU M.
Proof.
  intros psi w u U a b Hab Hu HU Hpart Hw Hfactor M.
  assert (Hb : forall E, TimeBound w u a b Hab Hu E <->
    ShellTimeBound w U a b Hab HU E).
  { apply (TIME_PARTITION_PRESERVES_ALL_BOUNDS psi w u U a b Hab Hu HU
      Hpart Hw Hfactor). }
  split; intros [Hbound Hleast]; split.
  - apply (proj1 (Hb M)). exact Hbound.
  - intros E HE. apply Hleast. apply (proj2 (Hb E)). exact HE.
  - apply (proj2 (Hb M)). exact Hbound.
  - intros E HE. apply Hleast. apply (proj1 (Hb E)). exact HE.
Qed.

Lemma time_total_exists : forall w u a b Hab Hu,
  (exists E, TimeBound w u a b Hab Hu E) ->
  exists M, TimeTotal w u a b Hab Hu M.
Proof.
  intros w u a b Hab Hu [E HE].
  set (values := fun r : R => exists N : nat,
    r = time_prefix w u a b Hab Hu N).
  assert (Hbound : bound values).
  { exists E. intros r [N Hr]. rewrite Hr. apply HE. }
  assert (Hnonempty : exists r, values r).
  { exists 0. exists O. reflexivity. }
  destruct (completeness values Hbound Hnonempty) as [M [Hupper Hleast]].
  exists M. split.
  - intro N. apply Hupper. exists N. reflexivity.
  - intros F HF. apply Hleast. intros r [N Hr]. rewrite Hr. apply HF.
Qed.

Lemma time_total_unique : forall w u a b Hab Hu M N,
  TimeTotal w u a b Hab Hu M -> TimeTotal w u a b Hab Hu N -> M=N.
Proof.
  intros w u a b Hab Hu M N [HM Hmin] [HN Hnin].
  specialize (Hmin N HN). specialize (Hnin M HM). lra.
Qed.

Definition time_values w u a b Hab Hu : R -> Prop :=
  fun r => exists N, r = time_prefix w u a b Hab Hu N.

Lemma time_values_bounded : forall w u a b Hab Hu,
  (exists E, TimeBound w u a b Hab Hu E) ->
  bound (time_values w u a b Hab Hu).
Proof.
  intros w u a b Hab Hu [E HE]. exists E.
  intros r [N Hr]. rewrite Hr. apply HE.
Qed.

Lemma time_values_nonempty : forall w u a b Hab Hu,
  exists r, time_values w u a b Hab Hu r.
Proof. intros. exists 0. exists O. reflexivity. Qed.

(* This is a real number selected by the standard real completeness theorem,
   not a supplied summation functional.  Its argument records finiteness. *)
Definition time_total_value w u a b Hab Hu
  (Hfinite : exists E, TimeBound w u a b Hab Hu E) : R :=
  proj1_sig (completeness (time_values w u a b Hab Hu)
    (time_values_bounded w u a b Hab Hu Hfinite)
    (time_values_nonempty w u a b Hab Hu)).

Theorem TIME_TOTAL_VALUE_SPEC : forall w u a b Hab Hu Hfinite,
  TimeTotal w u a b Hab Hu (time_total_value w u a b Hab Hu Hfinite).
Proof.
  intros w u a b Hab Hu Hfinite. unfold time_total_value.
  destruct (completeness (time_values w u a b Hab Hu)
    (time_values_bounded w u a b Hab Hu Hfinite)
    (time_values_nonempty w u a b Hab Hu)) as [M [Hupper Hleast]].
  simpl. split.
  - intro N. apply Hupper. exists N. reflexivity.
  - intros E HE. apply Hleast. intros r [N Hr]. rewrite Hr. apply HE.
Qed.

Theorem TIME_PREFIX_CONVERGES_TO_TOTAL : forall w u a b Hab Hu M,
  (forall i, 0 <= w i) -> TimeTotal w u a b Hab Hu M ->
  SeqLimit (fun N => time_prefix w u a b Hab Hu N) M.
Proof.
  intros w u a b Hab Hu M Hw [Hupper Hleast] eps Heps.
  assert (Hnear : exists N, M-eps < time_prefix w u a b Hab Hu N).
  { apply NNPP. intro Hnot.
    assert (Hlower : TimeBound w u a b Hab Hu (M-eps)).
    { intro N. destruct (Rle_dec (time_prefix w u a b Hab Hu N) (M-eps))
        as [Hle|Hgt]; [exact Hle|].
      exfalso. apply Hnot. exists N. lra. }
    specialize (Hleast (M-eps) Hlower). lra. }
  destruct Hnear as [N HN]. exists N. intros n Hn.
  assert (Hmono : time_prefix w u a b Hab Hu N <=
    time_prefix w u a b Hab Hu n).
  { unfold time_prefix. apply gp_sum_prefix_le; [|exact Hn].
    intro i. apply time_mode_nonnegative. exact Hw. }
  specialize (Hupper n). apply Rabs_def1; lra.
Qed.

Theorem TIME_SHARED_TOTAL_EXISTS : forall psi w u U a b Hab Hu HU,
  ScalarPartition psi -> (forall i, 0 <= w i) ->
  (forall t k i, a <= t <= b -> U t k i = psi k i*u t i) ->
  (exists E, TimeBound w u a b Hab Hu E) ->
  exists M, TimeTotal w u a b Hab Hu M /\ ShellTimeTotal w U a b Hab HU M.
Proof.
  intros psi w u U a b Hab Hu HU Hpart Hw Hfactor Hfinite.
  destruct (time_total_exists w u a b Hab Hu Hfinite) as [M HM].
  exists M. split; [exact HM|].
  apply (proj1 (TIME_PARTITION_PRESERVES_TOTAL psi w u U a b Hab Hu HU
    Hpart Hw Hfactor M)). exact HM.
Qed.

Print Assumptions integral_gp_sum.
Print Assumptions TIME_PARTITION_PRESERVES_ALL_BOUNDS.
Print Assumptions TIME_PARTITION_PRESERVES_TOTAL.
Print Assumptions TIME_SHARED_TOTAL_EXISTS.
End BKQR_TIME_INTEGRALS.
