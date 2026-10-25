From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_StrongSynthesis.

Module BKQR_INITIAL_TRACE.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_STRONG_SYNTHESIS.
Open Scope R_scope.

Definition StrongSeqLimit (X : nat -> nat -> R) (v : nat -> R) : Prop :=
  forall eps, 0 < eps -> exists n0, forall n, (n0 <= n)%nat ->
    PhysicalBound (fun i => X n i-v i) eps.

Definition StrongShellSeqLimit (X : nat -> nat -> nat -> R)
  (V : nat -> nat -> R) : Prop :=
  forall eps, 0 < eps -> exists n0, forall n, (n0 <= n)%nat ->
    ShellBound (fun k i => X n k i-V k i) eps.

Lemma sum_add : forall N f g,
  gp_sum N (fun i => f i+g i) = gp_sum N f+gp_sum N g.
Proof. induction N; intros; simpl; [ring|rewrite IHN; ring]. Qed.

Lemma limit_square_at : forall f l,
  SeqLimit f l -> SeqLimit (fun n => f n*f n) (l*l).
Proof.
  intros f l H.
  pose proof (limit_difference_zero f l H) as Hd.
  pose proof (limit_square_zero (fun n => f n-l) Hd) as Hs.
  pose proof (limit_scale (fun n => f n-l) 0 (2*l) Hd) as Hc.
  pose proof (limit_plus _ _ _ _ Hs Hc) as Ha.
  intros eps He. destruct (Ha eps He) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  replace (f n*f n-l*l) with
    ((f n-l)*(f n-l)+2*l*(f n-l)-(0+2*l*0)) by ring. exact HN.
Qed.

Lemma coordinate_limit_energy_head : forall X v,
  (forall i, SeqLimit (fun n => X n i) (v i)) -> forall J,
  SeqLimit (fun n => physical_prefix (X n) J) (physical_prefix v J).
Proof.
  intros X v H J. unfold physical_prefix.
  apply limit_gp_sum. intro i. apply limit_square_at. apply H.
Qed.

Lemma coordinate_limit_error_head : forall X v,
  (forall i, SeqLimit (fun n => X n i) (v i)) -> forall J,
  SeqLimit (fun n => physical_prefix (fun i => X n i-v i) J) 0.
Proof.
  intros X v H J. unfold physical_prefix. rewrite <- (gp_sum_zero J).
  apply limit_gp_sum. intro i. apply limit_square_zero.
  apply limit_difference_zero. apply H.
Qed.

(* The two tails can be estimated using energy caps, independently of any
   convergence of the total energies along X. *)
Lemma difference_tail_bound : forall x v E F J N,
  PhysicalBound x E -> PhysicalBound v F ->
  physical_prefix (fun i => x i-v i) N <=
  physical_prefix (fun i => x i-v i) J +
    2*(E-physical_prefix x J)+2*(F-physical_prefix v J).
Proof.
  intros x v E F J N Hx Hv.
  destruct (Nat.le_ge_cases N J) as [HNJ|HJN].
  - assert (Hmono : physical_prefix (fun i => x i-v i) N <=
        physical_prefix (fun i => x i-v i) J).
    { unfold physical_prefix. apply gp_sum_prefix_le;
        [intro i; apply Rle_0_sqr|exact HNJ]. }
    specialize (Hx J). specialize (Hv J). lra.
  - pose proof (gp_sum_gap_le
      (fun i => (x i-v i)*(x i-v i))
      (fun i => 2*(x i*x i+v i*v i)) J N
      (ltac:(intro i; pose proof (Rle_0_sqr (x i+v i)); unfold Rsqr in *; nra)) HJN) as Hgap.
    repeat rewrite gp_sum_scale in Hgap.
    repeat rewrite sum_add in Hgap.
    specialize (Hx N). specialize (Hv N). unfold physical_prefix in *. lra.
Qed.

(* This is the energy-cap argument at the initial time. Coordinate weak
   convergence together with the true initial total energy forces strong
   convergence. Strong continuity at other times is not assumed. *)
Theorem BKIT10_INITIAL_ENERGY_CAP_FORCES_STRONG_TRACE : forall X v E,
  PhysicalTotal v E -> (forall n, PhysicalBound (X n) E) ->
  (forall i, SeqLimit (fun n => X n i) (v i)) -> StrongSeqLimit X v.
Proof.
  intros X v E Hv HX Hcoord eps He.
  destruct (total_has_close_prefix v E Hv (eps/16)) as [J Htail]; [lra|].
  destruct (coordinate_limit_energy_head X v Hcoord J (eps/16))
    as [N1 H1]; [lra|].
  destruct (coordinate_limit_error_head X v Hcoord J (eps/4))
    as [N2 H2]; [lra|].
  exists (Nat.max N1 N2). intros n Hn N.
  specialize (H1 n (ltac:(lia))). specialize (H2 n (ltac:(lia))).
  apply Rabs_def2 in H1. apply Rabs_def2 in H2.
  destruct H1 as [H1u H1l]. destruct H2 as [H2u H2l].
  pose proof (difference_tail_bound (X n) v E E J N (HX n) (proj1 Hv)).
  lra.
Qed.

Theorem BKIT11_STRONG_TRACE_TRANSPORT : forall psi X v U V,
  ScalarPartition psi ->
  (forall n k i, U n k i = gp_encode psi (X n) k i) ->
  (forall k i, V k i = gp_encode psi v k i) ->
  (StrongSeqLimit X v <-> StrongShellSeqLimit U V).
Proof.
  intros psi X v U V Hp HU HV.
  assert (Hbounds : forall n E,
    PhysicalBound (fun i => X n i-v i) E <->
      ShellBound (fun k i => U n k i-V k i) E).
  { intros n E. apply GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY with (psi := psi).
    - exact Hp.
    - intros k i. rewrite HU, HV. unfold gp_encode. ring. }
  split; intros H eps He; destruct (H eps He) as [N HN]; exists N;
    intros n Hn.
  - apply (proj1 (Hbounds n eps)). apply HN. exact Hn.
  - apply (proj2 (Hbounds n eps)). apply HN. exact Hn.
Qed.

Theorem BKIT12_NATIVE_INITIAL_ENERGY_CAP_FORCES_STRONG_TRACE :
  forall psi lambda ell U V E,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  (forall n, AdjacentCompatible lambda ell (U n)) ->
  AdjacentCompatible lambda ell V -> ShellTotal V E ->
  (forall n, ShellBound (U n) E) ->
  (forall k i, SeqLimit (fun n => U n k i) (V k i)) ->
  StrongShellSeqLimit U V.
Proof.
  intros psi lambda ell U V E Hp Hr H0 He HU HV HVE HUE Hlim.
  assert (Hfactor : forall n k i, U n k i =
      gp_encode psi (reconstruct psi (U n)) k i).
  { intro n. eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION; eauto. }
  assert (HfactorV : forall k i, V k i = gp_encode psi (reconstruct psi V) k i).
  { eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION; eauto. }
  apply (proj1 (BKIT11_STRONG_TRACE_TRANSPORT psi
    (fun n => reconstruct psi (U n)) (reconstruct psi V) U V Hp Hfactor HfactorV)).
  apply BKIT10_INITIAL_ENERGY_CAP_FORCES_STRONG_TRACE with (E := E).
  - apply (proj2 (GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY
      psi (reconstruct psi V) V Hp HfactorV E)). exact HVE.
  - intro n. apply (proj2 (BKSC10_RECONSTRUCTION_PRESERVES_ALL_BOUNDS
      psi lambda ell (U n) Hp Hr H0 He (HU n) E)). apply HUE.
  - intro i. unfold reconstruct.
    pose proof (limit_scale (fun n => U n 0%nat i) (V 0%nat i)
      (/psi 0%nat i) (Hlim 0%nat i)) as H.
    unfold SeqLimit in *. intros eps Heps. destruct (H eps Heps) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn).
    replace (U n 0%nat i / psi 0%nat i - V 0%nat i / psi 0%nat i)
      with (/psi 0%nat i * U n 0%nat i - /psi 0%nat i * V 0%nat i)
      by (unfold Rdiv; ring).
    exact HN.
Qed.

End BKQR_INITIAL_TRACE.
