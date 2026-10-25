From Stdlib Require Import Reals Lra Psatz Lia Field Classical.
Require Import BKQR_CountableRange BKQR_ShellCoordinates.

Module BKQR_STRONG_SYNTHESIS.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES.
Open Scope R_scope.

(* Uniform bounds over every finite physical prefix express the squared
   ell2 norm.  Thus this is strong convergence of the infinite shell series,
   rather than convergence of each individual physical coordinate. *)
Definition StrongSynthesis (psi U : nat -> nat -> R) (v : nat -> R) : Prop :=
  forall eps : R, 0 < eps -> exists K0 : nat,
    forall K : nat, (K0 <= K)%nat -> forall N : nat,
    physical_prefix (fun i => synthesis_partial psi U K i - v i) N < eps.

Lemma gp_sum_zero : forall N, gp_sum N (fun _ => 0) = 0.
Proof. induction N; simpl; lra. Qed.

Lemma limit_difference_zero : forall f l,
  SeqLimit f l -> SeqLimit (fun n => f n-l) 0.
Proof.
  intros f l H eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. rewrite Rminus_0_r. apply HN. exact Hn.
Qed.

Lemma limit_square_zero : forall f,
  SeqLimit f 0 -> SeqLimit (fun n => f n*f n) 0.
Proof.
  intros f H eps Heps.
  assert (Hd : 0 < eps/(eps+1)) by (apply Rdiv_lt_0_compat; lra).
  assert (Heq : (eps/(eps+1))*(eps+1)=eps) by (field; lra).
  destruct (H (eps/(eps+1)) Hd) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  rewrite Rminus_0_r in HN. rewrite Rminus_0_r, Rabs_mult.
  assert (Hd1 : eps/(eps+1) < 1) by nra.
  assert (Hdeps : eps/(eps+1) < eps) by nra.
  pose proof (Rabs_pos (f n)).
  assert (Habs1 : Rabs (f n) < 1) by lra.
  assert (Hsq : Rabs (f n)*Rabs (f n) <= Rabs (f n)) by nra.
  lra.
Qed.

Lemma synthesis_encoded_formula : forall psi v K i,
  synthesis_partial psi (gp_encode psi v) K i =
  v i * gp_sum K (fun k => psi k i * psi k i).
Proof.
  intros. unfold synthesis_partial, gp_encode. rewrite <- gp_sum_scale.
  apply gp_sum_ext. intros. ring.
Qed.

Lemma encoded_coordinate_limit : forall psi v,
  ScalarPartition psi -> forall i,
  SeqLimit (fun K => synthesis_partial psi (gp_encode psi v) K i) (v i).
Proof.
  intros psi v Hp i.
  eapply limit_ext with
    (f := fun K => v i * gp_sum K (fun k => psi k i * psi k i)).
  - intro K. symmetry. apply synthesis_encoded_formula.
  - pose proof (limit_scale
      (fun K => gp_sum K (fun k => psi k i * psi k i))
      1 (v i) (Hp i)) as Hscaled.
    rewrite Rmult_1_r in Hscaled. exact Hscaled.
Qed.

Lemma encoded_error_prefix_limit : forall psi v,
  ScalarPartition psi -> forall N,
  SeqLimit (fun K => physical_prefix
    (fun i => synthesis_partial psi (gp_encode psi v) K i-v i) N) 0.
Proof.
  intros psi v Hp N. unfold physical_prefix.
  rewrite <- (gp_sum_zero N).
  apply limit_gp_sum. intro i. apply limit_square_zero.
  apply limit_difference_zero. apply encoded_coordinate_limit. exact Hp.
Qed.

Lemma encoded_error_dominated : forall psi v,
  ScalarPartition psi -> forall K i,
  (synthesis_partial psi (gp_encode psi v) K i-v i) *
    (synthesis_partial psi (gp_encode psi v) K i-v i) <= v i*v i.
Proof.
  intros psi v Hp K i. rewrite synthesis_encoded_formula.
  pose proof (partition_prefix_bounds psi Hp K i) as Hpart.
  set (p := gp_sum K (fun k => psi k i * psi k i)) in *.
  assert (Hq : (p-1)*(p-1) <= 1) by nra.
  assert (Hsq : 0 <= v i*v i) by nra.
  pose proof (Rmult_le_compat_l (v i*v i) ((p-1)*(p-1)) 1 Hsq Hq).
  nra.
Qed.

Lemma gp_sum_gap_le : forall a b J N,
  (forall i, a i <= b i) -> (J <= N)%nat ->
  gp_sum N a - gp_sum J a <= gp_sum N b - gp_sum J b.
Proof.
  intros a b J N Hab HJN. induction HJN as [|N HJN IH].
  - lra.
  - simpl. specialize (Hab N). lra.
Qed.

Lemma total_has_close_prefix : forall v M,
  PhysicalTotal v M -> forall eps, 0 < eps ->
  exists J, M-physical_prefix v J < eps.
Proof.
  intros v M [HM Hleast] eps Heps.
  destruct (classic (exists J, M-physical_prefix v J < eps))
    as [Hex|Hnone]; [exact Hex|].
  assert (Hsmaller : PhysicalBound v (M-eps)).
  { intro J. destruct (Rle_dec (physical_prefix v J) (M-eps));
      [assumption|]. exfalso. apply Hnone. exists J. lra. }
  specialize (Hleast (M-eps) Hsmaller). lra.
Qed.

(* Elementary dominated-sum estimate.  The tail of a dominated nonnegative
   sequence is paid by the tail of the genuine countable total energy. *)
Lemma dominated_prefix_tail : forall a v M J N,
  PhysicalBound v M -> (forall i, 0 <= a i <= v i*v i) ->
  gp_sum N a <= gp_sum J a + M-physical_prefix v J.
Proof.
  intros a v M J N HM Ha.
  destruct (Nat.le_ge_cases N J) as [HNJ|HJN].
  - assert (Hhead : gp_sum N a <= gp_sum J a).
    { apply gp_sum_prefix_le; [intro i; apply Ha|exact HNJ]. }
    specialize (HM J). lra.
  - assert (Hgap : gp_sum N a - gp_sum J a <=
        physical_prefix v N - physical_prefix v J).
    { unfold physical_prefix. apply gp_sum_gap_le; [intro i; apply Ha|exact HJN]. }
    specialize (HM N). lra.
Qed.

Theorem BKSS10_ENCODED_SYNTHESIS_CONVERGES_STRONGLY : forall psi v,
  ScalarPartition psi -> PhysicalSquareSummable v ->
  StrongSynthesis psi (gp_encode psi v) v.
Proof.
  intros psi v Hp Hv eps Heps.
  destruct (physical_total_exists v Hv) as [M HM].
  destruct (total_has_close_prefix v M HM (eps/2)) as [J Htail]; [lra|].
  destruct (encoded_error_prefix_limit psi v Hp J (eps/2))
    as [K0 HK0]; [lra|].
  exists K0. intros K HK N. specialize (HK0 K HK).
  rewrite Rminus_0_r in HK0. apply Rabs_def2 in HK0.
  destruct HK0 as [Hhead Hheadlower].
  assert (Hdom : forall i,
    0 <= (synthesis_partial psi (gp_encode psi v) K i-v i) *
      (synthesis_partial psi (gp_encode psi v) K i-v i) <= v i*v i).
  { intro i. split.
    - apply Rle_0_sqr.
    - apply encoded_error_dominated. exact Hp. }
  pose proof (dominated_prefix_tail
    (fun i => (synthesis_partial psi (gp_encode psi v) K i-v i) *
      (synthesis_partial psi (gp_encode psi v) K i-v i))
    v M J N (proj1 HM) Hdom) as Hbound.
  unfold physical_prefix in *. lra.
Qed.

Lemma synthesis_partial_ext : forall psi U V,
  (forall k i, U k i = V k i) -> forall K i,
  synthesis_partial psi U K i = synthesis_partial psi V K i.
Proof.
  intros psi U V H K i. unfold synthesis_partial.
  apply gp_sum_ext. intros k Hk. rewrite H. reflexivity.
Qed.

Theorem BKSS20_INTRINSIC_RECONSTRUCTION_IS_STRONG_SYNTHESIS :
  forall psi lambda ell U,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  IntrinsicState lambda ell U -> StrongSynthesis psi U (reconstruct psi U).
Proof.
  intros psi lambda ell U Hp Hr H0 He [HU [E HE]].
  assert (Hfactor : forall k i, U k i =
    gp_encode psi (reconstruct psi U) k i).
  { apply BKSC03_ADJACENCY_FORCES_FACTORIZATION with
      (lambda := lambda) (ell := ell); assumption. }
  assert (Hv : PhysicalSquareSummable (reconstruct psi U)).
  { exists E. apply (proj2 (BKSC10_RECONSTRUCTION_PRESERVES_ALL_BOUNDS
      psi lambda ell U Hp Hr H0 He HU E)). exact HE. }
  pose proof (BKSS10_ENCODED_SYNTHESIS_CONVERGES_STRONGLY
    psi (reconstruct psi U) Hp Hv) as Hstrong.
  intros eps Heps. destruct (Hstrong eps Heps) as [K0 HK0].
  exists K0. intros K HK N.
  assert (Herr : physical_prefix
      (fun i => synthesis_partial psi U K i-reconstruct psi U i) N =
      physical_prefix (fun i => synthesis_partial psi
        (gp_encode psi (reconstruct psi U)) K i-reconstruct psi U i) N).
  { unfold physical_prefix. apply gp_sum_ext. intros i Hi.
    rewrite (synthesis_partial_ext psi U
      (gp_encode psi (reconstruct psi U)) Hfactor K i). reflexivity. }
  rewrite Herr. apply HK0. exact HK.
Qed.

Print Assumptions BKSS10_ENCODED_SYNTHESIS_CONVERGES_STRONGLY.
Print Assumptions BKSS20_INTRINSIC_RECONSTRUCTION_IS_STRONG_SYNTHESIS.
End BKQR_STRONG_SYNTHESIS.
