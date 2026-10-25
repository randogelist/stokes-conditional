(* Countable GP energy transport.  The scalar partition law is an explicit
   analytic premise.  No concrete q-product, PDE realization, or finite-cut
   replacement of the countable range is asserted in this file. *)
From Stdlib Require Import Reals Lra Psatz Lia Field.

Module GP_COUNTABLE_RANGE.
Open Scope R_scope.

Fixpoint gp_sum (n : nat) (f : nat -> R) : R :=
  match n with O => 0 | S m => gp_sum m f + f m end.

Definition SeqLimit (f : nat -> R) (l : R) : Prop :=
  forall eps : R, 0 < eps -> exists N : nat,
    forall n : nat, (N <= n)%nat -> Rabs (f n - l) < eps.

Definition ScalarPartition (psi : nat -> nat -> R) : Prop :=
  forall i, SeqLimit
    (fun K => gp_sum K (fun k => psi k i * psi k i)) 1.

Definition gp_encode (psi : nat -> nat -> R) (v : nat -> R)
  (k i : nat) : R := psi k i * v i.
Definition physical_prefix (v : nat -> R) (N : nat) : R :=
  gp_sum N (fun i => v i * v i).
Definition shell_rectangle (U : nat -> nat -> R) (K N : nat) : R :=
  gp_sum N (fun i => gp_sum K (fun k => U k i * U k i)).
Definition PhysicalBound (v : nat -> R) (E : R) : Prop :=
  forall N, physical_prefix v N <= E.
Definition ShellBound (U : nat -> nat -> R) (E : R) : Prop :=
  forall K N, shell_rectangle U K N <= E.

Lemma gp_sum_ext : forall n f g,
  (forall i, (i < n)%nat -> f i = g i) -> gp_sum n f = gp_sum n g.
Proof.
  induction n as [|n IH]; intros f g H; simpl; [reflexivity|].
  rewrite (IH f g) by (intros; apply H; lia).
  rewrite H by lia. reflexivity.
Qed.

Lemma gp_sum_nonneg : forall n f,
  (forall i, 0 <= f i) -> 0 <= gp_sum n f.
Proof.
  induction n as [|n IH]; intros f H; simpl; [lra|].
  specialize (IH f H). specialize (H n). lra.
Qed.

Lemma gp_sum_le : forall n f g,
  (forall i, (i < n)%nat -> f i <= g i) -> gp_sum n f <= gp_sum n g.
Proof.
  induction n as [|n IH]; intros f g H; simpl; [lra|].
  assert (H0 : gp_sum n f <= gp_sum n g).
  { apply IH. intros. apply H. lia. }
  assert (H1 : f n <= g n) by (apply H; lia). lra.
Qed.

Lemma gp_sum_scale : forall n c f,
  gp_sum n (fun i => c * f i) = c * gp_sum n f.
Proof.
  induction n as [|n IH]; intros c f; simpl; [ring|].
  rewrite IH. ring.
Qed.

Lemma gp_sum_prefix_le : forall f m n,
  (forall i, 0 <= f i) -> (m <= n)%nat -> gp_sum m f <= gp_sum n f.
Proof.
  intros f m n Hpos Hmn. induction Hmn.
  - lra.
  - simpl. specialize (Hpos m0). lra.
Qed.

Lemma limit_ext : forall f g l,
  (forall n, f n = g n) -> SeqLimit f l -> SeqLimit g l.
Proof.
  intros f g l Hfg H eps Heps.
  destruct (H eps Heps) as [N HN]. exists N. intros n Hn.
  rewrite <- Hfg. apply HN. exact Hn.
Qed.

Lemma limit_const : forall c, SeqLimit (fun _ => c) c.
Proof.
  intros c eps Heps. exists O. intros n Hn.
  replace (c - c) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

Lemma limit_plus : forall f g a b,
  SeqLimit f a -> SeqLimit g b ->
  SeqLimit (fun n => f n + g n) (a + b).
Proof.
  intros f g a b Hf Hg eps Heps.
  destruct (Hf (eps/2)) as [N HN]; [lra|].
  destruct (Hg (eps/2)) as [M HM]; [lra|].
  exists (Nat.max N M). intros n Hn.
  assert (HNn : (N <= n)%nat) by lia.
  assert (HMn : (M <= n)%nat) by lia.
  specialize (HN n HNn). specialize (HM n HMn).
  apply Rabs_def2 in HN. apply Rabs_def2 in HM.
  destruct HN; destruct HM. apply Rabs_def1; lra.
Qed.

Lemma limit_scale : forall f l c,
  SeqLimit f l -> SeqLimit (fun n => c * f n) (c * l).
Proof.
  intros f l c H eps Heps.
  pose proof (Rabs_pos c) as Hc.
  assert (Hd : 0 < Rabs c + 1) by lra.
  assert (Hdelta : 0 < eps / (Rabs c + 1)).
  { apply Rdiv_lt_0_compat; assumption. }
  destruct (H (eps / (Rabs c + 1)) Hdelta) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  replace (c * f n - c * l) with (c * (f n - l)) by ring.
  rewrite Rabs_mult.
  assert (Heq : (Rabs c + 1) * (eps / (Rabs c + 1)) = eps).
  { field. lra. }
  pose proof (Rabs_pos (f n - l)). nra.
Qed.

Lemma limit_gp_sum : forall N (f : nat -> nat -> R) (l : nat -> R),
  (forall i, SeqLimit (fun n => f n i) (l i)) ->
  SeqLimit (fun n => gp_sum N (f n)) (gp_sum N l).
Proof.
  induction N as [|N IH]; intros f l H; simpl.
  - apply limit_const.
  - apply limit_plus.
    + apply IH. exact H.
    + apply H.
Qed.

Lemma limit_upper_bound : forall f l E,
  SeqLimit f l -> (forall n, f n <= E) -> l <= E.
Proof.
  intros f l E H Hupper.
  destruct (Rle_dec l E) as [Hle|Hnot]; [exact Hle|].
  assert (Heps : 0 < (l - E)/2) by lra.
  destruct (H ((l-E)/2) Heps) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  apply Rabs_def2 in HN. destruct HN.
  specialize (Hupper N). lra.
Qed.

Lemma monotone_limit_upper : forall f l,
  (forall m n, (m <= n)%nat -> f m <= f n) -> SeqLimit f l ->
  forall m, f m <= l.
Proof.
  intros f l Hmono Hlim m.
  destruct (Rle_dec (f m) l) as [Hle|Hnot]; [exact Hle|].
  assert (Heps : 0 < (f m-l)/2) by lra.
  destruct (Hlim ((f m-l)/2) Heps) as [N HN].
  assert (Hm : (m <= Nat.max m N)%nat) by lia.
  assert (HNmax : (N <= Nat.max m N)%nat) by lia.
  specialize (HN (Nat.max m N) HNmax).
  specialize (Hmono m (Nat.max m N) Hm).
  apply Rabs_def2 in HN. destruct HN. lra.
Qed.

Lemma partition_prefix_bounds : forall psi,
  ScalarPartition psi -> forall K i,
  0 <= gp_sum K (fun k => psi k i * psi k i) <= 1.
Proof.
  intros psi H K i. split.
  - apply gp_sum_nonneg. intro k. nra.
  - apply (monotone_limit_upper
      (fun n => gp_sum n (fun k => psi k i * psi k i)) 1).
    + intros m n Hmn. apply gp_sum_prefix_le; [intro k; nra|exact Hmn].
    + apply H.
Qed.

Lemma encode_rectangle_formula : forall psi v K N,
  shell_rectangle (gp_encode psi v) K N =
  gp_sum N (fun i => (v i * v i) *
    gp_sum K (fun k => psi k i * psi k i)).
Proof.
  intros psi v K N. unfold shell_rectangle, gp_encode.
  apply gp_sum_ext. intros i Hi. rewrite <- gp_sum_scale.
  apply gp_sum_ext. intros k Hk. ring.
Qed.

Lemma encoded_rectangle_limit : forall psi v,
  ScalarPartition psi -> forall N,
  SeqLimit (fun K => shell_rectangle (gp_encode psi v) K N)
    (physical_prefix v N).
Proof.
  intros psi v H N.
  eapply limit_ext.
  - intro K. symmetry. apply encode_rectangle_formula.
  - unfold physical_prefix. apply limit_gp_sum. intro i.
    pose proof (limit_scale
      (fun K => gp_sum K (fun k => psi k i * psi k i))
      1 (v i * v i) (H i)) as Hscaled.
    rewrite Rmult_1_r in Hscaled. exact Hscaled.
Qed.

Theorem GPR40_PARTITION_PRESERVES_ALL_ENERGY_BOUNDS : forall psi,
  ScalarPartition psi -> forall v E,
  PhysicalBound v E <-> ShellBound (gp_encode psi v) E.
Proof.
  intros psi Hpart v E. split.
  - intros Hv K N. rewrite encode_rectangle_formula.
    eapply Rle_trans; [|apply Hv]. unfold physical_prefix.
    apply gp_sum_le. intros i Hi.
    pose proof (partition_prefix_bounds psi Hpart K i) as Hweights.
    assert (Hsq : 0 <= v i * v i) by nra. nra.
  - intros HU N. eapply limit_upper_bound.
    + apply encoded_rectangle_limit. exact Hpart.
    + intro K. apply HU.
Qed.

Lemma shell_rectangle_ext : forall U V,
  (forall k i, U k i = V k i) ->
  forall K N, shell_rectangle U K N = shell_rectangle V K N.
Proof.
  intros U V H K N. unfold shell_rectangle.
  apply gp_sum_ext. intros i Hi.
  apply gp_sum_ext. intros k Hk. rewrite H. reflexivity.
Qed.

Theorem GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY : forall psi v U,
  ScalarPartition psi ->
  (forall k i, U k i = gp_encode psi v k i) ->
  forall E, PhysicalBound v E <-> ShellBound U E.
Proof.
  intros psi v U Hpart Hfactor E.
  pose proof (GPR40_PARTITION_PRESERVES_ALL_ENERGY_BOUNDS
    psi Hpart v E) as Hbounds.
  split.
  - intro Hv. destruct Hbounds as [Hforward Hback].
    specialize (Hforward Hv). intros K N.
    rewrite (shell_rectangle_ext U (gp_encode psi v) Hfactor K N).
    apply Hforward.
  - intro HU. destruct Hbounds as [Hforward Hback].
    apply Hback. intros K N.
    rewrite <- (shell_rectangle_ext U (gp_encode psi v) Hfactor K N).
    apply HU.
Qed.

Definition PhysicalSquareSummable (v : nat -> R) : Prop :=
  exists E, PhysicalBound v E.
Definition ShellSquareSummable (U : nat -> nat -> R) : Prop :=
  exists E, ShellBound U E.

Corollary GPR60_COUNTABLE_SQUARE_SUMMABILITY : forall psi v U,
  ScalarPartition psi ->
  (forall k i, U k i = gp_encode psi v k i) ->
  (PhysicalSquareSummable v <-> ShellSquareSummable U).
Proof.
  intros psi v U Hpart Hfactor. split; intros [E HE]; exists E.
  - apply (proj1 (GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY
      psi v U Hpart Hfactor E)). exact HE.
  - apply (proj2 (GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY
      psi v U Hpart Hfactor E)). exact HE.
Qed.

(* Total energies are least upper bounds of all finite prefixes/rectangles;
   these are actual countable sums of nonnegative squares. *)
Definition PhysicalTotal (v : nat -> R) (M : R) : Prop :=
  PhysicalBound v M /\ forall E, PhysicalBound v E -> M <= E.
Definition ShellTotal (U : nat -> nat -> R) (M : R) : Prop :=
  ShellBound U M /\ forall E, ShellBound U E -> M <= E.

Theorem GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY : forall psi v U,
  ScalarPartition psi ->
  (forall k i, U k i = gp_encode psi v k i) ->
  forall M, PhysicalTotal v M <-> ShellTotal U M.
Proof.
  intros psi v U Hpart Hfactor M.
  assert (Hb : forall E, PhysicalBound v E <-> ShellBound U E).
  { apply GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY with (psi := psi);
      assumption. }
  split; intros [Hbound Hleast]; split.
  - apply (proj1 (Hb M)). exact Hbound.
  - intros E HE. apply Hleast. apply (proj2 (Hb E)). exact HE.
  - apply (proj2 (Hb M)). exact Hbound.
  - intros E HE. apply Hleast. apply (proj1 (Hb E)). exact HE.
Qed.

Lemma physical_total_exists : forall v,
  PhysicalSquareSummable v -> exists M, PhysicalTotal v M.
Proof.
  intros v [E HE].
  set (values := fun r : R => exists N : nat, r = physical_prefix v N).
  assert (Hbound : bound values).
  { exists E. intros r [N Hr]. rewrite Hr. apply HE. }
  assert (Hnonempty : exists r, values r).
  { exists 0. exists O. reflexivity. }
  destruct (completeness values Hbound Hnonempty) as [M [Hupper Hleast]].
  exists M. split.
  - intro N. apply Hupper. exists N. reflexivity.
  - intros F HF. apply Hleast. intros r [N Hr]. rewrite Hr. apply HF.
Qed.

Lemma physical_total_unique : forall v M N,
  PhysicalTotal v M -> PhysicalTotal v N -> M = N.
Proof.
  intros v M N [HM Hmin] [HN Hnin].
  specialize (Hmin N HN). specialize (Hnin M HM). lra.
Qed.

Lemma shell_total_unique : forall U M N,
  ShellTotal U M -> ShellTotal U N -> M = N.
Proof.
  intros U M N [HM Hmin] [HN Hnin].
  specialize (Hmin N HN). specialize (Hnin M HM). lra.
Qed.

Theorem GPR80_SHARED_TOTAL_ENERGY_EXISTS : forall psi v U,
  ScalarPartition psi ->
  (forall k i, U k i = gp_encode psi v k i) ->
  PhysicalSquareSummable v ->
  exists M, PhysicalTotal v M /\ ShellTotal U M.
Proof.
  intros psi v U Hpart Hfactor Hv.
  destruct (physical_total_exists v Hv) as [M HM].
  exists M. split; [exact HM|].
  apply (proj1 (GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY
    psi v U Hpart Hfactor M)). exact HM.
Qed.

Print Assumptions GPR40_PARTITION_PRESERVES_ALL_ENERGY_BOUNDS.
Print Assumptions GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY.
Print Assumptions GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY.
Print Assumptions GPR80_SHARED_TOTAL_ENERGY_EXISTS.
End GP_COUNTABLE_RANGE.
