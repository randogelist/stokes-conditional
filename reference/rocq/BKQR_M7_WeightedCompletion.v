(* Completion of uniformly bounded weighted prefixes in the exact countable
   representation. No spatial operator or physical gradient is identified
   with the arbitrary nonnegative weights in this module. *)
From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_ClassificationAudit.
Require Import LHGP_Coordinates LHGP_Hilbert BKQR_LHGP_CoordinateBridge.

Module BKQR_M7_WEIGHTED_COMPLETION.
Module B := GP_COUNTABLE_RANGE.
Module S := BKQR_SHELL_COORDINATES.
Module C := BKQR_CLASSIFICATION.
Module H := LHGP_Hilbert.
Module D := LHGP_Coordinates.
Module G := BKQR_LHGP_COORDINATE_BRIDGE.
Open Scope R_scope.

Definition weighted_prefix (w a : nat -> R) (N : nat) : R :=
  B.gp_sum N (fun i => w i * a i * a i).
Definition weighted_vector (w a : nat -> R) (i : nat) : R :=
  sqrt (w i) * a i.
Definition WeightedTotal (w a : nat -> R) (M : R) : Prop :=
  (forall N, weighted_prefix w a N <= M) /\
  (forall E, (forall N, weighted_prefix w a N <= E) -> M <= E).

Theorem WEIGHTED_PREFIX_IS_PHYSICAL_PREFIX : forall w a,
  (forall i, 0 <= w i) -> forall N,
  weighted_prefix w a N = B.physical_prefix (weighted_vector w a) N.
Proof.
  intros w a Hw N. unfold weighted_prefix, B.physical_prefix, weighted_vector.
  apply B.gp_sum_ext. intros i Hi.
  pose proof (sqrt_def (w i) (Hw i)). nra.
Qed.

Theorem WEIGHTED_PREFIX_IS_HILBERT_NORM : forall hd
  (basis : H.OrthonormalBasis hd) w a,
  (forall i, 0 <= w i) -> forall N,
  H.HNorm hd (H.HFinite basis (weighted_vector w a) N) = weighted_prefix w a N.
Proof.
  intros hd basis w a Hw N. rewrite H.HFinite_norm, G.ENERGY_PREFIX_BRIDGE.
  symmetry. apply WEIGHTED_PREFIX_IS_PHYSICAL_PREFIX. exact Hw.
Qed.

Theorem WEIGHTED_PREFIX_NONNEGATIVE : forall w a,
  (forall i, 0 <= w i) -> forall N, 0 <= weighted_prefix w a N.
Proof.
  intros w a Hw N. unfold weighted_prefix. apply B.gp_sum_nonneg.
  intro i. replace (w i * a i * a i) with (w i * (a i * a i)) by ring.
  apply Rmult_le_pos; [apply Hw|nra].
Qed.

Theorem WEIGHTED_PREFIX_MONOTONE : forall w a,
  (forall i, 0 <= w i) -> forall N M,
  (N <= M)%nat -> weighted_prefix w a N <= weighted_prefix w a M.
Proof.
  intros w a Hw N M HNM. apply B.gp_sum_prefix_le; [|exact HNM].
  intro i. replace (w i * a i * a i) with (w i * (a i * a i)) by ring.
  apply Rmult_le_pos; [apply Hw|nra].
Qed.

Theorem WEIGHTED_TOTAL_IS_PHYSICAL_TOTAL : forall w a,
  (forall i, 0 <= w i) -> forall M,
  WeightedTotal w a M <-> B.PhysicalTotal (weighted_vector w a) M.
Proof.
  intros w a Hw M. unfold WeightedTotal, B.PhysicalTotal, B.PhysicalBound.
  split; intros [HM Hleast]; split.
  - intro N. rewrite <- WEIGHTED_PREFIX_IS_PHYSICAL_PREFIX by exact Hw. apply HM.
  - intros E HE. apply Hleast. intro N.
    rewrite WEIGHTED_PREFIX_IS_PHYSICAL_PREFIX by exact Hw. apply HE.
  - intro N. rewrite WEIGHTED_PREFIX_IS_PHYSICAL_PREFIX by exact Hw. apply HM.
  - intros E HE. apply Hleast. intro N.
    rewrite <- WEIGHTED_PREFIX_IS_PHYSICAL_PREFIX by exact Hw. apply HE.
Qed.

Theorem WEIGHTED_COMPLETION : forall w a Cbound,
  (forall i, 0 <= w i) ->
  (forall N, weighted_prefix w a N <= Cbound) ->
  exists M, 0 <= M <= Cbound /\ WeightedTotal w a M /\
    B.PhysicalTotal (weighted_vector w a) M.
Proof.
  intros w a Cbound Hw HC.
  assert (Hbound : B.PhysicalBound (weighted_vector w a) Cbound).
  { intro N. rewrite <- WEIGHTED_PREFIX_IS_PHYSICAL_PREFIX by exact Hw. apply HC. }
  destruct (B.physical_total_exists (weighted_vector w a)
    (ex_intro _ Cbound Hbound)) as [M HM].
  exists M. split.
  - split.
    + exact (proj1 HM 0%nat).
    + apply (proj2 HM). exact Hbound.
  - split; [apply (proj2 (WEIGHTED_TOTAL_IS_PHYSICAL_TOTAL w a Hw M))|]; exact HM.
Qed.

Theorem WEIGHTED_SHELL_COMPLETION : forall psi w a Cbound,
  B.ScalarPartition psi -> (forall i, 0 <= w i) ->
  (forall N, weighted_prefix w a N <= Cbound) ->
  exists M, 0 <= M <= Cbound /\ WeightedTotal w a M /\
    B.PhysicalTotal (weighted_vector w a) M /\
    B.ShellTotal (B.gp_encode psi (weighted_vector w a)) M.
Proof.
  intros psi w a Cbound Hpsi Hw HC.
  destruct (WEIGHTED_COMPLETION w a Cbound Hw HC) as [M [HM [Htotal Hphysical]]].
  exists M. split; [exact HM|]. split; [exact Htotal|].
  split; [exact Hphysical|].
  apply (proj1 (B.GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY psi
      (weighted_vector w a) (B.gp_encode psi (weighted_vector w a))
      Hpsi (fun k i => eq_refl) M)). exact Hphysical.
Qed.

Theorem WEIGHTED_PREFIX_CONVERGES_TO_TOTAL : forall w a M,
  (forall i, 0 <= w i) -> WeightedTotal w a M ->
  B.SeqLimit (weighted_prefix w a) M.
Proof.
  intros w a M Hw HM.
  assert (HE : D.EnergyValue (weighted_vector w a) M).
  { apply (proj2 (G.ENERGY_VALUE_BRIDGE _ _)).
    apply (proj1 (WEIGHTED_TOTAL_IS_PHYSICAL_TOTAL w a Hw M)). exact HM. }
  intros eps Heps.
  destruct (D.EnergyValue_prefix_converges _ _ HE eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  rewrite G.ENERGY_PREFIX_BRIDGE,
    <- WEIGHTED_PREFIX_IS_PHYSICAL_PREFIX in HN by exact Hw.
  apply Rabs_def1; lra.
Qed.

Theorem WEIGHTED_HILBERT_COMPLETION : forall hd
  (basis : H.OrthonormalBasis hd) psi w a Cbound,
  H.HComplete hd -> B.ScalarPartition psi ->
  (forall i, 0 <= w i) -> (forall N, weighted_prefix w a N <= Cbound) ->
  exists x : H.HCarrier hd,
    D.seq_eq (H.HAnalysis basis x) (weighted_vector w a) /\
    H.HConverges hd (H.HFinite basis (weighted_vector w a)) x /\
    0 <= H.HNorm hd x <= Cbound /\
    WeightedTotal w a (H.HNorm hd x) /\
    B.ShellTotal (B.gp_encode psi (weighted_vector w a)) (H.HNorm hd x).
Proof.
  intros hd basis psi w a Cbound Hcomplete Hpsi Hw HC.
  assert (HL2 : D.CoordinateL2 (weighted_vector w a)).
  { exists Cbound. intro N. rewrite G.ENERGY_PREFIX_BRIDGE,
      <- WEIGHTED_PREFIX_IS_PHYSICAL_PREFIX by exact Hw. apply HC. }
  destruct (H.HSynthesis_exists hd basis Hcomplete (weighted_vector w a) HL2)
    as [x [Hcoords [Hconv HE]]].
  assert (HP : B.PhysicalTotal (weighted_vector w a) (H.HNorm hd x)).
  { apply (proj1 (G.ENERGY_VALUE_BRIDGE _ _)). exact HE. }
  assert (HW : WeightedTotal w a (H.HNorm hd x)).
  { apply (proj2 (WEIGHTED_TOTAL_IS_PHYSICAL_TOTAL w a Hw _)). exact HP. }
  exists x. split; [exact Hcoords|]. split; [exact Hconv|]. split.
  - split; [apply H.HNorm_nonnegative|apply (proj2 HW); exact HC].
  - split; [exact HW|].
    apply (proj1 (B.GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY psi
      (weighted_vector w a) (B.gp_encode psi (weighted_vector w a))
      Hpsi (fun k i => eq_refl) (H.HNorm hd x))). exact HP.
Qed.

(* A least upper bound needs no monotonicity assumption. Therefore this
   generic completion is a supremum statement, not a sequential-limit claim. *)
Definition PrefixTotal (Dprefix : nat -> R) (M : R) : Prop :=
  (forall N, Dprefix N <= M) /\
  (forall E, (forall N, Dprefix N <= E) -> M <= E).

Theorem CUMULATIVE_PREFIX_TOTAL : forall Dprefix Cbound,
  Dprefix 0%nat = 0 -> (forall N, Dprefix N <= Cbound) ->
  exists M, 0 <= M <= Cbound /\ PrefixTotal Dprefix M.
Proof.
  intros Dprefix Cbound HD0 HC.
  set (values := fun r : R => exists N : nat, r = Dprefix N).
  assert (HB : bound values).
  { exists Cbound. intros r [N Hr]. rewrite Hr. apply HC. }
  assert (Hne : exists r, values r).
  { exists (Dprefix 0%nat). exists 0%nat. reflexivity. }
  destruct (completeness values HB Hne) as [M [Hupper Hleast]].
  assert (HM : PrefixTotal Dprefix M).
  { split.
    - intro N. apply Hupper. exists N. reflexivity.
    - intros E HE. apply Hleast. intros r [N Hr]. rewrite Hr. apply HE. }
  exists M. split; [|exact HM]. split.
  - rewrite <- HD0. apply (proj1 HM).
  - apply (proj2 HM). exact HC.
Qed.

Theorem PREFIX_TOTAL_UNIQUE : forall Dprefix M N,
  PrefixTotal Dprefix M -> PrefixTotal Dprefix N -> M = N.
Proof. intros Dprefix M N [HM HleastM] [HN HleastN].
  specialize (HleastM N HN). specialize (HleastN M HM). lra. Qed.

Theorem CUMULATIVE_NONNEGATIVE_COMPLETION : forall Dprefix Cbound,
  (forall N, 0 <= Dprefix N) -> (forall N, Dprefix N <= Cbound) ->
  exists M, 0 <= M <= Cbound /\ PrefixTotal Dprefix M.
Proof.
  intros Dprefix Cbound HD HC.
  set (values := fun r : R => exists N : nat, r = Dprefix N).
  assert (HB : bound values).
  { exists Cbound. intros r [N Hr]. rewrite Hr. apply HC. }
  assert (Hne : exists r, values r).
  { exists (Dprefix 0%nat). exists 0%nat. reflexivity. }
  destruct (completeness values HB Hne) as [M [Hupper Hleast]].
  assert (HM : PrefixTotal Dprefix M).
  { split.
    - intro N. apply Hupper. exists N. reflexivity.
    - intros E HE. apply Hleast. intros r [N Hr]. rewrite Hr. apply HE. }
  exists M. split; [|exact HM]. split.
  - eapply Rle_trans; [apply (HD 0%nat)|apply (proj1 HM)].
  - apply (proj2 HM). exact HC.
Qed.

Definition native_weighted_prefix (psi : nat -> nat -> R)
  (w : nat -> R) (U : nat -> nat -> R) (N : nat) : R :=
  B.gp_sum N (fun i =>
    w i * U 0%nat i * U 0%nat i / (psi 0%nat i * psi 0%nat i)).
Definition weight_shell (w : nat -> R) (U : nat -> nat -> R)
  (k i : nat) : R := sqrt (w i) * U k i.

Theorem NATIVE_WEIGHTED_PREFIX_IS_RECONSTRUCTED : forall psi w U,
  (forall i, psi 0%nat i <> 0) -> forall N,
  native_weighted_prefix psi w U N = weighted_prefix w (S.reconstruct psi U) N.
Proof.
  intros psi w U Hpsi N. unfold native_weighted_prefix, weighted_prefix, S.reconstruct.
  apply B.gp_sum_ext. intros i Hi. field. apply Hpsi.
Qed.

Section CanonicalProfile.
Variables q h : R.
Variable lambda : nat -> R.
Hypothesis Hq : 0 < q < 1.
Hypothesis Hh : 0 < h.
Hypothesis Hlambda : forall i, 0 <= lambda i.
Let psi := C.bkqr_weights q h lambda Hq Hh.

Theorem CANONICAL_WEIGHTED_SHELL_FACTORIZATION : forall w U,
  C.BKQRCompatible q h lambda U -> forall k i,
  weight_shell w U k i =
  B.gp_encode psi (weighted_vector w (S.reconstruct psi U)) k i.
Proof.
  intros w U HU k i. unfold weight_shell.
  rewrite (proj1 (C.BKCL11_RECONSTRUCTION_AND_UNIQUENESS
    q h lambda Hq Hh Hlambda U HU) k i).
  unfold C.J, C.R, B.gp_encode, weighted_vector, psi. ring.
Qed.

Theorem CANONICAL_NATIVE_WEIGHTED_COMPLETION : forall w U Cbound,
  (forall i, 0 <= w i) -> C.BKQRCompatible q h lambda U ->
  (forall N, native_weighted_prefix psi w U N <= Cbound) ->
  exists M, 0 <= M <= Cbound /\
    WeightedTotal w (S.reconstruct psi U) M /\
    B.PhysicalTotal (weighted_vector w (S.reconstruct psi U)) M /\
    B.ShellTotal (weight_shell w U) M.
Proof.
  intros w U Cbound Hw HU HC.
  assert (Hbound : forall N, weighted_prefix w (S.reconstruct psi U) N <= Cbound).
  { intro N. rewrite <- NATIVE_WEIGHTED_PREFIX_IS_RECONSTRUCTED.
    - apply HC.
    - apply C.BKCL02_ZERO_WEIGHT_NONZERO. }
  destruct (WEIGHTED_COMPLETION w (S.reconstruct psi U) Cbound Hw Hbound)
    as [M [HM [HW HP]]].
  exists M. split; [exact HM|]. split; [exact HW|]. split; [exact HP|].
  apply (proj1 (B.GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY psi
    (weighted_vector w (S.reconstruct psi U)) (weight_shell w U)
    (C.BKCL01_SCALAR_PARTITION q h lambda Hq Hh)
    (CANONICAL_WEIGHTED_SHELL_FACTORIZATION w U HU) M)). exact HP.
Qed.
End CanonicalProfile.

Print Assumptions WEIGHTED_COMPLETION.
Print Assumptions WEIGHTED_SHELL_COMPLETION.
Print Assumptions WEIGHTED_PREFIX_CONVERGES_TO_TOTAL.
Print Assumptions WEIGHTED_HILBERT_COMPLETION.
Print Assumptions CUMULATIVE_PREFIX_TOTAL.
Print Assumptions CUMULATIVE_NONNEGATIVE_COMPLETION.
Print Assumptions CANONICAL_NATIVE_WEIGHTED_COMPLETION.
End BKQR_M7_WEIGHTED_COMPLETION.
