From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import BKQR_CountableRange.

Module BKQR_SHELL_COORDINATES.
Import GP_COUNTABLE_RANGE.
Open Scope R_scope.

(* All indices range over N. There is no maximum shell or spectral cutoff.
   lambda is the diagonal symbol of L. For the physical torus application,
   a real Fourier basis and its identification with L2 still have to be built. *)
Definition AdjacentCompatible (lambda ell : nat -> R)
  (U : nat -> nat -> R) : Prop :=
  forall k i, lambda i * U k i = ell k * U (S k) i.

Definition ScalarRaising (psi : nat -> nat -> R)
  (lambda ell : nat -> R) : Prop :=
  forall k i, lambda i * psi k i = ell k * psi (S k) i.

Definition reconstruct (psi U : nat -> nat -> R) (i : nat) : R :=
  U 0%nat i / psi 0%nat i.

Definition SquareSummable (v : nat -> R) : Prop :=
  exists E, PhysicalBound v E.

Definition ShellSquareSummable (U : nat -> nat -> R) : Prop :=
  exists E, ShellBound U E.

Definition IntrinsicState (lambda ell : nat -> R)
  (U : nat -> nat -> R) : Prop :=
  AdjacentCompatible lambda ell U /\ ShellSquareSummable U.

Lemma BKSC01_ENCODE_ADJACENT : forall psi lambda ell v,
  ScalarRaising psi lambda ell ->
  AdjacentCompatible lambda ell (gp_encode psi v).
Proof.
  intros psi lambda ell v H k i.
  unfold gp_encode.
  replace (lambda i * (psi k i * v i))
    with ((lambda i * psi k i) * v i) by ring.
  rewrite (H k i). ring.
Qed.

Lemma BKSC02_RECONSTRUCT_ENCODE : forall psi v,
  (forall i, psi 0%nat i <> 0) ->
  forall i, reconstruct psi (gp_encode psi v) i = v i.
Proof.
  intros psi v H i. unfold reconstruct, gp_encode. field. apply H.
Qed.

(* The converse is derived from adjacency. It is not a field in the
   definition of a compatible state. Only the zeroth shell is divided by
   psi_0 here; bounded reconstruction follows from the full-energy theorem. *)
Theorem BKSC03_ADJACENCY_FORCES_FACTORIZATION : forall psi lambda ell U,
  ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) ->
  (forall k, ell k <> 0) ->
  AdjacentCompatible lambda ell U ->
  forall k i, U k i = gp_encode psi (reconstruct psi U) k i.
Proof.
  intros psi lambda ell U Hraise Hzero Hell Hcomp k.
  induction k as [|k IH]; intro i.
  - unfold gp_encode, reconstruct. field. apply Hzero.
  - apply (Rmult_eq_reg_l (ell k)).
    + rewrite <- (Hcomp k i). rewrite (IH i).
      unfold gp_encode.
      replace (lambda i * (psi k i * reconstruct psi U i))
        with ((lambda i * psi k i) * reconstruct psi U i) by ring.
      rewrite (Hraise k i). ring.
    + apply Hell.
Qed.

Theorem BKSC04_UNIQUE_REPRESENTATIVE : forall psi U v w,
  (forall i, psi 0%nat i <> 0) ->
  (forall k i, U k i = gp_encode psi v k i) ->
  (forall k i, U k i = gp_encode psi w k i) ->
  forall i, v i = w i.
Proof.
  intros psi U v w Hzero Hv Hw i.
  apply (Rmult_eq_reg_l (psi 0%nat i)); [|apply Hzero].
  change (gp_encode psi v 0%nat i = gp_encode psi w 0%nat i).
  rewrite <- (Hv 0%nat i), <- (Hw 0%nat i). reflexivity.
Qed.

Definition spectral_multiply (lambda v : nat -> R) (i : nat) : R :=
  lambda i * v i.

Definition shell_multiply (lambda : nat -> R)
  (U : nat -> nat -> R) (k i : nat) : R := lambda i * U k i.

Definition shell_shift (ell : nat -> R)
  (U : nat -> nat -> R) (k i : nat) : R := ell k * U (S k) i.

Lemma BKSC05_MULTIPLIER_INTERTWINING : forall psi lambda v k i,
  shell_multiply lambda (gp_encode psi v) k i =
  gp_encode psi (spectral_multiply lambda v) k i.
Proof. intros. unfold shell_multiply, gp_encode, spectral_multiply. ring. Qed.

Lemma BKSC06_SHIFT_IS_MULTIPLIER : forall lambda ell U,
  AdjacentCompatible lambda ell U ->
  forall k i, shell_shift ell U k i = shell_multiply lambda U k i.
Proof.
  intros lambda ell U H k i. unfold shell_shift, shell_multiply.
  symmetry. apply H.
Qed.

Theorem BKSC10_RECONSTRUCTION_PRESERVES_ALL_BOUNDS :
  forall psi lambda ell U,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  AdjacentCompatible lambda ell U ->
  forall E, PhysicalBound (reconstruct psi U) E <-> ShellBound U E.
Proof.
  intros psi lambda ell U Hp Hr H0 He HU E.
  apply GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY with (psi := psi).
  - exact Hp.
  - eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION; eassumption.
Qed.

(* Intrinsic membership only asserts adjacency and square summability.
   Existence of a represented square-summable vector is the conclusion. *)
Theorem BKSC11_EXACT_INTRINSIC_RANGE : forall psi lambda ell,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  forall U, IntrinsicState lambda ell U <->
    exists v, SquareSummable v /\
      forall k i, U k i = gp_encode psi v k i.
Proof.
  intros psi lambda ell Hp Hr H0 He U. split.
  - intros [HU [E HE]]. exists (reconstruct psi U). split.
    + exists E. apply (proj2 (BKSC10_RECONSTRUCTION_PRESERVES_ALL_BOUNDS
        psi lambda ell U Hp Hr H0 He HU E)). exact HE.
    + eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION; eassumption.
  - intros [v [[E HE] Hfactor]]. split.
    + intros k i. rewrite (Hfactor k i), (Hfactor (S k) i).
      exact (BKSC01_ENCODE_ADJACENT psi lambda ell v Hr k i).
    + exists E. apply (proj1 (GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY
        psi v U Hp Hfactor E)). exact HE.
Qed.

Theorem BKSC12_EXACT_TOTAL_ENERGY : forall psi lambda ell U,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  IntrinsicState lambda ell U ->
  exists M, PhysicalTotal (reconstruct psi U) M /\ ShellTotal U M.
Proof.
  intros psi lambda ell U Hp Hr H0 He [HU [E HE]].
  apply GPR80_SHARED_TOTAL_ENERGY_EXISTS with (psi := psi).
  - exact Hp.
  - eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION; eassumption.
  - exists E. apply (proj2 (BKSC10_RECONSTRUCTION_PRESERVES_ALL_BOUNDS
      psi lambda ell U Hp Hr H0 He HU E)). exact HE.
Qed.

Theorem BKSC13_EXACT_DISSIPATION_BOUNDS : forall psi lambda ell U,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  AdjacentCompatible lambda ell U ->
  forall D,
    PhysicalBound (spectral_multiply lambda (reconstruct psi U)) D <->
    ShellBound (shell_shift ell U) D.
Proof.
  intros psi lambda ell U Hp Hr H0 He HU D.
  apply GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY with (psi := psi).
  - exact Hp.
  - intros k i. rewrite (BKSC06_SHIFT_IS_MULTIPLIER lambda ell U HU k i).
    unfold shell_multiply.
    rewrite (BKSC03_ADJACENCY_FORCES_FACTORIZATION
      psi lambda ell U Hr H0 He HU k i).
    apply BKSC05_MULTIPLIER_INTERTWINING.
Qed.

Corollary BKSC14_DISSIPATION_DOMAIN_BOTH_DIRECTIONS :
  forall psi lambda ell U,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  AdjacentCompatible lambda ell U ->
  (SquareSummable (spectral_multiply lambda (reconstruct psi U)) <->
    ShellSquareSummable (shell_shift ell U)).
Proof.
  intros psi lambda ell U Hp Hr H0 He HU.
  split; intros [D HD]; exists D.
  - apply (proj1 (BKSC13_EXACT_DISSIPATION_BOUNDS
      psi lambda ell U Hp Hr H0 He HU D)). exact HD.
  - apply (proj2 (BKSC13_EXACT_DISSIPATION_BOUNDS
      psi lambda ell U Hp Hr H0 He HU D)). exact HD.
Qed.

Definition synthesis_partial (psi U : nat -> nat -> R)
  (K i : nat) : R := gp_sum K (fun k => psi k i * U k i).

Theorem BKSC15_COORDINATE_SYNTHESIS_CONVERGES : forall psi lambda ell U,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  AdjacentCompatible lambda ell U ->
  forall i, SeqLimit (fun K => synthesis_partial psi U K i)
    (reconstruct psi U i).
Proof.
  intros psi lambda ell U Hp Hr H0 He HU i.
  replace (reconstruct psi U i) with (reconstruct psi U i * 1) at 1 by ring.
  eapply limit_ext with
    (f := fun K => reconstruct psi U i * gp_sum K (fun k => psi k i * psi k i)).
  - intro K. unfold synthesis_partial. rewrite <- gp_sum_scale.
    apply gp_sum_ext. intros k Hk.
    rewrite (BKSC03_ADJACENCY_FORCES_FACTORIZATION
      psi lambda ell U Hr H0 He HU k i). unfold gp_encode. ring.
  - apply limit_scale. apply Hp.
Qed.

End BKQR_SHELL_COORDINATES.
