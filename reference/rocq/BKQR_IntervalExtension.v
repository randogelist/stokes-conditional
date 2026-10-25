From Stdlib Require Import Reals Lra Psatz.
Require Import BKQR_TimeIntegrals BKQR_PathTopology.

(* An explicit continuous extension closes the distinction between relative
   continuity on a closed interval and Stdlib's two-sided continuity_pt.
   No stronger endpoint regularity is required. *)
Module BKQR_INTERVAL_EXTENSION.
Import BKQR_TIME_INTEGRALS BKQR_PATH_TOPOLOGY.
Open Scope R_scope.

Definition RelativeClosedContinuous (f : R -> R) (a b : R) : Prop :=
  ScalarContinuousOn (fun t => a <= t <= b) f.

Lemma relative_continuity_restrict_interval : forall D f a b,
  ScalarContinuousOn D f ->
  (forall t, a <= t <= b -> D t) -> RelativeClosedContinuous f a b.
Proof.
  intros D f a b Hf HD t Ht eps Heps.
  destruct (Hf t (HD t Ht) eps Heps) as [delta [Hdelta Hcontrol]].
  exists delta. split; [exact Hdelta|]. intros s Hs Hdist.
  apply Hcontrol; [apply HD; exact Hs|exact Hdist].
Qed.

Definition clamp (a b t : R) : R := Rmax a (Rmin b t).

Lemma clamp_range : forall a b, a <= b -> forall t,
  a <= clamp a b t <= b.
Proof.
  intros a b Hab t. unfold clamp. split.
  - apply Rmax_l.
  - apply Rmax_lub; [exact Hab|apply Rmin_l].
Qed.

Lemma clamp_inside : forall a b t, a <= t <= b -> clamp a b t=t.
Proof.
  intros a b t [Hat Htb]. unfold clamp.
  rewrite Rmin_right by exact Htb. rewrite Rmax_right by exact Hat.
  reflexivity.
Qed.

Lemma clamp_idempotent : forall a b, a <= b -> forall t,
  clamp a b (clamp a b t)=clamp a b t.
Proof. intros. apply clamp_inside. apply clamp_range. exact H. Qed.

Theorem CLAMP_ONE_LIPSCHITZ : forall a b x y,
  Rabs (clamp a b x-clamp a b y) <= Rabs (x-y).
Proof.
  intros a b x y.
  pose proof (Rle_abs (x-y)) as Hpos.
  pose proof (Rle_abs (-(x-y))) as Hneg.
  rewrite Rabs_Ropp in Hneg.
  pose proof (Rabs_pos (x-y)) as Hnonneg.
  unfold clamp, Rmax, Rmin.
  repeat match goal with
    | H : context [Rle_dec ?r ?s] |- _ => destruct (Rle_dec r s)
    | |- context [Rle_dec ?r ?s] => destruct (Rle_dec r s)
  end; apply Rabs_le; split; lra.
Qed.

Definition interval_extension a b (f : R -> R) (t : R) : R :=
  f (clamp a b t).

Lemma interval_extension_agrees : forall a b f t,
  a <= t <= b -> interval_extension a b f t=f t.
Proof. intros. unfold interval_extension. rewrite clamp_inside by exact H. reflexivity. Qed.

Theorem INTERVAL_RELATIVE_CONTINUITY_HAS_CONTINUOUS_EXTENSION :
  forall a b, a <= b -> forall f,
  RelativeClosedContinuous f a b ->
  forall x, continuity_pt (interval_extension a b f) x.
Proof.
  intros a b Hab f Hf x.
  unfold continuity_pt, continue_in, limit1_in, limit_in.
  intros eps Heps.
  destruct (Hf (clamp a b x) (clamp_range a b Hab x) eps Heps)
    as [delta [Hdelta Hcontrol]].
  exists delta. split; [exact Hdelta|].
  intros y [Hy Hdist].
  change (Rabs (y-x) < delta) in Hdist.
  change (Rabs (f (clamp a b y)-f (clamp a b x)) < eps).
  apply Hcontrol; [apply clamp_range; exact Hab|].
  eapply Rle_lt_trans; [apply CLAMP_ONE_LIPSCHITZ|exact Hdist].
Qed.

Corollary interval_extension_closed_continuous : forall a b (Hab : a <= b) f,
  RelativeClosedContinuous f a b ->
  ClosedContinuous (interval_extension a b f) a b.
Proof.
  intros a b Hab f Hf t Ht.
  apply INTERVAL_RELATIVE_CONTINUITY_HAS_CONTINUOUS_EXTENSION; assumption.
Qed.

Definition coordinate_extension a b (u : R -> nat -> R) t i : R :=
  u (clamp a b t) i.
Definition shell_extension a b (U : R -> nat -> nat -> R) t k i : R :=
  U (clamp a b t) k i.

Theorem INTERVAL_COORDINATE_EXTENSION : forall a b, a <= b -> forall u,
  (forall i, RelativeClosedContinuous (fun t => u t i) a b) ->
  CoordinateContinuous (coordinate_extension a b u) a b /\
  (forall t i, a <= t <= b -> coordinate_extension a b u t i=u t i).
Proof.
  intros a b Hab u Hu. split.
  - intros i t Ht. unfold coordinate_extension.
    apply (INTERVAL_RELATIVE_CONTINUITY_HAS_CONTINUOUS_EXTENSION
      a b Hab (fun s => u s i) (Hu i) t).
  - intros t i Ht. unfold coordinate_extension. rewrite clamp_inside by exact Ht.
    reflexivity.
Qed.

Corollary INTERVAL_COORDINATE_EXTENSION_FROM_DOMAIN :
  forall D a b, a <= b -> forall u,
  CoordinateContinuousOn D u -> (forall t, a <= t <= b -> D t) ->
  CoordinateContinuous (coordinate_extension a b u) a b.
Proof.
  intros D a b Hab u Hu HD.
  apply (proj1 (INTERVAL_COORDINATE_EXTENSION a b Hab u
    (fun i => relative_continuity_restrict_interval
      D (fun t => u t i) a b (Hu i) HD))).
Qed.

Theorem INTERVAL_SHELL_EXTENSION : forall a b, a <= b -> forall U,
  (forall k i, RelativeClosedContinuous (fun t => U t k i) a b) ->
  ShellCoordinateContinuous (shell_extension a b U) a b /\
  (forall t k i, a <= t <= b -> shell_extension a b U t k i=U t k i).
Proof.
  intros a b Hab U HU. split.
  - intros k i t Ht. unfold shell_extension.
    apply (INTERVAL_RELATIVE_CONTINUITY_HAS_CONTINUOUS_EXTENSION
      a b Hab (fun s => U s k i) (HU k i) t).
  - intros t k i Ht. unfold shell_extension. rewrite clamp_inside by exact Ht.
    reflexivity.
Qed.

Theorem INTERVAL_EXTENSION_PRESERVES_FACTORIZATION :
  forall psi u U a b, a <= b ->
  (forall t k i, a <= t <= b -> U t k i=psi k i*u t i) ->
  forall t k i, shell_extension a b U t k i=
    psi k i*coordinate_extension a b u t i.
Proof.
  intros psi u U a b Hab Hfactor t k i.
  unfold shell_extension, coordinate_extension.
  apply Hfactor. apply clamp_range. exact Hab.
Qed.

(* Different extensions yield the same actual integrals on the interval.
   This follows from interval agreement, without proof irrelevance or any
   assumption about values outside the interval. *)
Theorem TIME_PREFIX_EXTENSION_INDEPENDENT :
  forall w u v a b Hab Hu Hv,
  (forall t i, a <= t <= b -> u t i=v t i) ->
  forall N, time_prefix w u a b Hab Hu N=time_prefix w v a b Hab Hv N.
Proof. exact time_prefix_ext. Qed.

Print Assumptions CLAMP_ONE_LIPSCHITZ.
Print Assumptions INTERVAL_RELATIVE_CONTINUITY_HAS_CONTINUOUS_EXTENSION.
Print Assumptions INTERVAL_COORDINATE_EXTENSION.
Print Assumptions INTERVAL_SHELL_EXTENSION.
Print Assumptions INTERVAL_EXTENSION_PRESERVES_FACTORIZATION.
End BKQR_INTERVAL_EXTENSION.
