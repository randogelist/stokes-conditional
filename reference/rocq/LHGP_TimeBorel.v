From Stdlib Require Import Reals Lra Psatz Lia Arith.Compare_dec Classical_Prop.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_WeakTopology.

Open Scope R_scope.

(* A relative Borel sigma algebra is generated from genuine epsilon-delta
   open sets. No measurability or closure laws are assumed as model fields.
   Ordinary classical logic is used explicitly for set complements. *)

Definition InInterval (T t : R) : Prop := 0 <= t <= T.

Definition TimeOpen (T : R) (A : R -> Prop) : Prop :=
  forall t, InInterval T t -> A t -> exists delta,
    0 < delta /\ forall s, InInterval T s -> Rabs (s - t) < delta -> A s.

Definition TimeClosed (T : R) (A : R -> Prop) : Prop :=
  TimeOpen T (fun t => ~ A t).

Inductive TimeBorel (T : R) : (R -> Prop) -> Prop :=
| TB_open : forall A, TimeOpen T A -> TimeBorel T A
| TB_complement : forall A, TimeBorel T A -> TimeBorel T (fun t => ~ A t)
| TB_union : forall A : nat -> R -> Prop,
    (forall n, TimeBorel T (A n)) -> TimeBorel T (fun t => exists n, A n t)
| TB_ext : forall A B, TimeBorel T A ->
    (forall t, InInterval T t -> (A t <-> B t)) -> TimeBorel T B.

Definition ScalarBorelOn (T : R) (f : R -> R) : Prop :=
  forall c, TimeBorel T (fun t => f t < c).

Lemma TimeBorel_all : forall T, TimeBorel T (fun _ => True).
Proof.
  intro T. apply TB_open. intros t Ht HA.
  exists 1. split; [lra | intros; exact I].
Qed.

Lemma TimeBorel_empty : forall T, TimeBorel T (fun _ => False).
Proof. intro T. apply TB_open. intros t Ht Hfalse. contradiction. Qed.

Lemma TB_closed : forall T A, TimeClosed T A -> TimeBorel T A.
Proof.
  intros T A Hclosed.
  eapply TB_ext with (A := fun t => ~ ~ A t).
  - apply TB_complement. apply TB_open. exact Hclosed.
  - intros t Ht. tauto.
Qed.

Lemma TimeBorel_union : forall T A B,
  TimeBorel T A -> TimeBorel T B ->
  TimeBorel T (fun t => A t \/ B t).
Proof.
  intros T A B HA HB.
  eapply TB_ext with (A := fun t => exists n : nat,
    match n with O => A t | S _ => B t end).
  - apply TB_union. intros [|n]; assumption.
  - intros t Ht. split.
    + intros [[|n] Hn]; [left | right]; exact Hn.
    + intros [H | H]; [exists O | exists (S O)]; exact H.
Qed.

Lemma TimeBorel_intersection : forall T A B,
  TimeBorel T A -> TimeBorel T B ->
  TimeBorel T (fun t => A t /\ B t).
Proof.
  intros T A B HA HB.
  eapply TB_ext with (A := fun t => ~ (~ A t \/ ~ B t)).
  - apply TB_complement. apply TimeBorel_union; apply TB_complement; assumption.
  - intros t Ht. tauto.
Qed.

Lemma TimeBorel_countable_intersection : forall T (A : nat -> R -> Prop),
  (forall n, TimeBorel T (A n)) ->
  TimeBorel T (fun t => forall n, A n t).
Proof.
  intros T A HA.
  eapply TB_ext with (A := fun t => ~ exists n, ~ A n t).
  - apply TB_complement. apply TB_union. intro n.
    apply TB_complement. apply HA.
  - intros t Ht. split.
    + intros H n. apply NNPP. intro Hnot. apply H. exists n. exact Hnot.
    + intros H [n Hnot]. apply Hnot. apply H.
Qed.

Lemma ScalarBorelOn_ext : forall T f g,
  (forall t, InInterval T t -> f t = g t) ->
  ScalarBorelOn T f -> ScalarBorelOn T g.
Proof.
  intros T f g Heq Hf c.
  eapply TB_ext with (A := fun t => f t < c); [apply Hf |].
  intros t Ht. rewrite (Heq t Ht). reflexivity.
Qed.

Theorem SCALAR_CONTINUOUS_BOREL : forall T f,
  ScalarContinuousOn T f -> ScalarBorelOn T f.
Proof.
  intros T f Hcont c. apply TB_open. intros t Ht Hfc.
  destruct (Hcont t Ht ((c - f t) / 2) ltac:(lra)) as [delta [Hd Hbound]].
  exists delta. split; [exact Hd |].
  intros s Hs Hst. specialize (Hbound s Hs Hst).
  destruct (Rabs_def2 _ _ Hbound) as [Hupper Hlower]. lra.
Qed.

Theorem SCALAR_BOREL_CONSTANT : forall T c,
  ScalarBorelOn T (fun _ => c).
Proof. intros T c. apply SCALAR_CONTINUOUS_BOREL. apply ScalarContinuousOn_constant. Qed.

Definition TimeGap (n : nat) : R := / INR (S n).

Lemma TimeGap_positive : forall n, 0 < TimeGap n.
Proof.
  intro n. unfold TimeGap. apply Rinv_0_lt_compat.
  apply lt_0_INR. lia.
Qed.

Lemma TimeGap_arbitrarily_small : forall eps,
  0 < eps -> exists n, TimeGap n < eps.
Proof.
  intros eps Heps.
  destruct (archimed_cor1 eps Heps) as [N [HN Hpositive]].
  destruct N as [|n]; [lia |].
  exists n. exact HN.
Qed.

Lemma TimeBorel_scalar_le : forall T f,
  ScalarBorelOn T f -> forall c, TimeBorel T (fun t => f t <= c).
Proof.
  intros T f Hf c.
  eapply TB_ext with (A := fun t => forall n, f t < c + TimeGap n).
  - apply TimeBorel_countable_intersection. intro n. apply Hf.
  - intros t Ht. split.
    + intro Hall. destruct (Rle_dec (f t) c) as [Hle | Hnot]; [exact Hle |].
      destruct (TimeGap_arbitrarily_small (f t - c) ltac:(lra)) as [n Hgap].
      specialize (Hall n). lra.
    + intros Hle n. pose proof (TimeGap_positive n). lra.
Qed.

Lemma TimeBorel_scalar_gt : forall T f,
  ScalarBorelOn T f -> forall c, TimeBorel T (fun t => c < f t).
Proof.
  intros T f Hf c.
  eapply TB_ext with (A := fun t => ~ f t <= c).
  - apply TB_complement. apply TimeBorel_scalar_le. exact Hf.
  - intros t Ht. lra.
Qed.

Lemma TimeBorel_scalar_ge : forall T f,
  ScalarBorelOn T f -> forall c, TimeBorel T (fun t => c <= f t).
Proof.
  intros T f Hf c.
  eapply TB_ext with (A := fun t => ~ f t < c).
  - apply TB_complement. apply Hf.
  - intros t Ht. lra.
Qed.

Lemma TimeBorel_scalar_eq : forall T f,
  ScalarBorelOn T f -> forall c, TimeBorel T (fun t => f t = c).
Proof.
  intros T f Hf c.
  eapply TB_ext with (A := fun t => f t <= c /\ c <= f t).
  - apply TimeBorel_intersection.
    + apply TimeBorel_scalar_le. exact Hf.
    + apply TimeBorel_scalar_ge. exact Hf.
  - intros t Ht. lra.
Qed.

Lemma SeqLimit_strict_sublevel_iff : forall f l c,
  SeqLimit f l ->
  (l < c <-> exists m N, forall n, (N <= n)%nat -> f n < c - TimeGap m).
Proof.
  intros f l c Hlim. split.
  - intro Hlc.
    assert (Heps : 0 < (c - l) / 2) by lra.
    destruct (TimeGap_arbitrarily_small _ Heps) as [m Hgap].
    destruct (Hlim _ Heps) as [N HN].
    exists m, N. intros n Hn. specialize (HN n Hn).
    destruct (Rabs_def2 _ _ HN) as [Hupper Hlower]. lra.
  - intros [m [N Hbound]].
    pose proof (TimeGap_positive m) as Hgap.
    destruct (Rlt_dec l c) as [Hlt | Hnot]; [exact Hlt |].
    assert (Heps : 0 < TimeGap m / 2) by lra.
    destruct (Hlim _ Heps) as [K HK].
    specialize (HK (Nat.max N K) ltac:(lia)).
    specialize (Hbound (Nat.max N K) ltac:(lia)).
    destruct (Rabs_def2 _ _ HK) as [Hupper Hlower]. lra.
Qed.

Theorem SCALAR_BOREL_POINTWISE_LIMIT : forall T (fn : nat -> R -> R) f,
  (forall n, ScalarBorelOn T (fn n)) ->
  (forall t, InInterval T t -> SeqLimit (fun n => fn n t) (f t)) ->
  ScalarBorelOn T f.
Proof.
  intros T fn f Hfn Hlim c.
  eapply TB_ext with (A := fun t => exists m N,
    forall n, (N <= n)%nat -> fn n t < c - TimeGap m).
  - apply TB_union. intro m. apply TB_union. intro N.
    apply TimeBorel_countable_intersection. intro n.
    destruct (le_dec N n) as [Hle | Hnot].
    + eapply TB_ext with (A := fun t => fn n t < c - TimeGap m).
      * apply Hfn.
      * intros t Ht. tauto.
    + eapply TB_ext with (A := fun _ => True).
      * apply TimeBorel_all.
      * intros t Ht. tauto.
  - intros t Ht. symmetry. apply SeqLimit_strict_sublevel_iff.
    apply Hlim. exact Ht.
Qed.

Theorem SCALAR_BOREL_ZERO_PATCH : forall T Active f g,
  TimeBorel T Active -> ScalarBorelOn T f ->
  (forall t, InInterval T t -> Active t -> g t = f t) ->
  (forall t, InInterval T t -> ~ Active t -> g t = 0) ->
  ScalarBorelOn T g.
Proof.
  intros T Active f g HA Hf Hon Hoff c.
  eapply TB_ext with
    (A := fun t => (Active t /\ f t < c) \/ (~ Active t /\ 0 < c)).
  - apply TimeBorel_union.
    + apply TimeBorel_intersection; [exact HA | apply Hf].
    + apply TimeBorel_intersection; [apply TB_complement; exact HA |].
      apply (SCALAR_BOREL_CONSTANT T 0 c).
  - intros t Ht. destruct (classic (Active t)) as [HtA | HtN].
    + rewrite (Hon t Ht HtA). tauto.
    + rewrite (Hoff t Ht HtN). tauto.
Qed.

Print Assumptions TimeBorel_countable_intersection.
Print Assumptions SCALAR_BOREL_POINTWISE_LIMIT.
Print Assumptions SCALAR_BOREL_ZERO_PATCH.
