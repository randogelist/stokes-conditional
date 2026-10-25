From Stdlib Require Import Reals Lra Psatz Lia.

Open Scope R_scope.

(* This module completes the diagonal GP coordinate representation.
   It does not construct a physical-space orthonormal basis or a Lebesgue
   integral. Physical L2 reconstruction is a separate analytic interface. *)

Definition Seq := nat -> R.

Definition seq_eq (a b : Seq) : Prop := forall i, a i = b i.

Fixpoint prefix (f : Seq) (n : nat) : R :=
  match n with
  | O => 0
  | S k => prefix f k + f k
  end.

Definition energy_prefix (a : Seq) (n : nat) : R :=
  prefix (fun i => a i * a i) n.

Definition GPNonzero (g : Seq) : Prop := forall i, g i <> 0.

Definition encode (g a : Seq) : Seq := fun i => g i * a i.
Definition decode (g p : Seq) : Seq := fun i => p i / g i.

(* Nonnegative partial sums make boundedness exactly the summability
   condition for the coordinate square norm. *)
Definition CoordinateL2 (a : Seq) : Prop :=
  exists B : R, forall n, energy_prefix a n <= B.

Definition GPL2 (g p : Seq) : Prop := CoordinateL2 (decode g p).

Definition EnergyValue (a : Seq) (E : R) : Prop :=
  (forall n, energy_prefix a n <= E) /\
  (forall B, (forall n, energy_prefix a n <= B) -> E <= B).

Lemma seq_eq_refl : forall a, seq_eq a a.
Proof. intros a i; reflexivity. Qed.

Lemma seq_eq_sym : forall a b, seq_eq a b -> seq_eq b a.
Proof. intros a b H i; symmetry; apply H. Qed.

Lemma seq_eq_trans : forall a b c,
  seq_eq a b -> seq_eq b c -> seq_eq a c.
Proof. intros a b c H1 H2 i; rewrite H1; apply H2. Qed.

Lemma prefix_ext : forall f h n,
  seq_eq f h -> prefix f n = prefix h n.
Proof.
  intros f h n Heq; induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH, Heq; reflexivity.
Qed.

Lemma prefix_nonnegative : forall f n,
  (forall i, 0 <= f i) -> 0 <= prefix f n.
Proof.
  intros f n H; induction n as [|n IH]; simpl.
  - lra.
  - specialize (H n); lra.
Qed.

Lemma prefix_monotone : forall f n m,
  (forall i, 0 <= f i) -> (n <= m)%nat ->
  prefix f n <= prefix f m.
Proof.
  intros f n m Hnonneg Hnm; induction Hnm.
  - lra.
  - simpl; specialize (Hnonneg m); lra.
Qed.

Lemma prefix_add : forall f h n,
  prefix (fun i => f i + h i) n = prefix f n + prefix h n.
Proof.
  intros f h n; induction n as [|n IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma prefix_scale : forall c f n,
  prefix (fun i => c * f i) n = c * prefix f n.
Proof.
  intros c f n; induction n as [|n IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma prefix_order : forall f h n,
  (forall i, f i <= h i) -> prefix f n <= prefix h n.
Proof.
  intros f h n H; induction n as [|n IH]; simpl; [lra|].
  specialize (H n); lra.
Qed.

Lemma energy_prefix_ext : forall a b n,
  seq_eq a b -> energy_prefix a n = energy_prefix b n.
Proof.
  intros a b n H; unfold energy_prefix; apply prefix_ext.
  intro i; rewrite H; reflexivity.
Qed.

Lemma energy_prefix_nonnegative : forall a n, 0 <= energy_prefix a n.
Proof.
  intros a n; unfold energy_prefix; apply prefix_nonnegative.
  intro i; nra.
Qed.

Lemma energy_prefix_monotone : forall a n m,
  (n <= m)%nat -> energy_prefix a n <= energy_prefix a m.
Proof.
  intros a n m H; unfold energy_prefix; apply prefix_monotone; [intro i; nra|exact H].
Qed.

Lemma energy_prefix_add_bound : forall a b n,
  energy_prefix (fun i => a i + b i) n <=
  2 * energy_prefix a n + 2 * energy_prefix b n.
Proof.
  intros a b n; induction n as [|n IH].
  - unfold energy_prefix; simpl; lra.
  - unfold energy_prefix in *; simpl in *.
    pose proof (Rle_0_sqr (a n - b n)) as Hsquare.
    unfold Rsqr in Hsquare; nra.
Qed.

Lemma energy_prefix_scale : forall c a n,
  energy_prefix (fun i => c * a i) n = c * c * energy_prefix a n.
Proof.
  intros c a n; induction n as [|n IH].
  - unfold energy_prefix; simpl; ring.
  - unfold energy_prefix in *; simpl in *; rewrite IH; ring.
Qed.

Lemma CoordinateL2_ext : forall a b,
  seq_eq a b -> (CoordinateL2 a <-> CoordinateL2 b).
Proof.
  intros a b Heq; split; intros [B HB]; exists B; intro n.
  - rewrite <- (energy_prefix_ext a b n Heq); apply HB.
  - rewrite (energy_prefix_ext a b n Heq); apply HB.
Qed.

Lemma CoordinateL2_zero : CoordinateL2 (fun _ => 0).
Proof.
  exists 0; intro n; unfold energy_prefix; induction n; simpl; lra.
Qed.

Lemma CoordinateL2_add : forall a b,
  CoordinateL2 a -> CoordinateL2 b ->
  CoordinateL2 (fun i => a i + b i).
Proof.
  intros a b [A HA] [B HB]; exists (2 * A + 2 * B); intro n.
  pose proof (energy_prefix_add_bound a b n).
  specialize (HA n); specialize (HB n); lra.
Qed.

Lemma CoordinateL2_scale : forall c a,
  CoordinateL2 a -> CoordinateL2 (fun i => c * a i).
Proof.
  intros c a [A HA]; exists (c * c * A); intro n.
  rewrite energy_prefix_scale; apply Rmult_le_compat_l; [nra|apply HA].
Qed.

Theorem decode_encode : forall g a,
  GPNonzero g -> seq_eq (decode g (encode g a)) a.
Proof.
  intros g a H i; unfold decode, encode; specialize (H i); field; exact H.
Qed.

Theorem encode_decode : forall g p,
  GPNonzero g -> seq_eq (encode g (decode g p)) p.
Proof.
  intros g p H i; unfold decode, encode; specialize (H i); field; exact H.
Qed.

Theorem encode_injective : forall g a b,
  GPNonzero g -> seq_eq (encode g a) (encode g b) -> seq_eq a b.
Proof.
  intros g a b Hnz Heq i.
  specialize (Heq i); unfold encode in Heq.
  apply (Rmult_eq_reg_l (g i)); [exact Heq|apply Hnz].
Qed.

Theorem decode_injective : forall g p q,
  GPNonzero g -> seq_eq (decode g p) (decode g q) -> seq_eq p q.
Proof.
  intros g p q Hnz Heq i.
  pose proof (encode_decode g p Hnz i) as Hp.
  pose proof (encode_decode g q Hnz i) as Hq.
  unfold encode in Hp, Hq; rewrite <- Hp, <- Hq; rewrite Heq; reflexivity.
Qed.

Theorem GP_energy_prefix_exact : forall g a n,
  GPNonzero g -> energy_prefix (decode g (encode g a)) n = energy_prefix a n.
Proof.
  intros g a n H; apply energy_prefix_ext; apply decode_encode; exact H.
Qed.

Theorem GP_L2_exact : forall g a,
  GPNonzero g -> (GPL2 g (encode g a) <-> CoordinateL2 a).
Proof.
  intros g a H; unfold GPL2; apply CoordinateL2_ext; apply decode_encode; exact H.
Qed.

Theorem GP_L2_surjective : forall g p,
  GPNonzero g -> GPL2 g p ->
  exists a, CoordinateL2 a /\ seq_eq (encode g a) p.
Proof.
  intros g p Hnz Hp; exists (decode g p); split.
  - exact Hp.
  - apply encode_decode; exact Hnz.
Qed.

Lemma EnergyValue_ext : forall a b E,
  seq_eq a b -> (EnergyValue a E <-> EnergyValue b E).
Proof.
  intros a b E Heq; unfold EnergyValue; split; intros [Hup Hleast]; split.
  - intro n; rewrite <- (energy_prefix_ext a b n Heq); apply Hup.
  - intros B HB; apply Hleast; intro n.
    rewrite (energy_prefix_ext a b n Heq); apply HB.
  - intro n; rewrite (energy_prefix_ext a b n Heq); apply Hup.
  - intros B HB; apply Hleast; intro n.
    rewrite <- (energy_prefix_ext a b n Heq); apply HB.
Qed.

Theorem EnergyValue_exists : forall a,
  CoordinateL2 a -> exists E, EnergyValue a E.
Proof.
  intros a [B HB].
  set (S := fun x : R => exists n : nat, x = energy_prefix a n).
  assert (HSbound : bound S).
  { exists B; intros x [n Hx]; rewrite Hx; apply HB. }
  assert (HSnonempty : exists x : R, S x).
  { exists (energy_prefix a 0); exists 0%nat; reflexivity. }
  destruct (completeness S HSbound HSnonempty) as [E [Hup Hleast]].
  exists E; split.
  - intro n; apply Hup; exists n; reflexivity.
  - intros C HC; apply Hleast; intros x [n Hx]; rewrite Hx; apply HC.
Qed.

Theorem EnergyValue_implies_L2 : forall a E,
  EnergyValue a E -> CoordinateL2 a.
Proof. intros a E [Hup _]; exists E; exact Hup. Qed.

Theorem EnergyValue_unique : forall a E F,
  EnergyValue a E -> EnergyValue a F -> E = F.
Proof.
  intros a E F [HEup HEleast] [HFup HFleast].
  apply Rle_antisym; [apply HEleast; exact HFup|apply HFleast; exact HEup].
Qed.

Theorem EnergyValue_nonnegative : forall a E,
  EnergyValue a E -> 0 <= E.
Proof.
  intros a E [Hup _]; exact (Hup 0%nat).
Qed.

Theorem GP_energy_value_exact : forall g a E,
  GPNonzero g ->
  (EnergyValue (decode g (encode g a)) E <-> EnergyValue a E).
Proof.
  intros g a E H; apply EnergyValue_ext; apply decode_encode; exact H.
Qed.

(* The supremum can be approximated by a finite cut. No rate is claimed. *)
Theorem EnergyValue_finite_approximation : forall a E eps,
  EnergyValue a E -> 0 < eps ->
  exists N : nat, E - eps < energy_prefix a N.
Proof.
  intros a E eps [Hup Hleast] Heps.
  destruct (ClassicalDedekindReals.sig_forall_dec
    (fun n : nat => energy_prefix a n <= E - eps)
    (fun n : nat => Rle_dec (energy_prefix a n) (E - eps)))
    as [[N HN]|Hall].
  - exists N; lra.
  - specialize (Hleast (E - eps) Hall); lra.
Qed.

Theorem EnergyValue_prefix_converges : forall a E,
  EnergyValue a E -> forall eps, 0 < eps ->
  exists N : nat, forall M : nat, (N <= M)%nat ->
    0 <= E - energy_prefix a M < eps.
Proof.
  intros a E HE eps Heps.
  destruct (EnergyValue_finite_approximation a E eps HE Heps) as [N HN].
  exists N; intros M HNM.
  pose proof (energy_prefix_monotone a N M HNM) as Hmono.
  destruct HE as [Hup _]; specialize (Hup M); lra.
Qed.

Theorem CoordinateL2_tail : forall a,
  CoordinateL2 a -> forall eps, 0 < eps ->
  exists N : nat, forall M : nat, (N <= M)%nat ->
    0 <= energy_prefix a M - energy_prefix a N < eps.
Proof.
  intros a HL2 eps Heps.
  destruct (EnergyValue_exists a HL2) as [E HE].
  destruct (EnergyValue_finite_approximation a E eps HE Heps) as [N HN].
  exists N; intros M HNM.
  pose proof (energy_prefix_monotone a N M HNM) as Hmono.
  destruct HE as [Hup _]; specialize (Hup M); lra.
Qed.

Theorem GPL2_tail : forall g p,
  GPL2 g p -> forall eps, 0 < eps ->
  exists N : nat, forall M : nat, (N <= M)%nat ->
    0 <= energy_prefix (decode g p) M - energy_prefix (decode g p) N < eps.
Proof. intros g p H; apply CoordinateL2_tail; exact H. Qed.

Print Assumptions GP_L2_exact.
Print Assumptions EnergyValue_exists.
Print Assumptions CoordinateL2_tail.
