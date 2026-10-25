From Stdlib Require Import Reals Lra Lia.
Require Import LHGP_Coordinates.

Open Scope R_scope.

(* This module proves exact coefficient-readout transport.  Test coefficients,
   costs, and a convergent readout are explicit data.  The identification with
   physical integrals, tensor products, and distributional gradients is not
   asserted here; those analytic bridges remain separate obligations. *)

Definition linear_prefix (a f : Seq) (n : nat) : R :=
  prefix (fun i => a i * f i) n.

Definition quadratic_prefix (a : Seq) (C : nat -> nat -> R) (n : nat) : R :=
  prefix (fun i => prefix (fun j => a i * a j * C i j) n) n.

Definition SeqLimit (f : Seq) (l : R) : Prop :=
  forall eps : R, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> Rabs (f n - l) < eps.

Definition linear_limit (a f : Seq) (l : R) : Prop :=
  SeqLimit (linear_prefix a f) l.

Definition quadratic_limit (a : Seq) (C : nat -> nat -> R) (l : R) : Prop :=
  SeqLimit (quadratic_prefix a C) l.

Lemma readout_prefix_ext : forall f h : Seq,
  seq_eq f h -> forall n, prefix f n = prefix h n.
Proof.
  intros f h E n. induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH, (E n). reflexivity.
Qed.

Lemma linear_prefix_ext : forall a b f,
  seq_eq a b -> forall n, linear_prefix a f n = linear_prefix b f n.
Proof.
  intros a b f E n. unfold linear_prefix.
  apply readout_prefix_ext. intro i. rewrite (E i). reflexivity.
Qed.

Lemma linear_prefix_test_ext : forall a f h,
  seq_eq f h -> forall n, linear_prefix a f n = linear_prefix a h n.
Proof.
  intros a f h E n. unfold linear_prefix.
  apply readout_prefix_ext. intro i. rewrite (E i). reflexivity.
Qed.

Lemma quadratic_prefix_ext : forall a b C,
  seq_eq a b -> forall n, quadratic_prefix a C n = quadratic_prefix b C n.
Proof.
  intros a b C E n. unfold quadratic_prefix.
  apply readout_prefix_ext. intro i.
  apply readout_prefix_ext. intro j.
  rewrite (E i), (E j). reflexivity.
Qed.

Lemma quadratic_prefix_kernel_ext : forall a C D,
  (forall i j, C i j = D i j) ->
  forall n, quadratic_prefix a C n = quadratic_prefix a D n.
Proof.
  intros a C D E n. unfold quadratic_prefix.
  apply readout_prefix_ext. intro i.
  apply readout_prefix_ext. intro j.
  rewrite (E i j). reflexivity.
Qed.

Lemma SeqLimit_ext : forall f h l,
  seq_eq f h -> (SeqLimit f l <-> SeqLimit h l).
Proof.
  intros f h l E. split; intros H eps Heps.
  - destruct (H eps Heps) as [N HN]. exists N.
    intros n Hn. rewrite <- (E n). apply HN. exact Hn.
  - destruct (H eps Heps) as [N HN]. exists N.
    intros n Hn. rewrite (E n). apply HN. exact Hn.
Qed.

Lemma SeqLimit_unique : forall f l m,
  SeqLimit f l -> SeqLimit f m -> l = m.
Proof.
  intros f l m Hl Hm.
  destruct (Req_dec l m) as [Heq | Hneq]; [exact Heq |].
  assert (Hpos : 0 < Rabs (l - m)).
  { apply Rabs_pos_lt. intro Hzero. apply Hneq. lra. }
  assert (Heps : 0 < Rabs (l - m) / 3) by lra.
  destruct (Hl _ Heps) as [Nl HNl].
  destruct (Hm _ Heps) as [Nm HNm].
  set (n := Nat.max Nl Nm).
  specialize (HNl n ltac:(unfold n; lia)).
  specialize (HNm n ltac:(unfold n; lia)).
  pose proof (Rabs_triang (l - f n) (f n - m)) as Htri.
  replace (l - f n + (f n - m)) with (l - m) in Htri by ring.
  rewrite (Rabs_minus_sym l (f n)) in Htri.
  lra.
Qed.

Lemma linear_limit_unique : forall a f l m,
  linear_limit a f l -> linear_limit a f m -> l = m.
Proof. intros a f l m Hl Hm. eapply SeqLimit_unique; eassumption. Qed.

Lemma linear_limit_ext : forall a b f l,
  seq_eq a b -> (linear_limit a f l <-> linear_limit b f l).
Proof.
  intros a b f l E. unfold linear_limit.
  apply SeqLimit_ext. intro n. apply linear_prefix_ext. exact E.
Qed.

Lemma quadratic_limit_ext : forall a b C l,
  seq_eq a b -> (quadratic_limit a C l <-> quadratic_limit b C l).
Proof.
  intros a b C l E. unfold quadratic_limit.
  apply SeqLimit_ext. intro n. apply quadratic_prefix_ext. exact E.
Qed.

Theorem gp_linear_prefix_transport : forall g a f,
  GPNonzero g -> forall n,
    linear_prefix (decode g (encode g a)) f n = linear_prefix a f n.
Proof.
  intros g a f Hg n. apply linear_prefix_ext.
  apply decode_encode. exact Hg.
Qed.

Theorem gp_quadratic_prefix_transport : forall g a C,
  GPNonzero g -> forall n,
    quadratic_prefix (decode g (encode g a)) C n = quadratic_prefix a C n.
Proof.
  intros g a C Hg n. apply quadratic_prefix_ext.
  apply decode_encode. exact Hg.
Qed.

Theorem gp_linear_limit_transport : forall g a f l,
  GPNonzero g ->
    (linear_limit (decode g (encode g a)) f l <-> linear_limit a f l).
Proof.
  intros g a f l Hg. apply linear_limit_ext.
  apply decode_encode. exact Hg.
Qed.

Theorem gp_quadratic_limit_transport : forall g a C l,
  GPNonzero g ->
    (quadratic_limit (decode g (encode g a)) C l <-> quadratic_limit a C l).
Proof.
  intros g a C l Hg. apply quadratic_limit_ext.
  apply decode_encode. exact Hg.
Qed.

(* Finite test truncations are exact before any infinite-dimensional limit.
   In particular the nonlinear readout retains both signed coefficients. *)
Lemma linear_prefix_add : forall a b f n,
  linear_prefix (fun i => a i + b i) f n =
  linear_prefix a f n + linear_prefix b f n.
Proof.
  intros a b f n. unfold linear_prefix.
  induction n as [|n IH]; simpl; [ring|].
  rewrite IH. ring.
Qed.

Lemma linear_prefix_scale : forall c a f n,
  linear_prefix (fun i => c * a i) f n = c * linear_prefix a f n.
Proof.
  intros c a f n. unfold linear_prefix.
  induction n as [|n IH]; simpl; [ring|].
  rewrite IH. ring.
Qed.

Lemma linear_prefix_polarization : forall a f n,
  4 * linear_prefix a f n =
  energy_prefix (fun i => a i + f i) n -
  energy_prefix (fun i => a i - f i) n.
Proof.
  intros a f n. unfold linear_prefix, energy_prefix.
  induction n as [|n IH]; simpl; [ring | nra].
Qed.

(* Unlike an arbitrary quadratic coefficient kernel, every L2 coefficient
   test has a convergent linear readout.  The proof constructs the limit
   from the two energy values in the real polarization identity. *)
Theorem linear_limit_exists_L2 : forall a f,
  CoordinateL2 a -> CoordinateL2 f -> exists l, linear_limit a f l.
Proof.
  intros a f Ha Hf.
  assert (Hplus : CoordinateL2 (fun i => a i + f i)).
  { apply CoordinateL2_add; assumption. }
  assert (Hminus_eq :
    seq_eq (fun i => a i + (-1) * f i) (fun i => a i - f i)).
  { intro i. ring. }
  assert (Hminus : CoordinateL2 (fun i => a i - f i)).
  { apply (proj1 (CoordinateL2_ext _ _ Hminus_eq)).
    apply CoordinateL2_add; [exact Ha |].
    apply CoordinateL2_scale. exact Hf. }
  destruct (EnergyValue_exists _ Hplus) as [Eplus HEplus].
  destruct (EnergyValue_exists _ Hminus) as [Eminus HEminus].
  exists ((Eplus - Eminus) / 4).
  intros eps Heps.
  destruct (EnergyValue_prefix_converges _ _ HEplus eps Heps)
    as [Nplus HNplus].
  destruct (EnergyValue_prefix_converges _ _ HEminus eps Heps)
    as [Nminus HNminus].
  exists (Nat.max Nplus Nminus).
  intros n Hn.
  specialize (HNplus n ltac:(lia)).
  specialize (HNminus n ltac:(lia)).
  pose proof (linear_prefix_polarization a f n) as Hpolar.
  apply Rabs_def1; lra.
Qed.

Lemma readout_prefix_scale : forall c f n,
  prefix (fun i => c * f i) n = c * prefix f n.
Proof.
  intros c f n. induction n as [|n IH]; simpl; [ring|].
  rewrite IH. ring.
Qed.

Lemma quadratic_prefix_scale : forall c a C n,
  quadratic_prefix (fun i => c * a i) C n =
  c * c * quadratic_prefix a C n.
Proof.
  intros c a C n. unfold quadratic_prefix.
  transitivity
    (prefix (fun i => (c * c) * prefix (fun j => a i * a j * C i j) n) n).
  - apply readout_prefix_ext. intro i.
    rewrite <- readout_prefix_scale.
    apply readout_prefix_ext. intro j. ring.
  - apply readout_prefix_scale.
Qed.

Section VariationalDissipation.
  Context {Test : Type}.
  Variable test_coeff : Test -> Seq.
  Variable test_cost : Test -> R.

  Definition ProbeValue (a : Seq) (t : Test) (l : R) : Prop :=
    linear_limit a (test_coeff t) l.

  Definition DissipationUpper (a : Seq) (B : R) : Prop :=
    forall t l, ProbeValue a t l -> -2 * l - test_cost t <= B.

  (* A real least-upper-bound relation, with no claim that it always exists.
     This permits the analytic completion to have infinite dissipation. *)
  Definition DissipationValue (a : Seq) (D : R) : Prop :=
    DissipationUpper a D /\
    forall B, DissipationUpper a B -> D <= B.

  Lemma ProbeValue_ext : forall a b,
    seq_eq a b -> forall t l, (ProbeValue a t l <-> ProbeValue b t l).
  Proof.
    intros a b E t l. unfold ProbeValue.
    apply linear_limit_ext. exact E.
  Qed.

  Lemma DissipationUpper_ext : forall a b,
    seq_eq a b -> forall B, (DissipationUpper a B <-> DissipationUpper b B).
  Proof.
    intros a b E B. split; intros H t l Hl.
    - apply (H t l). apply (proj2 (ProbeValue_ext a b E t l)). exact Hl.
    - apply (H t l). apply (proj1 (ProbeValue_ext a b E t l)). exact Hl.
  Qed.

  Lemma DissipationValue_ext : forall a b,
    seq_eq a b -> forall D, (DissipationValue a D <-> DissipationValue b D).
  Proof.
    intros a b E D. split; intros [HU HL]; split.
    - apply (proj1 (DissipationUpper_ext a b E D)). exact HU.
    - intros B HB. apply HL.
      apply (proj2 (DissipationUpper_ext a b E B)). exact HB.
    - apply (proj2 (DissipationUpper_ext a b E D)). exact HU.
    - intros B HB. apply HL.
      apply (proj1 (DissipationUpper_ext a b E B)). exact HB.
  Qed.

  Lemma DissipationValue_unique : forall a D E,
    DissipationValue a D -> DissipationValue a E -> D = E.
  Proof.
    intros a D E [HD HDmin] [HE HEmin].
    apply Rle_antisym; [apply HDmin | apply HEmin]; assumption.
  Qed.

  Lemma DissipationUpper_monotone : forall a B C,
    DissipationUpper a B -> B <= C -> DissipationUpper a C.
  Proof.
    intros a B C HB HBC t l Hl.
    eapply Rle_trans; [apply (HB t l Hl) | exact HBC].
  Qed.

  Theorem gp_probe_transport : forall g a,
    GPNonzero g -> forall t l,
    (ProbeValue (decode g (encode g a)) t l <-> ProbeValue a t l).
  Proof.
    intros g a Hg. apply ProbeValue_ext. apply decode_encode. exact Hg.
  Qed.

  Theorem gp_dissipation_upper_transport : forall g a,
    GPNonzero g -> forall B,
    (DissipationUpper (decode g (encode g a)) B <-> DissipationUpper a B).
  Proof.
    intros g a Hg. apply DissipationUpper_ext. apply decode_encode. exact Hg.
  Qed.

  Theorem gp_dissipation_value_transport : forall g a,
    GPNonzero g -> forall D,
    (DissipationValue (decode g (encode g a)) D <-> DissipationValue a D).
  Proof.
    intros g a Hg. apply DissipationValue_ext. apply decode_encode. exact Hg.
  Qed.
End VariationalDissipation.

Print Assumptions gp_linear_limit_transport.
Print Assumptions linear_limit_exists_L2.
Print Assumptions gp_quadratic_limit_transport.
Print Assumptions gp_dissipation_value_transport.
