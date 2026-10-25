From Stdlib Require Import Reals Field.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert.
Require Import LHGP_Realization LHGP_PathSynthesis LHGP_Evolution.
Require Import BKQR_CountableRange BKQR_ShellCoordinates.

Module BKQR_LHGP_EVOLUTION_BRIDGE.
Open Scope R_scope.

(* The two donor developments use the same ordered finite sums and the same
   epsilon definition of a real sequence limit.  We prove the finite-sum
   correspondence instead of identifying their interfaces by name. *)
Lemma native_sum_is_donor_prefix : forall n f,
  GP_COUNTABLE_RANGE.gp_sum n f = LHGP_Coordinates.prefix f n.
Proof. induction n; intros f; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Definition native_linear_prefix (psi U : nat -> nat -> R)
    (f : nat -> R) (N : nat) : R :=
  GP_COUNTABLE_RANGE.gp_sum N
    (fun i => U 0%nat i * f i / psi 0%nat i).

Definition native_quadratic_prefix (psi U : nat -> nat -> R)
    (C : nat -> nat -> R) (N : nat) : R :=
  GP_COUNTABLE_RANGE.gp_sum N (fun i =>
    GP_COUNTABLE_RANGE.gp_sum N (fun j =>
      U 0%nat i * U 0%nat j * C i j /
        (psi 0%nat i * psi 0%nat j))).

Definition native_linear_limit psi U f l : Prop :=
  GP_COUNTABLE_RANGE.SeqLimit (native_linear_prefix psi U f) l.
Definition native_quadratic_limit psi U C l : Prop :=
  GP_COUNTABLE_RANGE.SeqLimit (native_quadratic_prefix psi U C) l.

Lemma BKLE01_NATIVE_LINEAR_PREFIX : forall psi U f N,
  native_linear_prefix psi U f N =
  LHGP_Readouts.linear_prefix
    (LHGP_Coordinates.decode (psi 0%nat) (U 0%nat)) f N.
Proof.
  intros psi U f N. unfold native_linear_prefix, LHGP_Readouts.linear_prefix.
  rewrite native_sum_is_donor_prefix. apply LHGP_Readouts.readout_prefix_ext.
  intro i. unfold LHGP_Coordinates.decode, Rdiv. ring.
Qed.

Lemma BKLE02_NATIVE_QUADRATIC_PREFIX : forall psi U C N,
  (forall i, psi 0%nat i <> 0) ->
  native_quadratic_prefix psi U C N =
  LHGP_Readouts.quadratic_prefix
    (LHGP_Coordinates.decode (psi 0%nat) (U 0%nat)) C N.
Proof.
  intros psi U C N Hzero.
  unfold native_quadratic_prefix, LHGP_Readouts.quadratic_prefix.
  rewrite native_sum_is_donor_prefix. apply LHGP_Readouts.readout_prefix_ext.
  intro i. rewrite native_sum_is_donor_prefix.
  apply LHGP_Readouts.readout_prefix_ext. intro j.
  unfold LHGP_Coordinates.decode. field. split; apply Hzero.
Qed.

Lemma BKLE03_NATIVE_LINEAR_LIMIT : forall psi U f l,
  native_linear_limit psi U f l <->
  LHGP_Readouts.linear_limit
    (LHGP_Coordinates.decode (psi 0%nat) (U 0%nat)) f l.
Proof.
  intros psi U f l. unfold native_linear_limit,
    GP_COUNTABLE_RANGE.SeqLimit, LHGP_Readouts.linear_limit,
    LHGP_Readouts.SeqLimit.
  split; intros H eps Heps; destruct (H eps Heps) as [N HN];
    exists N; intros n Hn.
  - rewrite <- BKLE01_NATIVE_LINEAR_PREFIX. apply HN. exact Hn.
  - rewrite BKLE01_NATIVE_LINEAR_PREFIX. apply HN. exact Hn.
Qed.

Lemma BKLE04_NATIVE_QUADRATIC_LIMIT : forall psi U C l,
  (forall i, psi 0%nat i <> 0) ->
  (native_quadratic_limit psi U C l <->
  LHGP_Readouts.quadratic_limit
    (LHGP_Coordinates.decode (psi 0%nat) (U 0%nat)) C l).
Proof.
  intros psi U C l Hzero. unfold native_quadratic_limit,
    GP_COUNTABLE_RANGE.SeqLimit, LHGP_Readouts.quadratic_limit,
    LHGP_Readouts.SeqLimit.
  split; intros H eps Heps; destruct (H eps Heps) as [N HN];
    exists N; intros n Hn.
  - rewrite <- BKLE02_NATIVE_QUADRATIC_PREFIX by exact Hzero.
    apply HN. exact Hn.
  - rewrite BKLE02_NATIVE_QUADRATIC_PREFIX by exact Hzero.
    apply HN. exact Hn.
Qed.

(* This is an independently stated equation in native shell coefficients.
   The test class, bounded Hilbert bilinear form, integration operator,
   integrability predicate, signs, and initial trace are unchanged.
   No claim identifies TimeData with Riemann or Lebesgue integration. *)
Definition NativeWeakForm (h : HilbertData) (b : OrthonormalBasis h)
    (tests : EvolutionTests h) (td : TimeData) (nu T : R)
    (psi : nat -> nat -> R) (U : R -> nat -> nat -> R)
    (U0 : nat -> nat -> R) : Prop :=
  forall test : ETest h tests,
    exists lt lv nl : R -> R, exists initial : R,
      (forall t, native_linear_limit psi (U t)
        (HAnalysis b (ETime h tests test t)) (lt t)) /\
      (forall t, native_linear_limit psi (U t)
        (HAnalysis b (ELap h tests test t)) (lv t)) /\
      (forall t, native_quadratic_limit psi (U t)
        (fun i j => EConvection h tests test t
          (HBasis h b i) (HBasis h b j)) (nl t)) /\
      native_linear_limit psi U0
        (HAnalysis b (EInitial h tests test)) initial /\
      EvolutionScalarBalance td nu T lt lv nl initial.

Theorem BKLE20_NATIVE_GP_WEAK_FORM_EXACT : forall h b tests td nu T psi U U0,
  (forall i, psi 0%nat i <> 0) ->
  (NativeWeakForm h b tests td nu T psi U U0 <->
   GPWeakForm h b tests td nu T (psi 0%nat)
     (fun t => U t 0%nat) (U0 0%nat)).
Proof.
  intros h b tests td nu T psi U U0 Hzero.
  split; intros H test;
    destruct (H test) as [lt [lv [nl [initial [Ht [Hv [Hn [Hi Hb]]]]]]]];
    exists lt, lv, nl, initial; repeat split.
  - intro t. apply (proj1 (BKLE03_NATIVE_LINEAR_LIMIT _ _ _ _)). apply Ht.
  - intro t. apply (proj1 (BKLE03_NATIVE_LINEAR_LIMIT _ _ _ _)). apply Hv.
  - intro t. apply (proj1 (BKLE04_NATIVE_QUADRATIC_LIMIT _ _ _ _ Hzero)). apply Hn.
  - apply (proj1 (BKLE03_NATIVE_LINEAR_LIMIT _ _ _ _)). exact Hi.
  - exact (proj1 Hb).
  - exact (proj1 (proj2 Hb)).
  - exact (proj1 (proj2 (proj2 Hb))).
  - exact (proj2 (proj2 (proj2 Hb))).
  - intro t. apply (proj2 (BKLE03_NATIVE_LINEAR_LIMIT _ _ _ _)). apply Ht.
  - intro t. apply (proj2 (BKLE03_NATIVE_LINEAR_LIMIT _ _ _ _)). apply Hv.
  - intro t. apply (proj2 (BKLE04_NATIVE_QUADRATIC_LIMIT _ _ _ _ Hzero)). apply Hn.
  - apply (proj2 (BKLE03_NATIVE_LINEAR_LIMIT _ _ _ _)). exact Hi.
  - exact (proj1 Hb).
  - exact (proj1 (proj2 Hb)).
  - exact (proj1 (proj2 (proj2 Hb))).
  - exact (proj2 (proj2 (proj2 Hb))).
Qed.

(* The readout convergence below is derived from Hilbert completeness and
   the donor's actual ONB/bounded bilinear theorem; it is not a source limit
   supplied as an extra premise.  Full shell compatibility belongs to the
   state/energy classification and is unnecessary for ground readouts. *)
Theorem BKLE30_HILBERT_NATIVE_WEAK_FORM_EXACT : forall h b,
  HComplete h -> forall tests td nu T psi U U0 u u0,
  (forall i, psi 0%nat i <> 0) ->
  HGPPathRealizes h b (psi 0%nat) u (fun t => U t 0%nat) ->
  seq_eq (HGPEncode b (psi 0%nat) u0) (U0 0%nat) ->
  (HilbertWeakForm h tests td nu T u u0 <->
   NativeWeakForm h b tests td nu T psi U U0).
Proof.
  intros h b Hcomplete tests td nu T psi U U0 u u0 Hzero Hu Hinitial.
  rewrite BKLE20_NATIVE_GP_WEAK_FORM_EXACT by exact Hzero.
  apply EVOLUTION_WEAK_FORM_EXACT; assumption.
Qed.

Theorem BKLE31_ACTUAL_NATIVE_QUADRATIC_READOUT : forall h b,
  HComplete h -> forall tests psi U u,
  (forall i, psi 0%nat i <> 0) ->
  HGPPathRealizes h b (psi 0%nat) u (fun t => U t 0%nat) ->
  forall test t, native_quadratic_limit psi (U t)
    (fun i j => EConvection h tests test t (HBasis h b i) (HBasis h b j))
    (EConvection h tests test t (u t) (u t)).
Proof.
  intros h b Hcomplete tests psi U u Hzero Hu test t.
  apply (proj2 (BKLE04_NATIVE_QUADRATIC_LIMIT _ _ _ _ Hzero)).
  apply (EVOLUTION_QUADRATIC_READOUT h b Hcomplete tests
    (psi 0%nat) u (fun t => U t 0%nat) Hzero Hu).
Qed.

Print Assumptions BKLE20_NATIVE_GP_WEAK_FORM_EXACT.
Print Assumptions BKLE30_HILBERT_NATIVE_WEAK_FORM_EXACT.
Print Assumptions BKLE31_ACTUAL_NATIVE_QUADRATIC_READOUT.

End BKQR_LHGP_EVOLUTION_BRIDGE.
