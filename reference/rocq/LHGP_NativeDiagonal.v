From Stdlib Require Import Reals Lra.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Realization LHGP_PathSynthesis LHGP_NativeKQ.
Require Import awpi_nse_candidate_f_work_v0_51_0.

Open Scope R_scope.
Module NativeGP := NSE_CANDIDATE_F_WORK.

(* These are the literal gp_pull/gp_push/gp_metric constants from the
   supplied native anchor, not newly assumed maps. Their energy completion
   is the diagonal GPL2 class. This settles the real diagonal component;
   complex spectral powers and bilateral infinite Kq products remain open. *)

Theorem NATIVE_GP_PULL_IS_ENCODE : forall g a,
  seq_eq (NativeGP.gp_pull g a) (encode g a).
Proof. intros g a i; reflexivity. Qed.

Theorem NATIVE_GP_PUSH_IS_DECODE : forall g p,
  seq_eq (NativeGP.gp_push g p) (decode g p).
Proof. intros g p i; reflexivity. Qed.

Theorem NATIVE_GP_METRIC_IS_DECODED : forall n g p q,
  NativeGP.gp_metric n g p q = NativeGPMetric n g p q.
Proof. reflexivity. Qed.

Lemma NativeMetric_energy_prefix : forall n g p,
  NativeGP.gp_metric n g p p = energy_prefix (decode g p) n.
Proof.
  intros; change (NativeKQ.norm2 n (decode g p) = energy_prefix (decode g p) n).
  apply NativeNorm_energy_prefix.
Qed.

Definition NativeDiagonalL2 (g p : Seq) : Prop :=
  exists B, forall n, NativeGP.gp_metric n g p p <= B.

Definition NativeDiagonalEnergy (g p : Seq) (E : R) : Prop :=
  (forall n, NativeGP.gp_metric n g p p <= E) /\
  (forall B, (forall n, NativeGP.gp_metric n g p p <= B) -> E <= B).

Theorem NATIVE_DIAGONAL_ENERGY_CLASS_EXACT : forall g p,
  NativeDiagonalL2 g p <-> GPL2 g p.
Proof.
  intros g p; split; intros [B HB]; exists B; intro n.
  - rewrite <- NativeMetric_energy_prefix; apply HB.
  - rewrite NativeMetric_energy_prefix; apply HB.
Qed.

Theorem NATIVE_DIAGONAL_ENERGY_VALUE_EXACT : forall g p E,
  NativeDiagonalEnergy g p E <-> EnergyValue (decode g p) E.
Proof.
  intros g p E; split; intros [HU HL]; split.
  - intro n; rewrite <- NativeMetric_energy_prefix; apply HU.
  - intros B HB; apply HL; intro n; rewrite NativeMetric_energy_prefix; apply HB.
  - intro n; rewrite NativeMetric_energy_prefix; apply HU.
  - intros B HB; apply HL; intro n; rewrite <- NativeMetric_energy_prefix; apply HB.
Qed.

Theorem NATIVE_DIAGONAL_STATE_REALIZATION : forall h (b : OrthonormalBasis h),
  HComplete h -> forall g p,
  GPNonzero g -> NativeDiagonalL2 g p ->
  exists x : HCarrier h,
    seq_eq (NativeGP.gp_pull g (HAnalysis b x)) p /\
    NativeDiagonalEnergy g p (HNorm h x) /\
    (forall y, seq_eq (NativeGP.gp_pull g (HAnalysis b y)) p -> y = x).
Proof.
  intros h b Hcomplete g p Hg Hp.
  apply NATIVE_DIAGONAL_ENERGY_CLASS_EXACT in Hp.
  destruct (HGP_surjective_unique h b Hcomplete g p Hg Hp)
    as [x [Hx [HE HU]]].
  exists x; split; [exact Hx|]; split; [|exact HU].
  apply NATIVE_DIAGONAL_ENERGY_VALUE_EXACT; exact HE.
Qed.

Lemma NativeGP_realization_decodes : forall h (b : OrthonormalBasis h) g p x,
  GPNonzero g -> seq_eq (NativeGP.gp_pull g (HAnalysis b x)) p ->
  seq_eq (decode g p) (HAnalysis b x).
Proof.
  intros h b g p x Hg Hx i; unfold decode; rewrite <- (Hx i).
  change (g i * HAnalysis b x i / g i = HAnalysis b x i).
  field; apply Hg.
Qed.

Theorem NATIVE_DIAGONAL_PAIRING_COMPLETION : forall h (b : OrthonormalBasis h),
  HComplete h -> forall g p q x y,
  GPNonzero g ->
  seq_eq (NativeGP.gp_pull g (HAnalysis b x)) p ->
  seq_eq (NativeGP.gp_pull g (HAnalysis b y)) q ->
  SeqLimit (fun n => NativeGP.gp_metric n g p q) (HInner h x y).
Proof.
  intros h b Hcomplete g p q x y Hg Hx Hy eps Heps.
  destruct (LHGP_NATIVE_DOT_ANALYSIS_LIMIT h b Hcomplete x y eps Heps)
    as [N HN].
  exists N; intros n Hn; rewrite NATIVE_GP_METRIC_IS_DECODED.
  unfold NativeGPMetric.
  rewrite (NativeKQ.dot_ext_l n (decode g p) (HAnalysis b x))
    by (intros; apply (NativeGP_realization_decodes h b g p x Hg Hx)).
  rewrite (NativeKQ.dot_ext_r n (HAnalysis b x) (decode g q) (HAnalysis b y))
    by (intros; apply (NativeGP_realization_decodes h b g q y Hg Hy)).
  apply HN; exact Hn.
Qed.

Theorem NATIVE_DIAGONAL_PATH_REALIZATION : forall h (b : OrthonormalBasis h),
  HComplete h -> forall g p,
  GPNonzero g -> (forall t, NativeDiagonalL2 g (p t)) ->
  exists u : R -> HCarrier h,
    (forall t, seq_eq (NativeGP.gp_pull g (HAnalysis b (u t))) (p t)) /\
    (forall t, NativeDiagonalEnergy g (p t) (HNorm h (u t))) /\
    (forall v,
      (forall t, seq_eq (NativeGP.gp_pull g (HAnalysis b (v t))) (p t)) ->
      forall t, v t = u t).
Proof.
  intros h b Hcomplete g p Hg Hp.
  assert (HL2 : forall t, GPL2 g (p t)).
  { intro t; apply NATIVE_DIAGONAL_ENERGY_CLASS_EXACT; apply Hp. }
  destruct (HGP_PATH_SURJECTIVE_UNIQUE h b Hcomplete g p Hg HL2)
    as [u [Hu [HE HU]]].
  exists u; split; [exact Hu|]; split; [|exact HU].
  intro t; apply NATIVE_DIAGONAL_ENERGY_VALUE_EXACT; apply HE.
Qed.

Print Assumptions NATIVE_DIAGONAL_ENERGY_CLASS_EXACT.
Print Assumptions NATIVE_DIAGONAL_STATE_REALIZATION.
Print Assumptions NATIVE_DIAGONAL_PAIRING_COMPLETION.
Print Assumptions NATIVE_DIAGONAL_PATH_REALIZATION.
