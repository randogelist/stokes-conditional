From Stdlib Require Import Reals Lra Psatz Lia Logic.Classical_Pred_Type.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.
Require Import LHGP_Dual LHGP_Gradient.
Require Import LHGP_WeakTopology LHGP_TimeBorel.

Open Scope R_scope.

(* Forward-only weak-gradient identification. The tensor space k needs an
   inner product and a dense family of tests. No tensor completeness,
   tensor basis, Riesz theorem, or converse gradient construction is used.
   A concrete spatial application must realize FGEmbed and FGDiv and
   supply the known integration-by-parts identity WeakGradientForward. *)

Record ForwardGradientData (h k : HilbertData) := {
  FGTest : Type;
  FGEmbed : FGTest -> HCarrier k;
  FGDiv : FGTest -> HCarrier h;
  FGDense : forall G eps, 0 < eps ->
    exists z, HDist k G (FGEmbed z) < eps
}.

Definition WeakGradientForward h k (fg : ForwardGradientData h k)
    (u : HCarrier h) (G : HCarrier k) : Prop :=
  forall z, - HInner h u (FGDiv h k fg z) =
    HInner k G (FGEmbed h k fg z).

Definition ForwardGradientEnergyAt h k (fg : ForwardGradientData h k)
    (u : HCarrier h) (D : R) : Prop :=
  exists G, WeakGradientForward h k fg u G /\ HNorm k G = D.

Definition ForwardVariationalUpper h k (fg : ForwardGradientData h k)
    (u : HCarrier h) (M : R) : Prop :=
  forall z, 2 * (- HInner h u (FGDiv h k fg z)) -
    HNorm k (FGEmbed h k fg z) <= M.

Definition ForwardVariationalValue h k (fg : ForwardGradientData h k)
    (u : HCarrier h) (D : R) : Prop :=
  ForwardVariationalUpper h k fg u D /\
  forall M, ForwardVariationalUpper h k fg u M -> D <= M.

Definition ForwardGPDissipationUpper h k (b : OrthonormalBasis h)
    (fg : ForwardGradientData h k) (g p : Seq) (D : R) : Prop :=
  DissipationUpper
    (fun z => HAnalysis b (FGDiv h k fg z))
    (fun z => HNorm k (FGEmbed h k fg z)) (decode g p) D.

Definition ForwardGPDissipationValue h k (b : OrthonormalBasis h)
    (fg : ForwardGradientData h k) (g p : Seq) (D : R) : Prop :=
  DissipationValue
    (fun z => HAnalysis b (FGDiv h k fg z))
    (fun z => HNorm k (FGEmbed h k fg z)) (decode g p) D.

Lemma FORWARD_GRADIENT_COMPLETED_SQUARE :
  forall h k (fg : ForwardGradientData h k) u G,
  WeakGradientForward h k fg u G -> forall z,
  2 * (- HInner h u (FGDiv h k fg z)) - HNorm k (FGEmbed h k fg z) =
  HNorm k G - HDist k G (FGEmbed h k fg z).
Proof.
  intros h k fg u G HG z; rewrite HG; unfold HDist; ring.
Qed.

Theorem FORWARD_GRADIENT_VARIATIONAL_VALUE :
  forall h k (fg : ForwardGradientData h k) u G,
  WeakGradientForward h k fg u G ->
  ForwardVariationalValue h k fg u (HNorm k G).
Proof.
  intros h k fg u G HG; split.
  - intro z; rewrite (FORWARD_GRADIENT_COMPLETED_SQUARE h k fg u G HG z).
    pose proof (HDist_nonnegative k G (FGEmbed h k fg z)); lra.
  - intros M HM; apply Rnot_lt_le; intro Hbad.
    assert (Heps : 0 < HNorm k G - M) by lra.
    destruct (FGDense h k fg G _ Heps) as [z Hz].
    specialize (HM z).
    rewrite (FORWARD_GRADIENT_COMPLETED_SQUARE h k fg u G HG z) in HM.
    lra.
Qed.

Theorem FORWARD_GRADIENT_LINEAR_READOUT :
  forall h k (b : OrthonormalBasis h), HComplete h ->
  forall (fg : ForwardGradientData h k) g u p,
  GPNonzero g -> seq_eq (HGPEncode b g u) p ->
  forall z, linear_limit (decode g p) (HAnalysis b (FGDiv h k fg z))
    (HInner h u (FGDiv h k fg z)).
Proof.
  intros h k b Hcomplete fg g u p Hg Henc z.
  assert (Hdec : seq_eq (decode g p) (HAnalysis b u)).
  { intro i; unfold decode; rewrite <- (Henc i).
    unfold HGPEncode, encode; field; apply Hg. }
  apply (proj2 (linear_limit_ext _ _ (HAnalysis b (FGDiv h k fg z))
    (HInner h u (FGDiv h k fg z)) Hdec)).
  apply HAnalysis_linear_readout; exact Hcomplete.
Qed.

Theorem FORWARD_GP_VARIATIONAL_UPPER_EXACT :
  forall h k (b : OrthonormalBasis h), HComplete h ->
  forall (fg : ForwardGradientData h k) g u p M,
  GPNonzero g -> seq_eq (HGPEncode b g u) p ->
  (ForwardGPDissipationUpper h k b fg g p M <->
   ForwardVariationalUpper h k fg u M).
Proof.
  intros h k b Hcomplete fg g u p M Hg Henc; split.
  - intros HU z.
    specialize (HU z (HInner h u (FGDiv h k fg z))
      (FORWARD_GRADIENT_LINEAR_READOUT h k b Hcomplete fg g u p Hg Henc z)).
    lra.
  - intros HV z l Hl.
    pose proof (FORWARD_GRADIENT_LINEAR_READOUT h k b Hcomplete fg g u p Hg Henc z)
      as Hread.
    assert (Heq : l = HInner h u (FGDiv h k fg z)).
    { eapply linear_limit_unique; [exact Hl|exact Hread]. }
    specialize (HV z); rewrite Heq; lra.
Qed.

Theorem FORWARD_GP_VARIATIONAL_VALUE_EXACT :
  forall h k (b : OrthonormalBasis h), HComplete h ->
  forall (fg : ForwardGradientData h k) g u p D,
  GPNonzero g -> seq_eq (HGPEncode b g u) p ->
  (ForwardGPDissipationValue h k b fg g p D <->
   ForwardVariationalValue h k fg u D).
Proof.
  intros h k b Hcomplete fg g u p D Hg Henc.
  assert (Hupper : forall M,
    ForwardGPDissipationUpper h k b fg g p M <->
    ForwardVariationalUpper h k fg u M).
  { intro M; apply FORWARD_GP_VARIATIONAL_UPPER_EXACT; assumption. }
  split; intros [HU Hleast]; split.
  - apply (proj1 (Hupper D)); exact HU.
  - intros M HM; apply Hleast; apply (proj2 (Hupper M)); exact HM.
  - apply (proj2 (Hupper D)); exact HU.
  - intros M HM; apply Hleast; apply (proj1 (Hupper M)); exact HM.
Qed.

Theorem FORWARD_GRADIENT_DISSIPATION_EXACT :
  forall h k (b : OrthonormalBasis h), HComplete h ->
  forall (fg : ForwardGradientData h k) g u p G,
  GPNonzero g -> seq_eq (HGPEncode b g u) p ->
  WeakGradientForward h k fg u G ->
  ForwardGPDissipationValue h k b fg g p (HNorm k G).
Proof.
  intros h k b Hcomplete fg g u p G Hg Henc HG.
  apply (proj2 (FORWARD_GP_VARIATIONAL_VALUE_EXACT h k b Hcomplete
    fg g u p (HNorm k G) Hg Henc)).
  apply FORWARD_GRADIENT_VARIATIONAL_VALUE; exact HG.
Qed.

Theorem FORWARD_GRADIENT_ENERGY_TO_GP_VALUE :
  forall h k (b : OrthonormalBasis h), HComplete h ->
  forall (fg : ForwardGradientData h k) g u p D,
  GPNonzero g -> seq_eq (HGPEncode b g u) p ->
  ForwardGradientEnergyAt h k fg u D ->
  ForwardGPDissipationValue h k b fg g p D.
Proof.
  intros h k b Hcomplete fg g u p D Hg Henc [G [HG HD]].
  rewrite <- HD; apply FORWARD_GRADIENT_DISSIPATION_EXACT with (u := u);
    assumption.
Qed.

Definition ForwardDissipationCostAlong h k (fg : ForwardGradientData h k)
    (u : R -> HCarrier h) (z : FGTest h k fg) (t : R) : R :=
  2 * (- HInner h (u t) (FGDiv h k fg z)) - HNorm k (FGEmbed h k fg z).

Lemma FORWARD_DISSIPATION_TEST_COST_CONTINUOUS :
  forall h k (fg : ForwardGradientData h k) u T,
  HWeakContinuous h u T -> forall z,
  ScalarContinuousOn T (ForwardDissipationCostAlong h k fg u z).
Proof.
  intros h k fg u T Hweak z.
  eapply ScalarContinuousOn_ext with
    (f := fun t => (-2) * HInner h (u t) (FGDiv h k fg z) +
                   (- HNorm k (FGEmbed h k fg z))).
  - intros t Ht; unfold ForwardDissipationCostAlong; ring.
  - apply ScalarContinuousOn_add.
    + apply ScalarContinuousOn_scale; apply Hweak.
    + apply ScalarContinuousOn_constant.
Qed.

(* Lower semicontinuity of the extended variational dissipation is stated
   by open strict superlevels. A violating test yields the open neighborhood;
   no finite gradient, countable test reduction, or target completion is
   required. Openness and Borel measurability are relative to [0,T]. *)
Theorem FORWARD_DISSIPATION_STRICT_SUPERLEVEL_TIME_OPEN :
  forall h k (fg : ForwardGradientData h k) u T M,
  HWeakContinuous h u T ->
  TimeOpen T (fun t => ~ ForwardVariationalUpper h k fg (u t) M).
Proof.
  intros h k fg u T M Hweak t Ht Hnot.
  unfold ForwardVariationalUpper in Hnot.
  apply not_all_ex_not in Hnot; destruct Hnot as [z Hz].
  assert (Hgap : 0 < ForwardDissipationCostAlong h k fg u z t - M).
  { unfold ForwardDissipationCostAlong; lra. }
  destruct (FORWARD_DISSIPATION_TEST_COST_CONTINUOUS h k fg u T Hweak z
    t Ht _ Hgap) as [delta [Hdelta Hnear]].
  exists delta; split; [exact Hdelta|].
  intros s Hs Hst Hbound.
  specialize (Hnear s Hs Hst).
  apply Rabs_def2 in Hnear; destruct Hnear as [Hupper Hlower].
  specialize (Hbound z); unfold ForwardDissipationCostAlong in *; lra.
Qed.

Theorem FORWARD_DISSIPATION_SUBLEVEL_TIME_CLOSED :
  forall h k (fg : ForwardGradientData h k) u T M,
  HWeakContinuous h u T ->
  TimeClosed T (fun t => ForwardVariationalUpper h k fg (u t) M).
Proof.
  intros h k fg u T M Hweak.
  apply FORWARD_DISSIPATION_STRICT_SUPERLEVEL_TIME_OPEN; exact Hweak.
Qed.

Theorem FORWARD_DISSIPATION_SUBLEVEL_TIME_BOREL :
  forall h k (fg : ForwardGradientData h k) u T M,
  HWeakContinuous h u T ->
  TimeBorel T (fun t => ForwardVariationalUpper h k fg (u t) M).
Proof.
  intros h k fg u T M Hweak; apply TB_closed.
  apply FORWARD_DISSIPATION_SUBLEVEL_TIME_CLOSED; exact Hweak.
Qed.

(* Compatibility adapter only: the earlier two-way gradient model has
   stronger hypotheses. Its lifted ONB supplies the density needed by the
   forward model. The theorems above do not depend on this adapter. *)
Definition GradientModelToForward h (gm : GradientModel h) :
  ForwardGradientData h (DTarget (GDual h gm)).
Proof.
  refine {| FGTest := HCarrier (DTest (GDual h gm));
    FGEmbed := DEmbed (GDual h gm); FGDiv := GDiv h gm |}.
  intros G eps Heps.
  destruct (HAnalysis_reconstruction (DTarget (GDual h gm))
    (DBasis (GDual h gm)) (DComplete (GDual h gm)) G eps Heps) as [N HN].
  exists (HFinite (DTestONB (GDual h gm)) (HAnalysis (DBasis (GDual h gm)) G) N).
  rewrite DEmbed_finite, HDist_sym; apply HN; apply Nat.le_refl.
Defined.

Theorem GRADIENT_MODEL_FORWARD_ENERGY_EXACT :
  forall h (gm : GradientModel h) u D,
  (ForwardGradientEnergyAt h (DTarget (GDual h gm)) (GradientModelToForward h gm) u D
   <-> GradientEnergyAt h gm u D).
Proof. reflexivity. Qed.

Print Assumptions FORWARD_GRADIENT_VARIATIONAL_VALUE.
Print Assumptions FORWARD_GRADIENT_DISSIPATION_EXACT.
Print Assumptions FORWARD_GRADIENT_ENERGY_TO_GP_VALUE.
Print Assumptions FORWARD_DISSIPATION_SUBLEVEL_TIME_BOREL.
