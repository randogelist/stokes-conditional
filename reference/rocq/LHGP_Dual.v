From Stdlib Require Import Reals Lra Psatz Lia.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.

Open Scope R_scope.

(* A dense test domain is allowed to be incomplete.  Its isometric image
   contains a separating orthonormal basis of the complete target space.
   No Riesz theorem, continuity of a probe, or gradient representation is
   a field of this model.  Concrete smooth tests and distributional
   differentiation on R^3 remain an explicit physical instantiation. *)

Record DualTestModel := {
  DTest : HilbertData;
  DTarget : HilbertData;
  DComplete : HComplete DTarget;
  DBasis : OrthonormalBasis DTarget;
  DEmbed : HCarrier DTest -> HCarrier DTarget;
  DEmbed_inner : forall x y,
    HInner DTarget (DEmbed x) (DEmbed y) = HInner DTest x y;
  DEmbed_add : forall x y,
    DEmbed (HAdd DTest x y) = HAdd DTarget (DEmbed x) (DEmbed y);
  DEmbed_scale : forall c x,
    DEmbed (HScale DTest c x) = HScale DTarget c (DEmbed x);
  DTestBasis : nat -> HCarrier DTest;
  DTestBasis_image : forall i,
    DEmbed (DTestBasis i) = HBasis DTarget DBasis i
}.

Definition ProbeLinear (m : DualTestModel)
    (F : HCarrier (DTest m) -> R) : Prop :=
  (forall x y, F (HAdd (DTest m) x y) = F x + F y) /\
  (forall c x, F (HScale (DTest m) c x) = c * F x).

Definition ProbeRepresents (m : DualTestModel)
    (F : HCarrier (DTest m) -> R) (G : HCarrier (DTarget m)) : Prop :=
  forall z, F z = HInner (DTarget m) G (DEmbed m z).

Definition VarUpper (m : DualTestModel)
    (F : HCarrier (DTest m) -> R) (M : R) : Prop :=
  forall z, 2 * F z - HNorm (DTest m) z <= M.

Definition VarValue (m : DualTestModel)
    (F : HCarrier (DTest m) -> R) (D : R) : Prop :=
  VarUpper m F D /\ (forall M, VarUpper m F M -> D <= M).

Definition ProbeCoefficients (m : DualTestModel)
    (F : HCarrier (DTest m) -> R) : Seq := fun i => F (DTestBasis m i).

Section DenseDomain.
Variable m : DualTestModel.

Lemma DEmbed_norm : forall z,
  HNorm (DTarget m) (DEmbed m z) = HNorm (DTest m) z.
Proof. intro z; unfold HNorm; apply DEmbed_inner. Qed.

Lemma DEmbed_zero : DEmbed m (HZero (DTest m)) = HZero (DTarget m).
Proof. apply HNorm_definite; rewrite DEmbed_norm, HNorm_zero; reflexivity. Qed.

Lemma DEmbed_distance : forall x y,
  HDist (DTarget m) (DEmbed m x) (DEmbed m y) = HDist (DTest m) x y.
Proof. intros; unfold HDist; rewrite !DEmbed_norm, DEmbed_inner; reflexivity. Qed.

Definition DTestONB : OrthonormalBasis (DTest m).
Proof.
  refine {| HBasis := DTestBasis m |}.
  - intros i j; rewrite <- DEmbed_inner, !DTestBasis_image.
    apply HBasis_orthonormal.
  - intros x Hx; apply HNorm_definite.
    assert (Himage : DEmbed m x = HZero (DTarget m)).
    { apply (HBasis_separating (DTarget m) (DBasis m)).
      intro i; rewrite <- DTestBasis_image, DEmbed_inner; apply Hx. }
    rewrite <- DEmbed_norm, Himage, HNorm_zero; reflexivity.
Defined.

Lemma DEmbed_finite : forall a n,
  DEmbed m (HFinite DTestONB a n) = HFinite (DBasis m) a n.
Proof.
  intros a n; induction n as [|n IH]; simpl.
  - apply DEmbed_zero.
  - rewrite DEmbed_add, DEmbed_scale, IH; simpl.
    rewrite DTestBasis_image; reflexivity.
Qed.

Lemma Probe_zero : forall F, ProbeLinear m F -> F (HZero (DTest m)) = 0.
Proof.
  intros F [Hadd Hscale].
  pose proof (Hadd (HZero (DTest m)) (HZero (DTest m))) as H.
  rewrite HAdd_zero_left in H; lra.
Qed.

Lemma Probe_sub : forall F,
  ProbeLinear m F -> forall x y,
    F (HSub (DTest m) x y) = F x - F y.
Proof.
  intros F [Hadd Hscale] x y; unfold HSub; rewrite Hadd, Hscale; ring.
Qed.

Lemma Probe_finite : forall F,
  ProbeLinear m F -> forall a n,
    F (HFinite DTestONB a n) = linear_prefix a (ProbeCoefficients m F) n.
Proof.
  intros F Hlin a n; destruct Hlin as [Hadd Hscale].
  induction n as [|n IH]; simpl.
  - apply Probe_zero; split; assumption.
  - rewrite Hadd, Hscale, IH; unfold linear_prefix, ProbeCoefficients; simpl; reflexivity.
Qed.

Lemma VarUpper_nonnegative : forall F M,
  ProbeLinear m F -> VarUpper m F M -> 0 <= M.
Proof.
  intros F M Hlin Hupper.
  specialize (Hupper (HZero (DTest m))).
  rewrite (Probe_zero F Hlin), HNorm_zero in Hupper; lra.
Qed.

Theorem VarUpper_coefficient_bound : forall F M,
  ProbeLinear m F -> VarUpper m F M -> forall n,
    energy_prefix (ProbeCoefficients m F) n <= M.
Proof.
  intros F M Hlin Hupper n.
  specialize (Hupper (HFinite DTestONB (ProbeCoefficients m F) n)).
  rewrite Probe_finite, HFinite_norm in Hupper by exact Hlin.
  unfold linear_prefix, energy_prefix in *; lra.
Qed.

Theorem VarUpper_square_bound : forall F M,
  ProbeLinear m F -> VarUpper m F M -> forall z,
    F z * F z <= M * HNorm (DTest m) z.
Proof.
  intros F M Hlin Hupper z.
  destruct (Req_EM_T (HNorm (DTest m) z) 0) as [Hz|Hnz].
  - rewrite (HNorm_definite (DTest m) z Hz), (Probe_zero F Hlin), HNorm_zero; lra.
  - pose proof (HNorm_nonnegative (DTest m) z) as Hpos.
    specialize (Hupper (HScale (DTest m) (F z / HNorm (DTest m) z) z)).
    destruct Hlin as [_ Hscale]; rewrite Hscale, HNorm_scale in Hupper.
    assert (Hidentity :
      (2 * (F z / HNorm (DTest m) z * F z) -
        (F z / HNorm (DTest m) z) * (F z / HNorm (DTest m) z) * HNorm (DTest m) z)
        * HNorm (DTest m) z = F z * F z).
    { field; exact Hnz. }
    pose proof (Rmult_le_compat_r (HNorm (DTest m) z) _ _ Hpos Hupper) as Hmul.
    rewrite Hidentity in Hmul; exact Hmul.
Qed.

Theorem Probe_projection_limit : forall F M,
  ProbeLinear m F -> VarUpper m F M -> forall z,
    linear_limit (HAnalysis (DBasis m) (DEmbed m z)) (ProbeCoefficients m F) (F z).
Proof.
  intros F M Hlin Hupper z eps Heps.
  pose proof (VarUpper_nonnegative F M Hlin Hupper) as HM.
  assert (Hdenom : 0 < M + 1) by lra.
  assert (Hdelta : 0 < eps * eps / (M + 1)).
  { apply Rdiv_lt_0_compat; nra. }
  destruct (HAnalysis_reconstruction (DTarget m) (DBasis m) (DComplete m)
    (DEmbed m z) _ Hdelta) as [N HN].
  exists N; intros n Hn; specialize (HN n Hn).
  rewrite <- (Probe_finite F Hlin).
  set (v := HFinite DTestONB (HAnalysis (DBasis m) (DEmbed m z)) n).
  assert (Hnorm : HNorm (DTest m) (HSub (DTest m) v z) =
    HDist (DTarget m) (HFinite (DBasis m)
      (HAnalysis (DBasis m) (DEmbed m z)) n) (DEmbed m z)).
  { rewrite HNorm_sub, <- DEmbed_distance; unfold v; rewrite DEmbed_finite; reflexivity. }
  pose proof (VarUpper_square_bound F M Hlin Hupper (HSub (DTest m) v z)) as Hbound.
  rewrite (Probe_sub F Hlin), Hnorm in Hbound.
  pose proof (HDist_nonnegative (DTarget m)
    (HFinite (DBasis m) (HAnalysis (DBasis m) (DEmbed m z)) n) (DEmbed m z)) as Hd.
  pose proof (Rmult_lt_compat_r (M + 1) _ _ Hdenom HN) as Hsmall.
  assert (Hcancel : eps * eps / (M + 1) * (M + 1) = eps * eps).
  { field; lra. }
  rewrite Hcancel in Hsmall; change (Rabs (F v - F z) < eps).
  apply Rabs_def1; nra.
Qed.

Theorem VarUpper_representation : forall F M,
  ProbeLinear m F -> VarUpper m F M ->
    exists G, ProbeRepresents m F G.
Proof.
  intros F M Hlin Hupper.
  assert (HL2 : CoordinateL2 (ProbeCoefficients m F)).
  { exists M; apply VarUpper_coefficient_bound; assumption. }
  destruct (HSynthesis_exists (DTarget m) (DBasis m) (DComplete m)
    (ProbeCoefficients m F) HL2) as [G [Hcoeff _]].
  exists G; intro z.
  pose proof (Probe_projection_limit F M Hlin Hupper z) as HF.
  pose proof (HAnalysis_linear_readout (DTarget m) (DBasis m) (DComplete m)
    (DEmbed m z) G) as HG.
  assert (Hprefix : seq_eq
    (linear_prefix (HAnalysis (DBasis m) (DEmbed m z)) (HAnalysis (DBasis m) G))
    (linear_prefix (HAnalysis (DBasis m) (DEmbed m z)) (ProbeCoefficients m F))).
  { intro n; apply linear_prefix_test_ext; exact Hcoeff. }
  apply (proj1 (SeqLimit_ext _ _ _ Hprefix)) in HG.
  pose proof (linear_limit_unique _ _ _ _ HF HG) as Heq.
  rewrite HInner_sym; exact Heq.
Qed.

Theorem ProbeRepresents_unique : forall F G K,
  ProbeRepresents m F G -> ProbeRepresents m F K -> G = K.
Proof.
  intros F G K HG HK; apply (HAnalysis_injective (DTarget m) (DBasis m)).
  intro i; unfold HAnalysis.
  rewrite <- !DTestBasis_image, <- HG, <- HK; reflexivity.
Qed.

Theorem ProbeRepresents_upper : forall F G,
  ProbeRepresents m F G -> VarUpper m F (HNorm (DTarget m) G).
Proof.
  intros F G HG z; rewrite HG, <- DEmbed_norm.
  pose proof (HDist_nonnegative (DTarget m) G (DEmbed m z)); unfold HDist in *; lra.
Qed.

Theorem ProbeRepresents_value : forall F G,
  ProbeLinear m F -> ProbeRepresents m F G ->
    VarValue m F (HNorm (DTarget m) G).
Proof.
  intros F G Hlin HG; split; [apply ProbeRepresents_upper; exact HG|].
  intros M HM.
  destruct (HAnalysis_parseval (DTarget m) (DBasis m) (DComplete m) G)
    as [_ Hleast].
  apply Hleast; intro n.
  assert (Hcoeff : seq_eq (HAnalysis (DBasis m) G) (ProbeCoefficients m F)).
  { intro i; unfold HAnalysis, ProbeCoefficients.
    rewrite HG, DTestBasis_image; reflexivity. }
  rewrite (energy_prefix_ext _ _ n Hcoeff).
  apply VarUpper_coefficient_bound; assumption.
Qed.

Lemma VarValue_unique : forall F D E,
  VarValue m F D -> VarValue m F E -> D = E.
Proof.
  intros F D E [HDup HDleast] [HEup HEleast].
  specialize (HDleast E HEup); specialize (HEleast D HDup); lra.
Qed.

Theorem DUAL_FINITE_VARIATIONAL_IFF_RIESZ : forall F,
  ProbeLinear m F ->
  ((exists M, VarUpper m F M) <-> exists G, ProbeRepresents m F G).
Proof.
  intros F Hlin; split.
  - intros [M HM]; apply (VarUpper_representation F M); assumption.
  - intros [G HG]; exists (HNorm (DTarget m) G); apply ProbeRepresents_upper; exact HG.
Qed.

Theorem DUAL_VARIATIONAL_VALUE_IFF_GRADIENT : forall F D,
  ProbeLinear m F ->
  (VarValue m F D <-> exists G,
    ProbeRepresents m F G /\ HNorm (DTarget m) G = D).
Proof.
  intros F D Hlin; split.
  - intro HD.
    destruct (VarUpper_representation F D Hlin (proj1 HD)) as [G HG].
    exists G; split; [exact HG|].
    apply (VarValue_unique F); [apply ProbeRepresents_value; assumption|exact HD].
  - intros [G [HG HE]].
    rewrite <- HE; apply ProbeRepresents_value; assumption.
Qed.

Theorem DUAL_VARIATIONAL_REALIZATION_UNIQUE : forall F D,
  ProbeLinear m F -> VarValue m F D -> exists G,
    ProbeRepresents m F G /\ HNorm (DTarget m) G = D /\
    (forall K, ProbeRepresents m F K -> K = G).
Proof.
  intros F D Hlin HD.
  destruct (proj1 (DUAL_VARIATIONAL_VALUE_IFF_GRADIENT F D Hlin) HD) as [G [HG HE]].
  exists G; split; [exact HG|]; split; [exact HE|].
  intros K HK; apply (ProbeRepresents_unique F); assumption.
Qed.

End DenseDomain.

Print Assumptions VarUpper_square_bound.
Print Assumptions VarUpper_representation.
Print Assumptions DUAL_VARIATIONAL_VALUE_IFF_GRADIENT.
Print Assumptions DUAL_VARIATIONAL_REALIZATION_UNIQUE.
