From Stdlib Require Import Reals Lra Psatz.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.
Require Import LHGP_Dual.

Open Scope R_scope.

(* GDiv is the velocity-space representer of the divergence pairing.
   For solenoidal L2 on R^3 this is the projected divergence of a tensor
   test, characterized by <u,GDiv z> = <u,div z> for solenoidal u.
   Ordinary div z need not itself be solenoidal. A concrete physical
   instantiation must establish that pairing identity and identify the
   dense dual test/target spaces. No such instantiation is asserted here.

   The finite variational bound is not assumed to give a gradient: that
   implication is obtained from the proved dense-domain dual theorem. *)

Record GradientModel (h : HilbertData) := {
  GDual : DualTestModel;
  GDiv : HCarrier (DTest GDual) -> HCarrier h;
  GDiv_add : forall x y,
    GDiv (HAdd (DTest GDual) x y) = HAdd h (GDiv x) (GDiv y);
  GDiv_scale : forall c x,
    GDiv (HScale (DTest GDual) c x) = HScale h c (GDiv x)
}.

Definition GradientProbe h (gm : GradientModel h) (x : HCarrier h)
  (z : HCarrier (DTest (GDual h gm))) : R :=
  - HInner h x (GDiv h gm z).

Definition GradientEnergyAt h (gm : GradientModel h)
  (x : HCarrier h) (D : R) : Prop :=
  exists G : HCarrier (DTarget (GDual h gm)),
    ProbeRepresents (GDual h gm) (GradientProbe h gm x) G /\
    HNorm (DTarget (GDual h gm)) G = D.

Definition GPDissipationUpper h (b : OrthonormalBasis h)
  (gm : GradientModel h) (g p : Seq) (D : R) : Prop :=
  DissipationUpper
    (fun z => HAnalysis b (GDiv h gm z))
    (fun z => HNorm (DTest (GDual h gm)) z) (decode g p) D.

Definition GPDissipationValue h (b : OrthonormalBasis h)
  (gm : GradientModel h) (g p : Seq) (D : R) : Prop :=
  DissipationValue
    (fun z => HAnalysis b (GDiv h gm z))
    (fun z => HNorm (DTest (GDual h gm)) z) (decode g p) D.

Theorem GRADIENT_PROBE_LINEAR : forall h (gm : GradientModel h) x,
  ProbeLinear (GDual h gm) (GradientProbe h gm x).
Proof.
  intros h gm x; split.
  - intros y z; unfold GradientProbe.
    rewrite GDiv_add, HInner_add_r; ring.
  - intros c z; unfold GradientProbe.
    rewrite GDiv_scale, HInner_scale_r; ring.
Qed.

Theorem GRADIENT_LINEAR_READOUT : forall h (b : OrthonormalBasis h),
  HComplete h -> forall (gm : GradientModel h) g x p,
  GPNonzero g -> seq_eq (HGPEncode b g x) p ->
  forall z, linear_limit (decode g p) (HAnalysis b (GDiv h gm z))
    (HInner h x (GDiv h gm z)).
Proof.
  intros h b Hcomplete gm g x p Hg Henc z.
  assert (Hdec : seq_eq (decode g p) (HAnalysis b x)).
  { intro i; unfold decode; rewrite <- (Henc i).
    unfold HGPEncode, encode; field; apply Hg. }
  apply (proj2 (linear_limit_ext _ _ (HAnalysis b (GDiv h gm z))
    (HInner h x (GDiv h gm z)) Hdec)).
  apply HAnalysis_linear_readout; exact Hcomplete.
Qed.

Theorem GRADIENT_DISSIPATION_UPPER_EXACT :
  forall h (b : OrthonormalBasis h), HComplete h ->
  forall (gm : GradientModel h) g x p D,
  GPNonzero g -> seq_eq (HGPEncode b g x) p ->
  (GPDissipationUpper h b gm g p D <->
   VarUpper (GDual h gm) (GradientProbe h gm x) D).
Proof.
  intros h b Hcomplete gm g x p D Hg Henc; split.
  - intros HU z.
    specialize (HU z (HInner h x (GDiv h gm z))
      (GRADIENT_LINEAR_READOUT h b Hcomplete gm g x p Hg Henc z)).
    unfold GradientProbe; lra.
  - intros HV z l Hl.
    pose proof (GRADIENT_LINEAR_READOUT h b Hcomplete gm g x p Hg Henc z)
      as Hread.
    assert (Heq : l = HInner h x (GDiv h gm z)).
    { eapply linear_limit_unique; [exact Hl | exact Hread]. }
    specialize (HV z); unfold GradientProbe in HV; rewrite Heq; lra.
Qed.

Theorem GRADIENT_DISSIPATION_VALUE_EXACT :
  forall h (b : OrthonormalBasis h), HComplete h ->
  forall (gm : GradientModel h) g x p D,
  GPNonzero g -> seq_eq (HGPEncode b g x) p ->
  (GPDissipationValue h b gm g p D <->
   VarValue (GDual h gm) (GradientProbe h gm x) D).
Proof.
  intros h b Hcomplete gm g x p D Hg Henc.
  assert (Hupper : forall M,
    GPDissipationUpper h b gm g p M <->
    VarUpper (GDual h gm) (GradientProbe h gm x) M).
  { intro M; apply GRADIENT_DISSIPATION_UPPER_EXACT; assumption. }
  split; intros [HU Hleast]; split.
  - apply (proj1 (Hupper D)); exact HU.
  - intros M HM; apply Hleast; apply (proj2 (Hupper M)); exact HM.
  - apply (proj2 (Hupper D)); exact HU.
  - intros M HM; apply Hleast; apply (proj1 (Hupper M)); exact HM.
Qed.

Theorem GRADIENT_DISSIPATION_EXACT :
  forall h (b : OrthonormalBasis h), HComplete h ->
  forall (gm : GradientModel h) g x p D,
  GPNonzero g -> seq_eq (HGPEncode b g x) p ->
  (GPDissipationValue h b gm g p D <-> GradientEnergyAt h gm x D).
Proof.
  intros h b Hcomplete gm g x p D Hg Henc.
  rewrite (GRADIENT_DISSIPATION_VALUE_EXACT h b Hcomplete gm g x p D Hg Henc).
  unfold GradientEnergyAt.
  apply DUAL_VARIATIONAL_VALUE_IFF_GRADIENT.
  apply GRADIENT_PROBE_LINEAR.
Qed.

Print Assumptions GRADIENT_PROBE_LINEAR.
Print Assumptions GRADIENT_LINEAR_READOUT.
Print Assumptions GRADIENT_DISSIPATION_UPPER_EXACT.
Print Assumptions GRADIENT_DISSIPATION_VALUE_EXACT.
Print Assumptions GRADIENT_DISSIPATION_EXACT.
