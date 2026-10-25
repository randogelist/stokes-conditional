From Stdlib Require Import Reals Lra Psatz.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.
Require Import LHGP_Dual LHGP_Gradient LHGP_ClosedSubspace LHGP_OrthogonalProjection.

Open Scope R_scope.

(* The ambient raw divergence is explicit input. Its orthogonal projection
   and the velocity-space GradientModel are constructed, not supplied.
   In an R3 instance rawDiv must be the actual L2 class of tensor divergence. *)
Record ProjectedDivergence (h : HilbertData) (s : ClosedLinearSubspace h)
    (m : DualTestModel) (rawDiv : HCarrier (DTest m) -> HCarrier h) : Type := {
  PDValue : HCarrier (DTest m) -> HCarrier (SubspaceHilbert s);
  PDAdd : forall x y, PDValue (HAdd (DTest m) x y) =
    HAdd (SubspaceHilbert s) (PDValue x) (PDValue y);
  PDScale : forall c x, PDValue (HScale (DTest m) c x) =
    HScale (SubspaceHilbert s) c (PDValue x);
  PDPairing : forall u z,
    HInner (SubspaceHilbert s) u (PDValue z) =
      HInner h (SubspaceInclude s u) (rawDiv z)
}.

Theorem PROJECTED_DIVERGENCE_CONSTRUCTED : forall h (s : ClosedLinearSubspace h)
    (m : DualTestModel) rawDiv,
  HComplete h ->
  (forall x y, rawDiv (HAdd (DTest m) x y) = HAdd h (rawDiv x) (rawDiv y)) ->
  (forall c x, rawDiv (HScale (DTest m) c x) = HScale h c (rawDiv x)) ->
  inhabited (ProjectedDivergence h s m rawDiv).
Proof.
  intros h s m rawDiv HC HA HS.
  destruct (CLOSED_SUBSPACE_PROJECTION_MAP_EXISTS h s HC) as [P HP].
  assert (Hm : forall z, subspace_predicate s (P (rawDiv z))).
  { intro z; exact (proj1 (HP (rawDiv z))). }
  constructor.
  refine {| PDValue := fun z => exist _ (P (rawDiv z)) (Hm z) |}.
  - intros x y; apply SubspaceInclude_injective; simpl.
    rewrite HA; exact (ORTHOGONAL_PROJECTION_ADD h s P HP (rawDiv x) (rawDiv y)).
  - intros c x; apply SubspaceInclude_injective; simpl.
    rewrite HS; exact (ORTHOGONAL_PROJECTION_SCALE h s P HP c (rawDiv x)).
  - intros u z; change (HInner h (SubspaceInclude s u) (P (rawDiv z)) =
      HInner h (SubspaceInclude s u) (rawDiv z)).
    apply (ORTHOGONAL_PROJECTION_PAIRING h s P HP).
    apply SubspaceInclude_member.
Qed.

Definition ProjectedGradientModel h s m rawDiv
    (d : ProjectedDivergence h s m rawDiv) : GradientModel (SubspaceHilbert s) :=
  {| GDual := m;
     GDiv := PDValue h s m rawDiv d;
     GDiv_add := PDAdd h s m rawDiv d;
     GDiv_scale := PDScale h s m rawDiv d |}.

Definition AmbientWeakGradient h (s : ClosedLinearSubspace h) (m : DualTestModel)
    rawDiv (u : HCarrier (SubspaceHilbert s)) (G : HCarrier (DTarget m)) : Prop :=
  forall z, - HInner h (SubspaceInclude s u) (rawDiv z) =
    HInner (DTarget m) G (DEmbed m z).

Theorem PROJECTED_GRADIENT_PROBE_EXACT : forall h s m rawDiv
    (d : ProjectedDivergence h s m rawDiv) u z,
  GradientProbe (SubspaceHilbert s) (ProjectedGradientModel h s m rawDiv d) u z =
    - HInner h (SubspaceInclude s u) (rawDiv z).
Proof.
  intros; unfold GradientProbe; change
    (- HInner (SubspaceHilbert s) u (PDValue h s m rawDiv d z) =
     - HInner h (SubspaceInclude s u) (rawDiv z)).
  rewrite (PDPairing h s m rawDiv d); reflexivity.
Qed.

Theorem PROJECTED_GRADIENT_GRAPH_EXACT : forall h s m rawDiv
    (d : ProjectedDivergence h s m rawDiv) u G,
  (ProbeRepresents m
    (GradientProbe (SubspaceHilbert s) (ProjectedGradientModel h s m rawDiv d) u) G
   <-> AmbientWeakGradient h s m rawDiv u G).
Proof.
  intros h s m rawDiv d u G; unfold ProbeRepresents, AmbientWeakGradient.
  split; intros H z.
  - rewrite <- (PROJECTED_GRADIENT_PROBE_EXACT h s m rawDiv d u z); apply H.
  - rewrite PROJECTED_GRADIENT_PROBE_EXACT; apply H.
Qed.

Theorem PROJECTED_GRADIENT_ENERGY_EXACT : forall h s m rawDiv
    (d : ProjectedDivergence h s m rawDiv) u D,
  (GradientEnergyAt (SubspaceHilbert s)
     (ProjectedGradientModel h s m rawDiv d) u D <->
   exists G, AmbientWeakGradient h s m rawDiv u G /\ HNorm (DTarget m) G = D).
Proof.
  intros h s m rawDiv d u D; unfold GradientEnergyAt; split.
  - intros [G [HG HN]]; exists G; split; [|exact HN].
    apply (proj1 (PROJECTED_GRADIENT_GRAPH_EXACT h s m rawDiv d u G)); exact HG.
  - intros [G [HG HN]]; exists G; split; [|exact HN].
    apply (proj2 (PROJECTED_GRADIENT_GRAPH_EXACT h s m rawDiv d u G)); exact HG.
Qed.

Theorem PROJECTED_GP_DISSIPATION_EXACT : forall h s m rawDiv
    (d : ProjectedDivergence h s m rawDiv) (b : OrthonormalBasis (SubspaceHilbert s)),
  HComplete h -> forall g p u D,
  GPNonzero g -> seq_eq (HGPEncode b g u) p ->
  (GPDissipationValue (SubspaceHilbert s) b
     (ProjectedGradientModel h s m rawDiv d) g p D <->
   exists G, AmbientWeakGradient h s m rawDiv u G /\ HNorm (DTarget m) G = D).
Proof.
  intros h s m rawDiv d b HC g p u D Hg Hu.
  rewrite (GRADIENT_DISSIPATION_EXACT (SubspaceHilbert s) b
    (SubspaceComplete h s HC) (ProjectedGradientModel h s m rawDiv d)
    g u p D Hg Hu).
  apply PROJECTED_GRADIENT_ENERGY_EXACT.
Qed.

Print Assumptions PROJECTED_DIVERGENCE_CONSTRUCTED.
Print Assumptions PROJECTED_GRADIENT_GRAPH_EXACT.
Print Assumptions PROJECTED_GP_DISSIPATION_EXACT.
