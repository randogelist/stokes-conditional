From Stdlib Require Import Reals Lra Psatz Lia.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.
Require Import LHGP_Dual LHGP_Gradient LHGP_DissipationTopology.

Open Scope R_scope.

(* The gradient graph is a relation between two actual carrier values.
   Its completeness is derived from the two existing Hilbert completions
   and the proved closed-graph theorem; no additional completion or
   reconstruction premise is introduced. The concrete Sobolev-space
   interpretation on R^3 remains a physical instantiation. *)

Definition GradientGraph (h : HilbertData) (gm : GradientModel h)
    (x : HCarrier h) (G : HCarrier (DTarget (GDual h gm))) : Prop :=
  ProbeRepresents (GDual h gm) (GradientProbe h gm x) G.

Definition GraphEnergy (h : HilbertData) (gm : GradientModel h)
    (x : HCarrier h) (G : HCarrier (DTarget (GDual h gm))) : R :=
  HNorm h x + HNorm (DTarget (GDual h gm)) G.

Definition GraphDistance (h : HilbertData) (gm : GradientModel h)
    (x y : HCarrier h)
    (G K : HCarrier (DTarget (GDual h gm))) : R :=
  HDist h x y + HDist (DTarget (GDual h gm)) G K.

Definition GraphCauchy (h : HilbertData) (gm : GradientModel h)
    (xn : nat -> HCarrier h)
    (Gn : nat -> HCarrier (DTarget (GDual h gm))) : Prop :=
  forall eps : R, 0 < eps -> exists N : nat,
    forall n m : nat, (N <= n)%nat -> (N <= m)%nat ->
      GraphDistance h gm (xn n) (xn m) (Gn n) (Gn m) < eps.

Definition GraphConverges (h : HilbertData) (gm : GradientModel h)
    (xn : nat -> HCarrier h)
    (Gn : nat -> HCarrier (DTarget (GDual h gm)))
    (x : HCarrier h) (G : HCarrier (DTarget (GDual h gm))) : Prop :=
  forall eps : R, 0 < eps -> exists N : nat,
    forall n : nat, (N <= n)%nat ->
      GraphDistance h gm (xn n) x (Gn n) G < eps.

Theorem GRADIENT_GRAPH_ZERO : forall h (gm : GradientModel h),
  GradientGraph h gm (HZero h) (HZero (DTarget (GDual h gm))).
Proof.
  intros h gm z; unfold GradientProbe.
  rewrite !HInner_zero_l; ring.
Qed.

Theorem GRADIENT_GRAPH_ADD : forall h (gm : GradientModel h) x y G K,
  GradientGraph h gm x G -> GradientGraph h gm y K ->
  GradientGraph h gm (HAdd h x y)
    (HAdd (DTarget (GDual h gm)) G K).
Proof.
  intros h gm x y G K Hx Hy z.
  unfold GradientGraph, ProbeRepresents, GradientProbe in *.
  rewrite !HInner_add_l.
  specialize (Hx z); specialize (Hy z); lra.
Qed.

Theorem GRADIENT_GRAPH_SCALE : forall h (gm : GradientModel h) c x G,
  GradientGraph h gm x G ->
  GradientGraph h gm (HScale h c x)
    (HScale (DTarget (GDual h gm)) c G).
Proof.
  intros h gm c x G Hx z; unfold GradientGraph, ProbeRepresents, GradientProbe in *.
  rewrite !HInner_scale_l; specialize (Hx z); nra.
Qed.

Theorem GRADIENT_GRAPH_SUB : forall h (gm : GradientModel h) x y G K,
  GradientGraph h gm x G -> GradientGraph h gm y K ->
  GradientGraph h gm (HSub h x y)
    (HSub (DTarget (GDual h gm)) G K).
Proof.
  intros h gm x y G K Hx Hy; unfold HSub.
  apply GRADIENT_GRAPH_ADD; [exact Hx |].
  apply GRADIENT_GRAPH_SCALE; exact Hy.
Qed.

Theorem GRADIENT_GRAPH_UNIQUE : forall h (gm : GradientModel h) x G K,
  GradientGraph h gm x G -> GradientGraph h gm x K -> G = K.
Proof.
  intros h gm x G K HG HK.
  exact (ProbeRepresents_unique (GDual h gm) (GradientProbe h gm x) G K HG HK).
Qed.

Lemma GraphEnergy_nonnegative : forall h (gm : GradientModel h) x G,
  0 <= GraphEnergy h gm x G.
Proof.
  intros h gm x G; unfold GraphEnergy.
  pose proof (HNorm_nonnegative h x).
  pose proof (HNorm_nonnegative (DTarget (GDual h gm)) G); lra.
Qed.

Lemma GraphDistance_nonnegative : forall h (gm : GradientModel h) x y G K,
  0 <= GraphDistance h gm x y G K.
Proof.
  intros h gm x y G K; unfold GraphDistance.
  pose proof (HDist_nonnegative h x y).
  pose proof (HDist_nonnegative (DTarget (GDual h gm)) G K); lra.
Qed.

Theorem SOBOLEV_GRAPH_DISTANCE_IS_DIFFERENCE_ENERGY :
  forall h (gm : GradientModel h) x y G K,
  GraphDistance h gm x y G K =
    GraphEnergy h gm (HSub h x y) (HSub (DTarget (GDual h gm)) G K).
Proof.
  intros; unfold GraphDistance, GraphEnergy; rewrite !HNorm_sub; reflexivity.
Qed.

Theorem SOBOLEV_GRAPH_CAUCHY_IFF_COMPONENTS : forall h (gm : GradientModel h) xn Gn,
  GraphCauchy h gm xn Gn <->
  HCauchy h xn /\ HCauchy (DTarget (GDual h gm)) Gn.
Proof.
  intros h gm xn Gn; split.
  - intros Hgraph; split; intros eps Heps;
      destruct (Hgraph eps Heps) as [N HN]; exists N;
      intros n m Hn Hm; specialize (HN n m Hn Hm);
      unfold GraphDistance in HN.
    + pose proof (HDist_nonnegative (DTarget (GDual h gm)) (Gn n) (Gn m)); lra.
    + pose proof (HDist_nonnegative h (xn n) (xn m)); lra.
  - intros [Hx HG] eps Heps.
    destruct (Hx (eps / 2) ltac:(lra)) as [Nx HNx].
    destruct (HG (eps / 2) ltac:(lra)) as [NG HNG].
    exists (Nat.max Nx NG); intros n m Hn Hm.
    specialize (HNx n m ltac:(lia) ltac:(lia)).
    specialize (HNG n m ltac:(lia) ltac:(lia)).
    unfold GraphDistance; lra.
Qed.

Theorem SOBOLEV_GRAPH_CONVERGES_IFF_COMPONENTS :
  forall h (gm : GradientModel h) xn Gn x G,
  GraphConverges h gm xn Gn x G <->
  HConverges h xn x /\ HConverges (DTarget (GDual h gm)) Gn G.
Proof.
  intros h gm xn Gn x G; split.
  - intros Hgraph; split; intros eps Heps;
      destruct (Hgraph eps Heps) as [N HN]; exists N;
      intros n Hn; specialize (HN n Hn); unfold GraphDistance in HN.
    + pose proof (HDist_nonnegative (DTarget (GDual h gm)) (Gn n) G); lra.
    + pose proof (HDist_nonnegative h (xn n) x); lra.
  - intros [Hx HG] eps Heps.
    destruct (Hx (eps / 2) ltac:(lra)) as [Nx HNx].
    destruct (HG (eps / 2) ltac:(lra)) as [NG HNG].
    exists (Nat.max Nx NG); intros n Hn.
    specialize (HNx n ltac:(lia)); specialize (HNG n ltac:(lia)).
    unfold GraphDistance; lra.
Qed.

Theorem SOBOLEV_COMPONENT_CAUCHY_COMPLETES : forall h (gm : GradientModel h),
  HComplete h -> forall xn Gn,
  HCauchy h xn -> HCauchy (DTarget (GDual h gm)) Gn ->
  (forall n, GradientGraph h gm (xn n) (Gn n)) ->
  exists x G,
    HConverges h xn x /\
    HConverges (DTarget (GDual h gm)) Gn G /\
    GradientGraph h gm x G.
Proof.
  intros h gm Hcomplete xn Gn Hx HG Hgraph.
  destruct (Hcomplete xn Hx) as [x Hlimitx].
  destruct (DComplete (GDual h gm) Gn HG) as [G HlimitG].
  exists x, G; split; [exact Hlimitx |]; split; [exact HlimitG |].
  exact (GRADIENT_GRAPH_STRONG_CLOSED h gm xn x Gn G Hlimitx HlimitG Hgraph).
Qed.

Theorem SOBOLEV_GRAPH_COMPLETE : forall h (gm : GradientModel h),
  HComplete h -> forall xn Gn,
  GraphCauchy h gm xn Gn ->
  (forall n, GradientGraph h gm (xn n) (Gn n)) ->
  exists x G, GradientGraph h gm x G /\ GraphConverges h gm xn Gn x G.
Proof.
  intros h gm Hcomplete xn Gn HC HG.
  destruct (proj1 (SOBOLEV_GRAPH_CAUCHY_IFF_COMPONENTS h gm xn Gn) HC)
    as [HCx HCG].
  destruct (SOBOLEV_COMPONENT_CAUCHY_COMPLETES h gm Hcomplete xn Gn HCx HCG HG)
    as [x [G [Hx [HK Hgraph]]]].
  exists x, G; split; [exact Hgraph |].
  apply (proj2 (SOBOLEV_GRAPH_CONVERGES_IFF_COMPONENTS h gm xn Gn x G)).
  split; assumption.
Qed.

(* Actual scalar graph energy converges as well as the difference energy. *)
Theorem SOBOLEV_HNORM_STRONG_CONTINUOUS : forall h xn x,
  HConverges h xn x -> SeqLimit (fun n => HNorm h (xn n)) (HNorm h x).
Proof.
  intros h xn x Hconv eps Heps.
  pose proof (HStrongSequential_to_weak h xn x Hconv x) as Hpair.
  destruct (Hconv (eps / 2) ltac:(lra)) as [Nd HNd].
  destruct (Hpair (eps / 4) ltac:(lra)) as [Ni HNi].
  exists (Nat.max Nd Ni); intros n Hn.
  specialize (HNd n ltac:(lia)); specialize (HNi n ltac:(lia)).
  destruct (Rabs_def2 _ _ HNi) as [Hp Hm].
  pose proof (HDist_nonnegative h (xn n) x) as Hd.
  unfold HDist, HNorm in *; apply Rabs_def1; lra.
Qed.

Theorem SOBOLEV_GRAPH_ENERGY_CONTINUOUS : forall h (gm : GradientModel h) xn Gn x G,
  GraphConverges h gm xn Gn x G ->
  SeqLimit (fun n => GraphEnergy h gm (xn n) (Gn n)) (GraphEnergy h gm x G).
Proof.
  intros h gm xn Gn x G Hgraph eps Heps.
  destruct (proj1 (SOBOLEV_GRAPH_CONVERGES_IFF_COMPONENTS h gm xn Gn x G) Hgraph)
    as [Hx HG].
  destruct (SOBOLEV_HNORM_STRONG_CONTINUOUS h xn x Hx (eps / 2) ltac:(lra))
    as [Nx HNx].
  destruct (SOBOLEV_HNORM_STRONG_CONTINUOUS (DTarget (GDual h gm)) Gn G HG
    (eps / 2) ltac:(lra)) as [NG HNG].
  exists (Nat.max Nx NG); intros n Hn.
  specialize (HNx n ltac:(lia)); specialize (HNG n ltac:(lia)).
  unfold GraphEnergy.
  replace (HNorm h (xn n) + HNorm (DTarget (GDual h gm)) (Gn n) -
    (HNorm h x + HNorm (DTarget (GDual h gm)) G)) with
    ((HNorm h (xn n) - HNorm h x) +
     (HNorm (DTarget (GDual h gm)) (Gn n) - HNorm (DTarget (GDual h gm)) G))
    by ring.
  eapply Rle_lt_trans; [apply Rabs_triang | lra].
Qed.

Print Assumptions GRADIENT_GRAPH_ADD.
Print Assumptions GRADIENT_GRAPH_UNIQUE.
Print Assumptions SOBOLEV_GRAPH_CAUCHY_IFF_COMPONENTS.
Print Assumptions SOBOLEV_COMPONENT_CAUCHY_COMPLETES.
Print Assumptions SOBOLEV_GRAPH_COMPLETE.
Print Assumptions SOBOLEV_GRAPH_ENERGY_CONTINUOUS.
