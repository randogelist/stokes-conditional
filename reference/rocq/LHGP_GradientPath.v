From Stdlib Require Import Reals Lra Psatz Logic.ClassicalUniqueChoice.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.
Require Import LHGP_Dual LHGP_Gradient.

Open Scope R_scope.

(* A pointwise gradient on the active time set is extended by zero outside
   that set. The off-set scalar dissipation must likewise be zero. This is
   a representative of the gradient trajectory; it does not assert that
   an actual distributional gradient exists at an excluded time.

   Unique choice reifies the unique pointwise graph. Masked scalar
   coordinates are specified by implications rather than an informative
   excluded-middle function. No measurability or time integral is assumed
   or concluded in this module; subsequent time-topology results can use
   the explicit coordinate mask and the finite synthesis convergence. *)

Definition TotalGradientAt h (gm : GradientModel h)
  (u : R -> HCarrier h) (Active : R -> Prop) (D : R -> R)
  (t : R) (G : HCarrier (DTarget (GDual h gm))) : Prop :=
  (Active t ->
    ProbeRepresents (GDual h gm) (GradientProbe h gm (u t)) G /\
    HNorm (DTarget (GDual h gm)) G = D t) /\
  (~ Active t -> G = HZero (DTarget (GDual h gm))).

Definition TotalGradientPath h (gm : GradientModel h)
  (u : R -> HCarrier h) (Active : R -> Prop) (D : R -> R)
  (G : R -> HCarrier (DTarget (GDual h gm))) : Prop :=
  forall t, TotalGradientAt h gm u Active D t (G t).

Definition GradientCoordinateMask h (gm : GradientModel h)
  (u : R -> HCarrier h) (Active : R -> Prop) (c : R -> Seq) : Prop :=
  forall t i,
    (Active t -> c t i = GradientProbe h gm (u t) (DTestBasis (GDual h gm) i)) /\
    (~ Active t -> c t i = 0).

(* The canonical constructor does not start from a prescribed scalar
   dissipation. Its active set can therefore be the finite-probe domain,
   independently of any later ledger or its exceptional-time values. *)
Definition TotalGradientGraphAt h (gm : GradientModel h)
  (u : R -> HCarrier h) (Active : R -> Prop)
  (t : R) (G : HCarrier (DTarget (GDual h gm))) : Prop :=
  (Active t -> ProbeRepresents (GDual h gm) (GradientProbe h gm (u t)) G) /\
  (~ Active t -> G = HZero (DTarget (GDual h gm))).

Definition TotalGradientGraphPath h (gm : GradientModel h)
  (u : R -> HCarrier h) (Active : R -> Prop)
  (G : R -> HCarrier (DTarget (GDual h gm))) : Prop :=
  forall t, TotalGradientGraphAt h gm u Active t (G t).

Theorem GRADIENT_GRAPH_AT_UNIQUE : forall h (gm : GradientModel h)
  u Active t G K,
  TotalGradientGraphAt h gm u Active t G ->
  TotalGradientGraphAt h gm u Active t K -> K = G.
Proof.
  intros h gm u Active t G K [HGactive HGzero] [HKactive HKzero].
  destruct (classic (Active t)) as [Ha | Ha].
  - apply (ProbeRepresents_unique (GDual h gm) (GradientProbe h gm (u t)));
      [apply HKactive | apply HGactive]; exact Ha.
  - rewrite (HGzero Ha), (HKzero Ha); reflexivity.
Qed.

Theorem GRADIENT_GRAPH_AS_TOTAL_PATH : forall h (gm : GradientModel h)
  u Active G,
  TotalGradientGraphPath h gm u Active G ->
  TotalGradientPath h gm u Active
    (fun t => HNorm (DTarget (GDual h gm)) (G t)) G.
Proof.
  intros h gm u Active G HG t; split.
  - intro Ha; split; [exact (proj1 (HG t) Ha) | reflexivity].
  - exact (proj2 (HG t)).
Qed.

Theorem GRADIENT_GRAPH_NORM_ZERO_OUTSIDE : forall h (gm : GradientModel h)
  u Active G,
  TotalGradientGraphPath h gm u Active G -> forall t,
  ~ Active t -> HNorm (DTarget (GDual h gm)) (G t) = 0.
Proof.
  intros h gm u Active G HG t Ha; rewrite (proj2 (HG t) Ha); apply HNorm_zero.
Qed.

Theorem GRADIENT_PATH_FROM_POINTWISE_PROBES : forall h (gm : GradientModel h)
  (u : R -> HCarrier h) Active,
  (forall t, Active t -> exists G,
    ProbeRepresents (GDual h gm) (GradientProbe h gm (u t)) G) ->
  exists G : R -> HCarrier (DTarget (GDual h gm)),
    TotalGradientGraphPath h gm u Active G /\
    TotalGradientPath h gm u Active
      (fun t => HNorm (DTarget (GDual h gm)) (G t)) G /\
    (forall t, ~ Active t -> HNorm (DTarget (GDual h gm)) (G t) = 0) /\
    (forall K, TotalGradientGraphPath h gm u Active K -> forall t, K t = G t).
Proof.
  intros h gm u Active Hactive.
  assert (Hpoint : forall t, exists! G,
    TotalGradientGraphAt h gm u Active t G).
  { intro t; destruct (classic (Active t)) as [Ha | Ha].
    - destruct (Hactive t Ha) as [G HG].
      assert (Htotal : TotalGradientGraphAt h gm u Active t G).
      { split; [intro H; exact HG | intro Hnot; contradiction]. }
      exists G; split; [exact Htotal |].
      intros K HK; symmetry; exact (GRADIENT_GRAPH_AT_UNIQUE h gm u Active t G K Htotal HK).
    - assert (Htotal : TotalGradientGraphAt h gm u Active t
        (HZero (DTarget (GDual h gm)))).
      { split; [intro Hyes; contradiction | intro H; reflexivity]. }
      exists (HZero (DTarget (GDual h gm))); split; [exact Htotal |].
      intros K HK; symmetry.
      exact (GRADIENT_GRAPH_AT_UNIQUE h gm u Active t
        (HZero (DTarget (GDual h gm))) K Htotal HK). }
  destruct (unique_choice R (HCarrier (DTarget (GDual h gm)))
    (fun t G => TotalGradientGraphAt h gm u Active t G) Hpoint) as [G HG].
  exists G; split; [exact HG |]; split.
  - exact (GRADIENT_GRAPH_AS_TOTAL_PATH h gm u Active G HG).
  - split.
    + exact (GRADIENT_GRAPH_NORM_ZERO_OUTSIDE h gm u Active G HG).
    + intros K HK t; exact (GRADIENT_GRAPH_AT_UNIQUE h gm u Active t
        (G t) (K t) (HG t) (HK t)).
Qed.

Theorem GRADIENT_AT_UNIQUE : forall h (gm : GradientModel h)
  u Active D t G K,
  TotalGradientAt h gm u Active D t G ->
  TotalGradientAt h gm u Active D t K -> K = G.
Proof.
  intros h gm u Active D t G K [HGactive HGzero] [HKactive HKzero].
  destruct (classic (Active t)) as [Ha | Ha].
  - destruct (HGactive Ha) as [HG _]; destruct (HKactive Ha) as [HK _].
    apply (ProbeRepresents_unique (GDual h gm) (GradientProbe h gm (u t)));
      assumption.
  - rewrite (HGzero Ha), (HKzero Ha); reflexivity.
Qed.

Theorem GRADIENT_PATH_NORM : forall h (gm : GradientModel h)
  u Active D G,
  TotalGradientPath h gm u Active D G ->
  (forall t, ~ Active t -> D t = 0) ->
  forall t, HNorm (DTarget (GDual h gm)) (G t) = D t.
Proof.
  intros h gm u Active D G HG HD t.
  destruct (classic (Active t)) as [Ha | Ha].
  - exact (proj2 (proj1 (HG t) Ha)).
  - rewrite (proj2 (HG t) Ha), HNorm_zero, (HD t Ha); reflexivity.
Qed.

Theorem GRADIENT_PATH_EXISTS_UNIQUE : forall h (gm : GradientModel h)
  (u : R -> HCarrier h) Active D,
  (forall t, Active t -> GradientEnergyAt h gm (u t) (D t)) ->
  (forall t, ~ Active t -> D t = 0) ->
  exists G : R -> HCarrier (DTarget (GDual h gm)),
    TotalGradientPath h gm u Active D G /\
    (forall t, HNorm (DTarget (GDual h gm)) (G t) = D t) /\
    (forall K, TotalGradientPath h gm u Active D K -> forall t, K t = G t).
Proof.
  intros h gm u Active D Hactive Houtside.
  assert (Hpoint : forall t, exists! G,
    TotalGradientAt h gm u Active D t G).
  { intro t; destruct (classic (Active t)) as [Ha | Ha].
    - destruct (Hactive t Ha) as [G [HG Hnorm]].
      assert (Htotal : TotalGradientAt h gm u Active D t G).
      { split.
        - intro H; split; assumption.
        - intro Hnot; contradiction. }
      exists G; split; [exact Htotal |].
      intros K HK; symmetry; exact (GRADIENT_AT_UNIQUE h gm u Active D t G K Htotal HK).
    - assert (Htotal : TotalGradientAt h gm u Active D t
        (HZero (DTarget (GDual h gm)))).
      { split; [intro Hyes; contradiction | intro H; reflexivity]. }
      exists (HZero (DTarget (GDual h gm))); split; [exact Htotal |].
      intros K HK; symmetry.
      exact (GRADIENT_AT_UNIQUE h gm u Active D t
        (HZero (DTarget (GDual h gm))) K Htotal HK). }
  destruct (unique_choice R (HCarrier (DTarget (GDual h gm)))
    (fun t G => TotalGradientAt h gm u Active D t G) Hpoint) as [G HG].
  exists G; split; [exact HG |]; split.
  - exact (GRADIENT_PATH_NORM h gm u Active D G HG Houtside).
  - intros K HK t; exact (GRADIENT_AT_UNIQUE h gm u Active D t (G t) (K t)
      (HG t) (HK t)).
Qed.

Theorem GRADIENT_PATH_ACTIVE : forall h (gm : GradientModel h)
  u Active D G,
  TotalGradientPath h gm u Active D G -> forall t,
  Active t -> ProbeRepresents (GDual h gm) (GradientProbe h gm (u t)) (G t).
Proof. intros h gm u Active D G HG t Ha; exact (proj1 (proj1 (HG t) Ha)). Qed.

Theorem GRADIENT_PATH_ZERO_OUTSIDE : forall h (gm : GradientModel h)
  u Active D G,
  TotalGradientPath h gm u Active D G -> forall t,
  ~ Active t -> G t = HZero (DTarget (GDual h gm)).
Proof. intros h gm u Active D G HG t Ha; exact (proj2 (HG t) Ha). Qed.

Theorem GRADIENT_PATH_COORDINATE_MASK : forall h (gm : GradientModel h)
  u Active D G,
  TotalGradientPath h gm u Active D G ->
  GradientCoordinateMask h gm u Active
    (fun t => HAnalysis (DBasis (GDual h gm)) (G t)).
Proof.
  intros h gm u Active D G HG t i; split.
  - intro Ha.
    pose proof (GRADIENT_PATH_ACTIVE h gm u Active D G HG t Ha
      (DTestBasis (GDual h gm) i)) as Hprobe.
    rewrite DTestBasis_image in Hprobe; unfold HAnalysis; symmetry; exact Hprobe.
  - intro Ha; rewrite (GRADIENT_PATH_ZERO_OUTSIDE h gm u Active D G HG t Ha).
    unfold HAnalysis; apply HInner_zero_l.
Qed.

Theorem GRADIENT_MASK_EQUALS_ANALYSIS : forall h (gm : GradientModel h)
  u Active D G c,
  TotalGradientPath h gm u Active D G ->
  GradientCoordinateMask h gm u Active c -> forall t,
  seq_eq (c t) (HAnalysis (DBasis (GDual h gm)) (G t)).
Proof.
  intros h gm u Active D G c HG Hc t i.
  pose proof (GRADIENT_PATH_COORDINATE_MASK h gm u Active D G HG t i) as Hanalysis.
  destruct (classic (Active t)) as [Ha | Ha].
  - rewrite (proj1 (Hc t i) Ha), (proj1 Hanalysis Ha); reflexivity.
  - rewrite (proj2 (Hc t i) Ha), (proj2 Hanalysis Ha); reflexivity.
Qed.

Lemma Gradient_HFinite_ext : forall h (b : OrthonormalBasis h) a c,
  seq_eq a c -> forall n, HFinite b a n = HFinite b c n.
Proof.
  intros h b a c Heq n; induction n as [|n IH]; simpl; [reflexivity |].
  rewrite IH, (Heq n); reflexivity.
Qed.

Theorem GRADIENT_MASK_FINITE_SYNTHESIS : forall h (gm : GradientModel h)
  u Active D G c,
  TotalGradientPath h gm u Active D G ->
  GradientCoordinateMask h gm u Active c -> forall t,
  HConverges (DTarget (GDual h gm))
    (HFinite (DBasis (GDual h gm)) (c t)) (G t).
Proof.
  intros h gm u Active D G c HG Hc t eps Heps.
  destruct (HAnalysis_reconstruction (DTarget (GDual h gm))
    (DBasis (GDual h gm)) (DComplete (GDual h gm)) (G t) eps Heps)
    as [N HN].
  exists N; intros n Hn.
  rewrite (Gradient_HFinite_ext (DTarget (GDual h gm)) (DBasis (GDual h gm))
    (c t) (HAnalysis (DBasis (GDual h gm)) (G t))
    (GRADIENT_MASK_EQUALS_ANALYSIS h gm u Active D G c HG Hc t) n).
  exact (HN n Hn).
Qed.

Theorem GRADIENT_MASK_ENERGY_EXACT : forall h (gm : GradientModel h)
  u Active D G c,
  TotalGradientPath h gm u Active D G ->
  (forall t, ~ Active t -> D t = 0) ->
  GradientCoordinateMask h gm u Active c -> forall t,
  EnergyValue (c t) (D t).
Proof.
  intros h gm u Active D G c HG HD Hc t.
  rewrite <- (GRADIENT_PATH_NORM h gm u Active D G HG HD t).
  apply (proj2 (EnergyValue_ext _ _ (HNorm (DTarget (GDual h gm)) (G t))
    (GRADIENT_MASK_EQUALS_ANALYSIS h gm u Active D G c HG Hc t))).
  apply HAnalysis_parseval; apply DComplete.
Qed.

Theorem GRADIENT_MASK_PREFIX_BOUND : forall h (gm : GradientModel h)
  u Active D G c,
  TotalGradientPath h gm u Active D G ->
  (forall t, ~ Active t -> D t = 0) ->
  GradientCoordinateMask h gm u Active c -> forall t n,
  0 <= energy_prefix (c t) n /\ energy_prefix (c t) n <= D t.
Proof.
  intros h gm u Active D G c HG HD Hc t n; split.
  - apply energy_prefix_nonnegative.
  - exact (proj1 (GRADIENT_MASK_ENERGY_EXACT h gm u Active D G c HG HD Hc t) n).
Qed.

Theorem GRADIENT_MASK_RESIDUAL_EXACT : forall h (gm : GradientModel h)
  u Active D G c,
  TotalGradientPath h gm u Active D G ->
  (forall t, ~ Active t -> D t = 0) ->
  GradientCoordinateMask h gm u Active c -> forall t n,
  HDist (DTarget (GDual h gm))
    (HFinite (DBasis (GDual h gm)) (c t) n) (G t) = D t - energy_prefix (c t) n.
Proof.
  intros h gm u Active D G c HG HD Hc t n.
  pose proof (GRADIENT_MASK_EQUALS_ANALYSIS h gm u Active D G c HG Hc t) as Heq.
  rewrite HDist_sym.
  rewrite (Gradient_HFinite_ext (DTarget (GDual h gm)) (DBasis (GDual h gm))
    (c t) (HAnalysis (DBasis (GDual h gm)) (G t)) Heq n).
  rewrite HAnalysis_residual, (GRADIENT_PATH_NORM h gm u Active D G HG HD t).
  rewrite (energy_prefix_ext _ _ n Heq); reflexivity.
Qed.

Print Assumptions GRADIENT_PATH_EXISTS_UNIQUE.
Print Assumptions GRADIENT_PATH_FROM_POINTWISE_PROBES.
Print Assumptions GRADIENT_PATH_COORDINATE_MASK.
Print Assumptions GRADIENT_MASK_FINITE_SYNTHESIS.
Print Assumptions GRADIENT_MASK_ENERGY_EXACT.
Print Assumptions GRADIENT_MASK_RESIDUAL_EXACT.
