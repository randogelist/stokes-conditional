From Stdlib Require Import Reals Lra.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Realization LHGP_Dual LHGP_Gradient.
Require Import LHGP_WeakTopology LHGP_PathSynthesis LHGP_Evolution LHGP_Equivalence.
Require Import LHGP_HilbertSchur LHGP_NativeKQ LHGP_NativeDiagonal.
Require Import LHGP_DissipationTopology LHGP_SobolevGraph.

Open Scope R_scope.

(* The native real diagonal map below is an imported constant from the
   supplied project. This joins its proved energy completion to v030.
   No concrete R3 realization, physical detector/source assignment, or
   bilateral complex Kq product is asserted by these terminals. *)

Definition NativeGPPathRealizes h (b : OrthonormalBasis h) (g : Seq)
    (u : R -> HCarrier h) (p : CoefficientPath) : Prop :=
  forall t, seq_eq (NativeGP.gp_pull g (HAnalysis b (u t))) (p t).

Theorem LHGP_NATIVE_LH_TRAJECTORY_EQUIVALENCE :
  forall h (b : OrthonormalBasis h), HComplete h ->
  forall gm tests td nu T g, GPNonzero g -> forall p u0,
  GPLHModel h b gm tests td nu T g p (NativeGP.gp_pull g (HAnalysis b u0)) <->
  exists u : R -> HCarrier h,
    HilbertLHModel h gm tests td nu T u u0 /\
    NativeGPPathRealizes h b g u p /\
    (forall t, NativeDiagonalEnergy g (p t) (HNorm h (u t))) /\
    (forall v, NativeGPPathRealizes h b g v p -> forall t, v t = u t).
Proof.
  intros h b Hcomplete gm tests td nu T g Hg p u0; split.
  - intro HP.
    destruct (proj1 (LHGP_TRAJECTORY_EQUIVALENCE h b Hcomplete gm tests td
      nu T g Hg p u0) HP) as [u [HL [Hu HU]]].
    exists u; split; [exact HL|]; split; [exact Hu|]; split; [|exact HU].
    intro t; apply NATIVE_DIAGONAL_ENERGY_VALUE_EXACT.
    exact (HGP_PATH_ENERGY_EXACT h b Hcomplete g u p Hg Hu t).
  - intros [u [HL [Hu [HE HU]]]].
    apply (proj2 (LHGP_TRAJECTORY_EQUIVALENCE h b Hcomplete gm tests td
      nu T g Hg p u0)); exists u; split; [exact HL|]; split; assumption.
Qed.

Theorem LHGP_NATIVE_GP_WEAK_LIMIT_HAS_GRADIENT :
  forall h (b : OrthonormalBasis h), HComplete h -> forall gm g xn x pn M,
  GPNonzero g ->
  (forall n, seq_eq (NativeGP.gp_pull g (HAnalysis b (xn n))) (pn n)) ->
  HWeakSequential h xn x ->
  (forall n, GPDissipationUpper h b gm g (pn n) M) ->
  exists G,
    GradientGraph h gm x G /\
    HNorm (DTarget (GDual h gm)) G <= M /\
    GPDissipationValue h b gm g (NativeGP.gp_pull g (HAnalysis b x))
      (HNorm (DTarget (GDual h gm)) G).
Proof.
  intros h b Hcomplete gm g xn x pn M Hg Hpn Hweak Hbound.
  assert (HX : DissipationSublevel h gm x M).
  { apply (DISSIPATION_SUBLEVEL_WEAK_CLOSED h gm xn x M Hweak).
    intro n; apply (proj1 (GP_DISSIPATION_SUBLEVEL_EXACT h b Hcomplete gm
      g (pn n) (xn n) M Hg (Hpn n))); apply Hbound. }
  destruct (proj1 (DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND h gm x M) HX)
    as [G [HG HM]].
  exists G; split; [exact HG|]; split; [exact HM|].
  apply (proj2 (GRADIENT_DISSIPATION_EXACT h b Hcomplete gm g x
    (NativeGP.gp_pull g (HAnalysis b x)) (HNorm (DTarget (GDual h gm)) G)
    Hg (seq_eq_refl _))).
  exists G; split; [exact HG|reflexivity].
Qed.

(* This assigns the first Gram role to the reconstructed state only.
   f,n0,n1 and their orthogonality are explicit; no physical M7 roles or
   uniform production/payment bounds are inferred from representation. *)
Theorem LHGP_NATIVE_LH_GRAM_REALIZATION :
  forall h (b : OrthonormalBasis h), HComplete h ->
  forall gm tests td nu T g, GPNonzero g -> forall p u0,
  GPLHModel h b gm tests td nu T g p (NativeGP.gp_pull g (HAnalysis b u0)) ->
  exists u : R -> HCarrier h,
    HilbertLHModel h gm tests td nu T u u0 /\
    NativeGPPathRealizes h b g u p /\
    forall t f n0 n1,
      NativeGram.PSD4 (HilbertGram4 h (u t) f n0 n1) /\
      (forall i j, SeqLimit (fun n => NativeDecodedGram4 n g (p t)
        (NativeGP.gp_pull g (HAnalysis b f))
        (NativeGP.gp_pull g (HAnalysis b n0))
        (NativeGP.gp_pull g (HAnalysis b n1)) i j)
        (HilbertGram4 h (u t) f n0 n1 i j)) /\
      (HInner h (u t) n0 = 0 -> HInner h (u t) n1 = 0 ->
       HInner h (u t) f * HInner h (u t) f <=
         HNorm h (u t) * HReducedCapacity h f n0 n1).
Proof.
  intros h b Hcomplete gm tests td nu T g Hg p u0 HP.
  destruct (proj1 (LHGP_NATIVE_LH_TRAJECTORY_EQUIVALENCE h b Hcomplete gm tests td
    nu T g Hg p u0) HP) as [u [HL [Hu [HE HU]]]].
  exists u; split; [exact HL|]; split; [exact Hu|].
  intros t f n0 n1.
  destruct (LHGP_NATIVE_GP_GRAM_COMPLETION_STATE h b g Hcomplete Hg
    (u t) (p t) f n0 n1 (Hu t)) as [HPSD Hlimit].
  split; [exact HPSD|]; split; [exact Hlimit|].
  apply HSG20_SCHUR_ACTION_BOUND.
Qed.

Theorem LHGP_NATIVE_GRAPH_COMPLETION : forall h (b : OrthonormalBasis h),
  HComplete h -> forall gm g xn Gn,
  GPNonzero g -> GraphCauchy h gm xn Gn ->
  (forall n, GradientGraph h gm (xn n) (Gn n)) ->
  exists x G,
    GradientGraph h gm x G /\ GraphConverges h gm xn Gn x G /\
    NativeDiagonalL2 g (NativeGP.gp_pull g (HAnalysis b x)) /\
    GPDissipationValue h b gm g (NativeGP.gp_pull g (HAnalysis b x))
      (HNorm (DTarget (GDual h gm)) G) /\
    SeqLimit (fun n => GraphEnergy h gm (xn n) (Gn n)) (GraphEnergy h gm x G).
Proof.
  intros h b Hcomplete gm g xn Gn Hg HC Hgraph.
  destruct (SOBOLEV_GRAPH_COMPLETE h gm Hcomplete xn Gn HC Hgraph)
    as [x [G [HG HL]]].
  exists x, G; split; [exact HG|]; split; [exact HL|]; split.
  - apply NATIVE_DIAGONAL_ENERGY_CLASS_EXACT; apply HGP_L2; exact Hg.
  - split.
    + apply (proj2 (GRADIENT_DISSIPATION_EXACT h b Hcomplete gm g x
        (NativeGP.gp_pull g (HAnalysis b x)) (HNorm (DTarget (GDual h gm)) G)
        Hg (seq_eq_refl _))).
      exists G; split; [exact HG|reflexivity].
    + apply SOBOLEV_GRAPH_ENERGY_CONTINUOUS; exact HL.
Qed.

Print Assumptions LHGP_NATIVE_LH_TRAJECTORY_EQUIVALENCE.
Print Assumptions LHGP_NATIVE_GP_WEAK_LIMIT_HAS_GRADIENT.
Print Assumptions LHGP_NATIVE_LH_GRAM_REALIZATION.
Print Assumptions LHGP_NATIVE_GRAPH_COMPLETION.
