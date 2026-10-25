From Stdlib Require Import Reals Lra Psatz Lia Logic.Classical_Prop Logic.Classical_Pred_Type.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Hilbert LHGP_Realization.
Require Import LHGP_Dual LHGP_Gradient LHGP_WeakTopology LHGP_DissipationTopology.
Require Import LHGP_TimeBorel.

Open Scope R_scope.

(* The canonical finite-gradient domain is determined by all variational
   tests. Its measurability is proved from weak time continuity. No arbitrary
   predicate of good times, countable test reduction, or everywhere-finite
   dissipation is used. Openness of strict superlevels is obtained from one
   violating test, whose scalar readout is continuous in time. *)

Definition DissipationCostAlong h (gm : GradientModel h)
    (u : R -> HCarrier h) (z : HCarrier (DTest (GDual h gm))) (t : R) : R :=
  2 * GradientProbe h gm (u t) z - HNorm (DTest (GDual h gm)) z.

Definition CanonicalFiniteGradientDomain h (gm : GradientModel h)
    (u : R -> HCarrier h) (t : R) : Prop :=
  exists M : R, DissipationSublevel h gm (u t) M.

Definition CanonicalGPFiniteGradientDomain h (b : OrthonormalBasis h)
    (gm : GradientModel h) (g : Seq) (p : R -> Seq) (t : R) : Prop :=
  exists M : R, GPDissipationUpper h b gm g (p t) M.

Lemma DISSIPATION_TEST_COST_CONTINUOUS : forall h (gm : GradientModel h) u T,
  HWeakContinuous h u T -> forall z,
    ScalarContinuousOn T (DissipationCostAlong h gm u z).
Proof.
  intros h gm u T Hweak z.
  eapply ScalarContinuousOn_ext with
    (f := fun t => (-2) * HInner h (u t) (GDiv h gm z) +
                   (- HNorm (DTest (GDual h gm)) z)).
  - intros t Ht; unfold DissipationCostAlong, GradientProbe; ring.
  - apply ScalarContinuousOn_add.
    + apply ScalarContinuousOn_scale; apply Hweak.
    + apply ScalarContinuousOn_constant.
Qed.

Theorem DISSIPATION_STRICT_SUPERLEVEL_TIME_OPEN :
  forall h (gm : GradientModel h) u T M,
  HWeakContinuous h u T ->
  TimeOpen T (fun t => ~ DissipationSublevel h gm (u t) M).
Proof.
  intros h gm u T M Hweak t Ht Hnot.
  unfold DissipationSublevel, VarUpper in Hnot.
  apply not_all_ex_not in Hnot; destruct Hnot as [z Hz].
  assert (Hgap : 0 < DissipationCostAlong h gm u z t - M).
  { unfold DissipationCostAlong; lra. }
  destruct (DISSIPATION_TEST_COST_CONTINUOUS h gm u T Hweak z
    t Ht _ Hgap) as [delta [Hdelta Hnear]].
  exists delta; split; [exact Hdelta|].
  intros s Hs Hst Hbound.
  specialize (Hnear s Hs Hst).
  apply Rabs_def2 in Hnear; destruct Hnear as [Hupper Hlower].
  specialize (Hbound z); unfold DissipationCostAlong in *; lra.
Qed.

Theorem DISSIPATION_SUBLEVEL_TIME_CLOSED :
  forall h (gm : GradientModel h) u T M,
  HWeakContinuous h u T ->
  TimeClosed T (fun t => DissipationSublevel h gm (u t) M).
Proof.
  intros h gm u T M Hweak; apply DISSIPATION_STRICT_SUPERLEVEL_TIME_OPEN; exact Hweak.
Qed.

Theorem DISSIPATION_SUBLEVEL_TIME_BOREL :
  forall h (gm : GradientModel h) u T M,
  HWeakContinuous h u T ->
  TimeBorel T (fun t => DissipationSublevel h gm (u t) M).
Proof.
  intros h gm u T M Hweak; apply TB_closed.
  apply DISSIPATION_SUBLEVEL_TIME_CLOSED; exact Hweak.
Qed.

(* This is lower semicontinuity of the extended variational dissipation,
   stated through strict superlevels, including states with no finite bound. *)
Definition DissipationLowerSemicontinuous h (gm : GradientModel h)
    (u : R -> HCarrier h) (T : R) : Prop :=
  forall M, TimeOpen T (fun t => ~ DissipationSublevel h gm (u t) M).

Theorem WEAK_TIME_CONTINUITY_DERIVES_DISSIPATION_LSC :
  forall h (gm : GradientModel h) u T,
  HWeakContinuous h u T -> DissipationLowerSemicontinuous h gm u T.
Proof.
  intros h gm u T Hweak M; apply DISSIPATION_STRICT_SUPERLEVEL_TIME_OPEN; exact Hweak.
Qed.

Theorem CANONICAL_FINITE_GRADIENT_DOMAIN_COUNTABLE :
  forall h (gm : GradientModel h) u t,
  (CanonicalFiniteGradientDomain h gm u t <->
    exists n : nat, DissipationSublevel h gm (u t) (INR n)).
Proof.
  intros h gm u t; split.
  - intros [M HM]; destruct (INR_unbounded M) as [n Hn].
    exists n; eapply DissipationSublevel_monotone; [exact HM|lra].
  - intros [n Hn]; exists (INR n); exact Hn.
Qed.

Theorem CANONICAL_FINITE_GRADIENT_DOMAIN_BOREL :
  forall h (gm : GradientModel h) u T,
  HWeakContinuous h u T ->
  TimeBorel T (CanonicalFiniteGradientDomain h gm u).
Proof.
  intros h gm u T Hweak.
  eapply TB_ext with
    (A := fun t => exists n : nat, DissipationSublevel h gm (u t) (INR n)).
  - apply TB_union; intro n; apply DISSIPATION_SUBLEVEL_TIME_BOREL; exact Hweak.
  - intros t Ht; symmetry; apply CANONICAL_FINITE_GRADIENT_DOMAIN_COUNTABLE.
Qed.

Theorem CANONICAL_INFINITE_DISSIPATION_DOMAIN_BOREL :
  forall h (gm : GradientModel h) u T,
  HWeakContinuous h u T ->
  TimeBorel T (fun t => InfiniteDissipation h gm (u t)).
Proof.
  intros h gm u T Hweak.
  eapply TB_ext with (A := fun t => ~ CanonicalFiniteGradientDomain h gm u t).
  - apply TB_complement; apply CANONICAL_FINITE_GRADIENT_DOMAIN_BOREL; exact Hweak.
  - intros t Ht; unfold CanonicalFiniteGradientDomain, InfiniteDissipation; firstorder.
Qed.

Theorem CANONICAL_FINITE_GRADIENT_DOMAIN_IFF_GRADIENT :
  forall h (gm : GradientModel h) u t,
  (CanonicalFiniteGradientDomain h gm u t <->
    exists G, ProbeRepresents (GDual h gm) (GradientProbe h gm (u t)) G).
Proof.
  intros h gm u t; split.
  - intros [M HM].
    destruct (proj1 (DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND h gm (u t) M) HM)
      as [G [HG Hnorm]].
    exists G; exact HG.
  - intros [G HG]; exists (HNorm (DTarget (GDual h gm)) G).
    apply (proj2 (DISSIPATION_SUBLEVEL_IFF_GRADIENT_BOUND h gm (u t) _)).
    exists G; split; [exact HG|lra].
Qed.

Theorem CANONICAL_FINITE_GRADIENT_DOMAIN_IFF_ENERGY_VALUE :
  forall h (gm : GradientModel h) u t,
  (CanonicalFiniteGradientDomain h gm u t <->
    exists D, GradientEnergyAt h gm (u t) D).
Proof.
  intros h gm u t; rewrite CANONICAL_FINITE_GRADIENT_DOMAIN_IFF_GRADIENT; split.
  - intros [G HG]; exists (HNorm (DTarget (GDual h gm)) G).
    exists G; split; [exact HG|reflexivity].
  - intros [D [G [HG Hnorm]]]; exists G; exact HG.
Qed.

Theorem FINITE_GRADIENT_TIMES_INCLUDED_IN_CANONICAL :
  forall h (gm : GradientModel h) u (Good : R -> Prop) D,
  (forall t, Good t -> GradientEnergyAt h gm (u t) (D t)) ->
  forall t, Good t -> CanonicalFiniteGradientDomain h gm u t.
Proof.
  intros h gm u Good D Hgood t Ht.
  apply (proj2 (CANONICAL_FINITE_GRADIENT_DOMAIN_IFF_ENERGY_VALUE h gm u t)).
  exists (D t); apply Hgood; exact Ht.
Qed.

Theorem CANONICAL_GP_FINITE_GRADIENT_DOMAIN_EXACT :
  forall h (b : OrthonormalBasis h), HComplete h ->
  forall (gm : GradientModel h) g u p t,
  GPNonzero g -> seq_eq (HGPEncode b g (u t)) (p t) ->
  (CanonicalGPFiniteGradientDomain h b gm g p t <->
   CanonicalFiniteGradientDomain h gm u t).
Proof.
  intros h b Hcomplete gm g u p t Hg Hencode; split; intros [M HM]; exists M.
  - apply (proj1 (GRADIENT_DISSIPATION_UPPER_EXACT h b Hcomplete gm g (u t) (p t)
      M Hg Hencode)); exact HM.
  - apply (proj2 (GRADIENT_DISSIPATION_UPPER_EXACT h b Hcomplete gm g (u t) (p t)
      M Hg Hencode)); exact HM.
Qed.

Theorem CANONICAL_GP_FINITE_GRADIENT_DOMAIN_BOREL :
  forall h (b : OrthonormalBasis h), HComplete h ->
  forall (gm : GradientModel h) g u p T,
  GPNonzero g -> HWeakContinuous h u T ->
  (forall t, InInterval T t -> seq_eq (HGPEncode b g (u t)) (p t)) ->
  TimeBorel T (CanonicalGPFiniteGradientDomain h b gm g p).
Proof.
  intros h b Hcomplete gm g u p T Hg Hweak Hencode.
  eapply TB_ext with (A := CanonicalFiniteGradientDomain h gm u).
  - apply CANONICAL_FINITE_GRADIENT_DOMAIN_BOREL; exact Hweak.
  - intros t Ht; symmetry; apply CANONICAL_GP_FINITE_GRADIENT_DOMAIN_EXACT;
      [exact Hcomplete|exact Hg|apply Hencode; exact Ht].
Qed.

Print Assumptions DISSIPATION_SUBLEVEL_TIME_CLOSED.
Print Assumptions CANONICAL_FINITE_GRADIENT_DOMAIN_BOREL.
Print Assumptions CANONICAL_GP_FINITE_GRADIENT_DOMAIN_BOREL.
