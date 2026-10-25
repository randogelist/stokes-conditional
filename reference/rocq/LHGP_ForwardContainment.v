From Stdlib Require Import Reals Lra Psatz.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Realization LHGP_WeakTopology LHGP_PathSynthesis.
Require Import LHGP_Evolution LHGP_Equivalence LHGP_InitialEnergy.
Require Import LHGP_Dual LHGP_Gradient LHGP_ForwardGradient.

Open Scope R_scope.

(* Forward-only containment of independently stated abstract classes.
   Source gradients are supplied on a full-measure time set. The theorem
   does not construct gradients, synthesize arbitrary coefficient paths,
   or assert a restarted energy inequality. Tensor completeness, a tensor
   ONB, and a Riesz converse are absent from its hypotheses.

   Concrete L2_sigma(R^3), physical test integrals and Lebesgue TimeData
   still require their own realizations. A source value of the abstract
   predicate below is not itself a construction of those physical spaces. *)
Definition HilbertForwardEnergyLedger (h k : HilbertData)
    (fg : ForwardGradientData h k) (td : TimeData) (nu T : R)
    (u : R -> HCarrier h) : Prop :=
  exists (E D : R -> R) (GoodD : R -> Prop),
    EnergySchedule0 td nu T E D GoodD /\
    (forall t, E t = HNorm h (u t)) /\
    (forall t, 0 <= t <= T -> GoodD t ->
      ForwardGradientEnergyAt h k fg (u t) (D t)).

Definition GPForwardEnergyLedger (h k : HilbertData) (b : OrthonormalBasis h)
    (fg : ForwardGradientData h k) (td : TimeData) (nu T : R)
    (g : Seq) (p : CoefficientPath) : Prop :=
  exists (E D : R -> R) (GoodD : R -> Prop),
    EnergySchedule0 td nu T E D GoodD /\
    EnergyTrace (decode_path g p) E /\
    (forall t, 0 <= t <= T -> GoodD t ->
      ForwardGPDissipationValue h k b fg g (p t) (D t)).

Definition HilbertForwardLHModel (h k : HilbertData)
    (fg : ForwardGradientData h k) (tests : EvolutionTests h)
    (td : TimeData) (nu T : R) (u : R -> HCarrier h) (u0 : HCarrier h) : Prop :=
  0 < nu /\ 0 < T /\
  u 0 = u0 /\
  HWeakContinuous h u T /\
  (exists M, forall t, 0 <= t <= T -> HNorm h (u t) <= M) /\
  HilbertWeakForm h tests td nu T u u0 /\
  HilbertForwardEnergyLedger h k fg td nu T u.

Definition GPForwardLHModel (h k : HilbertData) (b : OrthonormalBasis h)
    (fg : ForwardGradientData h k) (tests : EvolutionTests h)
    (td : TimeData) (nu T : R) (g : Seq)
    (p : CoefficientPath) (p0 : Seq) : Prop :=
  0 < nu /\ 0 < T /\
  (forall t, GPL2 g (p t)) /\
  seq_eq (p 0) p0 /\
  CoordinatesContinuous (decode_path g p) T /\
  (exists M, GPEnergyBound g p T M) /\
  GPWeakForm h b tests td nu T g p p0 /\
  GPForwardEnergyLedger h k b fg td nu T g p.

Theorem LHGP_FORWARD_ENERGY_LEDGER : forall h k (b : OrthonormalBasis h),
  HComplete h -> forall fg td nu T g u p,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  HilbertForwardEnergyLedger h k fg td nu T u ->
  GPForwardEnergyLedger h k b fg td nu T g p.
Proof.
  intros h k b Hcomplete fg td nu T g u p Hg Hreal
    [E [D [GoodD [HS [HE HD]]]]].
  exists E, D, GoodD; split; [exact HS |]; split.
  - intro t; rewrite HE.
    exact (HGP_PATH_ENERGY_EXACT h b Hcomplete g u p Hg Hreal t).
  - intros t Ht Hgood.
    exact (FORWARD_GRADIENT_ENERGY_TO_GP_VALUE h k b Hcomplete fg g
      (u t) (p t) (D t) Hg (Hreal t) (HD t Ht Hgood)).
Qed.

Theorem LHGP_FORWARD_REALIZED_CONTAINMENT : forall h k (b : OrthonormalBasis h),
  HComplete h -> forall fg tests td nu T g u p u0,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  HilbertForwardLHModel h k fg tests td nu T u u0 ->
  GPForwardLHModel h k b fg tests td nu T g p (HGPEncode b g u0).
Proof.
  intros h k b Hcomplete fg tests td nu T g u p u0 Hg Hreal
    [Hnu [HT [H0 [HC [[M HM] [HW HE]]]]]].
  split; [exact Hnu |]; split; [exact HT |]; split.
  - intro t; unfold GPL2.
    apply (proj2 (CoordinateL2_ext _ _
      (HGP_PATH_DECODE_REALIZATION h b g u p Hg Hreal t))).
    apply HAnalysis_L2.
  - split.
    + intro i; rewrite <- (Hreal 0 i), H0; reflexivity.
    + split.
      * apply (proj2 (CoordinatesContinuous_ext
          (decode_path g p) (fun t => HAnalysis b (u t)) T
          (fun t Ht => HGP_PATH_DECODE_REALIZATION h b g u p Hg Hreal t))).
        apply HWeakContinuous_to_coordinates; exact HC.
      * split.
        -- exists M.
           apply (proj2 (HGP_PATH_PREFIX_BOUND_IFF h b Hcomplete
             g u p T M Hg Hreal)); exact HM.
        -- split.
           ++ apply (proj1 (EVOLUTION_WEAK_FORM_EXACT h b Hcomplete tests td
                nu T g u p u0 (HGPEncode b g u0) Hg Hreal (seq_eq_refl _))).
              exact HW.
           ++ exact (LHGP_FORWARD_ENERGY_LEDGER h k b Hcomplete fg td nu T
                g u p Hg Hreal HE).
Qed.

Theorem LHGP_FORWARD_ENCODING_CONTAINMENT : forall h k (b : OrthonormalBasis h),
  HComplete h -> forall fg tests td nu T g u u0,
  GPNonzero g -> HilbertForwardLHModel h k fg tests td nu T u u0 ->
  GPForwardLHModel h k b fg tests td nu T g
    (fun t => HGPEncode b g (u t)) (HGPEncode b g u0).
Proof.
  intros h k b Hcomplete fg tests td nu T g u u0 Hg HL.
  apply (LHGP_FORWARD_REALIZED_CONTAINMENT h k b Hcomplete fg tests td
    nu T g u (fun t => HGPEncode b g (u t)) u0 Hg).
  - intros t i; reflexivity.
  - exact HL.
Qed.

(* Injectivity concerns a fixed complete coefficient trajectory; it is not
   uniqueness of evolution from an initial datum. No completeness is used. *)
Theorem LHGP_FORWARD_ENCODING_INJECTIVE : forall h (b : OrthonormalBasis h) g,
  GPNonzero g -> forall (u v : R -> HCarrier h),
  (forall t, seq_eq (HGPEncode b g (u t)) (HGPEncode b g (v t))) ->
  forall t, u t = v t.
Proof.
  intros h b g Hg u v Heq t.
  exact (HGP_injective h b g (u t) (v t) Hg (Heq t)).
Qed.

Theorem LHGP_FORWARD_INITIAL_NORM_BOUND : forall h k fg tests td nu T u u0,
  IntegralNonnegative td -> HilbertForwardLHModel h k fg tests td nu T u u0 ->
  forall t, 0 <= t <= T -> HNorm h (u t) <= HNorm h (u 0).
Proof.
  intros h k fg tests td nu T u u0 HI HL t Ht.
  destruct HL as [Hnu [HT [H0 [HC [HB [HW Hledger]]]]]].
  destruct Hledger as [E [D [GoodD [HS [HE HD]]]]].
  rewrite <- (HE t), <- (HE 0).
  apply (ENERGY_SCHEDULE0_ENERGY_BOUND td nu T E D GoodD); [lra | exact HI | exact HS | exact Ht].
Qed.

Theorem LHGP_FORWARD_HILBERT_STRONG_INITIAL : forall h k fg tests td nu T u u0,
  IntegralNonnegative td -> HilbertForwardLHModel h k fg tests td nu T u u0 ->
  EnergyInitialTrace (fun t => HDist h (u t) u0).
Proof.
  intros h k fg tests td nu T u u0 HI HL.
  pose proof (LHGP_FORWARD_INITIAL_NORM_BOUND h k fg tests td nu T u u0 HI HL) as HB.
  destruct HL as [Hnu [HT [H0 [HC Hrest]]]].
  rewrite <- H0; apply (HWeak_energy_initial_trace h u T); assumption.
Qed.

Theorem LHGP_FORWARD_REALIZED_STRONG_INITIAL : forall h k (b : OrthonormalBasis h),
  HComplete h -> forall fg tests td nu T g u p u0,
  GPNonzero g -> IntegralNonnegative td -> HGPPathRealizes h b g u p ->
  HilbertForwardLHModel h k fg tests td nu T u u0 ->
  GPStrongInitialTrace g p (HGPEncode b g u0).
Proof.
  intros h k b Hcomplete fg tests td nu T g u p u0 Hg HI Hreal HL.
  pose proof (LHGP_FORWARD_HILBERT_STRONG_INITIAL h k fg tests td nu T u u0 HI HL) as HS.
  apply (proj2 (LHGP_HILBERT_STRONG_INITIAL_TRACE h b Hcomplete u u0)) in HS.
  unfold GPStrongInitialTrace.
  apply (proj2 (strong_trace_ext (decode_path g p)
    (fun t => HAnalysis b (u t)) (decode g (HGPEncode b g u0))
    (HAnalysis b u0) (HGP_PATH_DECODE_REALIZATION h b g u p Hg Hreal)
    (decode_encode g (HAnalysis b u0) Hg))).
  exact HS.
Qed.

Print Assumptions LHGP_FORWARD_ENERGY_LEDGER.
Print Assumptions LHGP_FORWARD_REALIZED_CONTAINMENT.
Print Assumptions LHGP_FORWARD_ENCODING_CONTAINMENT.
Print Assumptions LHGP_FORWARD_ENCODING_INJECTIVE.
Print Assumptions LHGP_FORWARD_HILBERT_STRONG_INITIAL.
Print Assumptions LHGP_FORWARD_REALIZED_STRONG_INITIAL.

(* The previous restart class is retained as a source subclass. This
   implication forgets its additional restart and tensor-basis structure;
   no converse or automatic restart assertion is made. *)
Theorem LHGP_RESTART_LEDGER_TO_FORWARD_LEDGER : forall h gm td nu T u,
  HilbertEnergyLedger h gm td nu T u ->
  HilbertForwardEnergyLedger h (DTarget (GDual h gm))
    (GradientModelToForward h gm) td nu T u.
Proof.
  intros h gm td nu T u [E [D [GoodD [GoodStart [HS [HE HD]]]]]].
  exists E, D, GoodD; split.
  - apply ENERGY_SCHEDULE_IMPLIES_SCHEDULE0 with (GoodStart := GoodStart); exact HS.
  - split; [exact HE |].
    intros t Ht Hgood.
    apply (proj2 (GRADIENT_MODEL_FORWARD_ENERGY_EXACT h gm (u t) (D t))).
    apply HD; assumption.
Qed.

Theorem LHGP_RESTART_MODEL_TO_FORWARD_MODEL : forall h gm tests td nu T u u0,
  HilbertLHModel h gm tests td nu T u u0 ->
  HilbertForwardLHModel h (DTarget (GDual h gm))
    (GradientModelToForward h gm) tests td nu T u u0.
Proof.
  intros h gm tests td nu T u u0 [Hnu [HT [H0 [HC [HB [HW HE]]]]]].
  split; [exact Hnu |]; split; [exact HT |]; split; [exact H0 |].
  split; [exact HC |]; split; [exact HB |]; split; [exact HW |].
  apply LHGP_RESTART_LEDGER_TO_FORWARD_LEDGER; exact HE.
Qed.

Print Assumptions LHGP_RESTART_LEDGER_TO_FORWARD_LEDGER.
Print Assumptions LHGP_RESTART_MODEL_TO_FORWARD_MODEL.
