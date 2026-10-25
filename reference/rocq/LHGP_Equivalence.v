From Stdlib Require Import Reals Lra Psatz.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Realization LHGP_Dual.
Require Import LHGP_WeakTopology LHGP_PathSynthesis.
Require Import LHGP_Gradient LHGP_Evolution.

Open Scope R_scope.

(* These predicates are two independently stated abstract evolution classes.
   They are not definitions by transport of one another. Concrete solenoidal
   L2(R^3), smooth tests, and Lebesgue time integration remain instances.

   Paths have values at every real time; all evolution conditions are on
   [0,T]. Pointwise square summability globally permits global synthesis.
   A finite-interval physical path can be extended outside the interval.

   GoodD and GoodStart are existential, solution-dependent sets. The finite
   variational value is required only on GoodD. D is a zero-extended scalar
   representative, not an assertion that every state's dissipation is finite.
   No measurability of a tensor-valued gradient path is inferred here. *)

Definition EnergySchedule (td : TimeData) (nu T : R)
    (E D : R -> R) (GoodD GoodStart : R -> Prop) : Prop :=
  TFullMeasure td T GoodD /\
  TFullMeasure td T GoodStart /\
  (forall t, 0 <= D t) /\
  (forall t, ~ (0 <= t <= T /\ GoodD t) -> D t = 0) /\
  (forall s t, 0 <= s <= t -> t <= T -> TIntegrable td s t D) /\
  RestartEnergyInequality nu T GoodStart (TIntegral td) E D.

(* A genuine positive time integral discharges this explicit law. It is
   unnecessary for representation equivalence, but essential when deducing
   the initial energy bound and strong initial convergence from the ledger. *)
Definition IntegralNonnegative (td : TimeData) : Prop :=
  forall s t f, s <= t -> TIntegrable td s t f ->
    (forall r, s <= r <= t -> 0 <= f r) -> 0 <= TIntegral td s t f.

Definition HilbertEnergyLedger (h : HilbertData) (gm : GradientModel h)
    (td : TimeData) (nu T : R) (u : R -> HCarrier h) : Prop :=
  exists (E D : R -> R) (GoodD GoodStart : R -> Prop),
    EnergySchedule td nu T E D GoodD GoodStart /\
    (forall t, E t = HNorm h (u t)) /\
    (forall t, 0 <= t <= T -> GoodD t ->
      GradientEnergyAt h gm (u t) (D t)).

Definition GPEnergyLedger (h : HilbertData) (b : OrthonormalBasis h)
    (gm : GradientModel h) (td : TimeData) (nu T : R)
    (g : Seq) (p : CoefficientPath) : Prop :=
  exists (E D : R -> R) (GoodD GoodStart : R -> Prop),
    EnergySchedule td nu T E D GoodD GoodStart /\
    EnergyTrace (decode_path g p) E /\
    (forall t, 0 <= t <= T -> GoodD t ->
      GPDissipationValue h b gm g (p t) (D t)).

Definition HilbertLHModel (h : HilbertData) (gm : GradientModel h)
    (tests : EvolutionTests h) (td : TimeData) (nu T : R)
    (u : R -> HCarrier h) (u0 : HCarrier h) : Prop :=
  0 < nu /\ 0 < T /\
  u 0 = u0 /\
  HWeakContinuous h u T /\
  (exists M, forall t, 0 <= t <= T -> HNorm h (u t) <= M) /\
  HilbertWeakForm h tests td nu T u u0 /\
  HilbertEnergyLedger h gm td nu T u.

Definition GPLHModel (h : HilbertData) (b : OrthonormalBasis h)
    (gm : GradientModel h) (tests : EvolutionTests h) (td : TimeData)
    (nu T : R) (g : Seq) (p : CoefficientPath) (p0 : Seq) : Prop :=
  0 < nu /\ 0 < T /\
  (forall t, GPL2 g (p t)) /\
  seq_eq (p 0) p0 /\
  CoordinatesContinuous (decode_path g p) T /\
  (exists M, GPEnergyBound g p T M) /\
  GPWeakForm h b tests td nu T g p p0 /\
  GPEnergyLedger h b gm td nu T g p.

Section Equivalence.
Variable h : HilbertData.
Variable b : OrthonormalBasis h.
Hypothesis Hcomplete : HComplete h.
Variable gm : GradientModel h.
Variable tests : EvolutionTests h.
Variable td : TimeData.
Variables nu T : R.
Variable g : Seq.
Hypothesis Hg : GPNonzero g.

Theorem LHGP_ENERGY_LEDGER_EXACT : forall u p,
  HGPPathRealizes h b g u p ->
  (HilbertEnergyLedger h gm td nu T u <->
   GPEnergyLedger h b gm td nu T g p).
Proof.
  intros u p Hu; split.
  - intros [E [D [GoodD [GoodStart [HS [HE HD]]]]]].
    exists E, D, GoodD, GoodStart; split; [exact HS|]; split.
    + intro t; rewrite HE.
      exact (HGP_PATH_ENERGY_EXACT h b Hcomplete g u p Hg Hu t).
    + intros t Ht Hgood.
      apply (proj2 (GRADIENT_DISSIPATION_EXACT h b Hcomplete gm g
        (u t) (p t) (D t) Hg (Hu t))).
      apply HD; assumption.
  - intros [E [D [GoodD [GoodStart [HS [HE HD]]]]]].
    exists E, D, GoodD, GoodStart; split; [exact HS|]; split.
    + exact (HGP_PATH_ENERGY_VALUE_UNIQUE h b Hcomplete g u p E Hg Hu HE).
    + intros t Ht Hgood.
      apply (proj1 (GRADIENT_DISSIPATION_EXACT h b Hcomplete gm g
        (u t) (p t) (D t) Hg (Hu t))).
      apply HD; assumption.
Qed.

Theorem LHGP_CONTINUITY_AND_BOUND_EXACT : forall u p,
  HGPPathRealizes h b g u p ->
  ((HWeakContinuous h u T /\
    exists M, forall t, 0 <= t <= T -> HNorm h (u t) <= M) <->
   (CoordinatesContinuous (decode_path g p) T /\
    exists M, GPEnergyBound g p T M)).
Proof.
  intros u p Hu.
  assert (HC : CoordinatesContinuous (decode_path g p) T <->
    HCoordinatesContinuous b u T).
  { apply CoordinatesContinuous_ext; intros t Ht.
    exact (HGP_PATH_DECODE_REALIZATION h b g u p Hg Hu t). }
  split.
  - intros [Hweak [M HM]]; split.
    + apply (proj2 HC); apply HWeakContinuous_to_coordinates; exact Hweak.
    + exists M; apply (proj2 (HGP_PATH_PREFIX_BOUND_IFF h b Hcomplete
        g u p T M Hg Hu)); exact HM.
  - intros [Hcoords [M HM]].
    assert (HB : forall t, 0 <= t <= T -> HNorm h (u t) <= M).
    { apply (proj1 (HGP_PATH_PREFIX_BOUND_IFF h b Hcomplete
        g u p T M Hg Hu)); exact HM. }
    split.
    + apply (HCoordinates_and_norm_bound_weak h b Hcomplete u T M);
        [apply (proj1 HC); exact Hcoords|exact HB].
    + exists M; exact HB.
Qed.

Theorem LHGP_REALIZED_TRAJECTORY_EQUIVALENCE : forall u p u0,
  HGPPathRealizes h b g u p ->
  (HilbertLHModel h gm tests td nu T u u0 <->
   GPLHModel h b gm tests td nu T g p (HGPEncode b g u0)).
Proof.
  intros u p u0 Hu; split.
  - intros [Hnu [HT [H0 [HC [HB [HW HE]]]]]].
    destruct (proj1 (LHGP_CONTINUITY_AND_BOUND_EXACT u p Hu)
      (conj HC HB)) as [HCp HBp].
    split; [exact Hnu|]; split; [exact HT|]; split.
    + intro t; unfold GPL2.
      apply (proj2 (CoordinateL2_ext _ _
        (HGP_PATH_DECODE_REALIZATION h b g u p Hg Hu t))).
      apply HAnalysis_L2.
    + split.
      * intro i; rewrite <- (Hu 0 i), H0; reflexivity.
      * split; [exact HCp|]; split; [exact HBp|]; split.
        -- apply (proj1 (EVOLUTION_WEAK_FORM_EXACT h b Hcomplete tests td
             nu T g u p u0 (HGPEncode b g u0) Hg Hu (seq_eq_refl _))).
           exact HW.
        -- apply (proj1 (LHGP_ENERGY_LEDGER_EXACT u p Hu)); exact HE.
  - intros [Hnu [HT [Hp [H0 [HC [HB [HW HE]]]]]]].
    destruct (proj2 (LHGP_CONTINUITY_AND_BOUND_EXACT u p Hu)
      (conj HC HB)) as [HCu HBu].
    split; [exact Hnu|]; split; [exact HT|]; split.
    + exact (HGP_PATH_INITIAL_MATCH h b g u p 0 u0 Hg Hu H0).
    + split; [exact HCu|]; split; [exact HBu|]; split.
      * apply (proj2 (EVOLUTION_WEAK_FORM_EXACT h b Hcomplete tests td
          nu T g u p u0 (HGPEncode b g u0) Hg Hu (seq_eq_refl _))).
        exact HW.
      * apply (proj2 (LHGP_ENERGY_LEDGER_EXACT u p Hu)); exact HE.
Qed.

Theorem LHGP_ENCODING_TRAJECTORY_EQUIVALENCE : forall u u0,
  HilbertLHModel h gm tests td nu T u u0 <->
  GPLHModel h b gm tests td nu T g
    (fun t => HGPEncode b g (u t)) (HGPEncode b g u0).
Proof.
  intros u u0; apply LHGP_REALIZED_TRAJECTORY_EQUIVALENCE.
  intros t i; reflexivity.
Qed.

(* The uniqueness clause is for a fixed entire coefficient trajectory.
   It is not uniqueness of Navier-Stokes solutions for fixed initial data. *)
Theorem LHGP_TRAJECTORY_EQUIVALENCE : forall p u0,
  GPLHModel h b gm tests td nu T g p (HGPEncode b g u0) <->
  exists u : R -> HCarrier h,
    HilbertLHModel h gm tests td nu T u u0 /\
    HGPPathRealizes h b g u p /\
    (forall v, HGPPathRealizes h b g v p -> forall t, v t = u t).
Proof.
  intros p u0; split.
  - intro HP.
    destruct HP as [Hnu [HT [Hp Hrest]]].
    destruct (HGP_PATH_SURJECTIVE_UNIQUE h b Hcomplete g p Hg Hp)
      as [u [Hu [HE Hunique]]].
    exists u; split.
    + apply (proj2 (LHGP_REALIZED_TRAJECTORY_EQUIVALENCE u p u0 Hu)).
      split; [exact Hnu|]; split; [exact HT|]; split; assumption.
    + split; assumption.
  - intros [u [HL [Hu Hunique]]].
    apply (proj1 (LHGP_REALIZED_TRAJECTORY_EQUIVALENCE u p u0 Hu)); exact HL.
Qed.

End Equivalence.

Theorem LHGP_INITIAL_NORM_BOUND : forall h gm tests td nu T u u0,
  IntegralNonnegative td ->
  HilbertLHModel h gm tests td nu T u u0 ->
  forall t, 0 <= t <= T -> HNorm h (u t) <= HNorm h (u 0).
Proof.
  intros h gm tests td nu T u u0 HI HL t Ht.
  destruct HL as [Hnu [HT [H0 [HC [HB [HW HE]]]]]].
  destruct HE as [E [D [GoodD [GoodStart [HS [HE HD]]]]]].
  destruct HS as [HfullD [HfullS [HDnonneg [HDzero [HDint HR]]]]].
  pose proof (HR 0 t ltac:(lra) (proj2 Ht) (or_introl eq_refl)) as HEI.
  assert (HIpos : 0 <= TIntegral td 0 t D).
  { apply HI; [lra|apply HDint; lra|intros r Hr; apply HDnonneg]. }
  rewrite (HE t), (HE 0) in HEI.
  assert (0 <= 2 * nu * TIntegral td 0 t D) by nra.
  lra.
Qed.

Theorem LHGP_HILBERT_MODEL_STRONG_INITIAL : forall h gm tests td nu T u u0,
  IntegralNonnegative td ->
  HilbertLHModel h gm tests td nu T u u0 ->
  EnergyInitialTrace (fun t => HDist h (u t) u0).
Proof.
  intros h gm tests td nu T u u0 HI HL.
  pose proof (LHGP_INITIAL_NORM_BOUND h gm tests td nu T u u0 HI HL) as HB.
  destruct HL as [Hnu [HT [H0 [HC Hrest]]]].
  rewrite <- H0; apply (HWeak_energy_initial_trace h u T); assumption.
Qed.

Theorem LHGP_GP_MODEL_STRONG_INITIAL : forall h (b : OrthonormalBasis h),
  HComplete h -> forall gm tests td nu T g p u0,
  GPNonzero g -> IntegralNonnegative td ->
  GPLHModel h b gm tests td nu T g p (HGPEncode b g u0) ->
  GPStrongInitialTrace g p (HGPEncode b g u0).
Proof.
  intros h b Hcomplete gm tests td nu T g p u0 Hg HI HP.
  destruct (proj1 (LHGP_TRAJECTORY_EQUIVALENCE h b Hcomplete gm tests td
    nu T g Hg p u0) HP) as [u [HL [Hu Hunique]]].
  pose proof (LHGP_HILBERT_MODEL_STRONG_INITIAL h gm tests td nu T u u0
    HI HL) as HS.
  apply (proj2 (LHGP_HILBERT_STRONG_INITIAL_TRACE h b Hcomplete u u0)) in HS.
  unfold GPStrongInitialTrace.
  apply (proj2 (strong_trace_ext (decode_path g p)
    (fun t => HAnalysis b (u t)) (decode g (HGPEncode b g u0))
    (HAnalysis b u0)
    (HGP_PATH_DECODE_REALIZATION h b g u p Hg Hu)
    (decode_encode g (HAnalysis b u0) Hg))).
  exact HS.
Qed.

Print Assumptions LHGP_ENERGY_LEDGER_EXACT.
Print Assumptions LHGP_CONTINUITY_AND_BOUND_EXACT.
Print Assumptions LHGP_ENCODING_TRAJECTORY_EQUIVALENCE.
Print Assumptions LHGP_TRAJECTORY_EQUIVALENCE.
Print Assumptions LHGP_HILBERT_MODEL_STRONG_INITIAL.
Print Assumptions LHGP_GP_MODEL_STRONG_INITIAL.
