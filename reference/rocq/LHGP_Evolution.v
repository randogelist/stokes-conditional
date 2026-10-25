From Stdlib Require Import Reals Lra Psatz Logic.FunctionalExtensionality.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Bilinear LHGP_Realization LHGP_PathSynthesis.

Open Scope R_scope.

(* The test vectors and bounded convection forms are explicit analytic data.
   TimeData supplies operators and predicates, not a disguised proof that
   those operators are Lebesgue integration or that a set has full measure.
   The theorem below needs no integration laws: it identifies each scalar
   readout pointwise, then uses functional extensionality to substitute the
   identical integrands. All physical instances remain separate obligations. *)

Record EvolutionTests (h : HilbertData) := {
  ETest : Type;
  ETime : ETest -> R -> HCarrier h;
  ELap : ETest -> R -> HCarrier h;
  EInitial : ETest -> HCarrier h;
  EConvection : ETest -> R -> HCarrier h -> HCarrier h -> R;
  EConvection_add_left : forall test t x y z,
    EConvection test t (HAdd h x y) z =
    EConvection test t x z + EConvection test t y z;
  EConvection_add_right : forall test t x y z,
    EConvection test t x (HAdd h y z) =
    EConvection test t x y + EConvection test t x z;
  EConvection_scale_left : forall test t c x y,
    EConvection test t (HScale h c x) y = c * EConvection test t x y;
  EConvection_scale_right : forall test t c x y,
    EConvection test t x (HScale h c y) = c * EConvection test t x y;
  EConvection_bound_constant : ETest -> R -> R;
  EConvection_bound_nonnegative : forall test t,
    0 <= EConvection_bound_constant test t;
  EConvection_bound : forall test t x y,
    Rabs (EConvection test t x y) <=
    EConvection_bound_constant test t * HLength h x * HLength h y
}.

Record TimeData := {
  TIntegral : TimeIntegral;
  TIntegrable : R -> R -> (R -> R) -> Prop;
  TFullMeasure : R -> (R -> Prop) -> Prop
}.

Definition EvolutionScalarBalance (td : TimeData) (nu T : R)
    (lt lv nl : R -> R) (initial : R) : Prop :=
  TIntegrable td 0 T lt /\
  TIntegrable td 0 T lv /\
  TIntegrable td 0 T nl /\
  TIntegral td 0 T lt + nu * TIntegral td 0 T lv +
    TIntegral td 0 T nl + initial = 0.

Definition HilbertWeakForm (h : HilbertData) (tests : EvolutionTests h)
    (td : TimeData) (nu T : R) (u : R -> HCarrier h)
    (u0 : HCarrier h) : Prop :=
  forall test : ETest h tests,
    EvolutionScalarBalance td nu T
      (fun t => HInner h (u t) (ETime h tests test t))
      (fun t => HInner h (u t) (ELap h tests test t))
      (fun t => EConvection h tests test t (u t) (u t))
      (HInner h u0 (EInitial h tests test)).

Definition GPWeakForm (h : HilbertData) (b : OrthonormalBasis h)
    (tests : EvolutionTests h) (td : TimeData) (nu T : R)
    (g : Seq) (p : CoefficientPath) (p0 : Seq) : Prop :=
  forall test : ETest h tests,
    exists lt lv nl : R -> R, exists initial : R,
      (forall t, linear_limit (decode g (p t))
        (HAnalysis b (ETime h tests test t)) (lt t)) /\
      (forall t, linear_limit (decode g (p t))
        (HAnalysis b (ELap h tests test t)) (lv t)) /\
      (forall t, quadratic_limit (decode g (p t))
        (fun i j => EConvection h tests test t
          (HBasis h b i) (HBasis h b j)) (nl t)) /\
      linear_limit (decode g p0)
        (HAnalysis b (EInitial h tests test)) initial /\
      EvolutionScalarBalance td nu T lt lv nl initial.

Theorem EVOLUTION_INITIAL_READOUT : forall h (b : OrthonormalBasis h),
  HComplete h -> forall g u0 p0,
  GPNonzero g -> seq_eq (HGPEncode b g u0) p0 ->
  forall y, linear_limit (decode g p0) (HAnalysis b y) (HInner h u0 y).
Proof.
  intros h b Hcomplete g u0 p0 Hg Hinitial y.
  assert (Hdecoded : seq_eq (decode g p0) (HAnalysis b u0)).
  { intro i; unfold decode; rewrite <- (Hinitial i).
    unfold HGPEncode, encode; field; apply Hg. }
  apply (proj2 (linear_limit_ext _ _ (HAnalysis b y)
    (HInner h u0 y) Hdecoded)).
  apply HAnalysis_linear_readout; exact Hcomplete.
Qed.

Theorem EVOLUTION_QUADRATIC_READOUT : forall h (b : OrthonormalBasis h),
  HComplete h -> forall (tests : EvolutionTests h) g u p,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  forall (test : ETest h tests) t,
    quadratic_limit (decode g (p t))
      (fun i j => EConvection h tests test t
        (HBasis h b i) (HBasis h b j))
      (EConvection h tests test t (u t) (u t)).
Proof.
  intros h b Hcomplete tests g u p Hg Hu test t.
  exact (HGP_PATH_QUADRATIC_READOUT h b Hcomplete
    (EConvection h tests test t)
    (EConvection_add_left h tests test t)
    (EConvection_add_right h tests test t)
    (EConvection_scale_left h tests test t)
    (EConvection_scale_right h tests test t)
    (EConvection_bound_constant h tests test t)
    (EConvection_bound_nonnegative h tests test t)
    (EConvection_bound h tests test t) g u p Hg Hu t).
Qed.

Theorem EVOLUTION_WEAK_FORM_EXACT : forall h (b : OrthonormalBasis h),
  HComplete h -> forall (tests : EvolutionTests h) (td : TimeData)
    nu T g u p u0 p0,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  seq_eq (HGPEncode b g u0) p0 ->
  (HilbertWeakForm h tests td nu T u u0 <->
   GPWeakForm h b tests td nu T g p p0).
Proof.
  intros h b Hcomplete tests td nu T g u p u0 p0 Hg Hu Hinitial.
  split.
  - intros Hweak test.
    exists (fun t => HInner h (u t) (ETime h tests test t)),
      (fun t => HInner h (u t) (ELap h tests test t)),
      (fun t => EConvection h tests test t (u t) (u t)),
      (HInner h u0 (EInitial h tests test)).
    split.
    + intro t; apply (HGP_PATH_LINEAR_READOUT h b Hcomplete g u p Hg Hu).
    + split.
      * intro t; apply (HGP_PATH_LINEAR_READOUT h b Hcomplete g u p Hg Hu).
      * split.
        -- intro t; apply (EVOLUTION_QUADRATIC_READOUT h b Hcomplete tests
             g u p Hg Hu).
        -- split.
           ++ apply (EVOLUTION_INITIAL_READOUT h b Hcomplete g u0 p0
                Hg Hinitial).
           ++ apply Hweak.
  - intros Hweak test.
    destruct (Hweak test) as
      [lt [lv [nl [initial [Ht [Hv [Hn [Hi Hbalance]]]]]]]].
    assert (Htime : lt = fun t => HInner h (u t) (ETime h tests test t)).
    { apply functional_extensionality; intro t.
      eapply linear_limit_unique; [apply Ht |].
      apply (HGP_PATH_LINEAR_READOUT h b Hcomplete g u p Hg Hu). }
    assert (Hlap : lv = fun t => HInner h (u t) (ELap h tests test t)).
    { apply functional_extensionality; intro t.
      eapply linear_limit_unique; [apply Hv |].
      apply (HGP_PATH_LINEAR_READOUT h b Hcomplete g u p Hg Hu). }
    assert (Hnonlinear : nl = fun t => EConvection h tests test t (u t) (u t)).
    { apply functional_extensionality; intro t.
      eapply SeqLimit_unique; [apply Hn |].
      apply (EVOLUTION_QUADRATIC_READOUT h b Hcomplete tests g u p Hg Hu). }
    assert (Hinit : initial = HInner h u0 (EInitial h tests test)).
    { eapply linear_limit_unique; [exact Hi |].
      apply (EVOLUTION_INITIAL_READOUT h b Hcomplete g u0 p0 Hg Hinitial). }
    rewrite Htime, Hlap, Hnonlinear, Hinit in Hbalance.
    exact Hbalance.
Qed.

Print Assumptions EVOLUTION_INITIAL_READOUT.
Print Assumptions EVOLUTION_QUADRATIC_READOUT.
Print Assumptions EVOLUTION_WEAK_FORM_EXACT.
