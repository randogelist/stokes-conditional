From Stdlib Require Import Reals Lra Psatz Logic.ClassicalUniqueChoice.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Bilinear LHGP_Realization.

Open Scope R_scope.

(* Pointwise Hilbert synthesis is assembled into one actual time-indexed
   carrier-valued function. ClassicalUniqueChoice is explicit and is used
   only to reify the already unique pointwise value. Uniqueness below is
   pointwise; no functional
   extensionality axiom is introduced for paths.

   These results remain abstract Hilbert realization statements. They do
   not construct the concrete R^3 solenoidal Hilbert space, its basis,
   the physical convection form, or Lebesgue time integration. *)

Definition HGPPathRealizes (h : HilbertData) (b : OrthonormalBasis h)
  (g : Seq) (u : R -> HCarrier h) (p : CoefficientPath) : Prop :=
  forall t, seq_eq (HGPEncode b g (u t)) (p t).

Theorem HGP_PATH_DECODE_REALIZATION : forall h (b : OrthonormalBasis h)
  g u p,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  forall t, seq_eq (decode g (p t)) (HAnalysis b (u t)).
Proof.
  intros h b g u p Hg Hu t i.
  unfold decode; rewrite <- (Hu t i).
  unfold HGPEncode, encode; field; apply Hg.
Qed.

Theorem HGP_PATH_POINTWISE_UNIQUE : forall h (b : OrthonormalBasis h)
  g u v p,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  HGPPathRealizes h b g v p -> forall t, v t = u t.
Proof.
  intros h b g u v p Hg Hu Hv t.
  apply (HGP_injective h b g); [exact Hg |].
  intro i; rewrite (Hu t i), (Hv t i); reflexivity.
Qed.

Theorem HGP_PATH_ENERGY_EXACT : forall h (b : OrthonormalBasis h),
  HComplete h -> forall g u p,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  forall t, EnergyValue (decode g (p t)) (HNorm h (u t)).
Proof.
  intros h b Hcomplete g u p Hg Hu t.
  apply (proj2 (EnergyValue_ext _ _ (HNorm h (u t))
    (HGP_PATH_DECODE_REALIZATION h b g u p Hg Hu t))).
  apply HAnalysis_parseval; exact Hcomplete.
Qed.

Theorem HGP_PATH_SURJECTIVE_UNIQUE : forall h (b : OrthonormalBasis h),
  HComplete h -> forall g p,
  GPNonzero g -> (forall t, GPL2 g (p t)) ->
  exists u : R -> HCarrier h,
    HGPPathRealizes h b g u p /\
    (forall t, EnergyValue (decode g (p t)) (HNorm h (u t))) /\
    (forall v, HGPPathRealizes h b g v p -> forall t, v t = u t).
Proof.
  intros h b Hcomplete g p Hg Hp.
  assert (Hpoint : forall t : R, exists! x : HCarrier h,
    seq_eq (HGPEncode b g x) (p t)).
  { intro t.
    destruct (HGP_surjective_unique h b Hcomplete g (p t) Hg (Hp t))
      as [x [Hx [_ Hunique]]].
    exists x; split; [exact Hx |].
    intros y Hy; symmetry; apply Hunique; exact Hy. }
  destruct (unique_choice R (HCarrier h)
    (fun t x => seq_eq (HGPEncode b g x) (p t)) Hpoint)
    as [u Hu].
  exists u; split; [exact Hu |]; split.
  - exact (HGP_PATH_ENERGY_EXACT h b Hcomplete g u p Hg Hu).
  - intros v Hv; exact (HGP_PATH_POINTWISE_UNIQUE h b g u v p Hg Hu Hv).
Qed.

Theorem HGP_PATH_INITIAL_MATCH : forall h (b : OrthonormalBasis h)
  g u p s u0,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  seq_eq (p s) (HGPEncode b g u0) -> u s = u0.
Proof.
  intros h b g u p s u0 Hg Hu H0.
  apply (HGP_injective h b g); [exact Hg |].
  intro i; rewrite (Hu s i); apply H0.
Qed.

Theorem HGP_PATH_ENERGY_VALUE_UNIQUE : forall h (b : OrthonormalBasis h),
  HComplete h -> forall g u p E,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  (forall t, EnergyValue (decode g (p t)) (E t)) ->
  forall t, E t = HNorm h (u t).
Proof.
  intros h b Hcomplete g u p E Hg Hu HE t.
  eapply EnergyValue_unique; [apply HE |].
  exact (HGP_PATH_ENERGY_EXACT h b Hcomplete g u p Hg Hu t).
Qed.

Theorem HGP_PATH_PREFIX_BOUND_IFF : forall h (b : OrthonormalBasis h),
  HComplete h -> forall g u p T B,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  (GPEnergyBound g p T B <->
   forall t, 0 <= t <= T -> HNorm h (u t) <= B).
Proof.
  intros h b Hcomplete g u p T B Hg Hu; split.
  - intros HP t Ht.
    destruct (HGP_PATH_ENERGY_EXACT h b Hcomplete g u p Hg Hu t)
      as [_ Hleast].
    apply Hleast; intro n; exact (HP t Ht n).
  - intros HB t Ht n.
    destruct (HGP_PATH_ENERGY_EXACT h b Hcomplete g u p Hg Hu t)
      as [Hupper _].
    specialize (Hupper n); specialize (HB t Ht).
    change (energy_prefix (decode g (p t)) n <= B); lra.
Qed.

Theorem HGP_PATH_LINEAR_READOUT : forall h (b : OrthonormalBasis h),
  HComplete h -> forall g u p,
  GPNonzero g -> HGPPathRealizes h b g u p ->
  forall t y,
    linear_limit (decode g (p t)) (HAnalysis b y) (HInner h (u t) y).
Proof.
  intros h b Hcomplete g u p Hg Hu t y.
  apply (proj2 (linear_limit_ext _ _ (HAnalysis b y) (HInner h (u t) y)
    (HGP_PATH_DECODE_REALIZATION h b g u p Hg Hu t))).
  apply HAnalysis_linear_readout; exact Hcomplete.
Qed.

Section PathQuadraticReadout.
Variable h : HilbertData.
Variable b : OrthonormalBasis h.
Hypothesis Hcomplete : HComplete h.
Variable B : HCarrier h -> HCarrier h -> R.
Hypothesis Badd_left : forall x y z,
  B (HAdd h x y) z = B x z + B y z.
Hypothesis Badd_right : forall x y z,
  B x (HAdd h y z) = B x y + B x z.
Hypothesis Bscale_left : forall c x y,
  B (HScale h c x) y = c * B x y.
Hypothesis Bscale_right : forall c x y,
  B x (HScale h c y) = c * B x y.
Variable C : R.
Hypothesis Cnonnegative : 0 <= C.
Hypothesis Bbound : forall x y,
  Rabs (B x y) <= C * HLength h x * HLength h y.

Theorem HGP_PATH_QUADRATIC_READOUT : forall g u p,
  GPNonzero g -> HGPPathRealizes h b g u p -> forall t,
  quadratic_limit (decode g (p t))
    (fun i j => B (HBasis h b i) (HBasis h b j)) (B (u t) (u t)).
Proof.
  intros g u p Hg Hu t.
  apply (proj2 (quadratic_limit_ext _ _
    (fun i j => B (HBasis h b i) (HBasis h b j)) (B (u t) (u t))
    (HGP_PATH_DECODE_REALIZATION h b g u p Hg Hu t))).
  exact (LHGP_HILBERT_QUADRATIC_READOUT h b Hcomplete B
    Badd_left Badd_right Bscale_left Bscale_right C Cnonnegative Bbound (u t)).
Qed.
End PathQuadraticReadout.

Print Assumptions HGP_PATH_SURJECTIVE_UNIQUE.
Print Assumptions HGP_PATH_POINTWISE_UNIQUE.
Print Assumptions HGP_PATH_ENERGY_EXACT.
Print Assumptions HGP_PATH_INITIAL_MATCH.
Print Assumptions HGP_PATH_PREFIX_BOUND_IFF.
Print Assumptions HGP_PATH_LINEAR_READOUT.
Print Assumptions HGP_PATH_QUADRATIC_READOUT.
