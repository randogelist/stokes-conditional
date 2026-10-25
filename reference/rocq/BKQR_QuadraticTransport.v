From Stdlib Require Import Reals Lra Psatz Field.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_TimeIntegrals.
Require Import BKQR_WeakBalance BKQR_EnergyPaths.

(* Independently defined coordinate and native quadratic weak equations.
   The source is an actual limit of tested finite coefficient polynomials;
   there is no supplied forcing readout. Physical NSE coefficient realization
   is a separate obligation. Source existence on energy paths is established
   for the bounded kernels in the nonlinear-time-source module. *)
Module BKQR_QUADRATIC_TRANSPORT.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_TIME_INTEGRALS.
Import BKQR_WEAK_BALANCE BKQR_ENERGY_PATHS.
Open Scope R_scope.

Definition quadratic_prefix (K : nat -> nat -> nat -> R)
  (u : R -> nat -> R) i N t :=
  gp_sum N (fun j => gp_sum N (fun l => K i j l * u t j * u t l)).

Lemma quadratic_prefix_continuous : forall K u a b,
  CoordinateContinuous u a b -> forall i N,
  ClosedContinuous (quadratic_prefix K u i N) a b.
Proof.
  intros K u a b Hu i N. unfold quadratic_prefix.
  apply continuous_gp_sum. intro j. apply continuous_gp_sum. intro l.
  apply wb_continuous_product; [apply continuous_scale|]; apply Hu.
Qed.

Definition coordinate_integrand (lambda : nat -> R) nu (u : R -> nat -> R) a b
  (eta : C1ZeroEndpointTest a b) i t :=
  -(u t i * test_derivative a b eta t) +
  nu * (lambda i * lambda i) * (u t i * test_value a b eta t).

Lemma coordinate_integrand_continuous : forall lambda nu u a b,
  CoordinateContinuous u a b -> forall eta i,
  ClosedContinuous (coordinate_integrand lambda nu u a b eta i) a b.
Proof.
  intros lambda nu u a b Hu eta i. unfold coordinate_integrand.
  apply continuous_plus.
  - apply wb_continuous_opp. apply wb_continuous_product.
    + apply Hu.
    + apply test_derivative_continuous.
  - apply continuous_scale. apply wb_continuous_product.
    + apply Hu.
    + apply test_value_continuous.
Qed.

Definition coordinate_linear lambda nu u a b Hab Hu eta i :=
  integral a b Hab (coordinate_integrand lambda nu u a b eta i)
    (coordinate_integrand_continuous lambda nu u a b Hu eta i).

Definition coordinate_source K u a b Hab Hu (eta : C1ZeroEndpointTest a b) i N :=
  integral a b Hab (fun t => test_value a b eta t * quadratic_prefix K u i N t)
    (wb_continuous_product a b _ _ (test_value_continuous a b eta)
      (quadratic_prefix_continuous K u a b Hu i N)).

(* The native expression uses only the ground shell, its scalar weights,
   and the same fixed coefficient tensor. Division is justified in the
   transport theorem by the constructed nonzero ground weights. *)
Definition native_quadratic_prefix K psi (U : R -> nat -> nat -> R) k i N t :=
  gp_sum N (fun j => gp_sum N (fun l =>
    (psi k i * K i j l / (psi 0%nat j * psi 0%nat l)) *
      U t 0%nat j * U t 0%nat l)).

Lemma native_quadratic_prefix_continuous : forall K psi U a b,
  ShellCoordinateContinuous U a b -> forall k i N,
  ClosedContinuous (native_quadratic_prefix K psi U k i N) a b.
Proof.
  intros K psi U a b HU k i N. unfold native_quadratic_prefix.
  apply continuous_gp_sum. intro j. apply continuous_gp_sum. intro l.
  apply wb_continuous_product; [apply continuous_scale|]; apply HU.
Qed.

Definition native_source K psi U a b Hab HU
  (eta : C1ZeroEndpointTest a b) k i N :=
  integral a b Hab
    (fun t => test_value a b eta t * native_quadratic_prefix K psi U k i N t)
    (wb_continuous_product a b _ _ (test_value_continuous a b eta)
      (native_quadratic_prefix_continuous K psi U a b HU k i N)).

Definition CoordinateQuadraticWeakEquation K lambda nu u a b Hab Hu : Prop :=
  forall eta i, SeqLimit (coordinate_source K u a b Hab Hu eta i)
    (- coordinate_linear lambda nu u a b Hab Hu eta i).

Definition NativeQuadraticWeakEquation K psi lambda ell nu U a b Hab HU : Prop :=
  forall eta k i, SeqLimit (native_source K psi U a b Hab HU eta k i)
    (- BKQR_WEAK_BALANCE.native_linear lambda ell a b nu Hab U HU eta k i).

Lemma nonzero_scale_limit_iff : forall f g c x,
  c <> 0 -> (forall N, g N = c*f N) ->
  (SeqLimit f x <-> SeqLimit g (c*x)).
Proof.
  intros f g c x Hc Heq. split.
  - intro H. eapply limit_ext; [intro N; symmetry; apply Heq|].
    apply limit_scale. exact H.
  - intro H. pose proof (limit_scale g (c*x) (/c) H) as HI.
    replace (/c*(c*x)) with x in HI by (field; exact Hc).
    apply (limit_ext (fun N => /c*g N) f x).
    + intro N. rewrite Heq. field. exact Hc.
    + exact HI.
Qed.

Section Factorization.
Variables K : nat -> nat -> nat -> R.
Variables psi : nat -> nat -> R.
Variables lambda ell : nat -> R.
Variables a b nu : R.
Variable Hab : a <= b.
Variable u : R -> nat -> R.
Variable U : R -> nat -> nat -> R.
Variable Hu : CoordinateContinuous u a b.
Variable HU : ShellCoordinateContinuous U a b.
Hypothesis Hzero : forall i, psi 0%nat i <> 0.
Hypothesis Hfactor : forall t k i, a <= t <= b -> U t k i=psi k i*u t i.
Hypothesis Hadjacent : forall t, a <= t <= b -> AdjacentCompatible lambda ell (U t).

Theorem BKQT10_FINITE_NONLINEAR_SOURCE_IDENTITY : forall k i N t,
  a <= t <= b ->
  native_quadratic_prefix K psi U k i N t = psi k i * quadratic_prefix K u i N t.
Proof.
  intros k i N t Ht. unfold native_quadratic_prefix, quadratic_prefix.
  rewrite <- gp_sum_scale. apply gp_sum_ext. intros j Hj.
  rewrite <- gp_sum_scale. apply gp_sum_ext. intros l Hl.
  rewrite (Hfactor t 0%nat j Ht), (Hfactor t 0%nat l Ht).
  field. split; apply Hzero.
Qed.

Theorem BKQT11_ACTUAL_TESTED_NONLINEAR_SOURCE_TRANSPORT : forall eta k i N,
  native_source K psi U a b Hab HU eta k i N =
  psi k i * coordinate_source K u a b Hab Hu eta i N.
Proof.
  intros eta k i N. unfold native_source, coordinate_source.
  set (f := fun t => test_value a b eta t * quadratic_prefix K u i N t).
  pose proof (wb_continuous_product a b _ _ (test_value_continuous a b eta)
    (quadratic_prefix_continuous K u a b Hu i N)) as Hf.
  transitivity (integral a b Hab (fun t => psi k i*f t)
    (continuous_scale a b (psi k i) f Hf)).
  - apply integral_ext. intros t Ht.
    rewrite BKQT10_FINITE_NONLINEAR_SOURCE_IDENTITY by exact Ht. unfold f. ring.
  - apply integral_scale.
Qed.

Theorem BKQT12_LINEAR_PART_TRANSPORT : forall eta k i,
  BKQR_WEAK_BALANCE.native_linear lambda ell a b nu Hab U HU eta k i =
  psi k i * coordinate_linear lambda nu u a b Hab Hu eta i.
Proof.
  intros eta k i. unfold BKQR_WEAK_BALANCE.native_linear, coordinate_linear.
  set (f := coordinate_integrand lambda nu u a b eta i).
  pose proof (coordinate_integrand_continuous lambda nu u a b Hu eta i) as Hf.
  transitivity (integral a b Hab (fun t => psi k i*f t)
    (continuous_scale a b (psi k i) f Hf)).
  - apply integral_ext. intros t Ht.
    unfold BKQR_WEAK_BALANCE.native_integrand, f, coordinate_integrand.
    pose proof (Hadjacent t Ht k i) as Hnext.
    unfold AdjacentCompatible in Hnext.
    replace (nu * (lambda i * ell k) * (U t (S k) i * test_value a b eta t))
      with (nu * lambda i * (ell k * U t (S k) i) * test_value a b eta t) by ring.
    rewrite <- Hnext, (Hfactor t k i Ht). ring.
  - apply integral_scale.
Qed.

Theorem BKQT20_EXACT_QUADRATIC_WEAK_EQUATION :
  CoordinateQuadraticWeakEquation K lambda nu u a b Hab Hu <->
  NativeQuadraticWeakEquation K psi lambda ell nu U a b Hab HU.
Proof.
  split.
  - intros H eta k i. rewrite BKQT12_LINEAR_PART_TRANSPORT.
    replace (- (psi k i * coordinate_linear lambda nu u a b Hab Hu eta i))
      with (psi k i * (-coordinate_linear lambda nu u a b Hab Hu eta i)) by ring.
    eapply limit_ext.
    + intro N. symmetry. apply BKQT11_ACTUAL_TESTED_NONLINEAR_SOURCE_TRANSPORT.
    + apply limit_scale. apply H.
  - intros H eta i. specialize (H eta 0%nat i).
    rewrite BKQT12_LINEAR_PART_TRANSPORT in H.
    replace (- (psi 0%nat i * coordinate_linear lambda nu u a b Hab Hu eta i))
      with (psi 0%nat i * (-coordinate_linear lambda nu u a b Hab Hu eta i)) in H by ring.
    apply (proj2 (nonzero_scale_limit_iff _ _ (psi 0%nat i) _ (Hzero i)
      (fun N => BKQT11_ACTUAL_TESTED_NONLINEAR_SOURCE_TRANSPORT eta 0%nat i N))).
    exact H.
Qed.
End Factorization.

(* Energy inequalities and the nonlinear weak equation are both included.
   Continuity witnesses are quantified rather than identified by axiom. *)
Definition SpectralQuadraticEnergyPath K lambda nu T Start u v0 E0 : Prop :=
  SpectralEnergyPath lambda nu T Start u v0 E0 /\
  forall (HT : 0 <= T) (Hu : CoordinateContinuous u 0 T),
    CoordinateQuadraticWeakEquation K lambda nu u 0 T HT Hu.

Definition NativeQuadraticEnergyPath K psi lambda ell nu T Start U V0 E0 : Prop :=
  NativeEnergyPath lambda ell nu T Start U V0 E0 /\
  forall (HT : 0 <= T) (HU : ShellCoordinateContinuous U 0 T),
    NativeQuadraticWeakEquation K psi lambda ell nu U 0 T HT HU.

Theorem BKQT30_EXACT_QUADRATIC_ENERGY_PATH :
  forall K psi lambda ell nu T Start u U v0 E0,
  0 <= T -> ScalarPartition psi -> (forall i, psi 0%nat i <> 0) ->
  CoordinateContinuous u 0 T -> ShellCoordinateContinuous U 0 T ->
  (forall t, 0 <= t <= T -> AdjacentCompatible lambda ell (U t)) ->
  (forall t k i, 0 <= t <= T -> U t k i=gp_encode psi (u t) k i) ->
  (SpectralQuadraticEnergyPath K lambda nu T Start u v0 E0 <->
   NativeQuadraticEnergyPath K psi lambda ell nu T Start U (gp_encode psi v0) E0).
Proof.
  intros K psi lambda ell nu T Start u U v0 E0 HT Hp H0 Hu HU HA HF.
  pose proof (BKEP22_EXACT_ENERGY_PATH psi lambda ell T HT Hp H0 u U Hu HU HA HF
    nu Start v0 E0) as HE.
  split; intros [Henergy Hweak]; split.
  - apply (proj1 HE). exact Henergy.
  - intros HT' HU'.
    apply (proj1 (BKQT20_EXACT_QUADRATIC_WEAK_EQUATION K psi lambda ell
      0 T nu HT' u U Hu HU' H0 HF HA)). apply Hweak.
  - apply (proj2 HE). exact Henergy.
  - intros HT' Hu'.
    apply (proj2 (BKQT20_EXACT_QUADRATIC_WEAK_EQUATION K psi lambda ell
      0 T nu HT' u U Hu' HU H0 HF HA)). apply Hweak.
Qed.

Print Assumptions BKQT11_ACTUAL_TESTED_NONLINEAR_SOURCE_TRANSPORT.
Print Assumptions BKQT20_EXACT_QUADRATIC_WEAK_EQUATION.
Print Assumptions BKQT30_EXACT_QUADRATIC_ENERGY_PATH.
End BKQR_QUADRATIC_TRANSPORT.
