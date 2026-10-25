From Stdlib Require Import Reals RiemannInt Lra Psatz Field.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_TimeIntegrals.

(* Exact transport of an interval weak linear balance with a supplied
   forcing readout.  The coordinate terms below are actual Riemann
   integrals, and the tests carry their actual derivative relation.
   The forcing is not constructed from Navier--Stokes convection here.
   In particular, this module does not identify a physical distribution,
   prove a nonlinear weak equation, or define a Leray--Hopf solution. *)
Module BKQR_WEAK_BALANCE.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_TIME_INTEGRALS.
Open Scope R_scope.

Record C1ZeroEndpointTest (a b : R) : Type := {
  test_value : R -> R;
  test_derivative : R -> R;
  test_derivative_correct : forall t, a <= t <= b ->
    derivable_pt_lim test_value t (test_derivative t);
  test_derivative_continuous : ClosedContinuous test_derivative a b;
  test_zero_left : test_value a = 0;
  test_zero_right : test_value b = 0
}.

Lemma test_value_continuous : forall a b (eta : C1ZeroEndpointTest a b),
  ClosedContinuous (test_value a b eta) a b.
Proof.
  intros a b eta t Ht. apply derivable_continuous_pt.
  exists (test_derivative a b eta t).
  apply test_derivative_correct. exact Ht.
Qed.

Definition quadratic_interval_test (a b : R) : C1ZeroEndpointTest a b.
Proof.
  refine {| test_value := fun t => (t-a)*(b-t);
    test_derivative := fun t => a+b-2*t |}.
  - intros t Ht.
    replace (a+b-2*t) with ((1-0)*(b-t)+(t-a)*(0-1)) by ring.
    apply (derivable_pt_lim_mult (fun x => x-a) (fun x => b-x)
      t (1-0) (0-1)).
    + apply derivable_pt_lim_minus.
      * apply derivable_pt_lim_id.
      * apply derivable_pt_lim_const.
    + apply derivable_pt_lim_minus.
      * apply derivable_pt_lim_const.
      * apply derivable_pt_lim_id.
  - intros t Ht. apply continuity_pt_minus.
    + apply continuity_pt_const. intros x y. reflexivity.
    + apply continuity_pt_mult.
      * apply continuity_pt_const. intros x y. reflexivity.
      * apply derivable_continuous_pt. apply derivable_pt_id.
  - ring.
  - ring.
Defined.

Lemma quadratic_test_nontrivial : forall a b, a < b ->
  0 < test_value a b (quadratic_interval_test a b) ((a+b)/2).
Proof.
  intros a b Hab. cbn. apply Rmult_lt_0_compat; lra.
Qed.

Lemma wb_continuous_product : forall a b f g,
  ClosedContinuous f a b -> ClosedContinuous g a b ->
  ClosedContinuous (fun t => f t * g t) a b.
Proof.
  intros a b f g Hf Hg t Ht.
  apply continuity_pt_mult; [apply Hf|apply Hg]; exact Ht.
Qed.

Lemma wb_continuous_opp : forall a b f,
  ClosedContinuous f a b -> ClosedContinuous (fun t => -f t) a b.
Proof.
  intros a b f Hf t Ht. apply continuity_pt_opp. apply Hf. exact Ht.
Qed.

Section CompatiblePath.
Variables psi : nat -> nat -> R.
Variables lambda ell : nat -> R.
Variables a b nu : R.
Hypothesis Hab : a <= b.
Variable U : R -> nat -> nat -> R.
Hypothesis HU : ShellCoordinateContinuous U a b.
Hypothesis Hraising : ScalarRaising psi lambda ell.
Hypothesis Hzero : forall i, psi 0%nat i <> 0.
Hypothesis Hell : forall k, ell k <> 0.
Hypothesis Hadjacent : forall t, a <= t <= b ->
  AdjacentCompatible lambda ell (U t).

Definition recovered (t : R) (i : nat) : R := reconstruct psi (U t) i.

Lemma recovered_continuous : CoordinateContinuous recovered a b.
Proof.
  intros i t Ht. unfold recovered, reconstruct, Rdiv.
  apply continuity_pt_mult.
  - apply HU. exact Ht.
  - apply continuity_pt_const. intros x y. reflexivity.
Qed.

Lemma path_factorization : forall t, a <= t <= b -> forall k i,
  U t k i = psi k i * recovered t i.
Proof.
  intros t Ht k i.
  exact (BKSC03_ADJACENCY_FORCES_FACTORIZATION psi lambda ell (U t)
    Hraising Hzero Hell (Hadjacent t Ht) k i).
Qed.

(* These are independent physical-coordinate and native adjacent-block
   expressions. Their equality is proved from compatibility, not assumed. *)
Definition physical_integrand (eta : C1ZeroEndpointTest a b) (i : nat)
  (t : R) : R :=
  -(recovered t i * test_derivative a b eta t) +
  nu * (lambda i * lambda i) * (recovered t i * test_value a b eta t).

Definition native_integrand (eta : C1ZeroEndpointTest a b) (k i : nat)
  (t : R) : R :=
  -(U t k i * test_derivative a b eta t) +
  nu * (lambda i * ell k) * (U t (S k) i * test_value a b eta t).

Lemma physical_integrand_continuous : forall eta i,
  ClosedContinuous (physical_integrand eta i) a b.
Proof.
  intros eta i. unfold physical_integrand. apply continuous_plus.
  - apply wb_continuous_opp. apply wb_continuous_product.
    + apply recovered_continuous.
    + apply test_derivative_continuous.
  - apply continuous_scale. apply wb_continuous_product.
    + apply recovered_continuous.
    + apply test_value_continuous.
Qed.

Lemma native_integrand_continuous : forall eta k i,
  ClosedContinuous (native_integrand eta k i) a b.
Proof.
  intros eta k i. unfold native_integrand. apply continuous_plus.
  - apply wb_continuous_opp. apply wb_continuous_product.
    + apply HU.
    + apply test_derivative_continuous.
  - apply continuous_scale. apply wb_continuous_product.
    + apply HU.
    + apply test_value_continuous.
Qed.

Theorem WB10_NATIVE_INTEGRAND_IS_ENCODED_LINEAR_INTEGRAND :
  forall eta k i t, a <= t <= b ->
  native_integrand eta k i t = psi k i * physical_integrand eta i t.
Proof.
  intros eta k i t Ht.
  pose proof (Hadjacent t Ht k i) as Hnext.
  unfold native_integrand, physical_integrand.
  replace (nu * (lambda i * ell k) *
    (U t (S k) i * test_value a b eta t))
    with (nu * lambda i * (ell k * U t (S k) i) *
      test_value a b eta t) by ring.
  rewrite <- Hnext. rewrite (path_factorization t Ht k i). ring.
Qed.

Definition physical_linear (eta : C1ZeroEndpointTest a b) (i : nat) : R :=
  integral a b Hab (physical_integrand eta i)
    (physical_integrand_continuous eta i).

Definition native_linear (eta : C1ZeroEndpointTest a b) (k i : nat) : R :=
  integral a b Hab (native_integrand eta k i)
    (native_integrand_continuous eta k i).

Theorem WB20_ACTUAL_RIEMANN_LINEAR_BALANCE_TRANSPORT : forall eta k i,
  native_linear eta k i = psi k i * physical_linear eta i.
Proof.
  intros eta k i. unfold native_linear, physical_linear.
  pose proof (continuous_scale a b (psi k i) (physical_integrand eta i)
    (physical_integrand_continuous eta i)) as Hscaled.
  transitivity (integral a b Hab
    (fun t => psi k i * physical_integrand eta i t) Hscaled).
  - apply integral_ext. intros t Ht.
    apply WB10_NATIVE_INTEGRAND_IS_ENCODED_LINEAR_INTEGRAND. exact Ht.
  - apply integral_scale.
Qed.

(* F can be a previously realized distributional source, but this theorem
   needs only its scalar test readouts. The same F is used on both sides:
   the native source is exactly psi(k,i) * F(i,eta). *)
Variable F : nat -> C1ZeroEndpointTest a b -> R.

Definition physical_residual (eta : C1ZeroEndpointTest a b) (i : nat) : R :=
  physical_linear eta i - F i eta.

Definition native_residual (eta : C1ZeroEndpointTest a b) (k i : nat) : R :=
  native_linear eta k i - psi k i * F i eta.

Theorem WB30_EXACT_RESIDUAL_TRANSPORT : forall eta k i,
  native_residual eta k i = psi k i * physical_residual eta i.
Proof.
  intros eta k i. unfold native_residual, physical_residual.
  rewrite WB20_ACTUAL_RIEMANN_LINEAR_BALANCE_TRANSPORT. ring.
Qed.

Definition CoordinateWeakBalance : Prop :=
  forall eta i, physical_residual eta i = 0.

Definition NativeBlockWeakBalance : Prop :=
  forall eta k i, native_residual eta k i = 0.

Theorem WB40_EXACT_WEAK_LINEAR_BALANCE_CLASSIFICATION :
  CoordinateWeakBalance <-> NativeBlockWeakBalance.
Proof.
  split.
  - intros H eta k i. rewrite WB30_EXACT_RESIDUAL_TRANSPORT.
    rewrite (H eta i). ring.
  - intros H eta i. pose proof (H eta 0%nat i) as Hzero_residual.
    rewrite WB30_EXACT_RESIDUAL_TRANSPORT in Hzero_residual.
    apply (Rmult_eq_reg_l (psi 0%nat i)).
    + rewrite Rmult_0_r. exact Hzero_residual.
    + apply Hzero.
Qed.
End CompatiblePath.

Check WB20_ACTUAL_RIEMANN_LINEAR_BALANCE_TRANSPORT.
Check WB40_EXACT_WEAK_LINEAR_BALANCE_CLASSIFICATION.
Print Assumptions WB20_ACTUAL_RIEMANN_LINEAR_BALANCE_TRANSPORT.
Print Assumptions WB30_EXACT_RESIDUAL_TRANSPORT.
Print Assumptions WB40_EXACT_WEAK_LINEAR_BALANCE_CLASSIFICATION.
End BKQR_WEAK_BALANCE.
