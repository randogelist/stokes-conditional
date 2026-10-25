
From Stdlib Require Import Reals Lra Psatz Lists.List ZArith Lia.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_leray_weak_test_specialization_v0_42_1.

Import ListNotations.
Open Scope R_scope.

Module NSE_LH_TORUS_FOURIER_TESTS.

Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module L42 := NSE_LERAY_WEAK_TEST_SPECIALIZATION.

(* ===================================================================== *)
(* Concrete Fourier lattice geometry on T^3                               *)
(* ===================================================================== *)

Record Z3 : Type := {
  kx : Z;
  ky : Z;
  kz : Z
}.

Definition z3_zero : Z3 :=
  {| kx := 0; ky := 0; kz := 0 |}.

Definition z3_add (a b : Z3) : Z3 :=
  {|
    kx := (kx a + kx b)%Z;
    ky := (ky a + ky b)%Z;
    kz := (kz a + kz b)%Z
  |}.

Definition z3_norm2_Z (k : Z3) : Z :=
  (kx k * kx k + ky k * ky k + kz k * kz k)%Z.

Definition stokes_symbol (k : Z3) : R :=
  IZR (z3_norm2_Z k).

Definition triad_support (k p q : Z3) : Prop :=
  k = z3_add p q.

Theorem LH44_00_Z3_NORM2_NONNEG :
  forall k : Z3,
    (0 <= z3_norm2_Z k)%Z.
Proof.
  intros [x y z].
  unfold z3_norm2_Z.
  simpl.
  nia.
Qed.

Theorem LH44_01_STOKES_SYMBOL_NONNEG :
  forall k : Z3,
    0 <= stokes_symbol k.
Proof.
  intro k.
  unfold stokes_symbol.
  change (IZR 0 <= IZR (z3_norm2_Z k)).
  apply IZR_le.
  exact (LH44_00_Z3_NORM2_NONNEG k).
Qed.

Theorem LH44_02_TRIAD_SUPPORT_COMPONENTS :
  forall k p q : Z3,
    triad_support k p q ->
    (kx k = (kx p + kx q)%Z) /\
    (ky k = (ky p + ky q)%Z) /\
    (kz k = (kz p + kz q)%Z).
Proof.
  intros k p q H.
  unfold triad_support, z3_add in H.
  subst k.
  simpl.
  repeat split; reflexivity.
Qed.

Theorem LH44_03_TRIAD_SUPPORT_COMMUTES :
  forall k p q : Z3,
    triad_support k p q ->
    triad_support k q p.
Proof.
  intros [kx0 ky0 kz0] [px py pz] [qx qy qz] H.
  unfold triad_support, z3_add in H |- *.
  simpl in H |- *.
  inversion H.
  f_equal; lia.
Qed.

(* ===================================================================== *)
(* Two generic C^2 sign identities used to canonically define N.          *)
(* ===================================================================== *)

Theorem LH44_10_CSCALE_MINUS_ONE_INVOLUTIVE :
  forall z : CH.C2,
    CH.cscale (-1) (CH.cscale (-1) z) = z.
Proof.
  intros [zr zi].
  unfold CH.cscale.
  simpl.
  f_equal; ring.
Qed.

(* ===================================================================== *)
(* The genuinely Fourier-specific test information for one lattice mode. *)
(*                                                                         *)
(* Compare v0.42.1 HelicalWeakMode:                                       *)
(*   - dU is NOT supplied here; it is the weak_dt_term by definition.     *)
(*   - N  is NOT supplied here; it is minus weak_nonlinear_term.          *)
(*   - their identification laws therefore become theorems.               *)
(*                                                                         *)
(* Remaining Fourier content is exactly:                                  *)
(*   phi_k is an admissible divergence-free test,                         *)
(*   U_k is its modal coefficient distribution,                           *)
(*   phi_k is a Stokes eigen-test with eigenvalue |k|^2.                  *)
(* ===================================================================== *)

Record TorusFourierWeakTest
  (W : L42.WeakTestCalculus)
  (k : Z3) : Type := {
  tfwt_phi : L42.space_test W;

  tfwt_phi_admissible :
    L42.space_admissible W tfwt_phi;

  tfwt_U :
    L42.time_test W -> CH.C2;

  tfwt_stokes_eigen :
    forall eta : L42.time_test W,
      L42.time_admissible W eta ->
      L42.weak_stokes_term W tfwt_phi eta
      =
      CH.cscale (stokes_symbol k) (tfwt_U eta)
}.

Definition torus_weak_dU
  {W : L42.WeakTestCalculus}
  {k : Z3}
  (M : TorusFourierWeakTest W k)
  (eta : L42.time_test W) : CH.C2 :=
  L42.weak_dt_term W
    (tfwt_phi W k M) eta.

Definition torus_weak_N
  {W : L42.WeakTestCalculus}
  {k : Z3}
  (M : TorusFourierWeakTest W k)
  (eta : L42.time_test W) : CH.C2 :=
  CH.cscale (-1)
    (L42.weak_nonlinear_term W
      (tfwt_phi W k M) eta).

Theorem LH44_11_CANONICAL_NONLINEAR_SOURCE_IDENTIFICATION :
  forall W : L42.WeakTestCalculus,
  forall k : Z3,
  forall M : TorusFourierWeakTest W k,
  forall eta : L42.time_test W,
    L42.weak_nonlinear_term W
      (tfwt_phi W k M) eta
    =
    CH.cscale (-1)
      (torus_weak_N M eta).
Proof.
  intros W k M eta.
  unfold torus_weak_N.
  symmetry.
  apply LH44_10_CSCALE_MINUS_ONE_INVOLUTIVE.
Qed.

Definition build_helical_weak_mode
  {W : L42.WeakTestCalculus}
  {k : Z3}
  (M : TorusFourierWeakTest W k)
  : L42.HelicalWeakMode W (stokes_symbol k) :=
  {|
    L42.hwm_phi := tfwt_phi W k M;

    L42.hwm_phi_admissible :=
      tfwt_phi_admissible W k M;

    L42.hwm_U := tfwt_U W k M;

    L42.hwm_dU := torus_weak_dU M;

    L42.hwm_N := torus_weak_N M;

    L42.hwm_dt_identification :=
      fun eta _ => eq_refl;

    L42.hwm_stokes_eigen_test :=
      tfwt_stokes_eigen W k M;

    L42.hwm_nonlinear_source :=
      fun eta _ =>
        LH44_11_CANONICAL_NONLINEAR_SOURCE_IDENTIFICATION
          W k M eta
  |}.

Theorem LH44_12_TORUS_TEST_BUILDS_HELICAL_WEAK_MODE :
  forall W : L42.WeakTestCalculus,
  forall k : Z3,
  forall M : TorusFourierWeakTest W k,
    exists H : L42.HelicalWeakMode W (stokes_symbol k),
      L42.hwm_U W (stokes_symbol k) H
      =
      tfwt_U W k M.
Proof.
  intros.
  exists (build_helical_weak_mode M).
  reflexivity.
Qed.

(* Universal LH weak momentum now specializes to the ACTUAL lattice symbol
   |k|^2, with dU and N constructed rather than supplied. *)
Theorem LH44_20_LH_WEAK_MOMENTUM_GIVES_TORUS_MODE_DISTRIBUTIONAL_EQUATION :
  forall W : L42.WeakTestCalculus,
  forall nu : R,
  forall H : L42.LerayHopfWeakMomentum W nu,
  forall k : Z3,
  forall M : TorusFourierWeakTest W k,
    L42.FixedModeDistributionalEquation
      W nu (stokes_symbol k)
      (build_helical_weak_mode M).
Proof.
  intros.
  exact
    (L42.LH42_00_STANDARD_WEAK_MOMENTUM_SPECIALIZES_TO_HELICAL_MODE
      W nu (stokes_symbol k) H
      (build_helical_weak_mode M)).
Qed.

(* ===================================================================== *)
(* A genuine lattice triad p+q=k                                          *)
(* ===================================================================== *)

Record TorusFourierWeakTriad
  (W : L42.WeakTestCalculus)
  (k p q : Z3) : Type := {
  tfwtri_support :
    triad_support k p q;

  tfwtri_k :
    TorusFourierWeakTest W k;

  tfwtri_p :
    TorusFourierWeakTest W p;

  tfwtri_q :
    TorusFourierWeakTest W q
}.

Definition build_helical_weak_triad
  {W : L42.WeakTestCalculus}
  {k p q : Z3}
  (T : TorusFourierWeakTriad W k p q)
  : L42.HelicalWeakTriad
      W
      (stokes_symbol k)
      (stokes_symbol p)
      (stokes_symbol q) :=
  {|
    L42.hwt_k :=
      build_helical_weak_mode
        (tfwtri_k W k p q T);

    L42.hwt_p :=
      build_helical_weak_mode
        (tfwtri_p W k p q T);

    L42.hwt_q :=
      build_helical_weak_mode
        (tfwtri_q W k p q T)
  |}.

Theorem LH44_21_LH_WEAK_MOMENTUM_GIVES_ACTUAL_LATTICE_TRIAD_EQUATIONS :
  forall W : L42.WeakTestCalculus,
  forall nu : R,
  forall H : L42.LerayHopfWeakMomentum W nu,
  forall k p q : Z3,
  forall T : TorusFourierWeakTriad W k p q,
    L42.TriadDistributionalEquations
      W nu
      (stokes_symbol k)
      (stokes_symbol p)
      (stokes_symbol q)
      (build_helical_weak_triad T).
Proof.
  intros.
  exact
    (L42.LH42_10_STANDARD_LH_WEAK_MOMENTUM_GIVES_TRIAD_DISTRIBUTIONAL_EQUATIONS
      W nu
      (stokes_symbol k)
      (stokes_symbol p)
      (stokes_symbol q)
      H
      (build_helical_weak_triad T)).
Qed.

Theorem LH44_22_ACTUAL_TRIAD_CARRIES_INTEGER_SUPPORT :
  forall W : L42.WeakTestCalculus,
  forall k p q : Z3,
  forall T : TorusFourierWeakTriad W k p q,
    k = z3_add p q.
Proof.
  intros.
  exact (tfwtri_support W k p q T).
Qed.

(* ===================================================================== *)
(* Leray-Hopf energy ledger: derive the standard inequalities once.       *)
(* This is the other classical part of the LH entrance.                    *)
(* ===================================================================== *)

Record LerayHopfEnergyCore
  (nu : R) : Type := {
  lhe_nu_positive :
    0 < nu;

  lhe_E0 : R;

  lhe_energy : R -> R;

  lhe_cumulative_dissipation : R -> R;

  lhe_E0_nonnegative :
    0 <= lhe_E0;

  lhe_energy_nonnegative :
    forall t : R,
      0 <= lhe_energy t;

  lhe_cumulative_nonnegative :
    forall t : R,
      0 <= lhe_cumulative_dissipation t;

  (* Standard unforced Leray-Hopf energy inequality. *)
  lhe_energy_inequality :
    forall t : R,
      lhe_energy t
      + 2 * nu * lhe_cumulative_dissipation t
      <=
      lhe_E0
}.

Theorem LH44_30_LERAY_ENERGY_IS_BOUNDED_BY_INITIAL_ENERGY :
  forall nu : R,
  forall H : LerayHopfEnergyCore nu,
  forall t : R,
    lhe_energy nu H t <= lhe_E0 nu H.
Proof.
  intros nu H t.
  pose proof (lhe_energy_inequality nu H t) as Hineq.
  pose proof (lhe_cumulative_nonnegative nu H t) as HC.
  pose proof (lhe_nu_positive nu H) as Hnu.
  nra.
Qed.

Theorem LH44_31_LERAY_DISSIPATION_LEDGER :
  forall nu : R,
  forall H : LerayHopfEnergyCore nu,
  forall t : R,
    2 * nu * lhe_cumulative_dissipation nu H t
    <=
    lhe_E0 nu H.
Proof.
  intros nu H t.
  pose proof (lhe_energy_inequality nu H t) as Hineq.
  pose proof (lhe_energy_nonnegative nu H t) as HE.
  nra.
Qed.

Theorem LH44_32_LERAY_CUMULATIVE_DISSIPATION_NONNEG :
  forall nu : R,
  forall H : LerayHopfEnergyCore nu,
  forall t : R,
    0 <= lhe_cumulative_dissipation nu H t.
Proof.
  intros.
  exact (lhe_cumulative_nonnegative nu H t).
Qed.

(* ===================================================================== *)
(* Current exact Branch-A frontier                                        *)
(* ===================================================================== *)

(* What this file has now constructed from the LH weak identity:
     - concrete integer lattice Z^3;
     - concrete Stokes symbol |k|^2 and its nonnegativity;
     - exact triad support k=p+q;
     - canonical dU from the weak time term;
     - canonical N from the weak nonlinear term;
     - fixed-mode and triad distributional NSE equations;
     - the classical LH energy/dissipation ledger.

   What remains genuinely analytic before the existing v0.33.2 frontend can
   be fully discharged:
     (1) construct tfwt_U as the actual torus Fourier coefficient pairing;
     (2) prove the Fourier exponential/helical test is admissible and is a
         Stokes eigen-test;
     (3) identify the nonlinear projection with the actual convolution sum;
     (4) Parseval/Plancherel and finite Galerkin projection convergence.

   No new AWPI packet/GP/M7 hypothesis is introduced here. *)

Definition RemainingConcreteTorusFourierAnalysisFrontier : Prop := True.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_LH_TORUS_FOURIER_TESTS.

Check NSE_LH_TORUS_FOURIER_TESTS.Z3.
Check NSE_LH_TORUS_FOURIER_TESTS.z3_norm2_Z.
Check NSE_LH_TORUS_FOURIER_TESTS.stokes_symbol.
Check NSE_LH_TORUS_FOURIER_TESTS.LH44_00_Z3_NORM2_NONNEG.
Check NSE_LH_TORUS_FOURIER_TESTS.LH44_01_STOKES_SYMBOL_NONNEG.
Check NSE_LH_TORUS_FOURIER_TESTS.triad_support.
Check NSE_LH_TORUS_FOURIER_TESTS.LH44_02_TRIAD_SUPPORT_COMPONENTS.
Check NSE_LH_TORUS_FOURIER_TESTS.LH44_03_TRIAD_SUPPORT_COMMUTES.
Check NSE_LH_TORUS_FOURIER_TESTS.TorusFourierWeakTest.
Check NSE_LH_TORUS_FOURIER_TESTS.torus_weak_dU.
Check NSE_LH_TORUS_FOURIER_TESTS.torus_weak_N.
Check NSE_LH_TORUS_FOURIER_TESTS.build_helical_weak_mode.
Check NSE_LH_TORUS_FOURIER_TESTS.LH44_20_LH_WEAK_MOMENTUM_GIVES_TORUS_MODE_DISTRIBUTIONAL_EQUATION.
Check NSE_LH_TORUS_FOURIER_TESTS.TorusFourierWeakTriad.
Check NSE_LH_TORUS_FOURIER_TESTS.LH44_21_LH_WEAK_MOMENTUM_GIVES_ACTUAL_LATTICE_TRIAD_EQUATIONS.
Check NSE_LH_TORUS_FOURIER_TESTS.LH44_22_ACTUAL_TRIAD_CARRIES_INTEGER_SUPPORT.
Check NSE_LH_TORUS_FOURIER_TESTS.LerayHopfEnergyCore.
Check NSE_LH_TORUS_FOURIER_TESTS.LH44_30_LERAY_ENERGY_IS_BOUNDED_BY_INITIAL_ENERGY.
Check NSE_LH_TORUS_FOURIER_TESTS.LH44_31_LERAY_DISSIPATION_LEDGER.
Check NSE_LH_TORUS_FOURIER_TESTS.LH44_32_LERAY_CUMULATIVE_DISSIPATION_NONNEG.
Check NSE_LH_TORUS_FOURIER_TESTS.RemainingConcreteTorusFourierAnalysisFrontier.
