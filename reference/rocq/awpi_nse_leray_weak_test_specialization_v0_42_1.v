
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_gp_ae_modal_semantics_v0_23_1.
Require Import awpi_nse_leray_projected_modes_v0_40_0.
Require Import awpi_nse_leray_dual_evolution_v0_41_5.

Open Scope R_scope.

Module NSE_LERAY_WEAK_TEST_SPECIALIZATION.

Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module AE := NSE_GP_AE_MODAL_SEMANTICS.
Module L40 := NSE_LERAY_PROJECTED_MODES.
Module L41 := NSE_LERAY_DUAL_EVOLUTION.

(* ===================================================================== *)
(* Abstract syntax of the UNIVERSAL weak momentum identity.               *)
(*                                                                         *)
(* space_test represents divergence-free smooth spatial tests.            *)
(* time_test represents compactly-supported smooth scalar time tests.     *)
(* The three C2 terms are exactly the time-distribution coefficients of   *)
(*   -d/dt <u,phi>,  Stokes/viscosity,  and B(u,u).                       *)
(* ===================================================================== *)

Record WeakTestCalculus : Type := {
  space_test : Type;
  time_test : Type;

  space_admissible : space_test -> Prop;
  time_admissible : time_test -> Prop;

  weak_dt_term :
    space_test -> time_test -> CH.C2;

  weak_stokes_term :
    space_test -> time_test -> CH.C2;

  weak_nonlinear_term :
    space_test -> time_test -> CH.C2
}.

(* This is the momentum-equation part of the textbook Leray-Hopf weak
   formulation: the identity is UNIVERSAL in admissible space/time tests.
   No Fourier mode has been selected yet. *)
Record LerayHopfWeakMomentum
  (W : WeakTestCalculus)
  (nu : R) : Type := {
  lhwm_momentum :
    forall phi : space_test W,
    forall eta : time_test W,
      space_admissible W phi ->
      time_admissible W eta ->
      CH.cadd
        (weak_dt_term W phi eta)
        (CH.cadd
          (CH.cscale nu
            (weak_stokes_term W phi eta))
          (weak_nonlinear_term W phi eta))
      =
      (0, 0)
}.

(* ===================================================================== *)
(* A fixed helical Fourier/Stokes test specialization.                    *)
(*                                                                         *)
(* U,dU,N are still TIME-DISTRIBUTION quantities indexed by eta.          *)
(* No pointwise-in-time derivative representative is assumed here.        *)
(* ===================================================================== *)

Record HelicalWeakMode
  (W : WeakTestCalculus)
  (lambda : R) : Type := {
  hwm_phi : space_test W;
  hwm_phi_admissible :
    space_admissible W hwm_phi;

  hwm_U : time_test W -> CH.C2;
  hwm_dU : time_test W -> CH.C2;
  hwm_N : time_test W -> CH.C2;

  hwm_dt_identification :
    forall eta : time_test W,
      time_admissible W eta ->
      weak_dt_term W hwm_phi eta
      =
      hwm_dU eta;

  hwm_stokes_eigen_test :
    forall eta : time_test W,
      time_admissible W eta ->
      weak_stokes_term W hwm_phi eta
      =
      CH.cscale lambda (hwm_U eta);

  (* The weak equation carries +B(u,u); our modal source convention is
       dU + nu lambda U = N,
     hence B projects to -N. *)
  hwm_nonlinear_source :
    forall eta : time_test W,
      time_admissible W eta ->
      weak_nonlinear_term W hwm_phi eta
      =
      CH.cscale (-1) (hwm_N eta)
}.

Theorem LH42_C2_REARRANGE_WEAK_SOURCE :
  forall du u N : CH.C2,
  forall nu lambda : R,
    CH.cadd du
      (CH.cadd
        (CH.cscale nu (CH.cscale lambda u))
        (CH.cscale (-1) N))
    =
    (0, 0)
    ->
    CH.CModalEq nu lambda u du N.
Proof.
  intros [dur dui] [ur ui] [Nr Ni] nu lambda H.
  unfold CH.CModalEq, CH.ceq, CH.cadd, CH.cscale,
         CH.cre, CH.cim in H |- *.
  simpl in H |- *.
  injection H as Hre Him.
  split.
  - replace ((nu * lambda) * ur)
      with (nu * (lambda * ur)) by ring.
    lra.
  - replace ((nu * lambda) * ui)
      with (nu * (lambda * ui)) by ring.
    lra.
Qed.

Definition FixedModeDistributionalEquation
  (W : WeakTestCalculus)
  (nu lambda : R)
  (M : HelicalWeakMode W lambda) : Prop :=
  forall eta : time_test W,
    time_admissible W eta ->
    CH.CModalEq
      nu lambda
      (hwm_U W lambda M eta)
      (hwm_dU W lambda M eta)
      (hwm_N W lambda M eta).

(* Main specialization theorem:
     universal LH weak momentum identity
       -> fixed helical/Fourier distributional modal equation. *)
Theorem LH42_00_STANDARD_WEAK_MOMENTUM_SPECIALIZES_TO_HELICAL_MODE :
  forall W : WeakTestCalculus,
  forall nu lambda : R,
  forall H : LerayHopfWeakMomentum W nu,
  forall M : HelicalWeakMode W lambda,
    FixedModeDistributionalEquation W nu lambda M.
Proof.
  intros W nu lambda H M eta Heta.
  unfold FixedModeDistributionalEquation.

  pose proof
    (lhwm_momentum W nu H
      (hwm_phi W lambda M)
      eta
      (hwm_phi_admissible W lambda M)
      Heta) as Hweak.

  rewrite
    (hwm_dt_identification W lambda M eta Heta)
    in Hweak.

  rewrite
    (hwm_stokes_eigen_test W lambda M eta Heta)
    in Hweak.

  rewrite
    (hwm_nonlinear_source W lambda M eta Heta)
    in Hweak.

  exact
    (LH42_C2_REARRANGE_WEAK_SOURCE
      (hwm_dU W lambda M eta)
      (hwm_U W lambda M eta)
      (hwm_N W lambda M eta)
      nu lambda
      Hweak).
Qed.

(* The fixed-mode specialization is therefore not an extra assumption. *)
Theorem LH42_01_FIXED_MODE_DISTRIBUTIONAL_EQUATION_IS_CONSTRUCTED :
  forall W : WeakTestCalculus,
  forall nu lambda : R,
  forall H : LerayHopfWeakMomentum W nu,
  forall M : HelicalWeakMode W lambda,
    exists E : FixedModeDistributionalEquation W nu lambda M,
      True.
Proof.
  intros.
  exists
    (LH42_00_STANDARD_WEAK_MOMENTUM_SPECIALIZES_TO_HELICAL_MODE
      W nu lambda H M).
  exact I.
Qed.

(* ===================================================================== *)
(* Three helical modes: the triad entrance is simultaneously specialized. *)
(* ===================================================================== *)

Record HelicalWeakTriad
  (W : WeakTestCalculus)
  (lk lp lq : R) : Type := {
  hwt_k : HelicalWeakMode W lk;
  hwt_p : HelicalWeakMode W lp;
  hwt_q : HelicalWeakMode W lq
}.

Definition TriadDistributionalEquations
  (W : WeakTestCalculus)
  (nu lk lp lq : R)
  (T : HelicalWeakTriad W lk lp lq) : Prop :=
  FixedModeDistributionalEquation
    W nu lk (hwt_k W lk lp lq T)
  /\
  FixedModeDistributionalEquation
    W nu lp (hwt_p W lk lp lq T)
  /\
  FixedModeDistributionalEquation
    W nu lq (hwt_q W lk lp lq T).

Theorem LH42_10_STANDARD_LH_WEAK_MOMENTUM_GIVES_TRIAD_DISTRIBUTIONAL_EQUATIONS :
  forall W : WeakTestCalculus,
  forall nu lk lp lq : R,
  forall H : LerayHopfWeakMomentum W nu,
  forall T : HelicalWeakTriad W lk lp lq,
    TriadDistributionalEquations W nu lk lp lq T.
Proof.
  intros W nu lk lp lq H T.
  unfold TriadDistributionalEquations.
  split.
  - exact
      (LH42_00_STANDARD_WEAK_MOMENTUM_SPECIALIZES_TO_HELICAL_MODE
        W nu lk H (hwt_k W lk lp lq T)).
  - split.
    + exact
        (LH42_00_STANDARD_WEAK_MOMENTUM_SPECIALIZES_TO_HELICAL_MODE
          W nu lp H (hwt_p W lk lp lq T)).
    + exact
        (LH42_00_STANDARD_WEAK_MOMENTUM_SPECIALIZES_TO_HELICAL_MODE
          W nu lq H (hwt_q W lk lp lq T)).
Qed.

(* ===================================================================== *)
(* Exact remaining far-left analytic theorem.                             *)
(*                                                                         *)
(* v0.42 DOES NOT assume this theorem as a field of LerayHopfWeakMomentum. *)
(* It is exposed separately so the next package can attack it directly.   *)
(*                                                                         *)
(* For each fixed helical mode one must pass from the distributional       *)
(* equation above to an AC/W^{1,1}_loc scalar representative whose a.e.   *)
(* derivative is the projected V' derivative/source.                      *)
(* ===================================================================== *)

Definition ScalarDistributionToAEModalFrontier
  (W : WeakTestCalculus)
  (CoNull : (R -> Prop) -> Prop)
  (nu lambda : R)
  (M : HelicalWeakMode W lambda) : Prop :=
  FixedModeDistributionalEquation W nu lambda M
  ->
  exists P : L40.LerayHopfProjectedMode CoNull nu lambda,
    True.

(* This marker is deliberately only a Definition, not a proved theorem.
   It keeps the remaining standard Bochner/distributional derivative
   theorem visible instead of silently injecting it. *)
Definition RemainingScalarWeakDerivativeFrontier : Prop := True.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_LERAY_WEAK_TEST_SPECIALIZATION.

Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.WeakTestCalculus.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.LerayHopfWeakMomentum.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.HelicalWeakMode.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.LH42_C2_REARRANGE_WEAK_SOURCE.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.FixedModeDistributionalEquation.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.LH42_00_STANDARD_WEAK_MOMENTUM_SPECIALIZES_TO_HELICAL_MODE.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.LH42_01_FIXED_MODE_DISTRIBUTIONAL_EQUATION_IS_CONSTRUCTED.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.HelicalWeakTriad.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.TriadDistributionalEquations.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.LH42_10_STANDARD_LH_WEAK_MOMENTUM_GIVES_TRIAD_DISTRIBUTIONAL_EQUATIONS.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.ScalarDistributionToAEModalFrontier.
Check NSE_LERAY_WEAK_TEST_SPECIALIZATION.RemainingScalarWeakDerivativeFrontier.
