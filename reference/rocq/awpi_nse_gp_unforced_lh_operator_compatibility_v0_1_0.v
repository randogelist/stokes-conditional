From Stdlib Require Import Reals String.
Require Import awpi_nse_leray_weak_test_specialization_v0_42_1.
Require Import awpi_nse_gp_unforced_operator_class_v0_1_0.
Require Import awpi_nse_gp_signed_source_closure_v0_51_0.
Require Import awpi_nse_gp_source_m7_energy_join_v0_51_0.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.
Module LH := NSE_LERAY_WEAK_TEST_SPECIALIZATION.
Module UFC := NSE_GP_UNFORCED_OPERATOR_CLASS.
Module SSC := NSE_GP_SIGNED_SOURCE_CLOSURE.
Module Join := NSE_GP_SOURCE_M7_ENERGY_JOIN.
Module Spine := NSE_GP_TO_M7_SPINE.
Module Energy := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* 1. The unforced Leray-Hopf weak momentum operator already commutes  *)
(*    with every admissible fixed GP coordinate/test realization.      *)
(*                                                                    *)
(* The inherited record is abstract at this point: no concrete Fourier *)
(* realization is needed below.  It only supplies an admissible weak   *)
(* test together with exact identifications of dt, Stokes, and the     *)
(* nonlinear source in that coordinate.                               *)
(* ------------------------------------------------------------------ *)

Definition GPWeakCoordinate
  (W : LH.WeakTestCalculus) (lambda : R) : Type :=
  LH.HelicalWeakMode W lambda.

Definition GPWeakCoordinateEquation
  (W : LH.WeakTestCalculus) (nu lambda : R)
  (G : GPWeakCoordinate W lambda) : Prop :=
  LH.FixedModeDistributionalEquation W nu lambda G.

Theorem ULH00_UNFORCED_LH_WEAK_OPERATOR_COMMUTES_WITH_GP_COORDINATE :
  forall W : LH.WeakTestCalculus,
  forall nu lambda : R,
  forall H : LH.LerayHopfWeakMomentum W nu,
  forall G : GPWeakCoordinate W lambda,
    GPWeakCoordinateEquation W nu lambda G.
Proof.
  intros W nu lambda H G.
  exact (LH.LH42_00_STANDARD_WEAK_MOMENTUM_SPECIALIZES_TO_HELICAL_MODE
    W nu lambda H G).
Qed.

Definition GPWeakTriad
  (W : LH.WeakTestCalculus) (lk lp lq : R) : Type :=
  LH.HelicalWeakTriad W lk lp lq.

Definition GPWeakTriadEquations
  (W : LH.WeakTestCalculus) (nu lk lp lq : R)
  (T : GPWeakTriad W lk lp lq) : Prop :=
  LH.TriadDistributionalEquations W nu lk lp lq T.

Theorem ULH01_UNFORCED_LH_WEAK_OPERATOR_COMMUTES_WITH_GP_TRIAD :
  forall W : LH.WeakTestCalculus,
  forall nu lk lp lq : R,
  forall H : LH.LerayHopfWeakMomentum W nu,
  forall T : GPWeakTriad W lk lp lq,
    GPWeakTriadEquations W nu lk lp lq T.
Proof.
  intros W nu lk lp lq H T.
  exact (LH.LH42_10_STANDARD_LH_WEAK_MOMENTUM_GIVES_TRIAD_DISTRIBUTIONAL_EQUATIONS
    W nu lk lp lq H T).
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The exact GP source witness used by the M7 ledger is an f=0 path *)
(*    and the external GP injection is identically zero.               *)
(* ------------------------------------------------------------------ *)

Theorem ULH10_EXACT_GP_SOURCE_WITNESS_IS_UNFORCED_CLOSED :
  forall D : SSC.GPSourceData51,
    SSC.GPSourceWitness51 D -> UFC.UnforcedGPClosed51 D.
Proof.
  intros D HW.
  exact (UFC.UFC30_EXISTING_GP_WITNESS_IS_UNFORCED_CLOSED D HW).
Qed.

Theorem ULH11_ZERO_FORCE_HAS_ZERO_GP_BKQR_INJECTION :
  forall D : SSC.GPSourceData51,
  forall t : R,
    UFC.combined_forcing_rate51
      (SSC.g51_packets D) (SSC.g51_nu D) (SSC.g51_Z D)
      (UFC.zero_forcing51 t) (SSC.g51_u D t) = 0.
Proof.
  intros D t.
  exact (UFC.UFC24_ZERO_COMBINED_FORCING_RATE
    (SSC.g51_packets D) (SSC.g51_nu D) (SSC.g51_Z D) (SSC.g51_u D t)).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Once an exact unforced GP source witness has been realized, the  *)
(*    only remaining premise in this layer is the INTERNAL signed      *)
(*    production/payment bound.  No forcing hypothesis survives.      *)
(* ------------------------------------------------------------------ *)

Theorem ULH20_UNFORCED_GP_SOURCE_PLUS_INTERNAL_PAYMENT_GIVES_CRITICAL_REGULARITY :
  forall D : SSC.GPSourceData51,
  forall theta Qstar : R,
    SSC.GPSourceWitness51 D ->
    0 <= theta -> theta < 1 -> 0 <= Qstar ->
    SSC.SignedProductionBudget51 D theta Qstar ->
    Energy.UniformCriticalEnergy (Join.TimePoint51 D)
      (fun t => SSC.g_mass D (proj1_sig t))
      (fun t => SSC.g51_Dcum D (proj1_sig t)).
Proof.
  intros D theta Qstar HW Hth0 Hth1 HQ HB.
  apply (UFC.UFC40_UNFORCED_CERTIFICATE_GIVES_CONTINUOUS_CRITICAL_BOUND
    D theta Qstar).
  unfold UFC.UnforcedM7RegularityCertificate51.
  split.
  - exact (UFC.UFC30_EXISTING_GP_WITNESS_IS_UNFORCED_CLOSED D HW).
  - split; [exact Hth0|].
    split; [exact Hth1|].
    split; [exact HQ|exact HB].
Qed.

Theorem ULH21_UNFORCED_GP_SOURCE_PLUS_INTERNAL_PAYMENT_GIVES_M7_GRID_TARGET :
  forall D : SSC.GPSourceData51,
  forall theta Qstar : R,
  forall grid : nat -> R,
    SSC.GPSourceWitness51 D ->
    0 <= theta -> theta < 1 -> 0 <= Qstar ->
    SSC.SignedProductionBudget51 D theta Qstar ->
    Join.SourceGrid51 D grid ->
    Spine.GPSequenceM7 (Join.source_cell51 D grid) /\
    Energy.CriticalH12Bound nat (fun n => SSC.g_mass D (grid n)) /\
    Energy.CriticalH32Dissipation nat (fun n => SSC.g51_Dcum D (grid n)).
Proof.
  intros D theta Qstar grid HW Hth0 Hth1 HQ HB HG.
  apply (UFC.UFC41_UNFORCED_CERTIFICATE_GIVES_GRID_M7_AND_CRITICAL_TARGET
    D theta Qstar grid).
  - unfold UFC.UnforcedM7RegularityCertificate51.
    split.
    + exact (UFC.UFC30_EXISTING_GP_WITNESS_IS_UNFORCED_CLOSED D HW).
    + split; [exact Hth0|].
      split; [exact Hth1|].
      split; [exact HQ|exact HB].
  - exact HG.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Exact claim boundary.                                             *)
(*                                                                    *)
(* Weak LH -> transformed distributional GP equation is proved above.  *)
(* GPSourceWitness -> f=0 closed source -> M7/critical target is proved *)
(* above, conditional only on internal SignedProductionBudget51.       *)
(* What is NOT proved here is the infinite-dimensional analytic entrance *)
(* identifying every weak LH trajectory with a GPSourceWitness51.      *)
(* The older LH layer already isolates its first standard analytic seam *)
(* as ScalarDistributionToAEModalFrontier.                              *)
(* ------------------------------------------------------------------ *)

Definition LHWeakToExactGPSourceWitnessFrontier : Prop := True.
Definition InternalSignedProductionFrontier : Prop := True.

Definition STATUS : string :=
  "NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY_V0_1_0_WEAK_GP_COMMUTATION_KERNEL_DERIVED_ZERO_FORCE_GP_CLOSED_KERNEL_DERIVED_M7_CRITICAL_TARGET_CONDITIONAL_ON_INTERNAL_PAYMENT_NO_ADMITTED"%string.

End NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.

Check NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH00_UNFORCED_LH_WEAK_OPERATOR_COMMUTES_WITH_GP_COORDINATE.
Check NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH01_UNFORCED_LH_WEAK_OPERATOR_COMMUTES_WITH_GP_TRIAD.
Check NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH10_EXACT_GP_SOURCE_WITNESS_IS_UNFORCED_CLOSED.
Check NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH11_ZERO_FORCE_HAS_ZERO_GP_BKQR_INJECTION.
Check NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH20_UNFORCED_GP_SOURCE_PLUS_INTERNAL_PAYMENT_GIVES_CRITICAL_REGULARITY.
Check NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH21_UNFORCED_GP_SOURCE_PLUS_INTERNAL_PAYMENT_GIVES_M7_GRID_TARGET.

Print Assumptions NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH00_UNFORCED_LH_WEAK_OPERATOR_COMMUTES_WITH_GP_COORDINATE.
Print Assumptions NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH01_UNFORCED_LH_WEAK_OPERATOR_COMMUTES_WITH_GP_TRIAD.
Print Assumptions NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH10_EXACT_GP_SOURCE_WITNESS_IS_UNFORCED_CLOSED.
Print Assumptions NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH11_ZERO_FORCE_HAS_ZERO_GP_BKQR_INJECTION.
Print Assumptions NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH20_UNFORCED_GP_SOURCE_PLUS_INTERNAL_PAYMENT_GIVES_CRITICAL_REGULARITY.
Print Assumptions NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.ULH21_UNFORCED_GP_SOURCE_PLUS_INTERNAL_PAYMENT_GIVES_M7_GRID_TARGET.
