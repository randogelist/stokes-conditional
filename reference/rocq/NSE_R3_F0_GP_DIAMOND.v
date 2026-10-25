From Stdlib Require Import Reals Lra Psatz String.
Require Import awpi_nse_gp_restart_action_covariance_v0_14_2.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_R3_F0_GP_DIAMOND.

Open Scope R_scope.

Module Cov := NSE_GP_RESTART_ACTION_COVARIANCE.
Module Spine := NSE_GP_TO_M7_SPINE.
Module Energy := NSE_M7_CRITICAL_ENERGY_INJECTION.

(* ------------------------------------------------------------------------- *)
(* Physical carrier marker: time-dependent velocity fields on R^3.            *)
(* No particular trajectory is selected by the Diamond theorem.              *)
(* ------------------------------------------------------------------------- *)

Definition R3 : Type := (R * (R * R))%type.
Definition R3Velocity : Type := R3 -> R3.
Definition R3Trajectory : Type := R -> R3Velocity.

(* ------------------------------------------------------------------------- *)
(* UNIVERSAL OPERATOR DIAMOND                                                 *)
(*                                                                           *)
(* LHForm is the positive/dissipative two-slot object.                       *)
(* NSEForm is the conservative nonlinear three-slot object.                  *)
(* GP transports both to the same representation space.                      *)
(* Cuts expose the otherwise globally cancelling nonlinear transfer.         *)
(* ------------------------------------------------------------------------- *)

Section OPERATOR_DIAMOND.

Context {GPState Cut : Type}.

Variable gp_forward : R3Trajectory -> GPState.
Variable gp_back : GPState -> R3Trajectory.

Hypothesis gp_left_inverse :
  forall u : R3Trajectory, gp_back (gp_forward u) = u.

Hypothesis gp_right_inverse :
  forall U : GPState, gp_forward (gp_back U) = U.

Variable LHForm : R3Trajectory -> R3Trajectory -> R.
Variable NSEForm : R3Trajectory -> R3Trajectory -> R3Trajectory -> R.

Variable physical_cut : Cut -> R3Trajectory -> R3Trajectory.
Variable gp_cut_operator : Cut -> GPState -> GPState.

Hypothesis gp_cut_commutes :
  forall (q : Cut) (u : R3Trajectory),
    gp_cut_operator q (gp_forward u) =
    gp_forward (physical_cut q u).

Definition GP_LHForm (U V : GPState) : R :=
  LHForm (gp_back U) (gp_back V).

Definition GP_NSEForm (U V W : GPState) : R :=
  NSEForm (gp_back U) (gp_back V) (gp_back W).

Definition physical_capacity (q : Cut) (u : R3Trajectory) : R :=
  LHForm u (physical_cut q u).

Definition physical_current (q : Cut) (u : R3Trajectory) : R :=
  NSEForm u u (physical_cut q u).

Definition gp_capacity (q : Cut) (U : GPState) : R :=
  GP_LHForm U (gp_cut_operator q U).

Definition gp_current (q : Cut) (U : GPState) : R :=
  GP_NSEForm U U (gp_cut_operator q U).

Definition physical_action (q : Cut) (u : R3Trajectory) : R :=
  Cov.action (physical_current q u) (physical_capacity q u).

Definition gp_action (q : Cut) (U : GPState) : R :=
  Cov.action (gp_current q U) (gp_capacity q U).

Theorem DIAMOND01_GP_TRANSPORTS_LH_FORM :
  forall u v : R3Trajectory,
    GP_LHForm (gp_forward u) (gp_forward v) = LHForm u v.
Proof.
  intros u v.
  unfold GP_LHForm.
  rewrite (gp_left_inverse u), (gp_left_inverse v).
  reflexivity.
Qed.

Theorem DIAMOND02_GP_TRANSPORTS_NSE_FORM :
  forall u v w : R3Trajectory,
    GP_NSEForm (gp_forward u) (gp_forward v) (gp_forward w) =
    NSEForm u v w.
Proof.
  intros u v w.
  unfold GP_NSEForm.
  rewrite (gp_left_inverse u), (gp_left_inverse v), (gp_left_inverse w).
  reflexivity.
Qed.

Theorem DIAMOND03_GP_TRANSPORTS_LH_CAPACITY :
  forall (q : Cut) (u : R3Trajectory),
    gp_capacity q (gp_forward u) = physical_capacity q u.
Proof.
  intros q u.
  unfold gp_capacity, physical_capacity, GP_LHForm.
  rewrite (gp_left_inverse u).
  rewrite (gp_cut_commutes q u).
  rewrite (gp_left_inverse (physical_cut q u)).
  reflexivity.
Qed.

Theorem DIAMOND04_GP_TRANSPORTS_NSE_CURRENT :
  forall (q : Cut) (u : R3Trajectory),
    gp_current q (gp_forward u) = physical_current q u.
Proof.
  intros q u.
  unfold gp_current, physical_current, GP_NSEForm.
  rewrite (gp_left_inverse u).
  rewrite (gp_cut_commutes q u).
  rewrite (gp_left_inverse (physical_cut q u)).
  reflexivity.
Qed.

Theorem DIAMOND05_GP_TRANSPORTS_BKQR_ACTION :
  forall (q : Cut) (u : R3Trajectory),
    gp_action q (gp_forward u) = physical_action q u.
Proof.
  intros q u.
  unfold gp_action, physical_action, gp_current, physical_current,
    gp_capacity, physical_capacity, GP_NSEForm, GP_LHForm.
  repeat rewrite (gp_left_inverse u).
  repeat rewrite (gp_cut_commutes q u).
  repeat rewrite (gp_left_inverse (physical_cut q u)).
  reflexivity.
Qed.

Hypothesis nse_global_energy_cancellation :
  forall u : R3Trajectory, NSEForm u u u = 0.

Theorem DIAMOND06_GP_PRESERVES_GLOBAL_NSE_CANCELLATION :
  forall U : GPState, GP_NSEForm U U U = 0.
Proof.
  intro U.
  unfold GP_NSEForm.
  apply nse_global_energy_cancellation.
Qed.

Theorem DIAMOND07_GP_IS_REPRESENTATION_NOT_NEW_PHYSICS :
  forall U : GPState,
    gp_forward (gp_back U) = U.
Proof.
  exact gp_right_inverse.
Qed.

End OPERATOR_DIAMOND.

(* ------------------------------------------------------------------------- *)
(* M7 READOUT OF THE DIAMOND                                                  *)
(*                                                                           *)
(* A countable BKQR channel family turns the universal scalar contraction     *)
(* into the resistant-action mass sequence consumed by the checked M7 spine. *)
(* ------------------------------------------------------------------------- *)

Section M7_DIAMOND.

Context {GPState Cut : Type}.

Variable D : Cut -> GPState -> R.
Variable J : Cut -> GPState -> R.
Variable channel : nat -> Cut.
Variable paid : GPState -> nat -> R.

Definition diamond_mass (U : GPState) (n : nat) : R :=
  Cov.action (J (channel n) U) (D (channel n) U).

Definition DiamondRenewal (U : GPState) : Prop :=
  Spine.GP509RenewalCertificate (diamond_mass U) (paid U).

Definition DiamondPaidBudget (U : GPState) : Prop :=
  Spine.GPUniformPaidPrefix (paid U).

Definition DiamondM7Regular (U : GPState) : Prop :=
  Spine.GPSequenceM7 (diamond_mass U).

Theorem DIAMOND20_RENEWAL_PLUS_FINITE_PAYMENT_GIVES_M7 :
  forall U : GPState,
    DiamondRenewal U ->
    DiamondPaidBudget U ->
    DiamondM7Regular U.
Proof.
  intros U Hrenew Hpaid.
  exact
    (Spine.NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7
       (diamond_mass U) (paid U) Hrenew Hpaid).
Qed.

Theorem DIAMOND21_ZERO_EXTERNAL_PAYMENT_GIVES_M7 :
  forall U : GPState,
    (forall n : nat, 0 <= diamond_mass U n) ->
    (forall n : nat,
       605 * diamond_mass U (S n) <= 509 * diamond_mass U n) ->
    DiamondM7Regular U.
Proof.
  intros U Hmass Hstep.
  exact
    (Spine.NSGM03_ZERO_PAID_CRITICAL_GP_RENEWAL_IS_SUMMABLE
       (diamond_mass U) Hmass Hstep).
Qed.

End M7_DIAMOND.

(* ------------------------------------------------------------------------- *)
(* UNIVERSAL R^3, f=0 TERMINAL                                               *)
(*                                                                           *)
(* This theorem is universally quantified over the R^3 Leray-Hopf/NSE class. *)
(* It does not choose a special solution.                                    *)
(*                                                                           *)
(* The sole substantive research interface is DiamondR3F0Realization:        *)
(* actual GP/BKQR cells from every common LH+NSE trajectory must satisfy      *)
(* the checked M7 renewal/payment semantics and the checked critical balance. *)
(* ------------------------------------------------------------------------- *)

Section R3_F0_TERMINAL.

Context {GPState Cut Time : Type}.

Variable gp_forward : R3Trajectory -> GPState.
Variable gp_back : GPState -> R3Trajectory.

Variable LerayHopfR3F0 : R3Trajectory -> Prop.
Variable NSER3F0 : R3Trajectory -> Prop.

Variable LHForm : R3Trajectory -> R3Trajectory -> R.
Variable NSEForm : R3Trajectory -> R3Trajectory -> R3Trajectory -> R.
Variable gp_cut_operator : Cut -> GPState -> GPState.
Variable channel : nat -> Cut.
Variable paid : GPState -> nat -> R.

Definition terminal_capacity (q : Cut) (U : GPState) : R :=
  LHForm (gp_back U) (gp_back (gp_cut_operator q U)).

Definition terminal_current (q : Cut) (U : GPState) : R :=
  NSEForm (gp_back U) (gp_back U) (gp_back (gp_cut_operator q U)).

Definition terminal_mass (U : GPState) (n : nat) : R :=
  Cov.action
    (terminal_current (channel n) U)
    (terminal_capacity (channel n) U).

Variable nu sigma initial_mass : R.
Variable critical_mass : GPState -> Time -> R.
Variable critical_dissipation : GPState -> Time -> R.
Variable action_cost : GPState -> Time -> R.

Definition DiamondCriticalRegular (U : GPState) : Prop :=
  Energy.CriticalH12Bound Time (critical_mass U) /\
  Energy.CriticalH32Dissipation Time (critical_dissipation U).

Record DiamondR3F0Realization (u : R3Trajectory) : Prop := {
  dr_gp_left_inverse : gp_back (gp_forward u) = u;

  dr_renewal :
    Spine.GP509RenewalCertificate
      (terminal_mass (gp_forward u))
      (paid (gp_forward u));

  dr_paid_budget :
    Spine.GPUniformPaidPrefix (paid (gp_forward u));

  dr_action_cost_realization :
    Energy.M7ActionCostRealization
      Time
      (terminal_mass (gp_forward u))
      (action_cost (gp_forward u));

  dr_critical_balance :
    Energy.CriticalEnergyBalance
      Time nu sigma initial_mass
      (critical_mass (gp_forward u))
      (critical_dissipation (gp_forward u))
      (action_cost (gp_forward u))
}.

Definition UniversalDiamondR3F0Realization : Prop :=
  forall u : R3Trajectory,
    LerayHopfR3F0 u ->
    NSER3F0 u ->
    DiamondR3F0Realization u.

Theorem DIAMOND80_REALIZATION_GIVES_M7_REGULARITY :
  forall u : R3Trajectory,
    DiamondR3F0Realization u ->
    Spine.GPSequenceM7 (terminal_mass (gp_forward u)).
Proof.
  intros u Hreal.
  destruct Hreal as [Hinv Hrenew Hpaid Hcost Hbalance].
  exact
    (Spine.NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7
       (terminal_mass (gp_forward u))
       (paid (gp_forward u))
       Hrenew Hpaid).
Qed.

Theorem DIAMOND90_REALIZATION_GIVES_CRITICAL_REGULARITY :
  forall u : R3Trajectory,
    DiamondR3F0Realization u ->
    DiamondCriticalRegular (gp_forward u).
Proof.
  intros u Hreal.
  destruct Hreal as [Hinv Hrenew Hpaid Hcost Hbalance].
  assert (HM7 :
    Spine.GPSequenceM7 (terminal_mass (gp_forward u))).
  {
    exact
      (Spine.NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7
         (terminal_mass (gp_forward u))
         (paid (gp_forward u))
         Hrenew Hpaid).
  }
  unfold DiamondCriticalRegular.
  exact
    (Energy.NSCE90_M7_INJECTS_INTO_CRITICAL_ENERGY_TARGET
       Time
       (terminal_mass (gp_forward u))
       nu sigma initial_mass
       (critical_mass (gp_forward u))
       (critical_dissipation (gp_forward u))
       (action_cost (gp_forward u))
       HM7 Hcost Hbalance).
Qed.

Theorem DIAMOND91_UNIVERSAL_R3_F0_CRITICAL_REGULARITY :
  UniversalDiamondR3F0Realization ->
  forall u : R3Trajectory,
    LerayHopfR3F0 u ->
    NSER3F0 u ->
    DiamondCriticalRegular (gp_forward u).
Proof.
  intros Huniv u HLH HNSE.
  pose proof (Huniv u HLH HNSE) as Hreal.
  destruct Hreal as [Hinv Hrenew Hpaid Hcost Hbalance].
  assert (HM7 :
    Spine.GPSequenceM7 (terminal_mass (gp_forward u))).
  {
    exact
      (Spine.NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7
         (terminal_mass (gp_forward u))
         (paid (gp_forward u))
         Hrenew Hpaid).
  }
  unfold DiamondCriticalRegular.
  exact
    (Energy.NSCE90_M7_INJECTS_INTO_CRITICAL_ENERGY_TARGET
       Time
       (terminal_mass (gp_forward u))
       nu sigma initial_mass
       (critical_mass (gp_forward u))
       (critical_dissipation (gp_forward u))
       (action_cost (gp_forward u))
       HM7 Hcost Hbalance).
Qed.

(* A classical PDE exit can be attached without changing the Diamond core.    *)
Variable PhysicalRegular : R3Trajectory -> Prop.
Variable critical_to_physical_regular :
  forall u : R3Trajectory,
    DiamondCriticalRegular (gp_forward u) ->
    PhysicalRegular u.

Theorem DIAMOND99_UNIVERSAL_R3_F0_PDE_REGULARITY :
  UniversalDiamondR3F0Realization ->
  forall u : R3Trajectory,
    LerayHopfR3F0 u ->
    NSER3F0 u ->
    PhysicalRegular u.
Proof.
  intros Huniv u HLH HNSE.
  apply critical_to_physical_regular.
  pose proof (Huniv u HLH HNSE) as Hreal.
  destruct Hreal as [Hinv Hrenew Hpaid Hcost Hbalance].
  assert (HM7 :
    Spine.GPSequenceM7 (terminal_mass (gp_forward u))).
  {
    exact
      (Spine.NSGM02_GP_RENEWAL_PLUS_PAID_BUDGET_GIVES_SEQUENCE_M7
         (terminal_mass (gp_forward u))
         (paid (gp_forward u))
         Hrenew Hpaid).
  }
  unfold DiamondCriticalRegular.
  exact
    (Energy.NSCE90_M7_INJECTS_INTO_CRITICAL_ENERGY_TARGET
       Time
       (terminal_mass (gp_forward u))
       nu sigma initial_mass
       (critical_mass (gp_forward u))
       (critical_dissipation (gp_forward u))
       (action_cost (gp_forward u))
       HM7 Hcost Hbalance).
Qed.

End R3_F0_TERMINAL.

Definition STATUS : string :=
  "NSE_R3_F0_GP_DIAMOND_V0_1_4_OPERATOR_CORE_NO_ADMITTED_UNIVERSAL_REALIZATION_EXPLICIT"%string.

End NSE_R3_F0_GP_DIAMOND.

Check NSE_R3_F0_GP_DIAMOND.DIAMOND01_GP_TRANSPORTS_LH_FORM.
Check NSE_R3_F0_GP_DIAMOND.DIAMOND02_GP_TRANSPORTS_NSE_FORM.
Check NSE_R3_F0_GP_DIAMOND.DIAMOND05_GP_TRANSPORTS_BKQR_ACTION.
Check NSE_R3_F0_GP_DIAMOND.DIAMOND06_GP_PRESERVES_GLOBAL_NSE_CANCELLATION.
Check NSE_R3_F0_GP_DIAMOND.DIAMOND20_RENEWAL_PLUS_FINITE_PAYMENT_GIVES_M7.
Check NSE_R3_F0_GP_DIAMOND.DIAMOND90_REALIZATION_GIVES_CRITICAL_REGULARITY.
Check NSE_R3_F0_GP_DIAMOND.DIAMOND91_UNIVERSAL_R3_F0_CRITICAL_REGULARITY.
Check NSE_R3_F0_GP_DIAMOND.DIAMOND99_UNIVERSAL_R3_F0_PDE_REGULARITY.

Print Assumptions NSE_R3_F0_GP_DIAMOND.DIAMOND05_GP_TRANSPORTS_BKQR_ACTION.
Print Assumptions NSE_R3_F0_GP_DIAMOND.DIAMOND20_RENEWAL_PLUS_FINITE_PAYMENT_GIVES_M7.
Print Assumptions NSE_R3_F0_GP_DIAMOND.DIAMOND91_UNIVERSAL_R3_F0_CRITICAL_REGULARITY.
Print Assumptions NSE_R3_F0_GP_DIAMOND.DIAMOND99_UNIVERSAL_R3_F0_PDE_REGULARITY.
