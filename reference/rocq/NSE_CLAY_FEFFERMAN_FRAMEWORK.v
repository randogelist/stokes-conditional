From Stdlib Require Import Reals String Lists.List.
Require Import NSE_R3_FORCED_GP_DIAMOND_STORAGE_BRIDGE.
Require Import NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.
Require Import awpi_nse_gp_storage_replenishment_v0_51_7.
Require Import awpi_nse_direct_gp_shell_occupancy_v0_48_4.
Require Import awpi_nse_scalar_comparison_v0_48_4.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.
Require Import NSE_R3_FORCED_GP_DIAMOND_SEPARATRIX.
Require Import NSE_R3_FORCED_GP_DIAMOND_INTRINSIC_FORCE_CLASS.
Require Import NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.
Require Import awpi_nse_torus_fourier_periodic_admissibility_v0_45_1.
Require Import awpi_nse_lh_torus_fourier_tests_v0_44_3.
Require Import awpi_nse_lh_fourier_polynomial_convolution_v0_45_1.

Module CLAY_FEFFERMAN_FRAMEWORK.
Module TPER := NSE_TORUS_FOURIER_PERIODIC_ADMISSIBILITY_V0451.
Module TTEST := NSE_LH_TORUS_FOURIER_TESTS.
Module TCONV := NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.
Module FC := NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.
Module SR := NSE_GP_STORAGE_REPLENISHMENT.
Module O := NSE_DIRECT_GP_SHELL_OCCUPANCY.
Module SC := NSE_SCALAR_COMPARISON.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

(* Generic logical layer for Fefferman A/B/C/D. *)
Section FORCE_CLASSIFICATION.
Context {Data Force Sol : Type}.
Variable InitOK : Data -> Prop.
Variable ForceOK : Force -> Prop.
Variable SmoothSolves : Data -> Force -> Sol -> Prop.

Definition RegularForceForAllData (f : Force) : Prop :=
  ForceOK f /\ forall d : Data, InitOK d -> exists s : Sol, SmoothSolves d f s.

Definition BreakdownForceForSomeData (f : Force) : Prop :=
  ForceOK f /\ exists d : Data, InitOK d /\ ~ exists s : Sol, SmoothSolves d f s.

Theorem FW00_REGULAR_AND_BREAKDOWN_FORCE_CLASSES_DISJOINT :
  forall f : Force,
    RegularForceForAllData f ->
    ~ BreakdownForceForSomeData f.
Proof.
  intros f [Hf Hreg] [Hf' [d [Hd Hbad]]].
  apply Hbad.
  exact (Hreg d Hd).
Qed.

Variable zero_force : Force.
Definition FeffermanUnforcedSmoothness : Prop :=
  forall d : Data, InitOK d -> exists s : Sol, SmoothSolves d zero_force s.

Theorem FW01_ZERO_FORCE_REGULAR_CLASS_GIVES_UNFORCED_SMOOTHNESS :
  RegularForceForAllData zero_force -> FeffermanUnforcedSmoothness.
Proof.
  intros [_ H]. exact H.
Qed.

Definition FeffermanBreakdownExistence : Prop :=
  exists f : Force, BreakdownForceForSomeData f.

Theorem FW02_ALL_ADMISSIBLE_FORCES_REGULAR_EXCLUDES_BREAKDOWN :
  (forall f : Force, ForceOK f -> RegularForceForAllData f) ->
  ~ FeffermanBreakdownExistence.
Proof.
  intros Hall [f Hbad].
  pose proof (proj1 Hbad) as Hf.
  pose proof (Hall f Hf) as Hreg.
  exact ((FW00_REGULAR_AND_BREAKDOWN_FORCE_CLASSES_DISJOINT f Hreg) Hbad).
Qed.

Variable RegClass : Force -> Prop.
Definition RegClassSound : Prop :=
  forall f : Force,
    ForceOK f -> RegClass f ->
    forall d : Data, InitOK d -> exists s : Sol, SmoothSolves d f s.

Theorem FW03_BREAKDOWN_FORCE_ESCAPES_ANY_SOUND_REGULAR_CLASS :
  RegClassSound ->
  forall f : Force,
    BreakdownForceForSomeData f ->
    ~ RegClass f.
Proof.
  intros Hsound f [Hf [d [Hd Hbad]]] Hreg.
  apply Hbad.
  exact (Hsound f Hf Hreg d Hd).
Qed.
End FORCE_CLASSIFICATION.

(* One domain-level Diamond record is enough to feed both the unforced
   statement (A or B) and the forced-breakdown exclusion statement (C or D). *)
Section DOMAIN_DIAMOND.
Context {Data Force Sol : Type}.
Variable InitOK : Data -> Prop.
Variable ForceOK : Force -> Prop.
Variable zero_force : Force.
Variable SmoothSolves : Data -> Force -> Sol -> Prop.
Variable CriticalClosed : Data -> Force -> Prop.
Variable IntrinsicRegularForce : Force -> Prop.

Record DomainDiamondClosure : Prop := {
  dd_zero_force_admissible : ForceOK zero_force;
  dd_zero_force_intrinsic : IntrinsicRegularForce zero_force;
  dd_intrinsic_to_critical :
    forall d f,
      InitOK d -> ForceOK f -> IntrinsicRegularForce f -> CriticalClosed d f;
  dd_critical_to_smooth :
    forall d f,
      CriticalClosed d f -> exists s : Sol, SmoothSolves d f s
}.

Theorem FW20_DOMAIN_DIAMOND_INTRINSIC_FORCE_REGULAR :
  DomainDiamondClosure ->
  forall f : Force,
    ForceOK f -> IntrinsicRegularForce f ->
    forall d : Data, InitOK d -> exists s : Sol, SmoothSolves d f s.
Proof.
  intros Hdiamond f Hf Hreg d Hd.
  destruct Hdiamond as [Hzero HzeroReg Hclose Hexit].
  apply Hexit.
  exact (Hclose d f Hd Hf Hreg).
Qed.

Theorem FW21_DOMAIN_DIAMOND_ZERO_FORCE_GIVES_UNFORCED :
  DomainDiamondClosure ->
  forall d : Data, InitOK d -> exists s : Sol, SmoothSolves d zero_force s.
Proof.
  intros Hdiamond d Hd.
  destruct Hdiamond as [Hzero HzeroReg Hclose Hexit].
  apply Hexit.
  exact (Hclose d zero_force Hd Hzero HzeroReg).
Qed.

Theorem FW22_DOMAIN_DIAMOND_BREAKDOWN_ESCAPES_INTRINSIC :
  DomainDiamondClosure ->
  forall f : Force,
    BreakdownForceForSomeData InitOK ForceOK SmoothSolves f ->
    ~ IntrinsicRegularForce f.
Proof.
  intros Hdiamond f [Hf [d [Hd Hbad]]] Hreg.
  apply Hbad.
  exact (FW20_DOMAIN_DIAMOND_INTRINSIC_FORCE_REGULAR
           Hdiamond f Hf Hreg d Hd).
Qed.

Theorem FW23_DOMAIN_DIAMOND_FORCE_EMBEDDING_EXCLUDES_BREAKDOWN :
  DomainDiamondClosure ->
  (forall f : Force, ForceOK f -> IntrinsicRegularForce f) ->
  ~ FeffermanBreakdownExistence InitOK ForceOK SmoothSolves.
Proof.
  intros Hdiamond Hembed [f Hbad].
  pose proof (proj1 Hbad) as Hf.
  pose proof (FW22_DOMAIN_DIAMOND_BREAKDOWN_ESCAPES_INTRINSIC
                Hdiamond f Hbad) as Hnot.
  exact (Hnot (Hembed f Hf)).
Qed.

Theorem FW24_DOMAIN_DIAMOND_CLASSIFIES_ZERO_AND_INTRINSIC_FORCES :
  DomainDiamondClosure ->
  (forall d : Data, InitOK d -> exists s : Sol, SmoothSolves d zero_force s) /\
  (forall f : Force,
     ForceOK f -> IntrinsicRegularForce f ->
     forall d : Data, InitOK d -> exists s : Sol, SmoothSolves d f s).
Proof.
  intro Hdiamond.
  split.
  - exact (FW21_DOMAIN_DIAMOND_ZERO_FORCE_GIVES_UNFORCED Hdiamond).
  - exact (FW20_DOMAIN_DIAMOND_INTRINSIC_FORCE_REGULAR Hdiamond).
Qed.
End DOMAIN_DIAMOND.



(* R3 storage-factorized domain closure.  The physical realization witness is
   separated from the analytic critical readout and the classical exit.  This
   lets A and C share the same concrete closure engine without hiding the
   remaining M7/storage realization inside one opaque DomainDiamondClosure. *)
Section STORAGE_DOMAIN_DIAMOND.
Context {Data Force Sol StorageWitness : Type}.
Variable InitOK : Data -> Prop.
Variable ForceOK : Force -> Prop.
Variable zero_force : Force.
Variable SmoothSolves : Data -> Force -> Sol -> Prop.
Variable CriticalClosed : Data -> Force -> Prop.
Variable IntrinsicRegularForce : Force -> Prop.
Variable WitnessFor : Data -> Force -> StorageWitness -> Prop.

Record StorageDomainDiamondClosure : Prop := {
  sdd_zero_force_admissible : ForceOK zero_force;
  sdd_zero_force_intrinsic : IntrinsicRegularForce zero_force;
  sdd_intrinsic_to_storage :
    forall d f,
      InitOK d -> ForceOK f -> IntrinsicRegularForce f ->
      exists w : StorageWitness, WitnessFor d f w;
  sdd_storage_to_critical :
    forall d f w,
      InitOK d -> ForceOK f -> WitnessFor d f w -> CriticalClosed d f;
  sdd_critical_to_smooth :
    forall d f,
      CriticalClosed d f -> exists s : Sol, SmoothSolves d f s
}.

Theorem FW30_STORAGE_DOMAIN_DIAMOND_TO_DOMAIN_DIAMOND :
  StorageDomainDiamondClosure ->
  DomainDiamondClosure InitOK ForceOK zero_force SmoothSolves
    CriticalClosed IntrinsicRegularForce.
Proof.
  intro H.
  destruct H as [Hzero HzeroReg Hstore Hread Hexit].
  constructor.
  - exact Hzero.
  - exact HzeroReg.
  - intros d f Hd Hf Hreg.
    destruct (Hstore d f Hd Hf Hreg) as [w Hw].
    exact (Hread d f w Hd Hf Hw).
  - exact Hexit.
Qed.

Theorem FW31_STORAGE_DOMAIN_DIAMOND_ZERO_FORCE_GIVES_UNFORCED :
  StorageDomainDiamondClosure ->
  forall d : Data, InitOK d -> exists s : Sol, SmoothSolves d zero_force s.
Proof.
  intros H d Hd.
  destruct H as [Hzero HzeroReg Hstore Hread Hexit].
  destruct (Hstore d zero_force Hd Hzero HzeroReg) as [w Hw].
  apply Hexit.
  exact (Hread d zero_force w Hd Hzero Hw).
Qed.

Theorem FW32_STORAGE_DOMAIN_DIAMOND_BREAKDOWN_ESCAPES_INTRINSIC :
  StorageDomainDiamondClosure ->
  forall f : Force,
    BreakdownForceForSomeData InitOK ForceOK SmoothSolves f ->
    ~ IntrinsicRegularForce f.
Proof.
  intros H f [Hf [d [Hd Hbad]]] Hreg.
  apply Hbad.
  destruct H as [Hzero HzeroReg Hstore Hread Hexit].
  destruct (Hstore d f Hd Hf Hreg) as [w Hw].
  apply Hexit.
  exact (Hread d f w Hd Hf Hw).
Qed.

Theorem FW33_STORAGE_DOMAIN_DIAMOND_FORCE_EMBEDDING_EXCLUDES_BREAKDOWN :
  StorageDomainDiamondClosure ->
  (forall f : Force, ForceOK f -> IntrinsicRegularForce f) ->
  ~ FeffermanBreakdownExistence InitOK ForceOK SmoothSolves.
Proof.
  intros H Hembed [f Hbad].
  pose proof (proj1 Hbad) as Hf.
  pose proof (FW32_STORAGE_DOMAIN_DIAMOND_BREAKDOWN_ESCAPES_INTRINSIC
                H f Hbad) as Hnot.
  exact (Hnot (Hembed f Hf)).
Qed.
End STORAGE_DOMAIN_DIAMOND.


(* Concrete R3 storage-terminal engine.  Unlike StorageDomainDiamondClosure,
   this section does not assume a separate storage-to-critical map.  The
   witness contains exactly the hypotheses consumed by NSRA99 plus the finite-
   cut/full-critical readout, and the uniform critical bound is derived here. *)
Section CONCRETE_R3_STORAGE_TERMINAL.
Context {Data Force Sol Cut Time : Type}.
Variable InitOK : Data -> Prop.
Variable ForceOK : Force -> Prop.
Variable zero_force : Force.
Variable SmoothSolves : Data -> Force -> Sol -> Prop.
Variable IntrinsicRegularForce : Force -> Prop.
Variable critical_mass : Data -> Force -> Time -> R.

Definition R3CriticalBounded (d : Data) (f : Force) : Prop :=
  exists B : R, forall t : Time, critical_mass d f t <= B.

Record R3StorageTerminalWitness (d : Data) (f : Force) : Type := {
  rst_ev : Cut -> O.ShellEvolution;
  rst_path : Cut -> SR.StoragePath;
  rst_stamp : Time -> R;
  rst_cut_time : nat -> Time;
  rst_nu : R;
  rst_cap : R;
  rst_theta : R;
  rst_cs : R;
  rst_E0 : R;
  rst_M0 : R;
  rst_T : R;
  rst_kappa : R;
  rst_Hinit : R;
  rst_gamma : R;
  rst_Chigh : R;
  rst_Hnu : 0 < rst_nu;
  rst_Hcap : 0 <= rst_cap;
  rst_HE0 : 0 <= rst_E0;
  rst_Htheta0 : 0 <= rst_theta;
  rst_Htheta1 : rst_theta < 1;
  rst_Hkappa : 0 <= rst_kappa;
  rst_Hgamma : rst_gamma < 1;
  rst_Hbindings :
    forall c : Cut,
      O.EvolutionBindings rst_nu rst_cap rst_theta rst_cs rst_E0 rst_M0 rst_T (rst_ev c);
  rst_Hstorage :
    forall c : Cut,
      SR.ExactIntegratedStorage rst_T (rst_ev c) (rst_path c);
  rst_Hinitial_storage :
    forall c : Cut, SR.sp_H (rst_path c) 0 <= rst_Hinit;
  rst_Hlower_payments :
    forall c : Cut,
      SR.LowerOutputPayments rst_nu rst_cap rst_kappa rst_T (rst_ev c) (rst_path c);
  rst_Hhigh_absorption :
    forall c : Cut,
      SR.HighOutputAbsorption rst_gamma rst_Chigh rst_T (rst_ev c) (rst_path c);
  rst_Htime : forall t : Time, SC.within rst_T (rst_stamp t);
  rst_Hzero : rst_stamp (rst_cut_time O) = 0;
  rst_Horder : forall n, rst_stamp (rst_cut_time n) <= rst_stamp (rst_cut_time (S n));
  rst_Hcofinal : forall t : Time, exists n, rst_stamp t <= rst_stamp (rst_cut_time n);
  rst_Hfull_readout :
    forall t : Time,
      FC.FullCriticalLimitReadout
        Cut
        (fun c : Cut => O.ev_E (rst_ev c) (rst_stamp t))
        (critical_mass d f t)
}.

Theorem FW40_STORAGE_TERMINAL_WITNESS_GIVES_UNIFORM_CRITICAL_BOUND :
  forall d f (w : R3StorageTerminalWitness d f),
    R3CriticalBounded d f.
Proof.
  intros d f w.
  destruct w as
    [ev path stamp cut
     nu cap theta cs E0 M0 T kappa Hinit gamma Chigh
     Hnu Hcap HE0 Htheta0 Htheta1 Hkappa Hgamma
     Hbindings Hstorage Hinitial_storage Hlower_payments Hhigh_absorption
     Htime Hzero Horder Hcofinal Hfull_readout].
  pose proof
    (SR.NSRA99_STORAGE_REPLENISHMENT_TO_EXISTING_M7_TERMINAL
      Cut Time
      ev path stamp cut
      nu cap theta cs E0 M0 T kappa Hinit gamma Chigh
      Hnu Hcap HE0 Htheta0 Htheta1 Hkappa Hgamma
      Hbindings Hstorage Hinitial_storage Hlower_payments Hhigh_absorption
      Htime Hzero Horder Hcofinal) as Hterm.
  cbv zeta in Hterm.
  destruct Hterm as [_ [_ [_ [_ Hcrit]]]].
  unfold CE.UniformCriticalEnergy in Hcrit.
  destruct Hcrit as [Mmax [Dmax [HM [HD [Hmass Hdiss]]]]].
  exists Mmax.
  intro t.
  destruct (Hfull_readout t) as [Hupper Hleast].
  apply Hleast.
  intro c.
  exact (Hmass (c, t)).
Qed.

Record ConcreteR3StorageDiamondClosure : Prop := {
  cr3_zero_force_admissible : ForceOK zero_force;
  cr3_zero_force_intrinsic : IntrinsicRegularForce zero_force;
  cr3_intrinsic_to_storage :
    forall d f,
      InitOK d -> ForceOK f -> IntrinsicRegularForce f ->
      exists w : R3StorageTerminalWitness d f, True;
  cr3_critical_to_smooth :
    forall d f,
      R3CriticalBounded d f -> exists s : Sol, SmoothSolves d f s
}.

Theorem FW41_CONCRETE_R3_STORAGE_DIAMOND_ZERO_FORCE_GIVES_UNFORCED :
  ConcreteR3StorageDiamondClosure ->
  forall d : Data, InitOK d -> exists s : Sol, SmoothSolves d zero_force s.
Proof.
  intros H d Hd.
  destruct H as [Hzero HzeroReg Hstore Hexit].
  destruct (Hstore d zero_force Hd Hzero HzeroReg) as [w _].
  apply Hexit.
  exact (FW40_STORAGE_TERMINAL_WITNESS_GIVES_UNIFORM_CRITICAL_BOUND d zero_force w).
Qed.

Theorem FW42_CONCRETE_R3_STORAGE_DIAMOND_BREAKDOWN_ESCAPES_INTRINSIC :
  ConcreteR3StorageDiamondClosure ->
  forall f : Force,
    BreakdownForceForSomeData InitOK ForceOK SmoothSolves f ->
    ~ IntrinsicRegularForce f.
Proof.
  intros H f [Hf [d [Hd Hbad]]] Hreg.
  apply Hbad.
  destruct H as [Hzero HzeroReg Hstore Hexit].
  destruct (Hstore d f Hd Hf Hreg) as [w _].
  apply Hexit.
  exact (FW40_STORAGE_TERMINAL_WITNESS_GIVES_UNIFORM_CRITICAL_BOUND d f w).
Qed.

Theorem FW43_CONCRETE_R3_STORAGE_DIAMOND_FORCE_EMBEDDING_EXCLUDES_BREAKDOWN :
  ConcreteR3StorageDiamondClosure ->
  (forall f : Force, ForceOK f -> IntrinsicRegularForce f) ->
  ~ FeffermanBreakdownExistence InitOK ForceOK SmoothSolves.
Proof.
  intros H Hembed [f Hbad].
  pose proof (proj1 Hbad) as Hf.
  pose proof (FW42_CONCRETE_R3_STORAGE_DIAMOND_BREAKDOWN_ESCAPES_INTRINSIC
                H f Hbad) as Hnot.
  exact (Hnot (Hembed f Hf)).
Qed.
End CONCRETE_R3_STORAGE_TERMINAL.

(* Periodic frontend facts already kernel-derived in imported torus anchors. *)
Theorem FW10_TORUS_PLANE_WAVE_GEOMETRY_READY :
  TPER.FullConcretePlaneWaveFamilyGeometry.
Proof.
  exact TPER.NSFPA60_FULL_CONCRETE_PLANE_WAVE_FAMILY_GEOMETRY_REALIZED.
Qed.

Theorem FW11_TORUS_FINITE_FOURIER_PRODUCT_IS_CONVOLUTION :
  forall P Q : list TCONV.FourierTerm,
  forall x : TCONV.R3,
    TCONV.poly_eval (TCONV.product_terms P Q) x =
    TCONV.CH.cmul (TCONV.poly_eval P x) (TCONV.poly_eval Q x).
Proof.
  exact TCONV.LH45_24_FINITE_FOURIER_PRODUCT_IS_CONVOLUTION.
Qed.

Definition STATUS : string :=
  "CLAY_FEFFERMAN_ABCD_FRAMEWORK_TWO_DOMAIN_DIAMONDS_PLUS_FORCE_CLASSIFICATION"%string.
End CLAY_FEFFERMAN_FRAMEWORK.

Print CLAY_FEFFERMAN_FRAMEWORK.FW20_DOMAIN_DIAMOND_INTRINSIC_FORCE_REGULAR.
Print CLAY_FEFFERMAN_FRAMEWORK.FW21_DOMAIN_DIAMOND_ZERO_FORCE_GIVES_UNFORCED.
Print CLAY_FEFFERMAN_FRAMEWORK.FW22_DOMAIN_DIAMOND_BREAKDOWN_ESCAPES_INTRINSIC.
Print CLAY_FEFFERMAN_FRAMEWORK.FW23_DOMAIN_DIAMOND_FORCE_EMBEDDING_EXCLUDES_BREAKDOWN.
Print CLAY_FEFFERMAN_FRAMEWORK.FW24_DOMAIN_DIAMOND_CLASSIFIES_ZERO_AND_INTRINSIC_FORCES.
Print CLAY_FEFFERMAN_FRAMEWORK.FW30_STORAGE_DOMAIN_DIAMOND_TO_DOMAIN_DIAMOND.
Print CLAY_FEFFERMAN_FRAMEWORK.FW31_STORAGE_DOMAIN_DIAMOND_ZERO_FORCE_GIVES_UNFORCED.
Print CLAY_FEFFERMAN_FRAMEWORK.FW32_STORAGE_DOMAIN_DIAMOND_BREAKDOWN_ESCAPES_INTRINSIC.
Print CLAY_FEFFERMAN_FRAMEWORK.FW33_STORAGE_DOMAIN_DIAMOND_FORCE_EMBEDDING_EXCLUDES_BREAKDOWN.
Print CLAY_FEFFERMAN_FRAMEWORK.FW10_TORUS_PLANE_WAVE_GEOMETRY_READY.
Print CLAY_FEFFERMAN_FRAMEWORK.FW11_TORUS_FINITE_FOURIER_PRODUCT_IS_CONVOLUTION.
Print CLAY_FEFFERMAN_FRAMEWORK.FW40_STORAGE_TERMINAL_WITNESS_GIVES_UNIFORM_CRITICAL_BOUND.
Print CLAY_FEFFERMAN_FRAMEWORK.FW41_CONCRETE_R3_STORAGE_DIAMOND_ZERO_FORCE_GIVES_UNFORCED.
Print CLAY_FEFFERMAN_FRAMEWORK.FW42_CONCRETE_R3_STORAGE_DIAMOND_BREAKDOWN_ESCAPES_INTRINSIC.
Print CLAY_FEFFERMAN_FRAMEWORK.FW43_CONCRETE_R3_STORAGE_DIAMOND_FORCE_EMBEDDING_EXCLUDES_BREAKDOWN.
