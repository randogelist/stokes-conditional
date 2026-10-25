From Stdlib Require Import Reals String Lra Psatz Field.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_gp_signed_source_closure_v0_51_0.
Require Import awpi_nse_gp_unforced_operator_class_v0_1_0.

Module NSE_GP_FORCING_CLASSIFICATION.
Module SSC := NSE_GP_SIGNED_SOURCE_CLOSURE.
Module UFC := NSE_GP_UNFORCED_OPERATOR_CLASS.
Import NSE_KQ_FINITE_ALGEBRA NSE_GP_SOURCE_STORAGE_DYNAMICS NSE_CONTINUOUS_TIME_CALCULUS.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* Trajectory-relative GP forcing classes.                            *)
(*                                                                    *)
(* IMPORTANT: these classes do not classify f by an ordinary Sobolev  *)
(* or time-integrability norm alone.  They classify the cumulative GP *)
(* work injected by f along the actual trajectory encoded in D.       *)
(* ------------------------------------------------------------------ *)

Definition gp_external_rate51
  (D : SSC.GPSourceData51) (f : UFC.ModalForcing51) (t : R) : R :=
  UFC.combined_forcing_rate51
    (SSC.g51_packets D) (SSC.g51_nu D) (SSC.g51_Z D)
    (f t) (SSC.g51_u D t).

Definition GPForcingPrimitive51
  (D : SSC.GPSourceData51) (f : UFC.ModalForcing51) (F : R -> R) : Prop :=
  PrimitiveOn (SSC.g51_t0 D) (SSC.g51_t1 D) (gp_external_rate51 D f) F.

Definition GPNullForcing51
  (D : SSC.GPSourceData51) (f : UFC.ModalForcing51) : Prop :=
  forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    gp_external_rate51 D f t = 0.

Definition GPFiniteForcingBudget51
  (D : SSC.GPSourceData51) (f : UFC.ModalForcing51)
  (F : R -> R) (Qf : R) : Prop :=
  GPForcingPrimitive51 D f F /\
  0 <= Qf /\
  forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t -> F t <= Qf.

Definition GPTimeIntegratedWorkBound51
  (D : SSC.GPSourceData51) (f : UFC.ModalForcing51)
  (F : R -> R) (Qf : R) : Prop :=
  GPFiniteForcingBudget51 D f F Qf.

Definition GPRelativeForcingBudget51
  (D : SSC.GPSourceData51) (f : UFC.ModalForcing51)
  (F : R -> R) (theta_f Qf : R) : Prop :=
  GPForcingPrimitive51 D f F /\
  0 <= theta_f /\
  0 <= Qf /\
  forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    F t <= Qf + theta_f * SSC.g51_nu D * SSC.g51_nu D * SSC.g51_Dcum D t.

Definition GPTotalProductionBudget51
  (D : SSC.GPSourceData51) (F : R -> R) (theta Qstar : R) : Prop :=
  forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    SSC.g51_Qcum D t + F t <=
      Qstar + theta * SSC.g51_nu D * SSC.g51_nu D * SSC.g51_Dcum D t.

(* ------------------------------------------------------------------ *)
(* Exact calibration points.                                          *)
(* ------------------------------------------------------------------ *)

Theorem GFC00_LITERAL_ZERO_FORCE_IS_GP_NULL :
  forall D : SSC.GPSourceData51,
    GPNullForcing51 D UFC.zero_forcing51.
Proof.
  intros D; unfold GPNullForcing51; intros t Ht.
  unfold gp_external_rate51.
  change (UFC.combined_forcing_rate51
    (SSC.g51_packets D) (SSC.g51_nu D) (SSC.g51_Z D)
    (UFC.zero_forcing51 0) (SSC.g51_u D t) = 0).
  apply UFC.UFC24_ZERO_COMBINED_FORCING_RATE.
Qed.

Theorem GFC01_LITERAL_ZERO_FORCE_HAS_ZERO_PRIMITIVE :
  forall D : SSC.GPSourceData51,
    GPForcingPrimitive51 D UFC.zero_forcing51 (fun _ : R => 0).
Proof.
  intros D; unfold GPForcingPrimitive51, PrimitiveOn; split.
  - reflexivity.
  - unfold DerivativeOn; intros t Ht.
    unfold gp_external_rate51.
    change (derivable_pt_lim (fun _ : R => 0) t 0).
    exact (derivable_pt_lim_const 0 t).
Qed.

Theorem GFC02_LITERAL_ZERO_FORCE_IS_RELATIVE_ZERO :
  forall D : SSC.GPSourceData51,
    GPRelativeForcingBudget51 D UFC.zero_forcing51
      (fun _ : R => 0) 0 0.
Proof.
  intros D; unfold GPRelativeForcingBudget51.
  split; [apply GFC01_LITERAL_ZERO_FORCE_HAS_ZERO_PRIMITIVE|].
  split; [lra|].
  split; [lra|].
  intros t Ht; ring_simplify; lra.
Qed.

Theorem GFC03_FINITE_BUDGET_IS_RELATIVE_WITH_THETA_ZERO :
  forall D f F Qf,
    GPFiniteForcingBudget51 D f F Qf ->
    GPRelativeForcingBudget51 D f F 0 Qf.
Proof.
  intros D f F Qf H; unfold GPFiniteForcingBudget51 in H.
  destruct H as [HP [HQ HB]].
  unfold GPRelativeForcingBudget51.
  split; [exact HP|].
  split; [lra|].
  split; [exact HQ|].
  intros t Ht; specialize (HB t Ht); ring_simplify; lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Internal M7 production + external GP production add exactly.        *)
(* ------------------------------------------------------------------ *)

Theorem GFC10_INTERNAL_PLUS_EXTERNAL_RELATIVE_BUDGETS_ADD :
  forall D f F theta_i Qi theta_f Qf,
    SSC.SignedProductionBudget51 D theta_i Qi ->
    GPRelativeForcingBudget51 D f F theta_f Qf ->
    GPTotalProductionBudget51 D F (theta_i + theta_f) (Qi + Qf).
Proof.
  intros D f F theta_i Qi theta_f Qf Hint Hrel.
  unfold GPRelativeForcingBudget51 in Hrel.
  destruct Hrel as [HP [Htf [HQf Hext]]].
  intros t Ht.
  specialize (Hint t Ht); specialize (Hext t Ht).
  nra.
Qed.

Definition GPRegularitySafeForcing51
  (D : SSC.GPSourceData51) (f : UFC.ModalForcing51)
  (F : R -> R) (theta_i Qi theta_f Qf : R) : Prop :=
  0 <= theta_i /\ 0 <= theta_f /\
  theta_i + theta_f < 1 /\
  0 <= Qi /\ 0 <= Qf /\
  SSC.SignedProductionBudget51 D theta_i Qi /\
  GPRelativeForcingBudget51 D f F theta_f Qf.

Theorem GFC12_ZERO_FORCE_IS_SAFE_WHEN_INTERNAL_MARGIN_IS_SUBUNIT :
  forall D theta_i Qi,
    0 <= theta_i -> theta_i < 1 -> 0 <= Qi ->
    SSC.SignedProductionBudget51 D theta_i Qi ->
    GPRegularitySafeForcing51 D UFC.zero_forcing51
      (fun _ : R => 0) theta_i Qi 0 0.
Proof.
  intros D theta_i Qi Hti Hti1 HQi Hint.
  unfold GPRegularitySafeForcing51.
  split; [exact Hti|].
  split; [lra|].
  split; [lra|].
  split; [exact HQi|].
  split; [lra|].
  split; [exact Hint|].
  exact (GFC02_LITERAL_ZERO_FORCE_IS_RELATIVE_ZERO D).
Qed.

Theorem GFC13_FINITE_GP_WORK_PRESERVES_INTERNAL_SUBUNIT_MARGIN :
  forall D f F theta_i Qi Qf,
    0 <= theta_i -> theta_i < 1 -> 0 <= Qi ->
    SSC.SignedProductionBudget51 D theta_i Qi ->
    GPFiniteForcingBudget51 D f F Qf ->
    GPRegularitySafeForcing51 D f F theta_i Qi 0 Qf.
Proof.
  intros D f F theta_i Qi Qf Hti Hti1 HQi Hint Hfin.
  unfold GPFiniteForcingBudget51 in Hfin.
  destruct Hfin as [HP [HQf HB]].
  unfold GPRegularitySafeForcing51.
  split; [exact Hti|].
  split; [lra|].
  split; [lra|].
  split; [exact HQi|].
  split; [exact HQf|].
  split; [exact Hint|].
  unfold GPRelativeForcingBudget51.
  split; [exact HP|].
  split; [lra|].
  split; [exact HQf|].
  intros t Ht; specialize (HB t Ht); ring_simplify; lra.
Qed.

Theorem GFC11_SAFE_FORCING_HAS_SUBUNIT_TOTAL_BUDGET :
  forall D f F theta_i Qi theta_f Qf,
    GPRegularitySafeForcing51 D f F theta_i Qi theta_f Qf ->
    0 <= theta_i + theta_f /\
    theta_i + theta_f < 1 /\
    0 <= Qi + Qf /\
    GPTotalProductionBudget51 D F (theta_i + theta_f) (Qi + Qf).
Proof.
  intros D f F theta_i Qi theta_f Qf Hsafe.
  unfold GPRegularitySafeForcing51 in Hsafe.
  destruct Hsafe as [Hti [Htf [Hsum [HQi [HQf [Hint Hext]]]]]].
  split; [nra|].
  split; [exact Hsum|].
  split; [nra|].
  exact (GFC10_INTERNAL_PLUS_EXTERNAL_RELATIVE_BUDGETS_ADD
    D f F theta_i Qi theta_f Qf Hint Hext).
Qed.

(* ------------------------------------------------------------------ *)
(* Abstract forced integrated GP ledger.                               *)
(*                                                                    *)
(* This is the exact integrated object required for regularity.        *)
(* It does not assume that every smooth or time-integrable f satisfies *)
(* the class.  That is deliberately left as a separate calibration.    *)
(* ------------------------------------------------------------------ *)

Record ForcedIntegratedGPLedger51
  (D : SSC.GPSourceData51) (F : R -> R) : Prop := {
  fig51_interval : SSC.g51_t0 D <= SSC.g51_t1 D;
  fig51_nu : 0 < SSC.g51_nu D;

  fig51_W_nonneg :
    forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
      0 <= SSC.g_W D t;

  fig51_mass_le_W :
    forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
      SSC.g_mass D t <= SSC.g_W D t;

  fig51_D_nonneg :
    forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
      0 <= SSC.g51_Dcum D t;

  fig51_combined_balance :
    forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
      SSC.g51_nu D * SSC.g_W D t
      + SSC.g51_nu D * SSC.g51_nu D * SSC.g51_Dcum D t
      <= SSC.g51_nu D * SSC.g_W D (SSC.g51_t0 D)
      + SSC.g51_Qcum D t + F t
}.

Definition forced_closure_mass51 D (Qi Qf : R) :=
  SSC.g_W D (SSC.g51_t0 D) + (Qi + Qf) / SSC.g51_nu D.

Definition forced_closure_diss51 D theta_i theta_f Qi Qf :=
  forced_closure_mass51 D Qi Qf /
    (SSC.g51_nu D * (1 - (theta_i + theta_f))).

Theorem GFC20_TOTAL_BUDGET_ABSORBS :
  forall D F theta Qstar t,
    ForcedIntegratedGPLedger51 D F ->
    0 <= theta -> theta < 1 -> 0 <= Qstar ->
    GPTotalProductionBudget51 D F theta Qstar ->
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    SSC.g_W D t +
      SSC.g51_nu D * (1-theta) * SSC.g51_Dcum D t
    <= SSC.g_W D (SSC.g51_t0 D) + Qstar / SSC.g51_nu D.
Proof.
  intros D F theta Qstar t HL Hth Hth1 HQ HB Ht.
  pose proof (fig51_combined_balance D F HL t Ht) as Hbal.
  pose proof (HB t Ht) as Hprod.
  apply (Rmult_le_reg_l (SSC.g51_nu D)); [exact (fig51_nu D F HL)|].
  replace (SSC.g51_nu D *
    (SSC.g_W D (SSC.g51_t0 D) + Qstar / SSC.g51_nu D)) with
    (SSC.g51_nu D * SSC.g_W D (SSC.g51_t0 D) + Qstar)
    by (field; pose proof (fig51_nu D F HL); lra).
  nra.
Qed.

Theorem GFC21_SAFE_FORCING_GIVES_CRITICAL_BOUNDS :
  forall D f F theta_i Qi theta_f Qf t,
    ForcedIntegratedGPLedger51 D F ->
    GPRegularitySafeForcing51 D f F theta_i Qi theta_f Qf ->
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    0 <= forced_closure_mass51 D Qi Qf /\
    0 <= forced_closure_diss51 D theta_i theta_f Qi Qf /\
    SSC.g_mass D t <= forced_closure_mass51 D Qi Qf /\
    SSC.g51_Dcum D t <= forced_closure_diss51 D theta_i theta_f Qi Qf.
Proof.
  intros D f F theta_i Qi theta_f Qf t HL Hsafe Ht.
  unfold GPRegularitySafeForcing51 in Hsafe.
  destruct Hsafe as [Hti [Htf [Hsum [HQi [HQf [Hint Hext]]]]]].
  assert (Htheta0 : 0 <= theta_i + theta_f) by nra.
  assert (HQ : 0 <= Qi + Qf) by nra.
  assert (HT : GPTotalProductionBudget51 D F
      (theta_i+theta_f) (Qi+Qf)).
  { exact (GFC10_INTERNAL_PLUS_EXTERNAL_RELATIVE_BUDGETS_ADD
      D f F theta_i Qi theta_f Qf Hint Hext). }
  pose proof (GFC20_TOTAL_BUDGET_ABSORBS D F
    (theta_i+theta_f) (Qi+Qf) t HL Htheta0 Hsum HQ HT Ht) as Habs.
  assert (Hnu : 0 < SSC.g51_nu D) by exact (fig51_nu D F HL).
  assert (He : 0 < SSC.g51_nu D * (1-(theta_i+theta_f))) by nra.
  assert (HM0 : 0 <= forced_closure_mass51 D Qi Qf).
  { unfold forced_closure_mass51.
    pose proof (fig51_W_nonneg D F HL (SSC.g51_t0 D)) as HW0.
    assert (Ht0 : InTime (SSC.g51_t0 D) (SSC.g51_t1 D) (SSC.g51_t0 D)).
    { unfold InTime; pose proof (fig51_interval D F HL); lra. }
    specialize (HW0 Ht0).
    assert (Hqdiv : 0 <= (Qi+Qf)/SSC.g51_nu D).
    { unfold Rdiv; apply Rmult_le_pos; [exact HQ|].
      apply Rlt_le; apply Rinv_0_lt_compat; exact Hnu. }
    lra. }
  assert (HD0 : 0 <= forced_closure_diss51 D theta_i theta_f Qi Qf).
  { unfold forced_closure_diss51, Rdiv.
    apply Rmult_le_pos; [exact HM0|].
    apply Rlt_le; apply Rinv_0_lt_compat; exact He. }
  assert (HDt : 0 <= SSC.g51_Dcum D t) by exact (fig51_D_nonneg D F HL t Ht).
  assert (Hnon : 0 <= SSC.g51_nu D * (1-(theta_i+theta_f)) * SSC.g51_Dcum D t).
  { apply Rmult_le_pos; [apply Rlt_le; exact He|exact HDt]. }
  assert (HWt : 0 <= SSC.g_W D t) by exact (fig51_W_nonneg D F HL t Ht).
  assert (Hm : SSC.g_mass D t <= forced_closure_mass51 D Qi Qf).
  { pose proof (fig51_mass_le_W D F HL t Ht) as HmW.
    unfold forced_closure_mass51 in *; nra. }
  assert (Hd : SSC.g51_Dcum D t <= forced_closure_diss51 D theta_i theta_f Qi Qf).
  { apply (Rmult_le_reg_l (SSC.g51_nu D * (1-(theta_i+theta_f)))); [exact He|].
    unfold forced_closure_diss51.
    replace ((SSC.g51_nu D * (1-(theta_i+theta_f))) *
      (forced_closure_mass51 D Qi Qf /
        (SSC.g51_nu D * (1-(theta_i+theta_f))))) with
      (forced_closure_mass51 D Qi Qf) by (field; lra).
    unfold forced_closure_mass51 in Habs; nra. }
  exact (conj HM0 (conj HD0 (conj Hm Hd))).
Qed.

(* Zero external forcing recovers exactly the old unforced constants. *)
Theorem GFC30_ZERO_EXTERNAL_RECOVERS_UNFORCED_MASS_CONSTANT :
  forall D theta_i Qi,
    forced_closure_mass51 D Qi 0 = SSC.closure_mass51 D theta_i Qi.
Proof.
  intros D theta_i Qi.
  unfold forced_closure_mass51, SSC.closure_mass51.
  replace (Qi + 0) with Qi by ring; reflexivity.
Qed.

Theorem GFC31_ZERO_EXTERNAL_RECOVERS_UNFORCED_DISS_CONSTANT :
  forall D theta_i Qi,
    forced_closure_diss51 D theta_i 0 Qi 0 =
      SSC.closure_diss51 D theta_i Qi.
Proof.
  intros D theta_i Qi.
  unfold forced_closure_diss51, SSC.closure_diss51.
  rewrite GFC30_ZERO_EXTERNAL_RECOVERS_UNFORCED_MASS_CONSTANT.
  replace (theta_i + 0) with theta_i by ring; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Claim boundary / calibration markers.                               *)
(* ------------------------------------------------------------------ *)

Definition ForcingClassTrajectoryDependent : Prop := True.
Definition OrdinaryNormOnlyClassificationNotClaimed : Prop := True.
Definition TimeIntegrabilityAloneNotClaimedSufficient : Prop := True.
Definition SmoothForcingAloneNotClaimedSufficient : Prop := True.

Definition STATUS : string :=
  "NSE_GP_FORCING_CLASSIFICATION_V0_1_0_TRAJECTORY_RELATIVE_GP_BUDGET_AND_SUBUNIT_MARGIN_NO_ADMITTED"%string.

End NSE_GP_FORCING_CLASSIFICATION.

Check NSE_GP_FORCING_CLASSIFICATION.GFC00_LITERAL_ZERO_FORCE_IS_GP_NULL.
Check NSE_GP_FORCING_CLASSIFICATION.GFC02_LITERAL_ZERO_FORCE_IS_RELATIVE_ZERO.
Check NSE_GP_FORCING_CLASSIFICATION.GFC10_INTERNAL_PLUS_EXTERNAL_RELATIVE_BUDGETS_ADD.
Check NSE_GP_FORCING_CLASSIFICATION.GFC12_ZERO_FORCE_IS_SAFE_WHEN_INTERNAL_MARGIN_IS_SUBUNIT.
Check NSE_GP_FORCING_CLASSIFICATION.GFC13_FINITE_GP_WORK_PRESERVES_INTERNAL_SUBUNIT_MARGIN.
Check NSE_GP_FORCING_CLASSIFICATION.GFC11_SAFE_FORCING_HAS_SUBUNIT_TOTAL_BUDGET.
Check NSE_GP_FORCING_CLASSIFICATION.GFC21_SAFE_FORCING_GIVES_CRITICAL_BOUNDS.
Check NSE_GP_FORCING_CLASSIFICATION.GFC30_ZERO_EXTERNAL_RECOVERS_UNFORCED_MASS_CONSTANT.
Check NSE_GP_FORCING_CLASSIFICATION.GFC31_ZERO_EXTERNAL_RECOVERS_UNFORCED_DISS_CONSTANT.

Print Assumptions NSE_GP_FORCING_CLASSIFICATION.GFC02_LITERAL_ZERO_FORCE_IS_RELATIVE_ZERO.
Print Assumptions NSE_GP_FORCING_CLASSIFICATION.GFC10_INTERNAL_PLUS_EXTERNAL_RELATIVE_BUDGETS_ADD.
Print Assumptions NSE_GP_FORCING_CLASSIFICATION.GFC21_SAFE_FORCING_GIVES_CRITICAL_BOUNDS.
