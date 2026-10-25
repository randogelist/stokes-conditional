From Stdlib Require Import Reals String Lra Psatz Field Lia.
Require Import awpi_nse_gp_ae_modal_semantics_v0_23_1.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_gp_source_storage_dynamics_v0_51_0.
Require Import awpi_nse_gp_signed_source_closure_v0_51_0.
Require Import awpi_nse_gp_source_m7_energy_join_v0_51_0.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.
Require Import awpi_nse_gp_unforced_lh_ae_source_entrance_v0_1_1.

Module NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.
Module AE := NSE_GP_AE_MODAL_SEMANTICS.
Module SSC := NSE_GP_SIGNED_SOURCE_CLOSURE.
Module UAE := NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.
Module Join := NSE_GP_SOURCE_M7_ENERGY_JOIN.
Module Spine := NSE_GP_TO_M7_SPINE.
Module Energy := NSE_M7_CRITICAL_ENERGY_INJECTION.
Import NSE_KQ_FINITE_ALGEBRA NSE_GP_SOURCE_STORAGE_DYNAMICS NSE_CONTINUOUS_TIME_CALCULUS.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* LH-compatible integrated ledger interface.                          *)
(*                                                                    *)
(* This record contains only the endpoint consequences supplied by     *)
(* the standard AC/a.e. fundamental theorem.  It DOES NOT require the  *)
(* everywhere-classical ModalPath / PrimitiveOn witness used by        *)
(* GPSourceWitness51.  Consequently all downstream M7 energy algebra   *)
(* can now consume a genuinely a.e.-compatible object.                 *)
(* ------------------------------------------------------------------ *)

Record AEIntegratedLedger51
  (CoNull : (R -> Prop) -> Prop)
  (D : SSC.GPSourceData51)
  (A : UAE.AEGPTimeData51 D) : Prop := {
  ail51_local : UAE.AEGPSourceWitness51 CoNull D A;

  ail51_R0 : SSC.g51_Rcum D (SSC.g51_t0 D) = 0;
  ail51_D0 : SSC.g51_Dcum D (SSC.g51_t0 D) = 0;
  ail51_Q0 : SSC.g51_Qcum D (SSC.g51_t0 D) = 0;

  ail51_R_nonneg :
    forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
      0 <= SSC.g51_Rcum D t;

  ail51_D_nonneg :
    forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
      0 <= SSC.g51_Dcum D t;

  ail51_R_mono :
    forall s t,
      InTime (SSC.g51_t0 D) (SSC.g51_t1 D) s ->
      InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
      s <= t ->
      SSC.g51_Rcum D s <= SSC.g51_Rcum D t;

  ail51_source_balance :
    forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
      SSC.g_H D t + SSC.g51_Rcum D t <=
      SSC.g_H D (SSC.g51_t0 D) + SSC.g51_Qcum D t;

  ail51_critical_balance :
    forall t, InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
      SSC.g51_nu D * SSC.g_mass D t
      + SSC.g51_nu D * SSC.g51_nu D * SSC.g51_Dcum D t
      <=
      SSC.g51_nu D * SSC.g_mass D (SSC.g51_t0 D)
      + SSC.g51_Rcum D t
}.

Lemma UAI00_LOCAL_WITNESS :
  forall CoNull D A,
    AEIntegratedLedger51 CoNull D A ->
    UAE.AEGPSourceWitness51 CoNull D A.
Proof. intros CoNull D A H; exact (ail51_local CoNull D A H). Qed.

Theorem UAI01_NONNEGATIVE_PHYSICAL_QUANTITIES :
  forall CoNull D A,
  forall HW : AEIntegratedLedger51 CoNull D A,
  forall t,
    0 <= SSC.g_H D t /\
    0 <= SSC.g_R D t /\
    0 <= SSC.g_mass D t /\
    0 <= SSC.g_diss D t.
Proof.
  intros CoNull D A HW t.
  pose proof (ail51_local CoNull D A HW) as Hloc.
  exact (NSSD10_STORAGE_AND_RATES_NONNEGATIVE
    (SSC.g51_packets D) (SSC.g51_nu D) (SSC.g51_Z D) (SSC.g51_u D t)
    (UAE.aew51_nu CoNull D A Hloc)
    (UAE.aew51_Z CoNull D A Hloc)
    (UAE.aew51_indices CoNull D A Hloc)
    (UAE.aew51_positive CoNull D A Hloc)).
Qed.

Lemma UAI02_COMBINED_STORAGE_BOUNDS :
  forall CoNull D A,
  forall HW : AEIntegratedLedger51 CoNull D A,
  forall t,
    0 <= SSC.g_W D t /\ SSC.g_mass D t <= SSC.g_W D t.
Proof.
  intros CoNull D A HW t.
  pose proof (ail51_local CoNull D A HW) as Hloc.
  destruct (UAI01_NONNEGATIVE_PHYSICAL_QUANTITIES CoNull D A HW t)
    as [HH [HR [Hm Hd]]].
  assert (Hx : 0 <= SSC.g_H D t / SSC.g51_nu D).
  { unfold Rdiv; apply Rmult_le_pos; [exact HH|].
    apply Rlt_le; apply Rinv_0_lt_compat.
    exact (UAE.aew51_nu CoNull D A Hloc). }
  change (0 <= SSC.g_mass D t + SSC.g_H D t / SSC.g51_nu D /\
    SSC.g_mass D t <= SSC.g_mass D t + SSC.g_H D t / SSC.g51_nu D).
  lra.
Qed.

(* The two integrated ledgers combine exactly as in the classical donor. *)
Theorem UAI10_AE_INTEGRATED_COUPLED_BALANCE :
  forall CoNull D A,
  forall HW : AEIntegratedLedger51 CoNull D A,
  forall t,
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    SSC.g51_nu D * SSC.g_W D t
    + SSC.g51_nu D * SSC.g51_nu D * SSC.g51_Dcum D t
    <=
    SSC.g51_nu D * SSC.g_W D (SSC.g51_t0 D)
    + SSC.g51_Qcum D t.
Proof.
  intros CoNull D A HW t Ht.
  pose proof (ail51_source_balance CoNull D A HW t Ht) as Hs.
  pose proof (ail51_critical_balance CoNull D A HW t Ht) as Hm.
  pose proof (ail51_local CoNull D A HW) as Hloc.
  assert (He : forall s,
    SSC.g51_nu D * SSC.g_W D s =
    SSC.g51_nu D * SSC.g_mass D s + SSC.g_H D s).
  { intro s.
    change (SSC.g51_nu D *
      (SSC.g_mass D s + SSC.g_H D s / SSC.g51_nu D) =
      SSC.g51_nu D * SSC.g_mass D s + SSC.g_H D s).
    field; pose proof (UAE.aew51_nu CoNull D A Hloc); lra. }
  rewrite !He; lra.
Qed.

Theorem UAI20_SIGNED_PRODUCTION_BUDGET_ABSORBS :
  forall CoNull D A theta Qstar t,
  forall HW : AEIntegratedLedger51 CoNull D A,
    0 <= theta -> theta < 1 -> 0 <= Qstar ->
    SSC.SignedProductionBudget51 D theta Qstar ->
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    SSC.g_W D t
      + SSC.g51_nu D * (1-theta) * SSC.g51_Dcum D t
      <= SSC.closure_mass51 D theta Qstar.
Proof.
  intros CoNull D A theta Qstar t HW Hth Hth1 HQ HB Ht.
  pose proof (UAI10_AE_INTEGRATED_COUPLED_BALANCE CoNull D A HW t Ht) as H.
  pose proof (HB t Ht) as Hp.
  pose proof (ail51_local CoNull D A HW) as Hloc.
  apply (Rmult_le_reg_l (SSC.g51_nu D));
    [exact (UAE.aew51_nu CoNull D A Hloc)|].
  unfold SSC.closure_mass51.
  replace (SSC.g51_nu D *
    (SSC.g_W D (SSC.g51_t0 D) + Qstar / SSC.g51_nu D)) with
    (SSC.g51_nu D * SSC.g_W D (SSC.g51_t0 D) + Qstar)
    by (field; pose proof (UAE.aew51_nu CoNull D A Hloc); lra).
  nra.
Qed.

Theorem UAI21_AE_CRITICAL_AND_SOURCE_BOUNDS :
  forall CoNull D A theta Qstar t,
  forall HW : AEIntegratedLedger51 CoNull D A,
    0 <= theta -> theta < 1 -> 0 <= Qstar ->
    SSC.SignedProductionBudget51 D theta Qstar ->
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    0 <= SSC.closure_mass51 D theta Qstar /\
    0 <= SSC.closure_diss51 D theta Qstar /\
    0 <= SSC.closure_source51 D theta Qstar /\
    SSC.g_mass D t <= SSC.closure_mass51 D theta Qstar /\
    SSC.g51_Dcum D t <= SSC.closure_diss51 D theta Qstar /\
    SSC.g51_Rcum D t <= SSC.closure_source51 D theta Qstar.
Proof.
  intros CoNull D A theta Qstar t HW Hth Hth1 HQ HB Ht.
  pose proof (ail51_local CoNull D A HW) as Hloc.
  pose proof (UAE.aew51_nu CoNull D A Hloc) as Hnu.
  assert (He : 0 < SSC.g51_nu D * (1-theta)) by nra.
  assert (HM : 0 <= SSC.closure_mass51 D theta Qstar).
  { unfold SSC.closure_mass51.
    pose proof (proj1 (UAI02_COMBINED_STORAGE_BOUNDS CoNull D A HW (SSC.g51_t0 D))) as HW0.
    assert (Hq : 0 <= Qstar / SSC.g51_nu D).
    { unfold Rdiv; apply Rmult_le_pos; [exact HQ|].
      apply Rlt_le; apply Rinv_0_lt_compat; exact Hnu. }
    lra. }
  assert (HD0 : 0 <= SSC.closure_diss51 D theta Qstar).
  { unfold SSC.closure_diss51, Rdiv; apply Rmult_le_pos; [exact HM|].
    apply Rlt_le; apply Rinv_0_lt_compat; exact He. }
  pose proof (Rlt_le 0 (SSC.g51_nu D) Hnu) as Hnu0.
  assert (Hcoef : 0 <= theta * SSC.g51_nu D * SSC.g51_nu D).
  { exact (Rmult_le_pos (theta * SSC.g51_nu D) (SSC.g51_nu D)
      (Rmult_le_pos theta (SSC.g51_nu D) Hth Hnu0) Hnu0). }
  assert (HP0 : 0 <= SSC.closure_source51 D theta Qstar).
  { pose proof (proj1 (UAI01_NONNEGATIVE_PHYSICAL_QUANTITIES
      CoNull D A HW (SSC.g51_t0 D))) as HH0.
    assert (Hprod : 0 <= theta * SSC.g51_nu D * SSC.g51_nu D
      * SSC.closure_diss51 D theta Qstar).
    { exact (Rmult_le_pos (theta * SSC.g51_nu D * SSC.g51_nu D)
        (SSC.closure_diss51 D theta Qstar) Hcoef HD0). }
    unfold SSC.closure_source51.
    exact (Rplus_le_le_0_compat (SSC.g_H D (SSC.g51_t0 D)+Qstar)
      (theta*SSC.g51_nu D*SSC.g51_nu D*SSC.closure_diss51 D theta Qstar)
      (Rplus_le_le_0_compat (SSC.g_H D (SSC.g51_t0 D)) Qstar HH0 HQ) Hprod). }
  pose proof (UAI20_SIGNED_PRODUCTION_BUDGET_ABSORBS
    CoNull D A theta Qstar t HW Hth Hth1 HQ HB Ht) as Hbal.
  destruct (UAI02_COMBINED_STORAGE_BOUNDS CoNull D A HW t) as [HW0 HmW].
  pose proof (ail51_R_nonneg CoNull D A HW t Ht) as HR0.
  pose proof (ail51_D_nonneg CoNull D A HW t Ht) as HD.
  assert (Hm : SSC.g_mass D t <= SSC.closure_mass51 D theta Qstar).
  { assert (Hx : 0 <= SSC.g51_nu D * (1-theta) * SSC.g51_Dcum D t).
    { exact (Rmult_le_pos (SSC.g51_nu D*(1-theta)) (SSC.g51_Dcum D t)
        (Rlt_le 0 (SSC.g51_nu D*(1-theta)) He) HD). }
    lra. }
  assert (Hd : SSC.g51_Dcum D t <= SSC.closure_diss51 D theta Qstar).
  { apply (Rmult_le_reg_l (SSC.g51_nu D*(1-theta))); [exact He|].
    unfold SSC.closure_diss51.
    replace ((SSC.g51_nu D*(1-theta)) *
      (SSC.closure_mass51 D theta Qstar /
       (SSC.g51_nu D*(1-theta)))) with
      (SSC.closure_mass51 D theta Qstar) by (field; lra).
    lra. }
  assert (Hr : SSC.g51_Rcum D t <= SSC.closure_source51 D theta Qstar).
  { pose proof (ail51_source_balance CoNull D A HW t Ht) as Hs.
    pose proof (HB t Ht) as Hq.
    pose proof (proj1 (UAI01_NONNEGATIVE_PHYSICAL_QUANTITIES CoNull D A HW t)) as HH.
    pose proof (Rmult_le_compat_l (theta*SSC.g51_nu D*SSC.g51_nu D)
      (SSC.g51_Dcum D t) (SSC.closure_diss51 D theta Qstar) Hcoef Hd).
    unfold SSC.closure_source51; lra. }
  exact (conj HM (conj HD0 (conj HP0 (conj Hm (conj Hd Hr))))).
Qed.

(* ------------------------------------------------------------------ *)
(* M7 sequence / critical-energy join without an everywhere derivative. *)
(* ------------------------------------------------------------------ *)

Theorem UAI30_AE_CELL_PREFIX_IS_CUMULATIVE :
  forall CoNull D A grid N,
  forall HW : AEIntegratedLedger51 CoNull D A,
    Join.SourceGrid51 D grid ->
    Spine.resistant_prefix (Join.source_cell51 D grid) N =
      SSC.g51_Rcum D (grid N).
Proof.
  intros CoNull D A grid N HW [Hg0 [Hgt Hgm]].
  rewrite Join.spine_prefix_is_sum51.
  unfold Join.source_cell51.
  transitivity (SSC.g51_Rcum D (grid N) - SSC.g51_Rcum D (grid O)).
  - exact (sum_telescoping N (fun k : nat => SSC.g51_Rcum D (grid k))).
  - rewrite Hg0, (ail51_R0 CoNull D A HW); ring.
Qed.

Theorem UAI31_AE_NORMALIZED_CELL_PREFIX_IS_ACTION_COST :
  forall CoNull D A grid N,
  forall HW : AEIntegratedLedger51 CoNull D A,
    Join.SourceGrid51 D grid ->
    Spine.resistant_prefix (Join.normalized_source_cell51 D grid) N =
      SSC.g51_Rcum D (grid N) / SSC.g51_nu D.
Proof.
  intros CoNull D A grid N HW HG.
  rewrite Join.spine_prefix_is_sum51.
  unfold Join.normalized_source_cell51, Rdiv.
  transitivity ((/SSC.g51_nu D) * sum N (Join.source_cell51 D grid)).
  - rewrite <- sum_scale; apply sum_ext; intros; ring.
  - rewrite <- Join.spine_prefix_is_sum51,
      (UAI30_AE_CELL_PREFIX_IS_CUMULATIVE CoNull D A grid N HW HG); ring.
Qed.

Theorem UAI32_AE_SOURCE_CELLS_NONNEGATIVE :
  forall CoNull D A grid,
  forall HW : AEIntegratedLedger51 CoNull D A,
    Join.SourceGrid51 D grid ->
    forall n,
      0 <= Join.source_cell51 D grid n /\
      0 <= Join.normalized_source_cell51 D grid n.
Proof.
  intros CoNull D A grid HW HG n.
  destruct HG as [Hg0 [Hgt Hgm]].
  assert (Hr : SSC.g51_Rcum D (grid n) <= SSC.g51_Rcum D (grid (S n))).
  { apply (ail51_R_mono CoNull D A HW (grid n) (grid (S n))).
    - exact (Hgt n).
    - exact (Hgt (S n)).
    - exact (Hgm n). }
  assert (Hcell : 0 <= Join.source_cell51 D grid n)
    by (unfold Join.source_cell51; lra).
  split; [exact Hcell|].
  unfold Join.normalized_source_cell51, Rdiv; apply Rmult_le_pos; [exact Hcell|].
  apply Rlt_le; apply Rinv_0_lt_compat.
  pose proof (ail51_local CoNull D A HW) as Hloc.
  exact (UAE.aew51_nu CoNull D A Hloc).
Qed.

Theorem UAI33_AE_SIGNED_PAYMENT_GIVES_SEQUENCE_M7 :
  forall CoNull D A theta Qstar grid,
  forall HW : AEIntegratedLedger51 CoNull D A,
    0 <= theta -> theta < 1 -> 0 <= Qstar ->
    SSC.SignedProductionBudget51 D theta Qstar ->
    Join.SourceGrid51 D grid ->
    Spine.GPSequenceM7 (Join.source_cell51 D grid) /\
    Spine.GPSequenceM7 (Join.normalized_source_cell51 D grid).
Proof.
  intros CoNull D A theta Qstar grid HW Hth Hth1 HQ HB HG.
  assert (HT0 : InTime (SSC.g51_t0 D) (SSC.g51_t1 D) (grid O))
    by exact (proj1 (proj2 HG) O).
  destruct (UAI21_AE_CRITICAL_AND_SOURCE_BOUNDS
    CoNull D A theta Qstar (grid O) HW Hth Hth1 HQ HB HT0)
    as [HM [HD [HP Hrest]]].
  split.
  - exists (SSC.closure_source51 D theta Qstar); split; [exact HP|].
    intro N.
    rewrite (UAI30_AE_CELL_PREFIX_IS_CUMULATIVE CoNull D A grid N HW HG).
    exact (proj2 (proj2 (proj2 (proj2 (proj2
      (UAI21_AE_CRITICAL_AND_SOURCE_BOUNDS CoNull D A theta Qstar (grid N)
        HW Hth Hth1 HQ HB (proj1 (proj2 HG) N))))))).
  - exists (SSC.closure_source51 D theta Qstar / SSC.g51_nu D); split.
    + unfold Rdiv; apply Rmult_le_pos; [exact HP|].
      apply Rlt_le; apply Rinv_0_lt_compat.
      pose proof (ail51_local CoNull D A HW) as Hloc.
      exact (UAE.aew51_nu CoNull D A Hloc).
    + intro N.
      rewrite (UAI31_AE_NORMALIZED_CELL_PREFIX_IS_ACTION_COST CoNull D A grid N HW HG).
      unfold Rdiv; apply Rmult_le_compat_r.
      * apply Rlt_le; apply Rinv_0_lt_compat.
        pose proof (ail51_local CoNull D A HW) as Hloc.
        exact (UAE.aew51_nu CoNull D A Hloc).
      * exact (proj2 (proj2 (proj2 (proj2 (proj2
          (UAI21_AE_CRITICAL_AND_SOURCE_BOUNDS CoNull D A theta Qstar (grid N)
            HW Hth Hth1 HQ HB (proj1 (proj2 HG) N))))))).
Qed.

Theorem UAI34_AE_CONSTRUCT_CRITICAL_ENERGY_BALANCE :
  forall CoNull D A grid,
  forall HW : AEIntegratedLedger51 CoNull D A,
    Join.SourceGrid51 D grid ->
    Energy.CriticalEnergyBalance nat (SSC.g51_nu D) 0
      (SSC.g_mass D (SSC.g51_t0 D))
      (fun n => SSC.g_mass D (grid n))
      (fun n => SSC.g51_Dcum D (grid n))
      (fun n => SSC.g51_Rcum D (grid n) / SSC.g51_nu D).
Proof.
  intros CoNull D A grid HW HG; constructor.
  - pose proof (ail51_local CoNull D A HW) as Hloc.
    exact (UAE.aew51_nu CoNull D A Hloc).
  - lra.
  - lra.
  - exact (proj1 (proj2 (proj2
      (UAI01_NONNEGATIVE_PHYSICAL_QUANTITIES CoNull D A HW (SSC.g51_t0 D))))).
  - intro n.
    exact (proj1 (proj2 (proj2
      (UAI01_NONNEGATIVE_PHYSICAL_QUANTITIES CoNull D A HW (grid n))))).
  - intro n; exact (ail51_D_nonneg CoNull D A HW (grid n) (proj1 (proj2 HG) n)).
  - intro n; unfold Rdiv; apply Rmult_le_pos.
    + exact (ail51_R_nonneg CoNull D A HW (grid n) (proj1 (proj2 HG) n)).
    + apply Rlt_le; apply Rinv_0_lt_compat.
      pose proof (ail51_local CoNull D A HW) as Hloc.
      exact (UAE.aew51_nu CoNull D A Hloc).
  - intro n.
    pose proof (ail51_critical_balance CoNull D A HW (grid n) (proj1 (proj2 HG) n)) as H.
    unfold Energy.effective_viscosity.
    pose proof (ail51_local CoNull D A HW) as Hloc.
    apply (Rmult_le_reg_l (SSC.g51_nu D));
      [exact (UAE.aew51_nu CoNull D A Hloc)|].
    replace (SSC.g51_nu D *
      (SSC.g_mass D (SSC.g51_t0 D)
       + SSC.g51_Rcum D (grid n) / SSC.g51_nu D)) with
      (SSC.g51_nu D * SSC.g_mass D (SSC.g51_t0 D)
       + SSC.g51_Rcum D (grid n))
      by (field; pose proof (UAE.aew51_nu CoNull D A Hloc); lra).
    nra.
Qed.

Theorem UAI35_AE_CONSTRUCT_ACTION_COST_REALIZATION :
  forall CoNull D A grid,
  forall HW : AEIntegratedLedger51 CoNull D A,
    Join.SourceGrid51 D grid ->
    Energy.M7ActionCostRealization nat
      (Join.normalized_source_cell51 D grid)
      (fun n => SSC.g51_Rcum D (grid n) / SSC.g51_nu D).
Proof.
  intros CoNull D A grid HW HG n; exists n.
  rewrite (UAI31_AE_NORMALIZED_CELL_PREFIX_IS_ACTION_COST CoNull D A grid n HW HG).
  apply Rle_refl.
Qed.

Theorem UAI40_AE_INTEGRATED_SOURCE_TO_M7_CRITICAL_TARGET :
  forall CoNull D A theta Qstar grid,
  forall HW : AEIntegratedLedger51 CoNull D A,
    0 <= theta -> theta < 1 -> 0 <= Qstar ->
    SSC.SignedProductionBudget51 D theta Qstar ->
    Join.SourceGrid51 D grid ->
    Spine.GPSequenceM7 (Join.source_cell51 D grid) /\
    Energy.CriticalH12Bound nat (fun n => SSC.g_mass D (grid n)) /\
    Energy.CriticalH32Dissipation nat (fun n => SSC.g51_Dcum D (grid n)).
Proof.
  intros CoNull D A theta Qstar grid HW Hth Hth1 HQ HB HG.
  destruct (UAI33_AE_SIGNED_PAYMENT_GIVES_SEQUENCE_M7
    CoNull D A theta Qstar grid HW Hth Hth1 HQ HB HG) as [HR HN].
  split; [exact HR|].
  exact (Energy.NSCE90_M7_INJECTS_INTO_CRITICAL_ENERGY_TARGET
    nat (Join.normalized_source_cell51 D grid) (SSC.g51_nu D) 0
    (SSC.g_mass D (SSC.g51_t0 D))
    (fun n => SSC.g_mass D (grid n))
    (fun n => SSC.g51_Dcum D (grid n))
    (fun n => SSC.g51_Rcum D (grid n) / SSC.g51_nu D)
    HN
    (UAI35_AE_CONSTRUCT_ACTION_COST_REALIZATION CoNull D A grid HW HG)
    (UAI34_AE_CONSTRUCT_CRITICAL_ENERGY_BALANCE CoNull D A grid HW HG)).
Qed.

Definition AETimePoint51 D := {t : R | InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t}.

Theorem UAI50_ALL_AE_INTEGRATED_ENDPOINTS_CRITICAL_BOUND :
  forall CoNull D A theta Qstar,
  forall HW : AEIntegratedLedger51 CoNull D A,
    0 <= theta -> theta < 1 -> 0 <= Qstar ->
    SSC.SignedProductionBudget51 D theta Qstar ->
    Energy.UniformCriticalEnergy (AETimePoint51 D)
      (fun t => SSC.g_mass D (proj1_sig t))
      (fun t => SSC.g51_Dcum D (proj1_sig t)).
Proof.
  intros CoNull D A theta Qstar HW Hth Hth1 HQ HB.
  pose proof (ail51_local CoNull D A HW) as Hloc.
  assert (Ht0 : InTime (SSC.g51_t0 D) (SSC.g51_t1 D) (SSC.g51_t0 D)).
  { unfold InTime; pose proof (UAE.aew51_order CoNull D A Hloc); lra. }
  destruct (UAI21_AE_CRITICAL_AND_SOURCE_BOUNDS
    CoNull D A theta Qstar (SSC.g51_t0 D) HW Hth Hth1 HQ HB Ht0)
    as [HM [HD Hrest]].
  exists (SSC.closure_mass51 D theta Qstar), (SSC.closure_diss51 D theta Qstar).
  split; [exact HM|]; split; [exact HD|]; split.
  - intros [t Ht]; cbn.
    destruct (UAI21_AE_CRITICAL_AND_SOURCE_BOUNDS
      CoNull D A theta Qstar t HW Hth Hth1 HQ HB Ht)
      as [HMt [HDt [HRt [Hmt [Hdt Hrt]]]]]; exact Hmt.
  - intros [t Ht]; cbn.
    destruct (UAI21_AE_CRITICAL_AND_SOURCE_BOUNDS
      CoNull D A theta Qstar t HW Hth Hth1 HQ HB Ht)
      as [HMt [HDt [HRt [Hmt [Hdt Hrt]]]]]; exact Hdt.
Qed.

(* ------------------------------------------------------------------ *)
(* Exact claim boundary after retargeting the downstream proof to a.e.  *)
(* semantics.  The standard AC/a.e. theorem now has ONE job: construct  *)
(* AEIntegratedLedger51 from AEGPSourceWitness51.                       *)
(* ------------------------------------------------------------------ *)

Definition AELedgerFTCFrontier51
  (CoNull : (R -> Prop) -> Prop) : Prop :=
  forall D A,
    UAE.AEGPSourceWitness51 CoNull D A ->
    exists H : AEIntegratedLedger51 CoNull D A, True.

Definition LHWeakToAESourceWitnessFrontier51 : Prop := True.
Definition InternalSignedProductionFrontier51 : Prop := True.

Definition STATUS : string :=
  "NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE_V0_1_2_AE_DOWNSTREAM_M7_RETARGETED_TO_INTEGRATED_LH_COMPATIBLE_LEDGER_AC_FTC_AND_INTERNAL_PAYMENT_EXPLICIT_FRONTIERS_NO_ADMITTED"%string.

End NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.

Check NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.AEIntegratedLedger51.
Check NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI10_AE_INTEGRATED_COUPLED_BALANCE.
Check NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI20_SIGNED_PRODUCTION_BUDGET_ABSORBS.
Check NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI21_AE_CRITICAL_AND_SOURCE_BOUNDS.
Check NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI30_AE_CELL_PREFIX_IS_CUMULATIVE.
Check NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI33_AE_SIGNED_PAYMENT_GIVES_SEQUENCE_M7.
Check NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI34_AE_CONSTRUCT_CRITICAL_ENERGY_BALANCE.
Check NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI40_AE_INTEGRATED_SOURCE_TO_M7_CRITICAL_TARGET.
Check NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI50_ALL_AE_INTEGRATED_ENDPOINTS_CRITICAL_BOUND.

Print Assumptions NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI10_AE_INTEGRATED_COUPLED_BALANCE.
Print Assumptions NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI21_AE_CRITICAL_AND_SOURCE_BOUNDS.
Print Assumptions NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI40_AE_INTEGRATED_SOURCE_TO_M7_CRITICAL_TARGET.
Print Assumptions NSE_GP_UNFORCED_LH_AE_INTEGRATED_M7_BRIDGE.UAI50_ALL_AE_INTEGRATED_ENDPOINTS_CRITICAL_BOUND.
