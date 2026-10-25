From Stdlib Require Import Reals Ranalysis1 Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.
Require Import awpi_nse_gp_pair_source_calculus_v0_51_0.
Require Import awpi_nse_gp_fixed_allocation_v0_51_0.
Require Import awpi_nse_gp_source_storage_dynamics_v0_51_0.
Require Import awpi_nse_gp_signed_source_closure_v0_51_0.
Require Import awpi_nse_gp_quarter_shift_firewall_v0_13_6.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_GP_SOURCE_M7_ENERGY_JOIN.
Import NSE_KQ_FINITE_ALGEBRA NSE_CONTINUOUS_TIME_CALCULUS.
Import NSE_GALERKIN_MODAL_CALCULUS NSE_GP_PAIR_SOURCE_CALCULUS.
Import NSE_GP_FIXED_ALLOCATION NSE_GP_SOURCE_STORAGE_DYNAMICS NSE_GP_SIGNED_SOURCE_CLOSURE.
Module Spine := NSE_GP_TO_M7_SPINE.
Module Energy := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

Definition SourceGrid51 D (grid : nat -> R) : Prop :=
  grid O=g51_t0 D /\
  (forall n, InTime (g51_t0 D) (g51_t1 D) (grid n)) /\
  (forall n, grid n<=grid (S n)).
Definition source_cell51 D grid n :=
  g51_Rcum D (grid (S n))-g51_Rcum D (grid n).
Definition normalized_source_cell51 D grid n := source_cell51 D grid n/g51_nu D.

Lemma spine_prefix_is_sum51 : forall f N,
  Spine.resistant_prefix f N=sum N f.
Proof. intros f N; induction N; simpl; [reflexivity|rewrite IHN; reflexivity]. Qed.

Theorem NSSJ10_ACTUAL_CELL_PREFIX_IS_CUMULATIVE : forall D grid N,
  GPSourceWitness51 D -> SourceGrid51 D grid ->
  Spine.resistant_prefix (source_cell51 D grid) N=g51_Rcum D (grid N).
Proof.
  intros D grid N HW [Hg0 [Hgt Hgm]].
  rewrite spine_prefix_is_sum51; unfold source_cell51.
  (* Instantiate the sampled primitive explicitly.  A generic rewrite need
     not infer the composition of Rcum with the time grid. *)
  transitivity (g51_Rcum D (grid N)-g51_Rcum D (grid O)).
  - exact (sum_telescoping N (fun k : nat => g51_Rcum D (grid k))).
  - rewrite Hg0, (proj1 (gw51_R_primitive D HW)); ring.
Qed.

Theorem NSSJ11_NORMALIZED_CELL_PREFIX_IS_ACTION_COST : forall D grid N,
  GPSourceWitness51 D -> SourceGrid51 D grid ->
  Spine.resistant_prefix (normalized_source_cell51 D grid) N=
    g51_Rcum D (grid N)/g51_nu D.
Proof.
  intros D grid N HW HG.
  rewrite spine_prefix_is_sum51; unfold normalized_source_cell51, Rdiv.
  transitivity ((/g51_nu D)*sum N (source_cell51 D grid)).
  - rewrite <- sum_scale; apply sum_ext; intros; ring.
  - rewrite <- spine_prefix_is_sum51, (NSSJ10_ACTUAL_CELL_PREFIX_IS_CUMULATIVE D grid N HW HG); ring.
Qed.

Theorem NSSJ12_ACTUAL_SOURCE_CELLS_NONNEGATIVE : forall D grid,
  GPSourceWitness51 D -> SourceGrid51 D grid ->
  forall n, 0<=source_cell51 D grid n /\ 0<=normalized_source_cell51 D grid n.
Proof.
  intros D grid HW HG n.
  destruct HG as [Hg0 [Hgt Hgm]].
  assert (HD : DerivativeOn (grid n) (grid (S n)) (g51_Rcum D) (g_R D)).
  { intros t Ht; apply (proj2 (gw51_R_primitive D HW)).
    pose proof (Hgt n); pose proof (Hgt (S n)); unfold InTime in *; lra. }
  assert (Hr : g51_Rcum D (grid n)<=g51_Rcum D (grid (S n))).
  { apply (NSCT00_NONNEGATIVE_DERIVATIVE_GIVES_ORDER (grid n) (grid (S n))
      (g51_Rcum D) (g_R D) (Hgm n) HD).
    intros t Ht; exact (proj1 (proj2 (NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES D HW t))). }
  assert (Hcell : 0<=source_cell51 D grid n) by (unfold source_cell51; lra).
  split; [exact Hcell|].
  unfold normalized_source_cell51, Rdiv; apply Rmult_le_pos; [exact Hcell|].
  apply Rlt_le; apply Rinv_0_lt_compat; exact (gw51_nu D HW).
Qed.

Theorem NSSJ20_ACTUAL_SIGNED_PAYMENT_GIVES_SEQUENCE_M7 : forall D theta Qstar grid,
  GPSourceWitness51 D -> 0<=theta -> theta<1 -> 0<=Qstar ->
  SignedProductionBudget51 D theta Qstar -> SourceGrid51 D grid ->
  Spine.GPSequenceM7 (source_cell51 D grid) /\
  Spine.GPSequenceM7 (normalized_source_cell51 D grid).
Proof.
  intros D theta Qstar grid HW Hth Hth1 HQ HB HG.
  assert (HT0 : InTime (g51_t0 D) (g51_t1 D) (grid O)) by exact (proj1 (proj2 HG) O).
  destruct (NSSC31_CRITICAL_AND_SOURCE_BOUNDS D theta Qstar (grid O) HW Hth Hth1 HQ HB HT0)
    as [HM [HD [HP Hrest]]].
  split.
  - exists (closure_source51 D theta Qstar); split; [exact HP|].
    intro N; rewrite (NSSJ10_ACTUAL_CELL_PREFIX_IS_CUMULATIVE D grid N HW HG).
    exact (proj2 (proj2 (proj2 (proj2 (proj2
      (NSSC31_CRITICAL_AND_SOURCE_BOUNDS D theta Qstar (grid N)
        HW Hth Hth1 HQ HB (proj1 (proj2 HG) N))))))).
  - exists (closure_source51 D theta Qstar/g51_nu D); split.
    + unfold Rdiv; apply Rmult_le_pos; [exact HP|].
      apply Rlt_le; apply Rinv_0_lt_compat; exact (gw51_nu D HW).
    + intro N; rewrite (NSSJ11_NORMALIZED_CELL_PREFIX_IS_ACTION_COST D grid N HW HG).
      unfold Rdiv; apply Rmult_le_compat_r.
      * apply Rlt_le; apply Rinv_0_lt_compat; exact (gw51_nu D HW).
      * exact (proj2 (proj2 (proj2 (proj2 (proj2
          (NSSC31_CRITICAL_AND_SOURCE_BOUNDS D theta Qstar (grid N)
            HW Hth Hth1 HQ HB (proj1 (proj2 HG) N))))))).
Qed.

(* This constructs the donor's critical balance from the same modal path;
   the balance is not an input field of GPSourceWitness51. *)
Theorem NSSJ30_CONSTRUCT_EXISTING_CRITICAL_ENERGY_BALANCE : forall D grid,
  GPSourceWitness51 D -> SourceGrid51 D grid ->
  Energy.CriticalEnergyBalance nat (g51_nu D) 0 (g_mass D (g51_t0 D))
    (fun n => g_mass D (grid n)) (fun n => g51_Dcum D (grid n))
    (fun n => g51_Rcum D (grid n)/g51_nu D).
Proof.
  intros D grid HW HG; constructor.
  - exact (gw51_nu D HW).
  - lra.
  - lra.
  - exact (proj1 (proj2 (proj2 (NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES D HW (g51_t0 D))))).
  - intro n; exact (proj1 (proj2 (proj2 (NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES D HW (grid n))))).
  - intro n; exact (proj2 (NSSC02_NONNEGATIVE_ACTUAL_CUMULATIVES D (grid n) HW (proj1 (proj2 HG) n))).
  - intro n; unfold Rdiv; apply Rmult_le_pos.
    + exact (proj1 (NSSC02_NONNEGATIVE_ACTUAL_CUMULATIVES D (grid n) HW (proj1 (proj2 HG) n))).
    + apply Rlt_le; apply Rinv_0_lt_compat; exact (gw51_nu D HW).
  - intro n; pose proof (NSSC20_ACTUAL_CRITICAL_INTEGRATED_BALANCE D (grid n) HW (proj1 (proj2 HG) n)) as H.
    unfold Energy.effective_viscosity.
    apply (Rmult_le_reg_l (g51_nu D)); [exact (gw51_nu D HW)|].
    replace (g51_nu D*(g_mass D (g51_t0 D)+g51_Rcum D (grid n)/g51_nu D)) with
      (g51_nu D*g_mass D (g51_t0 D)+g51_Rcum D (grid n))
      by (field; pose proof (gw51_nu D HW); lra).
    nra.
Qed.

Theorem NSSJ31_CONSTRUCT_EXISTING_ACTION_COST_REALIZATION : forall D grid,
  GPSourceWitness51 D -> SourceGrid51 D grid ->
  Energy.M7ActionCostRealization nat (normalized_source_cell51 D grid)
    (fun n => g51_Rcum D (grid n)/g51_nu D).
Proof.
  intros D grid HW HG n; exists n.
  rewrite (NSSJ11_NORMALIZED_CELL_PREFIX_IS_ACTION_COST D grid n HW HG); apply Rle_refl.
Qed.

Theorem NSSJ40_DIRECT_GP_SOURCE_TO_EXISTING_M7_CRITICAL_TARGET : forall D theta Qstar grid,
  GPSourceWitness51 D -> 0<=theta -> theta<1 -> 0<=Qstar ->
  SignedProductionBudget51 D theta Qstar -> SourceGrid51 D grid ->
  Spine.GPSequenceM7 (source_cell51 D grid) /\
  Energy.CriticalH12Bound nat (fun n => g_mass D (grid n)) /\
  Energy.CriticalH32Dissipation nat (fun n => g51_Dcum D (grid n)).
Proof.
  intros D theta Qstar grid HW Hth Hth1 HQ HB HG.
  destruct (NSSJ20_ACTUAL_SIGNED_PAYMENT_GIVES_SEQUENCE_M7 D theta Qstar grid HW Hth Hth1 HQ HB HG)
    as [HR HN].
  split; [exact HR|].
  exact (Energy.NSCE90_M7_INJECTS_INTO_CRITICAL_ENERGY_TARGET
    nat (normalized_source_cell51 D grid) (g51_nu D) 0 (g_mass D (g51_t0 D))
    (fun n => g_mass D (grid n)) (fun n => g51_Dcum D (grid n))
    (fun n => g51_Rcum D (grid n)/g51_nu D) HN
    (NSSJ31_CONSTRUCT_EXISTING_ACTION_COST_REALIZATION D grid HW HG)
    (NSSJ30_CONSTRUCT_EXISTING_CRITICAL_ENERGY_BALANCE D grid HW HG)).
Qed.

(* Unlike grid-only statements, this controls every real endpoint in the
   interval.  No assertion that the grid covers an arbitrary time is used. *)
Definition TimePoint51 D := {t : R | InTime (g51_t0 D) (g51_t1 D) t}.
Theorem NSSJ50_ALL_CONTINUOUS_ENDPOINTS_CRITICAL_BOUND : forall D theta Qstar,
  GPSourceWitness51 D -> 0<=theta -> theta<1 -> 0<=Qstar ->
  SignedProductionBudget51 D theta Qstar ->
  Energy.UniformCriticalEnergy (TimePoint51 D)
    (fun t => g_mass D (proj1_sig t)) (fun t => g51_Dcum D (proj1_sig t)).
Proof.
  intros D theta Qstar HW Hth Hth1 HQ HB.
  assert (Ht0 : InTime (g51_t0 D) (g51_t1 D) (g51_t0 D)).
  { unfold InTime; pose proof (gw51_order D HW); lra. }
  destruct (NSSC31_CRITICAL_AND_SOURCE_BOUNDS D theta Qstar (g51_t0 D) HW Hth Hth1 HQ HB Ht0)
    as [HM [HD Hrest]].
  exists (closure_mass51 D theta Qstar), (closure_diss51 D theta Qstar).
  split; [exact HM|]; split; [exact HD|]; split.
  - intros [t Ht]; cbn.
    destruct (NSSC31_CRITICAL_AND_SOURCE_BOUNDS D theta Qstar t HW Hth Hth1 HQ HB Ht)
      as [HMt [HDt [HRt [Hmt [Hdt Hrt]]]]]; exact Hmt.
  - intros [t Ht]; cbn.
    destruct (NSSC31_CRITICAL_AND_SOURCE_BOUNDS D theta Qstar t HW Hth Hth1 HQ HB Ht)
      as [HMt [HDt [HRt [Hmt [Hdt Hrt]]]]]; exact Hdt.
Qed.

(* Quantifiers are common-bound first, then arbitrary family index AND
   time.  No uniform bound at positive times is supplied in these inputs. *)
Theorem NSSJ60_COMMON_INITIAL_STORAGE_AND_SIGNED_PAYMENT :
  forall (Index : Type) (F : Index -> GPSourceData51) nu theta Qstar M0 H0,
  0<nu -> 0<=theta -> theta<1 -> 0<=Qstar -> 0<=M0 -> 0<=H0 ->
  (forall i, GPSourceWitness51 (F i)) ->
  (forall i, g51_nu (F i)=nu) ->
  (forall i, g_mass (F i) (g51_t0 (F i))<=M0) ->
  (forall i, g_H (F i) (g51_t0 (F i))<=H0) ->
  (forall i, SignedProductionBudget51 (F i) theta Qstar) ->
  exists B J Rmax,
    0<=B /\ 0<=J /\ 0<=Rmax /\
    forall i t, InTime (g51_t0 (F i)) (g51_t1 (F i)) t ->
      g_mass (F i) t<=B /\ g51_Dcum (F i) t<=J /\ g51_Rcum (F i) t<=Rmax.
Proof.
  intros Index F nu theta Qstar M0 H0 Hnu Hth Hth1 HQ HM HH HW Hnus Hm0 Hh0 Hpay.
  set (B := M0+(H0+Qstar)/nu).
  set (J := B/(nu*(1-theta))).
  set (Rmax := H0+Qstar+theta*nu*nu*J).
  assert (He : 0<nu*(1-theta)) by nra.
  assert (HB : 0<=B).
  { unfold B; assert (Hdiv : 0<=(H0+Qstar)/nu).
    { unfold Rdiv; apply Rmult_le_pos; [lra|].
      apply Rlt_le; apply Rinv_0_lt_compat; exact Hnu. } lra. }
  assert (HJ : 0<=J).
  { unfold J, Rdiv; apply Rmult_le_pos; [exact HB|].
    apply Rlt_le; apply Rinv_0_lt_compat; exact He. }
  (* Keep the established nonnegative bound J as one factor; do not
     unfold its quotient with repeated multiplication decomposition. *)
  pose proof (Rlt_le 0 nu Hnu) as Hnu0.
  assert (Hcoef : 0<=theta*nu*nu).
  { exact (Rmult_le_pos (theta*nu) nu
      (Rmult_le_pos theta nu Hth Hnu0) Hnu0). }
  assert (HR : 0<=Rmax).
  { assert (Hp : 0<=theta*nu*nu*J).
    { exact (Rmult_le_pos (theta*nu*nu) J Hcoef HJ). }
    unfold Rmax.
    exact (Rplus_le_le_0_compat (H0+Qstar) (theta*nu*nu*J)
      (Rplus_le_le_0_compat H0 Qstar HH HQ) Hp). }
  exists B, J, Rmax; split; [exact HB|]; split; [exact HJ|]; split; [exact HR|].
  intros i t Ht.
  pose proof (NSSC21_ACTUAL_COUPLED_INTEGRATED_BALANCE (F i) t (HW i) Ht) as Hbal.
  pose proof (Hpay i t Ht) as Hq.
  destruct (combined_storage_bounds51 (F i) (HW i) t) as [HWt HmWt].
  destruct (NSSC02_NONNEGATIVE_ACTUAL_CUMULATIVES (F i) t (HW i) Ht) as [HRt HDt].
  assert (Hinit : nu*g_W (F i) (g51_t0 (F i))<=nu*M0+H0).
  { change (nu*(g_mass (F i) (g51_t0 (F i))+
      g_H (F i) (g51_t0 (F i))/g51_nu (F i))<=nu*M0+H0).
    rewrite (Hnus i).
    replace (nu*(g_mass (F i) (g51_t0 (F i))+g_H (F i) (g51_t0 (F i))/nu)) with
      (nu*g_mass (F i) (g51_t0 (F i))+g_H (F i) (g51_t0 (F i))) by (field; lra).
    pose proof (Hm0 i); pose proof (Hh0 i); nra. }
  rewrite (Hnus i) in Hbal, Hq.
  assert (Htotal : g_W (F i) t+nu*(1-theta)*g51_Dcum (F i) t<=B).
  { apply (Rmult_le_reg_l nu); [exact Hnu|].
    unfold B; replace (nu*(M0+(H0+Qstar)/nu)) with (nu*M0+H0+Qstar) by (field; lra); nra. }
  assert (Hm : g_mass (F i) t<=B).
  { assert (Hnon : 0<=nu*(1-theta)*g51_Dcum (F i) t).
    { exact (Rmult_le_pos (nu*(1-theta)) (g51_Dcum (F i) t)
        (Rlt_le 0 (nu*(1-theta)) He) HDt). } lra. }
  assert (Hd : g51_Dcum (F i) t<=J).
  { apply (Rmult_le_reg_l (nu*(1-theta))); [exact He|].
    unfold J; replace ((nu*(1-theta))*(B/(nu*(1-theta)))) with B by (field; lra); lra. }
  assert (Hr : g51_Rcum (F i) t<=Rmax).
  { pose proof (NSSC10_SIGNED_SOURCE_INTEGRATION_WITHOUT_LH (F i) t (HW i) Ht) as Hs.
    pose proof (proj1 (NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES (F i) (HW i) t)) as Hpos.
    pose proof (Hh0 i).
    pose proof (Rmult_le_compat_l (theta*nu*nu) (g51_Dcum (F i) t) J Hcoef Hd).
    unfold Rmax; lra. }
  exact (conj Hm (conj Hd Hr)).
Qed.

Theorem NSSJ70_INITIAL_MOMENT_CONSTRUCTS_SOURCE_STORAGE_BOUND :
  forall D Cb L M0,
  GPSourceWitness51 D -> 0<=L -> 0<=M0 ->
  PacketCoefficientBound51 (g51_packets D) Cb ->
  PacketPairMultiplicity51 (g51_packets D) L ->
  g_mass D (g51_t0 D)<=M0 ->
  g_H D (g51_t0 D)<=
    (g51_Z D*Cb*Cb*L/g51_nu D)*M0*M0.
Proof.
  intros D Cb L M0 HW HL HM HC HP Hinit.
  pose proof (NSFA40_UNIFORM_STORAGE_FROM_FIXED_ALLOCATION
    (g51_packets D) (g51_nu D) (g51_Z D) Cb L (g51_u D (g51_t0 D))
    (gw51_nu D HW) (gw51_Z D HW) (gw51_indices D HW) (gw51_positive D HW)
    HC (gw51_geometry D HW) HP) as H.
  change (g_H D (g51_t0 D)<=
    (g51_Z D*Cb*Cb*L/g51_nu D)*g_mass D (g51_t0 D)*g_mass D (g51_t0 D)) in H.
  assert (Hcoef : 0<=g51_Z D*Cb*Cb*L/g51_nu D).
  { unfold Rdiv; apply Rmult_le_pos.
    - replace (g51_Z D*Cb*Cb*L) with (g51_Z D*(Cb*Cb)*L) by ring.
      apply Rmult_le_pos; [apply Rmult_le_pos; [pose proof (gw51_Z D HW); lra|exact (Rle_0_sqr Cb)]|exact HL].
    - apply Rlt_le; apply Rinv_0_lt_compat; exact (gw51_nu D HW). }
  pose proof (proj1 (proj2 (proj2
    (NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES D HW (g51_t0 D))))) as Hm0.
  assert (Hsq : g_mass D (g51_t0 D)*g_mass D (g51_t0 D)<=M0*M0) by nra.
  pose proof (Rmult_le_compat_l (g51_Z D*Cb*Cb*L/g51_nu D)
    (g_mass D (g51_t0 D)*g_mass D (g51_t0 D)) (M0*M0) Hcoef Hsq); nra.
Qed.

Theorem NSSJ80_FIXED_ALLOCATION_TO_COMMON_SOURCE_AND_CRITICAL_BOUNDS :
  forall (Index : Type) (F : Index -> GPSourceData51) nu Z Cb L theta Qstar M0,
  0<nu -> 0<Z -> 0<=L -> 0<=theta -> theta<1 -> 0<=Qstar -> 0<=M0 ->
  (forall i, GPSourceWitness51 (F i)) ->
  (forall i, g51_nu (F i)=nu) ->
  (forall i, g51_Z (F i)=Z) ->
  (forall i, PacketCoefficientBound51 (g51_packets (F i)) Cb) ->
  (forall i, PacketPairMultiplicity51 (g51_packets (F i)) L) ->
  (forall i, g_mass (F i) (g51_t0 (F i))<=M0) ->
  (forall i, SignedProductionBudget51 (F i) theta Qstar) ->
  exists B J Rmax,
    0<=B /\ 0<=J /\ 0<=Rmax /\
    forall i t, InTime (g51_t0 (F i)) (g51_t1 (F i)) t ->
      g_mass (F i) t<=B /\ g51_Dcum (F i) t<=J /\ g51_Rcum (F i) t<=Rmax.
Proof.
  intros Index F nu Z Cb L theta Qstar M0 Hnu HZ HL Hth Hth1 HQ HM
    HW Hnus HZs HC HP Hinit Hpay.
  set (H0 := (Z*Cb*Cb*L/nu)*M0*M0).
  assert (HH0 : 0<=H0).
  { unfold H0.
    replace ((Z*Cb*Cb*L/nu)*M0*M0) with ((Z*(Cb*Cb)*L/nu)*(M0*M0)) by (unfold Rdiv; ring).
    apply Rmult_le_pos; [|exact (Rle_0_sqr M0)].
    unfold Rdiv; apply Rmult_le_pos.
    - (* Cb may have either sign: use its square as a single factor. *)
      exact (Rmult_le_pos (Z*(Cb*Cb)) L
        (Rmult_le_pos Z (Cb*Cb) (Rlt_le 0 Z HZ) (Rle_0_sqr Cb)) HL).
    - apply Rlt_le; apply Rinv_0_lt_compat; exact Hnu. }
  apply (NSSJ60_COMMON_INITIAL_STORAGE_AND_SIGNED_PAYMENT Index F nu theta Qstar M0 H0
    Hnu Hth Hth1 HQ HM HH0 HW Hnus Hinit).
  - intro i.
    pose proof (NSSJ70_INITIAL_MOMENT_CONSTRUCTS_SOURCE_STORAGE_BOUND
      (F i) Cb L M0 (HW i) HL HM (HC i) (HP i) (Hinit i)) as H.
    rewrite (Hnus i), (HZs i) in H; exact H.
  - exact Hpay.
Qed.

Theorem NSSJ90_FIXED_ALLOCATION_UNIFORM_M7_CRITICAL_CHAIN :
  forall (Index : Type) (F : Index -> GPSourceData51) nu Z Cb L theta Qstar M0,
  0<nu -> 0<Z -> 0<=L -> 0<=theta -> theta<1 -> 0<=Qstar -> 0<=M0 ->
  (forall i, GPSourceWitness51 (F i)) ->
  (forall i, g51_nu (F i)=nu) ->
  (forall i, g51_Z (F i)=Z) ->
  (forall i, PacketCoefficientBound51 (g51_packets (F i)) Cb) ->
  (forall i, PacketPairMultiplicity51 (g51_packets (F i)) L) ->
  (forall i, g_mass (F i) (g51_t0 (F i))<=M0) ->
  (forall i, SignedProductionBudget51 (F i) theta Qstar) ->
  exists B J Rmax,
    0<=B /\ 0<=J /\ 0<=Rmax /\
    (forall i t, InTime (g51_t0 (F i)) (g51_t1 (F i)) t ->
      g_mass (F i) t<=B /\ g51_Dcum (F i) t<=J) /\
    (forall i grid, SourceGrid51 (F i) grid ->
      forall N, Spine.resistant_prefix (source_cell51 (F i) grid) N<=Rmax).
Proof.
  intros Index F nu Z Cb L theta Qstar M0 Hnu HZ HL Hth Hth1 HQ HM
    HW Hnus HZs HC HP Hinit Hpay.
  destruct (NSSJ80_FIXED_ALLOCATION_TO_COMMON_SOURCE_AND_CRITICAL_BOUNDS
    Index F nu Z Cb L theta Qstar M0 Hnu HZ HL Hth Hth1 HQ HM
    HW Hnus HZs HC HP Hinit Hpay) as [B [J [Rmax [HB [HJ [HR Hbounds]]]]]].
  exists B, J, Rmax; split; [exact HB|]; split; [exact HJ|]; split; [exact HR|]; split.
  - intros i t Ht; destruct (Hbounds i t Ht) as [Hm [Hd Hr]]; exact (conj Hm Hd).
  - intros i grid HG N.
    rewrite (NSSJ10_ACTUAL_CELL_PREFIX_IS_CUMULATIVE (F i) grid N (HW i) HG).
    exact (proj2 (proj2 (Hbounds i (grid N) (proj1 (proj2 HG) N)))).
Qed.

End NSE_GP_SOURCE_M7_ENERGY_JOIN.
