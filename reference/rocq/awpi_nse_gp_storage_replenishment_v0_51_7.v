From Stdlib Require Import Reals Lra String.
(* Direct imports expose the named modules used below; transitive
   Require Import dependencies are not relied upon for short-name visibility. *)
Require Import awpi_nse_finite_shell_algebra_v0_48_4.
Require Import awpi_nse_scalar_comparison_v0_48_4.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.
Require Import awpi_nse_direct_gp_action_m7_chain_v0_47_0.
Require Import awpi_nse_direct_gp_shell_occupancy_v0_48_4.
Require Import awpi_nse_gp_kq_gram_renewal_v0_50_0.
Require Import awpi_nse_storage_cost_algebra_v0_51_7.
Require Import awpi_nse_storage_interval_calculus_v0_51_7.
Require Import awpi_nse_storage_riemann_binding_v0_51_7.
Require Import awpi_nse_storage_modal_ledger_v0_51_7.
Require Import awpi_nse_storage_signed_time_v0_51_7.

Module NSE_GP_STORAGE_REPLENISHMENT.
Import NSE_FINITE_SHELL_ALGEBRA NSE_SCALAR_COMPARISON
  NSE_STORAGE_COST_ALGEBRA NSE_STORAGE_SIGNED_TIME.
Module O := NSE_DIRECT_GP_SHELL_OCCUPANCY.
Module DG := NSE_DIRECT_GP_ACTION_M7_CHAIN.
Module M7 := NSE_GP_TO_M7_SPINE.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

Record StoragePath : Type := {
  sp_H : R -> R;
  sp_low : R -> R;
  sp_high : R -> R;
  sp_heat : R -> R
}.

(* This identifies the integrated storage with the SAME ev_VI used by
   the frozen occupancy module.  It asserts an equality, not a budget.
   A C1 constructor and a finite-cell constructor are supplied below.
   Actual absolute-value/switching-time realization remains explicit. *)
Definition ExactIntegratedStorage T (d : O.ShellEvolution) p : Prop :=
  forall t, within T t ->
    0 <= sp_H p t /\
    sp_H p t+O.ev_VI d t=
      sp_H p 0+sp_low p t+sp_high p t+sp_heat p t.

Definition beta_of nu cap := cap/(4*O.threshold nu).
Definition LowerOutputPayments nu cap kappa T (d : O.ShellEvolution) p : Prop :=
  forall t, within T t ->
    sp_heat p t <= beta_of nu cap*O.ev_GI d t /\
    sp_low p t <= kappa*O.ev_GI d t.

(* This remains a separate, named analytic hypothesis.  No proof in this
   package establishes it for unrestricted NSE.  In particular this
   definition does not use the desired final energy or action bound. *)
Definition HighOutputAbsorption gamma Chigh T (d : O.ShellEvolution) p : Prop :=
  forall t, within T t -> sp_high p t <= gamma*O.ev_VI d t+Chigh.

Definition upstream_budget nu cap kappa Hinit M0 gamma Chigh :=
  replenishment_budget nu (beta_of nu cap) kappa Hinit M0 gamma Chigh.

Lemma NSRA00_BETA_NONNEG : forall nu cap,
  0 < nu -> 0 <= cap -> 0 <= beta_of nu cap.
Proof.
  intros nu cap Hnu Hcap. unfold beta_of, O.threshold.
  apply NSFA08_DIV_NONNEG; lra.
Qed.

Theorem NSRA10_C1_DATA_CONSTRUCT_EXACT_STORAGE :
  forall nu cap T d p plo phi e,
  (forall t, within T t -> 0 <= sp_H p t) ->
  (forall t, within T t -> derivable_pt_lim (sp_H p) t
    (plo t+phi t+e t-O.crowd_rate nu cap d t)) ->
  ZeroPrimitive T (O.ev_VI d) (O.crowd_rate nu cap d) ->
  ZeroPrimitive T (sp_low p) plo -> ZeroPrimitive T (sp_high p) phi ->
  ZeroPrimitive T (sp_heat p) e ->
  ExactIntegratedStorage T d p.
Proof.
  intros nu cap T d p plo phi e Hpos HD HV HL HH HE t Ht.
  split; [exact (Hpos t Ht)|].
  exact (NSSP10_CONTINUOUS_STORAGE_BALANCE T (sp_H p)
    (O.crowd_rate nu cap d) (O.ev_VI d) plo (sp_low p)
    phi (sp_high p) e (sp_heat p) t HD HV HL HH HE Ht).
Qed.

Theorem NSRA11_FINITE_CELLS_CONSTRUCT_EXACT_STORAGE :
  forall T d p,
  (forall t, within T t -> 0 <= sp_H p t) ->
  O.ev_VI d 0=0 -> sp_low p 0=0 -> sp_high p 0=0 -> sp_heat p 0=0 ->
  (forall t, within T t -> exists (n : nat) (cut : nat -> R),
    cut O=0 /\ cut n=t /\
    (forall i, (i<n)%nat ->
      sp_H p (cut (S i))-sp_H p (cut i)+O.ev_VI d (cut (S i))-O.ev_VI d (cut i)=
      sp_low p (cut (S i))-sp_low p (cut i)+
      sp_high p (cut (S i))-sp_high p (cut i)+
      sp_heat p (cut (S i))-sp_heat p (cut i))) ->
  ExactIntegratedStorage T d p.
Proof.
  intros T d p Hpos HV0 HL0 HH0 HE0 Hcells t Ht.
  split; [exact (Hpos t Ht)|].
  destruct (Hcells t Ht) as [n [cut [H0 [Hn HC]]]].
  exact (NSSP12_PARTITION_CONSTRUCTS_INTEGRATED_BALANCE n cut
    (sp_H p) (O.ev_VI d) (sp_low p) (sp_high p) (sp_heat p)
    t H0 Hn HV0 HL0 HH0 HE0 HC).
Qed.

Theorem NSRA20_POINTWISE_PAYMENTS_CONSTRUCT_LOWER_BUDGETS :
  forall nu cap kappa T d p plo e,
  ZeroPrimitive T (O.ev_GI d) (O.ev_G d) ->
  ZeroPrimitive T (sp_low p) plo -> ZeroPrimitive T (sp_heat p) e ->
  (forall t, within T t -> e t <= beta_of nu cap*O.ev_G d t) ->
  (forall t, within T t -> Rabs (plo t) <= kappa*O.ev_G d t) ->
  LowerOutputPayments nu cap kappa T d p.
Proof.
  intros nu cap kappa T d p plo e HG HL HE Hheat Hlow t Ht; split.
  - exact (NSSP01_POINTWISE_HEAT_PAYMENT_INTEGRATES T (sp_heat p) e
      (O.ev_GI d) (O.ev_G d) (beta_of nu cap) t HE HG Hheat Ht).
  - exact (NSSP02_ABSOLUTE_LOW_PAYMENT_INTEGRATES T (sp_low p) plo
      (O.ev_GI d) (O.ev_G d) kappa t HL HG Hlow Ht).
Qed.

Theorem NSRA40_STORAGE_HIGH_ABSORPTION_TO_EXISTING_VI :
  forall (Reg : Type) (ev : Reg -> O.ShellEvolution) (path : Reg -> StoragePath)
    nu cap theta cs E0 M0 T kappa Hinit gamma Chigh,
  0 < nu -> 0 <= cap -> 0 <= kappa -> gamma < 1 ->
  (forall eps, O.EvolutionBindings nu cap theta cs E0 M0 T (ev eps)) ->
  (forall eps, ExactIntegratedStorage T (ev eps) (path eps)) ->
  (forall eps, sp_H (path eps) 0 <= Hinit) ->
  (forall eps, LowerOutputPayments nu cap kappa T (ev eps) (path eps)) ->
  (forall eps, HighOutputAbsorption gamma Chigh T (ev eps) (path eps)) ->
  forall eps t, within T t ->
    O.ev_VI (ev eps) t <= upstream_budget nu cap kappa Hinit M0 gamma Chigh.
Proof.
  intros Reg ev path nu cap theta cs E0 M0 T kappa Hinit gamma Chigh
    Hnu Hcap Hk Hg Heb Hstore Hseed Hpaid Hhigh eps t Ht.
  destruct (Hstore eps t Ht) as [HH Hbalance].
  destruct (Hpaid eps t Ht) as [Hheat Hlow].
  unfold upstream_budget.
  exact (NSSP20_STRICT_HIGH_OUTPUT_ABSORPTION nu (beta_of nu cap)
    kappa Hinit M0 gamma Chigh (sp_H (path eps) t) (sp_H (path eps) 0)
    (O.ev_VI (ev eps) t) (O.ev_GI (ev eps) t)
    (sp_low (path eps) t) (sp_high (path eps) t) (sp_heat (path eps) t)
    Hnu (NSRA00_BETA_NONNEG nu cap Hnu Hcap) Hk Hg
    HH (Hseed eps) (O.eb_kinetic (Heb eps) t Ht) Hbalance
    Hheat Hlow (Hhigh eps t Ht)).
Qed.

Theorem NSRA50_UNIFORM_STORAGE_TO_CRITICAL_ENERGY_AND_ACTION :
  forall (Reg : Type) (ev : Reg -> O.ShellEvolution) (path : Reg -> StoragePath)
    nu cap theta cs E0 M0 T kappa Hinit gamma Chigh,
  0 < nu -> 0 <= cap -> 0 <= E0 -> 0 <= theta -> theta < 1 ->
  0 <= kappa -> gamma < 1 ->
  (forall eps, O.EvolutionBindings nu cap theta cs E0 M0 T (ev eps)) ->
  (forall eps, ExactIntegratedStorage T (ev eps) (path eps)) ->
  (forall eps, sp_H (path eps) 0 <= Hinit) ->
  (forall eps, LowerOutputPayments nu cap kappa T (ev eps) (path eps)) ->
  (forall eps, HighOutputAbsorption gamma Chigh T (ev eps) (path eps)) ->
  forall eps t, within T t ->
  let Ustar := upstream_budget nu cap kappa Hinit M0 gamma Chigh in
  O.total_energy nu (ev eps) t <= energy_budget nu cap M0 E0 Ustar /\
  O.ev_C (ev eps) t <= O.action_budget cs nu theta (energy_budget nu cap M0 E0 Ustar).
Proof.
  intros Reg ev path nu cap theta cs E0 M0 T kappa Hinit gamma Chigh
    Hnu Hcap HE0 Hth Hth1 Hk Hg Heb Hstore Hseed Hpaid Hhigh eps t Ht.
  cbv zeta.
  exact (O.NSOA90_UNIFORM_OCCUPANCY_ACTION_CHAIN Reg ev nu cap theta cs E0 M0 T
    (upstream_budget nu cap kappa Hinit M0 gamma Chigh)
    Hnu Hcap HE0 Hth Hth1 Heb
    (NSRA40_STORAGE_HIGH_ABSORPTION_TO_EXISTING_VI Reg ev path
      nu cap theta cs E0 M0 T kappa Hinit gamma Chigh
      Hnu Hcap Hk Hg Heb Hstore Hseed Hpaid Hhigh) eps t Ht).
Qed.

Theorem NSRA99_STORAGE_REPLENISHMENT_TO_EXISTING_M7_TERMINAL :
  forall (Reg Time : Type) (ev : Reg -> O.ShellEvolution) (path : Reg -> StoragePath)
    (stamp : Time -> R) (cut : nat -> Time)
    nu cap theta cs E0 M0 T kappa Hinit gamma Chigh,
  0 < nu -> 0 <= cap -> 0 <= E0 -> 0 <= theta -> theta < 1 ->
  0 <= kappa -> gamma < 1 ->
  (forall eps, O.EvolutionBindings nu cap theta cs E0 M0 T (ev eps)) ->
  (forall eps, ExactIntegratedStorage T (ev eps) (path eps)) ->
  (forall eps, sp_H (path eps) 0 <= Hinit) ->
  (forall eps, LowerOutputPayments nu cap kappa T (ev eps) (path eps)) ->
  (forall eps, HighOutputAbsorption gamma Chigh T (ev eps) (path eps)) ->
  (forall t, within T (stamp t)) -> stamp (cut O)=0 ->
  (forall n, stamp (cut n) <= stamp (cut (S n))) ->
  (forall t, exists n, stamp t <= stamp (cut n)) ->
  let Ustar := upstream_budget nu cap kappa Hinit M0 gamma Chigh in
  let C := fun eps t => O.ev_C (ev eps) (stamp t) in
  let Cmax := O.action_budget cs nu theta (energy_budget nu cap M0 E0 Ustar) in
  (forall eps, M7.GPSequenceM7 (DG.action_increment C cut eps)) /\
  (forall eps, CE.M7ActionCostRealization Time (DG.action_increment C cut eps) (C eps)) /\
  (forall eps, DG.action_increment C cut eps O <= Cmax) /\
  (forall eps n, M7.paid_prefix (DG.renewal_debt (DG.action_increment C cut eps)) n <= Cmax) /\
  CE.UniformCriticalEnergy (Reg*Time)%type
    (fun rt => O.ev_E (ev (fst rt)) (stamp (snd rt)))
    (fun rt => O.ev_DI (ev (fst rt)) (stamp (snd rt))).
Proof.
  intros Reg Time ev path stamp cut nu cap theta cs E0 M0 T kappa Hinit gamma Chigh
    Hnu Hcap HE0 Hth Hth1 Hk Hg Heb Hstore Hseed Hpaid Hhigh
    Htime Hzero Horder Hcofinal.
  cbv zeta.
  exact (O.NSOA99_OCCUPANCY_TO_EXISTING_M7_TERMINAL Reg Time ev stamp cut
    nu cap theta cs E0 M0 T (upstream_budget nu cap kappa Hinit M0 gamma Chigh)
    Hnu Hcap HE0 Hth Hth1 Heb
    (NSRA40_STORAGE_HIGH_ABSORPTION_TO_EXISTING_VI Reg ev path
      nu cap theta cs E0 M0 T kappa Hinit gamma Chigh
      Hnu Hcap Hk Hg Heb Hstore Hseed Hpaid Hhigh)
    Htime Hzero Horder Hcofinal).
Qed.

Definition STATUS : string :=
  "NSE_GP_STORAGE_REPLENISHMENT_V0_51_7_CONDITIONAL_EXACT_COST_NO_ADMITTED"%string.
End NSE_GP_STORAGE_REPLENISHMENT.

Print Assumptions NSE_STORAGE_COST_ALGEBRA.NSST11_EXACT_EXISTING_CROWD_RATE.
Print Assumptions NSE_STORAGE_INTERVAL_CALCULUS.NSSC40_FINITE_VALID_PIECES_INITIAL_STORAGE_BOUND.
Print Assumptions NSE_STORAGE_INTERVAL_CALCULUS.NSSC31_MOVING_ENDPOINTS_CANCEL.
Print Assumptions NSE_STORAGE_RIEMANN_BINDING.NSSR20_VALID_PIECE_REALIZES_WHOLE_STORAGE.
Print Assumptions NSE_STORAGE_MODAL_LEDGER.NSSM10_EXACT_FINITE_STORAGE_BALANCE.
Print Assumptions NSE_STORAGE_MODAL_LEDGER.NSSM22_HEAT_ERROR_KINETIC_PAYMENT.
Print Assumptions NSE_STORAGE_MODAL_LEDGER.NSSM40_FINITE_LOW_OUTPUT_KINETIC_PAYMENT.
Print Assumptions NSE_STORAGE_MODAL_LEDGER.NSSM53_ACTIVE_PASSAGE_FROM_RADIAL_ODE.
Print Assumptions NSE_STORAGE_SIGNED_TIME.NSSP20_STRICT_HIGH_OUTPUT_ABSORPTION.
Print Assumptions NSE_GP_STORAGE_REPLENISHMENT.NSRA99_STORAGE_REPLENISHMENT_TO_EXISTING_M7_TERMINAL.
Print NSE_STORAGE_INTERVAL_CALCULUS.PieceValid.
Print NSE_GP_STORAGE_REPLENISHMENT.ExactIntegratedStorage.
Print NSE_GP_STORAGE_REPLENISHMENT.LowerOutputPayments.
Print NSE_GP_STORAGE_REPLENISHMENT.HighOutputAbsorption.
Check NSE_GP_STORAGE_REPLENISHMENT.NSRA99_STORAGE_REPLENISHMENT_TO_EXISTING_M7_TERMINAL.
