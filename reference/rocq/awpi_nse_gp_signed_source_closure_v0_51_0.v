From Stdlib Require Import Reals Ranalysis1 Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.
Require Import awpi_nse_gp_pair_source_calculus_v0_51_0.
Require Import awpi_nse_gp_fixed_allocation_v0_51_0.
Require Import awpi_nse_gp_source_storage_dynamics_v0_51_0.

Module NSE_GP_SIGNED_SOURCE_CLOSURE.
Import NSE_KQ_FINITE_ALGEBRA NSE_CONTINUOUS_TIME_CALCULUS.
Import NSE_GALERKIN_MODAL_CALCULUS NSE_GP_PAIR_SOURCE_CALCULUS.
Import NSE_GP_FIXED_ALLOCATION NSE_GP_SOURCE_STORAGE_DYNAMICS.
Open Scope R_scope.

Record GPSourceData51 : Type := {
  g51_packets : PacketData51;
  g51_nu : R;
  g51_Z : R;
  g51_table : CoefficientTable;
  g51_t0 : R;
  g51_t1 : R;
  g51_u : R -> Vec;
  g51_Rcum : R -> R;
  g51_Dcum : R -> R;
  g51_Qcum : R -> R
}.
Definition g_mass D t := critical_mass (g51_packets D) (g51_u D t).
Definition g_diss D t := critical_dissipation (g51_packets D) (g51_u D t).
Definition g_H D t := packet_H (g51_packets D) (g51_nu D) (g51_Z D) (g51_u D t).
Definition g_R D t := source_mass (g51_packets D) (g51_Z D) (g51_u D t).
Definition g_DS D t := source_dissipation (g51_packets D) (g51_nu D) (g51_Z D) (g51_u D t).
Definition g_Q D t := source_production (g51_packets D) (g51_nu D) (g51_Z D)
  (g51_table D) (g51_u D t).
Definition g_W D t := combined_storage (g51_packets D) (g51_nu D) (g51_Z D) (g51_u D t).
Definition g_mrate D t := critical_rate (g51_packets D) (g51_nu D) (g51_table D) (g51_u D t).
Definition g_wrate D t := combined_rate (g51_packets D) (g51_nu D) (g51_Z D)
  (g51_table D) (g51_u D t).

(* No LH membership, kinetic-energy inequality, M7 assertion, current-time
   critical bound, or signed payment bound is a field of this record.
   The primitives are actual real derivatives on the closed interval, as in
   the preserved v0.50.0 calculus.  Their existence and AE/PDE identification
   are not proved by this record. *)
Record GPSourceWitness51 (D : GPSourceData51) : Prop := {
  gw51_order : g51_t0 D<=g51_t1 D;
  gw51_nu : 0<g51_nu D;
  gw51_Z : 0<g51_Z D;
  gw51_indices : PacketIndices51 (g51_packets D);
  gw51_positive : PacketPositive51 (g51_packets D);
  gw51_geometry : PacketDecayGeometry51 (g51_packets D);
  gw51_census : PacketGeometricCensus51 (g51_packets D) (g51_Z D);
  gw51_coefficients : PacketCoefficientIdentity51 (g51_packets D) (g51_table D);
  gw51_skew : SkewTable (ps_space (g51_packets D)) (g51_table D);
  gw51_path : ModalPath (ps_space (g51_packets D)) (packet_lambda (g51_packets D))
    (g51_table D) (g51_nu D) (g51_t0 D) (g51_t1 D) (g51_u D);
  gw51_R_primitive : PrimitiveOn (g51_t0 D) (g51_t1 D) (g_R D) (g51_Rcum D);
  gw51_D_primitive : PrimitiveOn (g51_t0 D) (g51_t1 D) (g_diss D) (g51_Dcum D);
  gw51_Q_primitive : PrimitiveOn (g51_t0 D) (g51_t1 D) (g_Q D) (g51_Qcum D)
}.

Lemma gw51_same_source : forall D, GPSourceWitness51 D ->
  PacketSourceReconstruction51 (g51_packets D) (g51_table D).
Proof.
  intros D HW; exact (NSFA45_COEFFICIENT_IDENTITY_CONSTRUCTS_FULL_SOURCE
    (g51_packets D) (g51_table D) (gw51_indices D HW) (gw51_coefficients D HW)).
Qed.

Definition SignedProductionBudget51 D theta Qstar : Prop :=
  forall t, InTime (g51_t0 D) (g51_t1 D) t ->
    g51_Qcum D t<=Qstar+theta*g51_nu D*g51_nu D*g51_Dcum D t.

Lemma nonpositive_to_endpoint51 : forall a b F f t,
  DerivativeOn a b F f ->
  (forall s, InTime a b s -> f s<=0) ->
  InTime a b t -> F t<=F a.
Proof.
  intros a b F f t HF Hf Ht.
  apply (NSCT01_NONPOSITIVE_DERIVATIVE_GIVES_ORDER a t F f).
  - unfold InTime in Ht; lra.
  - exact (derivative_on_restrict a b t F f Ht HF).
  - intros s Hs; apply Hf; unfold InTime in *; lra.
Qed.

Theorem NSSC00_ACTUAL_SOURCE_LEDGER_DERIVED : forall D,
  GPSourceWitness51 D ->
  DerivativeOn (g51_t0 D) (g51_t1 D) (g_H D) (fun t => g_Q D t-g_DS D t).
Proof.
  intros D HW.
  exact (NSSD30_EXACT_PHYSICAL_PACKET_STORAGE_DERIVATIVE
    (g51_packets D) (g51_nu D) (g51_Z D) (g51_table D)
    (g51_t0 D) (g51_t1 D) (g51_u D) (gw51_indices D HW) (gw51_path D HW)).
Qed.
Lemma source_damping_funds51 : forall D,
  GPSourceWitness51 D -> forall t, g_R D t<=g_DS D t.
Proof.
  intros D HW t; apply NSSD31_DAMPING_FUNDS_ACTUAL_SOURCE_MASS.
  - exact (gw51_nu D HW).
  - exact (gw51_Z D HW).
  - exact (gw51_indices D HW).
  - exact (gw51_positive D HW).
  - exact (gw51_geometry D HW).
Qed.
Theorem NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES : forall D,
  GPSourceWitness51 D -> forall t,
  0<=g_H D t /\ 0<=g_R D t /\ 0<=g_mass D t /\ 0<=g_diss D t.
Proof.
  intros D HW t; exact (NSSD10_STORAGE_AND_RATES_NONNEGATIVE
    (g51_packets D) (g51_nu D) (g51_Z D) (g51_u D t)
    (gw51_nu D HW) (gw51_Z D HW) (gw51_indices D HW) (gw51_positive D HW)).
Qed.
Theorem NSSC02_NONNEGATIVE_ACTUAL_CUMULATIVES : forall D t,
  GPSourceWitness51 D -> InTime (g51_t0 D) (g51_t1 D) t ->
  0<=g51_Rcum D t /\ 0<=g51_Dcum D t.
Proof.
  intros D t HW Ht; split.
  - apply (NSCT10_PRIMITIVE_NONNEGATIVE (g51_t0 D) (g51_t1 D)
      (g_R D) (g51_Rcum D) t (gw51_R_primitive D HW)).
    + intros s Hs; exact (proj1 (proj2 (NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES D HW s))).
    + exact Ht.
  - apply (NSCT10_PRIMITIVE_NONNEGATIVE (g51_t0 D) (g51_t1 D)
      (g_diss D) (g51_Dcum D) t (gw51_D_primitive D HW)).
    + intros s Hs; exact (proj2 (proj2 (proj2 (NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES D HW s)))).
    + exact Ht.
Qed.
Lemma combined_storage_bounds51 : forall D,
  GPSourceWitness51 D -> forall t, 0<=g_W D t /\ g_mass D t<=g_W D t.
Proof.
  intros D HW t.
  destruct (NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES D HW t) as [HH [HR [Hm Hd]]].
  assert (Hx : 0<=g_H D t/g51_nu D).
  { unfold Rdiv; apply Rmult_le_pos; [exact HH|].
    apply Rlt_le; apply Rinv_0_lt_compat; exact (gw51_nu D HW). }
  change (0<=g_mass D t+g_H D t/g51_nu D /\
    g_mass D t<=g_mass D t+g_H D t/g51_nu D); lra.
Qed.

Theorem NSSC10_SIGNED_SOURCE_INTEGRATION_WITHOUT_LH : forall D t,
  GPSourceWitness51 D -> InTime (g51_t0 D) (g51_t1 D) t ->
  g_H D t+g51_Rcum D t<=g_H D (g51_t0 D)+g51_Qcum D t.
Proof.
  intros D t HW Ht.
  assert (HD : DerivativeOn (g51_t0 D) (g51_t1 D)
    (fun s => g_H D s+g51_Rcum D s-g51_Qcum D s)
    (fun s => (g_Q D s-g_DS D s)+g_R D s-g_Q D s)).
  { apply derivative_on_minus.
    - apply derivative_on_plus; [exact (NSSC00_ACTUAL_SOURCE_LEDGER_DERIVED D HW)|
      exact (proj2 (gw51_R_primitive D HW))].
    - exact (proj2 (gw51_Q_primitive D HW)). }
  assert (Hneg : forall s, InTime (g51_t0 D) (g51_t1 D) s ->
    (g_Q D s-g_DS D s)+g_R D s-g_Q D s<=0).
  { intros s Hs; pose proof (source_damping_funds51 D HW s); lra. }
  pose proof (nonpositive_to_endpoint51 (g51_t0 D) (g51_t1 D) _ _ t HD Hneg Ht) as H.
  cbn beta in H.
  rewrite (proj1 (gw51_R_primitive D HW)), (proj1 (gw51_Q_primitive D HW)) in H; lra.
Qed.

Theorem NSSC20_ACTUAL_CRITICAL_INTEGRATED_BALANCE : forall D t,
  GPSourceWitness51 D -> InTime (g51_t0 D) (g51_t1 D) t ->
  g51_nu D*g_mass D t+g51_nu D*g51_nu D*g51_Dcum D t<=
  g51_nu D*g_mass D (g51_t0 D)+g51_Rcum D t.
Proof.
  intros D t HW Ht.
  assert (Hm : DerivativeOn (g51_t0 D) (g51_t1 D) (g_mass D) (g_mrate D)).
  { exact (NSSD40_CRITICAL_DERIVATIVE_FROM_SAME_MODAL_PATH
      (g51_packets D) (g51_nu D) (g51_table D)
      (g51_t0 D) (g51_t1 D) (g51_u D) (gw51_path D HW)). }
  assert (HD : DerivativeOn (g51_t0 D) (g51_t1 D)
    (fun s => g51_nu D*g_mass D s+g51_nu D*g51_nu D*g51_Dcum D s-g51_Rcum D s)
    (fun s => g51_nu D*g_mrate D s+g51_nu D*g51_nu D*g_diss D s-g_R D s)).
  { apply derivative_on_minus.
    - apply derivative_on_plus.
      + exact (derivative_on_scale _ _ _ _ (g51_nu D) Hm).
      + exact (derivative_on_scale _ _ _ _ (g51_nu D*g51_nu D)
          (proj2 (gw51_D_primitive D HW))).
    - exact (proj2 (gw51_R_primitive D HW)). }
  assert (Hneg : forall s, InTime (g51_t0 D) (g51_t1 D) s ->
    g51_nu D*g_mrate D s+g51_nu D*g51_nu D*g_diss D s-g_R D s<=0).
  { intros s Hs; pose proof (NSSD41_ACTUAL_CRITICAL_ABSORPTION
      (g51_packets D) (g51_nu D) (g51_Z D) (g51_table D) (g51_u D s)
      (gw51_nu D HW) (gw51_Z D HW) (gw51_indices D HW) (gw51_positive D HW)
      (gw51_census D HW) (gw51_same_source D HW)) as H; change
      (g51_nu D*g_mrate D s+g51_nu D*g51_nu D*g_diss D s<=g_R D s) in H; lra. }
  pose proof (nonpositive_to_endpoint51 (g51_t0 D) (g51_t1 D) _ _ t HD Hneg Ht) as H.
  cbn beta in H; rewrite (proj1 (gw51_D_primitive D HW)),
    (proj1 (gw51_R_primitive D HW)) in H; lra.
Qed.

Theorem NSSC21_ACTUAL_COUPLED_INTEGRATED_BALANCE : forall D t,
  GPSourceWitness51 D -> InTime (g51_t0 D) (g51_t1 D) t ->
  g51_nu D*g_W D t+g51_nu D*g51_nu D*g51_Dcum D t<=
  g51_nu D*g_W D (g51_t0 D)+g51_Qcum D t.
Proof.
  intros D t HW Ht.
  pose proof (NSSC10_SIGNED_SOURCE_INTEGRATION_WITHOUT_LH D t HW Ht) as Hs.
  pose proof (NSSC20_ACTUAL_CRITICAL_INTEGRATED_BALANCE D t HW Ht) as Hm.
  assert (He : forall s, g51_nu D*g_W D s=g51_nu D*g_mass D s+g_H D s).
  { intro s; change (g51_nu D*(g_mass D s+g_H D s/g51_nu D)=
      g51_nu D*g_mass D s+g_H D s); field; pose proof (gw51_nu D HW); lra. }
  rewrite !He; lra.
Qed.

Definition closure_mass51 D (theta Qstar : R) := g_W D (g51_t0 D)+Qstar/g51_nu D.
Definition closure_diss51 D theta Qstar :=
  closure_mass51 D theta Qstar/(g51_nu D*(1-theta)).
Definition closure_source51 D theta Qstar :=
  g_H D (g51_t0 D)+Qstar+theta*g51_nu D*g51_nu D*closure_diss51 D theta Qstar.

Theorem NSSC30_SIGNED_PRODUCTION_BUDGET_ABSORBS : forall D theta Qstar t,
  GPSourceWitness51 D -> 0<=theta -> theta<1 -> 0<=Qstar ->
  SignedProductionBudget51 D theta Qstar -> InTime (g51_t0 D) (g51_t1 D) t ->
  g_W D t+g51_nu D*(1-theta)*g51_Dcum D t<=closure_mass51 D theta Qstar.
Proof.
  intros D theta Qstar t HW Hth Hth1 HQ HB Ht.
  pose proof (NSSC21_ACTUAL_COUPLED_INTEGRATED_BALANCE D t HW Ht) as H.
  pose proof (HB t Ht) as Hp.
  apply (Rmult_le_reg_l (g51_nu D)); [exact (gw51_nu D HW)|].
  unfold closure_mass51.
  replace (g51_nu D*(g_W D (g51_t0 D)+Qstar/g51_nu D)) with
    (g51_nu D*g_W D (g51_t0 D)+Qstar)
    by (field; pose proof (gw51_nu D HW); lra).
  nra.
Qed.

Theorem NSSC31_CRITICAL_AND_SOURCE_BOUNDS : forall D theta Qstar t,
  GPSourceWitness51 D -> 0<=theta -> theta<1 -> 0<=Qstar ->
  SignedProductionBudget51 D theta Qstar -> InTime (g51_t0 D) (g51_t1 D) t ->
  0<=closure_mass51 D theta Qstar /\
  0<=closure_diss51 D theta Qstar /\
  0<=closure_source51 D theta Qstar /\
  g_mass D t<=closure_mass51 D theta Qstar /\
  g51_Dcum D t<=closure_diss51 D theta Qstar /\
  g51_Rcum D t<=closure_source51 D theta Qstar.
Proof.
  intros D theta Qstar t HW Hth Hth1 HQ HB Ht.
  pose proof (gw51_nu D HW) as Hnu.
  assert (He : 0<g51_nu D*(1-theta)) by nra.
  assert (HM : 0<=closure_mass51 D theta Qstar).
  { unfold closure_mass51.
    pose proof (proj1 (combined_storage_bounds51 D HW (g51_t0 D))) as HW0.
    assert (Hq : 0<=Qstar/g51_nu D).
    { unfold Rdiv; apply Rmult_le_pos; [exact HQ|].
      apply Rlt_le; apply Rinv_0_lt_compat; exact Hnu. }
    lra. }
  assert (HD0 : 0<=closure_diss51 D theta Qstar).
  { unfold closure_diss51, Rdiv; apply Rmult_le_pos; [exact HM|].
    apply Rlt_le; apply Rinv_0_lt_compat; exact He. }
  (* Treat the established closure_diss51 bound as one nonnegative factor.
     Do not unfold it by repeated multiplication decomposition. *)
  pose proof (Rlt_le 0 (g51_nu D) Hnu) as Hnu0.
  assert (Hcoef : 0<=theta*g51_nu D*g51_nu D).
  { exact (Rmult_le_pos (theta*g51_nu D) (g51_nu D)
      (Rmult_le_pos theta (g51_nu D) Hth Hnu0) Hnu0). }
  assert (HP0 : 0<=closure_source51 D theta Qstar).
  { pose proof (proj1 (NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES D HW (g51_t0 D))) as HH0.
    assert (Hprod : 0<=theta*g51_nu D*g51_nu D*closure_diss51 D theta Qstar).
    { exact (Rmult_le_pos (theta*g51_nu D*g51_nu D)
        (closure_diss51 D theta Qstar) Hcoef HD0). }
    unfold closure_source51.
    exact (Rplus_le_le_0_compat (g_H D (g51_t0 D)+Qstar)
      (theta*g51_nu D*g51_nu D*closure_diss51 D theta Qstar)
      (Rplus_le_le_0_compat (g_H D (g51_t0 D)) Qstar HH0 HQ) Hprod). }
  pose proof (NSSC30_SIGNED_PRODUCTION_BUDGET_ABSORBS D theta Qstar t HW Hth Hth1 HQ HB Ht) as Hbal.
  destruct (combined_storage_bounds51 D HW t) as [HW0 HmW].
  destruct (NSSC02_NONNEGATIVE_ACTUAL_CUMULATIVES D t HW Ht) as [HR0 HD].
  assert (Hm : g_mass D t<=closure_mass51 D theta Qstar).
  { assert (Hx : 0<=g51_nu D*(1-theta)*g51_Dcum D t).
    { exact (Rmult_le_pos (g51_nu D*(1-theta)) (g51_Dcum D t)
        (Rlt_le 0 (g51_nu D*(1-theta)) He) HD). } lra. }
  assert (Hd : g51_Dcum D t<=closure_diss51 D theta Qstar).
  { apply (Rmult_le_reg_l (g51_nu D*(1-theta))); [exact He|].
    unfold closure_diss51.
    replace ((g51_nu D*(1-theta))*(closure_mass51 D theta Qstar/(g51_nu D*(1-theta))))
      with (closure_mass51 D theta Qstar) by (field; lra).
    lra. }
  assert (Hr : g51_Rcum D t<=closure_source51 D theta Qstar).
  { pose proof (NSSC10_SIGNED_SOURCE_INTEGRATION_WITHOUT_LH D t HW Ht) as Hs.
    pose proof (HB t Ht) as Hq.
    pose proof (proj1 (NSSC01_NONNEGATIVE_PHYSICAL_QUANTITIES D HW t)) as HH.
    pose proof (Rmult_le_compat_l (theta*g51_nu D*g51_nu D)
      (g51_Dcum D t) (closure_diss51 D theta Qstar) Hcoef Hd).
    unfold closure_source51; lra. }
  exact (conj HM (conj HD0 (conj HP0 (conj Hm (conj Hd Hr))))).
Qed.

(* A ratewise estimate implies the signed prefix budget.  An everywhere
   differentiable primitive G of the nonnegative excess is an explicit
   analytic witness; the bound on G is a payment input, not a theorem that
   every NSE path satisfies it.  Signed Q is never replaced by |Q| here. *)
Theorem NSSC40_EXCESS_RATE_GIVES_SIGNED_BUDGET : forall D theta Qstar g G,
  GPSourceWitness51 D ->
  PrimitiveOn (g51_t0 D) (g51_t1 D) g G ->
  (forall t, InTime (g51_t0 D) (g51_t1 D) t ->
    g_Q D t<=theta*g51_nu D*g51_nu D*g_diss D t+g t) ->
  (forall t, InTime (g51_t0 D) (g51_t1 D) t -> G t<=Qstar) ->
  SignedProductionBudget51 D theta Qstar.
Proof.
  intros D theta Qstar g G HW HG Hrate Hcap t Ht.
  assert (HP : PrimitiveOn (g51_t0 D) (g51_t1 D)
    (fun s => theta*g51_nu D*g51_nu D*g_diss D s+g s)
    (fun s => theta*g51_nu D*g51_nu D*g51_Dcum D s+G s)).
  { split.
    - rewrite (proj1 (gw51_D_primitive D HW)), (proj1 HG); ring.
    - apply derivative_on_plus.
      + exact (derivative_on_scale _ _ _ _ (theta*g51_nu D*g51_nu D)
          (proj2 (gw51_D_primitive D HW))).
      + exact (proj2 HG). }
  pose proof (NSCT11_PRIMITIVE_COMPARISON (g51_t0 D) (g51_t1 D)
    (g_Q D) (fun s => theta*g51_nu D*g51_nu D*g_diss D s+g s)
    (g51_Qcum D) (fun s => theta*g51_nu D*g51_nu D*g51_Dcum D s+G s)
    t (gw51_Q_primitive D HW) HP Hrate Ht) as H.
  specialize (Hcap t Ht); cbn beta in H; lra.
Qed.

End NSE_GP_SIGNED_SOURCE_CLOSURE.
