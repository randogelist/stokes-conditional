From Stdlib Require Import Reals Ranalysis1 Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_gp_gram_geometry_v0_49_3.
Require Import awpi_nse_native_kq_ladder_v0_49_3.
Require Import awpi_nse_schur_action_ledger_v0_49_3.
Require Import awpi_nse_gram_m7_energy_join_v0_49_3.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.

Module NSE_CONTINUOUS_GRAM_LEDGER.
Import NSE_KQ_FINITE_ALGEBRA NSE_GP_GRAM_GEOMETRY NSE_NATIVE_KQ_LADDER.
Import NSE_SCHUR_ACTION_LEDGER NSE_GRAM_M7_ENERGY_JOIN.
Import NSE_CONTINUOUS_TIME_CALCULUS NSE_GALERKIN_MODAL_CALCULUS.
Module Energy50 := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

(* One actual real-time interval in one finite spatial/cut carrier.
   An outer Point may index arbitrary approximation sizes AND endpoints. *)
Record ModalLedgerData : Type := {
  ml_space : nat;
  ml_gram : nat;
  ml_t0 : R;
  ml_t1 : R;
  ml_nu : R;
  ml_lambda : Vec;
  ml_table : CoefficientTable;
  ml_u : R -> Vec;
  ml_cuts : nat;
  ml_weights : Vec;
  ml_symbols : nat -> Vec;
  ml_potential : Vec -> R;
  ml_detector : Vec -> Vec;
  ml_increment : R -> Vec;
  ml_readout : R -> Vec -> Vec;
  ml_null_field : Vec -> Vec;
  ml_Y : R -> R;
  ml_Q : R -> R;
  ml_Z : R -> R;
  ml_net : R -> R
}.

Definition state_action D (u : Vec) :=
  finite_cut_action (ml_space D) (ml_table D) (ml_lambda D)
    (ml_cuts D) (ml_weights D) (ml_symbols D) u.
Definition time_action D t := state_action D (ml_u D t).
Definition time_potential D t := ml_potential D (ml_u D t).
Definition time_energy D t := norm2 (ml_space D) (ml_u D t).
Definition time_dissipation D t := spectral_energy (ml_space D) (ml_lambda D) (ml_u D t).
Definition time_source D t := modal_source (ml_space D) (ml_table D) (ml_u D t).
Definition time_detector D t := ml_detector D (ml_u D t).
Definition gram_detector D t := ml_readout D t (time_detector D t).
Definition gram_null0 D t := ml_readout D t (ml_u D t).
Definition gram_null1 D t := ml_readout D t (ml_null_field D (ml_u D t)).
Definition increment_rate D t := norm2 (ml_gram D) (ml_increment D t).
Definition capacity_rate D t := reduced_capacity (ml_gram D)
  (gram_detector D t) (gram_null0 D t) (gram_null1 D t).
Definition renewal_rate D t := dot (ml_gram D) (ml_increment D t) (gram_detector D t).

(* Concrete finite-clock normalization.  There is no time-integrated
   Leray budget or IntegratedGramLedger field in this definition. *)
Definition ClockRealizationAt D t : Prop :=
  exists (ell : nat -> R) (seed : Vec) (stages : nat),
    (forall j, (j<stages)%nat -> 0 < ell j) /\
    (forall i, (i<ml_space D)%nat ->
      clock_run ell (ml_lambda D) seed stages i=ml_u D t i) /\
    increment_rate D t = sum stages (fun j =>
      clock_cost (ml_space D) (ell j) (ml_lambda D)
        (clock_run ell (ml_lambda D) seed j)).

(* All remaining semantic/analytic inputs are named explicitly.
   In particular: this is not a proof that the future-heat potential has
   the asserted gradient, or that the infinite GP/Kq readout is realized.
   The null field must be actual helicity (or another proved null test) in
   an application; energy skewness alone does not imply that cancellation.

   PrimitiveOn is genuine differentiability, not a generic integration
   record.  Its existence must be supplied, especially at rank changes.
   No bound on reduced capacity is included in this witness. *)
Record ModalLedgerWitness (D : ModalLedgerData) : Prop := {
  mw_time_order : ml_t0 D <= ml_t1 D;
  mw_viscosity_positive : 0 < ml_nu D;
  mw_stokes_positive : forall i, (i<ml_space D)%nat -> 0 < ml_lambda D i;
  mw_convection_skew : SkewTable (ml_space D) (ml_table D);
  mw_modal_equation : ModalPath (ml_space D) (ml_lambda D) (ml_table D)
    (ml_nu D) (ml_t0 D) (ml_t1 D) (ml_u D);
  mw_cut_weights : forall N, (N<ml_cuts D)%nat -> 0 <= ml_weights D N;
  mw_cut_symbols : forall N i, (N<ml_cuts D)%nat -> (i<ml_space D)%nat ->
    0 <= ml_symbols D N i;
  mw_potential_nonnegative : forall t, InTime (ml_t0 D) (ml_t1 D) t ->
    0 <= time_potential D t;
  mw_potential_chain : forall t, InTime (ml_t0 D) (ml_t1 D) t ->
    derivable_pt_lim (time_potential D) t
      (dot (ml_space D) (time_detector D t)
        (modal_rhs (ml_space D) (ml_lambda D) (ml_table D) (ml_nu D) (ml_u D t)));
  mw_heat_generator : forall t, InTime (ml_t0 D) (ml_t1 D) t ->
    (-ml_nu D)*dot (ml_space D) (time_detector D t)
      (mul (ml_lambda D) (ml_u D t)) = -time_action D t;
  mw_same_source_readout : forall t, InTime (ml_t0 D) (ml_t1 D) t -> forall H,
    dot (ml_gram D) (ml_increment D t) (ml_readout D t H) =
      -dot (ml_space D) (time_source D t) H;
  mw_second_null_cancellation : forall t, InTime (ml_t0 D) (ml_t1 D) t ->
    dot (ml_space D) (time_source D t) (ml_null_field D (ml_u D t))=0;
  mw_clock_realization : forall t, InTime (ml_t0 D) (ml_t1 D) t -> ClockRealizationAt D t;
  mw_action_primitive : PrimitiveOn (ml_t0 D) (ml_t1 D) (time_action D) (ml_Y D);
  mw_increment_primitive : PrimitiveOn (ml_t0 D) (ml_t1 D) (increment_rate D) (ml_Q D);
  mw_capacity_primitive : PrimitiveOn (ml_t0 D) (ml_t1 D) (capacity_rate D) (ml_Z D);
  mw_renewal_primitive : PrimitiveOn (ml_t0 D) (ml_t1 D) (renewal_rate D) (ml_net D)
}.

Lemma stokes_nonnegative : forall D, ModalLedgerWitness D ->
  forall i, (i<ml_space D)%nat -> 0 <= ml_lambda D i.
Proof.
  intros D HW i Hi; apply Rlt_le; exact (mw_stokes_positive D HW i Hi).
Qed.
Lemma endpoint_in_time : forall D, ModalLedgerWitness D ->
  InTime (ml_t0 D) (ml_t1 D) (ml_t1 D).
Proof. intros D HW; unfold InTime; split; [exact (mw_time_order D HW)|lra]. Qed.

Theorem NSCL00_PHYSICAL_ACTION_NONNEGATIVE : forall D,
  ModalLedgerWitness D -> forall t, 0 <= time_action D t.
Proof.
  intros D HW t; unfold time_action, state_action.
  apply NSMG21_FINITE_PHYSICAL_CUT_ACTION_NONNEGATIVE.
  - exact (stokes_nonnegative D HW).
  - exact (mw_cut_weights D HW).
  - exact (mw_cut_symbols D HW).
Qed.

Theorem NSCL01_READOUT_DERIVES_BOTH_NULL_ORTHOGONALITIES : forall D,
  ModalLedgerWitness D -> forall t, InTime (ml_t0 D) (ml_t1 D) t ->
  dot (ml_gram D) (ml_increment D t) (gram_null0 D t)=0 /\
  dot (ml_gram D) (ml_increment D t) (gram_null1 D t)=0.
Proof.
  intros D HW t Ht; split.
  - unfold gram_null0; rewrite (mw_same_source_readout D HW t Ht (ml_u D t)).
    unfold time_source.
    rewrite (NSMG02_ACTUAL_MODAL_SOURCE_ENERGY_CANCELLATION
      (ml_space D) (ml_table D) (ml_u D t) (mw_convection_skew D HW)); ring.
  - unfold gram_null1.
    rewrite (mw_same_source_readout D HW t Ht (ml_null_field D (ml_u D t))).
    rewrite (mw_second_null_cancellation D HW t Ht); ring.
Qed.

Theorem NSCL02_POINTWISE_PHYSICAL_SCHUR_BOUND : forall D,
  ModalLedgerWitness D -> forall t, InTime (ml_t0 D) (ml_t1 D) t ->
  renewal_rate D t*renewal_rate D t <= increment_rate D t*capacity_rate D t.
Proof.
  intros D HW t Ht.
  destruct (NSCL01_READOUT_DERIVES_BOTH_NULL_ORTHOGONALITIES D HW t Ht) as [H0 H1].
  exact (NSGG20_RANK_SAFE_SCHUR_ACTION_BOUND (ml_gram D) (ml_increment D t)
    (gram_detector D t) (gram_null0 D t) (gram_null1 D t) H0 H1).
Qed.

Theorem NSCL03_NATIVE_CLOCK_DERIVES_POINTWISE_BUDGET : forall D,
  ModalLedgerWitness D -> forall t, InTime (ml_t0 D) (ml_t1 D) t ->
  2*increment_rate D t <= time_dissipation D t.
Proof.
  intros D HW t Ht.
  destruct (mw_clock_realization D HW t Ht) as [ell [seed [stages [Hell [Hend Hnorm]]]]].
  exact (NSMG30_PHYSICAL_LADDER_NORMALIZATION_GIVES_BUDGET
    (ml_space D) (ml_gram D) ell (ml_lambda D) seed stages (ml_u D t)
    (ml_increment D t) (stokes_nonnegative D HW) Hend Hnorm).
Qed.

Theorem NSCL10_MODAL_ENERGY_TIME_BINDING : forall D,
  ModalLedgerWitness D ->
  DerivativeOn (ml_t0 D) (ml_t1 D) (time_energy D)
    (fun t => -2*ml_nu D*time_dissipation D t).
Proof.
  intros D HW.
  exact (NSMG11_MODAL_ODE_GIVES_LERAY_ENERGY_DERIVATIVE
    (ml_space D) (ml_lambda D) (ml_table D) (ml_nu D)
    (ml_t0 D) (ml_t1 D) (ml_u D)
    (mw_convection_skew D HW) (mw_modal_equation D HW)).
Qed.

Theorem NSCL11_NSE_DIRECTION_GIVES_SIGNED_RENEWAL_DERIVATIVE : forall D,
  ModalLedgerWitness D ->
  DerivativeOn (ml_t0 D) (ml_t1 D) (time_potential D)
    (fun t => renewal_rate D t-time_action D t).
Proof.
  intros D HW.
  apply (NSMG40_POTENTIAL_CHAIN_AND_HEAT_GENERATOR_GIVE_RENEWAL
    (ml_space D) (ml_lambda D) (ml_table D) (ml_nu D)
    (ml_t0 D) (ml_t1 D) (ml_u D) (ml_potential D) (ml_detector D)
    (state_action D) (renewal_rate D)).
  - exact (mw_potential_chain D HW).
  - exact (mw_heat_generator D HW).
  - intros t Ht; exact (mw_same_source_readout D HW t Ht (time_detector D t)).
Qed.

Theorem NSCL20_CONTINUOUS_SIGNED_BALANCE_FROM_MODAL_DATA : forall D,
  ModalLedgerWitness D -> forall t, InTime (ml_t0 D) (ml_t1 D) t ->
  time_potential D t+ml_Y D t = time_potential D (ml_t0 D)+ml_net D t.
Proof.
  intros D HW t Ht.
  exact (NSCT30_CONTINUOUS_SIGNED_BALANCE (ml_t0 D) (ml_t1 D)
    (time_potential D) (time_action D) (renewal_rate D) (ml_Y D) (ml_net D) t
    (NSCL11_NSE_DIRECTION_GIVES_SIGNED_RENEWAL_DERIVATIVE D HW)
    (mw_action_primitive D HW) (mw_renewal_primitive D HW) Ht).
Qed.

Theorem NSCL21_CONTINUOUS_GRAM_BOUND_FROM_MODAL_DATA : forall D,
  ModalLedgerWitness D -> forall t, InTime (ml_t0 D) (ml_t1 D) t ->
  ml_net D t*ml_net D t <= ml_Q D t*ml_Z D t.
Proof.
  intros D HW t Ht.
  apply (NSCT20_CONTINUOUS_SIGNED_CAUCHY (ml_t0 D) (ml_t1 D)
    (increment_rate D) (capacity_rate D) (renewal_rate D)
    (ml_Q D) (ml_Z D) (ml_net D) t).
  - exact (mw_increment_primitive D HW).
  - exact (mw_capacity_primitive D HW).
  - exact (mw_renewal_primitive D HW).
  - intros s Hs; apply norm2_nonneg.
  - intros s Hs; apply norm2_nonneg.
  - exact (NSCL02_POINTWISE_PHYSICAL_SCHUR_BOUND D HW).
  - exact Ht.
Qed.

(* This bound is DERIVED from the modal ODE and native clock.  There is no
   integrated Leray/action budget among ModalLedgerWitness's fields. *)
Theorem NSCL22_MODAL_ENERGY_FUNDS_CONTINUOUS_INCREMENT : forall D,
  ModalLedgerWitness D -> forall t, InTime (ml_t0 D) (ml_t1 D) t ->
  ml_Q D t <= time_energy D (ml_t0 D)/(4*ml_nu D).
Proof.
  intros D HW t Ht.
  pose proof (NSCL10_MODAL_ENERGY_TIME_BINDING D HW) as HE.
  destruct (mw_increment_primitive D HW) as [HQ0 HQ].
  assert (HD : DerivativeOn (ml_t0 D) (ml_t1 D)
    (fun s => time_energy D s+4*ml_nu D*ml_Q D s)
    (fun s => -2*ml_nu D*time_dissipation D s+4*ml_nu D*increment_rate D s)).
  { apply (derivative_on_plus (ml_t0 D) (ml_t1 D)
      (time_energy D) (fun s => 4*ml_nu D*ml_Q D s)
      (fun s => -2*ml_nu D*time_dissipation D s)
      (fun s => 4*ml_nu D*increment_rate D s)).
    - exact HE.
    - exact (derivative_on_scale (ml_t0 D) (ml_t1 D)
        (ml_Q D) (increment_rate D) (4*ml_nu D) HQ). }
  assert (Horder : time_energy D t+4*ml_nu D*ml_Q D t <=
    time_energy D (ml_t0 D)+4*ml_nu D*ml_Q D (ml_t0 D)).
  { apply (NSCT01_NONPOSITIVE_DERIVATIVE_GIVES_ORDER (ml_t0 D) t
      (fun s => time_energy D s+4*ml_nu D*ml_Q D s)
      (fun s => -2*ml_nu D*time_dissipation D s+4*ml_nu D*increment_rate D s)).
    - unfold InTime in Ht; lra.
    - exact (derivative_on_restrict (ml_t0 D) (ml_t1 D) t _ _ Ht HD).
    - intros s Hs.
      assert (Hsfull : InTime (ml_t0 D) (ml_t1 D) s) by (unfold InTime in *; lra).
      pose proof (NSCL03_NATIVE_CLOCK_DERIVES_POINTWISE_BUDGET D HW s Hsfull) as Hb.
      pose proof (mw_viscosity_positive D HW) as Hnu.
      assert (Hp : 0 <= (2*ml_nu D)*(time_dissipation D s-2*increment_rate D s)).
      { apply Rmult_le_pos; lra. }
      nra. }
  rewrite HQ0 in Horder.
  assert (HE0 : 0 <= time_energy D t) by apply norm2_nonneg.
  pose proof (mw_viscosity_positive D HW) as Hnu.
  apply (Rmult_le_reg_l (4*ml_nu D)); [nra|].
  replace ((4*ml_nu D)*(time_energy D (ml_t0 D)/(4*ml_nu D)))
    with (time_energy D (ml_t0 D)) by (field; lra).
  nra.
Qed.

Definition endpoint_action D := ml_Y D (ml_t1 D).
Definition endpoint_potential D := time_potential D (ml_t1 D).
Definition endpoint_increment D := ml_Q D (ml_t1 D).
Definition endpoint_capacity D := ml_Z D (ml_t1 D).
Definition endpoint_net D := ml_net D (ml_t1 D).
Definition initial_potential D := time_potential D (ml_t0 D).
Definition initial_increment_budget D := time_energy D (ml_t0 D)/(4*ml_nu D).

(* Point can contain both cutoff and endpoint.  The common constants V0,L0
   are required uniformly, not chosen independently after each endpoint. *)
Theorem NSCL40_CONSTRUCTED_CONTINUOUS_INTEGRATED_GRAM_LEDGER :
  forall (Point : Type) (D : Point -> ModalLedgerData) V0 L0,
  0 <= V0 -> 0 <= L0 ->
  (forall p, ModalLedgerWitness (D p)) ->
  (forall p, initial_potential (D p) <= V0) ->
  (forall p, initial_increment_budget (D p) <= L0) ->
  IntegratedGramLedger Point
    (fun p => endpoint_action (D p)) (fun p => endpoint_potential (D p))
    (fun p => endpoint_increment (D p)) (fun p => endpoint_capacity (D p))
    (fun p => endpoint_net (D p)) V0 L0.
Proof.
  intros Point D V0 L0 HV HL HW HVi HLi; constructor.
  - exact HV.
  - exact HL.
  - intro p; unfold endpoint_action.
    apply (NSCT10_PRIMITIVE_NONNEGATIVE (ml_t0 (D p)) (ml_t1 (D p))
      (time_action (D p)) (ml_Y (D p)) (ml_t1 (D p))).
    + exact (mw_action_primitive (D p) (HW p)).
    + intros s Hs; exact (NSCL00_PHYSICAL_ACTION_NONNEGATIVE (D p) (HW p) s).
    + exact (endpoint_in_time (D p) (HW p)).
  - intro p; exact (mw_potential_nonnegative (D p) (HW p)
      (ml_t1 (D p)) (endpoint_in_time (D p) (HW p))).
  - intro p; unfold endpoint_increment.
    apply (NSCT10_PRIMITIVE_NONNEGATIVE (ml_t0 (D p)) (ml_t1 (D p))
      (increment_rate (D p)) (ml_Q (D p)) (ml_t1 (D p))).
    + exact (mw_increment_primitive (D p) (HW p)).
    + intros s Hs; apply norm2_nonneg.
    + exact (endpoint_in_time (D p) (HW p)).
  - intro p; unfold endpoint_capacity.
    apply (NSCT10_PRIMITIVE_NONNEGATIVE (ml_t0 (D p)) (ml_t1 (D p))
      (capacity_rate (D p)) (ml_Z (D p)) (ml_t1 (D p))).
    + exact (mw_capacity_primitive (D p) (HW p)).
    + intros s Hs; apply norm2_nonneg.
    + exact (endpoint_in_time (D p) (HW p)).
  - intro p; eapply Rle_trans.
    + exact (NSCL22_MODAL_ENERGY_FUNDS_CONTINUOUS_INCREMENT (D p) (HW p)
        (ml_t1 (D p)) (endpoint_in_time (D p) (HW p))).
    + exact (HLi p).
  - intro p.
    pose proof (NSCL20_CONTINUOUS_SIGNED_BALANCE_FROM_MODAL_DATA (D p) (HW p)
      (ml_t1 (D p)) (endpoint_in_time (D p) (HW p))) as Hb.
    pose proof (HVi p) as Hi.
    unfold endpoint_potential, endpoint_action, endpoint_net, initial_potential in *; lra.
  - intro p; exact (NSCL21_CONTINUOUS_GRAM_BOUND_FROM_MODAL_DATA (D p) (HW p)
      (ml_t1 (D p)) (endpoint_in_time (D p) (HW p))).
Qed.

Theorem NSCL50_CONTINUOUS_MODAL_CAPACITY_TO_UNIFORM_ACTION :
  forall (Point : Type) (D : Point -> ModalLedgerData) V0 L0 c Z0,
  0 <= V0 -> 0 <= L0 ->
  (forall p, ModalLedgerWitness (D p)) ->
  (forall p, initial_potential (D p) <= V0) ->
  (forall p, initial_increment_budget (D p) <= L0) ->
  ReducedCapacityBound Point (fun p => endpoint_action (D p))
    (fun p => endpoint_capacity (D p)) c Z0 ->
  forall p, endpoint_action (D p) <= action_bound V0 L0 c Z0.
Proof.
  intros Point D V0 L0 c Z0 HV HL HW HVi HLi Hcap.
  exact (NSAR20_UNIFORM_REDUCED_CAPACITY_TO_ACTION Point
    (fun p => endpoint_action (D p)) (fun p => endpoint_potential (D p))
    (fun p => endpoint_increment (D p)) (fun p => endpoint_capacity (D p))
    (fun p => endpoint_net (D p)) V0 L0 c Z0
    (NSCL40_CONSTRUCTED_CONTINUOUS_INTEGRATED_GRAM_LEDGER Point D V0 L0 HV HL HW HVi HLi)
    Hcap).
Qed.

(* The same two ownership directions as v0.49.3 remain separate.  No fake
   sequence is created, and CriticalEnergyBalance remains an explicit
   semantic input to this generic M7 branch. *)
Theorem NSCL90_CONTINUOUS_MODAL_TO_EXISTING_M7_CRITICAL_TARGET :
  forall (Point : Type) (D : Point -> ModalLedgerData)
    V0 L0 c Z0 mass nu sigma initial_mass
    (critical_mass critical_dissipation action_cost : Point -> R),
  0 <= V0 -> 0 <= L0 ->
  (forall p, ModalLedgerWitness (D p)) ->
  (forall p, initial_potential (D p) <= V0) ->
  (forall p, initial_increment_budget (D p) <= L0) ->
  ReducedCapacityBound Point (fun p => endpoint_action (D p))
    (fun p => endpoint_capacity (D p)) c Z0 ->
  ActualMassPrefixDominated Point mass (fun p => endpoint_action (D p)) ->
  Energy50.M7ActionCostRealization Point mass action_cost ->
  Energy50.CriticalEnergyBalance Point nu sigma initial_mass
    critical_mass critical_dissipation action_cost ->
  Energy50.CriticalH12Bound Point critical_mass /\
  Energy50.CriticalH32Dissipation Point critical_dissipation.
Proof.
  intros Point D V0 L0 c Z0 mass nu sigma initial_mass
    critical_mass critical_dissipation action_cost HV HL HW HVi HLi Hcap Hown Hreal Hbalance.
  exact (NSGE90_GP_KQ_GRAM_M7_CRITICAL_TARGET Point
    (fun p => endpoint_action (D p)) (fun p => endpoint_potential (D p))
    (fun p => endpoint_increment (D p)) (fun p => endpoint_capacity (D p))
    (fun p => endpoint_net (D p)) V0 L0 c Z0 mass nu sigma initial_mass
    critical_mass critical_dissipation action_cost
    (NSCL40_CONSTRUCTED_CONTINUOUS_INTEGRATED_GRAM_LEDGER Point D V0 L0 HV HL HW HVi HLi)
    Hcap Hown Hreal Hbalance).
Qed.

End NSE_CONTINUOUS_GRAM_LEDGER.
