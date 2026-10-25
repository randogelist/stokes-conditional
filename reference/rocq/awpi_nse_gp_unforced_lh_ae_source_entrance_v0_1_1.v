From Stdlib Require Import Reals String Lra Psatz Lia.
Require Import awpi_nse_gp_ae_modal_semantics_v0_23_1.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.
Require Import awpi_nse_gp_pair_source_calculus_v0_51_0.
Require Import awpi_nse_gp_fixed_allocation_v0_51_0.
Require Import awpi_nse_gp_source_storage_dynamics_v0_51_0.
Require Import awpi_nse_gp_signed_source_closure_v0_51_0.
Require Import awpi_nse_gp_unforced_operator_class_v0_1_0.
Require Import awpi_nse_gp_unforced_lh_operator_compatibility_v0_1_0.

Module NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.
Module AE := NSE_GP_AE_MODAL_SEMANTICS.
Module SSC := NSE_GP_SIGNED_SOURCE_CLOSURE.
Module UFC := NSE_GP_UNFORCED_OPERATOR_CLASS.
Module ULH := NSE_GP_UNFORCED_LH_OPERATOR_COMPATIBILITY.
Import NSE_KQ_FINITE_ALGEBRA NSE_CONTINUOUS_TIME_CALCULUS.
Import NSE_GALERKIN_MODAL_CALCULUS NSE_GP_PAIR_SOURCE_CALCULUS.
Import NSE_GP_FIXED_ALLOCATION NSE_GP_SOURCE_STORAGE_DYNAMICS.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* Leray-Hopf compatible source semantics.                              *)
(*                                                                    *)
(* GPSourceWitness51 uses a classical derivative at EVERY time.       *)
(* A general LH trajectory naturally supplies an a.e. modal equation. *)
(* The record below separates the a.e. derivative REPRESENTATIVE from *)
(* the later analytic theorem identifying it with an AC weak          *)
(* derivative and integrating the resulting ledgers.                  *)
(* ------------------------------------------------------------------ *)

Record AEGPTimeData51 (D : SSC.GPSourceData51) : Type := {
  ae51_du : R -> Vec;
  ae51_good : R -> Prop
}.

Definition AEModalPath51
  (D : SSC.GPSourceData51)
  (A : AEGPTimeData51 D) : Prop :=
  forall t : R,
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    ae51_good D A t ->
    forall i : nat,
      (i < ps_space (SSC.g51_packets D))%nat ->
      ae51_du D A t i =
      modal_rhs
        (ps_space (SSC.g51_packets D))
        (packet_lambda (SSC.g51_packets D))
        (SSC.g51_table D)
        (SSC.g51_nu D)
        (SSC.g51_u D t)
        i.

Record AEGPSourceWitness51
  (CoNull : (R -> Prop) -> Prop)
  (D : SSC.GPSourceData51)
  (A : AEGPTimeData51 D) : Prop := {
  aew51_conull_calculus : AE.CoNullCalculus CoNull;
  aew51_order : SSC.g51_t0 D <= SSC.g51_t1 D;
  aew51_nu : 0 < SSC.g51_nu D;
  aew51_Z : 0 < SSC.g51_Z D;
  aew51_indices : PacketIndices51 (SSC.g51_packets D);
  aew51_positive : PacketPositive51 (SSC.g51_packets D);
  aew51_geometry : PacketDecayGeometry51 (SSC.g51_packets D);
  aew51_census : PacketGeometricCensus51 (SSC.g51_packets D) (SSC.g51_Z D);
  aew51_coefficients : PacketCoefficientIdentity51 (SSC.g51_packets D) (SSC.g51_table D);
  aew51_skew : SkewTable (ps_space (SSC.g51_packets D)) (SSC.g51_table D);
  aew51_conull : CoNull (ae51_good D A);
  aew51_path : AEModalPath51 D A
}.

(* Every classical GPSourceWitness is a special case of the a.e. source
   witness: take the formal derivative representative to be modal_rhs and
   the good-time predicate to be True.  Thus the new entrance semantics
   strictly weakens the time regularity demanded by the old donor. *)
Definition classical_ae_time_data51
  (D : SSC.GPSourceData51) : AEGPTimeData51 D :=
  {| ae51_du := fun t =>
       modal_rhs
         (ps_space (SSC.g51_packets D))
         (packet_lambda (SSC.g51_packets D))
         (SSC.g51_table D)
         (SSC.g51_nu D)
         (SSC.g51_u D t);
     ae51_good := fun _ => True |}.

Theorem UAE00_CLASSICAL_GPSOURCE_WITNESS_EMBEDS_IN_AE_SOURCE_WITNESS :
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall D : SSC.GPSourceData51,
    SSC.GPSourceWitness51 D ->
    AEGPSourceWitness51 CoNull D (classical_ae_time_data51 D).
Proof.
  intros CoNull HC D HW.
  refine
    {| aew51_conull_calculus := HC;
       aew51_order := SSC.gw51_order D HW;
       aew51_nu := SSC.gw51_nu D HW;
       aew51_Z := SSC.gw51_Z D HW;
       aew51_indices := SSC.gw51_indices D HW;
       aew51_positive := SSC.gw51_positive D HW;
       aew51_geometry := SSC.gw51_geometry D HW;
       aew51_census := SSC.gw51_census D HW;
       aew51_coefficients := SSC.gw51_coefficients D HW;
       aew51_skew := SSC.gw51_skew D HW;
       aew51_conull := _;
       aew51_path := _ |}.
  - change (CoNull (fun _ : R => True)).
    exact (AE.cn_all CoNull HC).
  - intros t Ht Hgood i Hi.
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Algebraic chain-rule rates on the a.e. derivative representative.   *)
(* No classical derivative, primitive, or integration theorem is used. *)
(* ------------------------------------------------------------------ *)

Definition ae_critical_chain_rate51
  (D : SSC.GPSourceData51)
  (A : AEGPTimeData51 D)
  (t : R) : R :=
  2 * sum (ps_space (SSC.g51_packets D))
    (fun i =>
      ps_radius (SSC.g51_packets D) i *
      SSC.g51_u D t i *
      ae51_du D A t i).

Definition ae_pair_chain_rate51
  (D : SSC.GPSourceData51)
  (A : AEGPTimeData51 D)
  (t : R) (i j : nat) : R :=
  ae51_du D A t i * SSC.g51_u D t j
  + SSC.g51_u D t i * ae51_du D A t j.

Definition ae_source_chain_rate51
  (D : SSC.GPSourceData51)
  (A : AEGPTimeData51 D)
  (t : R) : R :=
  2 * sum (ps_count (SSC.g51_packets D))
    (fun p =>
      packet_hcoef (SSC.g51_packets D) (SSC.g51_nu D) (SSC.g51_Z D) p *
      packet_q (SSC.g51_packets D) (SSC.g51_u D t) p *
      ae_pair_chain_rate51 D A t
        (ps_left (SSC.g51_packets D) p)
        (ps_right (SSC.g51_packets D) p)).

Definition ae_combined_chain_rate51
  (D : SSC.GPSourceData51)
  (A : AEGPTimeData51 D)
  (t : R) : R :=
  ae_critical_chain_rate51 D A t
  + ae_source_chain_rate51 D A t / SSC.g51_nu D.

Lemma UAE10_AE_WEIGHTED_MODAL_PAIRING :
  forall CoNull : (R -> Prop) -> Prop,
  forall D : SSC.GPSourceData51,
  forall A : AEGPTimeData51 D,
  forall HW : AEGPSourceWitness51 CoNull D A,
  forall t : R,
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    ae51_good D A t ->
    forall s : Vec,
      sum (ps_space (SSC.g51_packets D))
        (fun i => s i * SSC.g51_u D t i * ae51_du D A t i)
      =
      - SSC.g51_nu D *
        cut_dissipation
          (ps_space (SSC.g51_packets D))
          (packet_lambda (SSC.g51_packets D))
          s
          (SSC.g51_u D t)
      +
        cut_current
          (ps_space (SSC.g51_packets D))
          (SSC.g51_table D)
          s
          (SSC.g51_u D t).
Proof.
  intros CoNull D A HW t Ht Hgood s.
  transitivity
    (sum (ps_space (SSC.g51_packets D))
      (fun i => s i * SSC.g51_u D t i *
        modal_rhs
          (ps_space (SSC.g51_packets D))
          (packet_lambda (SSC.g51_packets D))
          (SSC.g51_table D)
          (SSC.g51_nu D)
          (SSC.g51_u D t) i)).
  - apply sum_ext; intros i Hi.
    rewrite (aew51_path CoNull D A HW t Ht Hgood i Hi).
    reflexivity.
  - transitivity
      (sum (ps_space (SSC.g51_packets D))
        (fun i =>
          (- SSC.g51_nu D) *
            (s i * packet_lambda (SSC.g51_packets D) i *
             SSC.g51_u D t i * SSC.g51_u D t i)
          - modal_source
              (ps_space (SSC.g51_packets D))
              (SSC.g51_table D)
              (SSC.g51_u D t) i *
            (s i * SSC.g51_u D t i))).
    + apply sum_ext; intros i Hi.
      unfold modal_rhs.
      ring.
    + rewrite sum_sub, sum_scale.
      unfold cut_dissipation, cut_current, dot, mul.
      ring.
Qed.

Theorem UAE11_AE_CRITICAL_CHAIN_RATE_IS_NSE_CRITICAL_RATE :
  forall CoNull : (R -> Prop) -> Prop,
  forall D : SSC.GPSourceData51,
  forall A : AEGPTimeData51 D,
  forall HW : AEGPSourceWitness51 CoNull D A,
  forall t : R,
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    ae51_good D A t ->
    ae_critical_chain_rate51 D A t = SSC.g_mrate D t.
Proof.
  intros CoNull D A HW t Ht Hgood.
  unfold ae_critical_chain_rate51, SSC.g_mrate, critical_rate,
         critical_dissipation.
  rewrite (UAE10_AE_WEIGHTED_MODAL_PAIRING
    CoNull D A HW t Ht Hgood (ps_radius (SSC.g51_packets D))).
  ring.
Qed.

Lemma UAE12_AE_PAIR_CHAIN_RATE_IS_PAIR_RHS :
  forall CoNull : (R -> Prop) -> Prop,
  forall D : SSC.GPSourceData51,
  forall A : AEGPTimeData51 D,
  forall HW : AEGPSourceWitness51 CoNull D A,
  forall t : R,
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    ae51_good D A t ->
    forall i j : nat,
      (i < ps_space (SSC.g51_packets D))%nat ->
      (j < ps_space (SSC.g51_packets D))%nat ->
      ae_pair_chain_rate51 D A t i j
      =
      pair_rhs
        (ps_space (SSC.g51_packets D))
        (packet_lambda (SSC.g51_packets D))
        (SSC.g51_table D)
        (SSC.g51_nu D)
        (SSC.g51_u D t) i j.
Proof.
  intros CoNull D A HW t Ht Hgood i j Hi Hj.
  unfold ae_pair_chain_rate51.
  rewrite (aew51_path CoNull D A HW t Ht Hgood i Hi).
  rewrite (aew51_path CoNull D A HW t Ht Hgood j Hj).
  unfold pair_rhs, pair_value, pair_regeneration, modal_rhs.
  ring.
Qed.

Theorem UAE13_AE_SOURCE_CHAIN_RATE_IS_GP_SOURCE_RATE :
  forall CoNull : (R -> Prop) -> Prop,
  forall D : SSC.GPSourceData51,
  forall A : AEGPTimeData51 D,
  forall HW : AEGPSourceWitness51 CoNull D A,
  forall t : R,
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    ae51_good D A t ->
    ae_source_chain_rate51 D A t = source_rate
      (SSC.g51_packets D) (SSC.g51_nu D) (SSC.g51_Z D)
      (SSC.g51_table D) (SSC.g51_u D t).
Proof.
  intros CoNull D A HW t Ht Hgood.
  unfold ae_source_chain_rate51.
  transitivity
    (2 * sum (ps_count (SSC.g51_packets D))
      (fun p =>
        packet_hcoef (SSC.g51_packets D) (SSC.g51_nu D) (SSC.g51_Z D) p *
        packet_q (SSC.g51_packets D) (SSC.g51_u D t) p *
        pair_rhs
          (ps_space (SSC.g51_packets D))
          (packet_lambda (SSC.g51_packets D))
          (SSC.g51_table D)
          (SSC.g51_nu D)
          (SSC.g51_u D t)
          (ps_left (SSC.g51_packets D) p)
          (ps_right (SSC.g51_packets D) p))).
  - f_equal.
    apply sum_ext; intros p Hp.
    rewrite (UAE12_AE_PAIR_CHAIN_RATE_IS_PAIR_RHS
      CoNull D A HW t Ht Hgood
      (ps_left (SSC.g51_packets D) p)
      (ps_right (SSC.g51_packets D) p)).
    + reflexivity.
    + exact (proj1 (proj2 (aew51_indices CoNull D A HW p Hp))).
    + exact (proj2 (proj2 (aew51_indices CoNull D A HW p Hp))).
  - unfold source_rate, source_production, source_dissipation.
    rewrite <- sum_scale, <- sum_sub.
    apply sum_ext; intros p Hp.
    unfold pair_rhs, pair_value, pair_regeneration,
           packet_q, packet_regeneration.
    ring.
Qed.

Theorem UAE14_AE_COMBINED_CHAIN_RATE_IS_GP_COMBINED_RATE :
  forall CoNull : (R -> Prop) -> Prop,
  forall D : SSC.GPSourceData51,
  forall A : AEGPTimeData51 D,
  forall HW : AEGPSourceWitness51 CoNull D A,
  forall t : R,
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    ae51_good D A t ->
    ae_combined_chain_rate51 D A t = SSC.g_wrate D t.
Proof.
  intros CoNull D A HW t Ht Hgood.
  unfold ae_combined_chain_rate51, SSC.g_wrate, combined_rate.
  rewrite (UAE11_AE_CRITICAL_CHAIN_RATE_IS_NSE_CRITICAL_RATE
    CoNull D A HW t Ht Hgood).
  rewrite (UAE13_AE_SOURCE_CHAIN_RATE_IS_GP_SOURCE_RATE
    CoNull D A HW t Ht Hgood).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The physical source and M7 coercive geometry already hold pointwise  *)
(* on the same a.e. witness.  They do not require the stronger          *)
(* everywhere-classical ModalPath.                                      *)
(* ------------------------------------------------------------------ *)

Theorem UAE20_AE_WITNESS_RECONSTRUCTS_EXACT_NSE_SOURCE :
  forall CoNull : (R -> Prop) -> Prop,
  forall D : SSC.GPSourceData51,
  forall A : AEGPTimeData51 D,
    AEGPSourceWitness51 CoNull D A ->
    PacketSourceReconstruction51 (SSC.g51_packets D) (SSC.g51_table D).
Proof.
  intros CoNull D A HW.
  exact (NSFA45_COEFFICIENT_IDENTITY_CONSTRUCTS_FULL_SOURCE
    (SSC.g51_packets D) (SSC.g51_table D)
    (aew51_indices CoNull D A HW)
    (aew51_coefficients CoNull D A HW)).
Qed.

Theorem UAE21_AE_WITNESS_HAS_POINTWISE_SOURCE_COERCIVITY :
  forall CoNull : (R -> Prop) -> Prop,
  forall D : SSC.GPSourceData51,
  forall A : AEGPTimeData51 D,
    AEGPSourceWitness51 CoNull D A ->
    forall t : R,
      cut_current
        (ps_space (SSC.g51_packets D))
        (SSC.g51_table D)
        (ps_radius (SSC.g51_packets D))
        (SSC.g51_u D t)
      *
      cut_current
        (ps_space (SSC.g51_packets D))
        (SSC.g51_table D)
        (ps_radius (SSC.g51_packets D))
        (SSC.g51_u D t)
      <=
      source_mass (SSC.g51_packets D) (SSC.g51_Z D) (SSC.g51_u D t)
      * critical_dissipation (SSC.g51_packets D) (SSC.g51_u D t).
Proof.
  intros CoNull D A HW t.
  apply NSSD20_NO_OVERLAP_ACTUAL_SOURCE_RECEIPT.
  - exact (aew51_Z CoNull D A HW).
  - exact (aew51_indices CoNull D A HW).
  - exact (aew51_positive CoNull D A HW).
  - exact (aew51_census CoNull D A HW).
  - exact (UAE20_AE_WITNESS_RECONSTRUCTS_EXACT_NSE_SOURCE CoNull D A HW).
Qed.

Theorem UAE22_AE_WITNESS_SOURCE_DAMPING_FUNDS_ACTION :
  forall CoNull : (R -> Prop) -> Prop,
  forall D : SSC.GPSourceData51,
  forall A : AEGPTimeData51 D,
    AEGPSourceWitness51 CoNull D A ->
    forall t : R,
      source_mass (SSC.g51_packets D) (SSC.g51_Z D) (SSC.g51_u D t)
      <=
      source_dissipation
        (SSC.g51_packets D) (SSC.g51_nu D) (SSC.g51_Z D) (SSC.g51_u D t).
Proof.
  intros CoNull D A HW t.
  apply NSSD31_DAMPING_FUNDS_ACTUAL_SOURCE_MASS.
  - exact (aew51_nu CoNull D A HW).
  - exact (aew51_Z CoNull D A HW).
  - exact (aew51_indices CoNull D A HW).
  - exact (aew51_positive CoNull D A HW).
  - exact (aew51_geometry CoNull D A HW).
Qed.

Definition AELocalClosedLedger51
  (CoNull : (R -> Prop) -> Prop)
  (D : SSC.GPSourceData51)
  (A : AEGPTimeData51 D)
  (HW : AEGPSourceWitness51 CoNull D A) : Prop :=
  forall t : R,
    InTime (SSC.g51_t0 D) (SSC.g51_t1 D) t ->
    ae51_good D A t ->
    ae_critical_chain_rate51 D A t = SSC.g_mrate D t /\
    ae_source_chain_rate51 D A t = source_rate
      (SSC.g51_packets D) (SSC.g51_nu D) (SSC.g51_Z D)
      (SSC.g51_table D) (SSC.g51_u D t) /\
    ae_combined_chain_rate51 D A t = SSC.g_wrate D t.

Theorem UAE30_AE_UNFORCED_SOURCE_HAS_EXACT_LOCAL_CLOSED_LEDGER :
  forall CoNull : (R -> Prop) -> Prop,
  forall D : SSC.GPSourceData51,
  forall A : AEGPTimeData51 D,
  forall HW : AEGPSourceWitness51 CoNull D A,
    AELocalClosedLedger51 CoNull D A HW.
Proof.
  intros CoNull D A HW t Ht Hgood.
  split.
  - exact (UAE11_AE_CRITICAL_CHAIN_RATE_IS_NSE_CRITICAL_RATE
      CoNull D A HW t Ht Hgood).
  - split.
    + exact (UAE13_AE_SOURCE_CHAIN_RATE_IS_GP_SOURCE_RATE
        CoNull D A HW t Ht Hgood).
    + exact (UAE14_AE_COMBINED_CHAIN_RATE_IS_GP_COMBINED_RATE
        CoNull D A HW t Ht Hgood).
Qed.

(* ------------------------------------------------------------------ *)
(* Exact new claim boundary.                                            *)
(*                                                                     *)
(* The local unforced GP/BKQR source algebra is now compatible with     *)
(* a.e. Leray-Hopf time evolution.  The next analytic theorem is no     *)
(* longer "make every LH path classically differentiable everywhere".  *)
(* It is the correct AC/a.e.-integration theorem:                       *)
(*                                                                     *)
(*   a.e. local closed ledger + AC primitives                           *)
(*       -> integrated source ledger / SignedProductionBudget inputs.   *)
(*                                                                     *)
(* The internal signed-production estimate itself remains the M7        *)
(* research frontier.                                                   *)
(* ------------------------------------------------------------------ *)

Definition LHWeakToAESourceWitnessFrontier : Prop := True.
Definition AELedgerIntegrationFrontier : Prop := True.
Definition InternalSignedProductionFrontier : Prop := True.

Definition STATUS : string :=
  "NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE_V0_1_0_AE_MODAL_SOURCE_LEDGER_KERNEL_TARGET_CLASSICAL_WITNESS_EMBEDS_AE_SOURCE_COERCIVITY_KERNEL_TARGET_INTEGRATION_AND_INTERNAL_PAYMENT_EXPLICIT_FRONTIERS_NO_ADMITTED"%string.

End NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.

Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.AEGPTimeData51.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.AEModalPath51.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.AEGPSourceWitness51.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE00_CLASSICAL_GPSOURCE_WITNESS_EMBEDS_IN_AE_SOURCE_WITNESS.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE10_AE_WEIGHTED_MODAL_PAIRING.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE11_AE_CRITICAL_CHAIN_RATE_IS_NSE_CRITICAL_RATE.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE12_AE_PAIR_CHAIN_RATE_IS_PAIR_RHS.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE13_AE_SOURCE_CHAIN_RATE_IS_GP_SOURCE_RATE.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE14_AE_COMBINED_CHAIN_RATE_IS_GP_COMBINED_RATE.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE20_AE_WITNESS_RECONSTRUCTS_EXACT_NSE_SOURCE.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE21_AE_WITNESS_HAS_POINTWISE_SOURCE_COERCIVITY.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE22_AE_WITNESS_SOURCE_DAMPING_FUNDS_ACTION.
Check NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE30_AE_UNFORCED_SOURCE_HAS_EXACT_LOCAL_CLOSED_LEDGER.

Print Assumptions NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE00_CLASSICAL_GPSOURCE_WITNESS_EMBEDS_IN_AE_SOURCE_WITNESS.
Print Assumptions NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE11_AE_CRITICAL_CHAIN_RATE_IS_NSE_CRITICAL_RATE.
Print Assumptions NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE13_AE_SOURCE_CHAIN_RATE_IS_GP_SOURCE_RATE.
Print Assumptions NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE21_AE_WITNESS_HAS_POINTWISE_SOURCE_COERCIVITY.
Print Assumptions NSE_GP_UNFORCED_LH_AE_SOURCE_ENTRANCE.UAE30_AE_UNFORCED_SOURCE_HAS_EXACT_LOCAL_CLOSED_LEDGER.
