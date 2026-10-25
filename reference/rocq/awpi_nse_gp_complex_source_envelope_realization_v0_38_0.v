
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_perspective_action_v0_11_2.
Require Import awpi_nse_gp_closed_action_envelope_v0_19_2.
Require Import awpi_nse_gp_leray_modal_triad_adapter_v0_13_3.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_gp_source_class_ownership_v0_25_4.
Require Import awpi_nse_gp_parent_degree_reproduction_v0_26_0.
Require Import awpi_nse_gp_to_m7_route_v0_28_3.
Require Import awpi_nse_gp_gk_cohomology_realization_v0_35_3.
Require Import awpi_nse_gp_three_leg_route_realization_v0_36_4.
Require Import awpi_nse_gp_complex_three_leg_realization_v0_37_4.

Import ListNotations.
Open Scope R_scope.

Module NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.

Module CE := NSE_GP_CLOSED_ACTION_ENVELOPE.
Module LM := NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.
Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module SO := NSE_GP_SOURCE_CLASS_OWNERSHIP.
Module PR := NSE_GP_PARENT_DEGREE_REPRODUCTION.
Module MR := NSE_GP_TO_M7_ROUTE.
Module GK := NSE_GP_GK_COHOMOLOGY_REALIZATION.
Module TL := NSE_GP_THREE_LEG_ROUTE_REALIZATION.
Module CTL := NSE_GP_COMPLEX_THREE_LEG_REALIZATION.

(* ===================================================================== *)
(* Exact complex norm algebra                                             *)
(* ===================================================================== *)

Definition cabs2 (z : CH.C2) : R :=
  CH.cre z * CH.cre z + CH.cim z * CH.cim z.

Theorem CSER00_CABS2_NONNEG :
  forall z : CH.C2,
    0 <= cabs2 z.
Proof.
  intro z.
  unfold cabs2.
  pose proof (Rle_0_sqr (CH.cre z)) as Hr.
  pose proof (Rle_0_sqr (CH.cim z)) as Hi.
  unfold Rsqr in Hr, Hi.
  nra.
Qed.

Theorem CSER01_CABS2_CONJ :
  forall z : CH.C2,
    cabs2 (CH.cconj z) = cabs2 z.
Proof.
  intros [zr zi].
  unfold cabs2, CH.cconj, CH.cre, CH.cim.
  simpl.
  ring.
Qed.

Theorem CSER02_CABS2_CMUL :
  forall z w : CH.C2,
    cabs2 (CH.cmul z w) = cabs2 z * cabs2 w.
Proof.
  intros [zr zi] [wr wi].
  unfold cabs2, CH.cmul, CH.cre, CH.cim.
  simpl.
  ring.
Qed.

Theorem CSER03_REAL_PART_SQUARE_LE_CABS2 :
  forall z : CH.C2,
    CH.cre z * CH.cre z <= cabs2 z.
Proof.
  intro z.
  unfold cabs2.
  pose proof (Rle_0_sqr (CH.cim z)) as Hi.
  unfold Rsqr in Hi.
  nra.
Qed.

Theorem CSER04_POS_SQUARE_LE_SQUARE :
  forall x : R,
    LM.pos x * LM.pos x <= x * x.
Proof.
  intro x.
  unfold LM.pos.
  destruct (Rle_dec 0 x) as [Hx | Hx].
  - rewrite (Rabs_pos_eq x Hx).
    ring_simplify.
    lra.
  - assert (Hlt : x < 0) by lra.
    rewrite (Rabs_left x Hlt).
    ring_simplify.
    pose proof (Rle_0_sqr x) as Hsq.
    unfold Rsqr in Hsq.
    nra.
Qed.

(* ===================================================================== *)
(* Canonical source-leg capacities and budgets                            *)
(* ===================================================================== *)

Definition source1_capacity
  (C Nk up uq : CH.C2) : R :=
  cabs2 Nk.

Definition source1_budget
  (C Nk up uq : CH.C2) : R :=
  cabs2 C * cabs2 up * cabs2 uq.

Definition source2_capacity
  (C uk Np uq : CH.C2) : R :=
  cabs2 Np.

Definition source2_budget
  (C uk Np uq : CH.C2) : R :=
  cabs2 C * cabs2 uk * cabs2 uq.

Definition source3_capacity
  (C uk up Nq : CH.C2) : R :=
  cabs2 Nq.

Definition source3_budget
  (C uk up Nq : CH.C2) : R :=
  cabs2 C * cabs2 uk * cabs2 up.

Theorem CSER10_SOURCE1_RAW_SQUARE_BOUND :
  forall C Nk up uq : CH.C2,
    CH.csource1 C Nk up uq * CH.csource1 C Nk up uq
    <=
    source1_capacity C Nk up uq
    * source1_budget C Nk up uq.
Proof.
  intros C Nk up uq.
  unfold CH.csource1.
  pose proof
    (CSER03_REAL_PART_SQUARE_LE_CABS2
      (CH.cmul
        (CH.cmul
          (CH.cmul C (CH.cconj Nk))
          up)
        uq)) as H.
  rewrite CSER02_CABS2_CMUL in H.
  rewrite CSER02_CABS2_CMUL in H.
  rewrite CSER02_CABS2_CMUL in H.
  rewrite CSER01_CABS2_CONJ in H.
  unfold source1_capacity, source1_budget.
  nra.
Qed.

Theorem CSER11_SOURCE2_RAW_SQUARE_BOUND :
  forall C uk Np uq : CH.C2,
    CH.csource2 C uk Np uq * CH.csource2 C uk Np uq
    <=
    source2_capacity C uk Np uq
    * source2_budget C uk Np uq.
Proof.
  intros C uk Np uq.
  unfold CH.csource2.
  pose proof
    (CSER03_REAL_PART_SQUARE_LE_CABS2
      (CH.cmul
        (CH.cmul
          (CH.cmul C (CH.cconj uk))
          Np)
        uq)) as H.
  rewrite CSER02_CABS2_CMUL in H.
  rewrite CSER02_CABS2_CMUL in H.
  rewrite CSER02_CABS2_CMUL in H.
  rewrite CSER01_CABS2_CONJ in H.
  unfold source2_capacity, source2_budget.
  nra.
Qed.

Theorem CSER12_SOURCE3_RAW_SQUARE_BOUND :
  forall C uk up Nq : CH.C2,
    CH.csource3 C uk up Nq * CH.csource3 C uk up Nq
    <=
    source3_capacity C uk up Nq
    * source3_budget C uk up Nq.
Proof.
  intros C uk up Nq.
  unfold CH.csource3.
  pose proof
    (CSER03_REAL_PART_SQUARE_LE_CABS2
      (CH.cmul
        (CH.cmul
          (CH.cmul C (CH.cconj uk))
          up)
        Nq)) as H.
  rewrite CSER02_CABS2_CMUL in H.
  rewrite CSER02_CABS2_CMUL in H.
  rewrite CSER02_CABS2_CMUL in H.
  rewrite CSER01_CABS2_CONJ in H.
  unfold source3_capacity, source3_budget.
  nra.
Qed.

Theorem CSER20_SOURCE1_ENVELOPE :
  forall C Nk up uq : CH.C2,
    CE.ActionEnvelope
      (LM.pos (CH.csource1 C Nk up uq))
      (source1_capacity C Nk up uq)
      (source1_budget C Nk up uq).
Proof.
  intros C Nk up uq.
  unfold CE.ActionEnvelope.
  repeat split.
  - unfold source1_capacity.
    apply CSER00_CABS2_NONNEG.
  - unfold source1_budget.
    apply Rmult_le_pos.
    + apply Rmult_le_pos;
      apply CSER00_CABS2_NONNEG.
    + apply CSER00_CABS2_NONNEG.
  - eapply Rle_trans.
    + apply CSER04_POS_SQUARE_LE_SQUARE.
    + apply CSER10_SOURCE1_RAW_SQUARE_BOUND.
Qed.

Theorem CSER21_SOURCE2_ENVELOPE :
  forall C uk Np uq : CH.C2,
    CE.ActionEnvelope
      (LM.pos (CH.csource2 C uk Np uq))
      (source2_capacity C uk Np uq)
      (source2_budget C uk Np uq).
Proof.
  intros C uk Np uq.
  unfold CE.ActionEnvelope.
  repeat split.
  - unfold source2_capacity.
    apply CSER00_CABS2_NONNEG.
  - unfold source2_budget.
    apply Rmult_le_pos.
    + apply Rmult_le_pos;
      apply CSER00_CABS2_NONNEG.
    + apply CSER00_CABS2_NONNEG.
  - eapply Rle_trans.
    + apply CSER04_POS_SQUARE_LE_SQUARE.
    + apply CSER11_SOURCE2_RAW_SQUARE_BOUND.
Qed.

Theorem CSER22_SOURCE3_ENVELOPE :
  forall C uk up Nq : CH.C2,
    CE.ActionEnvelope
      (LM.pos (CH.csource3 C uk up Nq))
      (source3_capacity C uk up Nq)
      (source3_budget C uk up Nq).
Proof.
  intros C uk up Nq.
  unfold CE.ActionEnvelope.
  repeat split.
  - unfold source3_capacity.
    apply CSER00_CABS2_NONNEG.
  - unfold source3_budget.
    apply Rmult_le_pos.
    + apply Rmult_le_pos;
      apply CSER00_CABS2_NONNEG.
    + apply CSER00_CABS2_NONNEG.
  - eapply Rle_trans.
    + apply CSER04_POS_SQUARE_LE_SQUARE.
    + apply CSER12_SOURCE3_RAW_SQUARE_BOUND.
Qed.

(* ===================================================================== *)
(* Actual complex triad certificate WITHOUT source-envelope assumptions   *)
(* ===================================================================== *)

Record ComplexTriadNormCertificate : Type := {
  cn_C : CH.C2;
  cn_uk : CH.C2;
  cn_up : CH.C2;
  cn_uq : CH.C2;

  cn_duk : CH.C2;
  cn_dup : CH.C2;
  cn_duq : CH.C2;

  cn_Nk : CH.C2;
  cn_Np : CH.C2;
  cn_Nq : CH.C2;

  cn_nu : R;
  cn_lk : R;
  cn_lp : R;
  cn_lq : R;
  cn_dc : R;

  cn_modal :
    CH.ComplexTriadCertificate
      cn_C cn_uk cn_up cn_uq
      cn_duk cn_dup cn_duq
      cn_Nk cn_Np cn_Nq
      cn_nu cn_lk cn_lp cn_lq cn_dc
}.

Definition build_complex_physical_from_norm
  (T : ComplexTriadNormCertificate)
  : CTL.ComplexThreeLegPhysicalCertificate :=
  {|
    CTL.ctl_C := cn_C T;
    CTL.ctl_uk := cn_uk T;
    CTL.ctl_up := cn_up T;
    CTL.ctl_uq := cn_uq T;

    CTL.ctl_duk := cn_duk T;
    CTL.ctl_dup := cn_dup T;
    CTL.ctl_duq := cn_duq T;

    CTL.ctl_Nk := cn_Nk T;
    CTL.ctl_Np := cn_Np T;
    CTL.ctl_Nq := cn_Nq T;

    CTL.ctl_nu := cn_nu T;
    CTL.ctl_lk := cn_lk T;
    CTL.ctl_lp := cn_lp T;
    CTL.ctl_lq := cn_lq T;
    CTL.ctl_dc := cn_dc T;

    CTL.ctl_modal := cn_modal T;

    CTL.ctl_dk :=
      source1_capacity (cn_C T) (cn_Nk T) (cn_up T) (cn_uq T);

    CTL.ctl_dp :=
      source2_capacity (cn_C T) (cn_uk T) (cn_Np T) (cn_uq T);

    CTL.ctl_dq :=
      source3_capacity (cn_C T) (cn_uk T) (cn_up T) (cn_Nq T);

    CTL.ctl_Mk :=
      source1_budget (cn_C T) (cn_Nk T) (cn_up T) (cn_uq T);

    CTL.ctl_Mp :=
      source2_budget (cn_C T) (cn_uk T) (cn_Np T) (cn_uq T);

    CTL.ctl_Mq :=
      source3_budget (cn_C T) (cn_uk T) (cn_up T) (cn_Nq T);

    CTL.ctl_env_k :=
      CSER20_SOURCE1_ENVELOPE
        (cn_C T) (cn_Nk T) (cn_up T) (cn_uq T);

    CTL.ctl_env_p :=
      CSER21_SOURCE2_ENVELOPE
        (cn_C T) (cn_uk T) (cn_Np T) (cn_uq T);

    CTL.ctl_env_q :=
      CSER22_SOURCE3_ENVELOPE
        (cn_C T) (cn_uk T) (cn_up T) (cn_Nq T)
  |}.

Theorem CSER30_NORM_TRIAD_CONSTRUCTS_COMPLEX_PHYSICAL :
  forall T : ComplexTriadNormCertificate,
    exists P : CTL.ComplexThreeLegPhysicalCertificate,
      CTL.ctl_C P = cn_C T /\
      CTL.ctl_uk P = cn_uk T /\
      CTL.ctl_up P = cn_up T /\
      CTL.ctl_uq P = cn_uq T.
Proof.
  intro T.
  exists (build_complex_physical_from_norm T).
  repeat split; reflexivity.
Qed.

Theorem CSER31_NORM_TRIAD_CONSTRUCTS_PARENT_ROUTE :
  forall T : ComplexTriadNormCertificate,
    exists P : PR.ParentRoute 3,
      PR.pr_source_class 3 P
      =
      CTL.ctl_parent_class (build_complex_physical_from_norm T).
Proof.
  intro T.
  exact
    (CTL.CTL20_COMPLEX_TRIAD_CONSTRUCTS_PARENT_ROUTE
      (build_complex_physical_from_norm T)).
Qed.

Theorem CSER32_NORM_TRIAD_ROUTE_REPRODUCTION :
  forall T : ComplexTriadNormCertificate,
    4 *
      PR.route_child_action
        (TL.build_three_leg_parent_route
          (CTL.build_complex_three_leg_physical_route
            (build_complex_physical_from_norm T)))
    <=
      PR.pr_parent_action 3
        (TL.build_three_leg_parent_route
          (CTL.build_complex_three_leg_physical_route
            (build_complex_physical_from_norm T)))
      +
      PR.pr_legal_cost 3
        (TL.build_three_leg_parent_route
          (CTL.build_complex_three_leg_physical_route
            (build_complex_physical_from_norm T))).
Proof.
  intro T.
  apply CTL.CTL21_COMPLEX_ROUTE_REPRODUCTION.
Qed.

Definition build_norm_three_leg_route
  (T : ComplexTriadNormCertificate)
  : TL.ThreeLegPhysicalRoute :=
  CTL.build_complex_three_leg_physical_route
    (build_complex_physical_from_norm T).

Definition build_norm_three_leg_routes
  (Ts : list ComplexTriadNormCertificate)
  : list TL.ThreeLegPhysicalRoute :=
  map build_norm_three_leg_route Ts.

(* ===================================================================== *)
(* Sequence-level P reduction                                             *)
(* ===================================================================== *)

Record ComplexNormGKSequenceCertificate : Type := {
  cng_action : nat -> R;
  cng_triads : nat -> list ComplexTriadNormCertificate;

  cng_scale_paid : nat -> R;
  cng_future_paid : nat -> R;
  cng_residual_paid : nat -> R;

  cng_action_nonnegative :
    forall n : nat, 0 <= cng_action n;

  cng_next_owned :
    forall n : nat,
      cng_action (S n)
      <=
      PR.forest_child_action
        (map TL.build_three_leg_parent_route
          (build_norm_three_leg_routes (cng_triads n)));

  cng_parent_paid :
    forall n : nat,
      PR.forest_parent_action
        (map TL.build_three_leg_parent_route
          (build_norm_three_leg_routes (cng_triads n)))
      <= cng_action n;

  cng_legal_cost_split :
    forall n : nat,
      PR.forest_legal_cost
        (map TL.build_three_leg_parent_route
          (build_norm_three_leg_routes (cng_triads n)))
      <=
      cng_scale_paid n
      + cng_future_paid n
      + cng_residual_paid n;

  cng_scale_gk :
    GK.GKChannelCertificate cng_scale_paid;

  cng_future_gk :
    GK.GKChannelCertificate cng_future_paid;

  cng_residual_gk :
    GK.GKChannelCertificate cng_residual_paid
}.

Definition build_three_leg_gk_from_norm
  (C : ComplexNormGKSequenceCertificate)
  : TL.ThreeLegGKSequenceCertificate :=
  {|
    TL.tlg_action := cng_action C;
    TL.tlg_physical_routes :=
      fun n => build_norm_three_leg_routes (cng_triads C n);

    TL.tlg_scale_paid := cng_scale_paid C;
    TL.tlg_future_paid := cng_future_paid C;
    TL.tlg_residual_paid := cng_residual_paid C;

    TL.tlg_action_nonnegative := cng_action_nonnegative C;
    TL.tlg_next_owned := cng_next_owned C;
    TL.tlg_parent_paid := cng_parent_paid C;
    TL.tlg_legal_cost_split := cng_legal_cost_split C;

    TL.tlg_scale_gk := cng_scale_gk C;
    TL.tlg_future_gk := cng_future_gk C;
    TL.tlg_residual_gk := cng_residual_gk C
  |}.

Theorem CSER40_NORM_GK_BUILDS_THREE_LEG_GK :
  forall C : ComplexNormGKSequenceCertificate,
    exists G : TL.ThreeLegGKSequenceCertificate,
      forall n : nat,
        TL.tlg_action G n = cng_action C n.
Proof.
  intro C.
  exists (build_three_leg_gk_from_norm C).
  intro n.
  reflexivity.
Qed.

Theorem CSER41_COMPLEX_NORM_GK_IMPLIES_DISCRETE_M7 :
  forall C : ComplexNormGKSequenceCertificate,
    MR.ActualDiscreteGPM7 (cng_action C).
Proof.
  intro C.
  exact
    (TL.TL31_THREE_LEG_GK_IMPLIES_DISCRETE_M7
      (build_three_leg_gk_from_norm C)).
Qed.

Theorem CSER42_COMPLEX_NORM_GK_IMPLIES_OLD_FINITE_MEMORY_M7 :
  forall C : ComplexNormGKSequenceCertificate,
    MR.RR.finite_memory_gpm7 (cng_action C).
Proof.
  intro C.
  exact
    (TL.TL32_THREE_LEG_GK_IMPLIES_OLD_FINITE_MEMORY_M7
      (build_three_leg_gk_from_norm C)).
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.

Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.cabs2.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER00_CABS2_NONNEG.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER01_CABS2_CONJ.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER02_CABS2_CMUL.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER03_REAL_PART_SQUARE_LE_CABS2.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER04_POS_SQUARE_LE_SQUARE.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER10_SOURCE1_RAW_SQUARE_BOUND.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER11_SOURCE2_RAW_SQUARE_BOUND.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER12_SOURCE3_RAW_SQUARE_BOUND.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER20_SOURCE1_ENVELOPE.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER21_SOURCE2_ENVELOPE.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER22_SOURCE3_ENVELOPE.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.ComplexTriadNormCertificate.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.build_complex_physical_from_norm.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER31_NORM_TRIAD_CONSTRUCTS_PARENT_ROUTE.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER32_NORM_TRIAD_ROUTE_REPRODUCTION.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.ComplexNormGKSequenceCertificate.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER41_COMPLEX_NORM_GK_IMPLIES_DISCRETE_M7.
Check NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.CSER42_COMPLEX_NORM_GK_IMPLIES_OLD_FINITE_MEMORY_M7.
