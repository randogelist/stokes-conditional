From Stdlib Require Import Reals Lra Psatz Lists.List String.
Require Import NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.
Require Import awpi_nse_gp_parent_degree_reproduction_v0_26_0.
Require Import awpi_nse_gp_three_leg_route_realization_v0_36_4.
Require Import awpi_nse_gp_gk_cohomology_realization_v0_35_3.
Require Import awpi_nse_gp_renewal_reduction_v0_3_1.
Require Import awpi_nse_gp_to_m7_route_v0_28_3.

Open Scope R_scope.

Module NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.

Module GA := NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.
Module PR := NSE_GP_PARENT_DEGREE_REPRODUCTION.
Module TL := NSE_GP_THREE_LEG_ROUTE_REALIZATION.
Module GK := NSE_GP_GK_COHOMOLOGY_REALIZATION.
Module RR := NSE_GP_RENEWAL_REDUCTION.
Module MR := NSE_GP_TO_M7_ROUTE.

(* ====================================================================== *)
(* 1. Canonical generation action.                                        *)
(*                                                                        *)
(* The M7 action at generation n is chosen to be exactly the parent-forest*)
(* action of the selected physical routes at generation n.  Consequently  *)
(* current-parent coverage is no longer an independent hypothesis.        *)
(* ====================================================================== *)

Definition canonical_generation_action
  (routes : nat -> list TL.ThreeLegPhysicalRoute)
  (n : nat) : R :=
  PR.forest_parent_action
    (GA.assembled_parent_forest (routes n)).

Theorem CL00_FOREST_PARENT_ACTION_NONNEG :
  forall Ps : list (PR.ParentRoute 3),
    0 <= PR.forest_parent_action Ps.
Proof.
  intro Ps.
  induction Ps as [|P tl IH].
  - simpl. lra.
  - simpl.
    pose proof (PR.pr_parent_action_nonnegative 3 P) as HP.
    lra.
Qed.

Theorem CL01_CANONICAL_GENERATION_ACTION_NONNEG :
  forall routes : nat -> list TL.ThreeLegPhysicalRoute,
  forall n : nat,
    0 <= canonical_generation_action routes n.
Proof.
  intros routes n.
  unfold canonical_generation_action.
  apply CL00_FOREST_PARENT_ACTION_NONNEG.
Qed.

Theorem CL02_CURRENT_PARENT_COVERAGE_IS_EQUALITY :
  forall routes : nat -> list TL.ThreeLegPhysicalRoute,
  forall n : nat,
    PR.forest_parent_action
      (GA.assembled_parent_forest (routes n))
    = canonical_generation_action routes n.
Proof.
  reflexivity.
Qed.

(* ====================================================================== *)
(* 2. Canonical legal-cost channel.                                       *)
(*                                                                        *)
(* The whole legal cost is assigned to one residual GK channel.  Scale and*)
(* future payment channels are identically zero and carry canonical GK     *)
(* certificates.  Thus the previous three-channel realization interface   *)
(* contracts to one GK certificate for the actual forest legal cost.       *)
(* ====================================================================== *)

Definition canonical_legal_cost
  (routes : nat -> list TL.ThreeLegPhysicalRoute)
  (n : nat) : R :=
  PR.forest_legal_cost
    (GA.assembled_parent_forest (routes n)).

Theorem CL10_FOREST_LEGAL_COST_NONNEG :
  forall Ps : list (PR.ParentRoute 3),
    0 <= PR.forest_legal_cost Ps.
Proof.
  intro Ps.
  induction Ps as [|P tl IH].
  - simpl. lra.
  - simpl.
    pose proof (PR.pr_legal_cost_nonnegative 3 P) as HP.
    lra.
Qed.

Theorem CL11_CANONICAL_LEGAL_COST_NONNEG :
  forall routes : nat -> list TL.ThreeLegPhysicalRoute,
  forall n : nat,
    0 <= canonical_legal_cost routes n.
Proof.
  intros routes n.
  unfold canonical_legal_cost.
  apply CL10_FOREST_LEGAL_COST_NONNEG.
Qed.

Definition zero_paid (_ : nat) : R := 0.

Theorem CL12_ZERO_PREFIX_SUM :
  forall N : nat,
    RR.prefix_sum zero_paid N = 0.
Proof.
  intro N.
  induction N as [|N IH].
  - reflexivity.
  - simpl. rewrite IH. unfold zero_paid. lra.
Qed.

Definition zero_gk_channel : GK.GKChannelCertificate zero_paid.
Proof.
  refine
    {| GK.gkc_cost := zero_paid;
       GK.gkc_potential := zero_paid;
       GK.gkc_alpha := 0;
       GK.gkc_lower := 0 |}.
  - intro n. unfold zero_paid. lra.
  - intro n. unfold zero_paid. lra.
  - lra.
  - intro n. unfold zero_paid. lra.
  - intro n. unfold zero_paid, GK.delta. lra.
  - exists 0.
    split.
    + lra.
    + intro N.
      rewrite CL12_ZERO_PREFIX_SUM.
      lra.
Defined.

Theorem CL13_ZERO_GK_CHANNEL_HAS_ZERO_PAID_BUDGET :
  RR.uniform_prefix_budget zero_paid.
Proof.
  exact (GK.GKGK10_CHANNEL_GIVES_UNIFORM_PAID_BUDGET zero_paid zero_gk_channel).
Qed.

(* ====================================================================== *)
(* 3. Canonical inter-generation compatibility.                           *)
(*                                                                        *)
(* Only two substantive pieces remain here:                               *)
(*   (i) next generation parent action is owned by current children;       *)
(*  (ii) the actual legal-cost sequence admits one GK channel certificate.*)
(* Current parent coverage and two of the three payment channels disappear*)
(* by canonical definitions.                                               *)
(* ====================================================================== *)

Record CanonicalIntergenerationCompatibility
  (routes : nat -> list TL.ThreeLegPhysicalRoute) : Type := {
  cic_next_owned :
    forall n : nat,
      canonical_generation_action routes (S n)
      <=
      PR.forest_child_action
        (GA.assembled_parent_forest (routes n));

  cic_legal_cost_gk :
    GK.GKChannelCertificate (canonical_legal_cost routes)
}.

Definition build_intergeneration_from_canonical
  (routes : nat -> list TL.ThreeLegPhysicalRoute)
  (H : CanonicalIntergenerationCompatibility routes)
  : GA.IntergenerationPaymentCompatibility
      (canonical_generation_action routes)
      routes
      zero_paid
      zero_paid
      (canonical_legal_cost routes).
Proof.
  refine
    {| GA.ipc_action_nonnegative := CL01_CANONICAL_GENERATION_ACTION_NONNEG routes;
       GA.ipc_next_generation_owned := cic_next_owned routes H;
       GA.ipc_current_parent_covered := _;
       GA.ipc_legal_cost_split := _;
       GA.ipc_scale_gk := zero_gk_channel;
       GA.ipc_future_gk := zero_gk_channel;
       GA.ipc_residual_gk := cic_legal_cost_gk routes H |}.
  - intro n.
    rewrite (CL02_CURRENT_PARENT_COVERAGE_IS_EQUALITY routes n).
    lra.
  - intro n.
    unfold canonical_legal_cost, zero_paid.
    lra.
Defined.

Theorem CL20_CANONICAL_LEDGER_GIVES_DISCRETE_M7 :
  forall routes : nat -> list TL.ThreeLegPhysicalRoute,
    CanonicalIntergenerationCompatibility routes ->
    MR.ActualDiscreteGPM7 (canonical_generation_action routes).
Proof.
  intros routes H.
  exact
    (GA.GA20_SELECTED_FORESTS_PLUS_INTERGENERATION_COMPATIBILITY_GIVE_M7
      (canonical_generation_action routes)
      routes
      zero_paid zero_paid (canonical_legal_cost routes)
      (build_intergeneration_from_canonical routes H)).
Qed.

(* A more explicit formulation of the remaining inter-generation action law. *)
Definition CanonicalNextGenerationOwnership
  (routes : nat -> list TL.ThreeLegPhysicalRoute) : Prop :=
  forall n : nat,
    PR.forest_parent_action
      (GA.assembled_parent_forest (routes (S n)))
    <=
    PR.forest_child_action
      (GA.assembled_parent_forest (routes n)).

Theorem CL21_CANONICAL_NEXT_OWNERSHIP_IS_EXACTLY_CIC_NEXT_OWNED :
  forall routes : nat -> list TL.ThreeLegPhysicalRoute,
    CanonicalNextGenerationOwnership routes ->
    forall n : nat,
      canonical_generation_action routes (S n)
      <=
      PR.forest_child_action
        (GA.assembled_parent_forest (routes n)).
Proof.
  intros routes H n.
  unfold CanonicalNextGenerationOwnership in H.
  unfold canonical_generation_action.
  exact (H n).
Qed.

Theorem CL22_NEXT_OWNERSHIP_PLUS_ONE_LEGAL_GK_CHANNEL_GIVES_M7 :
  forall routes : nat -> list TL.ThreeLegPhysicalRoute,
    CanonicalNextGenerationOwnership routes ->
    GK.GKChannelCertificate (canonical_legal_cost routes) ->
    MR.ActualDiscreteGPM7 (canonical_generation_action routes).
Proof.
  intros routes Hnext Hlegal.
  apply CL20_CANONICAL_LEDGER_GIVES_DISCRETE_M7.
  refine {| cic_next_owned := _; cic_legal_cost_gk := Hlegal |}.
  exact (CL21_CANONICAL_NEXT_OWNERSHIP_IS_EXACTLY_CIC_NEXT_OWNED routes Hnext).
Qed.

(* ====================================================================== *)
(* Claim boundary after canonical-ledger contraction.                      *)
(* ====================================================================== *)

Definition LH_FINITE_GENERATION_SLOT_PACKAGING_FRONTIER : Prop := True.
Definition CANONICAL_NEXT_GENERATION_OWNERSHIP_FRONTIER : Prop := True.
Definition CANONICAL_LEGAL_COST_GK_FRONTIER : Prop := True.
Definition CRITICAL_TIME_ROUTE_DEPTH_FRONTIER : Prop := True.

Definition STATUS : string :=
  "NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER_V0_7_1"%string.

End NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.

Check NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.canonical_generation_action.
Check NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.CL02_CURRENT_PARENT_COVERAGE_IS_EQUALITY.
Check NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.zero_gk_channel.
Check NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.CanonicalIntergenerationCompatibility.
Check NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.CL20_CANONICAL_LEDGER_GIVES_DISCRETE_M7.
Check NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.CL22_NEXT_OWNERSHIP_PLUS_ONE_LEGAL_GK_CHANNEL_GIVES_M7.

Print Assumptions NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.CL20_CANONICAL_LEDGER_GIVES_DISCRETE_M7.
Print Assumptions NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.CL22_NEXT_OWNERSHIP_PLUS_ONE_LEGAL_GK_CHANNEL_GIVES_M7.
