From Stdlib Require Import Reals Lists.List String.
Require Import NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.
Require Import awpi_nse_gp_ae_modal_semantics_v0_23_1.
Require Import awpi_nse_gp_three_leg_route_realization_v0_36_4.
Require Import awpi_nse_gp_to_m7_route_v0_28_3.
Require Import awpi_nse_gp_parent_degree_reproduction_v0_26_0.
Require Import awpi_nse_gp_gk_cohomology_realization_v0_35_3.

Open Scope R_scope.
Import ListNotations.

Module NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.

Module AE := NSE_GP_AE_MODAL_SEMANTICS.
Module TL := NSE_GP_THREE_LEG_ROUTE_REALIZATION.
Module MR := NSE_GP_TO_M7_ROUTE.
Module PR := NSE_GP_PARENT_DEGREE_REPRODUCTION.
Module GK := NSE_GP_GK_COHOMOLOGY_REALIZATION.

(* ====================================================================== *)
(* 1. Standard co-null nonemptiness.                                      *)
(*                                                                         *)
(* Concrete Lebesgue co-null sets on R have this property.  Keeping it     *)
(* separate makes clear that no new NSE/M7 input is hidden here.           *)
(* ====================================================================== *)

Record CoNullNonempty
  (CoNull : (R -> Prop) -> Prop) : Prop := {
  cne_nonempty :
    forall P : R -> Prop,
      CoNull P -> exists t : R, P t
}.

(* ====================================================================== *)
(* 2. One local route slot.                                                *)
(*                                                                         *)
(* A slot packages exactly the output already supplied by v0.5.3 for a    *)
(* fixed physical triad: almost every time realizes an actual three-leg    *)
(* route.                                                                  *)
(* ====================================================================== *)

Record LocalRouteSlot
  (CoNull : (R -> Prop) -> Prop) : Type := {
  lrs_realized : R -> TL.ThreeLegPhysicalRoute -> Prop;
  lrs_conull :
    CoNull
      (fun t : R =>
        exists rte : TL.ThreeLegPhysicalRoute,
          lrs_realized t rte)
}.

Inductive SlotsRealizedAt
  {CoNull : (R -> Prop) -> Prop}
  : list (LocalRouteSlot CoNull) ->
    R -> list TL.ThreeLegPhysicalRoute -> Prop :=
| SRA_nil :
    forall t : R,
      SlotsRealizedAt [] t []
| SRA_cons :
    forall (slot : LocalRouteSlot CoNull)
           (slots : list (LocalRouteSlot CoNull))
           (t : R)
           (rte : TL.ThreeLegPhysicalRoute)
           (rtes : list TL.ThreeLegPhysicalRoute),
      lrs_realized CoNull slot t rte ->
      SlotsRealizedAt slots t rtes ->
      SlotsRealizedAt (slot :: slots) t (rte :: rtes).

(* Finite intersection of co-null local route realizations is again co-null. *)
Theorem GA00_FINITE_LOCAL_ROUTE_SLOTS_ASSEMBLE_CONULL :
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall slots : list (LocalRouteSlot CoNull),
    CoNull
      (fun t : R =>
        exists rtes : list TL.ThreeLegPhysicalRoute,
          SlotsRealizedAt slots t rtes).
Proof.
  intros CoNull HC slots.
  induction slots as [|slot slots IH].
  - eapply (AE.cn_mono CoNull HC
      (fun _ : R => True)
      (fun t : R =>
        exists rtes : list TL.ThreeLegPhysicalRoute,
          SlotsRealizedAt [] t rtes)).
    + exact (AE.cn_all CoNull HC).
    + intros t _.
      exists [].
      constructor.
  - pose proof (lrs_conull CoNull slot) as Hslot.
    pose proof
      (AE.cn_inter CoNull HC
        (fun t : R =>
          exists rte : TL.ThreeLegPhysicalRoute,
            lrs_realized CoNull slot t rte)
        (fun t : R =>
          exists rtes : list TL.ThreeLegPhysicalRoute,
            SlotsRealizedAt slots t rtes)
        Hslot IH) as Hboth.
    eapply (AE.cn_mono CoNull HC
      (fun t : R =>
        (exists rte : TL.ThreeLegPhysicalRoute,
          lrs_realized CoNull slot t rte) /\
        (exists rtes : list TL.ThreeLegPhysicalRoute,
          SlotsRealizedAt slots t rtes))
      (fun t : R =>
        exists rtes : list TL.ThreeLegPhysicalRoute,
          SlotsRealizedAt (slot :: slots) t rtes)).
    + exact Hboth.
    + intros t [Hrte Hrtes].
      destruct Hrte as [rte Hrte].
      destruct Hrtes as [rtes Hrtes].
      exists (rte :: rtes).
      constructor; assumption.
Qed.

Theorem GA01_REALIZED_ROUTE_COUNT_MATCHES_SLOT_COUNT :
  forall CoNull : (R -> Prop) -> Prop,
  forall slots : list (LocalRouteSlot CoNull),
  forall t : R,
  forall rtes : list TL.ThreeLegPhysicalRoute,
    SlotsRealizedAt slots t rtes ->
    List.length rtes = List.length slots.
Proof.
  intros CoNull slots t rtes H.
  induction H.
  - reflexivity.
  - simpl.
    f_equal.
    exact IHSlotsRealizedAt.
Qed.

(* ====================================================================== *)
(* 3. Every selected finite forest automatically has the checked local     *)
(*    reproduction inequality.  There is no extra forest-reproduction      *)
(*    hypothesis left to prove.                                            *)
(* ====================================================================== *)

Definition assembled_parent_forest
  (rtes : list TL.ThreeLegPhysicalRoute)
  : list (PR.ParentRoute 3) :=
  TL.build_three_leg_forest rtes.

Theorem GA10_ASSEMBLED_FOREST_REPRODUCTION :
  forall rtes : list TL.ThreeLegPhysicalRoute,
    4 * PR.forest_child_action (assembled_parent_forest rtes)
    <=
    PR.forest_parent_action (assembled_parent_forest rtes)
    + PR.forest_legal_cost (assembled_parent_forest rtes).
Proof.
  intro rtes.
  unfold assembled_parent_forest.
  exact
    (PR.GPPR32_FOREST_REPRODUCTION
      3 (TL.build_three_leg_forest rtes)).
Qed.

(* Co-null nonemptiness now gives an actual finite route forest for one     *)
(* generation.                                                             *)
Theorem GA11_FINITE_GENERATION_HAS_ACTUAL_ROUTE_FOREST :
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall HNE : CoNullNonempty CoNull,
  forall slots : list (LocalRouteSlot CoNull),
    exists t : R,
    exists rtes : list TL.ThreeLegPhysicalRoute,
      SlotsRealizedAt slots t rtes /\
      4 * PR.forest_child_action (assembled_parent_forest rtes)
      <=
      PR.forest_parent_action (assembled_parent_forest rtes)
      + PR.forest_legal_cost (assembled_parent_forest rtes).
Proof.
  intros CoNull HC HNE slots.
  pose proof
    (GA00_FINITE_LOCAL_ROUTE_SLOTS_ASSEMBLE_CONULL
      CoNull HC slots) as Hconull.
  destruct
    (cne_nonempty CoNull HNE
      (fun t : R =>
        exists rtes : list TL.ThreeLegPhysicalRoute,
          SlotsRealizedAt slots t rtes)
      Hconull)
    as [t Ht].
  destruct Ht as [rtes Hrtes].
  exists t, rtes.
  split.
  - exact Hrtes.
  - exact (GA10_ASSEMBLED_FOREST_REPRODUCTION rtes).
Qed.

Definition GenerationSlots
  (CoNull : (R -> Prop) -> Prop) : Type :=
  nat -> list (LocalRouteSlot CoNull).

Theorem GA12_EVERY_FINITE_GENERATION_HAS_ROUTE_FOREST :
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall HNE : CoNullNonempty CoNull,
  forall G : GenerationSlots CoNull,
  forall n : nat,
    exists t : R,
    exists rtes : list TL.ThreeLegPhysicalRoute,
      SlotsRealizedAt (G n) t rtes /\
      4 * PR.forest_child_action (assembled_parent_forest rtes)
      <=
      PR.forest_parent_action (assembled_parent_forest rtes)
      + PR.forest_legal_cost (assembled_parent_forest rtes).
Proof.
  intros.
  exact
    (GA11_FINITE_GENERATION_HAS_ACTUAL_ROUTE_FOREST
      CoNull HC HNE (G n)).
Qed.

(* ====================================================================== *)
(* 4. What remains after route selection.                                 *)
(*                                                                         *)
(* Once a route forest has been selected at every generation, the full GK  *)
(* sequence certificate requires only inter-generation ownership/coverage  *)
(* and the three GK payment-channel certificates.                          *)
(* ====================================================================== *)

Record IntergenerationPaymentCompatibility
  (action : nat -> R)
  (routes : nat -> list TL.ThreeLegPhysicalRoute)
  (scale_paid future_paid residual_paid : nat -> R) : Type := {
  ipc_action_nonnegative :
    forall n : nat, 0 <= action n;

  ipc_next_generation_owned :
    forall n : nat,
      action (S n)
      <=
      PR.forest_child_action
        (assembled_parent_forest (routes n));

  ipc_current_parent_covered :
    forall n : nat,
      PR.forest_parent_action
        (assembled_parent_forest (routes n))
      <= action n;

  ipc_legal_cost_split :
    forall n : nat,
      PR.forest_legal_cost
        (assembled_parent_forest (routes n))
      <= scale_paid n + future_paid n + residual_paid n;

  ipc_scale_gk : GK.GKChannelCertificate scale_paid;
  ipc_future_gk : GK.GKChannelCertificate future_paid;
  ipc_residual_gk : GK.GKChannelCertificate residual_paid
}.

Definition build_three_leg_gk_from_selected_forests
  (action : nat -> R)
  (routes : nat -> list TL.ThreeLegPhysicalRoute)
  (scale_paid future_paid residual_paid : nat -> R)
  (H : IntergenerationPaymentCompatibility
        action routes scale_paid future_paid residual_paid)
  : TL.ThreeLegGKSequenceCertificate.
Proof.
  refine
    {| TL.tlg_action := action;
       TL.tlg_physical_routes := routes;
       TL.tlg_scale_paid := scale_paid;
       TL.tlg_future_paid := future_paid;
       TL.tlg_residual_paid := residual_paid;
       TL.tlg_action_nonnegative := ipc_action_nonnegative _ _ _ _ _ H;
       TL.tlg_next_owned := ipc_next_generation_owned _ _ _ _ _ H;
       TL.tlg_parent_paid := ipc_current_parent_covered _ _ _ _ _ H;
       TL.tlg_legal_cost_split := ipc_legal_cost_split _ _ _ _ _ H;
       TL.tlg_scale_gk := ipc_scale_gk _ _ _ _ _ H;
       TL.tlg_future_gk := ipc_future_gk _ _ _ _ _ H;
       TL.tlg_residual_gk := ipc_residual_gk _ _ _ _ _ H |}.
Defined.

Theorem GA20_SELECTED_FORESTS_PLUS_INTERGENERATION_COMPATIBILITY_GIVE_M7 :
  forall action : nat -> R,
  forall routes : nat -> list TL.ThreeLegPhysicalRoute,
  forall scale_paid future_paid residual_paid : nat -> R,
    IntergenerationPaymentCompatibility
      action routes scale_paid future_paid residual_paid ->
    MR.ActualDiscreteGPM7 action.
Proof.
  intros action routes scale_paid future_paid residual_paid H.
  exact
    (TL.TL31_THREE_LEG_GK_IMPLIES_DISCRETE_M7
      (build_three_leg_gk_from_selected_forests
        action routes scale_paid future_paid residual_paid H)).
Qed.

(* ====================================================================== *)
(* Claim boundary after generation assembly contraction.                  *)
(* ====================================================================== *)

Definition CONULL_NONEMPTY_FRONTIER : Prop := True.
Definition LH_FINITE_GENERATION_SLOT_PACKAGING_FRONTIER : Prop := True.
Definition NEXT_GENERATION_OWNERSHIP_FRONTIER : Prop := True.
Definition CURRENT_PARENT_COVERAGE_FRONTIER : Prop := True.
Definition GK_LEGAL_COST_CHANNEL_REALIZATION_FRONTIER : Prop := True.
Definition CRITICAL_TIME_ROUTE_DEPTH_FRONTIER : Prop := True.

Definition STATUS : string :=
  "NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY_V0_6_2"%string.

End NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.

Check NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.LocalRouteSlot.
Check NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.SlotsRealizedAt.
Check NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.GA00_FINITE_LOCAL_ROUTE_SLOTS_ASSEMBLE_CONULL.
Check NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.GA10_ASSEMBLED_FOREST_REPRODUCTION.
Check NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.GA11_FINITE_GENERATION_HAS_ACTUAL_ROUTE_FOREST.
Check NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.GA12_EVERY_FINITE_GENERATION_HAS_ROUTE_FOREST.
Check NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.IntergenerationPaymentCompatibility.
Check NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.GA20_SELECTED_FORESTS_PLUS_INTERGENERATION_COMPATIBILITY_GIVE_M7.

Print Assumptions NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.GA00_FINITE_LOCAL_ROUTE_SLOTS_ASSEMBLE_CONULL.
Print Assumptions NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.GA11_FINITE_GENERATION_HAS_ACTUAL_ROUTE_FOREST.
Print Assumptions NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.GA20_SELECTED_FORESTS_PLUS_INTERGENERATION_COMPATIBILITY_GIVE_M7.
