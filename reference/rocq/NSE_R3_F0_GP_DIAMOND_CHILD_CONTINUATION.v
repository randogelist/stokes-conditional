From Stdlib Require Import Reals Lra Psatz Lists.List String.
Require Import NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.
Require Import awpi_nse_gp_source_class_ownership_v0_25_4.
Require Import awpi_nse_gp_parent_degree_reproduction_v0_26_0.
Require Import awpi_nse_gp_three_leg_route_realization_v0_36_4.
Require Import awpi_nse_gp_complex_three_leg_realization_v0_37_4.
Require Import awpi_nse_gp_gk_cohomology_realization_v0_35_3.
Require Import awpi_nse_gp_to_m7_route_v0_28_3.

Open Scope R_scope.

Module NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.

Module CL := NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.NSE_R3_F0_GP_DIAMOND_CANONICAL_LEDGER.
Module GA := NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.NSE_R3_F0_GP_DIAMOND_GENERATION_ASSEMBLY.
Module SO := NSE_GP_SOURCE_CLASS_OWNERSHIP.
Module PR := NSE_GP_PARENT_DEGREE_REPRODUCTION.
Module TL := NSE_GP_THREE_LEG_ROUTE_REALIZATION.
Module CTL := NSE_GP_COMPLEX_THREE_LEG_REALIZATION.
Module GK := NSE_GP_GK_COHOMOLOGY_REALIZATION.
Module MR := NSE_GP_TO_M7_ROUTE.

(* ====================================================================== *)
(* 1. Source-class action ledger before child classes are forgotten.       *)
(* ====================================================================== *)

Fixpoint source_class_action
  (Ps : list SO.PhysicalSourceClass) : R :=
  match Ps with
  | nil => 0
  | P :: tl => TL.canonical_parent_action P + source_class_action tl
  end.

Theorem CC00_SOURCE_CLASS_ACTION_NONNEG :
  forall Ps : list SO.PhysicalSourceClass,
    0 <= source_class_action Ps.
Proof.
  intro Ps.
  induction Ps as [|P tl IH].
  - simpl. lra.
  - simpl.
    pose proof (TL.TL01_CANONICAL_PARENT_ACTION_NONNEG P) as HP.
    lra.
Qed.

Theorem CC01_SOURCE_CLASS_ACTION_APPEND :
  forall A B : list SO.PhysicalSourceClass,
    source_class_action (A ++ B)
    = source_class_action A + source_class_action B.
Proof.
  intros A B.
  induction A as [|P tl IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Fixpoint generation_parent_sources
  (Ts : list CTL.ComplexThreeLegPhysicalCertificate)
  : list SO.PhysicalSourceClass :=
  match Ts with
  | nil => nil
  | T :: tl => CTL.ctl_parent_class T :: generation_parent_sources tl
  end.

Fixpoint generation_child_sources
  (Ts : list CTL.ComplexThreeLegPhysicalCertificate)
  : list SO.PhysicalSourceClass :=
  match Ts with
  | nil => nil
  | T :: tl =>
      CTL.ctl_class_k T ::
      CTL.ctl_class_p T ::
      CTL.ctl_class_q T ::
      generation_child_sources tl
  end.

Definition routes_of_complex_generation
  (Ts : list CTL.ComplexThreeLegPhysicalCertificate)
  : list TL.ThreeLegPhysicalRoute :=
  CTL.build_complex_three_leg_routes Ts.

Definition routes_of_complex_sequence
  (triads : nat -> list CTL.ComplexThreeLegPhysicalCertificate)
  (n : nat) : list TL.ThreeLegPhysicalRoute :=
  routes_of_complex_generation (triads n).

(* ====================================================================== *)
(* 2. Exact identification of the forest scalar actions with source-class  *)
(*    actions.  Thus the scalar child ledger is a readout of the richer    *)
(*    physical child-source list.                                          *)
(* ====================================================================== *)

Theorem CC10_SINGLE_COMPLEX_PARENT_ACTION_EXACT :
  forall T : CTL.ComplexThreeLegPhysicalCertificate,
    PR.pr_parent_action 3
      (TL.build_three_leg_parent_route
        (CTL.build_complex_three_leg_physical_route T))
    =
    TL.canonical_parent_action (CTL.ctl_parent_class T).
Proof.
  intro T.
  reflexivity.
Qed.

Theorem CC11_SINGLE_COMPLEX_CHILD_ACTION_EXACT :
  forall T : CTL.ComplexThreeLegPhysicalCertificate,
    PR.route_child_action
      (TL.build_three_leg_parent_route
        (CTL.build_complex_three_leg_physical_route T))
    =
      TL.canonical_parent_action (CTL.ctl_class_k T)
      + TL.canonical_parent_action (CTL.ctl_class_p T)
      + TL.canonical_parent_action (CTL.ctl_class_q T).
Proof.
  intro T.
  change
    (CTL.ctl_child_k_action T
      + (CTL.ctl_child_p_action T
        + (CTL.ctl_child_q_action T + 0))
     =
      TL.canonical_parent_action (CTL.ctl_class_k T)
      + TL.canonical_parent_action (CTL.ctl_class_p T)
      + TL.canonical_parent_action (CTL.ctl_class_q T)).
  unfold CTL.ctl_child_k_action, CTL.ctl_child_p_action, CTL.ctl_child_q_action.
  ring.
Qed.

Theorem CC12_COMPLEX_FOREST_PARENT_ACTION_EXACT :
  forall Ts : list CTL.ComplexThreeLegPhysicalCertificate,
    PR.forest_parent_action
      (GA.assembled_parent_forest (routes_of_complex_generation Ts))
    =
    source_class_action (generation_parent_sources Ts).
Proof.
  intro Ts.
  induction Ts as [|T tl IH].
  - reflexivity.
  - change
      (PR.pr_parent_action 3
         (TL.build_three_leg_parent_route
           (CTL.build_complex_three_leg_physical_route T))
       + PR.forest_parent_action
           (GA.assembled_parent_forest (routes_of_complex_generation tl))
       =
       TL.canonical_parent_action (CTL.ctl_parent_class T)
       + source_class_action (generation_parent_sources tl)).
    rewrite CC10_SINGLE_COMPLEX_PARENT_ACTION_EXACT.
    exact (f_equal
      (fun x : R => TL.canonical_parent_action (CTL.ctl_parent_class T) + x)
      IH).
Qed.

Theorem CC13_COMPLEX_FOREST_CHILD_ACTION_EXACT :
  forall Ts : list CTL.ComplexThreeLegPhysicalCertificate,
    PR.forest_child_action
      (GA.assembled_parent_forest (routes_of_complex_generation Ts))
    =
    source_class_action (generation_child_sources Ts).
Proof.
  intro Ts.
  induction Ts as [|T tl IH].
  - reflexivity.
  - change
      (PR.route_child_action
         (TL.build_three_leg_parent_route
           (CTL.build_complex_three_leg_physical_route T))
       + PR.forest_child_action
           (GA.assembled_parent_forest (routes_of_complex_generation tl))
       =
       TL.canonical_parent_action (CTL.ctl_class_k T)
       + (TL.canonical_parent_action (CTL.ctl_class_p T)
          + (TL.canonical_parent_action (CTL.ctl_class_q T)
             + source_class_action (generation_child_sources tl)))).
    rewrite CC11_SINGLE_COMPLEX_CHILD_ACTION_EXACT.
    rewrite IH.
    ring.
Qed.

(* ====================================================================== *)
(* 3. Physical continuation statement.                                     *)
(*                                                                         *)
(* At each generation the emitted child source classes split canonically   *)
(* into the parent source classes which continue at the next generation    *)
(* and a terminal/safely-discarded remainder.  This is strictly richer     *)
(* than the old scalar next-action inequality.                              *)
(* ====================================================================== *)

Record CanonicalChildSourceContinuation
  (triads : nat -> list CTL.ComplexThreeLegPhysicalCertificate) : Type := {
  csc_terminal_sources : nat -> list SO.PhysicalSourceClass;

  csc_child_split :
    forall n : nat,
      generation_child_sources (triads n)
      =
      generation_parent_sources (triads (S n))
      ++ csc_terminal_sources n
}.

Theorem CC20_CHILD_SOURCE_CONTINUATION_GIVES_ACTION_OWNERSHIP :
  forall triads : nat -> list CTL.ComplexThreeLegPhysicalCertificate,
  forall H : CanonicalChildSourceContinuation triads,
  forall n : nat,
    source_class_action (generation_parent_sources (triads (S n)))
    <=
    source_class_action (generation_child_sources (triads n)).
Proof.
  intros triads H n.
  rewrite (csc_child_split triads H n).
  rewrite CC01_SOURCE_CLASS_ACTION_APPEND.
  pose proof
    (CC00_SOURCE_CLASS_ACTION_NONNEG (csc_terminal_sources triads H n))
    as Hterm.
  lra.
Qed.

Theorem CC21_CHILD_SOURCE_CONTINUATION_GIVES_CANONICAL_NEXT_OWNERSHIP :
  forall triads : nat -> list CTL.ComplexThreeLegPhysicalCertificate,
    CanonicalChildSourceContinuation triads ->
    CL.CanonicalNextGenerationOwnership
      (routes_of_complex_sequence triads).
Proof.
  intros triads H n.
  unfold routes_of_complex_sequence.
  rewrite (CC12_COMPLEX_FOREST_PARENT_ACTION_EXACT (triads (S n))).
  rewrite (CC13_COMPLEX_FOREST_CHILD_ACTION_EXACT (triads n)).
  exact (CC20_CHILD_SOURCE_CONTINUATION_GIVES_ACTION_OWNERSHIP triads H n).
Qed.

Definition NoTerminalChildSources
  {triads : nat -> list CTL.ComplexThreeLegPhysicalCertificate}
  (H : CanonicalChildSourceContinuation triads) : Prop :=
  forall n : nat, csc_terminal_sources triads H n = nil.

Theorem CC22_NO_TERMINAL_CHILDREN_GIVES_EXACT_ACTION_CONTINUATION :
  forall triads : nat -> list CTL.ComplexThreeLegPhysicalCertificate,
  forall H : CanonicalChildSourceContinuation triads,
    NoTerminalChildSources H ->
    forall n : nat,
      source_class_action (generation_parent_sources (triads (S n)))
      =
      source_class_action (generation_child_sources (triads n)).
Proof.
  intros triads H Hnone n.
  rewrite (csc_child_split triads H n).
  rewrite (Hnone n).
  rewrite CC01_SOURCE_CLASS_ACTION_APPEND.
  simpl.
  lra.
Qed.

(* ====================================================================== *)
(* 4. Source continuation + the one remaining legal-cost GK channel        *)
(*    reaches the already checked M7 theorem.                               *)
(* ====================================================================== *)

Theorem CC30_CHILD_SOURCE_CONTINUATION_PLUS_LEGAL_GK_GIVES_M7 :
  forall triads : nat -> list CTL.ComplexThreeLegPhysicalCertificate,
    CanonicalChildSourceContinuation triads ->
    GK.GKChannelCertificate
      (CL.canonical_legal_cost (routes_of_complex_sequence triads)) ->
    MR.ActualDiscreteGPM7
      (CL.canonical_generation_action (routes_of_complex_sequence triads)).
Proof.
  intros triads Hcont Hlegal.
  apply CL.CL22_NEXT_OWNERSHIP_PLUS_ONE_LEGAL_GK_CHANNEL_GIVES_M7.
  - exact (CC21_CHILD_SOURCE_CONTINUATION_GIVES_CANONICAL_NEXT_OWNERSHIP triads Hcont).
  - exact Hlegal.
Qed.

(* ====================================================================== *)
(* Claim boundary after child-source contraction.                           *)
(* ====================================================================== *)

Definition LH_COMPLEX_GENERATION_PACKAGING_FRONTIER : Prop := True.
Definition CANONICAL_CHILD_SOURCE_CONTINUATION_FRONTIER : Prop := True.
Definition CANONICAL_LEGAL_COST_GK_FRONTIER : Prop := True.
Definition CRITICAL_TIME_ROUTE_DEPTH_FRONTIER : Prop := True.

Definition STATUS : string :=
  "NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION_V0_8_2"%string.

End NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.

Check NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.source_class_action.
Check NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.CanonicalChildSourceContinuation.
Check NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.CC13_COMPLEX_FOREST_CHILD_ACTION_EXACT.
Check NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.CC21_CHILD_SOURCE_CONTINUATION_GIVES_CANONICAL_NEXT_OWNERSHIP.
Check NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.CC22_NO_TERMINAL_CHILDREN_GIVES_EXACT_ACTION_CONTINUATION.
Check NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.CC30_CHILD_SOURCE_CONTINUATION_PLUS_LEGAL_GK_GIVES_M7.

Print Assumptions NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.CC21_CHILD_SOURCE_CONTINUATION_GIVES_CANONICAL_NEXT_OWNERSHIP.
Print Assumptions NSE_R3_F0_GP_DIAMOND_CHILD_CONTINUATION.CC30_CHILD_SOURCE_CONTINUATION_PLUS_LEGAL_GK_GIVES_M7.
