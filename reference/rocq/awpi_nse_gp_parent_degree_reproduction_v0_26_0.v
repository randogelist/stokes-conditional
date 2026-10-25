
From Stdlib Require Import Reals Lra Psatz Lists.List Arith.Arith.
Require Import awpi_nse_gp_perspective_action_v0_11_2.
Require Import awpi_nse_gp_closed_action_envelope_v0_19_2.
Require Import awpi_nse_gp_finite_cutoff_envelope_v0_20_0.
Require Import awpi_nse_gp_leray_modal_triad_adapter_v0_13_3.
Require Import awpi_nse_gp_source_class_ownership_v0_25_4.
Import ListNotations.
Open Scope R_scope.

Module NSE_GP_PARENT_DEGREE_REPRODUCTION.

Module PA := NSE_GP_PERSPECTIVE_ACTION.
Module SO := NSE_GP_SOURCE_CLASS_OWNERSHIP.

(* A small internal nat->R embedding, used only for finite parent degree.
   Keeping it recursive avoids dependence on library theorem names for INR. *)
Fixpoint natR (n : nat) : R :=
  match n with
  | O => 0
  | S k => 1 + natR k
  end.

Theorem GPPR00_NATR_NONNEG :
  forall n : nat, 0 <= natR n.
Proof.
  intro n.
  induction n as [|n IH].
  - simpl. lra.
  - simpl. lra.
Qed.

Theorem GPPR01_NATR_MONOTONE :
  forall n m : nat,
    (n <= m)%nat ->
    natR n <= natR m.
Proof.
  intros n m H.
  induction H.
  - lra.
  - simpl.
    lra.
Qed.

Fixpoint AllNonnegative (xs : list R) : Prop :=
  match xs with
  | [] => True
  | x :: tl => 0 <= x /\ AllNonnegative tl
  end.

Fixpoint AllLe (B : R) (xs : list R) : Prop :=
  match xs with
  | [] => True
  | x :: tl => x <= B /\ AllLe B tl
  end.

Theorem GPPR10_SUM_NONNEG :
  forall xs : list R,
    AllNonnegative xs ->
    0 <= SO.sumR xs.
Proof.
  intros xs H.
  induction xs as [|x tl IH].
  - simpl. lra.
  - simpl in H.
    destruct H as [Hx Htl].
    simpl.
    specialize (IH Htl).
    lra.
Qed.

(* Bounded degree + each child action <= outgoing parent capacity
   gives the combinatorial action bound sum(children) <= degree*capacity. *)
Theorem GPPR11_SUM_LE_LENGTH_TIMES_BOUND :
  forall B : R,
  forall xs : list R,
    0 <= B ->
    AllLe B xs ->
    SO.sumR xs <= natR (length xs) * B.
Proof.
  intros B xs HB Hle.
  induction xs as [|x tl IH].
  - simpl. nra.
  - simpl in Hle.
    destruct Hle as [Hx Htl].
    simpl.
    specialize (IH Htl).
    nra.
Qed.

Theorem GPPR12_BOUNDED_DEGREE_CHILD_ACTION :
  forall dstar : nat,
  forall B : R,
  forall xs : list R,
    0 <= B ->
    AllLe B xs ->
    (length xs <= dstar)%nat ->
    SO.sumR xs <= natR dstar * B.
Proof.
  intros dstar B xs HB Hle Hdeg.
  pose proof (GPPR11_SUM_LE_LENGTH_TIMES_BOUND B xs HB Hle) as Hsum.
  pose proof (GPPR01_NATR_MONOTONE (length xs) dstar Hdeg) as Hnr.
  nra.
Qed.

(* One physically-owned parent route.
   - source_class is already group-first/action-second from v0.25.4;
   - child_actions are actual outgoing child actions;
   - each child action is bounded by the one outgoing parent capacity B;
   - there are at most dstar children;
   - the reproduction inequality is stated in the common action currency. *)
Record ParentRoute (dstar : nat) : Type := {
  pr_source_class : SO.PhysicalSourceClass;

  pr_parent_action : R;
  pr_parent_action_nonnegative : 0 <= pr_parent_action;
  pr_parent_action_rel :
    PA.ActionRel
      (SO.class_positive_work pr_source_class)
      (SO.psc_capacity pr_source_class)
      pr_parent_action;
  pr_parent_action_budget :
    pr_parent_action <= SO.psc_budget pr_source_class;

  pr_outgoing_capacity : R;
  pr_outgoing_capacity_nonnegative : 0 <= pr_outgoing_capacity;

  pr_child_actions : list R;
  pr_child_actions_nonnegative : AllNonnegative pr_child_actions;
  pr_each_child_bounded :
    AllLe pr_outgoing_capacity pr_child_actions;
  pr_degree_bound :
    (length pr_child_actions <= dstar)%nat;

  pr_legal_cost : R;
  pr_legal_cost_nonnegative : 0 <= pr_legal_cost;

  pr_reproduction :
    4 * natR dstar * pr_outgoing_capacity
      <= pr_parent_action + pr_legal_cost
}.

Definition route_child_action
  {dstar : nat} (P : ParentRoute dstar) : R :=
  SO.sumR (pr_child_actions dstar P).

Theorem GPPR20_ROUTE_CHILD_ACTION_NONNEG :
  forall dstar : nat,
  forall P : ParentRoute dstar,
    0 <= route_child_action P.
Proof.
  intros dstar P.
  unfold route_child_action.
  apply GPPR10_SUM_NONNEG.
  exact (pr_child_actions_nonnegative dstar P).
Qed.

Theorem GPPR21_ROUTE_DEGREE_PAYS_CHILD_ACTION :
  forall dstar : nat,
  forall P : ParentRoute dstar,
    route_child_action P
      <= natR dstar * pr_outgoing_capacity dstar P.
Proof.
  intros dstar P.
  unfold route_child_action.
  eapply GPPR12_BOUNDED_DEGREE_CHILD_ACTION.
  - exact (pr_outgoing_capacity_nonnegative dstar P).
  - exact (pr_each_child_bounded dstar P).
  - exact (pr_degree_bound dstar P).
Qed.

(* This is the key local reduction:
      degree bound + reproduction capacity
   removes dstar and yields a direct parent->children action inequality. *)
Theorem GPPR22_ROUTE_REPRODUCTION_PAYS_ALL_CHILDREN :
  forall dstar : nat,
  forall P : ParentRoute dstar,
    4 * route_child_action P
      <= pr_parent_action dstar P + pr_legal_cost dstar P.
Proof.
  intros dstar P.
  pose proof (GPPR21_ROUTE_DEGREE_PAYS_CHILD_ACTION dstar P) as Hchild.
  pose proof (pr_reproduction dstar P) as Hrep.
  nra.
Qed.

Fixpoint forest_child_action
  {dstar : nat} (Ps : list (ParentRoute dstar)) : R :=
  match Ps with
  | [] => 0
  | P :: tl => route_child_action P + forest_child_action tl
  end.

Fixpoint forest_parent_action
  {dstar : nat} (Ps : list (ParentRoute dstar)) : R :=
  match Ps with
  | [] => 0
  | P :: tl => pr_parent_action dstar P + forest_parent_action tl
  end.

Fixpoint forest_legal_cost
  {dstar : nat} (Ps : list (ParentRoute dstar)) : R :=
  match Ps with
  | [] => 0
  | P :: tl => pr_legal_cost dstar P + forest_legal_cost tl
  end.

Fixpoint forest_source_budget
  {dstar : nat} (Ps : list (ParentRoute dstar)) : R :=
  match Ps with
  | [] => 0
  | P :: tl =>
      SO.psc_budget (pr_source_class dstar P)
      + forest_source_budget tl
  end.

Theorem GPPR30_FOREST_CHILD_ACTION_NONNEG :
  forall dstar : nat,
  forall Ps : list (ParentRoute dstar),
    0 <= forest_child_action Ps.
Proof.
  intros dstar Ps.
  induction Ps as [|P tl IH].
  - simpl. lra.
  - simpl.
    pose proof (GPPR20_ROUTE_CHILD_ACTION_NONNEG dstar P) as HP.
    lra.
Qed.

Theorem GPPR31_FOREST_PARENT_ACTION_BOUNDED_BY_SOURCE_BUDGET :
  forall dstar : nat,
  forall Ps : list (ParentRoute dstar),
    forest_parent_action Ps <= forest_source_budget Ps.
Proof.
  intros dstar Ps.
  induction Ps as [|P tl IH].
  - simpl. lra.
  - simpl.
    pose proof (pr_parent_action_budget dstar P) as HP.
    lra.
Qed.

(* Sum the local reproduction inequalities over an arbitrary finite forest. *)
Theorem GPPR32_FOREST_REPRODUCTION :
  forall dstar : nat,
  forall Ps : list (ParentRoute dstar),
    4 * forest_child_action Ps
      <= forest_parent_action Ps + forest_legal_cost Ps.
Proof.
  intros dstar Ps.
  induction Ps as [|P tl IH].
  - simpl. lra.
  - simpl.
    pose proof
      (GPPR22_ROUTE_REPRODUCTION_PAYS_ALL_CHILDREN dstar P) as HP.
    lra.
Qed.

Theorem GPPR33_FOREST_REPRODUCTION_BY_SOURCE_BUDGET :
  forall dstar : nat,
  forall Ps : list (ParentRoute dstar),
    4 * forest_child_action Ps
      <= forest_source_budget Ps + forest_legal_cost Ps.
Proof.
  intros dstar Ps.
  pose proof (GPPR32_FOREST_REPRODUCTION dstar Ps) as Hrep.
  pose proof
    (GPPR31_FOREST_PARENT_ACTION_BOUNDED_BY_SOURCE_BUDGET
      dstar Ps) as Hbud.
  lra.
Qed.

(* Uniform M7-facing form: if grouped parent budgets and legal costs have
   finite global bounds, then all outgoing child action is paid. *)
Theorem GPPR40_UNIFORM_PARENT_REPRODUCTION_BOUND :
  forall dstar : nat,
  forall Ps : list (ParentRoute dstar),
  forall M C : R,
    forest_source_budget Ps <= M ->
    forest_legal_cost Ps <= C ->
    4 * forest_child_action Ps <= M + C.
Proof.
  intros dstar Ps M C HM HC.
  pose proof (GPPR33_FOREST_REPRODUCTION_BY_SOURCE_BUDGET dstar Ps) as H.
  lra.
Qed.

(* Direct local-recurrence adapter:
   if the next resistant action is owned by these children, then the parent
   forest and legal costs pay it in exactly the 4*next <= parent+cost form. *)
Theorem GPPR41_NEXT_ACTION_PAID_BY_PARENT_FOREST :
  forall dstar : nat,
  forall Ps : list (ParentRoute dstar),
  forall Anext : R,
    Anext <= forest_child_action Ps ->
    4 * Anext
      <= forest_parent_action Ps + forest_legal_cost Ps.
Proof.
  intros dstar Ps Anext Hnext.
  pose proof (GPPR32_FOREST_REPRODUCTION dstar Ps) as Hrep.
  lra.
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_PARENT_DEGREE_REPRODUCTION.

Check NSE_GP_PARENT_DEGREE_REPRODUCTION.natR.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR00_NATR_NONNEG.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR01_NATR_MONOTONE.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.AllNonnegative.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.AllLe.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR10_SUM_NONNEG.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR11_SUM_LE_LENGTH_TIMES_BOUND.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR12_BOUNDED_DEGREE_CHILD_ACTION.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.ParentRoute.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.route_child_action.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR20_ROUTE_CHILD_ACTION_NONNEG.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR21_ROUTE_DEGREE_PAYS_CHILD_ACTION.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR22_ROUTE_REPRODUCTION_PAYS_ALL_CHILDREN.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.forest_child_action.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.forest_parent_action.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.forest_legal_cost.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.forest_source_budget.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR31_FOREST_PARENT_ACTION_BOUNDED_BY_SOURCE_BUDGET.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR32_FOREST_REPRODUCTION.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR33_FOREST_REPRODUCTION_BY_SOURCE_BUDGET.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR40_UNIFORM_PARENT_REPRODUCTION_BOUND.
Check NSE_GP_PARENT_DEGREE_REPRODUCTION.GPPR41_NEXT_ACTION_PAID_BY_PARENT_FOREST.
