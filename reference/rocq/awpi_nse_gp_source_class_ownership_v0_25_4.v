
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_perspective_action_v0_11_2.
Require Import awpi_nse_gp_closed_action_envelope_v0_19_2.
Require Import awpi_nse_gp_finite_cutoff_envelope_v0_20_0.
Require Import awpi_nse_gp_leray_modal_triad_adapter_v0_13_3.
Import ListNotations.
Open Scope R_scope.

Module NSE_GP_SOURCE_CLASS_OWNERSHIP.

Module PA := NSE_GP_PERSPECTIVE_ACTION.
Module CE := NSE_GP_CLOSED_ACTION_ENVELOPE.
Module CU := NSE_GP_FINITE_CUTOFF_ENVELOPE.
Module LM := NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.

Fixpoint sumR (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: tl => x + sumR tl
  end.

Theorem GPSO00_SUMR_APP :
  forall xs ys : list R,
    sumR (xs ++ ys) = sumR xs + sumR ys.
Proof.
  intros xs ys.
  induction xs as [|x tl IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Theorem GPSO01_SUMR_CONCAT :
  forall xss : list (list R),
    sumR (concat xss) = sumR (map sumR xss).
Proof.
  intro xss.
  induction xss as [|xs tl IH].
  - reflexivity.
  - simpl.
    rewrite GPSO00_SUMR_APP.
    rewrite IH.
    reflexivity.
Qed.

(* A physical parent/source class is represented by its actual signed physical
   contributions.  The class work is formed by summing those contributions
   FIRST; only then is the positive part squared through ActionEnvelope.

   Thus cross terms internal to a source class remain part of the class action.
   There is intentionally no per-triad action field here. *)
Record PhysicalSourceClass : Type := {
  psc_atoms : list R;
  psc_capacity : R;
  psc_budget : R;
  psc_capacity_nonnegative : 0 <= psc_capacity;
  psc_budget_nonnegative : 0 <= psc_budget;
  psc_group_envelope :
    CE.ActionEnvelope
      (LM.pos (sumR psc_atoms))
      psc_capacity
      psc_budget
}.

Definition class_signed_work (P : PhysicalSourceClass) : R :=
  sumR (psc_atoms P).

Definition class_positive_work (P : PhysicalSourceClass) : R :=
  LM.pos (class_signed_work P).

Theorem GPSO10_CLASS_SIGNED_WORK_IS_PHYSICAL_SUM :
  forall P : PhysicalSourceClass,
    class_signed_work P = sumR (psc_atoms P).
Proof.
  reflexivity.
Qed.

Theorem GPSO11_CLASS_ACTION_IS_GROUP_FIRST :
  forall P : PhysicalSourceClass,
    CE.ActionEnvelope
      (class_positive_work P)
      (psc_capacity P)
      (psc_budget P).
Proof.
  intro P.
  unfold class_positive_work, class_signed_work.
  exact (psc_group_envelope P).
Qed.

Theorem GPSO12_CLASS_POLYNOMIAL_BOUND :
  forall P : PhysicalSourceClass,
    class_positive_work P * class_positive_work P
      <= psc_capacity P * psc_budget P.
Proof.
  intro P.
  exact
    (CE.GPCE20_ENVELOPE_IS_POLYNOMIAL_BOUND
      (class_positive_work P)
      (psc_capacity P)
      (psc_budget P)
      (GPSO11_CLASS_ACTION_IS_GROUP_FIRST P)).
Qed.

Theorem GPSO13_CLASS_RECONSTRUCTS_EXACT_ACTION :
  forall P : PhysicalSourceClass,
    exists A : R,
      0 <= A /\
      A <= psc_budget P /\
      PA.ActionRel
        (class_positive_work P)
        (psc_capacity P)
        A.
Proof.
  intro P.
  apply CE.GPCE12_CLOSED_ENVELOPE_RECONSTRUCTS_ACTION.
  exact (GPSO11_CLASS_ACTION_IS_GROUP_FIRST P).
Qed.

Fixpoint parent_signed_work (Ps : list PhysicalSourceClass) : R :=
  match Ps with
  | [] => 0
  | P :: tl => class_signed_work P + parent_signed_work tl
  end.

Fixpoint parent_positive_work (Ps : list PhysicalSourceClass) : R :=
  match Ps with
  | [] => 0
  | P :: tl => class_positive_work P + parent_positive_work tl
  end.

Fixpoint parent_capacity (Ps : list PhysicalSourceClass) : R :=
  match Ps with
  | [] => 0
  | P :: tl => psc_capacity P + parent_capacity tl
  end.

Fixpoint parent_budget (Ps : list PhysicalSourceClass) : R :=
  match Ps with
  | [] => 0
  | P :: tl => psc_budget P + parent_budget tl
  end.

Definition physical_atoms (Ps : list PhysicalSourceClass) : list R :=
  concat (map psc_atoms Ps).

(* Exact ownership decomposition: summing all physical atoms is exactly the
   same as summing the already-grouped signed parent/source-class works. *)
Theorem GPSO20_EXACT_PHYSICAL_PARENT_DECOMPOSITION :
  forall Ps : list PhysicalSourceClass,
    sumR (physical_atoms Ps) = parent_signed_work Ps.
Proof.
  intro Ps.
  unfold physical_atoms.
  rewrite GPSO01_SUMR_CONCAT.
  induction Ps as [|P tl IH].
  - reflexivity.
  - simpl.
    unfold class_signed_work.
    rewrite IH.
    reflexivity.
Qed.

Theorem GPSO21_POS_ZERO :
  LM.pos 0 = 0.
Proof.
  unfold LM.pos.
  rewrite Rabs_R0.
  lra.
Qed.

Theorem GPSO22_POS_BINARY_SUBADDITIVE :
  forall a b : R,
    LM.pos (a+b) <= LM.pos a + LM.pos b.
Proof.
  intros a b.
  pose proof (LM.GPLM02_POS_THREE_SUBADDITIVE a b 0) as H.
  rewrite GPSO21_POS_ZERO in H.
  replace (a + b + 0) with (a + b) in H by lra.
  lra.
Qed.

(* The positive part of the full resistant cut is dominated by the sum of
   positive parent/source-class works.  We do NOT replace each class action by
   a sum of per-triad actions. *)
Theorem GPSO23_TOTAL_POSITIVE_WORK_DOMINATED_BY_PARENT_CLASSES :
  forall Ps : list PhysicalSourceClass,
    LM.pos (parent_signed_work Ps) <= parent_positive_work Ps.
Proof.
  intro Ps.
  induction Ps as [|P tl IH].
  - simpl. rewrite GPSO21_POS_ZERO. lra.
  - simpl.
    eapply Rle_trans.
    + apply GPSO22_POS_BINARY_SUBADDITIVE.
    + unfold class_positive_work.
      lra.
Qed.

(* Parent/source classes can now be fused at the class level.  Since each
   envelope was constructed AFTER physical grouping, internal interference is
   retained while only inter-class fusion uses perspective convexity. *)
Theorem GPSO30_PARENT_CLASS_ENVELOPE :
  forall Ps : list PhysicalSourceClass,
    CE.ActionEnvelope
      (parent_positive_work Ps)
      (parent_capacity Ps)
      (parent_budget Ps).
Proof.
  intro Ps.
  induction Ps as [|P tl IH].
  - simpl.
    exact CU.GPCU30_EMPTY_CUTOFF_ENVELOPE.
  - simpl.
    apply CU.GPCU10_BINARY_FUSION_PRESERVES_ENVELOPE.
    + exact (GPSO11_CLASS_ACTION_IS_GROUP_FIRST P).
    + exact IH.
Qed.

Theorem GPSO31_PARENT_CLASS_POLYNOMIAL_BOUND :
  forall Ps : list PhysicalSourceClass,
    parent_positive_work Ps * parent_positive_work Ps
      <= parent_capacity Ps * parent_budget Ps.
Proof.
  intro Ps.
  exact
    (CE.GPCE20_ENVELOPE_IS_POLYNOMIAL_BOUND
      (parent_positive_work Ps)
      (parent_capacity Ps)
      (parent_budget Ps)
      (GPSO30_PARENT_CLASS_ENVELOPE Ps)).
Qed.

Theorem GPSO32_PARENT_CLASS_RECONSTRUCTS_ACTION :
  forall Ps : list PhysicalSourceClass,
    exists A : R,
      0 <= A /\
      A <= parent_budget Ps /\
      PA.ActionRel
        (parent_positive_work Ps)
        (parent_capacity Ps)
        A.
Proof.
  intro Ps.
  apply CE.GPCE12_CLOSED_ENVELOPE_RECONSTRUCTS_ACTION.
  exact (GPSO30_PARENT_CLASS_ENVELOPE Ps).
Qed.

(* If the total signed resistant cut is exactly the physical parent
   decomposition, its positive work is controlled by the grouped parent
   positive works, before any action is formed. *)
Theorem GPSO40_RESISTANT_CUT_OWNED_BY_PARENT_CLASSES :
  forall Ps : list PhysicalSourceClass,
  forall Wres : R,
    Wres = sumR (physical_atoms Ps) ->
    LM.pos Wres <= parent_positive_work Ps.
Proof.
  intros Ps Wres Hres.
  rewrite Hres.
  rewrite GPSO20_EXACT_PHYSICAL_PARENT_DECOMPOSITION.
  apply GPSO23_TOTAL_POSITIVE_WORK_DOMINATED_BY_PARENT_CLASSES.
Qed.

(* The remaining PDE theorem may supply a uniform parent budget M.
   Once it does, the entire grouped parent family is in the same closed
   action currency. *)
Theorem GPSO41_UNIFORM_PARENT_BUDGET :
  forall Ps : list PhysicalSourceClass,
  forall M : R,
    0 <= M ->
    parent_budget Ps <= M ->
    parent_positive_work Ps * parent_positive_work Ps
      <= parent_capacity Ps * M.
Proof.
  intros Ps M HM Hbudget.
  pose proof (GPSO30_PARENT_CLASS_ENVELOPE Ps) as Henv.
  unfold CE.ActionEnvelope in Henv.
  destruct Henv as [HD [HB Hpoly]].
  nra.
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_SOURCE_CLASS_OWNERSHIP.

Check NSE_GP_SOURCE_CLASS_OWNERSHIP.sumR.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO00_SUMR_APP.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO01_SUMR_CONCAT.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.PhysicalSourceClass.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.class_signed_work.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.class_positive_work.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO11_CLASS_ACTION_IS_GROUP_FIRST.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO12_CLASS_POLYNOMIAL_BOUND.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO13_CLASS_RECONSTRUCTS_EXACT_ACTION.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.parent_signed_work.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.parent_positive_work.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.parent_capacity.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.parent_budget.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.physical_atoms.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO20_EXACT_PHYSICAL_PARENT_DECOMPOSITION.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO23_TOTAL_POSITIVE_WORK_DOMINATED_BY_PARENT_CLASSES.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO30_PARENT_CLASS_ENVELOPE.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO31_PARENT_CLASS_POLYNOMIAL_BOUND.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO32_PARENT_CLASS_RECONSTRUCTS_ACTION.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO40_RESISTANT_CUT_OWNED_BY_PARENT_CLASSES.
Check NSE_GP_SOURCE_CLASS_OWNERSHIP.GPSO41_UNIFORM_PARENT_BUDGET.
