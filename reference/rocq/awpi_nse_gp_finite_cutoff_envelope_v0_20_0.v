
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_perspective_action_v0_11_2.
Require Import awpi_nse_gp_closed_action_envelope_v0_19_2.
Import ListNotations.
Open Scope R_scope.

Module NSE_GP_FINITE_CUTOFF_ENVELOPE.

Module PA := NSE_GP_PERSPECTIVE_ACTION.
Module CE := NSE_GP_CLOSED_ACTION_ENVELOPE.

(* A closed action envelope is stable under a nonnegative common kernel
   weight.  This is the denominator-free version of matched positive-kernel
   propagation. *)
Theorem GPCU00_POSITIVE_WEIGHT_PRESERVES_ENVELOPE :
  forall k w d M : R,
    0 <= k ->
    CE.ActionEnvelope w d M ->
    CE.ActionEnvelope (k*w) (k*d) (k*M).
Proof.
  intros k w d M Hk Henv.
  unfold CE.ActionEnvelope in *.
  destruct Henv as [Hd [HM Hbound]].
  split.
  - nra.
  - split.
    + nra.
    + nra.
Qed.

(* Binary fusion closure.  No quotient is used in the statement, and
   the zero-capacity cases are handled explicitly. *)
Theorem GPCU10_BINARY_FUSION_PRESERVES_ENVELOPE :
  forall w1 d1 M1 w2 d2 M2 : R,
    CE.ActionEnvelope w1 d1 M1 ->
    CE.ActionEnvelope w2 d2 M2 ->
    CE.ActionEnvelope (w1+w2) (d1+d2) (M1+M2).
Proof.
  intros w1 d1 M1 w2 d2 M2 Henv1 Henv2.

  unfold CE.ActionEnvelope in Henv1, Henv2.
  destruct Henv1 as [Hd1 [HM1 Hb1]].
  destruct Henv2 as [Hd2 [HM2 Hb2]].

  unfold CE.ActionEnvelope.
  split.
  - lra.
  - split.
    + lra.
    + destruct (Req_dec d1 0) as [Hz1 | Hnz1].
      * subst d1.
        assert (Hw1 : w1 = 0).
        {
          apply (CE.GPCE01_ZERO_CAPACITY_FORCES_ZERO_WORK w1 M1).
          unfold CE.ActionEnvelope.
          split.
          - lra.
          - split.
            + exact HM1.
            + exact Hb1.
        }
        subst w1.
        nra.
      * destruct (Req_dec d2 0) as [Hz2 | Hnz2].
        -- subst d2.
           assert (Hw2 : w2 = 0).
           {
             apply (CE.GPCE01_ZERO_CAPACITY_FORCES_ZERO_WORK w2 M2).
             unfold CE.ActionEnvelope.
             split.
             - lra.
             - split.
               + exact HM2.
               + exact Hb2.
           }
           subst w2.
           nra.
        -- assert (Hd1p : 0 < d1) by lra.
           assert (Hd2p : 0 < d2) by lra.
           assert (Hsum : 0 < d1+d2) by lra.
           assert (Hsumne : d1+d2 <> 0) by lra.

           assert (Henv1' : CE.ActionEnvelope w1 d1 M1).
           {
             unfold CE.ActionEnvelope.
             split; [exact Hd1|].
             split; assumption.
           }
           assert (Henv2' : CE.ActionEnvelope w2 d2 M2).
           {
             unfold CE.ActionEnvelope.
             split; [exact Hd2|].
             split; assumption.
           }

           destruct
             (CE.GPCE10_POSITIVE_ENVELOPE_RECONSTRUCTS_ACTION
               w1 d1 M1 Hd1p Henv1')
             as [A1 [HA1 [HA1M Hrel1]]].
           destruct
             (CE.GPCE10_POSITIVE_ENVELOPE_RECONSTRUCTS_ACTION
               w2 d2 M2 Hd2p Henv2')
             as [A2 [HA2 [HA2M Hrel2]]].

           set (Ac := ((w1+w2)*(w1+w2))/(d1+d2)).
           assert (Hrelc : PA.ActionRel (w1+w2) (d1+d2) Ac).
           {
             unfold PA.ActionRel.
             unfold Ac.
             unfold Rdiv.
             replace
               ((d1+d2) * (((w1+w2)*(w1+w2)) * / (d1+d2)))
               with
               (((w1+w2)*(w1+w2)) * ((d1+d2) * / (d1+d2)))
               by ring.
             rewrite Rinv_r.
             - ring.
             - exact Hsumne.
           }

           pose proof
             (PA.GPPA11_BINARY_FUSION_CONTRACTS_ACTION
               w1 w2 d1 d2 A1 A2 Ac
               Hd1p Hd2p Hrel1 Hrel2 Hrelc) as Hcontract.

           unfold PA.ActionRel in Hrelc.
           nra.
Qed.

Theorem GPCU20_THREE_ATOM_FUSION_PRESERVES_ENVELOPE :
  forall w1 d1 M1 w2 d2 M2 w3 d3 M3 : R,
    CE.ActionEnvelope w1 d1 M1 ->
    CE.ActionEnvelope w2 d2 M2 ->
    CE.ActionEnvelope w3 d3 M3 ->
    CE.ActionEnvelope
      ((w1+w2)+w3)
      ((d1+d2)+d3)
      ((M1+M2)+M3).
Proof.
  intros w1 d1 M1 w2 d2 M2 w3 d3 M3 H1 H2 H3.
  pose proof
    (GPCU10_BINARY_FUSION_PRESERVES_ENVELOPE
      w1 d1 M1 w2 d2 M2 H1 H2) as H12.
  exact
    (GPCU10_BINARY_FUSION_PRESERVES_ENVELOPE
      (w1+w2) (d1+d2) (M1+M2)
      w3 d3 M3 H12 H3).
Qed.

Theorem GPCU21_FOUR_ATOM_FUSION_PRESERVES_ENVELOPE :
  forall w0 d0 M0 w1 d1 M1 w2 d2 M2 w3 d3 M3 : R,
    CE.ActionEnvelope w0 d0 M0 ->
    CE.ActionEnvelope w1 d1 M1 ->
    CE.ActionEnvelope w2 d2 M2 ->
    CE.ActionEnvelope w3 d3 M3 ->
    CE.ActionEnvelope
      (((w0+w1)+w2)+w3)
      (((d0+d1)+d2)+d3)
      (((M0+M1)+M2)+M3).
Proof.
  intros w0 d0 M0 w1 d1 M1 w2 d2 M2 w3 d3 M3 H0 H1 H2 H3.
  pose proof
    (GPCU20_THREE_ATOM_FUSION_PRESERVES_ENVELOPE
      w0 d0 M0 w1 d1 M1 w2 d2 M2 H0 H1 H2) as H012.
  exact
    (GPCU10_BINARY_FUSION_PRESERVES_ENVELOPE
      ((w0+w1)+w2) ((d0+d1)+d2) ((M0+M1)+M2)
      w3 d3 M3 H012 H3).
Qed.

(* Finite-cutoff carrier.  Each atom already contains the closed local
   action bound; summing the carrier gives the face quantities. *)
Record EnvelopeAtom : Type := {
  atom_work : R;
  atom_capacity : R;
  atom_budget : R;
  atom_envelope :
    CE.ActionEnvelope atom_work atom_capacity atom_budget
}.

Fixpoint cutoff_work (xs : list EnvelopeAtom) : R :=
  match xs with
  | [] => 0
  | x :: tl => atom_work x + cutoff_work tl
  end.

Fixpoint cutoff_capacity (xs : list EnvelopeAtom) : R :=
  match xs with
  | [] => 0
  | x :: tl => atom_capacity x + cutoff_capacity tl
  end.

Fixpoint cutoff_budget (xs : list EnvelopeAtom) : R :=
  match xs with
  | [] => 0
  | x :: tl => atom_budget x + cutoff_budget tl
  end.

Theorem GPCU30_EMPTY_CUTOFF_ENVELOPE :
  CE.ActionEnvelope 0 0 0.
Proof.
  unfold CE.ActionEnvelope.
  repeat split; lra.
Qed.

(* Arbitrary finite Fourier/Galerkin face:
   (sum work)^2 <= (sum capacity)(sum action budget). *)
Theorem GPCU31_FINITE_CUTOFF_ENVELOPE :
  forall xs : list EnvelopeAtom,
    CE.ActionEnvelope
      (cutoff_work xs)
      (cutoff_capacity xs)
      (cutoff_budget xs).
Proof.
  intros xs.
  induction xs as [|x tl IH].
  - exact GPCU30_EMPTY_CUTOFF_ENVELOPE.
  - simpl.
    apply GPCU10_BINARY_FUSION_PRESERVES_ENVELOPE.
    + exact (atom_envelope x).
    + exact IH.
Qed.

Theorem GPCU32_FINITE_CUTOFF_POLYNOMIAL_BOUND :
  forall xs : list EnvelopeAtom,
    cutoff_work xs * cutoff_work xs
      <= cutoff_capacity xs * cutoff_budget xs.
Proof.
  intros xs.
  pose proof (GPCU31_FINITE_CUTOFF_ENVELOPE xs) as H.
  exact (CE.GPCE20_ENVELOPE_IS_POLYNOMIAL_BOUND
    (cutoff_work xs) (cutoff_capacity xs) (cutoff_budget xs) H).
Qed.

(* If the total cutoff budget is uniformly bounded by M, the whole finite
   face already satisfies the common closed envelope w^2 <= d M. *)
Theorem GPCU33_FINITE_CUTOFF_UNIFORM_BUDGET :
  forall xs : list EnvelopeAtom, forall M : R,
    0 <= M ->
    cutoff_budget xs <= M ->
    cutoff_work xs * cutoff_work xs
      <= cutoff_capacity xs * M.
Proof.
  intros xs M HM Hbudget.
  pose proof (GPCU31_FINITE_CUTOFF_ENVELOPE xs) as Henv.
  unfold CE.ActionEnvelope in Henv.
  destruct Henv as [Hd [HB Hpoly]].
  nra.
Qed.

(* Reconstruct the face ActionRel certificate after finite aggregation. *)
Theorem GPCU40_FINITE_CUTOFF_RECONSTRUCTS_FACE_ACTION :
  forall xs : list EnvelopeAtom,
    exists A : R,
      0 <= A /\
      A <= cutoff_budget xs /\
      PA.ActionRel
        (cutoff_work xs)
        (cutoff_capacity xs)
        A.
Proof.
  intros xs.
  apply CE.GPCE12_CLOSED_ENVELOPE_RECONSTRUCTS_ACTION.
  apply GPCU31_FINITE_CUTOFF_ENVELOPE.
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_FINITE_CUTOFF_ENVELOPE.

Check NSE_GP_FINITE_CUTOFF_ENVELOPE.GPCU00_POSITIVE_WEIGHT_PRESERVES_ENVELOPE.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.GPCU10_BINARY_FUSION_PRESERVES_ENVELOPE.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.GPCU20_THREE_ATOM_FUSION_PRESERVES_ENVELOPE.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.GPCU21_FOUR_ATOM_FUSION_PRESERVES_ENVELOPE.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.EnvelopeAtom.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.cutoff_work.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.cutoff_capacity.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.cutoff_budget.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.GPCU30_EMPTY_CUTOFF_ENVELOPE.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.GPCU31_FINITE_CUTOFF_ENVELOPE.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.GPCU32_FINITE_CUTOFF_POLYNOMIAL_BOUND.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.GPCU33_FINITE_CUTOFF_UNIFORM_BUDGET.
Check NSE_GP_FINITE_CUTOFF_ENVELOPE.GPCU40_FINITE_CUTOFF_RECONSTRUCTS_FACE_ACTION.
