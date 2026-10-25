From Stdlib Require Import Reals Lra Psatz String.

Module NSE_GP_MATCHED_HEAT_RENEWAL.

Open Scope R_scope.

(*
  Matched heat-scale renewal algebra.

  Intended analytic input on one dyadic Stokes band Lambda <= lambda <= 4 Lambda:
    tau := 1/Lambda,
    c(lambda) := 1 - exp(-2*tau*lambda).

  The elementary heat-weight range gives a condition ratio <= 4/3.
  A Kantorovich certificate then gives P <= 49/48.  Combined with the
  projection certificate 1 <= P*(1-eta), this forces eta <= 1/49.

  This file formalizes only the finite real algebra after those analytic
  certificates.  It then combines:
    compact/internal action <= 1/49 parent,
    sqrt-action triangle for the boundary piece,
    cumulative factor-two DT contraction of boundary descendants,
  to obtain the strict two-stage renewal factor 17/49.
*)

Section MATCHED_HEAT_CONDITION.

  Theorem NSMH00_HEAT_RANGE_GIVES_FOUR_THIRDS_CONDITION :
    forall cmin cmax : R,
      0 <= cmin ->
      3 <= 4 * cmin ->
      cmax <= 1 ->
      3 * cmax <= 4 * cmin.
  Proof.
    intros cmin cmax Hmin Hcmin Hcmax.
    nra.
  Qed.

  (*
    Cross-multiplied Kantorovich/projection consequence:
      P <= 49/48,
      1 <= P*(1-eta)
    imply eta <= 1/49.
  *)
  Theorem NSMH01_MATCHED_CONDITION_GIVES_ONE_OVER_49_EFFICIENCY_GAP :
    forall eta P : R,
      0 <= eta ->
      0 < P ->
      48 * P <= 49 ->
      1 <= P * (1 - eta) ->
      49 * eta <= 1.
  Proof.
    intros eta P Heta HP Hband Hproj.
    assert (Hone : 0 <= 1 - eta).
    {
      nra.
    }
    assert (Hmul : 0 <= (49 - 48 * P) * (1 - eta)).
    {
      apply Rmult_le_pos.
      - lra.
      - exact Hone.
    }
    nra.
  Qed.

End MATCHED_HEAT_CONDITION.

Section ACTION_TRIANGLE_AND_DT.

  (*
    a,i,b are square-root action amplitudes of parent, internal, boundary.
    7*i <= a is the amplitude form of I <= A/49.
    b <= a+i is the reverse action triangle for boundary = parent-internal.
  *)
  Theorem NSMH10_BOUNDARY_AMPLITUDE_IS_AT_MOST_EIGHT_SEVENTHS :
    forall a i b : R,
      0 <= a ->
      0 <= i ->
      0 <= b ->
      7 * i <= a ->
      b <= a + i ->
      7 * b <= 8 * a.
  Proof.
    intros a i b Ha Hi Hb Hint Htri.
    lra.
  Qed.

  Theorem NSMH11_BOUNDARY_ACTION_IS_AT_MOST_64_OVER_49 :
    forall a i b : R,
      0 <= a ->
      0 <= i ->
      0 <= b ->
      7 * i <= a ->
      b <= a + i ->
      49 * b * b <= 64 * a * a.
  Proof.
    intros a i b Ha Hi Hb Hint Htri.
    pose proof
      (NSMH10_BOUNDARY_AMPLITUDE_IS_AT_MOST_EIGHT_SEVENTHS
         a i b Ha Hi Hb Hint Htri) as Hamp.
    assert (Hprod : 0 <= (8 * a - 7 * b) * (8 * a + 7 * b)).
    {
      apply Rmult_le_pos.
      - lra.
      - nra.
    }
    nra.
  Qed.

  Theorem NSMH12_INTERNAL_ACTION_IS_AT_MOST_ONE_OVER_49 :
    forall a i : R,
      0 <= a ->
      0 <= i ->
      7 * i <= a ->
      49 * i * i <= a * a.
  Proof.
    intros a i Ha Hi Hint.
    assert (Hprod : 0 <= (a - 7 * i) * (a + 7 * i)).
    {
      apply Rmult_le_pos.
      - lra.
      - nra.
    }
    nra.
  Qed.

  (* Boundary action B <= 64/49 A, followed by factor-two DT action law U <= B/4. *)
  Theorem NSMH13_BOUNDARY_THEN_DT_GIVES_16_OVER_49 :
    forall parent boundary uv : R,
      0 <= parent ->
      0 <= boundary ->
      0 <= uv ->
      49 * boundary <= 64 * parent ->
      4 * uv <= boundary ->
      49 * uv <= 16 * parent.
  Proof.
    intros parent boundary uv Hp Hb Huv Hbound Hdt.
    nra.
  Qed.

  Theorem NSMH14_INTERNAL_PLUS_BOUNDARY_DT_GIVES_17_OVER_49 :
    forall parent internal uv : R,
      0 <= parent ->
      0 <= internal ->
      0 <= uv ->
      49 * internal <= parent ->
      49 * uv <= 16 * parent ->
      49 * (internal + uv) <= 17 * parent.
  Proof.
    intros parent internal uv Hp Hi Huv Hint Hdt.
    nra.
  Qed.

  (* Fully composed amplitude-level two-stage renewal. *)
  Theorem NSMH15_MATCHED_HEAT_TWO_STAGE_RENEWAL_17_OVER_49 :
    forall a i b uv child paid : R,
      0 <= a ->
      0 <= i ->
      0 <= b ->
      0 <= uv ->
      0 <= child ->
      0 <= paid ->
      7 * i <= a ->
      b <= a + i ->
      4 * uv <= b * b ->
      child <= i * i + uv + paid ->
      49 * child <= 17 * a * a + 49 * paid.
  Proof.
    intros a i b uv child paid Ha Hi Hb Huv Hchild Hpaid Hint Htri Hdt Hsplit.
    pose proof
      (NSMH11_BOUNDARY_ACTION_IS_AT_MOST_64_OVER_49
         a i b Ha Hi Hb Hint Htri) as Hboundary.
    pose proof
      (NSMH12_INTERNAL_ACTION_IS_AT_MOST_ONE_OVER_49
         a i Ha Hi Hint) as Hinternal.
    assert (Huv49 : 49 * uv <= 16 * (a * a)).
    {
      nra.
    }
    nra.
  Qed.

End ACTION_TRIANGLE_AND_DT.

Section PREFIX_TELESCOPING.

  Fixpoint resistant_prefix (mass : nat -> R) (N : nat) : R :=
    match N with
    | O => mass O
    | S n => resistant_prefix mass n + mass (S n)
    end.

  Fixpoint paid_prefix (paid : nat -> R) (N : nat) : R :=
    match N with
    | O => 0
    | S n => paid_prefix paid n + paid n
    end.

  Theorem NSMH20_EXACT_17_OVER_49_PREFIX_INVARIANT :
    forall (mass paid : nat -> R),
      (forall n : nat, 0 <= mass n) ->
      (forall n : nat,
         49 * mass (S n) <= 17 * mass n + 49 * paid n) ->
      forall N : nat,
        32 * resistant_prefix mass N + 17 * mass N <=
        49 * mass O + 49 * paid_prefix paid N.
  Proof.
    intros mass paid Hmass Hstep N.
    induction N as [|N IHN].
    - simpl.
      nra.
    - simpl.
      specialize (Hstep N).
      nra.
  Qed.

  Theorem NSMH21_UNIFORM_PAID_BUDGET_GIVES_17_OVER_49_PREFIX_BOUND :
    forall (mass paid : nat -> R) (B : R),
      (forall n : nat, 0 <= mass n) ->
      (forall n : nat,
         49 * mass (S n) <= 17 * mass n + 49 * paid n) ->
      (forall N : nat, paid_prefix paid N <= B) ->
      forall N : nat,
        32 * resistant_prefix mass N <= 49 * mass O + 49 * B.
  Proof.
    intros mass paid B Hmass Hstep Hbudget N.
    pose proof
      (NSMH20_EXACT_17_OVER_49_PREFIX_INVARIANT
         mass paid Hmass Hstep N) as Hinv.
    specialize (Hbudget N).
    specialize (Hmass N).
    nra.
  Qed.

End PREFIX_TELESCOPING.

Section ABSTRACT_PHYSICAL_FRONTIER.

  Context {Velocity : Type}.

  Variable LerayHopfT3 : Velocity -> Prop.
  Variable MatchedHeatActionFaithfulRenewal : Velocity -> Prop.
  Variable UniformPaidInjectionBudget : Velocity -> Prop.
  Variable ActualGPM7 : Velocity -> Prop.

  Definition MatchedHeatRenewalToGPM7Principle : Prop :=
    forall u : Velocity,
      LerayHopfT3 u ->
      MatchedHeatActionFaithfulRenewal u ->
      UniformPaidInjectionBudget u ->
      ActualGPM7 u.

  Theorem NSMH90_MATCHED_HEAT_RENEWAL_PLUS_PAID_BUDGET_REDUCES_TO_GPM7 :
    MatchedHeatRenewalToGPM7Principle ->
    forall u : Velocity,
      LerayHopfT3 u ->
      MatchedHeatActionFaithfulRenewal u ->
      UniformPaidInjectionBudget u ->
      ActualGPM7 u.
  Proof.
    intros H u Hlh Hrenew Hpaid.
    exact (H u Hlh Hrenew Hpaid).
  Qed.

End ABSTRACT_PHYSICAL_FRONTIER.

Definition STATUS : string :=
  "NSE_GP_MATCHED_HEAT_17_OVER_49_RENEWAL_STANDALONE_NO_ADMITTED"%string.

End NSE_GP_MATCHED_HEAT_RENEWAL.

Print Assumptions NSE_GP_MATCHED_HEAT_RENEWAL.NSMH01_MATCHED_CONDITION_GIVES_ONE_OVER_49_EFFICIENCY_GAP.
Print Assumptions NSE_GP_MATCHED_HEAT_RENEWAL.NSMH15_MATCHED_HEAT_TWO_STAGE_RENEWAL_17_OVER_49.
Print Assumptions NSE_GP_MATCHED_HEAT_RENEWAL.NSMH20_EXACT_17_OVER_49_PREFIX_INVARIANT.
