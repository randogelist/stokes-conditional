(* Countable completion of the actual M7 critical readouts, followed by the
   existing conditional Serrin exit. The full readout is the least upper
   bound of ALL finite prefixes, never bounded by a chosen finite prefix.

   This module constructs the countable readout functions from real
   completeness. Physical Sobolev norms, their actual time integrals and
   the continuation theorem remain explicit binding/exit hypotheses. *)
From Stdlib Require Import Reals Lra Psatz Field.
Require Import LHGP_Hilbert.
Require Import BKQR_LHGP_M7Injection BKQR_M7_WeightedCompletion.
Require Import BKQR_M7_CriticalCalculus BKQR_M7_ActionCells.
Require Import NSH_ChainInterface NSR_CriticalInterpolation NSR_Terminal.

Module BKQR_M7_SERRIN_BRIDGE.
Module I := BKQR_LHGP_M7_INJECTION.
Module W := BKQR_M7_WEIGHTED_COMPLETION.
Module M := BKQR_M7_CRITICAL_CALCULUS.
Module A := BKQR_M7_ACTION_CELLS.
Module CE := I.CE.
Module NS := NSE_CRITICAL_SERRIN_INTERPOLATION.
Module EX := NSE_SERRIN_BACK_TERMINAL.
Module SH := NSE_SHARED_CHAIN_INTERFACE.
Open Scope R_scope.

Definition critical_cap (X0 Seed Paid : R) : R :=
  X0 + A.sharp_action_budget Seed Paid.

Definition serrin_budget (Csq nu X0 Seed Paid : R) : R :=
  Csq * Csq * (critical_cap X0 Seed Paid) ^ 2 / nu.

Record CountableCriticalReadout (T : R) (lambda : nat -> R)
    (a : R -> nat -> R) (Dcum : nat -> R -> R)
    (Xinf Dinf : R -> R) : Prop := {
  countable_mass_identification : forall t, M.OpenTime T t ->
    W.WeightedTotal lambda (a t) (Xinf t);
  countable_dissipation_identification : forall t, M.OpenTime T t ->
    W.PrefixTotal (fun N => Dcum N t) (Dinf t)
}.

Definition SerrinNormBinding T (endpoints : A.OpenTime T -> NS.NormEndpoint)
    (Xinf Dinf : R -> R) (Csq : R) : Prop :=
  NS.CriticalNormBinding (A.OpenTime T) endpoints
    (fun p => Xinf (proj1_sig p)) (fun p => Dinf (proj1_sig p)) Csq.

(* A concrete supremum constructor: no selection from a Prop-valued
   existence theorem, and no additional axiom of countable choice. *)
Definition sequence_values (f : nat -> R) : R -> Prop :=
  fun r => exists N, r = f N.

Lemma sequence_values_bounded : forall f C,
  (forall N, f N <= C) -> bound (sequence_values f).
Proof.
  intros f C HC. exists C. intros r [N Hr]. rewrite Hr. apply HC.
Qed.

Lemma sequence_values_nonempty : forall f,
  exists r, sequence_values f r.
Proof. intro f. exists (f 0%nat). exists 0%nat. reflexivity. Qed.

Definition bounded_sequence_sup (f : nat -> R) (C : R)
    (HC : forall N, f N <= C) : R :=
  proj1_sig (completeness (sequence_values f)
    (sequence_values_bounded f C HC) (sequence_values_nonempty f)).

Lemma bounded_sequence_sup_total : forall f C HC,
  W.PrefixTotal f (bounded_sequence_sup f C HC).
Proof.
  intros f C HC. unfold bounded_sequence_sup.
  destruct (completeness (sequence_values f)
    (sequence_values_bounded f C HC) (sequence_values_nonempty f))
    as [v [Hupper Hleast]]. simpl. split.
  - intro N. apply Hupper. exists N. reflexivity.
  - intros E HE. apply Hleast. intros r [N Hr]. rewrite Hr. apply HE.
Qed.

Definition open_time_dec (T t : R) : {M.OpenTime T t} + {~ M.OpenTime T t}.
Proof.
  unfold M.OpenTime.
  destruct (Rle_dec 0 t) as [Hlo|Hlo];
    destruct (Rlt_dec t T) as [Hhi|Hhi].
  - left. split; assumption.
  - right. intros [_ H]. contradiction.
  - right. intros [H _]. contradiction.
  - right. intros [H _]. contradiction.
Defined.

Lemma injection_mass_prefix_bound : forall T nu lambda a Dcum Ccum X0 Seed Paid,
  I.SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid ->
  forall t, M.OpenTime T t -> forall N,
    W.weighted_prefix lambda (a t) N <= critical_cap X0 Seed Paid.
Proof.
  intros T nu lambda a Dcum Ccum X0 Seed Paid HI t Ht N.
  rewrite <- I.critical_mass_is_weighted_prefix.
  exact (I.injection_critical_mass_bound T nu lambda a Dcum Ccum
    X0 Seed Paid HI N t Ht).
Qed.

Definition canonical_mass_readout T nu lambda a Dcum Ccum X0 Seed Paid
    (HI : I.SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid)
    (t : R) : R :=
  match open_time_dec T t with
  | left Ht => bounded_sequence_sup (W.weighted_prefix lambda (a t))
      (critical_cap X0 Seed Paid)
      (injection_mass_prefix_bound T nu lambda a Dcum Ccum X0 Seed Paid HI t Ht)
  | right _ => 0
  end.

Definition canonical_dissipation_readout T nu lambda a Dcum Ccum X0 Seed Paid
    (HI : I.SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid)
    (t : R) : R :=
  match open_time_dec T t with
  | left Ht => bounded_sequence_sup (fun N => Dcum N t)
      ((X0 + A.sharp_action_budget Seed Paid) / nu)
      (fun N => I.injection_critical_dissipation_bound T nu lambda a Dcum Ccum
        X0 Seed Paid HI N t Ht)
  | right _ => 0
  end.

Theorem BKMS11_CANONICAL_COUNTABLE_READOUT :
  forall T nu lambda a Dcum Ccum X0 Seed Paid
    (HI : I.SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid),
  CountableCriticalReadout T lambda a Dcum
    (canonical_mass_readout T nu lambda a Dcum Ccum X0 Seed Paid HI)
    (canonical_dissipation_readout T nu lambda a Dcum Ccum X0 Seed Paid HI).
Proof.
  intros T nu lambda a Dcum Ccum X0 Seed Paid HI. constructor; intros t Ht.
  - unfold canonical_mass_readout. destruct (open_time_dec T t) as [H|H].
    + apply bounded_sequence_sup_total.
    + contradiction.
  - unfold canonical_dissipation_readout. destruct (open_time_dec T t) as [H|H].
    + apply bounded_sequence_sup_total.
    + contradiction.
Qed.

Theorem BKMS12_COUNTABLE_READOUT_EXISTS :
  forall T nu lambda a Dcum Ccum X0 Seed Paid,
  I.SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid ->
  exists Xinf Dinf : R -> R, CountableCriticalReadout T lambda a Dcum Xinf Dinf.
Proof.
  intros T nu lambda a Dcum Ccum X0 Seed Paid HI.
  exists (canonical_mass_readout T nu lambda a Dcum Ccum X0 Seed Paid HI),
    (canonical_dissipation_readout T nu lambda a Dcum Ccum X0 Seed Paid HI).
  apply BKMS11_CANONICAL_COUNTABLE_READOUT.
Qed.

Theorem BKMS10_COMPLETED_TOTALS_BOUNDED :
  forall T nu lambda a Dcum Ccum X0 Seed Paid Xinf Dinf,
  I.SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid ->
  CountableCriticalReadout T lambda a Dcum Xinf Dinf ->
  forall t, M.OpenTime T t ->
    0 <= Xinf t <= critical_cap X0 Seed Paid /\
    0 <= Dinf t <= critical_cap X0 Seed Paid / nu.
Proof.
  intros T nu lambda a Dcum Ccum X0 Seed Paid Xinf Dinf HI HR t Ht.
  destruct HR as [HX HD]. specialize (HX t Ht). specialize (HD t Ht).
  assert (HXnonneg : 0 <= Xinf t).
  { exact (proj1 HX 0%nat). }
  assert (HDnonneg : 0 <= Dinf t).
  { destruct (I.injection_countable_dissipation T nu lambda a Dcum Ccum
      X0 Seed Paid HI t Ht) as [v [[Hv _] HV]].
    assert (Dinf t = v) by (eapply W.PREFIX_TOTAL_UNIQUE; eassumption).
    lra. }
  split; split; try assumption.
  - apply (proj2 HX). exact (injection_mass_prefix_bound T nu lambda a Dcum
      Ccum X0 Seed Paid HI t Ht).
  - apply (proj2 HD). intro N.
    exact (I.injection_critical_dissipation_bound T nu lambda a Dcum Ccum
      X0 Seed Paid HI N t Ht).
Qed.

Lemma critical_cap_nonnegative_from_injection :
  forall T nu lambda a Dcum Ccum X0 Seed Paid,
  0 < T ->
  I.SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid ->
  0 <= critical_cap X0 Seed Paid.
Proof.
  intros T nu lambda a Dcum Ccum X0 Seed Paid HT HI.
  assert (Ht : M.OpenTime T 0) by (unfold M.OpenTime; lra).
  exact (I.injection_critical_mass_bound T nu lambda a Dcum Ccum
    X0 Seed Paid HI 0%nat 0 Ht).
Qed.

Theorem BKMS20_COMPLETED_UNIFORM_CRITICAL_ENERGY :
  forall T nu lambda a Dcum Ccum X0 Seed Paid Xinf Dinf,
  0 < T -> 0 < nu ->
  I.SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid ->
  CountableCriticalReadout T lambda a Dcum Xinf Dinf ->
  CE.UniformCriticalEnergy (A.OpenTime T)
    (fun p => Xinf (proj1_sig p)) (fun p => Dinf (proj1_sig p)).
Proof.
  intros T nu lambda a Dcum Ccum X0 Seed Paid Xinf Dinf HT Hnu HI HR.
  pose proof (critical_cap_nonnegative_from_injection T nu lambda a Dcum Ccum
    X0 Seed Paid HT HI) as HK.
  exists (critical_cap X0 Seed Paid), (critical_cap X0 Seed Paid / nu).
  split; [exact HK|]. split.
  - unfold Rdiv. apply Rmult_le_pos; [exact HK|left; apply Rinv_0_lt_compat; exact Hnu].
  - split; intro p;
      pose proof (BKMS10_COMPLETED_TOTALS_BOUNDED T nu lambda a Dcum Ccum
        X0 Seed Paid Xinf Dinf HI HR (proj1_sig p) (proj2_sig p)) as Hbound;
      tauto.
Qed.

(* Csq is the square of the spatial H1 -> L6 embedding constant. Thus
   Csq*Csq below is the fourth power of the ordinary embedding constant. *)
Theorem BKMS30_INJECTION_TO_SERRIN_OBSERVABLE :
  forall T nu lambda a Dcum Ccum X0 Seed Paid Xinf Dinf endpoints Csq,
  0 < T -> 0 < nu ->
  I.SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid ->
  CountableCriticalReadout T lambda a Dcum Xinf Dinf ->
  SerrinNormBinding T endpoints Xinf Dinf Csq ->
  forall p, NS.serrin46_observation (endpoints p) <=
    serrin_budget Csq nu X0 Seed Paid.
Proof.
  intros T nu lambda a Dcum Ccum X0 Seed Paid Xinf Dinf endpoints Csq
    HT Hnu HI HR Hnorm p.
  pose proof (critical_cap_nonnegative_from_injection T nu lambda a Dcum Ccum
    X0 Seed Paid HT HI) as HK.
  assert (HDcap : 0 <= critical_cap X0 Seed Paid / nu).
  { unfold Rdiv. apply Rmult_le_pos; [exact HK|left; apply Rinv_0_lt_compat; exact Hnu]. }
  assert (HX : forall p : A.OpenTime T,
      Xinf (proj1_sig p) <= critical_cap X0 Seed Paid).
  { intro p'. exact (proj2 (proj1 (BKMS10_COMPLETED_TOTALS_BOUNDED
      T nu lambda a Dcum Ccum X0 Seed Paid Xinf Dinf HI HR
      (proj1_sig p') (proj2_sig p')))). }
  assert (HD : forall p : A.OpenTime T,
      Dinf (proj1_sig p) <= critical_cap X0 Seed Paid / nu).
  { intro p'. exact (proj2 (proj2 (BKMS10_COMPLETED_TOTALS_BOUNDED
      T nu lambda a Dcum Ccum X0 Seed Paid Xinf Dinf HI HR
      (proj1_sig p') (proj2_sig p')))). }
  pose proof (NS.NSR22_EXPLICIT_INTEGRATED_SERRIN46_BOUND (A.OpenTime T)
    endpoints (fun p => Xinf (proj1_sig p)) (fun p => Dinf (proj1_sig p))
    Csq (critical_cap X0 Seed Paid) (critical_cap X0 Seed Paid / nu)
    Hnorm HK HDcap HX HD p) as Hbound.
  unfold serrin_budget.
  replace (Csq * Csq * critical_cap X0 Seed Paid ^ 2 / nu)
    with (Csq * Csq * critical_cap X0 Seed Paid *
      (critical_cap X0 Seed Paid / nu)) by (unfold Rdiv; ring).
  exact Hbound.
Qed.

Theorem BKMS31_INJECTION_TO_UNIFORM_SERRIN_OBSERVABLE :
  forall T nu lambda a Dcum Ccum X0 Seed Paid Xinf Dinf endpoints Csq,
  0 < T -> 0 < nu ->
  I.SamePathM7Injection T nu lambda a Dcum Ccum X0 Seed Paid ->
  CountableCriticalReadout T lambda a Dcum Xinf Dinf ->
  SerrinNormBinding T endpoints Xinf Dinf Csq ->
  SH.UniformAction (A.OpenTime T)
    (fun p => NS.serrin46_observation (endpoints p)).
Proof.
  intros T nu lambda a Dcum Ccum X0 Seed Paid Xinf Dinf endpoints Csq
    HT Hnu HI HR Hnorm.
  exists (serrin_budget Csq nu X0 Seed Paid). split.
  - unfold serrin_budget, Rdiv. apply Rmult_le_pos.
    + apply Rmult_le_pos; nra.
    + left. apply Rinv_0_lt_compat. exact Hnu.
  - exact (BKMS30_INJECTION_TO_SERRIN_OBSERVABLE T nu lambda a Dcum Ccum
      X0 Seed Paid Xinf Dinf endpoints Csq HT Hnu HI HR Hnorm).
Qed.

(* A stronger optional entrance pins the endpoint intervals and all four
   scalar measurements to the same path. The measurement functions are
   explicit inputs: proving that they are physical Sobolev/L6 norms is
   not hidden in the names of these fields. Integrability is retained on
   the donor's explicit integral domain. *)
Record SamePathNormReadouts hd (u : R -> HCarrier hd) T
    (endpoints : A.OpenTime T -> NS.NormEndpoint)
    (h12 h32 h1 l6 : HCarrier hd -> R) : Prop := {
  same_path_endpoint_geometry : forall p,
    NS.ne_t0 (endpoints p) = 0 /\ NS.ne_t1 (endpoints p) = proj1_sig p;
  same_path_endpoint_values : forall p t, 0 <= t <= proj1_sig p ->
    NS.ne_h12_sq (endpoints p) t = h12 (u t) /\
    NS.ne_h32_sq (endpoints p) t = h32 (u t) /\
    NS.ne_h1_sq (endpoints p) t = h1 (u t) /\
    NS.ne_l6_sq (endpoints p) t = l6 (u t)
}.

Theorem BKMS40_SAME_PATH_READOUTS_GIVE_NORM_BINDING :
  forall hd (u : R -> HCarrier hd) T endpoints h12 h32 h1 l6 Xinf Dinf Csq,
  SamePathNormReadouts hd u T endpoints h12 h32 h1 l6 ->
  0 <= Csq ->
  (forall t, M.OpenTime T t ->
    0 <= h12 (u t) /\ 0 <= h32 (u t) /\
    0 <= h1 (u t) /\ 0 <= l6 (u t) /\
    h1 (u t) * h1 (u t) <= h12 (u t) * h32 (u t) /\
    l6 (u t) <= Csq * h1 (u t)) ->
  (forall t, M.OpenTime T t -> Xinf t = h12 (u t)) ->
  (forall p, SH.integrable (NS.ne_integral (endpoints p))
    (NS.ne_h32_sq (endpoints p))) ->
  (forall p, SH.integrable (NS.ne_integral (endpoints p))
    (fun t => NS.ne_l6_sq (endpoints p) t * NS.ne_l6_sq (endpoints p) t)) ->
  (forall p, SH.integral (NS.ne_integral (endpoints p))
    (NS.ne_h32_sq (endpoints p)) <= Dinf (proj1_sig p)) ->
  SerrinNormBinding T endpoints Xinf Dinf Csq.
Proof.
  intros hd u T endpoints h12 h32 h1 l6 Xinf Dinf Csq
    [Hgeometry Hvalues] HCsq Hpoint Hmass HintD HintL Hdiss.
  assert (Hopen : forall p : A.OpenTime T, forall t,
      0 <= t <= proj1_sig p -> M.OpenTime T t).
  { intros p t Ht. destruct p as [s Hs]. simpl in Ht.
    unfold M.OpenTime. lra. }
  constructor.
  - exact HCsq.
  - exact HintD.
  - exact HintL.
  - intros p t Ht. destruct (Hgeometry p) as [H0 H1].
    rewrite H0, H1 in Ht.
    destruct (Hvalues p t Ht) as [He [Hd [Hh Hl]]].
    rewrite He, Hd, Hh, Hl. apply Hpoint. exact (Hopen p t Ht).
  - intros p t Ht. destruct (Hgeometry p) as [H0 H1].
    rewrite H0, H1 in Ht.
    pose proof (Hopen p t Ht) as Htopen.
    exists (exist (fun r => 0 <= r < T) t Htopen). simpl.
    rewrite (proj1 (Hvalues p t Ht)), (Hmass t Htopen). lra.
  - exact Hdiss.
Qed.

(* The final contract refers to the SAME Hilbert-valued path u whose
   coordinates generated the M7 action. It is deliberately not an
   assertion that an arbitrary NormEndpoint is already a physical norm,
   nor a new proof of the physical Prodi--Serrin continuation theorem. *)
Theorem BKMS50_SAME_PATH_SERRIN_CONTINUATION :
  forall hd (basis : OrthonormalBasis hd) (u : R -> HCarrier hd)
    T nu lambda Dcum Ccum X0 Seed Paid Xinf Dinf endpoints Csq
    (ActualSerrin46 Continues : (R -> HCarrier hd) -> Prop),
  0 < T -> 0 < nu ->
  I.SamePathM7Injection T nu lambda (I.same_coordinates hd basis u)
    Dcum Ccum X0 Seed Paid ->
  CountableCriticalReadout T lambda (I.same_coordinates hd basis u)
    Dcum Xinf Dinf ->
  SerrinNormBinding T endpoints Xinf Dinf Csq ->
  EX.SerrinExitContract (R -> HCarrier hd) (A.OpenTime T) u
    (fun p => NS.serrin46_observation (endpoints p)) ActualSerrin46 Continues ->
  ActualSerrin46 u /\ Continues u.
Proof.
  intros hd basis u T nu lambda Dcum Ccum X0 Seed Paid Xinf Dinf endpoints Csq
    ActualSerrin46 Continues HT Hnu HI HR Hnorm Hexit.
  apply (EX.NSR80_OBSERVABLE_AND_EXPLICIT_SERRIN_EXIT
    (R -> HCarrier hd) (A.OpenTime T) u
    (fun p => NS.serrin46_observation (endpoints p))
    ActualSerrin46 Continues Hexit).
  exact (BKMS31_INJECTION_TO_UNIFORM_SERRIN_OBSERVABLE T nu lambda
    (I.same_coordinates hd basis u) Dcum Ccum X0 Seed Paid Xinf Dinf
    endpoints Csq HT Hnu HI HR Hnorm).
Qed.

Print Assumptions BKMS11_CANONICAL_COUNTABLE_READOUT.
Print Assumptions BKMS30_INJECTION_TO_SERRIN_OBSERVABLE.
Print Assumptions BKMS40_SAME_PATH_READOUTS_GIVE_NORM_BINDING.
Print Assumptions BKMS50_SAME_PATH_SERRIN_CONTINUATION.

End BKQR_M7_SERRIN_BRIDGE.
