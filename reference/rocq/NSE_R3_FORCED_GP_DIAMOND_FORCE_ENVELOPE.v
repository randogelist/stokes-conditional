From Stdlib Require Import Reals Lra Psatz String List.
Require Import NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.
Require Import NSE_R3_FORCED_GP_DIAMOND_SEPARATRIX.

Import ListNotations.

Module NSE_R3_FORCED_GP_DIAMOND_FORCE_ENVELOPE.

Module FC := NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.NSE_R3_FORCED_GP_DIAMOND_CRITICAL_CLASSES.

Open Scope R_scope.

Definition sq (x : R) : R := x * x.

Fixpoint sumR (xs : list R) : R :=
  match xs with
  | nil => 0
  | x :: tl => x + sumR tl
  end.

(* Exact critical dual coefficient.  The witness is the Riesz-aligned
   critical direction.  This is the algebraic core behind the H^{-1/2}
   forcing norm. *)
Section CRITICAL_DUAL.

Variable Force State : Type.
Variable force_size2 : Force -> R.
Variable critical_dissipation : State -> R.
Variable critical_work : Force -> State -> R.
Variable riesz_state : Force -> State.

Record CriticalDualGeometry : Prop := {
  cdg_force_size_nonnegative :
    forall f : Force, 0 <= force_size2 f;
  cdg_dissipation_nonnegative :
    forall u : State, 0 <= critical_dissipation u;
  cdg_cauchy_bound :
    forall (f : Force) (u : State),
      sq (critical_work f u)
      <= force_size2 f * critical_dissipation u;
  cdg_riesz_dissipation :
    forall f : Force,
      critical_dissipation (riesz_state f) = force_size2 f;
  cdg_riesz_work :
    forall f : Force,
      critical_work f (riesz_state f) = force_size2 f
}.

Definition UniformWorkCoefficient (f : Force) (C : R) : Prop :=
  0 <= C /\
  forall u : State,
    sq (critical_work f u) <= C * critical_dissipation u.

Theorem FE01_FORCE_SIZE_IS_A_UNIFORM_WORK_COEFFICIENT :
  CriticalDualGeometry ->
  forall f : Force,
    UniformWorkCoefficient f (force_size2 f).
Proof.
  intros Hgeo f.
  destruct Hgeo as [Hsize Hdiss Hcs Hwd Hww].
  split.
  - exact (Hsize f).
  - intro u. exact (Hcs f u).
Qed.

Theorem FE02_FORCE_SIZE_IS_LEAST_UNIFORM_WORK_COEFFICIENT :
  CriticalDualGeometry ->
  forall (f : Force) (C : R),
    UniformWorkCoefficient f C ->
    force_size2 f <= C.
Proof.
  intros Hgeo f C HC.
  destruct Hgeo as [Hsize Hdiss Hcs Hwd Hww].
  destruct HC as [HC0 HC].
  pose proof (Hsize f) as Hs.
  specialize (HC (riesz_state f)).
  rewrite (Hww f), (Hwd f) in HC.
  unfold sq in HC.
  nra.
Qed.

Theorem FE03_FORCE_SIZE_EXACTLY_CLASSIFIES_UNIFORM_CRITICAL_WORK :
  CriticalDualGeometry ->
  forall f : Force,
    UniformWorkCoefficient f (force_size2 f) /\
    forall C : R,
      UniformWorkCoefficient f C -> force_size2 f <= C.
Proof.
  intro Hgeo.
  intro f.
  split.
  - apply FE01_FORCE_SIZE_IS_A_UNIFORM_WORK_COEFFICIENT.
    exact Hgeo.
  - intros C HC.
    eapply FE02_FORCE_SIZE_IS_LEAST_UNIFORM_WORK_COEFFICIENT.
    + exact Hgeo.
    + exact HC.
Qed.

End CRITICAL_DUAL.

(* Finite BKQR windows.  Each channel has its own critical dual geometry;
   the tight-frame identity says the sum of the channel least coefficients
   is the global critical dual coefficient. *)
Section BKQR_FRAME.

Variable Channel Force State : Type.
Variable channels : list Channel.
Variable global_force_size2 : Force -> R.
Variable channel_force_size2 : Channel -> Force -> R.
Variable channel_dissipation : Channel -> State -> R.
Variable channel_work : Channel -> Force -> State -> R.
Variable channel_riesz_state : Channel -> Force -> State.

Record BKQRTightForceFrame : Prop := {
  bft_global_nonnegative :
    forall f : Force, 0 <= global_force_size2 f;
  bft_channel_nonnegative :
    forall (q : Channel) (f : Force), 0 <= channel_force_size2 q f;
  bft_dissipation_nonnegative :
    forall (q : Channel) (u : State), 0 <= channel_dissipation q u;
  bft_channel_cauchy :
    forall (q : Channel) (f : Force) (u : State),
      sq (channel_work q f u)
      <= channel_force_size2 q f * channel_dissipation q u;
  bft_channel_riesz_dissipation :
    forall (q : Channel) (f : Force),
      channel_dissipation q (channel_riesz_state q f)
      = channel_force_size2 q f;
  bft_channel_riesz_work :
    forall (q : Channel) (f : Force),
      channel_work q f (channel_riesz_state q f)
      = channel_force_size2 q f;
  bft_tight_frame :
    forall f : Force,
      global_force_size2 f
      = sumR (map (fun q => channel_force_size2 q f) channels)
}.

Definition ChannelUniformWorkCoefficient
  (q : Channel) (f : Force) (C : R) : Prop :=
  0 <= C /\
  forall u : State,
    sq (channel_work q f u) <= C * channel_dissipation q u.

Definition universal_bkqr_force_envelope (f : Force) : R :=
  sumR (map (fun q => channel_force_size2 q f) channels).

Definition normalized_force_action (w d : R) : R :=
  if Rlt_dec 0 d then sq w / d else 0.

Definition trajectory_bkqr_force_action (f : Force) (u : State) : R :=
  sumR
    (map
      (fun q => normalized_force_action
        (channel_work q f u)
        (channel_dissipation q u))
      channels).

Lemma sumR_map_le :
  forall (qs : list Channel) (a b : Channel -> R),
    (forall q : Channel, In q qs -> a q <= b q) ->
    sumR (map a qs) <= sumR (map b qs).
Proof.
  intros qs.
  induction qs as [|q tl IH].
  - intros a b H. simpl. lra.
  - intros a b H.
    simpl.
    assert (Hq : a q <= b q).
    { apply H. simpl. left. reflexivity. }
    assert (Htl : sumR (map a tl) <= sumR (map b tl)).
    {
      apply IH.
      intros q' HIn.
      apply H.
      simpl. right. exact HIn.
    }
    lra.
Qed.

Theorem FE10_CHANNEL_SIZE_IS_LEAST_UNIFORM_COEFFICIENT :
  BKQRTightForceFrame ->
  forall (q : Channel) (f : Force),
    ChannelUniformWorkCoefficient q f (channel_force_size2 q f) /\
    forall C : R,
      ChannelUniformWorkCoefficient q f C ->
      channel_force_size2 q f <= C.
Proof.
  intros Hframe q f.
  destruct Hframe as [Hg Hcn Hd Hcs Hwd Hww Htight].
  split.
  - split.
    + exact (Hcn q f).
    + intro u. exact (Hcs q f u).
  - intros C [HC0 HC].
    pose proof (Hcn q f) as Hsize.
    specialize (HC (channel_riesz_state q f)).
    rewrite (Hww q f), (Hwd q f) in HC.
    unfold sq in HC.
    nra.
Qed.

Theorem FE11_UNIVERSAL_BKQR_ENVELOPE_EQUALS_GLOBAL_CRITICAL_SIZE :
  BKQRTightForceFrame ->
  forall f : Force,
    universal_bkqr_force_envelope f = global_force_size2 f.
Proof.
  intros Hframe f.
  destruct Hframe as [Hg Hcn Hd Hcs Hwd Hww Htight].
  unfold universal_bkqr_force_envelope.
  symmetry.
  exact (Htight f).
Qed.

Theorem FE12_SINGLE_CHANNEL_TRAJECTORY_ACTION_LE_CHANNEL_ENVELOPE :
  BKQRTightForceFrame ->
  forall (q : Channel) (f : Force) (u : State),
    normalized_force_action
      (channel_work q f u)
      (channel_dissipation q u)
    <= channel_force_size2 q f.
Proof.
  intros Hframe q f u.
  destruct Hframe as [Hg Hcn Hd Hcs Hwd Hww Htight].
  pose proof (Hcn q f) as Hsize.
  pose proof (Hd q u) as Hd0.
  pose proof (Hcs q f u) as Hbound.
  unfold normalized_force_action.
  destruct (Rlt_dec 0 (channel_dissipation q u)) as [Hdpos|Hdnot].
  - assert (Hdne : channel_dissipation q u <> 0) by lra.
    apply (Rmult_le_reg_l (channel_dissipation q u)).
    + exact Hdpos.
    + replace
        (channel_dissipation q u *
          (sq (channel_work q f u) / channel_dissipation q u))
        with (sq (channel_work q f u)).
      * replace
          (channel_dissipation q u * channel_force_size2 q f)
          with (channel_force_size2 q f * channel_dissipation q u) by ring.
        exact Hbound.
      * unfold Rdiv.
        rewrite <- Rmult_assoc.
        rewrite (Rmult_comm (channel_dissipation q u)
          (sq (channel_work q f u))).
        rewrite Rmult_assoc.
        rewrite (Rinv_r (channel_dissipation q u) Hdne).
        ring.
  - exact Hsize.
Qed.

Theorem FE13_TRAJECTORY_BKQR_ACTION_LE_UNIVERSAL_ENVELOPE :
  BKQRTightForceFrame ->
  forall (f : Force) (u : State),
    trajectory_bkqr_force_action f u
    <= universal_bkqr_force_envelope f.
Proof.
  intros Hframe f u.
  unfold trajectory_bkqr_force_action, universal_bkqr_force_envelope.
  apply sumR_map_le.
  intros q HIn.
  apply FE12_SINGLE_CHANNEL_TRAJECTORY_ACTION_LE_CHANNEL_ENVELOPE.
  exact Hframe.
Qed.

Theorem FE14_TRAJECTORY_BKQR_ACTION_LE_GLOBAL_CRITICAL_SIZE :
  BKQRTightForceFrame ->
  forall (f : Force) (u : State),
    trajectory_bkqr_force_action f u <= global_force_size2 f.
Proof.
  intros Hframe f u.
  pose proof (FE13_TRAJECTORY_BKQR_ACTION_LE_UNIVERSAL_ENVELOPE
    Hframe f u) as Hact.
  pose proof (FE11_UNIVERSAL_BKQR_ENVELOPE_EQUALS_GLOBAL_CRITICAL_SIZE
    Hframe f) as Heq.
  rewrite Heq in Hact.
  exact Hact.
Qed.

End BKQR_FRAME.

(* Cumulative ledgers: any physical external ledger dominated by the
   cumulative critical-force envelope inherits boundedness from it. *)
Section CUMULATIVE_LEDGER.

Variable Time : Type.
Variable physical_force_ledger critical_force_envelope : Time -> R.

Definition EnvelopeDominatesPhysicalLedger : Prop :=
  forall t : Time, physical_force_ledger t <= critical_force_envelope t.

Theorem FE20_BOUNDED_FORCE_ENVELOPE_GIVES_BOUNDED_PHYSICAL_LEDGER :
  EnvelopeDominatesPhysicalLedger ->
  FC.BoundedLedger
    Time critical_force_envelope ->
  FC.BoundedLedger
    Time physical_force_ledger.
Proof.
  intros Hdom [Cmax [HC0 HC]].
  exists Cmax.
  split.
  - exact HC0.
  - intro t.
    specialize (Hdom t).
    specialize (HC t).
    lra.
Qed.

End CUMULATIVE_LEDGER.

Definition STATUS : string :=
  "NSE_R3_FORCED_GP_DIAMOND_FORCE_ENVELOPE_V0_11_1"%string.

End NSE_R3_FORCED_GP_DIAMOND_FORCE_ENVELOPE.
