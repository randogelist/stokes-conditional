(* Forward containment in the intrinsic countable BKQR shell range.
   The source and target are independently stated. The target uses actual
   shell pairings and literal native coefficient readouts. Its gradient
   remains the supplied variational gradient; it is not silently replaced
   by a diagonal spectral multiplier. TimeData and the initial-time energy
   schedule are preserved. No spatial domain is identified here. *)
From Stdlib Require Import Reals Lra Psatz Field.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport LHGP_Hilbert.
Require Import LHGP_Realization LHGP_WeakTopology LHGP_PathSynthesis.
Require Import LHGP_Evolution LHGP_ForwardGradient LHGP_InitialEnergy.
Require Import LHGP_ForwardContainment LHGP_Completion070.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_PathTopology.
Require Import BKQR_ClassificationAudit BKQR_LHGP_CoordinateBridge.
Require Import BKQR_LHGP_EvolutionBridge.

Module BKQR_LHGP_FORWARD_BRIDGE.
Module B := GP_COUNTABLE_RANGE.
Module S := BKQR_SHELL_COORDINATES.
Module P := BKQR_PATH_TOPOLOGY.
Module C := BKQR_CLASSIFICATION.
Module CB := BKQR_LHGP_COORDINATE_BRIDGE.
Module EB := BKQR_LHGP_EVOLUTION_BRIDGE.
Open Scope R_scope.

Definition NativeForwardDissipationUpper hd kd (basis : OrthonormalBasis hd)
    (fg : ForwardGradientData hd kd) (psi U : nat -> nat -> R) (M : R) : Prop :=
  forall z r,
    EB.native_linear_limit psi U (HAnalysis basis (FGDiv hd kd fg z)) r ->
    -2 * r - HNorm kd (FGEmbed hd kd fg z) <= M.

Definition NativeForwardDissipationValue hd kd (basis : OrthonormalBasis hd)
    (fg : ForwardGradientData hd kd) (psi U : nat -> nat -> R) (D : R) : Prop :=
  NativeForwardDissipationUpper hd kd basis fg psi U D /\
  forall M, NativeForwardDissipationUpper hd kd basis fg psi U M -> D <= M.

Definition NativeForwardEnergyLedger hd kd (basis : OrthonormalBasis hd)
    (fg : ForwardGradientData hd kd) (td : TimeData) (nu T : R)
    (psi : nat -> nat -> R) (U : R -> nat -> nat -> R) : Prop :=
  exists (E D : R -> R) (GoodD : R -> Prop),
    EnergySchedule0 td nu T E D GoodD /\
    (forall t, B.ShellTotal (U t) (E t)) /\
    (forall t, 0 <= t <= T -> GoodD t ->
      NativeForwardDissipationValue hd kd basis fg psi (U t) (D t)).

Definition NativeForwardLHModel hd kd (basis : OrthonormalBasis hd)
    (fg : ForwardGradientData hd kd) (tests : EvolutionTests hd)
    (td : TimeData) (nu T : R) (psi : nat -> nat -> R)
    (lambda ell : nat -> R) (U : R -> nat -> nat -> R)
    (U0 : nat -> nat -> R) : Prop :=
  0 < nu /\ 0 < T /\
  (forall t, S.IntrinsicState lambda ell (U t)) /\
  (forall k i, U 0 k i = U0 k i) /\
  P.ShellWeakContinuousOn (fun t => 0 <= t <= T) lambda ell U /\
  (exists M, forall t, 0 <= t <= T -> B.ShellBound (U t) M) /\
  EB.NativeWeakForm hd basis tests td nu T psi U U0 /\
  NativeForwardEnergyLedger hd kd basis fg td nu T psi U.

Definition HilbertShellEncode hd (basis : OrthonormalBasis hd)
    (psi : nat -> nat -> R) (x : HCarrier hd) : nat -> nat -> R :=
  B.gp_encode psi (HAnalysis basis x).

Theorem BKLF01_HILBERT_SHELL_ENERGY : forall hd (basis : OrthonormalBasis hd),
  HComplete hd -> forall psi, B.ScalarPartition psi -> forall x,
  B.ShellTotal (HilbertShellEncode hd basis psi x) (HNorm hd x).
Proof.
  intros hd basis HC psi HP x.
  apply (proj1 (B.GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY psi
    (HAnalysis basis x) (HilbertShellEncode hd basis psi x) HP
    (fun k i => eq_refl) (HNorm hd x))).
  apply (proj1 (CB.ENERGY_VALUE_BRIDGE _ _)).
  apply HAnalysis_parseval. exact HC.
Qed.

Theorem BKLF02_HILBERT_SHELL_INTRINSIC : forall hd (basis : OrthonormalBasis hd)
    psi lambda ell,
  B.ScalarPartition psi -> S.ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) -> forall x,
  S.IntrinsicState lambda ell (HilbertShellEncode hd basis psi x).
Proof.
  intros hd basis psi lambda ell HP HR H0 HE x.
  apply (proj2 (S.BKSC11_EXACT_INTRINSIC_RANGE psi lambda ell HP HR H0 HE _)).
  exists (HAnalysis basis x). split.
  - apply (proj1 (CB.COORDINATE_L2_BRIDGE _)). apply HAnalysis_L2.
  - intros k i. reflexivity.
Qed.

Theorem BKLF03_HILBERT_SHELL_INJECTIVE : forall hd (basis : OrthonormalBasis hd)
    psi, (forall i, psi 0%nat i <> 0) -> forall x y,
  (forall k i, HilbertShellEncode hd basis psi x k i =
    HilbertShellEncode hd basis psi y k i) -> x = y.
Proof.
  intros hd basis psi H0 x y Heq. apply (HAnalysis_injective hd basis).
  intro i. apply (Rmult_eq_reg_l (psi 0%nat i)); [apply Heq|apply H0].
Qed.

Theorem BKLF04_HILBERT_SHELL_TRAJECTORY_INJECTIVE :
  forall hd (basis : OrthonormalBasis hd) psi,
  (forall i, psi 0%nat i <> 0) -> forall (u v : R -> HCarrier hd),
  (forall t k i, HilbertShellEncode hd basis psi (u t) k i =
    HilbertShellEncode hd basis psi (v t) k i) -> forall t, u t = v t.
Proof. intros hd basis psi H0 u v Heq t. eapply BKLF03_HILBERT_SHELL_INJECTIVE;
  [exact H0|apply Heq]. Qed.

Theorem BKLF10_HILBERT_SHELL_WEAK_CONTINUITY :
  forall hd (basis : OrthonormalBasis hd) psi lambda ell T u M,
  B.ScalarPartition psi -> S.ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  HWeakContinuous hd u T ->
  (forall t, 0 <= t <= T -> HNorm hd (u t) <= M) ->
  P.ShellWeakContinuousOn (fun t => 0 <= t <= T) lambda ell
    (fun t => HilbertShellEncode hd basis psi (u t)).
Proof.
  intros hd basis psi lambda ell T u M HP HR H0 HE HC HM.
  assert (HI : forall t, 0 <= t <= T ->
    S.IntrinsicState lambda ell (HilbertShellEncode hd basis psi (u t))).
  { intros t Ht. apply BKLF02_HILBERT_SHELL_INTRINSIC; assumption. }
  assert (HB : forall t, 0 <= t <= T ->
    B.ShellBound (HilbertShellEncode hd basis psi (u t)) M).
  { intros t Ht. apply (proj1 (B.GPR40_PARTITION_PRESERVES_ALL_ENERGY_BOUNDS
      psi HP (HAnalysis basis (u t)) M)).
    intro N. rewrite <- CB.ENERGY_PREFIX_BRIDGE.
    eapply Rle_trans; [apply HAnalysis_bessel|apply HM; exact Ht]. }
  apply (proj2 (P.BKPT33_BOUNDED_NATIVE_WEAK_CONTINUITY_IFF_SHELL_COORDINATES
    psi lambda ell (fun t => 0 <= t <= T)
    (fun t => HilbertShellEncode hd basis psi (u t)) M HP HR H0 HE HI HB)).
  intros k i. unfold HilbertShellEncode, B.gp_encode.
  apply (P.scalar_continuous_ext_on (fun t => 0 <= t <= T)
    (fun t => HAnalysis basis (u t) i * psi k i)).
  - intros t Ht. ring.
  - apply P.scalar_continuous_scale.
    exact (HWeakContinuous_to_coordinates hd basis u T HC i).
Qed.

Theorem BKLF11_NATIVE_DISSIPATION_EXACT : forall hd kd basis fg psi U D,
  NativeForwardDissipationValue hd kd basis fg psi U D <->
  ForwardGPDissipationValue hd kd basis fg (psi 0%nat) (U 0%nat) D.
Proof.
  intros hd kd basis fg psi U D.
  assert (HU : forall M,
    NativeForwardDissipationUpper hd kd basis fg psi U M <->
    ForwardGPDissipationUpper hd kd basis fg (psi 0%nat) (U 0%nat) M).
  { intro M. split; intros H z r Hr; apply (H z r).
    - apply (proj2 (EB.BKLE03_NATIVE_LINEAR_LIMIT _ _ _ _)). exact Hr.
    - apply (proj1 (EB.BKLE03_NATIVE_LINEAR_LIMIT _ _ _ _)). exact Hr. }
  split; intros [HD Hleast]; split.
  - apply (proj1 (HU D)). exact HD.
  - intros M HM. apply Hleast. apply (proj2 (HU M)). exact HM.
  - apply (proj2 (HU D)). exact HD.
  - intros M HM. apply Hleast. apply (proj1 (HU M)). exact HM.
Qed.

Theorem BKLF12_KNOWN_GRADIENT_NATIVE_VALUE :
  forall hd kd (basis : OrthonormalBasis hd), HComplete hd ->
  forall fg psi x D,
  (forall i, psi 0%nat i <> 0) ->
  ForwardGradientEnergyAt hd kd fg x D ->
  NativeForwardDissipationValue hd kd basis fg psi
    (HilbertShellEncode hd basis psi x) D.
Proof.
  intros hd kd basis HC fg psi x D H0 HG.
  apply (proj2 (BKLF11_NATIVE_DISSIPATION_EXACT _ _ _ _ _ _ _)).
  eapply (FORWARD_GRADIENT_ENERGY_TO_GP_VALUE hd kd basis HC fg
    (psi 0%nat) x _ D).
  - exact H0.
  - intro i. reflexivity.
  - exact HG.
Qed.

Theorem BKLF20_HILBERT_FORWARD_CONTAINMENT :
  forall hd kd (basis : OrthonormalBasis hd), HComplete hd ->
  forall psi lambda ell,
  B.ScalarPartition psi -> S.ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  forall fg tests td nu T u u0,
  HilbertForwardLHModel hd kd fg tests td nu T u u0 ->
  NativeForwardLHModel hd kd basis fg tests td nu T psi lambda ell
    (fun t => HilbertShellEncode hd basis psi (u t))
    (HilbertShellEncode hd basis psi u0).
Proof.
  intros hd kd basis HC psi lambda ell HP HR H0 HE fg tests td nu T u u0
    [Hnu [HT [Hinitial [Hweak [[M HM] [HW Hledger]]]]]].
  split; [exact Hnu|]. split; [exact HT|]. split.
  - intro t. apply BKLF02_HILBERT_SHELL_INTRINSIC; assumption.
  - split.
    + intros k i. rewrite Hinitial. reflexivity.
    + split.
      * eapply BKLF10_HILBERT_SHELL_WEAK_CONTINUITY; eassumption.
      * split.
        -- exists M. intros t Ht.
           pose proof (BKLF01_HILBERT_SHELL_ENERGY hd basis HC psi HP (u t))
             as [HB Hleast].
           intros K N. eapply Rle_trans; [apply HB|apply HM; exact Ht].
        -- split.
           ++ apply (proj1 (EB.BKLE30_HILBERT_NATIVE_WEAK_FORM_EXACT hd basis HC
                tests td nu T psi
                (fun t => HilbertShellEncode hd basis psi (u t))
                (HilbertShellEncode hd basis psi u0) u u0 H0
                (fun t i => eq_refl) (fun i => eq_refl))). exact HW.
           ++ destruct Hledger as [E [D [GoodD [HS [HEnergy HD]]]]].
              exists E, D, GoodD. split; [exact HS|]. split.
              ** intro t. rewrite HEnergy.
                 apply BKLF01_HILBERT_SHELL_ENERGY; assumption.
              ** intros t Ht Hgood. apply BKLF12_KNOWN_GRADIENT_NATIVE_VALUE;
                   try assumption. apply HD; assumption.
Qed.

(* The shell profile below is the already constructed countable BKQR
   q-profile: its partition and raising laws are proved in the old branch.
   lambda merely chooses this representation profile. It is not asserted
   to diagonalize the independent gradient data or the evolution tests. *)
Theorem BKLF30_CANONICAL_HILBERT_FORWARD_CONTAINMENT :
  forall q step lambda (Hq : 0 < q < 1) (Hstep : 0 < step),
  (forall i, 0 <= lambda i) ->
  forall hd kd (basis : OrthonormalBasis hd), HComplete hd ->
  forall fg tests td nu T u u0,
  HilbertForwardLHModel hd kd fg tests td nu T u u0 ->
  NativeForwardLHModel hd kd basis fg tests td nu T
    (C.bkqr_weights q step lambda Hq Hstep) lambda (C.bkqr_ell q step)
    (fun t => HilbertShellEncode hd basis
      (C.bkqr_weights q step lambda Hq Hstep) (u t))
    (HilbertShellEncode hd basis (C.bkqr_weights q step lambda Hq Hstep) u0).
Proof.
  intros q step lambda Hq Hstep Hlambda hd kd basis HC fg tests td nu T u u0 Hu.
  apply BKLF20_HILBERT_FORWARD_CONTAINMENT.
  - exact HC.
  - apply C.BKCL01_SCALAR_PARTITION.
  - apply C.BKCL04_SCALAR_RAISING. exact Hlambda.
  - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
  - apply C.BKCL03_ELL_NONZERO; assumption.
  - exact Hu.
Qed.

Section ExactCanonicalForwardModels.
Variables q step : R.
Variable lambda : nat -> R.
Hypothesis Hq : 0 < q < 1.
Hypothesis Hstep : 0 < step.
Hypothesis Hlambda : forall i, 0 <= lambda i.
Let psi := C.bkqr_weights q step lambda Hq Hstep.
Let ell := C.bkqr_ell q step.

Theorem BKLF40_CANONICAL_ENERGY_LEDGERS_EXACT :
  forall hd kd basis fg td nu T U,
  (forall t, C.BKQRCompatible q step lambda (U t)) ->
  (NativeForwardEnergyLedger hd kd basis fg td nu T psi U <->
   GPForwardEnergyLedger hd kd basis fg td nu T (psi 0%nat)
     (fun t => U t 0%nat)).
Proof.
  intros hd kd basis fg td nu T U Hcomp.
  split; intros [E [D [GoodD [HS [HE HD]]]]];
    exists E, D, GoodD; split; [exact HS| |exact HS|]; split.
  - intro t. apply (proj2 (CB.CANONICAL_ZERO_ROW_ENERGY_IS_FULL_SHELL_ENERGY
      q step lambda Hq Hstep Hlambda (U t) (Hcomp t) (E t))). apply HE.
  - intros t Ht Hgood.
    apply (proj1 (BKLF11_NATIVE_DISSIPATION_EXACT _ _ _ _ _ _ _)).
    apply HD; assumption.
  - intro t. apply (proj1 (CB.CANONICAL_ZERO_ROW_ENERGY_IS_FULL_SHELL_ENERGY
      q step lambda Hq Hstep Hlambda (U t) (Hcomp t) (E t))). apply HE.
  - intros t Ht Hgood.
    apply (proj2 (BKLF11_NATIVE_DISSIPATION_EXACT _ _ _ _ _ _ _)).
    apply HD; assumption.
Qed.

(* This equivalence compares the same coefficient path. Its hypothesis is
   intrinsic BKQR adjacency, not existence of a represented trajectory.
   Zeroth-row initial equality then determines every initial shell.
   Both continuity interfaces here are relative to [0,T]; neither is the
   two-sided continuity_pt interface used by the separate time-integral
   branch. No physical torus/R3 or time-integration identification occurs. *)
Theorem BKLF50_CANONICAL_FORWARD_MODELS_EXACT :
  forall hd kd basis fg tests td nu T U U0,
  (forall t, C.BKQRCompatible q step lambda (U t)) ->
  C.BKQRCompatible q step lambda U0 ->
  (NativeForwardLHModel hd kd basis fg tests td nu T psi lambda ell U U0 <->
   GPForwardLHModel hd kd basis fg tests td nu T (psi 0%nat)
     (fun t => U t 0%nat) (U0 0%nat)).
Proof.
  intros hd kd basis fg tests td nu T U U0 Hcomp Hcomp0.
  assert (HP : B.ScalarPartition psi) by apply C.BKCL01_SCALAR_PARTITION.
  assert (HR : S.ScalarRaising psi lambda ell).
  { apply C.BKCL04_SCALAR_RAISING. exact Hlambda. }
  assert (H0 : forall i, psi 0%nat i <> 0) by apply C.BKCL02_ZERO_WEIGHT_NONZERO.
  assert (HE : forall k, ell k <> 0).
  { apply C.BKCL03_ELL_NONZERO; assumption. }
  assert (HA : forall t, S.AdjacentCompatible lambda ell (U t)).
  { intro t. apply (proj1 (C.BKCL05_ADJACENCY_EQUIVALENCE q step lambda
      Hq Hstep (U t))). apply Hcomp. }
  split.
  - intros [Hnu [HT [HI [Hinitial [HW [[M HM] [Hform Hledger]]]]]]].
    split; [exact Hnu|]. split; [exact HT|]. split.
    + intro t. apply (proj2 (CB.CANONICAL_ZERO_ROW_L2_IFF_FULL_SHELL_L2
        q step lambda Hq Hstep Hlambda (U t) (Hcomp t))).
      exact (proj2 (HI t)).
    + split.
      * intro i. apply Hinitial.
      * split.
        -- assert (Hphysical : forall t, 0 <= t <= T ->
             B.PhysicalBound (S.reconstruct psi (U t)) M).
           { intros t Ht. apply (proj2 (S.BKSC10_RECONSTRUCTION_PRESERVES_ALL_BOUNDS
               psi lambda ell (U t) HP HR H0 HE (HA t) M)). apply HM. exact Ht. }
           pose proof (proj1 (P.BKPT32_WEAK_CONTINUITY_TRANSPORT psi lambda ell
             (fun t => 0 <= t <= T) U HP HR H0 HE (fun t _ => HI t)) HW) as HWp.
           exact (proj1 (P.BKPT20_BOUNDED_WEAK_CONTINUITY_IFF_COORDINATES
             (fun t => 0 <= t <= T) (fun t => S.reconstruct psi (U t)) M
             Hphysical) HWp).
        -- split.
           ++ exists M. apply (proj2 (CB.CANONICAL_PATH_UNIFORM_ENERGY_EXACT
                q step lambda Hq Hstep Hlambda U T M (fun t _ => Hcomp t))). exact HM.
           ++ split.
              ** apply (proj1 (EB.BKLE20_NATIVE_GP_WEAK_FORM_EXACT
                   hd basis tests td nu T psi U U0 H0)). exact Hform.
              ** apply (proj1 (BKLF40_CANONICAL_ENERGY_LEDGERS_EXACT
                   hd kd basis fg td nu T U Hcomp)). exact Hledger.
  - intros [Hnu [HT [HL2 [Hinitial [HC [[M HM] [Hform Hledger]]]]]]].
    assert (HI : forall t, S.IntrinsicState lambda ell (U t)).
    { intro t. split; [apply HA|].
      apply (proj1 (CB.CANONICAL_ZERO_ROW_L2_IFF_FULL_SHELL_L2
        q step lambda Hq Hstep Hlambda (U t) (Hcomp t))). apply HL2. }
    assert (HB : forall t, 0 <= t <= T -> B.ShellBound (U t) M).
    { apply (proj1 (CB.CANONICAL_PATH_UNIFORM_ENERGY_EXACT
        q step lambda Hq Hstep Hlambda U T M (fun t _ => Hcomp t))). exact HM. }
    split; [exact Hnu|]. split; [exact HT|]. split; [exact HI|]. split.
    + intros k i.
      rewrite (proj1 (C.BKCL11_RECONSTRUCTION_AND_UNIQUENESS
        q step lambda Hq Hstep Hlambda (U 0) (Hcomp 0)) k i).
      rewrite (proj1 (C.BKCL11_RECONSTRUCTION_AND_UNIQUENESS
        q step lambda Hq Hstep Hlambda U0 Hcomp0) k i).
      unfold C.J, C.R, S.reconstruct, B.gp_encode. rewrite (Hinitial i). reflexivity.
    + split.
      * apply (proj2 (P.BKPT32_WEAK_CONTINUITY_TRANSPORT psi lambda ell
          (fun t => 0 <= t <= T) U HP HR H0 HE (fun t _ => HI t))).
        assert (Hphysical : forall t, 0 <= t <= T ->
          B.PhysicalBound (S.reconstruct psi (U t)) M).
        { intros t Ht. apply (proj2 (S.BKSC10_RECONSTRUCTION_PRESERVES_ALL_BOUNDS
            psi lambda ell (U t) HP HR H0 HE (HA t) M)). apply HB. exact Ht. }
        apply (proj2 (P.BKPT20_BOUNDED_WEAK_CONTINUITY_IFF_COORDINATES
          (fun t => 0 <= t <= T) (fun t => S.reconstruct psi (U t)) M Hphysical)).
        exact HC.
      * split.
        -- exists M. exact HB.
        -- split.
           ++ apply (proj2 (EB.BKLE20_NATIVE_GP_WEAK_FORM_EXACT
                hd basis tests td nu T psi U U0 H0)). exact Hform.
           ++ apply (proj2 (BKLF40_CANONICAL_ENERGY_LEDGERS_EXACT
                hd kd basis fg td nu T U Hcomp)). exact Hledger.
Qed.
End ExactCanonicalForwardModels.

Print Assumptions BKLF20_HILBERT_FORWARD_CONTAINMENT.
Print Assumptions BKLF30_CANONICAL_HILBERT_FORWARD_CONTAINMENT.
Print Assumptions BKLF04_HILBERT_SHELL_TRAJECTORY_INJECTIVE.
Print Assumptions BKLF50_CANONICAL_FORWARD_MODELS_EXACT.
End BKQR_LHGP_FORWARD_BRIDGE.
