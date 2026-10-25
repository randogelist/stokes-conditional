From Stdlib Require Import Reals Lra Psatz Field.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_TimeIntegrals.

Module BKQR_ENERGY_PATHS.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_TIME_INTEGRALS.
Open Scope R_scope.

Definition multiply_path (lambda : nat -> R) (u : R -> nat -> R)
  (t : R) := spectral_multiply lambda (u t).
Definition shift_path (ell : nat -> R) (U : R -> nat -> nat -> R)
  (t : R) := shell_shift ell (U t).

Lemma multiply_path_continuous : forall lambda u a b,
  CoordinateContinuous u a b -> CoordinateContinuous (multiply_path lambda u) a b.
Proof. intros lambda u a b H i. apply continuous_scale. apply H. Qed.

Lemma shift_path_continuous : forall ell U a b,
  ShellCoordinateContinuous U a b ->
  ShellCoordinateContinuous (shift_path ell U) a b.
Proof. intros ell U a b H k i. apply continuous_scale. apply H. Qed.

Lemma reconstruct_path_continuous : forall psi U a b,
  ShellCoordinateContinuous U a b ->
  CoordinateContinuous (fun t => reconstruct psi (U t)) a b.
Proof.
  intros psi U a b H i t Ht. unfold reconstruct, Rdiv.
  apply continuity_pt_mult.
  - apply H. exact Ht.
  - apply continuity_pt_const. intros x y. reflexivity.
Qed.

Lemma coordinate_continuity_restrict : forall u a b s t,
  CoordinateContinuous u a b -> a <= s -> t <= b ->
  CoordinateContinuous u s t.
Proof. intros u a b s t H Ha Hb i r Hr. apply H. lra. Qed.

Lemma shell_continuity_restrict : forall U a b s t,
  ShellCoordinateContinuous U a b -> a <= s -> t <= b ->
  ShellCoordinateContinuous U s t.
Proof. intros U a b s t H Ha Hb k i r Hr. apply H. lra. Qed.

(* Integrals are actual coordinate Riemann integrals followed by the
   constructed nonnegative countable sum. Continuity witnesses are
   existential; the numeric totals do not depend on these witnesses. *)
Definition DissipationTotal lambda u a b (Hab : a <= b) D : Prop :=
  exists H : CoordinateContinuous (multiply_path lambda u) a b,
    TimeTotal (fun _ => 1) (multiply_path lambda u) a b Hab H D.

Definition NativeDissipationTotal ell U a b (Hab : a <= b) D : Prop :=
  exists H : ShellCoordinateContinuous (shift_path ell U) a b,
    ShellTimeTotal (fun _ => 1) (shift_path ell U) a b Hab H D.

Lemma dissipation_total_nonnegative : forall lambda u a b Hab D,
  DissipationTotal lambda u a b Hab D -> 0 <= D.
Proof.
  intros lambda u a b Hab D [H [Hb Hleast]].
  specialize (Hb O). exact Hb.
Qed.

Lemma native_dissipation_total_nonnegative : forall ell U a b Hab D,
  NativeDissipationTotal ell U a b Hab D -> 0 <= D.
Proof.
  intros ell U a b Hab D [H [Hb Hleast]].
  specialize (Hb O O). exact Hb.
Qed.

Definition IntervalEnergy lambda nu T (Start : R -> Prop) u : Prop :=
  forall s t (Hst : s <= t), 0 <= s -> t <= T -> (s=0 \/ Start s) ->
    exists Es Et D,
      PhysicalTotal (u s) Es /\ PhysicalTotal (u t) Et /\
      DissipationTotal lambda u s t Hst D /\ Et+2*nu*D <= Es.

Definition NativeIntervalEnergy ell nu T (Start : R -> Prop) U : Prop :=
  forall s t (Hst : s <= t), 0 <= s -> t <= T -> (s=0 \/ Start s) ->
    exists Es Et D,
      ShellTotal (U s) Es /\ ShellTotal (U t) Et /\
      NativeDissipationTotal ell U s t Hst D /\ Et+2*nu*D <= Es.

(* The same arbitrary start set is preserved. In a physical application
   it must be the full-measure admissible set. We do not replace a.e.
   starting times by an all-starting-times requirement. *)
Definition SpectralEnergyPath lambda nu T Start u v0 E0 : Prop :=
  CoordinateContinuous u 0 T /\ (forall i, u 0 i=v0 i) /\
  PhysicalTotal (u 0) E0 /\ IntervalEnergy lambda nu T Start u.

Definition NativeEnergyPath lambda ell nu T Start U V0 E0 : Prop :=
  ShellCoordinateContinuous U 0 T /\
  (forall t, 0 <= t <= T -> AdjacentCompatible lambda ell (U t)) /\
  (forall k i, U 0 k i=V0 k i) /\ ShellTotal (U 0) E0 /\
  NativeIntervalEnergy ell nu T Start U.

Theorem BKEP10_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP :
  forall lambda nu T Start u v0 E0,
  0 <= nu -> SpectralEnergyPath lambda nu T Start u v0 E0 ->
  forall t, 0 <= t <= T -> PhysicalBound (u t) E0.
Proof.
  intros lambda nu T Start u v0 E0 Hnu [HC [Hinit [H0 Henergy]]] t Ht.
  destruct (Henergy 0 t (proj1 Ht) (Rle_refl 0) (proj2 Ht) (or_introl eq_refl))
    as [Es [Et [D [Hs [He [HD Hineq]]]]]].
  assert (Hs0 : Es=E0) by (eapply physical_total_unique; eassumption).
  subst Es. pose proof (dissipation_total_nonnegative lambda u 0 t (proj1 Ht) D HD).
  intros N. pose proof (proj1 He N). nra.
Qed.

Theorem BKEP11_NATIVE_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP :
  forall lambda ell nu T Start U V0 E0,
  0 <= nu -> NativeEnergyPath lambda ell nu T Start U V0 E0 ->
  forall t, 0 <= t <= T -> ShellBound (U t) E0.
Proof.
  intros lambda ell nu T Start U V0 E0 Hnu
    [HC [Hadj [Hinit [H0 Henergy]]]] t Ht.
  destruct (Henergy 0 t (proj1 Ht) (Rle_refl 0) (proj2 Ht) (or_introl eq_refl))
    as [Es [Et [D [Hs [He [HD Hineq]]]]]].
  assert (Hs0 : Es=E0) by (eapply shell_total_unique; eassumption).
  subst Es. pose proof (native_dissipation_total_nonnegative ell U 0 t (proj1 Ht) D HD).
  intros K N. pose proof (proj1 He K N). nra.
Qed.

Section Factorization.
Variable psi : nat -> nat -> R.
Variables lambda ell : nat -> R.
Variable T : R.
Hypothesis HT : 0 <= T.
Hypothesis Hp : ScalarPartition psi.
Hypothesis Hzero : forall i, psi 0%nat i <> 0.
Variable u : R -> nat -> R.
Variable U : R -> nat -> nat -> R.
Hypothesis Hu : CoordinateContinuous u 0 T.
Hypothesis HU : ShellCoordinateContinuous U 0 T.
Hypothesis Hcomp : forall t, 0 <= t <= T -> AdjacentCompatible lambda ell (U t).
Hypothesis Hfactor : forall t k i, 0 <= t <= T -> U t k i=gp_encode psi (u t) k i.

Lemma path_total_energy : forall t, 0 <= t <= T -> forall E,
  PhysicalTotal (u t) E <-> ShellTotal (U t) E.
Proof.
  intros t Ht E. apply GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY with (psi := psi).
  - exact Hp.
  - intros k i. apply Hfactor. exact Ht.
Qed.

Lemma path_dissipation_factorization : forall t k i,
  0 <= t <= T -> shift_path ell U t k i =
    psi k i * multiply_path lambda u t i.
Proof.
  intros t k i Ht. unfold shift_path, shell_shift, multiply_path, spectral_multiply.
  rewrite <- (Hcomp t Ht k i). rewrite (Hfactor t k i Ht).
  unfold gp_encode. ring.
Qed.

Theorem BKEP20_EXACT_INTEGRATED_DISSIPATION : forall a b Hab,
  0 <= a -> b <= T -> forall D,
  DissipationTotal lambda u a b Hab D <-> NativeDissipationTotal ell U a b Hab D.
Proof.
  intros a b Hab Ha Hb D.
  assert (Huc : CoordinateContinuous (multiply_path lambda u) a b).
  { apply multiply_path_continuous. eapply coordinate_continuity_restrict; eauto. }
  assert (HUc : ShellCoordinateContinuous (shift_path ell U) a b).
  { apply shift_path_continuous. eapply shell_continuity_restrict; eauto. }
  assert (HF : forall t k i, a <= t <= b -> shift_path ell U t k i =
      psi k i*multiply_path lambda u t i).
  { intros t k i Ht. apply path_dissipation_factorization. lra. }
  split.
  - intros [H Htotal]. exists HUc.
    apply (proj1 (TIME_PARTITION_PRESERVES_TOTAL psi (fun _ => 1)
      (multiply_path lambda u) (shift_path ell U) a b Hab H HUc
      Hp (ltac:(intro i; lra)) HF D)). exact Htotal.
  - intros [H Htotal]. exists Huc.
    apply (proj2 (TIME_PARTITION_PRESERVES_TOTAL psi (fun _ => 1)
      (multiply_path lambda u) (shift_path ell U) a b Hab Huc H
      Hp (ltac:(intro i; lra)) HF D)). exact Htotal.
Qed.

Theorem BKEP21_EXACT_INTERVAL_ENERGY : forall nu Start,
  IntervalEnergy lambda nu T Start u <-> NativeIntervalEnergy ell nu T Start U.
Proof.
  intros nu Start. split.
  - intros H s t Hst Hs Ht Hstart.
    destruct (H s t Hst Hs Ht Hstart) as [Es [Et [D [Hes [Het [HD Hineq]]]]]].
    exists Es, Et, D. split.
    + apply (proj1 (path_total_energy s (ltac:(lra)) Es)); exact Hes.
    + split.
      * apply (proj1 (path_total_energy t (ltac:(lra)) Et)); exact Het.
      * split.
        -- apply (proj1 (BKEP20_EXACT_INTEGRATED_DISSIPATION s t Hst Hs Ht D)); exact HD.
        -- exact Hineq.
  - intros H s t Hst Hs Ht Hstart.
    destruct (H s t Hst Hs Ht Hstart) as [Es [Et [D [Hes [Het [HD Hineq]]]]]].
    exists Es, Et, D. split.
    + apply (proj2 (path_total_energy s (ltac:(lra)) Es)); exact Hes.
    + split.
      * apply (proj2 (path_total_energy t (ltac:(lra)) Et)); exact Het.
      * split.
        -- apply (proj2 (BKEP20_EXACT_INTEGRATED_DISSIPATION s t Hst Hs Ht D)); exact HD.
        -- exact Hineq.
Qed.

Theorem BKEP22_EXACT_ENERGY_PATH : forall nu Start v0 E0,
  SpectralEnergyPath lambda nu T Start u v0 E0 <->
  NativeEnergyPath lambda ell nu T Start U (gp_encode psi v0) E0.
Proof.
  intros nu Start v0 E0. split.
  - intros [_ [Hinit [HE HI]]]. split; [exact HU|].
    split; [exact Hcomp|]. split.
    + intros k i. rewrite Hfactor by lra. unfold gp_encode. rewrite Hinit. reflexivity.
    + split.
      * apply (proj1 (path_total_energy 0 (ltac:(lra)) E0)). exact HE.
      * apply (proj1 (BKEP21_EXACT_INTERVAL_ENERGY nu Start)). exact HI.
  - intros [_ [_ [Hinit [HE HI]]]]. split; [exact Hu|]. split.
    + intro i. apply (Rmult_eq_reg_l (psi 0%nat i)); [|apply Hzero].
      change (gp_encode psi (u 0) 0%nat i=gp_encode psi v0 0%nat i).
      rewrite <- (Hfactor 0 0%nat i (ltac:(lra))). apply Hinit.
    + split.
      * apply (proj2 (path_total_energy 0 (ltac:(lra)) E0)). exact HE.
      * apply (proj2 (BKEP21_EXACT_INTERVAL_ENERGY nu Start)). exact HI.
Qed.
End Factorization.

Theorem BKEP30_ENCODE_ENERGY_PATH : forall psi lambda ell nu T Start u v0 E0,
  0 <= T -> ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) ->
  SpectralEnergyPath lambda nu T Start u v0 E0 ->
  NativeEnergyPath lambda ell nu T Start (fun t => gp_encode psi (u t))
    (gp_encode psi v0) E0.
Proof.
  intros psi lambda ell nu T Start u v0 E0 HT Hp Hr H0 Hpath.
  pose proof (proj1 Hpath) as Hu.
  eapply (proj1 (BKEP22_EXACT_ENERGY_PATH psi lambda ell T HT Hp H0
    u (fun t => gp_encode psi (u t)) Hu
    (shell_encode_continuous psi u 0 T Hu)
    (fun t _ => BKSC01_ENCODE_ADJACENT psi lambda ell (u t) Hr)
    (fun t k i _ => eq_refl) nu Start v0 E0)). exact Hpath.
Qed.

Theorem BKEP31_DECODE_ENERGY_PATH : forall psi lambda ell nu T Start U v0 E0,
  0 <= T -> ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  NativeEnergyPath lambda ell nu T Start U (gp_encode psi v0) E0 ->
  SpectralEnergyPath lambda nu T Start (fun t => reconstruct psi (U t)) v0 E0.
Proof.
  intros psi lambda ell nu T Start U v0 E0 HT Hp Hr H0 He Hpath.
  pose proof (proj1 Hpath) as HU. pose proof (proj1 (proj2 Hpath)) as Hcomp.
  assert (Hfactor : forall t k i, 0 <= t <= T ->
    U t k i=gp_encode psi (reconstruct psi (U t)) k i).
  { intros t k i Ht. eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION; eauto. }
  apply (proj2 (BKEP22_EXACT_ENERGY_PATH psi lambda ell T HT Hp H0
    (fun t => reconstruct psi (U t)) U
    (reconstruct_path_continuous psi U 0 T HU) HU Hcomp Hfactor nu Start v0 E0)).
  exact Hpath.
Qed.

End BKQR_ENERGY_PATHS.
