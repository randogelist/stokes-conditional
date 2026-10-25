From Stdlib Require Import Reals Lra Psatz.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.
Require Import LHGP_Hilbert LHGP_Realization LHGP_WeakTopology.
Require Import LHGP_Evolution LHGP_Equivalence.

Open Scope R_scope.

(* Initial-time energy is a separate condition from the stronger restart
   condition. No later-time inequality is obtained by subtracting two
   initial-time upper bounds. D is a scalar representative on GoodD;
   no assertion of finite dissipation at every time is made. *)
Definition InitialEnergyInequality (nu T : R) (I : TimeIntegral)
    (E D : R -> R) : Prop :=
  forall t, 0 <= t <= T -> E t + 2 * nu * I 0 t D <= E 0.

Definition EnergySchedule0 (td : TimeData) (nu T : R)
    (E D : R -> R) (GoodD : R -> Prop) : Prop :=
  TFullMeasure td T GoodD /\
  (forall t, 0 <= D t) /\
  (forall t, ~ (0 <= t <= T /\ GoodD t) -> D t = 0) /\
  (forall s t, 0 <= s <= t -> t <= T -> TIntegrable td s t D) /\
  InitialEnergyInequality nu T (TIntegral td) E D.

Theorem RESTART_ENERGY_IMPLIES_INITIAL_ENERGY : forall nu T I E D GoodStart,
  RestartEnergyInequality nu T GoodStart I E D ->
  InitialEnergyInequality nu T I E D.
Proof.
  intros nu T I E D GoodStart Hrestart t Ht.
  apply (Hrestart 0 t); [lra | exact (proj2 Ht) | left; reflexivity].
Qed.

Theorem ENERGY_SCHEDULE_IMPLIES_SCHEDULE0 : forall td nu T E D GoodD GoodStart,
  EnergySchedule td nu T E D GoodD GoodStart ->
  EnergySchedule0 td nu T E D GoodD.
Proof.
  intros td nu T E D GoodD GoodStart
    [HfullD [HfullStart [Hnonnegative [Hzero [Hint Hrestart]]]]].
  split; [exact HfullD |]; split; [exact Hnonnegative |].
  split; [exact Hzero |]; split; [exact Hint |].
  apply RESTART_ENERGY_IMPLIES_INITIAL_ENERGY with (GoodStart := GoodStart).
  exact Hrestart.
Qed.

Theorem ENERGY_SCHEDULE0_ENERGY_BOUND : forall td nu T E D GoodD,
  0 <= nu -> IntegralNonnegative td ->
  EnergySchedule0 td nu T E D GoodD ->
  forall t, 0 <= t <= T -> E t <= E 0.
Proof.
  intros td nu T E D GoodD Hnu HI
    [Hfull [Hnonnegative [Hzero [Hint Henergy]]]] t Ht.
  specialize (Henergy t Ht).
  assert (Hpositive : 0 <= TIntegral td 0 t D).
  { apply HI; [lra | apply Hint; lra |].
    intros r Hr; apply Hnonnegative. }
  assert (0 <= 2 * nu * TIntegral td 0 t D) by nra.
  lra.
Qed.

Theorem ENERGY_SCHEDULE0_STRONG_INITIAL : forall h td nu T u E D GoodD,
  0 <= nu -> 0 < T -> IntegralNonnegative td ->
  HWeakContinuous h u T ->
  (forall t, E t = HNorm h (u t)) ->
  EnergySchedule0 td nu T E D GoodD ->
  EnergyInitialTrace (fun t => HDist h (u t) (u 0)).
Proof.
  intros h td nu T u E D GoodD Hnu HT HI HC HE HS.
  apply (HWeak_energy_initial_trace h u T HT HC).
  intros t Ht; rewrite <- (HE t), <- (HE 0).
  exact (ENERGY_SCHEDULE0_ENERGY_BOUND td nu T E D GoodD Hnu HI HS t Ht).
Qed.

Print Assumptions ENERGY_SCHEDULE_IMPLIES_SCHEDULE0.
Print Assumptions ENERGY_SCHEDULE0_ENERGY_BOUND.
Print Assumptions ENERGY_SCHEDULE0_STRONG_INITIAL.
