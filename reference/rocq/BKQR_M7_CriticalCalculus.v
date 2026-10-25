From Stdlib Require Import Reals Ranalysis1 Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_schur_action_ledger_v0_49_3.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module BKQR_M7_CRITICAL_CALCULUS.
Module K := NSE_KQ_FINITE_ALGEBRA.
Module TC := NSE_CONTINUOUS_TIME_CALCULUS.
Module AL := NSE_SCHUR_ACTION_LEDGER.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

(* lambda is the frequency (the Stokes eigenvalue is lambda squared).
   The source b is the full source of a. No finite Galerkin closure is used.
   Identification of lambda with a physical operator, and derivation of
   ModalEquation from a weak PDE, are separate explicit obligations. *)
Definition critical_mass (lambda : nat -> R) (a : R -> nat -> R)
    (N : nat) (t : R) : R :=
  K.sum N (fun i => lambda i * a t i * a t i).
Definition critical_density (lambda : nat -> R) (a : R -> nat -> R)
    (N : nat) (t : R) : R :=
  K.sum N (fun i => lambda i * lambda i * lambda i * a t i * a t i).
Definition critical_current (lambda : nat -> R) (a b : R -> nat -> R)
    (N : nat) (t : R) : R :=
  - K.sum N (fun i => lambda i * a t i * b t i).
Definition raw_action lambda a b N t : R :=
  AL.positive_action (critical_current lambda a b N t)
    (critical_density lambda a N t).
Definition normalized_action nu lambda a b N t : R :=
  raw_action lambda a b N t / nu.
Definition critical_rate nu lambda a b N t : R :=
  2 * critical_current lambda a b N t - 2 * nu * critical_density lambda a N t.

Definition OpenTime (T t : R) : Prop := 0 <= t < T.
(* These are supplied ordinary derivative primitives on [0,T), including
   the initial point. Their existence is not asserted. In particular, the
   zero-capacity action convention need not give a continuous density at
   rank changes; an almost-everywhere/absolute-continuity extension would
   require a separate integration theorem. *)
Definition OpenPrimitive T (f F : R -> R) : Prop :=
  F 0 = 0 /\ forall t, OpenTime T t -> derivable_pt_lim F t (f t).
Definition ModalEquation T nu lambda (a b : R -> nat -> R) : Prop :=
  forall t i, OpenTime T t ->
    derivable_pt_lim (fun s => a s i) t
      (-nu * lambda i * lambda i * a t i - b t i).
Definition CriticalPoint T : Type := (nat * {t : R | OpenTime T t})%type.
Definition point_mass T lambda a (p : CriticalPoint T) : R :=
  critical_mass lambda a (fst p) (proj1_sig (snd p)).
Definition point_cumulative T (F : nat -> R -> R) (p : CriticalPoint T) : R :=
  F (fst p) (proj1_sig (snd p)).

Lemma critical_mass_nonnegative : forall lambda a N t,
  (forall i, 0 <= lambda i) -> 0 <= critical_mass lambda a N t.
Proof.
  intros lambda a N t Hlambda. unfold critical_mass.
  apply K.sum_nonneg. intros i Hi.
  replace (lambda i * a t i * a t i) with (lambda i * (a t i * a t i)) by ring.
  apply Rmult_le_pos; [apply Hlambda | nra].
Qed.

Lemma critical_density_nonnegative : forall lambda a N t,
  (forall i, 0 <= lambda i) -> 0 <= critical_density lambda a N t.
Proof.
  intros lambda a N t Hlambda. unfold critical_density.
  apply K.sum_nonneg. intros i Hi.
  replace (lambda i * lambda i * lambda i * a t i * a t i)
    with (lambda i * ((lambda i * a t i) * (lambda i * a t i))) by ring.
  apply Rmult_le_pos; [apply Hlambda | nra].
Qed.

Theorem BKMC10_ZERO_DENSITY_FORCES_ZERO_CURRENT : forall lambda a b N t,
  (forall i, 0 <= lambda i) ->
  critical_density lambda a N t = 0 -> critical_current lambda a b N t = 0.
Proof.
  intros lambda a b N. induction N as [|N IH]; intros t Hlambda HD.
  - unfold critical_current. simpl. ring.
  - assert (Hp : 0 <= critical_density lambda a N t).
    { apply critical_density_nonnegative. exact Hlambda. }
    assert (Hn : 0 <= lambda N * lambda N * lambda N * a t N * a t N).
    { replace (lambda N * lambda N * lambda N * a t N * a t N)
        with (lambda N * ((lambda N * a t N) * (lambda N * a t N))) by ring.
      apply Rmult_le_pos; [apply Hlambda | nra]. }
    change (critical_density lambda a N t +
      lambda N * lambda N * lambda N * a t N * a t N = 0) in HD.
    assert (Hprev : critical_density lambda a N t = 0) by lra.
    assert (Hterm : (lambda N * a t N) * (lambda N * a t N) * lambda N = 0) by nra.
    assert (Hla : lambda N * a t N = 0).
    { apply Rmult_integral in Hterm. destruct Hterm as [Hsq | Hz]; nra. }
    specialize (IH t Hlambda Hprev).
    unfold critical_current in *. simpl. rewrite Hla.
    lra.
Qed.

Lemma raw_action_nonnegative : forall lambda a b N t,
  (forall i, 0 <= lambda i) -> 0 <= raw_action lambda a b N t.
Proof.
  intros lambda a b N t Hlambda. unfold raw_action, AL.positive_action, Rdiv.
  apply Rmult_le_pos; [nra |].
  pose proof (critical_density_nonnegative lambda a N t Hlambda) as HD.
  destruct (Req_dec (critical_density lambda a N t) 0) as [Hz | Hnz].
  - rewrite Hz, Rinv_0. lra.
  - apply Rlt_le, Rinv_0_lt_compat. lra.
Qed.

Lemma normalized_action_nonnegative : forall nu lambda a b N t,
  0 < nu -> (forall i, 0 <= lambda i) ->
  0 <= normalized_action nu lambda a b N t.
Proof.
  intros nu lambda a b N t Hnu Hlambda. unfold normalized_action, Rdiv.
  apply Rmult_le_pos; [apply raw_action_nonnegative; exact Hlambda |].
  apply Rlt_le, Rinv_0_lt_compat. exact Hnu.
Qed.

Theorem BKMC11_EXACT_QUADRATIC_ACTION : forall lambda a b N t,
  (forall i, 0 <= lambda i) ->
  Rmax (critical_current lambda a b N t) 0 *
    Rmax (critical_current lambda a b N t) 0 =
  raw_action lambda a b N t * critical_density lambda a N t.
Proof.
  intros lambda a b N t Hlambda.
  destruct (Req_dec (critical_density lambda a N t) 0) as [Hz | Hnz].
  - pose proof (BKMC10_ZERO_DENSITY_FORCES_ZERO_CURRENT lambda a b N t Hlambda Hz) as Hj.
    unfold raw_action, AL.positive_action. rewrite Hz, Hj, Rmax_left by lra. ring.
  - unfold raw_action, AL.positive_action. field. exact Hnz.
Qed.

Theorem BKMC20_LOCAL_ABSORPTION : forall nu lambda a b N t,
  0 < nu -> (forall i, 0 <= lambda i) ->
  critical_rate nu lambda a b N t + nu * critical_density lambda a N t <=
    normalized_action nu lambda a b N t.
Proof.
  intros nu lambda a b N t Hnu Hlambda.
  pose proof (critical_density_nonnegative lambda a N t Hlambda) as HD.
  pose proof (raw_action_nonnegative lambda a b N t Hlambda) as HA.
  pose proof (Rmax_r (critical_current lambda a b N t) 0) as Hr.
  pose proof (Rmax_l (critical_current lambda a b N t) 0) as Hj.
  pose proof (BKMC11_EXACT_QUADRATIC_ACTION lambda a b N t Hlambda) as Heq.
  pose proof (CE.NSCE00_QUADRATIC_RESISTANT_ACTION_YOUNG nu
    (critical_density lambda a N t) (raw_action lambda a b N t)
    (Rmax (critical_current lambda a b N t) 0) Hnu HD HA Hr
    ltac:(lra)) as HY.
  unfold critical_rate, normalized_action.
  apply (Rmult_le_reg_l nu); [exact Hnu |].
  replace (nu * (raw_action lambda a b N t / nu))
    with (raw_action lambda a b N t) by (field; lra).
  nra.
Qed.

Theorem BKMC21_ACTUAL_CRITICAL_MASS_DERIVATIVE : forall T nu lambda a b,
  ModalEquation T nu lambda a b -> forall N t, OpenTime T t ->
  derivable_pt_lim (critical_mass lambda a N) t (critical_rate nu lambda a b N t).
Proof.
  intros T nu lambda a b Hmodal N t Ht.
  pose proof (TC.NSCT40_FINITE_WEIGHTED_ENERGY_DERIVATIVE N lambda a
    (fun i => -nu * lambda i * lambda i * a t i - b t i) t
    (fun i _ => Hmodal t i Ht)) as HD.
  assert (Heq : 2 * K.sum N (fun i => lambda i * a t i *
      (-nu * lambda i * lambda i * a t i - b t i)) =
    critical_rate nu lambda a b N t).
  { unfold critical_rate, critical_current, critical_density.
    rewrite <- K.sum_scale.
    replace (2 * - K.sum N (fun i => lambda i * a t i * b t i) -
      2 * nu * K.sum N (fun i => lambda i * lambda i * lambda i * a t i * a t i))
      with ((-2) * K.sum N (fun i => lambda i * a t i * b t i) +
      (-2*nu) * K.sum N (fun i => lambda i * lambda i * lambda i * a t i * a t i)) by ring.
    rewrite <- !K.sum_scale, <- K.sum_add. apply K.sum_ext. intros i Hi. ring. }
  cbn beta in HD. rewrite Heq in HD. exact HD.
Qed.

Lemma open_primitive_on_segment : forall T f F,
  OpenPrimitive T f F -> forall t, OpenTime T t -> TC.PrimitiveOn 0 t f F.
Proof.
  intros T f F [H0 HD] t Ht. split; [exact H0 |].
  intros r Hr. apply HD. unfold TC.InTime, OpenTime in *. lra.
Qed.

Theorem BKMC30_OPEN_PRIMITIVE_NONNEGATIVE : forall T f F,
  OpenPrimitive T f F ->
  (forall t, OpenTime T t -> 0 <= f t) ->
  forall t, OpenTime T t -> 0 <= F t.
Proof.
  intros T f F HF Hf t Ht.
  apply (TC.NSCT10_PRIMITIVE_NONNEGATIVE 0 t f F t).
  - apply (open_primitive_on_segment T f F HF t Ht).
  - intros r Hr. apply Hf. unfold TC.InTime, OpenTime in *. lra.
  - unfold TC.InTime, OpenTime in *. lra.
Qed.

Theorem BKMC31_OPEN_PRIMITIVE_MONOTONE : forall T f F,
  OpenPrimitive T f F ->
  (forall t, OpenTime T t -> 0 <= f t) ->
  forall s t, OpenTime T s -> OpenTime T t -> s <= t -> F s <= F t.
Proof.
  intros T f F [H0 HD] Hf s t Hs Ht Hst.
  apply (TC.NSCT00_NONNEGATIVE_DERIVATIVE_GIVES_ORDER s t F f Hst).
  - intros r Hr. apply HD. unfold TC.InTime, OpenTime in *. lra.
  - intros r Hr. apply Hf. unfold TC.InTime, OpenTime in *. lra.
Qed.

Theorem BKMC33_NORMALIZED_ACTION_PRIMITIVE_PROPERTIES :
  forall T nu lambda a b N C,
  0 < nu -> (forall i, 0 <= lambda i) ->
  OpenPrimitive T (normalized_action nu lambda a b N) C ->
  (forall t, OpenTime T t -> 0 <= C t) /\
  (forall s t, OpenTime T s -> OpenTime T t -> s <= t ->
    0 <= C t - C s).
Proof.
  intros T nu lambda a b N C Hnu Hlambda HC.
  assert (Ha : forall t, OpenTime T t ->
      0 <= normalized_action nu lambda a b N t).
  { intros t Ht. apply normalized_action_nonnegative; assumption. }
  split.
  - exact (BKMC30_OPEN_PRIMITIVE_NONNEGATIVE T
      (normalized_action nu lambda a b N) C HC Ha).
  - intros s t Hs Ht Hst.
    pose proof (BKMC31_OPEN_PRIMITIVE_MONOTONE T
      (normalized_action nu lambda a b N) C HC Ha s t Hs Ht Hst). lra.
Qed.

Theorem BKMC32_INTEGRATED_CRITICAL_BALANCE : forall T nu lambda a b D C,
  0 < nu -> (forall i, 0 <= lambda i) -> ModalEquation T nu lambda a b ->
  (forall N, OpenPrimitive T (critical_density lambda a N) (D N)) ->
  (forall N, OpenPrimitive T (normalized_action nu lambda a b N) (C N)) ->
  forall N t, OpenTime T t ->
    critical_mass lambda a N t + nu * D N t <=
      critical_mass lambda a N 0 + C N t.
Proof.
  intros T nu lambda a b D C Hnu Hlambda Hmodal HD HC N t Ht.
  set (F := fun r => critical_mass lambda a N r + nu * D N r - C N r).
  set (f := fun r => critical_rate nu lambda a b N r +
    nu * critical_density lambda a N r - normalized_action nu lambda a b N r).
  assert (HF : TC.DerivativeOn 0 t F f).
  { intros r Hr. assert (HrT : OpenTime T r) by (unfold TC.InTime, OpenTime in *; lra).
    unfold F, f. apply derivable_pt_lim_minus.
    - apply derivable_pt_lim_plus.
      + apply (BKMC21_ACTUAL_CRITICAL_MASS_DERIVATIVE T nu lambda a b Hmodal N r HrT).
      + apply derivable_pt_lim_scal. exact (proj2 (HD N) r HrT).
    - exact (proj2 (HC N) r HrT). }
  assert (Hneg : forall r, TC.InTime 0 t r -> f r <= 0).
  { intros r Hr. unfold f.
    pose proof (BKMC20_LOCAL_ABSORPTION nu lambda a b N r Hnu Hlambda). lra. }
  pose proof (TC.NSCT01_NONPOSITIVE_DERIVATIVE_GIVES_ORDER 0 t F f
    (proj1 Ht) HF Hneg) as Hle.
  unfold F in Hle. rewrite (proj1 (HD N)), (proj1 (HC N)) in Hle. lra.
Qed.

Theorem BKMC40_DERIVED_CRITICAL_ENERGY_BALANCE : forall T nu lambda a b D C X0,
  0 < T -> 0 < nu -> (forall i, 0 <= lambda i) ->
  ModalEquation T nu lambda a b ->
  (forall N, OpenPrimitive T (critical_density lambda a N) (D N)) ->
  (forall N, OpenPrimitive T (normalized_action nu lambda a b N) (C N)) ->
  (forall N, critical_mass lambda a N 0 <= X0) ->
  CE.CriticalEnergyBalance (CriticalPoint T) nu 0 X0
    (point_mass T lambda a) (point_cumulative T D) (point_cumulative T C).
Proof.
  intros T nu lambda a b D C X0 HT Hnu Hlambda Hmodal HD HC HX0.
  constructor.
  - exact Hnu.
  - lra.
  - lra.
  - specialize (HX0 O). change (0 <= X0) in HX0. exact HX0.
  - intros [N [t Ht]]. apply critical_mass_nonnegative. exact Hlambda.
  - intros [N [t Ht]]. unfold point_cumulative; simpl.
    apply (BKMC30_OPEN_PRIMITIVE_NONNEGATIVE T
      (critical_density lambda a N) (D N) (HD N)); [|exact Ht].
    intros r Hr. apply critical_density_nonnegative. exact Hlambda.
  - intros [N [t Ht]]. unfold point_cumulative; simpl.
    apply (BKMC30_OPEN_PRIMITIVE_NONNEGATIVE T
      (normalized_action nu lambda a b N) (C N) (HC N)); [|exact Ht].
    intros r Hr. apply normalized_action_nonnegative; assumption.
  - intros [N [t Ht]]. unfold point_mass, point_cumulative; simpl.
    unfold CE.effective_viscosity.
    pose proof (BKMC32_INTEGRATED_CRITICAL_BALANCE T nu lambda a b D C
      Hnu Hlambda Hmodal HD HC N t Ht). specialize (HX0 N). lra.
Qed.

Print Assumptions BKMC10_ZERO_DENSITY_FORCES_ZERO_CURRENT.
Print Assumptions BKMC21_ACTUAL_CRITICAL_MASS_DERIVATIVE.
Print Assumptions BKMC40_DERIVED_CRITICAL_ENERGY_BALANCE.

End BKQR_M7_CRITICAL_CALCULUS.
