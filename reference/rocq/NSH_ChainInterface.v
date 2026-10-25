From Stdlib Require Import Reals Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_schur_action_ledger_v0_49_3.

Module NSE_SHARED_CHAIN_INTERFACE.
Import NSE_KQ_FINITE_ALGEBRA NSE_SCHUR_ACTION_LEDGER.
Open Scope R_scope.

(* Byte-identical in both packages.  A point must index BOTH the cut count
   and the physical endpoint when those parameters are present.  Constants
   in a theorem are common to all points, never chosen separately per cut. *)
Record CutTime (t0 t1 : R) : Type := {
  ct_cut : nat;
  ct_time : R;
  ct_admissible : t0 <= ct_time <= t1
}.

Definition UniformAction (Point : Type) (Y : Point -> R) : Prop :=
  exists C : R, 0 <= C /\ forall p, Y p <= C.

(* Exact preserved interface: no renamed action, no new quotient. *)
Definition SharedGramLedger := IntegratedGramLedger.
Definition SharedCapacityEstimate := ReducedCapacityBound.

Theorem NSH00_SHARED_CAPACITY_CLOSES_ACTION :
  forall Point Y W Q Z net V0 Q0 c Z0,
  SharedGramLedger Point Y W Q Z net V0 Q0 ->
  SharedCapacityEstimate Point Y Z c Z0 ->
  UniformAction Point Y.
Proof.
  intros Point Y W Q Z net V0 Q0 c Z0 HG HC.
  exists (action_bound V0 Q0 c Z0); split.
  - destruct HG as [HV HQ HY HW Hq Hz Hb Hs Hcs].
    destruct HC as [Hc [Hz0 Hcap]].
    apply action_bound_nonneg; assumption.
  - exact (NSAR20_UNIFORM_REDUCED_CAPACITY_TO_ACTION
      Point Y W Q Z net V0 Q0 c Z0 HG HC).
Qed.

(* A real integration interface with an explicit integrable domain.
   It does NOT pretend all real functions are integrable.  It can be
   instantiated by finite positive quadrature; a Lebesgue realization and
   the required integrability/trace facts remain explicit analytic work. *)
Record PositiveIntegral (a b : R) : Type := {
  integrable : (R -> R) -> Prop;
  integral : (R -> R) -> R;
  integrable_zero : integrable (fun _ => 0);
  integrable_add : forall f g, integrable f -> integrable g ->
    integrable (fun t => f t + g t);
  integrable_scale : forall c f, integrable f ->
    integrable (fun t => c * f t);
  integral_zero : integral (fun _ => 0) = 0;
  integral_add : forall f g, integrable f -> integrable g ->
    integral (fun t => f t + g t) = integral f + integral g;
  integral_scale : forall c f, integrable f ->
    integral (fun t => c * f t) = c * integral f;
  integral_ext : forall f g, integrable f -> integrable g ->
    (forall t, a <= t <= b -> f t = g t) -> integral f = integral g;
  integral_positive : forall f, integrable f ->
    (forall t, a <= t <= b -> 0 <= f t) -> 0 <= integral f
}.
Arguments integrable {a b} _ _.
Arguments integral {a b} _ _.

Theorem NSH10_INTEGRAL_ORDER : forall a b (I : PositiveIntegral a b) f g,
  integrable I f -> integrable I g ->
  (forall t, a <= t <= b -> f t <= g t) ->
  integral I f <= integral I g.
Proof.
  intros a b I f g Hf Hg Hfg.
  assert (Hneg : integrable I (fun t => -1 * f t)).
  { exact (integrable_scale a b I (-1) f Hf). }
  assert (Hi : integrable I (fun t => g t + -1 * f t)).
  { exact (integrable_add a b I g (fun t => -1*f t) Hg Hneg). }
  pose proof (integral_positive a b I (fun t => g t + -1*f t) Hi) as Hpos.
  assert (Hp : forall t, a <= t <= b -> 0 <= g t + -1*f t).
  { intros t Ht; specialize (Hfg t Ht); lra. }
  specialize (Hpos Hp).
  rewrite (integral_add a b I g (fun t => -1*f t) Hg Hneg) in Hpos.
  rewrite (integral_scale a b I (-1) f Hf) in Hpos; lra.
Qed.

Theorem NSH11_INTEGRATED_SIGNED_CAUCHY :
  forall a b (I : PositiveIntegral a b) q z r,
  integrable I q -> integrable I z -> integrable I r ->
  (forall t, a <= t <= b -> 0 <= q t) ->
  (forall t, a <= t <= b -> 0 <= z t) ->
  (forall t, a <= t <= b -> r t*r t <= q t*z t) ->
  integral I r * integral I r <= integral I q * integral I z.
Proof.
  intros a b I q z r Hq Hz Hr Hq0 Hz0 Hcs.
  apply quadratic_cauchy.
  - exact (integral_positive a b I q Hq Hq0).
  - exact (integral_positive a b I z Hz Hz0).
  - intro x.
    assert (Hi1 : integrable I (fun t => (-2*x)*r t)).
    { exact (integrable_scale a b I (-2*x) r Hr). }
    assert (Hi2 : integrable I (fun t => (x*x)*z t)).
    { exact (integrable_scale a b I (x*x) z Hz). }
    assert (Hi3 : integrable I (fun t => q t+(-2*x)*r t)).
    { exact (integrable_add a b I q (fun t => (-2*x)*r t) Hq Hi1). }
    assert (Hi4 : integrable I (fun t => (q t+(-2*x)*r t)+(x*x)*z t)).
    { exact (integrable_add a b I (fun t => q t+(-2*x)*r t)
        (fun t => (x*x)*z t) Hi3 Hi2). }
    pose proof (integral_positive a b I
      (fun t => (q t+(-2*x)*r t)+(x*x)*z t) Hi4) as HP.
    assert (Hpoint : forall t, a <= t <= b ->
      0 <= (q t+(-2*x)*r t)+(x*x)*z t).
    { intros t Ht.
      pose proof (cauchy_quadratic (q t) (z t) (r t)
        (Hq0 t Ht) (Hz0 t Ht) (Hcs t Ht) x); nra. }
    specialize (HP Hpoint).
    rewrite (integral_add a b I (fun t => q t+(-2*x)*r t)
      (fun t => (x*x)*z t) Hi3 Hi2) in HP.
    rewrite (integral_add a b I q (fun t => (-2*x)*r t) Hq Hi1) in HP.
    rewrite (integral_scale a b I (-2*x) r Hr) in HP.
    rewrite (integral_scale a b I (x*x) z Hz) in HP; nra.
Qed.


Lemma finite_zero_sum : forall n, sum n (fun _=>0)=0.
Proof. induction n; simpl; [reflexivity|rewrite IHn; ring]. Qed.

(* An actual inhabitant of the integral interface.  This proves finite
   quadrature consistency, NOT a quadrature-to-Lebesgue limit theorem. *)
Definition finite_positive_quadrature (a b : R) (n : nat)
  (weight node : nat -> R)
  (Hw : forall i, (i<n)%nat -> 0<=weight i)
  (Hnode : forall i, (i<n)%nat -> a<=node i<=b) : PositiveIntegral a b.
Proof.
  refine {| integrable := fun _ => True;
            integral := fun f => sum n (fun i=>weight i*f (node i)) |}.
  - exact I.
  - intros; exact I.
  - intros; exact I.
  - transitivity (sum n (fun _=>0)).
    + apply sum_ext; intros; ring.
    + apply finite_zero_sum.
  - intros f g Hf Hg; rewrite <- sum_add; apply sum_ext; intros; ring.
  - intros c f Hf; rewrite <- sum_scale; apply sum_ext; intros; ring.
  - intros f g Hf Hg Heq; apply sum_ext; intros i Hi.
    rewrite (Heq (node i) (Hnode i Hi)); reflexivity.
  - intros f Hf Hp; apply sum_nonneg; intros i Hi.
    apply Rmult_le_pos; [exact (Hw i Hi)|exact (Hp (node i) (Hnode i Hi))].
Defined.

(* The omitted uniform-capacity assertion cannot be manufactured from
   the other ledger fields: this imports the existing checked countermodel. *)
Theorem NSH90_CAPACITY_IS_NOT_DERIVED_FROM_LEDGER_ALONE :
  SharedGramLedger R (fun x => x*x) (fun _ => 0) (fun _ => 1)
    (fun x => (x*x)*(x*x)) (fun x => x*x) 0 1 /\
  ~ (exists C : R, forall x : R, x*x <= C).
Proof. exact NSAR90_LEDGER_WITHOUT_CAPACITY_CAN_HAVE_UNBOUNDED_ACTION. Qed.

End NSE_SHARED_CHAIN_INTERFACE.
