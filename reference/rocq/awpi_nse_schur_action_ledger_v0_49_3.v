From Stdlib Require Import Reals Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_gp_gram_geometry_v0_49_3.

Module NSE_SCHUR_ACTION_LEDGER.
Import NSE_KQ_FINITE_ALGEBRA NSE_GP_GRAM_GEOMETRY.
Open Scope R_scope.

(* The physical action normalization cancels its moving scale drift.
   This is real algebra, NOT an assertion of differentiability of a PDE. *)
Definition positive_action (phi g : R) := Rmax phi 0 * Rmax phi 0 / g.
Definition renewal_pairing (phi g Q J : R) :=
  2 * Rmax phi 0 * Q/g - positive_action phi g * J/g.

Lemma rmax_positive_scale : forall rho x,
  0 < rho -> Rmax (rho*x) 0 = rho*Rmax x 0.
Proof.
  intros rho x Hr; destruct (Rle_dec 0 x) as [Hx | Hx].
  - rewrite Rmax_left by nra; rewrite Rmax_left by lra; reflexivity.
  - rewrite Rmax_right by nra; rewrite Rmax_right by lra; ring.
Qed.

Theorem NSAR00_MOVING_GP_ACTION_INVARIANCE : forall rho phi g,
  0 < rho -> 0 < g -> positive_action (rho*phi) (rho*rho*g) = positive_action phi g.
Proof.
  intros; unfold positive_action; rewrite rmax_positive_scale by assumption; field; nra.
Qed.

Theorem NSAR01_MOVING_GP_RENEWAL_DRIFT_CANCELLATION : forall rho drho phi g Q J,
  0 < rho -> 0 < g ->
  renewal_pairing (rho*phi) (rho*rho*g) (rho*Q+drho*phi)
    (rho*rho*J+2*rho*drho*g) = renewal_pairing phi g Q J.
Proof.
  intros rho drho phi g Q J Hr Hg.
  unfold renewal_pairing.
  rewrite (NSAR00_MOVING_GP_ACTION_INVARIANCE rho phi g Hr Hg).
  rewrite rmax_positive_scale by assumption.
  destruct (Rle_dec 0 phi) as [Hp | Hp].
  - unfold positive_action; rewrite Rmax_left by lra; field; nra.
  - unfold positive_action; rewrite Rmax_right by lra; field; nra.
Qed.

(* A denominator-free absorption argument.  The square-root form below is
   only a convenience wrapper.  Signed replenishment r is NOT assumed >=0. *)
Theorem NSAR10_SIGNED_GRAM_ABSORPTION : forall Y Vend V Q Z r L c Z0 s : R,
  0 <= Y -> 0 <= Vend -> 0 <= V -> 0 <= Q -> 0 <= Z ->
  0 <= L -> 0 <= c -> 0 <= Z0 -> 0 <= s -> s*s = L*Z0 ->
  Q <= L -> Z <= c*Y+Z0 -> r*r <= Q*Z -> Vend+Y <= V+r ->
  Y <= 2*V+2*s+c*L.
Proof.
  intros Y Vend V Q Z r L c Z0 s HY HVend HV HQ HZ HL Hc HZ0 Hs Hs2
    HQL Hcap Hgram Hbal.
  assert (Hp1 : 0 <= (L-Q)*Z) by (apply Rmult_le_pos; lra).
  assert (Hp2 : 0 <= L*(c*Y+Z0-Z)) by (apply Rmult_le_pos; lra).
  assert (Hr2 : r*r <= (c*L)*Y+s*s) by nra.
  assert (HC : 0 <= c*L) by (apply Rmult_le_pos; assumption).
  set (t := (Y+c*L)/2+s).
  assert (Ht : 0 <= t) by (unfold t; lra).
  assert (Hsq : 0 <= (Y-c*L)*(Y-c*L)).
  { exact (Rle_0_sqr (Y-c*L)). }
  assert (Hprod : 0 <= (Y+c*L)*s) by (apply Rmult_le_pos; lra).
  assert (Ht2 : (c*L)*Y+s*s <= t*t) by (unfold t; nra).
  assert (Hr : r <= t) by nra.
  unfold t in Hr; lra.
Qed.

Definition action_bound (V L c Z0 : R) := 2*V+2*sqrt (L*Z0)+c*L.

Lemma action_bound_nonneg : forall V L c Z0,
  0 <= V -> 0 <= L -> 0 <= c -> 0 <= action_bound V L c Z0.
Proof.
  intros; unfold action_bound; pose proof (sqrt_pos (L*Z0)).
  assert (0 <= c*L) by (apply Rmult_le_pos; assumption); lra.
Qed.

Theorem NSAR11_EXPLICIT_ACTION_BOUND : forall Y Vend V Q Z r L c Z0 : R,
  0 <= Y -> 0 <= Vend -> 0 <= V -> 0 <= Q -> 0 <= Z ->
  0 <= L -> 0 <= c -> 0 <= Z0 ->
  Q <= L -> Z <= c*Y+Z0 -> r*r <= Q*Z -> Vend+Y <= V+r ->
  Y <= action_bound V L c Z0.
Proof.
  intros Y Vend V Q Z r L c Z0 HY HVend HV HQ HZ HL Hc HZ0 HQL Hcap Hgram Hbal.
  unfold action_bound.
  apply (NSAR10_SIGNED_GRAM_ABSORPTION Y Vend V Q Z r L c Z0 (sqrt (L*Z0)));
    try assumption.
  - apply sqrt_pos.
  - apply sqrt_def; apply Rmult_le_pos; assumption.
Qed.

(* This record is an INTEGRATED ANALYTIC INTERFACE, not a PDE construction.
   Point may be Approximation x PhysicalTime, so constants are common to all
   cutoffs.  The crucial capacity estimate is a SEPARATE premise. *)
Record IntegratedGramLedger (Point : Type) (Y Vend Q Z net : Point -> R)
  (V L : R) : Prop := {
  igl_initial_nonnegative : 0 <= V;
  igl_leray_budget_nonnegative : 0 <= L;
  igl_action_nonnegative : forall p, 0 <= Y p;
  igl_potential_nonnegative : forall p, 0 <= Vend p;
  igl_increment_nonnegative : forall p, 0 <= Q p;
  igl_capacity_nonnegative : forall p, 0 <= Z p;
  igl_increment_budget : forall p, Q p <= L;
  igl_signed_balance : forall p, Vend p+Y p <= V+net p;
  igl_space_time_gram : forall p, net p*net p <= Q p*Z p
}.

Definition ReducedCapacityBound (Point : Type) (Y Z : Point -> R) (c Z0 : R) : Prop :=
  0 <= c /\ 0 <= Z0 /\ forall p, Z p <= c*Y p+Z0.

Theorem NSAR20_UNIFORM_REDUCED_CAPACITY_TO_ACTION : forall Point Y Vend Q Z net V L c Z0,
  IntegratedGramLedger Point Y Vend Q Z net V L ->
  ReducedCapacityBound Point Y Z c Z0 ->
  forall p, Y p <= action_bound V L c Z0.
Proof.
  intros Point Y Vend Q Z net V L c Z0 Hledger Hcapacity p.
  destruct Hledger as [HV HL HY HP HQ HZ HB Hbalance Hgram].
  destruct Hcapacity as [Hc [HZ0 Hcap]].
  apply (NSAR11_EXPLICIT_ACTION_BOUND (Y p) (Vend p) V (Q p) (Z p) (net p) L c Z0);
    auto.
Qed.

(* A finite quadrature/step version is actually CONSTRUCTED below.
   No Riemann/Bochner integral or infinite summation is silently substituted. *)
Lemma finite_signed_balance : forall m w A P r,
  (forall i, (i<m)%nat -> P (S i)+w i*A i <= P i+w i*r i) ->
  P m+sum m (fun i => w i*A i) <= P O+sum m (fun i => w i*r i).
Proof.
  intros m w A P r H.
  assert (Hsum : sum m (fun i => (P (S i)-P i)+w i*A i) <=
    sum m (fun i => w i*r i)).
  { apply sum_mono; intros i Hi; specialize (H i Hi); lra. }
  rewrite sum_add, (sum_telescoping m P) in Hsum; lra.
Qed.

Theorem NSAR30_FINITE_GRAM_SPACE_TIME_BOUND : forall m n w
  (d f n0 n1 : nat -> Vec),
  (forall i, (i<m)%nat -> 0 <= w i) ->
  (forall i, (i<m)%nat -> dot n (d i) (n0 i) = 0) ->
  (forall i, (i<m)%nat -> dot n (d i) (n1 i) = 0) ->
  let Rr := sum m (fun i => w i*dot n (d i) (f i)) in
  let Q := sum m (fun i => w i*norm2 n (d i)) in
  let Z := sum m (fun i => w i*reduced_capacity n (f i) (n0 i) (n1 i)) in
  Rr*Rr <= Q*Z.
Proof.
  intros m n w d f n0 n1 Hw H0 H1; cbv zeta.
  apply (NSKA20_WEIGHTED_CAUCHY m w (fun i => norm2 n (d i))
    (fun i => reduced_capacity n (f i) (n0 i) (n1 i))
    (fun i => dot n (d i) (f i))).
  - exact Hw.
  - intros; apply norm2_nonneg.
  - intros; apply norm2_nonneg.
  - intros; apply NSGG20_RANK_SAFE_SCHUR_ACTION_BOUND; auto.
Qed.

Theorem NSAR40_FINITE_GRAM_LEDGER_ACTION_BOUND : forall m n w A P
  (d f n0 n1 : nat -> Vec) L c Z0,
  0 <= P O -> 0 <= P m -> 0 <= L -> 0 <= c -> 0 <= Z0 ->
  (forall i, (i<m)%nat -> 0 <= w i) ->
  (forall i, (i<m)%nat -> 0 <= A i) ->
  (forall i, (i<m)%nat -> dot n (d i) (n0 i) = 0) ->
  (forall i, (i<m)%nat -> dot n (d i) (n1 i) = 0) ->
  (forall i, (i<m)%nat -> P (S i)+w i*A i <= P i+w i*dot n (d i) (f i)) ->
  sum m (fun i => w i*norm2 n (d i)) <= L ->
  sum m (fun i => w i*reduced_capacity n (f i) (n0 i) (n1 i)) <=
    c*sum m (fun i => w i*A i)+Z0 ->
  sum m (fun i => w i*A i) <= action_bound (P O) L c Z0.
Proof.
  intros m n w A P d f n0 n1 L c Z0 HP0 HPm HL Hc HZ0 Hw HA H0 H1 Hstep Hbudget Hcap.
  apply (NSAR11_EXPLICIT_ACTION_BOUND
    (sum m (fun i => w i*A i)) (P m) (P O)
    (sum m (fun i => w i*norm2 n (d i)))
    (sum m (fun i => w i*reduced_capacity n (f i) (n0 i) (n1 i)))
    (sum m (fun i => w i*dot n (d i) (f i))) L c Z0).
  - apply sum_nonneg; intros; apply Rmult_le_pos; auto.
  - exact HPm.
  - exact HP0.
  - apply sum_nonneg; intros; apply Rmult_le_pos; [auto | apply norm2_nonneg].
  - apply sum_nonneg; intros; apply Rmult_le_pos; [auto | apply norm2_nonneg].
  - exact HL.
  - exact Hc.
  - exact HZ0.
  - exact Hbudget.
  - exact Hcap.
  - apply NSAR30_FINITE_GRAM_SPACE_TIME_BOUND; assumption.
  - apply finite_signed_balance; exact Hstep.
Qed.

(* A scalar expression of the ordinary energy-funded time budget.
   The integrated ladder and Leray identities are supplied explicitly. *)
Theorem NSAR50_LADDER_PLUS_LERAY_BUDGET : forall E0 nu D Q : R,
  0 < nu -> 0 <= D -> 2*Q <= D -> 2*nu*D <= E0 -> Q <= E0/(4*nu).
Proof.
  intros E0 nu D Q Hnu HD HQ HE.
  apply (Rmult_le_reg_l (4*nu)); [nra |].
  replace ((4*nu)*(E0/(4*nu))) with E0 by (field; nra).
  nra.
Qed.

(* Algebraic countermodel, NOT an NSE solution.  It proves that the
   capacity premise is substantive even after all other ledger fields. *)
Theorem NSAR90_LEDGER_WITHOUT_CAPACITY_CAN_HAVE_UNBOUNDED_ACTION :
  IntegratedGramLedger R (fun x => x*x) (fun _ => 0) (fun _ => 1)
    (fun x => (x*x)*(x*x)) (fun x => x*x) 0 1 /\
  ~ (exists C : R, forall x : R, x*x <= C).
Proof.
  split.
  - constructor.
    + lra.
    + lra.
    + intro x; exact (Rle_0_sqr x).
    + intro x; lra.
    + intro x; lra.
    + intro x; exact (Rle_0_sqr (x*x)).
    + intro x; lra.
    + intro x; lra.
    + intro x; nra.
  - intros [C HC].
    specialize (HC (C+1)).
    assert (Hsq : 0 <= (C+1/2)*(C+1/2)).
    { exact (Rle_0_sqr (C+1/2)). }
    nra.
Qed.

End NSE_SCHUR_ACTION_LEDGER.
