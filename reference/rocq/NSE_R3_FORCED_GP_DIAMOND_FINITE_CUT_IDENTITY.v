From Stdlib Require Import Reals Ranalysis1 Lra Psatz Field Lia String.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_native_kq_ladder_v0_49_3.
Require Import awpi_nse_schur_action_ledger_v0_49_3.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.

Module NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.
Import NSE_KQ_FINITE_ALGEBRA NSE_NATIVE_KQ_LADDER.
Import NSE_SCHUR_ACTION_LEDGER NSE_CONTINUOUS_TIME_CALCULUS.
Module GM := NSE_GALERKIN_MODAL_CALCULUS.
Open Scope R_scope.

(* A finite forced modal NSE.  F is the projected external force on the
   finite carrier.  No full critical-space test is used here. *)
Definition forced_modal_rhs n (lambda : Vec) (T : GM.CoefficientTable)
  (nu : R) (F u : Vec) : Vec :=
  fun i => -nu * lambda i * u i - GM.modal_source n T u i + F i.

Definition ForcedModalPath n lambda T nu (F : R -> Vec)
  a b (u : R -> Vec) : Prop :=
  forall t, InTime a b t -> forall i, (i<n)%nat ->
    derivable_pt_lim (fun s => u s i) t
      (forced_modal_rhs n lambda T nu (F t) (u t) i).

Definition forcing_current n (s F u : Vec) : R :=
  dot n F (mul s u).

Lemma FC00_FORCING_CURRENT_UNIT_CUT : forall n F u,
  forcing_current n (fun _ => 1) F u = dot n F u.
Proof.
  intros n F u; unfold forcing_current.
  apply dot_ext_r; intros i Hi; unfold mul; ring.
Qed.

Theorem FC10_FORCED_MODAL_ODE_GIVES_EXACT_CUT_DERIVATIVE :
  forall n lambda T nu F a b u s t,
    ForcedModalPath n lambda T nu F a b u -> InTime a b t ->
    derivable_pt_lim (fun r => GM.cut_mass n s (u r)) t
      (2*GM.cut_current n T s (u t)
       -2*nu*GM.cut_dissipation n lambda s (u t)
       +2*forcing_current n s (F t) (u t)).
Proof.
  intros n lambda T nu F a b u s t Hpath Ht.
  pose proof (NSCT40_FINITE_WEIGHTED_ENERGY_DERIVATIVE n s u
    (forced_modal_rhs n lambda T nu (F t) (u t)) t (Hpath t Ht)) as HD.
  assert (He :
    sum n (fun i => s i*u t i*forced_modal_rhs n lambda T nu (F t) (u t) i) =
      -nu*GM.cut_dissipation n lambda s (u t)
      + GM.cut_current n T s (u t)
      + forcing_current n s (F t) (u t)).
  {
    unfold forced_modal_rhs, GM.cut_dissipation, GM.cut_current,
      forcing_current, dot, mul.
    transitivity (sum n (fun i =>
      (-nu)*(s i*lambda i*u t i*u t i)
      - GM.modal_source n T (u t) i*(s i*u t i)
      + F t i*(s i*u t i))).
    - apply sum_ext; intros; ring.
    - rewrite sum_add, sum_sub, sum_scale; ring.
  }
  rewrite He in HD.
  replace
    (2*(-nu*GM.cut_dissipation n lambda s (u t)
       +GM.cut_current n T s (u t)
       +forcing_current n s (F t) (u t)))
    with
    (2*GM.cut_current n T s (u t)
     -2*nu*GM.cut_dissipation n lambda s (u t)
     +2*forcing_current n s (F t) (u t)) in HD by ring.
  exact HD.
Qed.

Theorem FC11_FORCED_MODAL_ODE_GIVES_EXACT_NONNEGATIVE_CUT_IDENTITY :
  forall n lambda T nu F a b u s t,
    (forall i, (i<n)%nat -> 0 <= lambda i) ->
    (forall i, (i<n)%nat -> 0 <= s i) ->
    ForcedModalPath n lambda T nu F a b u -> InTime a b t ->
    0 <= GM.cut_dissipation n lambda s (u t) /\
    derivable_pt_lim (fun r => GM.cut_mass n s (u r)) t
      (2*GM.cut_current n T s (u t)
       -2*nu*GM.cut_dissipation n lambda s (u t)
       +2*forcing_current n s (F t) (u t)).
Proof.
  intros n lambda T nu F a b u s t Hlam Hs Hpath Ht; split.
  - apply GM.cut_dissipation_nonnegative; assumption.
  - exact (@FC10_FORCED_MODAL_ODE_GIVES_EXACT_CUT_DERIVATIVE
      n lambda T nu F a b u s t Hpath Ht).
Qed.

Theorem FC20_FORCED_MODAL_ODE_GIVES_EXACT_GLOBAL_ENERGY_DERIVATIVE :
  forall n lambda T nu F a b u t,
    GM.SkewTable n T ->
    ForcedModalPath n lambda T nu F a b u -> InTime a b t ->
    derivable_pt_lim (fun r => norm2 n (u r)) t
      (-2*nu*spectral_energy n lambda (u t) + 2*dot n (F t) (u t)).
Proof.
  intros n lambda T nu F a b u t Hskew Hpath Ht.
  pose proof (FC10_FORCED_MODAL_ODE_GIVES_EXACT_CUT_DERIVATIVE
    n lambda T nu F a b u (fun _ => 1) t Hpath Ht) as HD.
  rewrite (GM.unit_cut_current n T (u t) Hskew), GM.unit_cut_dissipation,
    FC00_FORCING_CURRENT_UNIT_CUT in HD.
  replace (2*0 - 2*nu*spectral_energy n lambda (u t) + 2*dot n (F t) (u t))
    with (-2*nu*spectral_energy n lambda (u t) + 2*dot n (F t) (u t)) in HD by ring.
  exact (derivable_pt_lim_ext
    (fun r => GM.cut_mass n (fun _ => 1) (u r))
    (fun r => norm2 n (u r)) t
    (-2*nu*spectral_energy n lambda (u t) + 2*dot n (F t) (u t))
    (fun r => GM.unit_cut_mass n (u r)) HD).
Qed.

(* The finite-cut route is the non-circular entrance: an actual LH solution
   only needs to realize these finite projected ODEs.  A full critical test
   A^(1/2)u is not assumed at this stage. *)
Definition UniformFiniteCutRealization
  (Cut : Type) (Realizes : Cut -> Prop) : Prop :=
  forall c : Cut, Realizes c.

Definition UniformFiniteCutBound
  (Cut : Type) (critical_mass : Cut -> R) : Prop :=
  exists B : R, forall c : Cut, critical_mass c <= B.

Definition FullCriticalLimitReadout
  (Cut : Type) (critical_mass : Cut -> R) (full_mass : R) : Prop :=
  (forall c : Cut, critical_mass c <= full_mass) /\
  (forall B : R, (forall c : Cut, critical_mass c <= B) -> full_mass <= B).

Theorem FC30_UNIFORM_FINITE_CUT_BOUND_CONTROLS_FULL_CRITICAL_READOUT :
  forall (Cut : Type) (critical_mass : Cut -> R) (full_mass : R),
    FullCriticalLimitReadout Cut critical_mass full_mass ->
    UniformFiniteCutBound Cut critical_mass ->
    exists B : R, full_mass <= B.
Proof.
  intros Cut critical_mass full_mass Hread Hbound.
  destruct Hread as [_ Hleast].
  destruct Hbound as [B HB].
  exists B; apply Hleast; exact HB.
Qed.

Definition STATUS : Prop := True.

End NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.

Print NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.FC10_FORCED_MODAL_ODE_GIVES_EXACT_CUT_DERIVATIVE.
Print NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.FC20_FORCED_MODAL_ODE_GIVES_EXACT_GLOBAL_ENERGY_DERIVATIVE.
Print NSE_R3_FORCED_GP_DIAMOND_FINITE_CUT_IDENTITY.FC30_UNIFORM_FINITE_CUT_BOUND_CONTROLS_FULL_CRITICAL_READOUT.
