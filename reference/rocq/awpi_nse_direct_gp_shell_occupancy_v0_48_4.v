From Stdlib Require Import Reals Lra Psatz String.
Require Import awpi_nse_finite_shell_algebra_v0_48_4.
Require Import awpi_nse_shell_occupancy_algebra_v0_48_4.
Require Import awpi_nse_scalar_comparison_v0_48_4.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.
Require Import awpi_nse_direct_gp_action_m7_chain_v0_47_0.

Module NSE_DIRECT_GP_SHELL_OCCUPANCY.
Import NSE_FINITE_SHELL_ALGEBRA NSE_SHELL_OCCUPANCY_ALGEBRA
       NSE_SCALAR_COMPARISON.
Module DG := NSE_DIRECT_GP_ACTION_M7_CHAIN.
Module M7 := NSE_GP_TO_M7_SPINE.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

Record ShellEvolution : Type := {
  ev_count : nat;
  ev_A : R -> nat -> R;
  ev_U : R -> nat -> R;
  ev_E : R -> R;
  ev_D : R -> R;
  ev_G : R -> R;
  ev_Phi : R -> R;
  ev_Edot : R -> R;
  ev_GI : R -> R;
  ev_DI : R -> R;
  ev_VI : R -> R;
  ev_JI : R -> R;
  ev_C : R -> R
}.

Definition threshold (nu : R) := nu/128.
Definition crowd_rate nu cap (d : ShellEvolution) t :=
  shell_unpaid (ev_A d t) (ev_U d t) (threshold nu) cap (ev_count d)
  / (4*threshold nu).
Definition action_density nu theta (d : ShellEvolution) t :=
  if Rlt_dec 0 (ev_D d t) then
    pos (ev_Phi d t-theta*nu*ev_D d t)*
    pos (ev_Phi d t-theta*nu*ev_D d t)/(ev_D d t)
  else 0.
Definition eta nu theta := (1-theta)*nu.
Definition total_energy nu (d : ShellEvolution) t := ev_E d t+nu*ev_DI d t.
Definition coefficient nu cap (d : ShellEvolution) t :=
  (2304*cap/nu)*ev_G d t+72*crowd_rate nu cap d t.
Definition coefficient_primitive nu cap (d : ShellEvolution) t :=
  (2304*cap/nu)*ev_GI d t+72*ev_VI d t.
Definition action_budget cs nu theta B := cs*cs*B*B/((1-theta)*nu*nu).

(* This record is the EXPLICIT analytic seam. No field states M7, a
   critical-energy bound, or Gronwall's conclusion. Its scalar derivative
   and spectral/source identities must still be realized for the actual
   Galerkin NSE. The crowded primitive budget is a separate hypothesis
   of the terminal theorems, not hidden in this record. *)
Record EvolutionBindings (nu cap theta cs E0 M0 T : R)
  (d : ShellEvolution) : Prop := {
  eb_shells : forall t, within T t -> forall j,
    0 <= ev_A d t j /\ 0 <= ev_U d t j /\
    (ev_U d t j=0 -> ev_A d t j=0);
  eb_nonnegative : forall t, within T t ->
    0 <= ev_E d t /\ 0 <= ev_D d t /\ 0 <= ev_G d t;
  eb_spectral : forall t, within T t ->
    shell_E (ev_U d t) (ev_count d) <= ev_E d t /\
    shell_D (ev_U d t) (ev_count d) <= ev_D d t /\
    shell_G (ev_U d t) (ev_count d) <= ev_G d t;
  eb_flux : forall t, within T t ->
    Rabs (ev_Phi d t) <= triad_majorant (ev_A d t) (ev_U d t) (ev_count d);
  eb_balance : forall t, within T t ->
    ev_Edot d t/2+nu*ev_D d t=ev_Phi d t;
  eb_interpolation : forall t, within T t ->
    ev_G d t*ev_G d t <= ev_E d t*ev_D d t;
  eb_source : forall t, within T t ->
    ev_Phi d t*ev_Phi d t <= cs*cs*ev_G d t*ev_G d t*ev_D d t;
  eb_Eder : forall t, within T t ->
    derivable_pt_lim (ev_E d) t (ev_Edot d t);
  eb_GIder : forall t, within T t ->
    derivable_pt_lim (ev_GI d) t (ev_G d t);
  eb_DIder : forall t, within T t ->
    derivable_pt_lim (ev_DI d) t (ev_D d t);
  eb_VIder : forall t, within T t ->
    derivable_pt_lim (ev_VI d) t (crowd_rate nu cap d t);
  eb_JIder : forall t, within T t ->
    derivable_pt_lim (ev_JI d) t (ev_G d t*ev_G d t);
  eb_Cder : forall t, within T t ->
    derivable_pt_lim (ev_C d) t (action_density nu theta d t/eta nu theta);
  eb_initial : ev_E d 0 <= E0 /\ ev_GI d 0=0 /\ ev_DI d 0=0 /\
    ev_VI d 0=0 /\ ev_JI d 0=0 /\ ev_C d 0=0;
  eb_kinetic : forall t, within T t -> 2*nu*ev_GI d t <= M0
}.
Arguments eb_shells {nu cap theta cs E0 M0 T d} _ _ _ _.
Arguments eb_nonnegative {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_spectral {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_flux {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_balance {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_interpolation {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_source {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_Eder {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_GIder {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_DIder {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_VIder {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_JIder {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_Cder {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_kinetic {nu cap theta cs E0 M0 T d} _ _ _.
Arguments eb_initial {nu cap theta cs E0 M0 T d} _.

Lemma NSOA00_ETA_POS : forall nu theta,
  0 < nu -> theta < 1 -> 0 < eta nu theta.
Proof. intros; unfold eta; nra. Qed.

Lemma NSOA01_CROWD_RATE_NONNEG : forall nu cap d t,
  0 < nu -> 0 <= crowd_rate nu cap d t.
Proof.
  intros. unfold crowd_rate. apply NSFA08_DIV_NONNEG.
  - unfold shell_unpaid; apply NSFA02_TOTAL_NONNEG; intros; apply NSSO07_UNPAID_NONNEG.
  - unfold threshold; lra.
Qed.

Lemma NSOA02_CROWD_RATE_IS_COVERED : forall nu cap d t,
  0 < nu -> 0 <= cap ->
  crowd_rate nu cap d t <=
    shell_crowded (ev_A d t) (ev_U d t) (threshold nu) cap (ev_count d).
Proof.
  intros nu cap d t Hnu Hcap.
  assert (Hsum : shell_unpaid (ev_A d t) (ev_U d t)
      (threshold nu) cap (ev_count d) <=
    4*threshold nu*shell_crowded (ev_A d t) (ev_U d t)
      (threshold nu) cap (ev_count d)).
  { unfold shell_unpaid, shell_crowded. rewrite <- NSFA04_TOTAL_SCALE.
    apply NSFA01_TOTAL_LE. intros j Hj.
    apply NSSO12_HARD_REMAINDER_COVERS_DEBT.
    - apply NSFA20_WAVE_POS.
    - unfold threshold; lra.
    - exact Hcap. }
  assert (Hden : 0 < 4*threshold nu) by (unfold threshold; lra).
  assert (Heq : (4*threshold nu)*crowd_rate nu cap d t=
    shell_unpaid (ev_A d t) (ev_U d t) (threshold nu) cap (ev_count d)).
  { unfold crowd_rate; field; repeat split; lra. }
  nra.
Qed.

Lemma NSOA03_ACTION_NONNEG : forall nu theta d t,
  0 <= action_density nu theta d t.
Proof.
  intros. unfold action_density.
  destruct (Rlt_dec 0 (ev_D d t)) as [HD|HD]; [|lra].
  apply NSFA08_DIV_NONNEG; [|lra].
  pose proof (Rle_0_sqr (pos (ev_Phi d t-theta*nu*ev_D d t))).
  unfold Rsqr in *; lra.
Qed.

Theorem NSOA10_FINITE_CLASSIFICATION_TO_ODE :
  forall nu cap theta cs E0 M0 T d,
  0 < nu -> 0 <= cap -> EvolutionBindings nu cap theta cs E0 M0 T d ->
  forall t, within T t ->
  ev_Edot d t+nu*ev_D d t <= coefficient nu cap d t*ev_E d t.
Proof.
  intros nu cap theta cs E0 M0 T d Hnu Hcap Hb t Ht.
  destruct (eb_nonnegative Hb t Ht) as [HE [HD HG]].
  destruct (eb_spectral Hb t Ht) as [HSE [HSD HSG]].
  assert (HU : forall j, 0 <= ev_U d t j).
  { intro j; exact (proj1 (proj2 (eb_shells Hb t Ht j))). }
  pose proof (NSSO41_ACTUAL_FLUX_SEAM_TO_64_36
    (ev_Phi d t) (ev_A d t) (ev_U d t) (threshold nu) (ev_count d)
    (ev_E d t) (ev_D d t) ltac:(unfold threshold; lra)
    HU HSE HSD (eb_flux Hb t Ht)) as HF.
  pose proof (NSSO20_FINITE_CONTINUOUS_SPLIT (ev_A d t) (ev_U d t)
    (threshold nu) cap (ev_count d)) as HP.
  pose proof (Rmult_le_compat_l cap _ _ Hcap HSG) as HGpaid.
  assert (HV : 4*threshold nu*crowd_rate nu cap d t=
    shell_unpaid (ev_A d t) (ev_U d t) (threshold nu) cap (ev_count d)).
  { unfold crowd_rate; field; repeat split; unfold threshold; lra. }
  unfold coefficient. apply (NSSO51_CLASSIFIED_DIFFERENTIAL_INEQUALITY
    nu cap (ev_E d t) (ev_D d t) (ev_G d t)
    (shell_L (ev_A d t) (threshold nu) (ev_count d))
    (crowd_rate nu cap d t) (ev_Phi d t) (ev_Edot d t));
    try assumption.
  - exact (eb_balance Hb t Ht).
  - unfold threshold in *; lra.
Qed.

Lemma NSOA11_DISSIPATION_PRIMITIVE_NONNEG :
  forall nu cap theta cs E0 M0 T d,
  EvolutionBindings nu cap theta cs E0 M0 T d ->
  forall t, within T t -> 0 <= ev_DI d t.
Proof.
  intros nu cap theta cs E0 M0 T d Hb t Ht.
  destruct (eb_initial Hb) as [H0 [HG0 [HD0 Hrest]]].
  apply (NSCP01_NONNEG_PRIMITIVE (ev_DI d) (ev_D d) T t);
    try assumption.
  - exact (eb_DIder Hb).
  - intros x Hx; exact (proj1 (proj2 (eb_nonnegative Hb x Hx))).
Qed.

Theorem NSOA20_ACTUAL_SCALAR_GRONWALL :
  forall nu cap theta cs E0 M0 T d,
  0 < nu -> 0 <= cap -> EvolutionBindings nu cap theta cs E0 M0 T d ->
  forall t, within T t ->
  total_energy nu d t <= E0*exp (coefficient_primitive nu cap d t).
Proof.
  intros nu cap theta cs E0 M0 T d Hnu Hcap Hb t Ht.
  destruct (eb_initial Hb) as [HE0 [HG0 [HD0 [HV0 [HJ0 HC0]]]]].
  apply (NSCP10_INTEGRATING_FACTOR_GRONWALL
    (total_energy nu d) (fun x => ev_Edot d x+nu*ev_D d x)
    (coefficient_primitive nu cap d) (coefficient nu cap d) T t E0).
  - exact Ht.
  - unfold coefficient_primitive; rewrite HG0, HV0; ring.
  - unfold total_energy; rewrite HD0; nra.
  - intros x Hx; unfold total_energy.
    apply derivable_pt_lim_plus.
    + exact (eb_Eder Hb x Hx).
    + apply derivable_pt_lim_scal. exact (eb_DIder Hb x Hx).
  - intros x Hx; unfold coefficient_primitive, coefficient.
    apply derivable_pt_lim_plus; apply derivable_pt_lim_scal.
    + exact (eb_GIder Hb x Hx).
    + exact (eb_VIder Hb x Hx).
  - intros x Hx.
    pose proof (NSOA10_FINITE_CLASSIFICATION_TO_ODE
      nu cap theta cs E0 M0 T d Hnu Hcap Hb x Hx) as Hode.
    pose proof (NSOA11_DISSIPATION_PRIMITIVE_NONNEG
      nu cap theta cs E0 M0 T d Hb x Hx) as HDI.
    assert (Hq : 0 <= coefficient nu cap d x).
    { unfold coefficient.
      assert (Hc : 0 <= 2304*cap/nu) by (apply NSFA08_DIV_NONNEG; lra).
      pose proof (proj2 (proj2 (eb_nonnegative Hb x Hx))) as HG.
      pose proof (NSOA01_CROWD_RATE_NONNEG nu cap d x Hnu) as HV.
      nra. }
    assert (Hef : ev_E d x <= total_energy nu d x).
    { unfold total_energy; nra. }
    pose proof (Rmult_le_compat_l (coefficient nu cap d x) _ _ Hq Hef).
    lra.
Qed.

Theorem NSOA21_CROWDED_BUDGET_TO_CRITICAL_ENERGY :
  forall nu cap theta cs E0 M0 T Ustar d,
  0 < nu -> 0 <= cap -> 0 <= E0 ->
  EvolutionBindings nu cap theta cs E0 M0 T d ->
  (forall x, within T x -> ev_VI d x <= Ustar) ->
  forall t, within T t ->
  total_energy nu d t <= energy_budget nu cap M0 E0 Ustar.
Proof.
  intros nu cap theta cs E0 M0 T Ustar d Hnu Hcap HE0 Hb HV t Ht.
  apply (NSCP13_ENVELOPE_TO_UNIFORM_BOUND
    nu cap M0 E0 Ustar (ev_GI d t) (ev_VI d t) (total_energy nu d t));
    try assumption.
  - exact (eb_kinetic Hb t Ht).
  - exact (HV t Ht).
  - exact (NSOA20_ACTUAL_SCALAR_GRONWALL
      nu cap theta cs E0 M0 T d Hnu Hcap Hb t Ht).
Qed.

Lemma NSOA30_ACTION_FROM_SOURCE : forall nu cap theta cs E0 M0 T d,
  0 < nu -> 0 <= theta ->
  EvolutionBindings nu cap theta cs E0 M0 T d ->
  forall t, within T t ->
  action_density nu theta d t <= cs*cs*ev_G d t*ev_G d t.
Proof.
  intros nu cap theta cs E0 M0 T d Hnu Hth Hb t Ht.
  pose proof (eb_source Hb t Ht) as Hsource.
  unfold action_density. destruct (Rlt_dec 0 (ev_D d t)) as [HD|HD].
  - pose proof (NSFA18_RESISTANT_SQUARE (ev_Phi d t) nu theta (ev_D d t)
      (Rlt_le _ _ Hnu) Hth (Rlt_le _ _ HD)) as Hsq.
    assert (Hcancel :
      (pos (ev_Phi d t-theta*nu*ev_D d t)*
       pos (ev_Phi d t-theta*nu*ev_D d t)/ev_D d t)*ev_D d t =
       pos (ev_Phi d t-theta*nu*ev_D d t)*
       pos (ev_Phi d t-theta*nu*ev_D d t)).
    { field; repeat split; lra. }
    nra.
  - pose proof (Rle_0_sqr (cs*ev_G d t)); unfold Rsqr in *; nra.
Qed.

Lemma NSOA31_ACTION_PRIMITIVE_COMPARISON :
  forall nu cap theta cs E0 M0 T d,
  0 < nu -> 0 <= theta -> theta < 1 ->
  EvolutionBindings nu cap theta cs E0 M0 T d ->
  forall t, within T t ->
  ev_C d t <= (cs*cs/eta nu theta)*ev_JI d t.
Proof.
  intros nu cap theta cs E0 M0 T d Hnu Hth Hth1 Hb t Ht.
  destruct (eb_initial Hb) as [HE0 [HG0 [HD0 [HV0 [HJ0 HC0]]]]].
  apply (NSCP20_PRIMITIVE_COMPARISON (ev_C d)
    (fun x => action_density nu theta d x/eta nu theta)
    (ev_JI d) (fun x => ev_G d x*ev_G d x)
    T t (cs*cs/eta nu theta)); try assumption.
  - exact (eb_Cder Hb).
  - exact (eb_JIder Hb).
  - intros x Hx.
    pose proof (NSOA30_ACTION_FROM_SOURCE
      nu cap theta cs E0 M0 T d Hnu Hth Hb x Hx) as Ha.
    assert (Hi : 0 <= /eta nu theta).
    { left; apply Rinv_0_lt_compat; apply NSOA00_ETA_POS; assumption. }
    pose proof (Rmult_le_compat_l (/eta nu theta) _ _ Hi Ha) as HM.
    unfold Rdiv; nra.
Qed.

Lemma NSOA32_SQUARE_PRIMITIVE_COMPARISON :
  forall nu cap theta cs E0 M0 T d B,
  EvolutionBindings nu cap theta cs E0 M0 T d ->
  (forall x, within T x -> ev_E d x <= B) ->
  forall t, within T t -> ev_JI d t <= B*ev_DI d t.
Proof.
  intros nu cap theta cs E0 M0 T d B Hb HE t Ht.
  destruct (eb_initial Hb) as [HE0 [HG0 [HD0 [HV0 [HJ0 HC0]]]]].
  apply (NSCP20_PRIMITIVE_COMPARISON (ev_JI d)
    (fun x => ev_G d x*ev_G d x)
    (ev_DI d) (ev_D d) T t B); try assumption.
  - exact (eb_JIder Hb).
  - exact (eb_DIder Hb).
  - intros x Hx.
    pose proof (eb_interpolation Hb x Hx) as Hi.
    pose proof (proj1 (proj2 (eb_nonnegative Hb x Hx))) as HD.
    pose proof (Rmult_le_compat_r (ev_D d x) _ _ HD (HE x Hx)) as HM.
    lra.
Qed.

Theorem NSOA40_BOUND_THE_ORIGINAL_ACTION :
  forall nu cap theta cs E0 M0 T Ustar d,
  0 < nu -> 0 <= cap -> 0 <= E0 -> 0 <= theta -> theta < 1 ->
  EvolutionBindings nu cap theta cs E0 M0 T d ->
  (forall x, within T x -> ev_VI d x <= Ustar) ->
  forall t, within T t ->
  ev_C d t <= action_budget cs nu theta (energy_budget nu cap M0 E0 Ustar).
Proof.
  intros nu cap theta cs E0 M0 T Ustar d Hnu Hcap HE0 Hth Hth1 Hb HV t Ht.
  set (B := energy_budget nu cap M0 E0 Ustar).
  assert (HB : 0 <= B).
  { unfold B; apply NSCP12_ENERGY_BUDGET_NONNEG; exact HE0. }
  assert (HF : forall x, within T x -> total_energy nu d x <= B).
  { intros; unfold B; eapply NSOA21_CROWDED_BUDGET_TO_CRITICAL_ENERGY; eauto. }
  assert (HE : forall x, within T x -> ev_E d x <= B).
  { intros x Hx.
    pose proof (NSOA11_DISSIPATION_PRIMITIVE_NONNEG
      nu cap theta cs E0 M0 T d Hb x Hx) as HDI.
    specialize (HF x Hx); unfold total_energy in HF; nra. }
  pose proof (NSOA31_ACTION_PRIMITIVE_COMPARISON
    nu cap theta cs E0 M0 T d Hnu Hth Hth1 Hb t Ht) as HC.
  pose proof (NSOA32_SQUARE_PRIMITIVE_COMPARISON
    nu cap theta cs E0 M0 T d B Hb HE t Ht) as HJ.
  assert (HDI : ev_DI d t <= B/nu).
  { specialize (HF t Ht); unfold total_energy in HF.
    pose proof (proj1 (eb_nonnegative Hb t Ht)) as HEpos.
    assert (Hcancel : nu*(B/nu)=B) by (field; repeat split; lra).
    nra. }
  assert (Hc : 0 <= cs*cs/eta nu theta).
  { apply NSFA08_DIV_NONNEG.
    - pose proof (Rle_0_sqr cs); unfold Rsqr in *; lra.
    - pose proof (NSOA00_ETA_POS nu theta Hnu Hth1); lra. }
  pose proof (Rmult_le_compat_l B _ _ HB HDI) as HBD.
  pose proof (Rmult_le_compat_l (cs*cs/eta nu theta) _ _ Hc HJ) as H1.
  pose proof (Rmult_le_compat_l (cs*cs/eta nu theta) _ _ Hc HBD) as H2.
  assert (Heq : (cs*cs/eta nu theta)*(B*(B/nu))=action_budget cs nu theta B).
  { unfold eta, action_budget; field; repeat split; nra. }
  rewrite Heq in H2. change (ev_C d t <= action_budget cs nu theta B); lra.
Qed.

Lemma NSOA41_ACTION_BUDGET_NONNEG : forall cs nu theta B,
  0 < nu -> theta < 1 -> 0 <= action_budget cs nu theta B.
Proof.
  intros cs nu theta B Hnu Htheta.
  unfold action_budget. apply NSFA08_DIV_NONNEG.
  - replace (cs*cs*B*B) with ((cs*B)*(cs*B)) by ring.
    exact (Rle_0_sqr (cs*B)).
  - apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat.
      * lra.
      * exact Hnu.
    + exact Hnu.
Qed.

Lemma NSOA42_ACTION_MONOTONE : forall nu cap theta cs E0 M0 T d,
  0 < nu -> theta < 1 ->
  EvolutionBindings nu cap theta cs E0 M0 T d ->
  forall s t, within T s -> within T t -> s <= t -> ev_C d s <= ev_C d t.
Proof.
  intros nu cap theta cs E0 M0 T d Hnu Hth Hb s t Hs Ht Hst.
  apply (NSCP02_NONNEG_DERIVATIVE_MONOTONE (ev_C d)
    (fun x => action_density nu theta d x/eta nu theta) T s t);
    try assumption.
  - exact (eb_Cder Hb).
  - intros x Hx; apply NSFA08_DIV_NONNEG.
    + apply NSOA03_ACTION_NONNEG.
    + pose proof (NSOA00_ETA_POS nu theta Hnu Hth); lra.
Qed.

(* Uniform bound -> the SAME mass definition and SAME M7 predicate as
   the frozen v0.47.0 chain. No new substitute M7 is defined. *)
Theorem NSOA80_BOUNDED_ACTION_TO_EXISTING_M7 :
  forall (Reg Time : Type) (C : Reg -> Time -> R)
    (stamp : Time -> R) (cut : nat -> Time) Cmax,
  0 <= Cmax ->
  (forall eps, C eps (cut O)=0) ->
  (forall eps s t, stamp s <= stamp t -> C eps s <= C eps t) ->
  (forall n, stamp (cut n) <= stamp (cut (S n))) ->
  (forall t, exists n, stamp t <= stamp (cut n)) ->
  (forall eps t, C eps t <= Cmax) ->
  (forall eps, M7.GPSequenceM7 (DG.action_increment C cut eps)) /\
  (forall eps, CE.M7ActionCostRealization Time
    (DG.action_increment C cut eps) (C eps)) /\
  (forall eps, DG.action_increment C cut eps O <= Cmax) /\
  (forall eps n, M7.paid_prefix
    (DG.renewal_debt (DG.action_increment C cut eps)) n <= Cmax).
Proof.
  intros Reg Time C stamp cut Cmax HCmax Hzero Hmono Horder Hcofinal Hbound.
  assert (Hmass : forall eps n, 0 <= DG.action_increment C cut eps n).
  { apply (DG.NSDG00_ACTION_INCREMENT_NONNEG Reg Time C stamp cut); assumption. }
  assert (Hprefix : forall eps n,
    M7.resistant_prefix (DG.action_increment C cut eps) n <= Cmax).
  { intros. rewrite (DG.NSDG01_ACTION_PREFIX_TELESCOPES Reg Time C cut Hzero eps n).
    apply Hbound. }
  split.
  - intro eps; exists Cmax; split; [exact HCmax|apply Hprefix].
  - split.
    + exact (DG.NSDG02_TIME_COFINALITY_CONSTRUCTS_ACTION_REALIZATION
        Reg Time C stamp cut Hzero Hmono Hcofinal).
    + split.
      * intro eps. specialize (Hprefix eps (S O)).
        change (0+DG.action_increment C cut eps O <= Cmax) in Hprefix. lra.
      * intros eps n.
        pose proof (DG.NSDG14_DEBT_PREFIX_AT_MOST_SHIFTED_MASS_PREFIX
          (DG.action_increment C cut eps) (Hmass eps) n) as HP.
        pose proof (Hprefix eps (S n)). pose proof (Hmass eps O). lra.
Qed.

Theorem NSOA90_UNIFORM_OCCUPANCY_ACTION_CHAIN :
  forall (Reg : Type) (ev : Reg -> ShellEvolution)
    nu cap theta cs E0 M0 T Ustar,
  0 < nu -> 0 <= cap -> 0 <= E0 -> 0 <= theta -> theta < 1 ->
  (forall eps, EvolutionBindings nu cap theta cs E0 M0 T (ev eps)) ->
  (forall eps t, within T t -> ev_VI (ev eps) t <= Ustar) ->
  forall eps t, within T t ->
  total_energy nu (ev eps) t <= energy_budget nu cap M0 E0 Ustar /\
  ev_C (ev eps) t <= action_budget cs nu theta (energy_budget nu cap M0 E0 Ustar).
Proof.
  intros Reg ev nu cap theta cs E0 M0 T Ustar Hnu Hcap HE0 Hth Hth1 Hb HV eps t Ht.
  split.
  - eapply NSOA21_CROWDED_BUDGET_TO_CRITICAL_ENERGY; eauto.
  - eapply NSOA40_BOUND_THE_ORIGINAL_ACTION; eauto.
Qed.

Theorem NSOA99_OCCUPANCY_TO_EXISTING_M7_TERMINAL :
  forall (Reg Time : Type) (ev : Reg -> ShellEvolution)
    (stamp : Time -> R) (cut : nat -> Time)
    nu cap theta cs E0 M0 T Ustar,
  0 < nu -> 0 <= cap -> 0 <= E0 -> 0 <= theta -> theta < 1 ->
  (forall eps, EvolutionBindings nu cap theta cs E0 M0 T (ev eps)) ->
  (forall eps t, within T t -> ev_VI (ev eps) t <= Ustar) ->
  (forall t, within T (stamp t)) ->
  stamp (cut O)=0 ->
  (forall n, stamp (cut n) <= stamp (cut (S n))) ->
  (forall t, exists n, stamp t <= stamp (cut n)) ->
  let C := fun eps t => ev_C (ev eps) (stamp t) in
  let Cmax := action_budget cs nu theta (energy_budget nu cap M0 E0 Ustar) in
  (forall eps, M7.GPSequenceM7 (DG.action_increment C cut eps)) /\
  (forall eps, CE.M7ActionCostRealization Time (DG.action_increment C cut eps) (C eps)) /\
  (forall eps, DG.action_increment C cut eps O <= Cmax) /\
  (forall eps n, M7.paid_prefix (DG.renewal_debt (DG.action_increment C cut eps)) n <= Cmax) /\
  CE.UniformCriticalEnergy (Reg*Time)%type
    (fun rt => ev_E (ev (fst rt)) (stamp (snd rt)))
    (fun rt => ev_DI (ev (fst rt)) (stamp (snd rt))).
Proof.
  intros Reg Time ev stamp cut nu cap theta cs E0 M0 T Ustar
    Hnu Hcap HE0 Hth Hth1 Hb HV Htime Hzero Horder Hcofinal.
  cbv zeta.
  set (B := energy_budget nu cap M0 E0 Ustar).
  set (Cmax := action_budget cs nu theta B).
  set (C := fun eps t => ev_C (ev eps) (stamp t)).
  assert (HCmax : 0 <= Cmax).
  { unfold Cmax; apply NSOA41_ACTION_BUDGET_NONNEG; assumption. }
  assert (HCzero : forall eps, C eps (cut O)=0).
  { intro eps; unfold C; rewrite Hzero.
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (eb_initial (Hb eps))))))). }
  assert (HCmono : forall eps s t, stamp s <= stamp t -> C eps s <= C eps t).
  { intros eps s t Hst; unfold C.
    eapply NSOA42_ACTION_MONOTONE; eauto. }
  assert (HCbound : forall eps t, C eps t <= Cmax).
  { intros eps t; unfold C, Cmax, B.
    eapply NSOA40_BOUND_THE_ORIGINAL_ACTION; eauto. }
  destruct (NSOA80_BOUNDED_ACTION_TO_EXISTING_M7 Reg Time C stamp cut Cmax
    HCmax HCzero HCmono Horder Hcofinal HCbound) as [HM7 [Hreal [Hseed Hpaid]]].
  split; [exact HM7|]. split; [exact Hreal|]. split; [exact Hseed|].
  split; [exact Hpaid|].
  unfold CE.UniformCriticalEnergy.
  exists B, (B/nu).
  assert (HB : 0 <= B).
  { unfold B; apply NSCP12_ENERGY_BUDGET_NONNEG; exact HE0. }
  repeat split.
  - exact HB.
  - apply NSFA08_DIV_NONNEG; lra.
  - intros [eps t]. cbn.
    pose proof (NSOA21_CROWDED_BUDGET_TO_CRITICAL_ENERGY
      nu cap theta cs E0 M0 T Ustar (ev eps) Hnu Hcap HE0 (Hb eps) (HV eps)
      (stamp t) (Htime t)) as HF.
    pose proof (NSOA11_DISSIPATION_PRIMITIVE_NONNEG
      nu cap theta cs E0 M0 T (ev eps) (Hb eps) (stamp t) (Htime t)) as HDI.
    unfold total_energy in HF; unfold B; nra.
  - intros [eps t]. cbn.
    pose proof (NSOA21_CROWDED_BUDGET_TO_CRITICAL_ENERGY
      nu cap theta cs E0 M0 T Ustar (ev eps) Hnu Hcap HE0 (Hb eps) (HV eps)
      (stamp t) (Htime t)) as HF.
    pose proof (proj1 (eb_nonnegative (Hb eps) (stamp t) (Htime t))) as HE.
    unfold total_energy in HF.
    assert (Hcancel : nu*(B/nu)=B) by (field; repeat split; lra).
    unfold B in *; nra.
Qed.

Definition STATUS : string :=
  "NSE_DIRECT_GP_SHELL_OCCUPANCY_V0_48_4_CONDITIONAL_ANALYTIC_SEAM_NO_ADMITTED"%string.
End NSE_DIRECT_GP_SHELL_OCCUPANCY.

Print Assumptions NSE_FINITE_SHELL_ALGEBRA.NSFA40_HELICAL_RESIDUAL_FACTOR.
Print Assumptions NSE_SHELL_OCCUPANCY_ALGEBRA.NSSO21_FINITE_HARD_SPLIT.
Print Assumptions NSE_SHELL_OCCUPANCY_ALGEBRA.NSSO40_FINITE_64_36_MAJORANT.
Print Assumptions NSE_SCALAR_COMPARISON.NSCP10_INTEGRATING_FACTOR_GRONWALL.
Print Assumptions NSE_DIRECT_GP_SHELL_OCCUPANCY.NSOA90_UNIFORM_OCCUPANCY_ACTION_CHAIN.
Print Assumptions NSE_DIRECT_GP_SHELL_OCCUPANCY.NSOA99_OCCUPANCY_TO_EXISTING_M7_TERMINAL.
