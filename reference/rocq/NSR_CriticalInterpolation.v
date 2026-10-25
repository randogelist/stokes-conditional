From Stdlib Require Import Reals Lra Psatz Field Lia.
Require Import NSH_ChainInterface.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_CRITICAL_SERRIN_INTERPOLATION.
Import NSE_SHARED_CHAIN_INTERFACE NSE_KQ_FINITE_ALGEBRA.
Module CE := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

(* All four observables are SQUARED spatial norms:
     e = ||u||_{H1/2}^2, d = ||u||_{H3/2}^2,
     h = ||u||_{H1}^2,   l = ||u||_{L6}^2.
   Csq is the SQUARE of the H1 -> L6 embedding constant.
   Their physical identity and common solution are explicit binding work. *)
Theorem NSR20_POINTWISE_SQUARED_NORM_INTERPOLATION :
  forall e d h l Csq M,
  0 <= e -> 0 <= d -> 0 <= h -> 0 <= l -> 0 <= Csq ->
  e<=M -> h*h<=e*d -> l<=Csq*h ->
  l*l <= (Csq*Csq*M)*d.
Proof.
  intros e d h l Csq M He Hd Hh Hl HC HeM Hinter Hsob.
  assert (HCh : 0 <= Csq*h) by (apply Rmult_le_pos; assumption).
  assert (Hprod : 0 <= (Csq*h-l)*(Csq*h+l)).
  { apply Rmult_le_pos; lra. }
  assert (Hl2 : l*l <= (Csq*h)*(Csq*h)) by nra.
  assert (HC2 : 0 <= Csq*Csq) by nra.
  pose proof (Rmult_le_compat_l (Csq*Csq) (h*h) (e*d) HC2 Hinter) as H1.
  pose proof (Rmult_le_compat_r d e M Hd HeM) as H2.
  pose proof (Rmult_le_compat_l (Csq*Csq) (e*d) (M*d) HC2 H2) as H3.
  nra.
Qed.

Theorem NSR21_FINITE_SERRIN46_BUDGET :
  forall n weight e d h l Csq M D,
  0 <= Csq -> 0 <= M ->
  (forall i, (i<n)%nat -> 0<=weight i) ->
  (forall i, (i<n)%nat -> 0<=e i /\ 0<=d i /\ 0<=h i /\ 0<=l i /\
    e i<=M /\ h i*h i<=e i*d i /\ l i<=Csq*h i) ->
  sum n (fun i=>weight i*d i)<=D ->
  sum n (fun i=>weight i*(l i*l i))<=Csq*Csq*M*D.
Proof.
  intros n weight e d h l Csq M D HC HM Hw Hlocal HD.
  assert (Hpt : sum n (fun i=>weight i*(l i*l i)) <=
    sum n (fun i=>weight i*((Csq*Csq*M)*d i))).
  { apply sum_mono; intros i Hi; apply Rmult_le_compat_l; [exact (Hw i Hi)|].
    destruct (Hlocal i Hi) as [He [Hd [Hh [Hl [HeM [Hinter Hsob]]]]]].
    exact (NSR20_POINTWISE_SQUARED_NORM_INTERPOLATION
      (e i) (d i) (h i) (l i) Csq M He Hd Hh Hl HC HeM Hinter Hsob). }
  assert (Hsum : sum n (fun i=>weight i*((Csq*Csq*M)*d i))=
      (Csq*Csq*M)*sum n (fun i=>weight i*d i)).
  { rewrite <- sum_scale; apply sum_ext; intros; ring. }
  rewrite Hsum in Hpt.
  assert (Hconst : 0<=Csq*Csq*M).
  { apply Rmult_le_pos; [nra|exact HM]. }
  pose proof (Rmult_le_compat_l (Csq*Csq*M)
    (sum n (fun i=>weight i*d i)) D Hconst HD); lra.
Qed.

Record NormEndpoint : Type := {
  ne_t0 : R; ne_t1 : R;
  ne_integral : PositiveIntegral ne_t0 ne_t1;
  ne_h12_sq : R -> R;
  ne_h32_sq : R -> R;
  ne_h1_sq : R -> R;
  ne_l6_sq : R -> R
}.
Definition serrin46_observation D :=
  integral (ne_integral D) (fun t=>ne_l6_sq D t*ne_l6_sq D t).

Record CriticalNormBinding (Point : Type) (D : Point -> NormEndpoint)
  (mass diss : Point -> R) (Csq : R) : Prop := {
  cnb_sobolev_constant : 0<=Csq;
  cnb_integrable_diss : forall p,
    integrable (ne_integral (D p)) (ne_h32_sq (D p));
  cnb_integrable_l6_fourth : forall p,
    integrable (ne_integral (D p))
      (fun t=>ne_l6_sq (D p) t*ne_l6_sq (D p) t);
  cnb_pointwise : forall p t, ne_t0 (D p)<=t<=ne_t1 (D p) ->
    0<=ne_h12_sq (D p) t /\ 0<=ne_h32_sq (D p) t /\
    0<=ne_h1_sq (D p) t /\ 0<=ne_l6_sq (D p) t /\
    ne_h1_sq (D p) t*ne_h1_sq (D p) t<=
      ne_h12_sq (D p) t*ne_h32_sq (D p) t /\
    ne_l6_sq (D p) t<=Csq*ne_h1_sq (D p) t;
  cnb_time_reindex : forall p t, ne_t0 (D p)<=t<=ne_t1 (D p) ->
    exists p', ne_h12_sq (D p) t<=mass p';
  cnb_dissipation_identification : forall p,
    integral (ne_integral (D p)) (ne_h32_sq (D p))<=diss p
}.

Theorem NSR22_EXPLICIT_INTEGRATED_SERRIN46_BOUND :
  forall Point D mass diss Csq Mmax Dmax,
  CriticalNormBinding Point D mass diss Csq ->
  0<=Mmax -> 0<=Dmax ->
  (forall p, mass p<=Mmax) -> (forall p, diss p<=Dmax) ->
  forall p, serrin46_observation (D p)<=Csq*Csq*Mmax*Dmax.
Proof.
  intros Point D mass diss Csq Mmax Dmax HB HM HD Hmass Hdiss p.
  pose proof (cnb_integrable_diss Point D mass diss Csq HB p) as HintD.
  pose proof (cnb_integrable_l6_fourth Point D mass diss Csq HB p) as HintL.
  pose proof (cnb_sobolev_constant Point D mass diss Csq HB) as HC.
  set (K := Csq*Csq*Mmax).
  assert (HK : 0<=K).
  { unfold K; apply Rmult_le_pos; [nra|exact HM]. }
  assert (HintK : integrable (ne_integral (D p))
    (fun t=>K*ne_h32_sq (D p) t)).
  { exact (integrable_scale (ne_t0 (D p)) (ne_t1 (D p)) (ne_integral (D p))
      K (ne_h32_sq (D p)) HintD). }
  assert (Hpt : forall t, ne_t0 (D p)<=t<=ne_t1 (D p) ->
    ne_l6_sq (D p) t*ne_l6_sq (D p) t<=K*ne_h32_sq (D p) t).
  { intros t Ht.
    destruct (cnb_pointwise Point D mass diss Csq HB p t Ht)
      as [He [Hd [Hh [Hl [Hinter Hsob]]]]].
    destruct (cnb_time_reindex Point D mass diss Csq HB p t Ht) as [p' Hp'].
    assert (HeM : ne_h12_sq (D p) t<=Mmax).
    { eapply Rle_trans; [exact Hp'|exact (Hmass p')]. }
    unfold K; exact (NSR20_POINTWISE_SQUARED_NORM_INTERPOLATION
      (ne_h12_sq (D p) t) (ne_h32_sq (D p) t)
      (ne_h1_sq (D p) t) (ne_l6_sq (D p) t)
      Csq Mmax He Hd Hh Hl HC HeM Hinter Hsob). }
  pose proof (NSH10_INTEGRAL_ORDER
    (ne_t0 (D p)) (ne_t1 (D p)) (ne_integral (D p))
    (fun t=>ne_l6_sq (D p) t*ne_l6_sq (D p) t)
    (fun t=>K*ne_h32_sq (D p) t) HintL HintK Hpt) as HI.
  rewrite (integral_scale (ne_t0 (D p)) (ne_t1 (D p)) (ne_integral (D p))
    K (ne_h32_sq (D p)) HintD) in HI.
  pose proof (cnb_dissipation_identification Point D mass diss Csq HB p) as Hbind.
  assert (Hcum : integral (ne_integral (D p)) (ne_h32_sq (D p))<=Dmax).
  { eapply Rle_trans; [exact Hbind|exact (Hdiss p)]. }
  pose proof (Rmult_le_compat_l K
    (integral (ne_integral (D p)) (ne_h32_sq (D p))) Dmax HK Hcum).
  unfold serrin46_observation; unfold K in *; lra.
Qed.

Theorem NSR23_CRITICAL_ENERGY_TO_UNIFORM_SERRIN46_OBSERVABLE :
  forall Point D mass diss Csq,
  CriticalNormBinding Point D mass diss Csq ->
  CE.UniformCriticalEnergy Point mass diss ->
  UniformAction Point (fun p=>serrin46_observation (D p)).
Proof.
  intros Point D mass diss Csq HB [Mmax [Dmax [HM [HD [Hmass Hdiss]]]]].
  exists (Csq*Csq*Mmax*Dmax); split.
  - apply Rmult_le_pos; [|exact HD].
    apply Rmult_le_pos; [nra|exact HM].
  - exact (NSR22_EXPLICIT_INTEGRATED_SERRIN46_BOUND
      Point D mass diss Csq Mmax Dmax HB HM HD Hmass Hdiss).
Qed.

Theorem NSR24_SERRIN46_SCALING : (0<4)%R /\ (3<6)%R /\ (2/4+3/6=1)%R.
Proof. repeat split; try lra; field. Qed.

End NSE_CRITICAL_SERRIN_INTERPOLATION.
