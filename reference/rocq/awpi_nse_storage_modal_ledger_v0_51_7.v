From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import awpi_nse_finite_shell_algebra_v0_48_4.
Require Import awpi_nse_storage_cost_algebra_v0_51_7.
Require Import awpi_nse_storage_interval_calculus_v0_51_7.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.

Module NSE_STORAGE_MODAL_LEDGER.
Import NSE_FINITE_SHELL_ALGEBRA NSE_STORAGE_COST_ALGEBRA
  NSE_STORAGE_INTERVAL_CALCULUS.
Module K := NSE_KQ_FINITE_ALGEBRA.
Open Scope R_scope.

Definition moment n q a := total (fun k => q k*a k) n.
Definition square_moment n q a := total (fun k => q k*a k*a k) n.
Definition shell_square n a := total (fun k => a k*a k) n.
Definition heat_linear n lambda q a :=
  total (fun k => (q k-lambda*lambda)*a k) n.
Definition heat_square n lambda q a :=
  total (fun k => (q k-lambda*lambda)*a k*a k) n.
Definition modal_y_rate n nu lambda q a s :=
  (-nu/ lambda)*moment n q a+total s n/lambda.
Definition modal_S_rate n nu q a s :=
  -2*nu*square_moment n q a+2*total (fun k => a k*s k) n.
Definition storage_rate nu alpha beta zeta yd Sd :=
  (alpha*yd-beta*zeta*Sd)/nu.
Definition modal_production n nu lambda alpha beta zeta a s :=
  (alpha*total s n/lambda-2*beta*zeta*total (fun k => a k*s k) n)/nu.
Definition heat_error n lambda alpha beta zeta q a :=
  -(alpha/lambda)*heat_linear n lambda q a+
    2*beta*zeta*heat_square n lambda q a.

Lemma NSSM00_LINEAR_MOMENT_SPLIT : forall n lambda q a,
  moment n q a=lambda*lambda*total a n+heat_linear n lambda q a.
Proof.
  intros n lambda q a; unfold moment, heat_linear.
  induction n as [|n IH]; simpl; [ring|rewrite IH; ring].
Qed.
Lemma NSSM01_SQUARE_MOMENT_SPLIT : forall n lambda q a,
  square_moment n q a=lambda*lambda*shell_square n a+heat_square n lambda q a.
Proof.
  intros n lambda q a; unfold square_moment, shell_square, heat_square.
  induction n as [|n IH]; simpl; [ring|rewrite IH; ring].
Qed.

Theorem NSSM10_EXACT_FINITE_STORAGE_BALANCE :
  forall n nu lambda alpha beta zeta r q a s,
  0 < nu -> 0 < lambda ->
  (total a n/lambda)*alpha-2*beta*(shell_square n a)*zeta=
    pos (total a n/lambda-r-beta*shell_square n a) ->
  storage_rate nu alpha beta zeta
    (modal_y_rate n nu lambda q a s) (modal_S_rate n nu q a s)+
  folded_cost lambda (total a n/lambda) (shell_square n a) r beta=
  modal_production n nu lambda alpha beta zeta a s+
  heat_error n lambda alpha beta zeta q a.
Proof.
  intros n nu lambda alpha beta zeta r q a s Hnu Hl Heuler.
  unfold storage_rate, modal_y_rate, modal_S_rate,
    modal_production, heat_error, folded_cost.
  rewrite <- Heuler.
  rewrite (NSSM00_LINEAR_MOMENT_SPLIT n lambda q a).
  rewrite (NSSM01_SQUARE_MOMENT_SPLIT n lambda q a).
  field; repeat split; lra.
Qed.

Lemma NSSM20_HEAT_LINEAR_NONNEG : forall n lambda q a,
  (forall k, (k<n)%nat -> lambda*lambda <= q k) ->
  (forall k, (k<n)%nat -> 0 <= a k) ->
  0 <= heat_linear n lambda q a.
Proof.
  intros n lambda q a Hq Ha. unfold heat_linear.
  apply NSFA02_TOTAL_NONNEG; intros k Hk; apply Rmult_le_pos.
  - pose proof (Hq k Hk); lra.
  - exact (Ha k Hk).
Qed.

Lemma NSSM21_HEAT_SQUARE_BOUNDS : forall n lambda q a,
  (forall k, (k<n)%nat -> lambda*lambda <= q k) ->
  0 <= heat_square n lambda q a /\
  heat_square n lambda q a <= square_moment n q a.
Proof.
  intros n lambda q a Hq; split.
  - unfold heat_square. apply NSFA02_TOTAL_NONNEG; intros k Hk.
    replace ((q k-lambda*lambda)*a k*a k)
      with ((q k-lambda*lambda)*(a k*a k)) by ring.
    apply Rmult_le_pos; [pose proof (Hq k Hk); lra|exact (Rle_0_sqr (a k))].
  - unfold heat_square, square_moment. apply NSFA01_TOTAL_LE; intros k Hk.
    assert (Hp : 0 <= (lambda*lambda)*(a k*a k)).
    { apply Rmult_le_pos; apply Rle_0_sqr. }
    nra.
Qed.

Theorem NSSM22_HEAT_ERROR_KINETIC_PAYMENT :
  forall n lambda alpha beta zeta q a,
  0 < lambda -> 0 <= alpha -> 0 <= beta -> 0 <= zeta -> 2*zeta <= 1 ->
  (forall k, (k<n)%nat -> lambda*lambda <= q k) ->
  (forall k, (k<n)%nat -> 0 <= a k) ->
  heat_error n lambda alpha beta zeta q a <= beta*square_moment n q a.
Proof.
  intros n lambda alpha beta zeta q a Hl Ha Hb Hz Hz1 Hq Hu.
  pose proof (NSSM20_HEAT_LINEAR_NONNEG n lambda q a Hq Hu) as HL.
  destruct (NSSM21_HEAT_SQUARE_BOUNDS n lambda q a Hq) as [HS HSle].
  assert (Hcoeff : 0 <= alpha/lambda) by (apply NSFA08_DIV_NONNEG; assumption).
  assert (Hneg : 0 <= (alpha/lambda)*heat_linear n lambda q a)
    by (apply Rmult_le_pos; assumption).
  pose proof (Rmult_le_compat_l beta _ _ Hb Hz1) as Hcz.
  pose proof (Rmult_le_compat_r (heat_square n lambda q a) _ _ HS Hcz) as HczS.
  pose proof (Rmult_le_compat_l beta _ _ Hb HSle) as Hpay.
  unfold heat_error; nra.
Qed.

Theorem NSSM23_FINITE_SHELL_HEAT_PAYMENT : forall n beta E G,
  0 <= beta ->
  (forall j, (j<n)%nat -> E j <= beta*G j) ->
  total E n <= beta*total G n.
Proof.
  intros n beta E G Hb Hpay. rewrite <- NSFA04_TOTAL_SCALE.
  apply NSFA01_TOTAL_LE; exact Hpay.
Qed.

Lemma NSSM30_SIGNED_DETECTOR_FORM : forall n nu lambda alpha beta zeta a s,
  modal_production n nu lambda alpha beta zeta a s=
  total (fun k => ((alpha/lambda)-2*beta*zeta*a k)*s k/nu) n.
Proof.
  intros n nu lambda alpha beta zeta a s.
  unfold modal_production; induction n as [|n IH]; simpl.
  - unfold Rdiv; ring.
  - rewrite <- IH. unfold Rdiv; ring.
Qed.

Lemma NSSM31_ABS_FROM_INTERVAL : forall x B,
  -B <= x -> x <= B -> Rabs x <= B.
Proof.
  intros x B Hl Hu. destruct (Rle_dec 0 x) as [H|H].
  - rewrite Rabs_pos_eq by exact H; exact Hu.
  - rewrite Rabs_left by lra; lra.
Qed.

Lemma NSSM32_FINITE_ABS_SUM : forall n f,
  Rabs (total f n) <= total (fun k => Rabs (f k)) n.
Proof.
  intros n f; induction n as [|n IH]; simpl.
  - rewrite Rabs_R0; lra.
  - pose proof (Rabs_triang (total f n) (f n)); lra.
Qed.

Theorem NSSM33_DETECTOR_ENVELOPE : forall lambda alpha beta zeta a,
  0 < lambda -> 0 <= alpha -> alpha <= 1 ->
  0 <= beta -> 0 <= zeta -> 2*zeta <= 1 -> 0 <= a ->
  Rabs (alpha/lambda-2*beta*zeta*a) <= /lambda+beta*a.
Proof.
  intros lambda alpha beta zeta a Hl Ha Ha1 Hb Hz Hz1 Hu.
  assert (Hinv : 0 <= /lambda) by (left; apply Rinv_0_lt_compat; exact Hl).
  pose proof (Rmult_le_compat_r (/lambda) _ _ Hinv Ha1) as Hat.
  assert (Ha0 : 0 <= alpha/lambda) by (apply NSFA08_DIV_NONNEG; assumption).
  assert (Hza : 0 <= 2*beta*zeta*a).
  { repeat apply Rmult_le_pos; lra. }
  pose proof (Rmult_le_compat_l beta _ _ Hb Hz1) as Hzb.
  pose proof (Rmult_le_compat_r a _ _ Hu Hzb) as Hzba.
  assert (Hba : 0 <= beta*a) by (apply Rmult_le_pos; assumption).
  apply NSSM31_ABS_FROM_INTERVAL; unfold Rdiv in *; nra.
Qed.

Theorem NSSM34_SINGLE_LOW_OUTPUT_PAYMENT :
  forall nu lambda q alpha beta zeta a s M,
  0 < nu -> 0 < lambda -> 0 <= q -> q <= 2*lambda ->
  0 <= alpha -> alpha <= 1 -> 0 <= beta ->
  0 <= zeta -> 2*zeta <= 1 -> 0 <= a -> 0 <= M ->
  Rabs s <= q*M ->
  Rabs (((alpha/lambda)-2*beta*zeta*a)*s/nu) <=
    (M/nu)*(2+beta*q*a).
Proof.
  intros nu lambda q alpha beta zeta a s M Hnu Hl Hq Hq2
    Ha Ha1 Hb Hz Hz1 Hu HM Hs.
  pose proof (NSSM33_DETECTOR_ENVELOPE lambda alpha beta zeta a
    Hl Ha Ha1 Hb Hz Hz1 Hu) as Hd.
  assert (Hdi : 0 <= /lambda+beta*a).
  { assert (Hi : 0 <= /lambda) by (left; apply Rinv_0_lt_compat; exact Hl).
    assert (Hp : 0 <= beta*a) by (apply Rmult_le_pos; assumption); lra. }
  pose proof (Rmult_le_compat_r (Rabs s) _ _ (Rabs_pos s) Hd) as Hm1.
  pose proof (Rmult_le_compat_l (/lambda+beta*a) _ _ Hdi Hs) as Hm2.
  assert (Hiv : 0 <= /nu) by (left; apply Rinv_0_lt_compat; exact Hnu).
  assert (Hm : Rabs (alpha/lambda-2*beta*zeta*a)*Rabs s <=
      (/lambda+beta*a)*(q*M)) by lra.
  pose proof (Rmult_le_compat_r (/nu) _ _ Hiv Hm) as Hm3.
  assert (Hqdiv : q/lambda <= 2).
  { apply (Rmult_le_reg_l lambda); [exact Hl|].
    replace (lambda*(q/lambda)) with q by (field; repeat split; lra); nra. }
  assert (HMnu : 0 <= M/nu) by (apply NSFA08_DIV_NONNEG; assumption).
  pose proof (Rmult_le_compat_l (M/nu) _ _ HMnu Hqdiv) as Hqm.
  unfold Rdiv at 1. rewrite !Rabs_mult.
  rewrite (Rabs_pos_eq (/nu) Hiv).
  assert (He : ((/lambda+beta*a)*(q*M))*/nu=
    (M/nu)*(q/lambda+beta*q*a)) by (unfold Rdiv; ring).
  rewrite He in Hm3; nra.
Qed.

Lemma NSSM35_TOTAL_KQ_SUM : forall n f, total f n=K.sum n f.
Proof. intros n f; induction n; simpl; [reflexivity|rewrite IHn; reflexivity]. Qed.

Theorem NSSM36_FINITE_AMPLITUDE_CAUCHY : forall n q a,
  total (fun k => q k*a k) n*total (fun k => q k*a k) n <=
  total (fun k => q k*q k) n*total (fun k => a k*a k) n.
Proof.
  intros n q a; rewrite !NSSM35_TOTAL_KQ_SUM.
  exact (K.NSKA10_FINITE_CAUCHY n q a).
Qed.

Lemma NSSM37_TOTAL_CONSTANT : forall n c, total (fun _ => c) n=INR n*c.
Proof.
  intros n c; induction n as [|n IH].
  - change (0=0*c); ring.
  - change (total (fun _ => c) n+c=INR (S n)*c).
    rewrite IH, S_INR; ring.
Qed.

Theorem NSSM38_CAUCHY_TO_FIXED_ENVELOPE : forall n q a L rootM M0,
  0 <= L -> 0 <= rootM -> rootM*rootM=M0 ->
  total (fun k => q k*q k) n <= L*L ->
  total (fun k => a k*a k) n <= M0 ->
  total (fun k => q k*a k) n <= L*rootM.
Proof.
  intros n q a L rootM M0 HL Hroot Hroot2 Hq Ha.
  pose proof (NSSM36_FINITE_AMPLITUDE_CAUCHY n q a) as Hcs.
  assert (HA0 : 0 <= total (fun k => a k*a k) n).
  { apply NSFA02_TOTAL_NONNEG; intros; apply Rle_0_sqr. }
  pose proof (Rmult_le_compat_r (total (fun k => a k*a k) n)
    (total (fun k => q k*q k) n) (L*L) HA0 Hq) as H1.
  pose proof (Rmult_le_compat_l (L*L) _ _ (Rle_0_sqr L) Ha) as H2.
  assert (Hprod : 0 <= L*rootM) by (apply Rmult_le_pos; assumption).
  set (v := total (fun k => q k*a k) n) in *.
  rewrite <- Hroot2 in H2.
  assert (Hsq : v*v <= (L*rootM)*(L*rootM)) by nra.
  destruct (Rle_dec v (L*rootM)); [assumption|].
  assert (Hp : 0 < (v-L*rootM)*(v+L*rootM))
    by (apply Rmult_lt_0_compat; lra).
  nra.
Qed.

Definition low_coefficient nu beta count L rootM :=
  (2*count+beta*L*rootM)/nu.

Theorem NSSM40_FINITE_LOW_OUTPUT_KINETIC_PAYMENT :
  forall n nu beta M G M0 L rootM
    (lambda q alpha zeta a s : nat -> R),
  0 < nu -> 0 <= beta -> 0 <= M -> M <= G ->
  0 <= L -> 0 <= rootM -> rootM*rootM=M0 ->
  (forall k, (k<n)%nat -> 0 < lambda k /\ 0 <= q k /\ q k <= 2*lambda k /\
    0 <= alpha k /\ alpha k <= 1 /\ 0 <= zeta k /\ 2*zeta k <= 1 /\
    0 <= a k /\ Rabs (s k) <= q k*M) ->
  total (fun k => q k*q k) n <= L*L ->
  total (fun k => a k*a k) n <= M0 ->
  Rabs (total (fun k => ((alpha k/lambda k)-2*beta*zeta k*a k)*s k/nu) n)
  <= low_coefficient nu beta (INR n) L rootM*G.
Proof.
  intros n nu beta M G M0 L rootM lambda q alpha zeta a s
    Hnu Hb HM HMG HL Hroot Hr2 Hm Hq Ha.
  eapply Rle_trans; [apply NSSM32_FINITE_ABS_SUM|].
  assert (Hterm : total (fun k =>
    Rabs (((alpha k/lambda k)-2*beta*zeta k*a k)*s k/nu)) n <=
    total (fun k => (M/nu)*(2+beta*q k*a k)) n).
  { apply NSFA01_TOTAL_LE; intros k Hk.
    destruct (Hm k Hk) as [Hl [Hq0 [Hq2 [Hal [Hau [Hz [Hzu [Hak Hsk]]]]]]]].
    exact (NSSM34_SINGLE_LOW_OUTPUT_PAYMENT nu (lambda k) (q k)
      (alpha k) beta (zeta k) (a k) (s k) M
      Hnu Hl Hq0 Hq2 Hal Hau Hb Hz Hzu Hak HM Hsk). }
  assert (Hsum : total (fun k => (M/nu)*(2+beta*q k*a k)) n =
    (M/nu)*(2*INR n+beta*total (fun k => q k*a k) n)).
  { rewrite NSFA04_TOTAL_SCALE.
    replace (total (fun k => 2+beta*q k*a k) n) with
      (total (fun _ => 2) n+beta*total (fun k => q k*a k) n).
    - rewrite NSSM37_TOTAL_CONSTANT; ring.
    - transitivity (total (fun k => 1*2+beta*(q k*a k)) n).
      + rewrite NSFA03_TOTAL_LINEAR; ring.
      + apply NSFA00_TOTAL_EXT; intros; ring. }
  rewrite Hsum in Hterm.
  pose proof (NSSM38_CAUCHY_TO_FIXED_ENVELOPE n q a L rootM M0
    HL Hroot Hr2 Hq Ha) as Hqa.
  pose proof (Rmult_le_compat_l beta _ _ Hb Hqa) as HqaB.
  assert (Hmn : 0 <= M/nu) by (apply NSFA08_DIV_NONNEG; assumption).
  assert (Hinner : 2*INR n+beta*total (fun k => q k*a k) n <=
      2*INR n+beta*(L*rootM)) by lra.
  pose proof (Rmult_le_compat_l (M/nu) _ _ Hmn Hinner) as Hi.
  assert (Hcoef : 0 <= low_coefficient nu beta (INR n) L rootM).
  { unfold low_coefficient. apply NSFA08_DIV_NONNEG; [|exact Hnu].
    pose proof (pos_INR n).
    assert (Hp : 0 <= beta*L*rootM) by (repeat apply Rmult_le_pos; assumption).
    lra. }
  pose proof (Rmult_le_compat_l (low_coefficient nu beta (INR n) L rootM)
    M G Hcoef HMG) as Hlast.
  unfold low_coefficient in *; unfold Rdiv in *; nra.
Qed.


Lemma NSSM50_FINITE_TIME_DERIVATIVE : forall n (a : R -> nat -> R) ad t,
  (forall k, (k<n)%nat -> derivable_pt_lim (fun x => a x k) t (ad k)) ->
  derivable_pt_lim (fun x => total (a x) n) t (total ad n).
Proof.
  induction n as [|n IH]; intros a ad t Hd.
  - change (derivable_pt_lim (fun _ : R => 0) t 0).
    exact (derivable_pt_lim_const 0 t).
  - change (derivable_pt_lim (fun x => total (a x) n+a x n) t (total ad n+ad n)).
    apply derivable_pt_lim_plus.
    + apply IH; intros k Hk; apply Hd; lia.
    + apply Hd; lia.
Qed.

Theorem NSSM51_RADIAL_ODE_GIVES_Y_DERIVATIVE :
  forall n nu lambda q (a s : R -> nat -> R) t,
  (forall k, (k<n)%nat -> derivable_pt_lim (fun x => a x k) t
    (-nu*q k*a t k+s t k)) ->
  derivable_pt_lim (fun x => total (a x) n/lambda) t
    (modal_y_rate n nu lambda q (a t) (s t)).
Proof.
  intros n nu lambda q a s t Hd.
  pose proof (NSSM50_FINITE_TIME_DERIVATIVE n a
    (fun k => -nu*q k*a t k+s t k) t Hd) as Hsum.
  assert (He : total (fun k => -nu*q k*a t k+s t k) n=
      -nu*moment n q (a t)+total (s t) n).
  { unfold moment.
    transitivity (total (fun k => (-nu)*(q k*a t k)+1*(s t k)) n).
    - apply NSFA00_TOTAL_EXT; intros; ring.
    - rewrite NSFA03_TOTAL_LINEAR; ring. }
  rewrite He in Hsum.
  replace (modal_y_rate n nu lambda q (a t) (s t)) with
    ((/lambda)*(-nu*moment n q (a t)+total (s t) n))
    by (unfold modal_y_rate, Rdiv; ring).
  apply (@derivable_pt_lim_ext
    (fun x => (/lambda)*total (a x) n) (fun x => total (a x) n/lambda) t
    ((/lambda)*(-nu*moment n q (a t)+total (s t) n))).
  - intro x; unfold Rdiv; ring.
  - apply derivable_pt_lim_scal; exact Hsum.
Qed.

Theorem NSSM52_RADIAL_ODE_GIVES_S_DERIVATIVE :
  forall n nu q (a s : R -> nat -> R) t,
  (forall k, (k<n)%nat -> derivable_pt_lim (fun x => a x k) t
    (-nu*q k*a t k+s t k)) ->
  derivable_pt_lim (fun x => shell_square n (a x)) t
    (modal_S_rate n nu q (a t) (s t)).
Proof.
  intros n nu q a s t Hd.
  assert (Hsq : forall k, (k<n)%nat ->
    derivable_pt_lim (fun x => a x k*a x k) t
    ((-nu*q k*a t k+s t k)*a t k+a t k*(-nu*q k*a t k+s t k))).
  { intros k Hk; apply derivable_pt_lim_mult; apply Hd; exact Hk. }
  pose proof (NSSM50_FINITE_TIME_DERIVATIVE n
    (fun x k => a x k*a x k)
    (fun k => (-nu*q k*a t k+s t k)*a t k+a t k*(-nu*q k*a t k+s t k))
    t Hsq) as Hsum.
  assert (He : total
    (fun k => (-nu*q k*a t k+s t k)*a t k+a t k*(-nu*q k*a t k+s t k)) n=
    modal_S_rate n nu q (a t) (s t)).
  { unfold modal_S_rate, square_moment.
    transitivity (total (fun k => (-2*nu)*(q k*a t k*a t k)+2*(a t k*s t k)) n).
    - apply NSFA00_TOTAL_EXT; intros; ring.
    - rewrite NSFA03_TOTAL_LINEAR; ring. }
  rewrite He in Hsum; exact Hsum.
Qed.

(* A pointwise constructor at differentiability times. It never assumes
   that a modal absolute value is differentiable at all of its zeros. *)
Theorem NSSM53_ACTIVE_PASSAGE_FROM_RADIAL_ODE :
  forall n nu lambda r beta q (u s : R -> nat -> R)
    (lo hi : R -> R) lod hid t,
  0 < nu -> 0 < lambda ->
  (forall k, (k<n)%nat -> derivable_pt_lim (fun x => u x k) t
    (-nu*q k*u t k+s t k)) ->
  derivable_pt_lim lo t lod -> derivable_pt_lim hi t hid ->
  PieceValid (total (u t) n/lambda) r beta (shell_square n (u t))
    (ActivePassage (lo t) (hi t)) ->
  profile (total (u t) n/lambda) r beta (shell_square n (u t)) (lo t)*lod=0 ->
  profile (total (u t) n/lambda) r beta (shell_square n (u t)) (hi t)*hid=0 ->
  let al := active_width (lo t) (hi t) in
  let ze := active_moment (lo t) (hi t) in
  derivable_pt_lim
    (fun x => closed_storage nu (total (u x) n/lambda) r beta
      (shell_square n (u x)) (lo x) (hi x)) t
    (modal_production n nu lambda al beta ze (u t) (s t)+
     heat_error n lambda al beta ze q (u t)-
     folded_cost lambda (total (u t) n/lambda) (shell_square n (u t)) r beta).
Proof.
  intros n nu lambda r beta q u s lo hi lod hid t
    Hnu Hl Hode Hlo Hhi Hvalid Hlc Hhc.
  cbv zeta.
  pose proof (NSSC20_VALID_PIECE_MOMENTS
    (total (u t) n/lambda) r beta (shell_square n (u t))
    (ActivePassage (lo t) (hi t)) Hvalid) as Hmom.
  cbn [piece_alpha piece_zeta] in Hmom.
  destruct Hmom as [Ha [Ha1 [Hz [Hz1 Heuler]]]].
  destruct Hvalid as [Hlot [Horder Hrest]].
  assert (Hhit : 0 < hi t) by lra.
  pose proof (NSSM51_RADIAL_ODE_GIVES_Y_DERIVATIVE n nu lambda q u s t Hode) as HY.
  pose proof (NSSM52_RADIAL_ODE_GIVES_S_DERIVATIVE n nu q u s t Hode) as HS.
  pose proof (NSSC31_MOVING_ENDPOINTS_CANCEL
    (fun x => total (u x) n/lambda) (fun x => shell_square n (u x)) lo hi
    (modal_y_rate n nu lambda q (u t) (s t))
    (modal_S_rate n nu q (u t) (s t)) lod hid nu r beta t
    HY HS Hlo Hhi Hlot Hhit Hlc Hhc) as HD.
  pose proof (NSSM10_EXACT_FINITE_STORAGE_BALANCE n nu lambda
    (active_width (lo t) (hi t)) beta (active_moment (lo t) (hi t))
    r q (u t) (s t) Hnu Hl Heuler) as Hbal.
  unfold storage_rate in Hbal.
  replace
    (modal_production n nu lambda (active_width (lo t) (hi t)) beta
        (active_moment (lo t) (hi t)) (u t) (s t)+
     heat_error n lambda (active_width (lo t) (hi t)) beta
        (active_moment (lo t) (hi t)) q (u t)-
     folded_cost lambda (total (u t) n/lambda) (shell_square n (u t)) r beta)
    with
    (/nu*(active_width (lo t) (hi t)*modal_y_rate n nu lambda q (u t) (s t)-
      beta*active_moment (lo t) (hi t)*modal_S_rate n nu q (u t) (s t)))
    by (unfold Rdiv in Hbal; nra).
  exact HD.
Qed.

End NSE_STORAGE_MODAL_LEDGER.
