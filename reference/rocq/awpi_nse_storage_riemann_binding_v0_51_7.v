From Stdlib Require Import Reals Lra Psatz Field Reals.RiemannInt.
Require Import awpi_nse_finite_shell_algebra_v0_48_4.
Require Import awpi_nse_storage_cost_algebra_v0_51_7.
Require Import awpi_nse_storage_interval_calculus_v0_51_7.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.

Module NSE_STORAGE_RIEMANN_BINDING.
Import NSE_FINITE_SHELL_ALGEBRA NSE_STORAGE_COST_ALGEBRA
  NSE_STORAGE_INTERVAL_CALCULUS.
Module CT := NSE_CONTINUOUS_TIME_CALCULUS.
Open Scope R_scope.

Lemma NSSR00_ID_CONTINUOUS : forall x, continuity_pt id x.
Proof.
  intro x; apply derivable_continuous_pt.
  exists 1; exact (derivable_pt_lim_id x).
Qed.
Lemma NSSR01_CONSTANT_CONTINUOUS : forall c x,
  continuity_pt (fun _ : R => c) x.
Proof. intros; apply continuity_pt_const; intros y z; reflexivity. Qed.

Lemma NSSR02_PROFILE_DIV_CONTINUOUS : forall y r beta S x,
  0 < x -> continuity_pt (fun z => profile y r beta S z/z) x.
Proof.
  intros y r beta S x Hx. apply continuity_pt_div.
  - unfold profile. apply continuity_pt_minus.
    + apply continuity_pt_minus.
      * apply continuity_pt_mult; [apply NSSR00_ID_CONTINUOUS|apply NSSR01_CONSTANT_CONTINUOUS].
      * apply NSSR01_CONSTANT_CONTINUOUS.
    + apply continuity_pt_mult.
      * apply continuity_pt_mult.
        -- apply continuity_pt_mult; [apply NSSR01_CONSTANT_CONTINUOUS|apply NSSR00_ID_CONTINUOUS].
        -- apply NSSR00_ID_CONTINUOUS.
      * apply NSSR01_CONSTANT_CONTINUOUS.
  - apply NSSR00_ID_CONTINUOUS.
  - lra.
Qed.

(* Local FTC: constructed Stdlib Riemann primitive compared with a
   concrete antiderivative. No integral axiom is introduced. *)
Theorem NSSR05_LOCAL_FTC : forall f F a b (Hab : a <= b)
    (Hc : forall x, a <= x <= b -> continuity_pt f x)
    (pr : Riemann_integrable f a b),
  (forall x, a <= x <= b -> derivable_pt_lim F x (f x)) ->
  @RiemannInt f a b pr=F b-F a.
Proof.
  intros f F a b Hab Hc pr HF.
  set (P := @primitive f a b Hab (@FTC_P1 f a b Hab Hc)).
  assert (HP : forall x, a <= x <= b -> derivable_pt_lim P x (f x)).
  { intros x Hx; unfold P; exact (@RiemannInt_P28 f a b x Hab Hc Hx). }
  assert (HD : CT.DerivativeOn a b (fun x => F x-P x) (fun _ => 0)).
  { intros x Hx; replace 0 with (f x-f x) by ring.
    apply derivable_pt_lim_minus; [apply HF|apply HP]; exact Hx. }
  pose proof (CT.NSCT02_ZERO_DERIVATIVE_GIVES_EQUALITY a b
    (fun x => F x-P x) Hab HD) as Hconst.
  pose proof (@RiemannInt_P20 f a b Hab (@FTC_P1 f a b Hab Hc) pr) as Hri.
  change (@RiemannInt f a b pr=P b-P a) in Hri.
  cbn beta in Hconst; lra.
Qed.

Theorem NSSR10_ACTIVE_INTERVAL_INTEGRAL :
  forall nu y r beta S a b,
  0 < a -> a <= b ->
  (forall z, a <= z <= b -> 0 <= profile y r beta S z) ->
  { pr : Riemann_integrable (passage_integrand y r beta S) a b |
    /nu * @RiemannInt (passage_integrand y r beta S) a b pr =
      closed_storage nu y r beta S a b }.
Proof.
  intros nu y r beta S a b Ha Hab Hg.
  set (f := fun z => profile y r beta S z/z).
  assert (Hc : forall z, a <= z <= b -> continuity_pt f z).
  { intros z Hz; unfold f; apply NSSR02_PROFILE_DIV_CONTINUOUS; lra. }
  pose (prf := @continuity_implies_RiemannInt f a b Hab Hc).
  assert (Heq : forall z, Rmin a b <= z <= Rmax a b ->
    f z=passage_integrand y r beta S z).
  { intros z Hz; rewrite Rmin_left, Rmax_right in Hz by exact Hab.
    unfold f, passage_integrand. rewrite (NSFA13_POS_ID _ (Hg z Hz)); reflexivity. }
  pose (pr := @Riemann_integrable_ext f (passage_integrand y r beta S)
    a b Heq prf).
  exists pr.
  assert (Hri : @RiemannInt (passage_integrand y r beta S) a b pr =
      @RiemannInt f a b prf).
  { apply (@RiemannInt_P18 (passage_integrand y r beta S) f a b pr prf Hab).
    intros z Hz; symmetry; apply Heq.
    rewrite Rmin_left, Rmax_right by exact Hab; lra. }
  rewrite Hri.
  assert (Hftc : @RiemannInt f a b prf=
      passage_primitive y r beta S b-passage_primitive y r beta S a).
  { apply (NSSR05_LOCAL_FTC f (passage_primitive y r beta S) a b Hab Hc prf).
    intros z Hz; unfold f; apply NSSC00_PASSAGE_PRIMITIVE_DERIVATIVE; lra. }
  rewrite Hftc; reflexivity.
Qed.

Lemma NSSR11_ZERO_PROFILE_INTEGRABLE : forall y r beta S a b,
  a <= b ->
  (forall z, a <= z <= b -> profile y r beta S z <= 0) ->
  { pr : Riemann_integrable (passage_integrand y r beta S) a b |
    @RiemannInt (passage_integrand y r beta S) a b pr=0 }.
Proof.
  intros y r beta S a b Hab Hg.
  pose (pr0 := @RiemannInt_P14 a b 0).
  assert (Heq : forall z, Rmin a b <= z <= Rmax a b ->
      (fun _ : R => 0) z=passage_integrand y r beta S z).
  { intros z Hz; rewrite Rmin_left, Rmax_right in Hz by exact Hab.
    unfold passage_integrand. rewrite (NSFA12_POS_ZERO _ (Hg z Hz)).
    unfold Rdiv; ring. }
  pose (pr := @Riemann_integrable_ext (fun _ : R => 0)
      (passage_integrand y r beta S) a b Heq pr0).
  exists pr.
  pose proof (@RiemannInt_P18 (passage_integrand y r beta S)
    (fun _ : R => 0) a b pr pr0 Hab) as Hri.
  assert (Hint : forall z, a < z < b ->
    passage_integrand y r beta S z=(fun _ : R => 0) z).
  { intros z Hz; symmetry; apply Heq.
    rewrite Rmin_left, Rmax_right by exact Hab; lra. }
  (* Compose equalities with their integral witnesses explicitly.  In
     particular, do not ask rewrite to match the constant-function
     integral against a differently presented, proof-indexed term. *)
  exact (@eq_trans R
    (@RiemannInt (passage_integrand y r beta S) a b pr)
    (@RiemannInt (fct_cte 0) a b pr0)
    0
    (Hri Hint)
    (@eq_trans R
      (@RiemannInt (fct_cte 0) a b pr0)
      (0*(b-a)) 0
      (@RiemannInt_P15 a b 0 pr0)
      (Rmult_0_l (b-a)))).
Qed.

(* This is an actual Riemann integral on [0,1], including the apparent
   singular endpoint. The supplied PieceValid certificate specifies
   the active interval but does not supply any integral or its bound. *)
Theorem NSSR20_VALID_PIECE_REALIZES_WHOLE_STORAGE :
  forall nu y r beta S p,
  PieceValid y r beta S p ->
  { pr : Riemann_integrable (passage_integrand y r beta S) 0 1 |
    /nu * @RiemannInt (passage_integrand y r beta S) 0 1 pr =
      piece_storage nu y r beta S p }.
Proof.
  intros nu y r beta S p Hp; destruct p as [|a b].
  - destruct (NSSR11_ZERO_PROFILE_INTEGRABLE y r beta S 0 1 ltac:(lra) Hp)
      as [pr Hri]. exists pr; rewrite Hri; cbn [piece_storage]; ring.
  - destruct Hp as [Ha [Hab [Hb [Hpa [Hpb [Hg Hout]]]]]].
    assert (Hleft : forall z, 0 <= z <= a -> profile y r beta S z <= 0).
    { intros z Hz. destruct (Req_dec z a) as [Hza|Hza].
      - subst z; rewrite Hpa; lra.
      - apply Hout; [lra|left; lra]. }
    destruct (NSSR11_ZERO_PROFILE_INTEGRABLE y r beta S 0 a ltac:(lra) Hleft)
      as [prL HL].
    destruct (NSSR10_ACTIVE_INTERVAL_INTEGRAL nu y r beta S a b Ha Hab Hg)
      as [prM HM].
    assert (Hright : { prR : Riemann_integrable (passage_integrand y r beta S) b 1 |
      @RiemannInt (passage_integrand y r beta S) b 1 prR=0 }).
    { destruct (Req_dec_T b 1) as [Hb1|Hb1].
      - subst b. exists (@RiemannInt_P7 (passage_integrand y r beta S) 1).
        apply RiemannInt_P9.
      - assert (Hb_lt : b < 1) by lra.
        assert (Hone : 0 <= (1 : R) <= 1) by lra.
        assert (Houtside : (1 : R) < a \/ b < 1).
        { right; exact Hb_lt. }
        assert (Hg1 : y-r-beta*S <= 0).
        { pose proof (Hout 1 Hone Houtside) as Hprofile1.
          replace (profile y r beta S 1) with (y-r-beta*S)
            in Hprofile1 by (unfold profile; ring).
          exact Hprofile1. }
        assert (Hgb : profile y r beta S b=0).
        { rewrite Hpb, NSFA12_POS_ZERO by exact Hg1; reflexivity. }
        apply (NSSR11_ZERO_PROFILE_INTEGRABLE y r beta S b 1 Hb).
        intros z Hz. destruct (Req_dec z b) as [Hzb|Hzb].
        + subst z; rewrite Hgb; lra.
        + apply Hout; [lra|right; lra]. }
    destruct Hright as [prR HR].
    pose (prLM := @RiemannInt_P21 (passage_integrand y r beta S) 0 a b
      ltac:(lra) Hab prL prM).
    pose (pr := @RiemannInt_P21 (passage_integrand y r beta S) 0 b 1
      ltac:(lra) Hb prLM prR).
    exists pr.
    pose proof (@RiemannInt_P25 (passage_integrand y r beta S) 0 a b
      prL prM prLM ltac:(lra) Hab) as Hlm.
    pose proof (@RiemannInt_P25 (passage_integrand y r beta S) 0 b 1
      prLM prR pr ltac:(lra) Hb) as Hall.
    rewrite HL in Hlm; rewrite HR in Hall.
    cbn [piece_storage].
    replace (@RiemannInt (passage_integrand y r beta S) 0 1 pr)
      with (@RiemannInt (passage_integrand y r beta S) a b prM) by lra.
    exact HM.
Qed.

Theorem NSSR21_WHOLE_STORAGE_INTEGRAL_BOUND :
  forall nu y r beta S p,
  0 < nu -> 0 < r -> 0 <= beta -> 0 <= S -> PieceValid y r beta S p ->
  { pr : Riemann_integrable (passage_integrand y r beta S) 0 1 |
    0 <= /nu * @RiemannInt (passage_integrand y r beta S) 0 1 pr /\
    /nu * @RiemannInt (passage_integrand y r beta S) 0 1 pr <= y*y/(8*r*nu) }.
Proof.
  intros nu y r beta S p Hnu Hr Hb HS Hp.
  destruct (NSSR20_VALID_PIECE_REALIZES_WHOLE_STORAGE nu y r beta S p Hp)
    as [pr Hri]. exists pr; rewrite Hri.
  exact (NSSC21_VALID_PIECE_STORAGE_BOUND nu y r beta S p Hnu Hr Hb HS Hp).
Qed.

End NSE_STORAGE_RIEMANN_BINDING.
