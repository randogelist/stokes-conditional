From Stdlib Require Import Reals Lra Psatz.
From Stdlib Require Import Reals.MVT Reals.Exp_prop.
Require Import awpi_nse_finite_shell_algebra_v0_48_4.

Module NSE_SCALAR_COMPARISON.
Import NSE_FINITE_SHELL_ALGEBRA.
Open Scope R_scope.
Definition within (T t : R) : Prop := 0 <= t /\ t <= T.

Lemma NSCP00_NONPOS_DERIVATIVE : forall (f df : R -> R) a b,
  a <= b ->
  (forall x, a <= x <= b -> derivable_pt_lim f x (df x)) ->
  (forall x, a <= x <= b -> df x <= 0) ->
  f b <= f a.
Proof.
  intros f df a b Hab Hder Hsign.
  destruct (Rlt_dec a b) as [Hlt|Hlt].
  - destruct (MVT_cor2 f df a b Hlt Hder) as [c [Heq Hc]].
    assert (Hcc : a <= c <= b) by lra.
    specialize (Hsign c Hcc). nra.
  - assert (a=b) by lra; subst; lra.
Qed.

Lemma NSCP01_NONNEG_PRIMITIVE : forall f df T t,
  within T t -> f 0=0 ->
  (forall x, within T x -> derivable_pt_lim f x (df x)) ->
  (forall x, within T x -> 0 <= df x) -> 0 <= f t.
Proof.
  intros f df T t Ht Hzero Hder Hsign.
  assert (Hdec : (-f t) <= (-f 0)).
  { apply (NSCP00_NONPOS_DERIVATIVE (fun x => -f x)
      (fun x => -df x) 0 t).
    - unfold within in Ht; lra.
    - intros x Hx. apply derivable_pt_lim_opp. apply Hder.
      unfold within in *; lra.
    - intros x Hx. assert (Hxt : within T x) by (unfold within in *; lra).
      specialize (Hsign x Hxt); lra. }
  rewrite Hzero in Hdec; lra.
Qed.

Lemma NSCP02_NONNEG_DERIVATIVE_MONOTONE : forall f df T s t,
  within T s -> within T t -> s <= t ->
  (forall x, within T x -> derivable_pt_lim f x (df x)) ->
  (forall x, within T x -> 0 <= df x) -> f s <= f t.
Proof.
  intros f df T s t Hs Ht Hst Hder Hsign.
  assert (Hdec : -f t <= -f s).
  { apply (NSCP00_NONPOS_DERIVATIVE (fun x => -f x)
      (fun x => -df x) s t); [exact Hst| |].
    - intros x Hx. apply derivable_pt_lim_opp. apply Hder.
      unfold within in *; lra.
    - intros x Hx. assert (Hxt : within T x) by (unfold within in *; lra).
      specialize (Hsign x Hxt); lra. }
  lra.
Qed.

Lemma NSCP03_EXP_MONOTONE : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H. destruct (Rlt_dec x y).
  - left; apply exp_increasing; assumption.
  - assert (x=y) by lra; subst; lra.
Qed.

(* Genuine one-dimensional Gronwall proof, not an assumed envelope.
   Q is a supplied primitive of q; no integral operator is axiomatized. *)
Theorem NSCP10_INTEGRATING_FACTOR_GRONWALL :
  forall (F Fdot Q q : R -> R) T t E0,
  within T t -> Q 0=0 -> F 0 <= E0 ->
  (forall x, within T x -> derivable_pt_lim F x (Fdot x)) ->
  (forall x, within T x -> derivable_pt_lim Q x (q x)) ->
  (forall x, within T x -> Fdot x <= q x*F x) ->
  F t <= E0*exp (Q t).
Proof.
  intros F Fdot Q q T t E0 Ht HQ0 HF0 HF HQ Hineq.
  set (W := fun x => F x*exp (-Q x)).
  set (Wdot := fun x => Fdot x*exp (-Q x)+
      F x*(exp (-Q x)*(-q x))).
  assert (HD : forall x, within T x -> derivable_pt_lim W x (Wdot x)).
  { intros x Hx.
    (* Fix every function, point and derivative value explicitly.
       Inner derivative: -Q at x. Outer derivative: exp at -Q x. *)
    pose proof (@derivable_pt_lim_opp Q x (q x) (HQ x Hx)) as Hneg.
    pose proof (@derivable_pt_lim_exp (-Q x)) as Hexp.
    pose proof (@derivable_pt_lim_comp
      (opp_fct Q) exp x (-q x) (exp (-Q x)) Hneg Hexp) as HexpQ.
    unfold W, Wdot.
    exact (@derivable_pt_lim_mult
      F (fun y => exp (-Q y)) x
      (Fdot x) (exp (-Q x)*(-q x)) (HF x Hx) HexpQ). }
  assert (HS : forall x, within T x -> Wdot x <= 0).
  { intros x Hx. specialize (Hineq x Hx).
    pose proof (Rmult_le_compat_l (exp (-Q x)) _ _
      (Rlt_le _ _ (exp_pos (-Q x))) Hineq) as HM.
    unfold Wdot; nra. }
  assert (HW : W t <= W 0).
  { apply (NSCP00_NONPOS_DERIVATIVE W Wdot 0 t).
    - unfold within in Ht; lra.
    - intros x Hx; apply HD; unfold within in *; lra.
    - intros x Hx; apply HS; unfold within in *; lra. }
  unfold W in HW. rewrite HQ0 in HW.
  replace (-0) with 0 in HW by ring. rewrite exp_0 in HW.
  assert (HM : (F t*exp (-Q t))*exp (Q t) <= F 0*exp (Q t)).
  { apply Rmult_le_compat_r.
    - left; apply exp_pos.
    - nra. }
  assert (Hcancel : (F t*exp (-Q t))*exp (Q t)=F t).
  { rewrite Rmult_assoc. rewrite <- exp_plus.
    replace (-Q t+Q t) with 0 by ring. rewrite exp_0; ring. }
  rewrite Hcancel in HM.
  assert (Hinit : F 0*exp (Q t) <= E0*exp (Q t)).
  { apply Rmult_le_compat_r; [left; apply exp_pos|exact HF0]. }
  lra.
Qed.

Lemma NSCP11_BOUNDED_COEFFICIENT_PRIMITIVE : forall nu cap M0 Ustar KI UI,
  0 < nu -> 0 <= cap -> 2*nu*KI <= M0 -> UI <= Ustar ->
  (2304*cap/nu)*KI+72*UI <= 1152*cap*M0/(nu*nu)+72*Ustar.
Proof.
  intros nu cap M0 Ustar KI UI Hnu Hcap HK HU.
  assert (Hdiv : (2*nu)*(M0/(2*nu))=M0) by (field; repeat split; lra).
  assert (HK' : KI <= M0/(2*nu)) by nra.
  assert (Hc : 0 <= 2304*cap/nu).
  { apply NSFA08_DIV_NONNEG; lra. }
  pose proof (Rmult_le_compat_l (2304*cap/nu) _ _ Hc HK') as HM.
  assert (Heq : (2304*cap/nu)*(M0/(2*nu))=1152*cap*M0/(nu*nu)).
  { field; repeat split; lra. }
  rewrite Heq in HM; lra.
Qed.

Definition energy_budget nu cap M0 E0 Ustar :=
  E0*exp (1152*cap*M0/(nu*nu)+72*Ustar).

Lemma NSCP12_ENERGY_BUDGET_NONNEG : forall nu cap M0 E0 Ustar,
  0 <= E0 -> 0 <= energy_budget nu cap M0 E0 Ustar.
Proof.
  intros; unfold energy_budget; apply Rmult_le_pos; [assumption|left; apply exp_pos].
Qed.

Lemma NSCP13_ENVELOPE_TO_UNIFORM_BOUND : forall nu cap M0 E0 Ustar KI UI F,
  0 < nu -> 0 <= cap -> 0 <= E0 ->
  2*nu*KI <= M0 -> UI <= Ustar ->
  F <= E0*exp ((2304*cap/nu)*KI+72*UI) ->
  F <= energy_budget nu cap M0 E0 Ustar.
Proof.
  intros nu cap M0 E0 Ustar KI UI F Hnu Hcap HE0 HK HU HF.
  pose proof (NSCP11_BOUNDED_COEFFICIENT_PRIMITIVE
    nu cap M0 Ustar KI UI Hnu Hcap HK HU) as HQ.
  apply NSCP03_EXP_MONOTONE in HQ.
  pose proof (Rmult_le_compat_l E0 _ _ HE0 HQ).
  unfold energy_budget; lra.
Qed.

Theorem NSCP20_PRIMITIVE_COMPARISON : forall f df g dg T t c,
  within T t -> f 0=0 -> g 0=0 ->
  (forall x, within T x -> derivable_pt_lim f x (df x)) ->
  (forall x, within T x -> derivable_pt_lim g x (dg x)) ->
  (forall x, within T x -> df x <= c*dg x) -> f t <= c*g t.
Proof.
  intros f df g dg T t c Ht Hf0 Hg0 Hf Hg Hineq.
  assert (Hdec : (f t-c*g t) <= (f 0-c*g 0)).
  { apply (NSCP00_NONPOS_DERIVATIVE
      (fun x => f x-c*g x) (fun x => df x-c*dg x) 0 t).
    - unfold within in Ht; lra.
    - intros x Hx. apply derivable_pt_lim_minus.
      + apply Hf; unfold within in *; lra.
      + apply derivable_pt_lim_scal. apply Hg; unfold within in *; lra.
    - intros x Hx. assert (Hxt : within T x) by (unfold within in *; lra).
      specialize (Hineq x Hxt); lra. }
  rewrite Hf0, Hg0 in Hdec; lra.
Qed.

End NSE_SCALAR_COMPARISON.
