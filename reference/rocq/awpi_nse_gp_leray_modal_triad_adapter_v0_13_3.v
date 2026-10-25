
From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

Module NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.

(* Positive part written algebraically via |x|. *)
Definition pos (x : R) : R :=
  (x + Rabs x) / 2.

Theorem GPLM00_POS_NONNEG :
  forall x : R, 0 <= pos x.
Proof.
  intro x.
  unfold pos.
  destruct (Rle_dec 0 x) as [Hx | Hx].
  - rewrite (Rabs_pos_eq x Hx).
    lra.
  - assert (Hxn : x < 0) by lra.
    rewrite (Rabs_left x Hxn).
    ring_simplify.
    lra.
Qed.

Theorem GPLM01_POS_DOMINATES :
  forall x : R, x <= pos x.
Proof.
  intro x.
  unfold pos.
  destruct (Rle_dec 0 x) as [Hx | Hx].
  - rewrite (Rabs_pos_eq x Hx).
    lra.
  - assert (Hxn : x < 0) by lra.
    rewrite (Rabs_left x Hxn).
    ring_simplify.
    lra.
Qed.

Theorem GPLM02_POS_THREE_SUBADDITIVE :
  forall a b c : R,
    pos (a + b + c) <= pos a + pos b + pos c.
Proof.
  intros a b c.
  unfold pos.
  pose proof (Rabs_triang a b) as Hab.
  pose proof (Rabs_triang (a+b) c) as Habc.
  assert (Htri : Rabs (a+b+c) <= Rabs a + Rabs b + Rabs c).
  {
    eapply Rle_trans.
    - exact Habc.
    - lra.
  }
  lra.
Qed.

(* Three scalar modal ODEs:
     du_i + nu*lambda_i*u_i = N_i.
   dc is the Leibniz derivative of c = uk*up*uq.
   The result is the exact three-leg source split. *)
Theorem GPLM10_THREE_LEG_MODAL_SOURCE_SPLIT :
  forall
    nu lk lp lq
    uk up uq
    duk dup duq
    Nk Np Nq dc : R,
    duk + nu * lk * uk = Nk ->
    dup + nu * lp * up = Np ->
    duq + nu * lq * uq = Nq ->
    dc = duk * up * uq + uk * dup * uq + uk * up * duq ->
    dc + nu * (lk + lp + lq) * (uk * up * uq)
      =
      Nk * up * uq
      + uk * Np * uq
      + uk * up * Nq.
Proof.
  intros nu lk lp lq uk up uq duk dup duq Nk Np Nq dc
    Hk Hp Hq Hdc.
  assert (Hdk : duk = Nk - nu*lk*uk) by lra.
  assert (Hdp : dup = Np - nu*lp*up) by lra.
  assert (Hdq : duq = Nq - nu*lq*uq) by lra.
  rewrite Hdc, Hdk, Hdp, Hdq.
  ring.
Qed.

Definition triad_work (uk up uq : R) : R :=
  uk * up * uq.

Definition source1 (Nk up uq : R) : R :=
  Nk * up * uq.

Definition source2 (uk Np uq : R) : R :=
  uk * Np * uq.

Definition source3 (uk up Nq : R) : R :=
  uk * up * Nq.

Definition gamma (lk lp lq : R) : R :=
  lk + lp + lq.

Theorem GPLM11_GAMMA_NONNEG :
  forall lk lp lq : R,
    0 <= lk ->
    0 <= lp ->
    0 <= lq ->
    0 <= gamma lk lp lq.
Proof.
  intros lk lp lq Hk Hp Hq.
  unfold gamma.
  lra.
Qed.

Theorem GPLM12_GAMMA_POSITIVE_IF_ONE_MODE_POSITIVE :
  forall lk lp lq : R,
    0 <= lk ->
    0 <= lp ->
    0 <= lq ->
    0 < lk ->
    0 < gamma lk lp lq.
Proof.
  intros lk lp lq Hk Hp Hq Hkp.
  unfold gamma.
  lra.
Qed.

(* Pointwise positive-source domination after the exact three-leg split.
   This is the scalar algebra later used beneath the positive-part
   Duhamel inequality. *)
Theorem GPLM20_POSITIVE_THREE_SOURCE_DOMINATION :
  forall r1 r2 r3 : R,
    pos (r1 + r2 + r3)
      <= pos r1 + pos r2 + pos r3.
Proof.
  intros.
  apply GPLM02_POS_THREE_SUBADDITIVE.
Qed.

(* If the damped triad derivative equals the three-source sum, its
   positive forcing is dominated by the three positive one-leg classes. *)
Theorem GPLM21_DAMPED_WORK_POSITIVE_FORCING :
  forall dc damp r1 r2 r3 : R,
    dc + damp = r1 + r2 + r3 ->
    pos (dc + damp) <= pos r1 + pos r2 + pos r3.
Proof.
  intros dc damp r1 r2 r3 H.
  rewrite H.
  apply GPLM20_POSITIVE_THREE_SOURCE_DOMINATION.
Qed.

(* Same statement with the modal source definitions exposed. *)
Theorem GPLM22_MODAL_SOURCE_POSITIVE_DOMINATION :
  forall
    nu lk lp lq
    uk up uq
    duk dup duq
    Nk Np Nq dc : R,
    duk + nu * lk * uk = Nk ->
    dup + nu * lp * up = Np ->
    duq + nu * lq * uq = Nq ->
    dc = duk * up * uq + uk * dup * uq + uk * up * duq ->
    pos
      (dc + nu * gamma lk lp lq * triad_work uk up uq)
    <=
      pos (source1 Nk up uq)
      + pos (source2 uk Np uq)
      + pos (source3 uk up Nq).
Proof.
  intros nu lk lp lq uk up uq duk dup duq Nk Np Nq dc
    Hk Hp Hq Hdc.
  unfold gamma, triad_work, source1, source2, source3.
  pose proof
    (GPLM10_THREE_LEG_MODAL_SOURCE_SPLIT
      nu lk lp lq uk up uq duk dup duq Nk Np Nq dc
      Hk Hp Hq Hdc) as Hsplit.
  rewrite Hsplit.
  apply GPLM20_POSITIVE_THREE_SOURCE_DOMINATION.
Qed.

(* The one-leg source matrix algebra:
   each hub-fixed source coefficient is a rank-one product x_i*y_j.
   This theorem freezes the 2x2 minor identity characterizing rank one. *)
Theorem GPLM30_RANK_ONE_STAR_MINOR_ZERO :
  forall x1 x2 y1 y2 : R,
    (x1*y1)*(x2*y2) - (x1*y2)*(x2*y1) = 0.
Proof.
  intros.
  ring.
Qed.

(* Aggregating a fixed parent factor against a sum of source factors
   retains the rank-one/star form. *)
Theorem GPLM31_STAR_AGGREGATION_FACTORS :
  forall x y1 y2 y3 : R,
    x*y1 + x*y2 + x*y3 = x*(y1+y2+y3).
Proof.
  intros.
  ring.
Qed.

(* Abstract interface consumed by the analytic Leray-Hopf adapter:
   once an actual modal solution supplies the three scalar ODE premises
   and the Leibniz relation, the triad-source conclusion is immediate. *)
Definition ModalTriadCertificate
  (nu lk lp lq
   uk up uq
   duk dup duq
   Nk Np Nq dc : R) : Prop :=
  duk + nu*lk*uk = Nk /\
  dup + nu*lp*up = Np /\
  duq + nu*lq*uq = Nq /\
  dc = duk*up*uq + uk*dup*uq + uk*up*duq.

Theorem GPLM40_MODAL_CERTIFICATE_GIVES_THREE_SOURCE :
  forall
    nu lk lp lq
    uk up uq
    duk dup duq
    Nk Np Nq dc : R,
    ModalTriadCertificate
      nu lk lp lq uk up uq duk dup duq Nk Np Nq dc ->
    dc + nu * gamma lk lp lq * triad_work uk up uq
      =
      source1 Nk up uq
      + source2 uk Np uq
      + source3 uk up Nq.
Proof.
  intros nu lk lp lq uk up uq duk dup duq Nk Np Nq dc H.
  destruct H as [Hk [Hp [Hq Hdc]]].
  unfold gamma, triad_work, source1, source2, source3.
  eapply GPLM10_THREE_LEG_MODAL_SOURCE_SPLIT; eauto.
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.

Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM00_POS_NONNEG.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM01_POS_DOMINATES.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM02_POS_THREE_SUBADDITIVE.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM10_THREE_LEG_MODAL_SOURCE_SPLIT.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM11_GAMMA_NONNEG.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM12_GAMMA_POSITIVE_IF_ONE_MODE_POSITIVE.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM20_POSITIVE_THREE_SOURCE_DOMINATION.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM21_DAMPED_WORK_POSITIVE_FORCING.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM22_MODAL_SOURCE_POSITIVE_DOMINATION.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM30_RANK_ONE_STAR_MINOR_ZERO.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM31_STAR_AGGREGATION_FACTORS.
Check NSE_GP_LERAY_MODAL_TRIAD_ADAPTER.GPLM40_MODAL_CERTIFICATE_GIVES_THREE_SOURCE.
