
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_gp_ae_modal_semantics_v0_23_1.
Require Import awpi_nse_leray_ae_to_parent_route_v0_39_0.

Open Scope R_scope.

Module NSE_LERAY_PROJECTED_MODES.

Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module AE := NSE_GP_AE_MODAL_SEMANTICS.
Module L39 := NSE_LERAY_AE_TO_PARENT_ROUTE.

(* ===================================================================== *)
(* One Fourier/helical mode after direct projection of the LH weak form.  *)
(*                                                                         *)
(* Instead of assuming CModalEq as an opaque field, retain the two scalar *)
(* real/imaginary balances that are exactly what fixed-mode testing must   *)
(* establish.                                                              *)
(* ===================================================================== *)

Record LerayHopfProjectedMode
  (CoNull : (R -> Prop) -> Prop)
  (nu lambda : R) : Type := {
  lhpm_u : R -> CH.C2;
  lhpm_dt_u : R -> CH.C2;
  lhpm_N : R -> CH.C2;

  lhpm_good : R -> Prop;
  lhpm_conull : CoNull lhpm_good;

  lhpm_balance_re :
    forall t : R,
      lhpm_good t ->
      CH.cre (lhpm_dt_u t)
      + (nu * lambda) * CH.cre (lhpm_u t)
      =
      CH.cre (lhpm_N t);

  lhpm_balance_im :
    forall t : R,
      lhpm_good t ->
      CH.cim (lhpm_dt_u t)
      + (nu * lambda) * CH.cim (lhpm_u t)
      =
      CH.cim (lhpm_N t)
}.

Theorem LH40_00_PROJECTED_MODE_GIVES_COMPLEX_MODAL_EQUATION :
  forall CoNull : (R -> Prop) -> Prop,
  forall nu lambda : R,
  forall M : LerayHopfProjectedMode CoNull nu lambda,
  forall t : R,
    lhpm_good CoNull nu lambda M t ->
    CH.CModalEq
      nu lambda
      (lhpm_u CoNull nu lambda M t)
      (lhpm_dt_u CoNull nu lambda M t)
      (lhpm_N CoNull nu lambda M t).
Proof.
  intros CoNull nu lambda M t Hgood.
  unfold CH.CModalEq, CH.ceq, CH.cadd, CH.cscale,
         CH.cre, CH.cim.
  simpl.
  split.
  - exact (lhpm_balance_re CoNull nu lambda M t Hgood).
  - exact (lhpm_balance_im CoNull nu lambda M t Hgood).
Qed.

Definition build_ae_modal_from_projected
  {CoNull : (R -> Prop) -> Prop}
  {nu lambda : R}
  (M : LerayHopfProjectedMode CoNull nu lambda)
  : AE.AEModalData CoNull nu lambda :=
  {|
    AE.ae_u := lhpm_u CoNull nu lambda M;
    AE.ae_dt_u := lhpm_dt_u CoNull nu lambda M;
    AE.ae_N := lhpm_N CoNull nu lambda M;
    AE.ae_modal_good := lhpm_good CoNull nu lambda M;
    AE.ae_modal_conull := lhpm_conull CoNull nu lambda M;
    AE.ae_modal_equation :=
      LH40_00_PROJECTED_MODE_GIVES_COMPLEX_MODAL_EQUATION
        CoNull nu lambda M
  |}.

Theorem LH40_01_PROJECTED_MODE_BUILDS_AE_MODAL :
  forall CoNull : (R -> Prop) -> Prop,
  forall nu lambda : R,
  forall M : LerayHopfProjectedMode CoNull nu lambda,
    exists A : AE.AEModalData CoNull nu lambda,
      AE.ae_u CoNull nu lambda A
        = lhpm_u CoNull nu lambda M /\
      AE.ae_dt_u CoNull nu lambda A
        = lhpm_dt_u CoNull nu lambda M /\
      AE.ae_N CoNull nu lambda A
        = lhpm_N CoNull nu lambda M.
Proof.
  intros CoNull nu lambda M.
  exists (build_ae_modal_from_projected M).
  repeat split; reflexivity.
Qed.

(* ===================================================================== *)
(* Three projected LH modes.                                              *)
(* No separate cubic-Leibniz certificate is assumed.                      *)
(* ===================================================================== *)

Record LerayHopfProjectedTriad
  (CoNull : (R -> Prop) -> Prop)
  (C : CH.C2) (nu lk lp lq : R) : Type := {
  lhpt_k : LerayHopfProjectedMode CoNull nu lk;
  lhpt_p : LerayHopfProjectedMode CoNull nu lp;
  lhpt_q : LerayHopfProjectedMode CoNull nu lq
}.

Definition projected_cubic_dt
  {CoNull : (R -> Prop) -> Prop}
  {C : CH.C2} {nu lk lp lq : R}
  (T : LerayHopfProjectedTriad CoNull C nu lk lp lq)
  (t : R) : R :=
  CH.ctriad
    C
    (lhpm_dt_u CoNull nu lk
      (lhpt_k CoNull C nu lk lp lq T) t)
    (lhpm_u CoNull nu lp
      (lhpt_p CoNull C nu lk lp lq T) t)
    (lhpm_u CoNull nu lq
      (lhpt_q CoNull C nu lk lp lq T) t)
  +
  CH.ctriad
    C
    (lhpm_u CoNull nu lk
      (lhpt_k CoNull C nu lk lp lq T) t)
    (lhpm_dt_u CoNull nu lp
      (lhpt_p CoNull C nu lk lp lq T) t)
    (lhpm_u CoNull nu lq
      (lhpt_q CoNull C nu lk lp lq T) t)
  +
  CH.ctriad
    C
    (lhpm_u CoNull nu lk
      (lhpt_k CoNull C nu lk lp lq T) t)
    (lhpm_u CoNull nu lp
      (lhpt_p CoNull C nu lk lp lq T) t)
    (lhpm_dt_u CoNull nu lq
      (lhpt_q CoNull C nu lk lp lq T) t).

Definition projected_triad_good
  {CoNull : (R -> Prop) -> Prop}
  {C : CH.C2} {nu lk lp lq : R}
  (T : LerayHopfProjectedTriad CoNull C nu lk lp lq)
  (t : R) : Prop :=
  lhpm_good CoNull nu lk
    (lhpt_k CoNull C nu lk lp lq T) t /\
  lhpm_good CoNull nu lp
    (lhpt_p CoNull C nu lk lp lq T) t /\
  lhpm_good CoNull nu lq
    (lhpt_q CoNull C nu lk lp lq T) t.

Theorem LH40_10_PROJECTED_TRIAD_GOOD_IS_CONULL :
  forall CoNull : (R -> Prop) -> Prop,
    AE.CoNullCalculus CoNull ->
    forall C : CH.C2,
    forall nu lk lp lq : R,
    forall T : LerayHopfProjectedTriad CoNull C nu lk lp lq,
      CoNull (projected_triad_good T).
Proof.
  intros CoNull HC C nu lk lp lq T.
  unfold projected_triad_good.
  eapply AE.GPAE00_INTER3.
  - exact HC.
  - exact
      (lhpm_conull CoNull nu lk
        (lhpt_k CoNull C nu lk lp lq T)).
  - exact
      (lhpm_conull CoNull nu lp
        (lhpt_p CoNull C nu lk lp lq T)).
  - exact
      (lhpm_conull CoNull nu lq
        (lhpt_q CoNull C nu lk lp lq T)).
Qed.

Theorem LH40_11_PROJECTED_CUBIC_DT_GIVES_LEIBNIZ :
  forall CoNull : (R -> Prop) -> Prop,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : LerayHopfProjectedTriad CoNull C nu lk lp lq,
  forall t : R,
    CH.CTriadLeibniz
      C
      (lhpm_u CoNull nu lk
        (lhpt_k CoNull C nu lk lp lq T) t)
      (lhpm_u CoNull nu lp
        (lhpt_p CoNull C nu lk lp lq T) t)
      (lhpm_u CoNull nu lq
        (lhpt_q CoNull C nu lk lp lq T) t)
      (lhpm_dt_u CoNull nu lk
        (lhpt_k CoNull C nu lk lp lq T) t)
      (lhpm_dt_u CoNull nu lp
        (lhpt_p CoNull C nu lk lp lq T) t)
      (lhpm_dt_u CoNull nu lq
        (lhpt_q CoNull C nu lk lp lq T) t)
      (projected_cubic_dt T t).
Proof.
  intros.
  unfold CH.CTriadLeibniz, projected_cubic_dt.
  reflexivity.
Qed.

Definition build_ae_triad_from_projected
  {CoNull : (R -> Prop) -> Prop}
  (HC : AE.CoNullCalculus CoNull)
  {C : CH.C2} {nu lk lp lq : R}
  (T : LerayHopfProjectedTriad CoNull C nu lk lp lq)
  : AE.AETriadSemanticData CoNull C nu lk lp lq :=
  {|
    AE.ae_k :=
      build_ae_modal_from_projected
        (lhpt_k CoNull C nu lk lp lq T);

    AE.ae_p :=
      build_ae_modal_from_projected
        (lhpt_p CoNull C nu lk lp lq T);

    AE.ae_q :=
      build_ae_modal_from_projected
        (lhpt_q CoNull C nu lk lp lq T);

    AE.ae_dc := projected_cubic_dt T;

    AE.ae_leibniz_good := projected_triad_good T;

    AE.ae_leibniz_conull :=
      LH40_10_PROJECTED_TRIAD_GOOD_IS_CONULL
        CoNull HC C nu lk lp lq T;

    AE.ae_leibniz :=
      fun t _ =>
        LH40_11_PROJECTED_CUBIC_DT_GIVES_LEIBNIZ
          CoNull C nu lk lp lq T t
  |}.

Theorem LH40_12_PROJECTED_TRIAD_BUILDS_AE_TRIAD :
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : LerayHopfProjectedTriad CoNull C nu lk lp lq,
    exists A : AE.AETriadSemanticData CoNull C nu lk lp lq,
      AE.ae_dc CoNull C nu lk lp lq A
        = projected_cubic_dt T.
Proof.
  intros.
  exists (build_ae_triad_from_projected HC T).
  reflexivity.
Qed.

(* ===================================================================== *)
(* Compose directly with v0.39.0: projected LH modes -> ParentRoute_3     *)
(* on a co-null set of times.                                             *)
(* ===================================================================== *)

Definition projected_leray_parent_route_realized
  {CoNull : (R -> Prop) -> Prop}
  (HC : AE.CoNullCalculus CoNull)
  {C : CH.C2} {nu lk lp lq : R}
  (T : LerayHopfProjectedTriad CoNull C nu lk lp lq)
  (t : R) : Prop :=
  L39.leray_parent_route_realized
    CoNull C nu lk lp lq
    (build_ae_triad_from_projected HC T)
    t.

Theorem LH40_20_PROJECTED_LERAY_TRIAD_GIVES_PARENT_ROUTE_CONULL :
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : LerayHopfProjectedTriad CoNull C nu lk lp lq,
    CoNull
      (projected_leray_parent_route_realized HC T).
Proof.
  intros CoNull HC C nu lk lp lq T.
  unfold projected_leray_parent_route_realized.
  exact
    (L39.LH39_21_LERAY_PARENT_ROUTE_REALIZED_CONULL
      CoNull HC C nu lk lp lq
      (build_ae_triad_from_projected HC T)).
Qed.

(* The remaining leftmost theorem is now sharply isolated:
     textbook Leray-Hopf weak formulation
       -> LerayHopfProjectedMode
   for each fixed Fourier/helical mode.
   In analysis language this is the standard fixed smooth-test projection
   plus W^{1,1}_loc / AC representative theorem. *)

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_LERAY_PROJECTED_MODES.

Check NSE_LERAY_PROJECTED_MODES.LerayHopfProjectedMode.
Check NSE_LERAY_PROJECTED_MODES.LH40_00_PROJECTED_MODE_GIVES_COMPLEX_MODAL_EQUATION.
Check NSE_LERAY_PROJECTED_MODES.build_ae_modal_from_projected.
Check NSE_LERAY_PROJECTED_MODES.LH40_01_PROJECTED_MODE_BUILDS_AE_MODAL.
Check NSE_LERAY_PROJECTED_MODES.LerayHopfProjectedTriad.
Check NSE_LERAY_PROJECTED_MODES.projected_cubic_dt.
Check NSE_LERAY_PROJECTED_MODES.projected_triad_good.
Check NSE_LERAY_PROJECTED_MODES.LH40_10_PROJECTED_TRIAD_GOOD_IS_CONULL.
Check NSE_LERAY_PROJECTED_MODES.LH40_11_PROJECTED_CUBIC_DT_GIVES_LEIBNIZ.
Check NSE_LERAY_PROJECTED_MODES.build_ae_triad_from_projected.
Check NSE_LERAY_PROJECTED_MODES.LH40_12_PROJECTED_TRIAD_BUILDS_AE_TRIAD.
Check NSE_LERAY_PROJECTED_MODES.LH40_20_PROJECTED_LERAY_TRIAD_GIVES_PARENT_ROUTE_CONULL.
