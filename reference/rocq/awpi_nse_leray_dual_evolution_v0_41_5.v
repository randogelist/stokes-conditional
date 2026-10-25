
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_gp_ae_modal_semantics_v0_23_1.
Require Import awpi_nse_leray_ae_to_parent_route_v0_39_0.
Require Import awpi_nse_leray_projected_modes_v0_40_0.

Open Scope R_scope.

Module NSE_LERAY_DUAL_EVOLUTION.

Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module AE := NSE_GP_AE_MODAL_SEMANTICS.
Module L39 := NSE_LERAY_AE_TO_PARENT_ROUTE.
Module L40 := NSE_LERAY_PROJECTED_MODES.

(* ===================================================================== *)
(* Abstract V' algebra + one fixed Fourier/helical evaluation functional. *)
(* This is the standard spatial projection part of the LH evolution law.  *)
(* ===================================================================== *)

Record DualEvolutionOps : Type := {
  dv : Type;
  dzero : dv;
  dadd : dv -> dv -> dv;
  dscale : R -> dv -> dv;

  deval : dv -> CH.C2;

  deval_zero :
    deval dzero = (0, 0);

  deval_add :
    forall x y : dv,
      deval (dadd x y)
      =
      CH.cadd (deval x) (deval y);

  deval_scale :
    forall a : R,
    forall x : dv,
      deval (dscale a x)
      =
      CH.cscale a (deval x)
}.

Definition projected_nonlinear
  (O : DualEvolutionOps)
  (B : dv O) : CH.C2 :=
  CH.cscale (-1) (deval O B).

(* ===================================================================== *)
(* One mode in the a.e. V'-evolution formulation of Leray-Hopf.           *)
(*                                                                         *)
(* At good times:                                                         *)
(*      u_t + nu A u + B(u,u) = 0  in V'.                                *)
(* The fixed helical Fourier functional is represented by deval.          *)
(* Its Stokes eigen-relation is                                           *)
(*      <Au,e_k> = lambda_k <u,e_k>.                                      *)
(* ===================================================================== *)

Record LerayHopfDualEvolutionMode
  (CoNull : (R -> Prop) -> Prop)
  (O : DualEvolutionOps)
  (nu lambda : R) : Type := {
  lhdm_u : R -> CH.C2;

  lhdm_ut : R -> dv O;
  lhdm_Au : R -> dv O;
  lhdm_B : R -> dv O;

  lhdm_good : R -> Prop;
  lhdm_conull : CoNull lhdm_good;

  lhdm_evolution :
    forall t : R,
      lhdm_good t ->
      dadd O
        (lhdm_ut t)
        (dadd O
          (dscale O nu (lhdm_Au t))
          (lhdm_B t))
      =
      dzero O;

  lhdm_stokes_projection :
    forall t : R,
      lhdm_good t ->
      deval O (lhdm_Au t)
      =
      CH.cscale lambda (lhdm_u t)
}.

Theorem LH41_C2_REARRANGE_DAMPED_EVOLUTION :
  forall du u B : CH.C2,
  forall nu lambda : R,
    CH.cadd du
      (CH.cadd
        (CH.cscale nu (CH.cscale lambda u))
        B)
    =
    (0, 0)
    ->
    CH.CModalEq
      nu lambda
      u
      du
      (CH.cscale (-1) B).
Proof.
  intros [dur dui] [ur ui] [Br Bi] nu lambda H.
  unfold CH.CModalEq, CH.ceq, CH.cadd, CH.cscale,
         CH.cre, CH.cim in H |- *.
  simpl in H |- *.
  injection H as Hre Him.
  split.
  - replace ((nu * lambda) * ur)
      with (nu * (lambda * ur)) by ring.
    replace (-1 * Br) with (- Br) by ring.
    lra.
  - replace ((nu * lambda) * ui)
      with (nu * (lambda * ui)) by ring.
    replace (-1 * Bi) with (- Bi) by ring.
    lra.
Qed.

Theorem LH41_00_DUAL_EVOLUTION_GIVES_COMPLEX_MODAL_EQ :
  forall CoNull : (R -> Prop) -> Prop,
  forall O : DualEvolutionOps,
  forall nu lambda : R,
  forall M : LerayHopfDualEvolutionMode CoNull O nu lambda,
  forall t : R,
    lhdm_good CoNull O nu lambda M t ->
    CH.CModalEq
      nu lambda
      (lhdm_u CoNull O nu lambda M t)
      (deval O (lhdm_ut CoNull O nu lambda M t))
      (projected_nonlinear
        O
        (lhdm_B CoNull O nu lambda M t)).
Proof.
  intros CoNull O nu lambda M t Hgood.

  pose proof
    (lhdm_evolution CoNull O nu lambda M t Hgood)
    as Hevol.

  pose proof
    (f_equal (deval O) Hevol)
    as Heval.

  rewrite
    (deval_add O
      (lhdm_ut CoNull O nu lambda M t)
      (dadd O
        (dscale O nu (lhdm_Au CoNull O nu lambda M t))
        (lhdm_B CoNull O nu lambda M t)))
    in Heval.

  rewrite
    (deval_add O
      (dscale O nu (lhdm_Au CoNull O nu lambda M t))
      (lhdm_B CoNull O nu lambda M t))
    in Heval.

  rewrite
    (deval_scale O
      nu
      (lhdm_Au CoNull O nu lambda M t))
    in Heval.

  rewrite (deval_zero O) in Heval.

  rewrite
    (lhdm_stokes_projection
      CoNull O nu lambda M t Hgood)
    in Heval.

  unfold projected_nonlinear.

  exact
    (LH41_C2_REARRANGE_DAMPED_EVOLUTION
      (deval O (lhdm_ut CoNull O nu lambda M t))
      (lhdm_u CoNull O nu lambda M t)
      (deval O (lhdm_B CoNull O nu lambda M t))
      nu lambda
      Heval).
Qed.

(* The two scalar balances required by v0.40 are now THEOREMS. *)
Theorem LH41_01_DUAL_EVOLUTION_GIVES_REAL_PROJECTED_BALANCE :
  forall CoNull : (R -> Prop) -> Prop,
  forall O : DualEvolutionOps,
  forall nu lambda : R,
  forall M : LerayHopfDualEvolutionMode CoNull O nu lambda,
  forall t : R,
    lhdm_good CoNull O nu lambda M t ->
    CH.cre (deval O (lhdm_ut CoNull O nu lambda M t))
    +
    (nu * lambda)
      * CH.cre (lhdm_u CoNull O nu lambda M t)
    =
    CH.cre
      (projected_nonlinear
        O
        (lhdm_B CoNull O nu lambda M t)).
Proof.
  intros CoNull O nu lambda M t Hgood.
  pose proof
    (LH41_00_DUAL_EVOLUTION_GIVES_COMPLEX_MODAL_EQ
      CoNull O nu lambda M t Hgood)
    as H.
  unfold CH.CModalEq, CH.ceq in H.
  destruct H as [Hre Him].
  cbn [CH.cadd CH.cscale CH.cre] in Hre.
  exact Hre.
Qed.

Theorem LH41_02_DUAL_EVOLUTION_GIVES_IMAG_PROJECTED_BALANCE :
  forall CoNull : (R -> Prop) -> Prop,
  forall O : DualEvolutionOps,
  forall nu lambda : R,
  forall M : LerayHopfDualEvolutionMode CoNull O nu lambda,
  forall t : R,
    lhdm_good CoNull O nu lambda M t ->
    CH.cim (deval O (lhdm_ut CoNull O nu lambda M t))
    +
    (nu * lambda)
      * CH.cim (lhdm_u CoNull O nu lambda M t)
    =
    CH.cim
      (projected_nonlinear
        O
        (lhdm_B CoNull O nu lambda M t)).
Proof.
  intros CoNull O nu lambda M t Hgood.
  pose proof
    (LH41_00_DUAL_EVOLUTION_GIVES_COMPLEX_MODAL_EQ
      CoNull O nu lambda M t Hgood)
    as H.
  unfold CH.CModalEq, CH.ceq in H.
  destruct H as [Hre Him].
  cbn [CH.cadd CH.cscale CH.cim] in Him.
  exact Him.
Qed.

Definition build_projected_mode_from_dual
  {CoNull : (R -> Prop) -> Prop}
  {O : DualEvolutionOps}
  {nu lambda : R}
  (M : LerayHopfDualEvolutionMode CoNull O nu lambda)
  : L40.LerayHopfProjectedMode CoNull nu lambda :=
  {|
    L40.lhpm_u :=
      lhdm_u CoNull O nu lambda M;

    L40.lhpm_dt_u :=
      fun t =>
        deval O
          (lhdm_ut CoNull O nu lambda M t);

    L40.lhpm_N :=
      fun t =>
        projected_nonlinear
          O
          (lhdm_B CoNull O nu lambda M t);

    L40.lhpm_good :=
      lhdm_good CoNull O nu lambda M;

    L40.lhpm_conull :=
      lhdm_conull CoNull O nu lambda M;

    L40.lhpm_balance_re :=
      LH41_01_DUAL_EVOLUTION_GIVES_REAL_PROJECTED_BALANCE
        CoNull O nu lambda M;

    L40.lhpm_balance_im :=
      LH41_02_DUAL_EVOLUTION_GIVES_IMAG_PROJECTED_BALANCE
        CoNull O nu lambda M
  |}.

Theorem LH41_03_DUAL_MODE_BUILDS_PROJECTED_MODE :
  forall CoNull : (R -> Prop) -> Prop,
  forall O : DualEvolutionOps,
  forall nu lambda : R,
  forall M : LerayHopfDualEvolutionMode CoNull O nu lambda,
    exists P : L40.LerayHopfProjectedMode CoNull nu lambda,
      L40.lhpm_u CoNull nu lambda P
      =
      lhdm_u CoNull O nu lambda M.
Proof.
  intros.
  exists (build_projected_mode_from_dual M).
  reflexivity.
Qed.

(* ===================================================================== *)
(* Three actual dual-evolution modes -> the already passed LH chain.       *)
(* ===================================================================== *)

Record LerayHopfDualEvolutionTriad
  (CoNull : (R -> Prop) -> Prop)
  (O : DualEvolutionOps)
  (C : CH.C2)
  (nu lk lp lq : R) : Type := {
  lhdt_k :
    LerayHopfDualEvolutionMode CoNull O nu lk;

  lhdt_p :
    LerayHopfDualEvolutionMode CoNull O nu lp;

  lhdt_q :
    LerayHopfDualEvolutionMode CoNull O nu lq
}.

Definition build_projected_triad_from_dual
  {CoNull : (R -> Prop) -> Prop}
  {O : DualEvolutionOps}
  {C : CH.C2}
  {nu lk lp lq : R}
  (T : LerayHopfDualEvolutionTriad
        CoNull O C nu lk lp lq)
  : L40.LerayHopfProjectedTriad
      CoNull C nu lk lp lq :=
  {|
    L40.lhpt_k :=
      build_projected_mode_from_dual
        (lhdt_k CoNull O C nu lk lp lq T);

    L40.lhpt_p :=
      build_projected_mode_from_dual
        (lhdt_p CoNull O C nu lk lp lq T);

    L40.lhpt_q :=
      build_projected_mode_from_dual
        (lhdt_q CoNull O C nu lk lp lq T)
  |}.

Theorem LH41_10_DUAL_TRIAD_BUILDS_PROJECTED_TRIAD :
  forall CoNull : (R -> Prop) -> Prop,
  forall O : DualEvolutionOps,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : LerayHopfDualEvolutionTriad
              CoNull O C nu lk lp lq,
    exists P : L40.LerayHopfProjectedTriad
                 CoNull C nu lk lp lq,
      True.
Proof.
  intros.
  exists (build_projected_triad_from_dual T).
  exact I.
Qed.

Definition dual_leray_parent_route_realized
  {CoNull : (R -> Prop) -> Prop}
  (HC : AE.CoNullCalculus CoNull)
  {O : DualEvolutionOps}
  {C : CH.C2}
  {nu lk lp lq : R}
  (T : LerayHopfDualEvolutionTriad
        CoNull O C nu lk lp lq)
  (t : R) : Prop :=
  L40.projected_leray_parent_route_realized
    HC
    (build_projected_triad_from_dual T)
    t.

Theorem LH41_20_DUAL_LERAY_TRIAD_GIVES_PARENT_ROUTE_CONULL :
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall O : DualEvolutionOps,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : LerayHopfDualEvolutionTriad
              CoNull O C nu lk lp lq,
    CoNull
      (dual_leray_parent_route_realized HC T).
Proof.
  intros CoNull HC O C nu lk lp lq T.
  unfold dual_leray_parent_route_realized.
  exact
    (L40.LH40_20_PROJECTED_LERAY_TRIAD_GIVES_PARENT_ROUTE_CONULL
      CoNull HC C nu lk lp lq
      (build_projected_triad_from_dual T)).
Qed.

(* ===================================================================== *)
(* Frontier marker                                                         *)
(* ===================================================================== *)

(* After this file the spatial Fourier/helical projection itself is no
   longer a premise: it is derived from the a.e. V'-evolution equation and
   linear evaluation.

   What remains on the far left is the genuine infinite-dimensional
   analysis theorem:
       textbook integrated Leray-Hopf weak formulation
         -> a.e. V'-evolution representative u_t
         -> LerayHopfDualEvolutionMode
   together with the semantic fact that evaluating u_t is the genuine
   a.e. derivative of the scalar modal coefficient. *)

Definition RemainingWeakToDualEvolutionFrontier : Prop := True.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_LERAY_DUAL_EVOLUTION.

Check NSE_LERAY_DUAL_EVOLUTION.DualEvolutionOps.
Check NSE_LERAY_DUAL_EVOLUTION.projected_nonlinear.
Check NSE_LERAY_DUAL_EVOLUTION.LerayHopfDualEvolutionMode.
Check NSE_LERAY_DUAL_EVOLUTION.LH41_C2_REARRANGE_DAMPED_EVOLUTION.
Check NSE_LERAY_DUAL_EVOLUTION.LH41_00_DUAL_EVOLUTION_GIVES_COMPLEX_MODAL_EQ.
Check NSE_LERAY_DUAL_EVOLUTION.LH41_01_DUAL_EVOLUTION_GIVES_REAL_PROJECTED_BALANCE.
Check NSE_LERAY_DUAL_EVOLUTION.LH41_02_DUAL_EVOLUTION_GIVES_IMAG_PROJECTED_BALANCE.
Check NSE_LERAY_DUAL_EVOLUTION.build_projected_mode_from_dual.
Check NSE_LERAY_DUAL_EVOLUTION.LH41_03_DUAL_MODE_BUILDS_PROJECTED_MODE.
Check NSE_LERAY_DUAL_EVOLUTION.LerayHopfDualEvolutionTriad.
Check NSE_LERAY_DUAL_EVOLUTION.build_projected_triad_from_dual.
Check NSE_LERAY_DUAL_EVOLUTION.LH41_20_DUAL_LERAY_TRIAD_GIVES_PARENT_ROUTE_CONULL.
Check NSE_LERAY_DUAL_EVOLUTION.RemainingWeakToDualEvolutionFrontier.
