From Stdlib Require Import Reals Lra Psatz Strings.String.
Require Import NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_gp_ae_modal_semantics_v0_23_1.
Require Import awpi_nse_leray_weak_test_specialization_v0_42_1.
Require Import awpi_nse_leray_projected_modes_v0_40_0.

Open Scope R_scope.

Module NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.

Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module AE := NSE_GP_AE_MODAL_SEMANTICS.
Module L42 := NSE_LERAY_WEAK_TEST_SPECIALIZATION.
Module E4 :=
  NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.

(* ====================================================================== *)
(* Generic linear scalar-distribution pairing.                            *)
(* ====================================================================== *)

Record LinearScalarDistributionPairing
  (W : L42.WeakTestCalculus) : Type := {
  lsp_pair :
    (R -> CH.C2) -> L42.time_test W -> CH.C2;

  lsp_add :
    forall f g : R -> CH.C2,
    forall eta : L42.time_test W,
      L42.time_admissible W eta ->
      lsp_pair (fun t => CH.cadd (f t) (g t)) eta
      = CH.cadd (lsp_pair f eta) (lsp_pair g eta);

  lsp_scale :
    forall a : R,
    forall f : R -> CH.C2,
    forall eta : L42.time_test W,
      L42.time_admissible W eta ->
      lsp_pair (fun t => CH.cscale a (f t)) eta
      = CH.cscale a (lsp_pair f eta)
}.

Definition modal_residual
  (nu lambda : R)
  (u du N : R -> CH.C2)
  (t : R) : CH.C2 :=
  CH.cadd
    (CH.cadd (du t) (CH.cscale (nu * lambda) (u t)))
    (CH.cscale (-1) (N t)).

Theorem DB00_MODAL_EQ_GIVES_RESIDUAL_ZERO :
  forall nu lambda : R,
  forall u du N : CH.C2,
    CH.CModalEq nu lambda u du N ->
    CH.cadd
      (CH.cadd du (CH.cscale (nu * lambda) u))
      (CH.cscale (-1) N)
    = (0,0).
Proof.
  intros nu lambda [ur ui] [dur dui] [Nr Ni] H.
  unfold CH.CModalEq, CH.ceq, CH.cadd, CH.cscale,
         CH.cre, CH.cim in H |- *.
  simpl in H |- *.
  destruct H as [Hre Him].
  f_equal; lra.
Qed.

Theorem DB01_RESIDUAL_ZERO_GIVES_MODAL_EQ :
  forall nu lambda : R,
  forall u du N : CH.C2,
    CH.cadd
      (CH.cadd du (CH.cscale (nu * lambda) u))
      (CH.cscale (-1) N)
    = (0,0) ->
    CH.CModalEq nu lambda u du N.
Proof.
  intros nu lambda [ur ui] [dur dui] [Nr Ni] H.
  unfold CH.CModalEq, CH.ceq, CH.cadd, CH.cscale,
         CH.cre, CH.cim in H |- *.
  simpl in H |- *.
  injection H as Hre Him.
  split; lra.
Qed.

Theorem DB02_PAIRING_OF_MODAL_RESIDUAL :
  forall W : L42.WeakTestCalculus,
  forall P : LinearScalarDistributionPairing W,
  forall nu lambda : R,
  forall u du N : R -> CH.C2,
  forall eta : L42.time_test W,
    L42.time_admissible W eta ->
    lsp_pair W P (modal_residual nu lambda u du N) eta
    =
    CH.cadd
      (CH.cadd
        (lsp_pair W P du eta)
        (CH.cscale (nu * lambda) (lsp_pair W P u eta)))
      (CH.cscale (-1) (lsp_pair W P N eta)).
Proof.
  intros W P nu lambda u du N eta Heta.
  unfold modal_residual.
  rewrite (lsp_add W P
    (fun t => CH.cadd (du t) (CH.cscale (nu * lambda) (u t)))
    (fun t => CH.cscale (-1) (N t)) eta Heta).
  rewrite (lsp_add W P du
    (fun t => CH.cscale (nu * lambda) (u t)) eta Heta).
  rewrite (lsp_scale W P (nu * lambda) u eta Heta).
  rewrite (lsp_scale W P (-1) N eta Heta).
  reflexivity.
Qed.

(* The only generic distribution theorem still required: a represented     *)
(* scalar distribution which pairs to zero against every admissible time   *)
(* test vanishes on a co-null set.                                         *)
Record ZeroDistributionAEFaithfulness
  (W : L42.WeakTestCalculus)
  (CoNull : (R -> Prop) -> Prop)
  (P : LinearScalarDistributionPairing W) : Type := {
  zdf_zero_ae :
    forall f : R -> CH.C2,
      (forall eta : L42.time_test W,
        L42.time_admissible W eta ->
        lsp_pair W P f eta = (0,0)) ->
      CoNull (fun t : R => f t = (0,0))
}.

Definition build_scalar_distribution_ae_criterion
  {W : L42.WeakTestCalculus}
  {CoNull : (R -> Prop) -> Prop}
  (HC : AE.CoNullCalculus CoNull)
  (P : LinearScalarDistributionPairing W)
  (F : ZeroDistributionAEFaithfulness W CoNull P)
  : E4.ScalarDistributionAECriterion W CoNull.
Proof.
  refine
    {| E4.sd_pair := lsp_pair W P |}.
  intros nu lambda u du N Hdist.
  pose proof
    (zdf_zero_ae W CoNull P F
      (modal_residual nu lambda u du N)) as Hzero.
  assert (Hzero_dist :
    forall eta : L42.time_test W,
      L42.time_admissible W eta ->
      lsp_pair W P (modal_residual nu lambda u du N) eta = (0,0)).
  {
    intros eta Heta.
    rewrite (DB02_PAIRING_OF_MODAL_RESIDUAL
      W P nu lambda u du N eta Heta).
    exact
      (DB00_MODAL_EQ_GIVES_RESIDUAL_ZERO
        nu lambda
        (lsp_pair W P u eta)
        (lsp_pair W P du eta)
        (lsp_pair W P N eta)
        (Hdist eta Heta)).
  }
  specialize (Hzero Hzero_dist).
  eapply (AE.cn_mono CoNull HC
    (fun t => modal_residual nu lambda u du N t = (0,0))
    (fun t => CH.CModalEq nu lambda (u t) (du t) (N t))).
  - exact Hzero.
  - intros t Ht.
    exact (DB01_RESIDUAL_ZERO_GIVES_MODAL_EQ
      nu lambda (u t) (du t) (N t) Ht).
Defined.

Theorem DB03_LINEAR_PAIRING_PLUS_FAITHFULNESS_BUILDS_AE_CRITERION :
  forall W : L42.WeakTestCalculus,
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall P : LinearScalarDistributionPairing W,
  forall F : ZeroDistributionAEFaithfulness W CoNull P,
    exists S : E4.ScalarDistributionAECriterion W CoNull, True.
Proof.
  intros.
  exists (build_scalar_distribution_ae_criterion HC P F).
  exact I.
Qed.

(* ====================================================================== *)
(* Universal representatives for the actual weak terms.                   *)
(*                                                                         *)
(* This is stronger and cleaner than asking every fixed helical mode for   *)
(* three unrelated representation witnesses.                              *)
(* ====================================================================== *)

Record WeakTermDistributionRepresentation
  (W : L42.WeakTestCalculus)
  (P : LinearScalarDistributionPairing W) : Type := {
  wtr_dt : L42.space_test W -> R -> CH.C2;
  wtr_stokes : L42.space_test W -> R -> CH.C2;
  wtr_nonlinear : L42.space_test W -> R -> CH.C2;

  wtr_dt_rep :
    forall phi : L42.space_test W,
    forall eta : L42.time_test W,
      L42.space_admissible W phi ->
      L42.time_admissible W eta ->
      L42.weak_dt_term W phi eta
      = lsp_pair W P (wtr_dt phi) eta;

  wtr_stokes_rep :
    forall phi : L42.space_test W,
    forall eta : L42.time_test W,
      L42.space_admissible W phi ->
      L42.time_admissible W eta ->
      L42.weak_stokes_term W phi eta
      = lsp_pair W P (wtr_stokes phi) eta;

  wtr_nonlinear_rep :
    forall phi : L42.space_test W,
    forall eta : L42.time_test W,
      L42.space_admissible W phi ->
      L42.time_admissible W eta ->
      L42.weak_nonlinear_term W phi eta
      = lsp_pair W P (wtr_nonlinear phi) eta
}.

Theorem DB10_CSCALE_INV_CANCEL :
  forall a : R, a <> 0 ->
  forall z : CH.C2,
    CH.cscale (/ a) (CH.cscale a z) = z.
Proof.
  intros a Ha [x y].
  unfold CH.cscale, CH.cre, CH.cim.
  simpl.
  f_equal; field; exact Ha.
Qed.

Theorem DB11_CSCALE_NEG_ONE_INVOLUTION :
  forall z : CH.C2,
    CH.cscale (-1) (CH.cscale (-1) z) = z.
Proof.
  intros [x y].
  unfold CH.cscale, CH.cre, CH.cim.
  simpl.
  f_equal; ring.
Qed.

Definition mode_u_rep
  {W : L42.WeakTestCalculus}
  {P : LinearScalarDistributionPairing W}
  (Rwt : WeakTermDistributionRepresentation W P)
  {lambda : R}
  (M : L42.HelicalWeakMode W lambda)
  (t : R) : CH.C2 :=
  CH.cscale (/ lambda)
    (wtr_stokes W P Rwt (L42.hwm_phi W lambda M) t).

Definition mode_du_rep
  {W : L42.WeakTestCalculus}
  {P : LinearScalarDistributionPairing W}
  (Rwt : WeakTermDistributionRepresentation W P)
  {lambda : R}
  (M : L42.HelicalWeakMode W lambda)
  (t : R) : CH.C2 :=
  wtr_dt W P Rwt (L42.hwm_phi W lambda M) t.

Definition mode_N_rep
  {W : L42.WeakTestCalculus}
  {P : LinearScalarDistributionPairing W}
  (Rwt : WeakTermDistributionRepresentation W P)
  {lambda : R}
  (M : L42.HelicalWeakMode W lambda)
  (t : R) : CH.C2 :=
  CH.cscale (-1)
    (wtr_nonlinear W P Rwt (L42.hwm_phi W lambda M) t).

Definition build_mode_distribution_representation
  {W : L42.WeakTestCalculus}
  {CoNull : (R -> Prop) -> Prop}
  {P : LinearScalarDistributionPairing W}
  (HC : AE.CoNullCalculus CoNull)
  (F : ZeroDistributionAEFaithfulness W CoNull P)
  (Rwt : WeakTermDistributionRepresentation W P)
  {lambda : R}
  (M : L42.HelicalWeakMode W lambda)
  (Hlambda : lambda <> 0)
  : E4.ModeDistributionRepresentation
      W CoNull
      (build_scalar_distribution_ae_criterion HC P F)
      lambda M.
Proof.
  refine
    {| E4.mdr_u := mode_u_rep Rwt M;
       E4.mdr_du := mode_du_rep Rwt M;
       E4.mdr_N := mode_N_rep Rwt M |}.
  - intros eta Heta.
    pose proof
      (wtr_stokes_rep W P Rwt
        (L42.hwm_phi W lambda M) eta
        (L42.hwm_phi_admissible W lambda M) Heta) as Hrep.
    pose proof
      (L42.hwm_stokes_eigen_test W lambda M eta Heta) as Heig.
    change
      (L42.hwm_U W lambda M eta
       = lsp_pair W P
           (fun t : R =>
              CH.cscale (/ lambda)
                (wtr_stokes W P Rwt (L42.hwm_phi W lambda M) t))
           eta).
    rewrite (lsp_scale W P (/ lambda)
      (wtr_stokes W P Rwt (L42.hwm_phi W lambda M)) eta Heta).
    rewrite <- Hrep.
    rewrite Heig.
    symmetry.
    exact (DB10_CSCALE_INV_CANCEL lambda Hlambda
      (L42.hwm_U W lambda M eta)).
  - intros eta Heta.
    change
      (L42.hwm_dU W lambda M eta
       = lsp_pair W P
           (wtr_dt W P Rwt (L42.hwm_phi W lambda M))
           eta).
    rewrite <- (wtr_dt_rep W P Rwt
      (L42.hwm_phi W lambda M) eta
      (L42.hwm_phi_admissible W lambda M) Heta).
    symmetry.
    exact (L42.hwm_dt_identification W lambda M eta Heta).
  - intros eta Heta.
    pose proof
      (wtr_nonlinear_rep W P Rwt
        (L42.hwm_phi W lambda M) eta
        (L42.hwm_phi_admissible W lambda M) Heta) as Hrep.
    pose proof
      (L42.hwm_nonlinear_source W lambda M eta Heta) as Hsrc.
    change
      (L42.hwm_N W lambda M eta
       = lsp_pair W P
           (fun t : R =>
              CH.cscale (-1)
                (wtr_nonlinear W P Rwt (L42.hwm_phi W lambda M) t))
           eta).
    rewrite (lsp_scale W P (-1)
      (wtr_nonlinear W P Rwt (L42.hwm_phi W lambda M)) eta Heta).
    rewrite <- Hrep.
    rewrite Hsrc.
    symmetry.
    exact (DB11_CSCALE_NEG_ONE_INVOLUTION
      (L42.hwm_N W lambda M eta)).
Defined.

Theorem DB12_NONZERO_MODE_REPRESENTATION_IS_DERIVED_FROM_WEAK_TERMS :
  forall W : L42.WeakTestCalculus,
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall P : LinearScalarDistributionPairing W,
  forall F : ZeroDistributionAEFaithfulness W CoNull P,
  forall Rwt : WeakTermDistributionRepresentation W P,
  forall lambda : R,
  forall M : L42.HelicalWeakMode W lambda,
    lambda <> 0 ->
    exists Rm : E4.ModeDistributionRepresentation
      W CoNull (build_scalar_distribution_ae_criterion HC P F) lambda M,
      True.
Proof.
  intros.
  exists (build_mode_distribution_representation HC F Rwt M H).
  exact I.
Qed.

(* Three nonzero helical modes are therefore represented from one universal *)
(* weak-term representation package.                                      *)
Definition build_triad_distribution_representation
  {W : L42.WeakTestCalculus}
  {CoNull : (R -> Prop) -> Prop}
  {P : LinearScalarDistributionPairing W}
  (HC : AE.CoNullCalculus CoNull)
  (F : ZeroDistributionAEFaithfulness W CoNull P)
  (Rwt : WeakTermDistributionRepresentation W P)
  {lk lp lq : R}
  (T : L42.HelicalWeakTriad W lk lp lq)
  (Hlk : lk <> 0) (Hlp : lp <> 0) (Hlq : lq <> 0)
  : E4.TriadDistributionRepresentation
      W CoNull
      (build_scalar_distribution_ae_criterion HC P F)
      lk lp lq T.
Proof.
  refine
    {| E4.tdr_k :=
         build_mode_distribution_representation
           HC F Rwt (L42.hwt_k W lk lp lq T) Hlk;
       E4.tdr_p :=
         build_mode_distribution_representation
           HC F Rwt (L42.hwt_p W lk lp lq T) Hlp;
       E4.tdr_q :=
         build_mode_distribution_representation
           HC F Rwt (L42.hwt_q W lk lp lq T) Hlq |}.
Defined.

Theorem DB20_WEAK_LH_TRIAD_WITH_STANDARD_REPRESENTATION_GIVES_ROUTE_CONULL :
  forall W : L42.WeakTestCalculus,
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall P : LinearScalarDistributionPairing W,
  forall F : ZeroDistributionAEFaithfulness W CoNull P,
  forall Rwt : WeakTermDistributionRepresentation W P,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall H : L42.LerayHopfWeakMomentum W nu,
  forall T : L42.HelicalWeakTriad W lk lp lq,
  forall Hlk : lk <> 0,
  forall Hlp : lp <> 0,
  forall Hlq : lq <> 0,
    CoNull
      (@NSE_LERAY_PROJECTED_MODES.projected_leray_parent_route_realized
        CoNull HC C nu lk lp lq
        (E4.build_projected_triad_from_weak_representation
          (C := C)
          (build_scalar_distribution_ae_criterion HC P F)
          H T
          (build_triad_distribution_representation
            HC F Rwt T Hlk Hlp Hlq))).
Proof.
  intros W CoNull HC P F Rwt C nu lk lp lq H T Hlk Hlp Hlq.
  exact
    (E4.DIAMOND_AE20_REPRESENTED_WEAK_TRIAD_GIVES_PARENT_ROUTE_CONULL
      W CoNull HC
      (build_scalar_distribution_ae_criterion HC P F)
      C nu lk lp lq H T
      (build_triad_distribution_representation
        HC F Rwt T Hlk Hlp Hlq)).
Qed.

(* ====================================================================== *)
(* Claim boundary after contraction.                                      *)
(* ====================================================================== *)

Definition ZERO_DISTRIBUTION_AE_FAITHFULNESS_FRONTIER : Prop := True.
Definition LH_WEAK_TERM_DISTRIBUTION_REPRESENTATION_FRONTIER : Prop := True.
Definition GLOBAL_LH_ROUTE_ASSEMBLY_FRONTIER : Prop := True.
Definition CRITICAL_TIME_ROUTE_DEPTH_FRONTIER : Prop := True.

Definition STATUS : string :=
  "NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE_V0_5_0"%string.

End NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.

Check NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.LinearScalarDistributionPairing.
Check NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.ZeroDistributionAEFaithfulness.
Check NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.build_scalar_distribution_ae_criterion.
Check NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.DB03_LINEAR_PAIRING_PLUS_FAITHFULNESS_BUILDS_AE_CRITERION.
Check NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.WeakTermDistributionRepresentation.
Check NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.build_mode_distribution_representation.
Check NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.DB12_NONZERO_MODE_REPRESENTATION_IS_DERIVED_FROM_WEAK_TERMS.
Check NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.build_triad_distribution_representation.
Check NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.DB20_WEAK_LH_TRIAD_WITH_STANDARD_REPRESENTATION_GIVES_ROUTE_CONULL.

Print Assumptions NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.DB03_LINEAR_PAIRING_PLUS_FAITHFULNESS_BUILDS_AE_CRITERION.
Print Assumptions NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.DB12_NONZERO_MODE_REPRESENTATION_IS_DERIVED_FROM_WEAK_TERMS.
Print Assumptions NSE_R3_F0_GP_DIAMOND_DISTRIBUTION_BRIDGE.DB20_WEAK_LH_TRIAD_WITH_STANDARD_REPRESENTATION_GIVES_ROUTE_CONULL.
