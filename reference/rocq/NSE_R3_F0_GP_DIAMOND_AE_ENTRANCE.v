From Stdlib Require Import Reals Lra Psatz String Lists.List.
Require Import NSE_R3_F0_GP_DIAMOND_LH_ROUTE.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_gp_ae_modal_semantics_v0_23_1.
Require Import awpi_nse_leray_ae_to_parent_route_v0_39_0.
Require Import awpi_nse_leray_projected_modes_v0_40_0.
Require Import awpi_nse_leray_weak_test_specialization_v0_42_1.

Open Scope R_scope.

Module NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.

Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module AE := NSE_GP_AE_MODAL_SEMANTICS.
Module L39 := NSE_LERAY_AE_TO_PARENT_ROUTE.
Module L40 := NSE_LERAY_PROJECTED_MODES.
Module L42 := NSE_LERAY_WEAK_TEST_SPECIALIZATION.

(* ====================================================================== *)
(* Universal scalar distribution -> a.e. criterion.                       *)
(*                                                                         *)
(* This is deliberately independent of NSE.  In the concrete analytic     *)
(* realization, sd_pair is integration against a compactly supported       *)
(* smooth time test.  sd_modal_eq_conull is the standard fact that an      *)
(* L^1_loc distribution represented by a function and equal to zero is     *)
(* zero almost everywhere.                                                 *)
(* ====================================================================== *)

Record ScalarDistributionAECriterion
  (W : L42.WeakTestCalculus)
  (CoNull : (R -> Prop) -> Prop) : Type := {
  sd_pair :
    (R -> CH.C2) -> L42.time_test W -> CH.C2;

  sd_modal_eq_conull :
    forall nu lambda : R,
    forall u du N : R -> CH.C2,
      (forall eta : L42.time_test W,
        L42.time_admissible W eta ->
        CH.CModalEq
          nu lambda
          (sd_pair u eta)
          (sd_pair du eta)
          (sd_pair N eta))
      ->
      CoNull
        (fun t : R =>
          CH.CModalEq nu lambda (u t) (du t) (N t))
}.

(* A weak helical mode whose three time distributions U,dU,N are all       *)
(* represented by actual scalar functions through the SAME sd_pair.       *)
Record ModeDistributionRepresentation
  (W : L42.WeakTestCalculus)
  (CoNull : (R -> Prop) -> Prop)
  (S : ScalarDistributionAECriterion W CoNull)
  (lambda : R)
  (M : L42.HelicalWeakMode W lambda) : Type := {
  mdr_u  : R -> CH.C2;
  mdr_du : R -> CH.C2;
  mdr_N  : R -> CH.C2;

  mdr_U_rep :
    forall eta : L42.time_test W,
      L42.time_admissible W eta ->
      L42.hwm_U W lambda M eta
      = sd_pair W CoNull S mdr_u eta;

  mdr_dU_rep :
    forall eta : L42.time_test W,
      L42.time_admissible W eta ->
      L42.hwm_dU W lambda M eta
      = sd_pair W CoNull S mdr_du eta;

  mdr_N_rep :
    forall eta : L42.time_test W,
      L42.time_admissible W eta ->
      L42.hwm_N W lambda M eta
      = sd_pair W CoNull S mdr_N eta
}.

(* Distributional modal equality + scalar representation gives the same    *)
(* modal ODE on a co-null set.                                              *)
Theorem DIAMOND_AE00_REPRESENTED_MODE_MODAL_EQ_CONULL :
  forall W : L42.WeakTestCalculus,
  forall CoNull : (R -> Prop) -> Prop,
  forall S : ScalarDistributionAECriterion W CoNull,
  forall nu lambda : R,
  forall M : L42.HelicalWeakMode W lambda,
  forall E : L42.FixedModeDistributionalEquation W nu lambda M,
  forall Rm : ModeDistributionRepresentation W CoNull S lambda M,
    CoNull
      (fun t : R =>
        CH.CModalEq
          nu lambda
          (mdr_u W CoNull S lambda M Rm t)
          (mdr_du W CoNull S lambda M Rm t)
          (mdr_N W CoNull S lambda M Rm t)).
Proof.
  intros W CoNull S nu lambda M E Rm.
  eapply (sd_modal_eq_conull W CoNull S nu lambda
    (mdr_u W CoNull S lambda M Rm)
    (mdr_du W CoNull S lambda M Rm)
    (mdr_N W CoNull S lambda M Rm)).
  intros eta Heta.
  pose proof (E eta Heta) as HE.
  rewrite (mdr_U_rep W CoNull S lambda M Rm eta Heta) in HE.
  rewrite (mdr_dU_rep W CoNull S lambda M Rm eta Heta) in HE.
  rewrite (mdr_N_rep W CoNull S lambda M Rm eta Heta) in HE.
  exact HE.
Qed.

Definition build_projected_mode_from_representation
  {W : L42.WeakTestCalculus}
  {CoNull : (R -> Prop) -> Prop}
  (S : ScalarDistributionAECriterion W CoNull)
  {nu lambda : R}
  {M : L42.HelicalWeakMode W lambda}
  (E : L42.FixedModeDistributionalEquation W nu lambda M)
  (Rm : ModeDistributionRepresentation W CoNull S lambda M)
  : L40.LerayHopfProjectedMode CoNull nu lambda.
Proof.
  refine
    {| L40.lhpm_u := mdr_u W CoNull S lambda M Rm;
       L40.lhpm_dt_u := mdr_du W CoNull S lambda M Rm;
       L40.lhpm_N := mdr_N W CoNull S lambda M Rm;
       L40.lhpm_good :=
         fun t : R =>
           CH.CModalEq
             nu lambda
             (mdr_u W CoNull S lambda M Rm t)
             (mdr_du W CoNull S lambda M Rm t)
             (mdr_N W CoNull S lambda M Rm t);
       L40.lhpm_conull :=
         DIAMOND_AE00_REPRESENTED_MODE_MODAL_EQ_CONULL
           W CoNull S nu lambda M E Rm |}.
  - intros t Hgood.
    unfold CH.CModalEq, CH.ceq, CH.cadd, CH.cscale in Hgood.
    exact (proj1 Hgood).
  - intros t Hgood.
    unfold CH.CModalEq, CH.ceq, CH.cadd, CH.cscale in Hgood.
    exact (proj2 Hgood).
Defined.

Theorem DIAMOND_AE01_REPRESENTED_MODE_BUILDS_PROJECTED_MODE :
  forall W : L42.WeakTestCalculus,
  forall CoNull : (R -> Prop) -> Prop,
  forall S : ScalarDistributionAECriterion W CoNull,
  forall nu lambda : R,
  forall M : L42.HelicalWeakMode W lambda,
  forall E : L42.FixedModeDistributionalEquation W nu lambda M,
  forall Rm : ModeDistributionRepresentation W CoNull S lambda M,
    exists P : L40.LerayHopfProjectedMode CoNull nu lambda,
      L40.lhpm_u CoNull nu lambda P
        = mdr_u W CoNull S lambda M Rm /\
      L40.lhpm_dt_u CoNull nu lambda P
        = mdr_du W CoNull S lambda M Rm /\
      L40.lhpm_N CoNull nu lambda P
        = mdr_N W CoNull S lambda M Rm.
Proof.
  intros.
  exists (build_projected_mode_from_representation S E Rm).
  repeat split; reflexivity.
Qed.

(* ====================================================================== *)
(* Three represented weak modes -> projected LH triad -> canonical route.  *)
(* ====================================================================== *)

Record TriadDistributionRepresentation
  (W : L42.WeakTestCalculus)
  (CoNull : (R -> Prop) -> Prop)
  (S : ScalarDistributionAECriterion W CoNull)
  (lk lp lq : R)
  (T : L42.HelicalWeakTriad W lk lp lq) : Type := {
  tdr_k :
    ModeDistributionRepresentation
      W CoNull S lk (L42.hwt_k W lk lp lq T);
  tdr_p :
    ModeDistributionRepresentation
      W CoNull S lp (L42.hwt_p W lk lp lq T);
  tdr_q :
    ModeDistributionRepresentation
      W CoNull S lq (L42.hwt_q W lk lp lq T)
}.

Definition build_projected_triad_from_weak_representation
  {W : L42.WeakTestCalculus}
  {CoNull : (R -> Prop) -> Prop}
  (S : ScalarDistributionAECriterion W CoNull)
  {C : CH.C2}
  {nu lk lp lq : R}
  (H : L42.LerayHopfWeakMomentum W nu)
  (T : L42.HelicalWeakTriad W lk lp lq)
  (Rt : TriadDistributionRepresentation W CoNull S lk lp lq T)
  : L40.LerayHopfProjectedTriad CoNull C nu lk lp lq.
Proof.
  pose proof
    (L42.LH42_10_STANDARD_LH_WEAK_MOMENTUM_GIVES_TRIAD_DISTRIBUTIONAL_EQUATIONS
      W nu lk lp lq H T) as HE.
  destruct HE as [HEk [HEp HEq]].
  refine
    {| L40.lhpt_k :=
         build_projected_mode_from_representation
           S HEk (tdr_k W CoNull S lk lp lq T Rt);
       L40.lhpt_p :=
         build_projected_mode_from_representation
           S HEp (tdr_p W CoNull S lk lp lq T Rt);
       L40.lhpt_q :=
         build_projected_mode_from_representation
           S HEq (tdr_q W CoNull S lk lp lq T Rt) |}.
Defined.

Theorem DIAMOND_AE10_REPRESENTED_WEAK_TRIAD_BUILDS_PROJECTED_TRIAD :
  forall W : L42.WeakTestCalculus,
  forall CoNull : (R -> Prop) -> Prop,
  forall S : ScalarDistributionAECriterion W CoNull,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall H : L42.LerayHopfWeakMomentum W nu,
  forall T : L42.HelicalWeakTriad W lk lp lq,
  forall Rt : TriadDistributionRepresentation W CoNull S lk lp lq T,
    exists P : L40.LerayHopfProjectedTriad CoNull C nu lk lp lq,
      True.
Proof.
  intros.
  exists (build_projected_triad_from_weak_representation S H T Rt).
  exact I.
Qed.

Theorem DIAMOND_AE20_REPRESENTED_WEAK_TRIAD_GIVES_PARENT_ROUTE_CONULL :
  forall W : L42.WeakTestCalculus,
  forall CoNull : (R -> Prop) -> Prop,
  forall HC : AE.CoNullCalculus CoNull,
  forall S : ScalarDistributionAECriterion W CoNull,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall H : L42.LerayHopfWeakMomentum W nu,
  forall T : L42.HelicalWeakTriad W lk lp lq,
  forall Rt : TriadDistributionRepresentation W CoNull S lk lp lq T,
    CoNull
      (@L40.projected_leray_parent_route_realized
        CoNull HC C nu lk lp lq
        (build_projected_triad_from_weak_representation (C := C) S H T Rt)).
Proof.
  intros.
  exact
    (L40.LH40_20_PROJECTED_LERAY_TRIAD_GIVES_PARENT_ROUTE_CONULL
      CoNull HC C nu lk lp lq
      (build_projected_triad_from_weak_representation S H T Rt)).
Qed.

(* ====================================================================== *)
(* Claim boundary.                                                         *)
(*                                                                         *)
(* The old NSE-specific frontier                                          *)
(*   distributional modal equation -> a.e. projected LH mode              *)
(* has been reduced to ONE generic scalar-distribution criterion plus      *)
(* representability of the three fixed-mode distributions.                 *)
(* No route, M7, or NSE recurrence hypothesis occurs in this entrance.     *)
(* ====================================================================== *)

Definition STANDARD_SCALAR_DISTRIBUTION_AE_CRITERION_FRONTIER : Prop := True.
Definition LH_FIXED_MODE_DISTRIBUTION_REPRESENTATION_FRONTIER : Prop := True.
Definition GLOBAL_LH_ROUTE_ASSEMBLY_FRONTIER : Prop := True.
Definition CRITICAL_TIME_ROUTE_DEPTH_FRONTIER : Prop := True.

Definition STATUS : string :=
  "NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE_V0_4_1_STANDARD_DISTRIBUTION_BRIDGE_ISOLATED"%string.

End NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.

Check NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.ScalarDistributionAECriterion.
Check NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.ModeDistributionRepresentation.
Check NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.DIAMOND_AE00_REPRESENTED_MODE_MODAL_EQ_CONULL.
Check NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.build_projected_mode_from_representation.
Check NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.DIAMOND_AE01_REPRESENTED_MODE_BUILDS_PROJECTED_MODE.
Check NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.TriadDistributionRepresentation.
Check NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.build_projected_triad_from_weak_representation.
Check NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.DIAMOND_AE20_REPRESENTED_WEAK_TRIAD_GIVES_PARENT_ROUTE_CONULL.

Print Assumptions NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.DIAMOND_AE00_REPRESENTED_MODE_MODAL_EQ_CONULL.
Print Assumptions NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.DIAMOND_AE01_REPRESENTED_MODE_BUILDS_PROJECTED_MODE.
Print Assumptions NSE_R3_F0_GP_DIAMOND_AE_ENTRANCE.DIAMOND_AE20_REPRESENTED_WEAK_TRIAD_GIVES_PARENT_ROUTE_CONULL.
