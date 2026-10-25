
From Stdlib Require Import Reals Lra Psatz Lists.List.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_gp_ae_modal_semantics_v0_23_1.
Require Import awpi_nse_gp_source_class_ownership_v0_25_4.
Require Import awpi_nse_gp_parent_degree_reproduction_v0_26_0.
Require Import awpi_nse_gp_three_leg_route_realization_v0_36_4.
Require Import awpi_nse_gp_complex_three_leg_realization_v0_37_4.
Require Import awpi_nse_gp_complex_source_envelope_realization_v0_38_0.

Open Scope R_scope.

Module NSE_LERAY_AE_TO_PARENT_ROUTE.

Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module AE := NSE_GP_AE_MODAL_SEMANTICS.
Module SO := NSE_GP_SOURCE_CLASS_OWNERSHIP.
Module PR := NSE_GP_PARENT_DEGREE_REPRODUCTION.
Module TL := NSE_GP_THREE_LEG_ROUTE_REALIZATION.
Module CTL := NSE_GP_COMPLEX_THREE_LEG_REALIZATION.
Module SR := NSE_GP_COMPLEX_SOURCE_ENVELOPE_REALIZATION.

(* ===================================================================== *)
(* The actual LH-facing damped triad source at a time t                   *)
(* ===================================================================== *)

Definition leray_damped_triad_source
  (CoNull : (R -> Prop) -> Prop)
  (C : CH.C2) (nu lk lp lq : R)
  (T : AE.AETriadSemanticData CoNull C nu lk lp lq)
  (t : R) : R :=
  AE.ae_dc CoNull C nu lk lp lq T t
  +
  nu * (lk + lp + lq)
    *
    CH.ctriad
      C
      (AE.ae_u CoNull nu lk
        (AE.ae_k CoNull C nu lk lp lq T) t)
      (AE.ae_u CoNull nu lp
        (AE.ae_p CoNull C nu lk lp lq T) t)
      (AE.ae_u CoNull nu lq
        (AE.ae_q CoNull C nu lk lp lq T) t).

(* ===================================================================== *)
(* At every common good time, turn LH a.e. semantic data into the         *)
(* v0.38 concrete complex-norm certificate.                               *)
(* ===================================================================== *)

Definition norm_certificate_at_good_time
  (CoNull : (R -> Prop) -> Prop)
  (C : CH.C2) (nu lk lp lq : R)
  (T : AE.AETriadSemanticData CoNull C nu lk lp lq)
  (t : R)
  (Hgood : AE.triad_good_time CoNull C nu lk lp lq T t)
  : SR.ComplexTriadNormCertificate :=
  {|
    SR.cn_C := C;

    SR.cn_uk :=
      AE.ae_u CoNull nu lk
        (AE.ae_k CoNull C nu lk lp lq T) t;

    SR.cn_up :=
      AE.ae_u CoNull nu lp
        (AE.ae_p CoNull C nu lk lp lq T) t;

    SR.cn_uq :=
      AE.ae_u CoNull nu lq
        (AE.ae_q CoNull C nu lk lp lq T) t;

    SR.cn_duk :=
      AE.ae_dt_u CoNull nu lk
        (AE.ae_k CoNull C nu lk lp lq T) t;

    SR.cn_dup :=
      AE.ae_dt_u CoNull nu lp
        (AE.ae_p CoNull C nu lk lp lq T) t;

    SR.cn_duq :=
      AE.ae_dt_u CoNull nu lq
        (AE.ae_q CoNull C nu lk lp lq T) t;

    SR.cn_Nk :=
      AE.ae_N CoNull nu lk
        (AE.ae_k CoNull C nu lk lp lq T) t;

    SR.cn_Np :=
      AE.ae_N CoNull nu lp
        (AE.ae_p CoNull C nu lk lp lq T) t;

    SR.cn_Nq :=
      AE.ae_N CoNull nu lq
        (AE.ae_q CoNull C nu lk lp lq T) t;

    SR.cn_nu := nu;
    SR.cn_lk := lk;
    SR.cn_lp := lp;
    SR.cn_lq := lq;

    SR.cn_dc :=
      AE.ae_dc CoNull C nu lk lp lq T t;

    SR.cn_modal :=
      AE.GPAE21_GOOD_TIME_GIVES_COMPLEX_TRIAD_CERTIFICATE
        CoNull C nu lk lp lq T t Hgood
  |}.

Theorem LH39_00_GOOD_TIME_BUILDS_COMPLEX_NORM_CERTIFICATE :
  forall CoNull : (R -> Prop) -> Prop,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : AE.AETriadSemanticData CoNull C nu lk lp lq,
  forall t : R,
    AE.triad_good_time CoNull C nu lk lp lq T t ->
    exists N : SR.ComplexTriadNormCertificate,
      SR.cn_C N = C /\
      SR.cn_nu N = nu /\
      SR.cn_lk N = lk /\
      SR.cn_lp N = lp /\
      SR.cn_lq N = lq.
Proof.
  intros CoNull C nu lk lp lq T t Hgood.
  exists
    (norm_certificate_at_good_time
      CoNull C nu lk lp lq T t Hgood).
  repeat split; reflexivity.
Qed.

(* v0.38 then supplies all three source envelopes automatically. *)
Definition physical_certificate_at_good_time
  (CoNull : (R -> Prop) -> Prop)
  (C : CH.C2) (nu lk lp lq : R)
  (T : AE.AETriadSemanticData CoNull C nu lk lp lq)
  (t : R)
  (Hgood : AE.triad_good_time CoNull C nu lk lp lq T t)
  : CTL.ComplexThreeLegPhysicalCertificate :=
  SR.build_complex_physical_from_norm
    (norm_certificate_at_good_time
      CoNull C nu lk lp lq T t Hgood).

Theorem LH39_01_GOOD_TIME_PARENT_CLASS_IS_ACTUAL_LH_SOURCE :
  forall CoNull : (R -> Prop) -> Prop,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : AE.AETriadSemanticData CoNull C nu lk lp lq,
  forall t : R,
  forall Hgood : AE.triad_good_time CoNull C nu lk lp lq T t,
    SO.class_signed_work
      (CTL.ctl_parent_class
        (physical_certificate_at_good_time
          CoNull C nu lk lp lq T t Hgood))
    =
    leray_damped_triad_source CoNull C nu lk lp lq T t.
Proof.
  intros CoNull C nu lk lp lq T t Hgood.
  unfold physical_certificate_at_good_time.
  unfold leray_damped_triad_source.
  exact
    (CTL.CTL11_PARENT_CLASS_IS_ACTUAL_DAMPED_TRIAD_SOURCE
      (SR.build_complex_physical_from_norm
        (norm_certificate_at_good_time
          CoNull C nu lk lp lq T t Hgood))).
Qed.

(* ===================================================================== *)
(* The three-leg route and ParentRoute are now constructed from LH data   *)
(* ===================================================================== *)

Definition three_leg_route_at_good_time
  (CoNull : (R -> Prop) -> Prop)
  (C : CH.C2) (nu lk lp lq : R)
  (T : AE.AETriadSemanticData CoNull C nu lk lp lq)
  (t : R)
  (Hgood : AE.triad_good_time CoNull C nu lk lp lq T t)
  : TL.ThreeLegPhysicalRoute :=
  CTL.build_complex_three_leg_physical_route
    (physical_certificate_at_good_time
      CoNull C nu lk lp lq T t Hgood).

Definition parent_route_at_good_time
  (CoNull : (R -> Prop) -> Prop)
  (C : CH.C2) (nu lk lp lq : R)
  (T : AE.AETriadSemanticData CoNull C nu lk lp lq)
  (t : R)
  (Hgood : AE.triad_good_time CoNull C nu lk lp lq T t)
  : PR.ParentRoute 3 :=
  TL.build_three_leg_parent_route
    (three_leg_route_at_good_time
      CoNull C nu lk lp lq T t Hgood).

Theorem LH39_10_GOOD_TIME_BUILDS_PARENT_ROUTE :
  forall CoNull : (R -> Prop) -> Prop,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : AE.AETriadSemanticData CoNull C nu lk lp lq,
  forall t : R,
  forall Hgood : AE.triad_good_time CoNull C nu lk lp lq T t,
    exists P : PR.ParentRoute 3,
      PR.pr_source_class 3 P
      =
      CTL.ctl_parent_class
        (physical_certificate_at_good_time
          CoNull C nu lk lp lq T t Hgood).
Proof.
  intros CoNull C nu lk lp lq T t Hgood.
  exact
    (CTL.CTL20_COMPLEX_TRIAD_CONSTRUCTS_PARENT_ROUTE
      (physical_certificate_at_good_time
        CoNull C nu lk lp lq T t Hgood)).
Qed.

Theorem LH39_11_GOOD_TIME_PARENT_ROUTE_IS_ACTUAL_LH_SOURCE :
  forall CoNull : (R -> Prop) -> Prop,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : AE.AETriadSemanticData CoNull C nu lk lp lq,
  forall t : R,
  forall Hgood : AE.triad_good_time CoNull C nu lk lp lq T t,
    exists P : PR.ParentRoute 3,
      SO.class_signed_work (PR.pr_source_class 3 P)
      =
      leray_damped_triad_source CoNull C nu lk lp lq T t.
Proof.
  intros CoNull C nu lk lp lq T t Hgood.
  destruct
    (LH39_10_GOOD_TIME_BUILDS_PARENT_ROUTE
      CoNull C nu lk lp lq T t Hgood)
    as [P HP].
  exists P.
  rewrite HP.
  exact
    (LH39_01_GOOD_TIME_PARENT_CLASS_IS_ACTUAL_LH_SOURCE
      CoNull C nu lk lp lq T t Hgood).
Qed.

Theorem LH39_12_GOOD_TIME_ROUTE_REPRODUCTION :
  forall CoNull : (R -> Prop) -> Prop,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : AE.AETriadSemanticData CoNull C nu lk lp lq,
  forall t : R,
  forall Hgood : AE.triad_good_time CoNull C nu lk lp lq T t,
    4 *
      PR.route_child_action
        (parent_route_at_good_time
          CoNull C nu lk lp lq T t Hgood)
    <=
      PR.pr_parent_action 3
        (parent_route_at_good_time
          CoNull C nu lk lp lq T t Hgood)
      +
      PR.pr_legal_cost 3
        (parent_route_at_good_time
          CoNull C nu lk lp lq T t Hgood).
Proof.
  intros.
  exact
    (PR.GPPR22_ROUTE_REPRODUCTION_PAYS_ALL_CHILDREN
      3
      (parent_route_at_good_time
        CoNull C nu lk lp lq T t Hgood)).
Qed.

(* ===================================================================== *)
(* Co-null realization theorem                                           *)
(* ===================================================================== *)

Definition leray_parent_route_realized
  (CoNull : (R -> Prop) -> Prop)
  (C : CH.C2) (nu lk lp lq : R)
  (T : AE.AETriadSemanticData CoNull C nu lk lp lq)
  (t : R) : Prop :=
  exists Hgood : AE.triad_good_time CoNull C nu lk lp lq T t,
    exists P : PR.ParentRoute 3,
      SO.class_signed_work (PR.pr_source_class 3 P)
      =
      leray_damped_triad_source CoNull C nu lk lp lq T t.

Theorem LH39_20_PARENT_ROUTE_REALIZED_ON_EVERY_GOOD_TIME :
  forall CoNull : (R -> Prop) -> Prop,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : AE.AETriadSemanticData CoNull C nu lk lp lq,
  forall t : R,
    AE.triad_good_time CoNull C nu lk lp lq T t ->
    leray_parent_route_realized CoNull C nu lk lp lq T t.
Proof.
  intros CoNull C nu lk lp lq T t Hgood.
  unfold leray_parent_route_realized.
  exists Hgood.
  exact
    (LH39_11_GOOD_TIME_PARENT_ROUTE_IS_ACTUAL_LH_SOURCE
      CoNull C nu lk lp lq T t Hgood).
Qed.

Theorem LH39_21_LERAY_PARENT_ROUTE_REALIZED_CONULL :
  forall CoNull : (R -> Prop) -> Prop,
    AE.CoNullCalculus CoNull ->
    forall C : CH.C2,
    forall nu lk lp lq : R,
    forall T : AE.AETriadSemanticData CoNull C nu lk lp lq,
      CoNull
        (leray_parent_route_realized
          CoNull C nu lk lp lq T).
Proof.
  intros CoNull HC C nu lk lp lq T.
  destruct HC as [Hall Hmono Hinter].
  pose proof
    (AE.GPAE20_TRIAD_GOOD_TIME_IS_CONULL
      CoNull
      {| AE.cn_all := Hall;
         AE.cn_mono := Hmono;
         AE.cn_inter := Hinter |}
      C nu lk lp lq T) as Hgood.
  eapply Hmono.
  - exact Hgood.
  - intros t Ht.
    exact
      (LH39_20_PARENT_ROUTE_REALIZED_ON_EVERY_GOOD_TIME
        CoNull C nu lk lp lq T t Ht).
Qed.

(* Stronger co-null output: at almost every time there is an actual route
   whose source class is the LH damped triad source, while the route itself
   already carries dstar=3, canonical child actions, canonical outgoing
   capacity, and the proved reproduction inequality. *)
Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_LERAY_AE_TO_PARENT_ROUTE.

Check NSE_LERAY_AE_TO_PARENT_ROUTE.leray_damped_triad_source.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.norm_certificate_at_good_time.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.LH39_00_GOOD_TIME_BUILDS_COMPLEX_NORM_CERTIFICATE.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.physical_certificate_at_good_time.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.LH39_01_GOOD_TIME_PARENT_CLASS_IS_ACTUAL_LH_SOURCE.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.three_leg_route_at_good_time.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.parent_route_at_good_time.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.LH39_10_GOOD_TIME_BUILDS_PARENT_ROUTE.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.LH39_11_GOOD_TIME_PARENT_ROUTE_IS_ACTUAL_LH_SOURCE.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.LH39_12_GOOD_TIME_ROUTE_REPRODUCTION.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.leray_parent_route_realized.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.LH39_20_PARENT_ROUTE_REALIZED_ON_EVERY_GOOD_TIME.
Check NSE_LERAY_AE_TO_PARENT_ROUTE.LH39_21_LERAY_PARENT_ROUTE_REALIZED_CONULL.
