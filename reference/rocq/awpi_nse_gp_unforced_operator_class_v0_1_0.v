From Stdlib Require Import Reals Ranalysis1 Lra Psatz Field Lia String.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.
Require Import awpi_nse_gp_pair_source_calculus_v0_51_0.
Require Import awpi_nse_gp_fixed_allocation_v0_51_0.
Require Import awpi_nse_gp_source_storage_dynamics_v0_51_0.
Require Import awpi_nse_gp_signed_source_closure_v0_51_0.
Require Import awpi_nse_gp_source_m7_energy_join_v0_51_0.
Require Import awpi_nse_gp_to_m7_spine_v0_21_7.
Require Import awpi_nse_m7_critical_energy_injection_v0_35_8.

Module NSE_GP_UNFORCED_OPERATOR_CLASS.
Import NSE_KQ_FINITE_ALGEBRA NSE_CONTINUOUS_TIME_CALCULUS.
Import NSE_GALERKIN_MODAL_CALCULUS NSE_GP_PAIR_SOURCE_CALCULUS.
Import NSE_GP_FIXED_ALLOCATION NSE_GP_SOURCE_STORAGE_DYNAMICS.
Import NSE_GP_SIGNED_SOURCE_CLOSURE.
Module Join := NSE_GP_SOURCE_M7_ENERGY_JOIN.
Module Spine := NSE_GP_TO_M7_SPINE.
Module Energy := NSE_M7_CRITICAL_ENERGY_INJECTION.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* 1. Forced extension of the already-unforced finite modal dynamics.  *)
(* ------------------------------------------------------------------ *)

Definition ModalForcing51 := R -> Vec.

Definition forced_modal_rhs51 n (lambda : Vec) T nu
  (f : ModalForcing51) (t : R) (u : Vec) : Vec :=
  fun i => modal_rhs n lambda T nu u i + f t i.

Definition ForcedModalPath51 n (lambda : Vec) T nu a b
  (f : ModalForcing51) (u : R -> Vec) : Prop :=
  forall t, InTime a b t -> forall i, (i<n)%nat ->
    derivable_pt_lim (fun s => u s i) t
      (forced_modal_rhs51 n lambda T nu f t (u t) i).

Definition ZeroForcingOn51 n a b (f : ModalForcing51) : Prop :=
  forall t, InTime a b t -> forall i, (i<n)%nat -> f t i = 0.

Definition zero_forcing51 : ModalForcing51 := fun _ _ => 0.

Theorem UFC00_ZERO_FORCING_COLLAPSES_FORCED_PATH :
  forall n lambda T nu a b f u,
  ZeroForcingOn51 n a b f ->
  (ForcedModalPath51 n lambda T nu a b f u <->
   ModalPath n lambda T nu a b u).
Proof.
  intros n lambda T nu a b f u Hf; split; intros Hp t Ht i Hi.
  - specialize (Hp t Ht i Hi).
    unfold forced_modal_rhs51 in Hp.
    rewrite (Hf t Ht i Hi) in Hp.
    replace (modal_rhs n lambda T nu (u t) i + 0)
      with (modal_rhs n lambda T nu (u t) i) in Hp by ring.
    exact Hp.
  - specialize (Hp t Ht i Hi).
    unfold forced_modal_rhs51.
    rewrite (Hf t Ht i Hi).
    replace (modal_rhs n lambda T nu (u t) i + 0)
      with (modal_rhs n lambda T nu (u t) i) by ring.
    exact Hp.
Qed.

Lemma UFC01_LITERAL_ZERO_FORCING : forall n a b,
  ZeroForcingOn51 n a b zero_forcing51.
Proof. intros n a b t Ht i Hi; reflexivity. Qed.

Theorem UFC02_LITERAL_ZERO_PATH_IFF_MODAL_PATH :
  forall n lambda T nu a b u,
  ForcedModalPath51 n lambda T nu a b zero_forcing51 u <->
  ModalPath n lambda T nu a b u.
Proof.
  intros; apply UFC00_ZERO_FORCING_COLLAPSES_FORCED_PATH.
  apply UFC01_LITERAL_ZERO_FORCING.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The exact external terms produced by a forcing.                  *)
(* ------------------------------------------------------------------ *)

Definition cut_forcing_current51 n (s u f : Vec) :=
  sum n (fun i => s i*u i*f i).

Definition critical_forcing_rate51 P (u f : Vec) :=
  2*cut_forcing_current51 (ps_space P) (ps_radius P) u f.

Theorem UFC10_FORCED_MODAL_CUT_DERIVATIVE :
  forall n lambda T nu a b f u s t,
  ForcedModalPath51 n lambda T nu a b f u -> InTime a b t ->
  derivable_pt_lim (fun r => cut_mass n s (u r)) t
    (2*cut_current n T s (u t)-
     2*nu*cut_dissipation n lambda s (u t)+
     2*cut_forcing_current51 n s (u t) (f t)).
Proof.
  intros n lambda T nu a b f u s t Hpath Ht.
  pose proof (NSCT40_FINITE_WEIGHTED_ENERGY_DERIVATIVE n s u
    (forced_modal_rhs51 n lambda T nu f t (u t)) t
    (Hpath t Ht)) as HD.
  assert (He : sum n (fun i => s i*u t i*
      forced_modal_rhs51 n lambda T nu f t (u t) i) =
      -nu*cut_dissipation n lambda s (u t)+
      cut_current n T s (u t)+
      cut_forcing_current51 n s (u t) (f t)).
  {
    unfold forced_modal_rhs51, modal_rhs, cut_dissipation,
      cut_current, cut_forcing_current51, dot, mul.
    transitivity (sum n (fun i =>
      ((-nu)*(s i*lambda i*u t i*u t i)-
       modal_source n T (u t) i*(s i*u t i))+
       s i*u t i*f t i)).
    - apply sum_ext; intros; ring.
    - rewrite sum_add, sum_sub, sum_scale; ring.
  }
  rewrite He in HD.
  replace (2*(-nu*cut_dissipation n lambda s (u t)+
      cut_current n T s (u t)+
      cut_forcing_current51 n s (u t) (f t))) with
    (2*cut_current n T s (u t)-
     2*nu*cut_dissipation n lambda s (u t)+
     2*cut_forcing_current51 n s (u t) (f t)) in HD by ring.
  exact HD.
Qed.

Definition pair_forcing51 (f u : Vec) i j :=
  f i*u j+u i*f j.

Definition forced_pair_rhs51 n lambda T nu (f u : Vec) i j :=
  pair_rhs n lambda T nu u i j + pair_forcing51 f u i j.

Theorem UFC11_FORCED_MODAL_PRODUCT_EQUATION :
  forall n lambda T nu a b f u i j t,
  ForcedModalPath51 n lambda T nu a b f u ->
  (i<n)%nat -> (j<n)%nat -> InTime a b t ->
  derivable_pt_lim (fun s => pair_value (u s) i j) t
    (forced_pair_rhs51 n lambda T nu (f t) (u t) i j).
Proof.
  intros n lambda T nu a b f u i j t Hp Hi Hj Ht.
  pose proof (derivable_pt_lim_mult
    (fun s => u s i) (fun s => u s j) t
    (forced_modal_rhs51 n lambda T nu f t (u t) i)
    (forced_modal_rhs51 n lambda T nu f t (u t) j)
    (Hp t Ht i Hi) (Hp t Ht j Hj)) as HD.
  change (derivable_pt_lim (fun s => pair_value (u s) i j) t
    (forced_modal_rhs51 n lambda T nu f t (u t) i*u t j+
     u t i*forced_modal_rhs51 n lambda T nu f t (u t) j)) in HD.
  replace (forced_pair_rhs51 n lambda T nu (f t) (u t) i j) with
    (forced_modal_rhs51 n lambda T nu f t (u t) i*u t j+
     u t i*forced_modal_rhs51 n lambda T nu f t (u t) j).
  - exact HD.
  - unfold forced_pair_rhs51, pair_forcing51, forced_modal_rhs51,
      pair_rhs, pair_value, pair_regeneration, modal_rhs; ring.
Qed.

Definition source_forcing_rate51 P nu Z (f u : Vec) :=
  2*sum (ps_count P) (fun p =>
    packet_hcoef P nu Z p*packet_q P u p*
    pair_forcing51 f u (ps_left P p) (ps_right P p)).

Theorem UFC12_FORCED_PACKET_STORAGE_DERIVATIVE :
  forall P nu Z T a b f u,
  PacketIndices51 P ->
  ForcedModalPath51 (ps_space P) (packet_lambda P) T nu a b f u ->
  DerivativeOn a b (fun t => packet_H P nu Z (u t))
    (fun t => source_rate P nu Z T (u t)+
      source_forcing_rate51 P nu Z (f t) (u t)).
Proof.
  intros P nu Z T a b f u HI Hp t Ht.
  assert (HD : derivable_pt_lim
    (fun s => sum (ps_count P) (fun p => packet_hcoef P nu Z p*
      packet_q P (u s) p*packet_q P (u s) p)) t
    (2*sum (ps_count P) (fun p => packet_hcoef P nu Z p*
      packet_q P (u t) p*
      forced_pair_rhs51 (ps_space P) (packet_lambda P) T nu
        (f t) (u t) (ps_left P p) (ps_right P p)))).
  {
    apply NSCT40_FINITE_WEIGHTED_ENERGY_DERIVATIVE; intros p Hpi.
    apply (UFC11_FORCED_MODAL_PRODUCT_EQUATION
      (ps_space P) (packet_lambda P) T nu a b f u
      (ps_left P p) (ps_right P p) t Hp).
    - exact (proj1 (proj2 (HI p Hpi))).
    - exact (proj2 (proj2 (HI p Hpi))).
    - exact Ht.
  }
  assert (Hunforced :
    2*sum (ps_count P) (fun p => packet_hcoef P nu Z p*
      packet_q P (u t) p*
      pair_rhs (ps_space P) (packet_lambda P) T nu
        (u t) (ps_left P p) (ps_right P p)) =
    source_rate P nu Z T (u t)).
  {
    unfold source_rate, source_production, source_dissipation.
    rewrite <- sum_scale, <- sum_sub; apply sum_ext; intros.
    unfold pair_rhs, pair_value, pair_regeneration,
      packet_q, packet_regeneration; ring.
  }
  assert (Hsplit :
    2*sum (ps_count P) (fun p => packet_hcoef P nu Z p*
      packet_q P (u t) p*
      forced_pair_rhs51 (ps_space P) (packet_lambda P) T nu
        (f t) (u t) (ps_left P p) (ps_right P p)) =
    2*sum (ps_count P) (fun p => packet_hcoef P nu Z p*
      packet_q P (u t) p*
      pair_rhs (ps_space P) (packet_lambda P) T nu
        (u t) (ps_left P p) (ps_right P p))+
    source_forcing_rate51 P nu Z (f t) (u t)).
  {
    unfold source_forcing_rate51, forced_pair_rhs51.
    replace
      (sum (ps_count P) (fun p => packet_hcoef P nu Z p*
        packet_q P (u t) p*
        (pair_rhs (ps_space P) (packet_lambda P) T nu (u t)
          (ps_left P p) (ps_right P p)+
         pair_forcing51 (f t) (u t) (ps_left P p) (ps_right P p))))
      with
      (sum (ps_count P) (fun p => packet_hcoef P nu Z p*
        packet_q P (u t) p*
        pair_rhs (ps_space P) (packet_lambda P) T nu (u t)
          (ps_left P p) (ps_right P p))+
       sum (ps_count P) (fun p => packet_hcoef P nu Z p*
        packet_q P (u t) p*
        pair_forcing51 (f t) (u t) (ps_left P p) (ps_right P p))).
    - ring.
    - rewrite <- sum_add; apply sum_ext; intros; ring.
  }
  rewrite Hsplit, Hunforced in HD; exact HD.
Qed.

Definition combined_forcing_rate51 P nu Z (f u : Vec) :=
  critical_forcing_rate51 P u f + source_forcing_rate51 P nu Z f u/nu.

Theorem UFC13_FORCED_CRITICAL_DERIVATIVE : forall P nu T a b f u,
  ForcedModalPath51 (ps_space P) (packet_lambda P) T nu a b f u ->
  DerivativeOn a b (fun t => critical_mass P (u t))
    (fun t => critical_rate P nu T (u t)+
      critical_forcing_rate51 P (u t) (f t)).
Proof.
  intros P nu T a b f u Hp t Ht.
  exact (UFC10_FORCED_MODAL_CUT_DERIVATIVE
    (ps_space P) (packet_lambda P) T nu a b f u
    (ps_radius P) t Hp Ht).
Qed.

Theorem UFC14_FORCED_COMBINED_STORAGE_DERIVATIVE :
  forall P nu Z T a b f u,
  PacketIndices51 P ->
  ForcedModalPath51 (ps_space P) (packet_lambda P) T nu a b f u ->
  DerivativeOn a b (fun t => combined_storage P nu Z (u t))
    (fun t => combined_rate P nu Z T (u t)+
      combined_forcing_rate51 P nu Z (f t) (u t)).
Proof.
  intros P nu Z T a b f u HI Hp t Ht.
  pose proof (UFC13_FORCED_CRITICAL_DERIVATIVE P nu T a b f u Hp t Ht) as Hm.
  pose proof (UFC12_FORCED_PACKET_STORAGE_DERIVATIVE P nu Z T a b f u HI Hp t Ht) as HH.
  pose proof (derivable_pt_lim_scal (fun s => packet_H P nu Z (u s)) (/nu) t
    (source_rate P nu Z T (u t)+source_forcing_rate51 P nu Z (f t) (u t)) HH)
    as Hscaled.
  pose proof (derivable_pt_lim_plus
    (fun s => critical_mass P (u s))
    (fun s => (/nu)*packet_H P nu Z (u s)) t
    (critical_rate P nu T (u t)+critical_forcing_rate51 P (u t) (f t))
    ((/nu)*(source_rate P nu Z T (u t)+
      source_forcing_rate51 P nu Z (f t) (u t))) Hm Hscaled) as H.
  apply (derivable_pt_lim_ext
    (fun s => critical_mass P (u s)+(/nu)*packet_H P nu Z (u s))
    (fun s => combined_storage P nu Z (u s)) t
    (combined_rate P nu Z T (u t)+
      combined_forcing_rate51 P nu Z (f t) (u t))).
  - intro s; unfold combined_storage, Rdiv; ring.
  - replace (combined_rate P nu Z T (u t)+
      combined_forcing_rate51 P nu Z (f t) (u t)) with
    ((critical_rate P nu T (u t)+critical_forcing_rate51 P (u t) (f t))+
     (/nu)*(source_rate P nu Z T (u t)+
      source_forcing_rate51 P nu Z (f t) (u t))) by
      (unfold combined_rate, combined_forcing_rate51, Rdiv; ring).
    exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. f=0 kills every external GP/BKQR production term exactly.       *)
(* ------------------------------------------------------------------ *)

Lemma UFC20_ZERO_CUT_FORCING_CURRENT : forall n s u,
  cut_forcing_current51 n s u (zero_forcing51 0) = 0.
Proof.
  intros n s u; unfold cut_forcing_current51, zero_forcing51.
  transitivity (sum n (fun _ => 0)).
  - apply sum_ext; intros; ring.
  - apply finite_sum_zero.
Qed.

Lemma UFC21_ZERO_CRITICAL_FORCING_RATE : forall P u,
  critical_forcing_rate51 P u (zero_forcing51 0)=0.
Proof.
  intros; unfold critical_forcing_rate51.
  rewrite UFC20_ZERO_CUT_FORCING_CURRENT; ring.
Qed.

Lemma UFC22_ZERO_PAIR_FORCING : forall u i j,
  pair_forcing51 (zero_forcing51 0) u i j=0.
Proof. intros; unfold pair_forcing51, zero_forcing51; ring. Qed.

Lemma UFC23_ZERO_SOURCE_FORCING_RATE : forall P nu Z u,
  source_forcing_rate51 P nu Z (zero_forcing51 0) u=0.
Proof.
  intros; unfold source_forcing_rate51.
  transitivity (2*sum (ps_count P) (fun _ => 0)).
  - f_equal; apply sum_ext; intros p Hp; rewrite UFC22_ZERO_PAIR_FORCING; ring.
  - rewrite finite_sum_zero; ring.
Qed.

Theorem UFC24_ZERO_COMBINED_FORCING_RATE : forall P nu Z u,
  combined_forcing_rate51 P nu Z (zero_forcing51 0) u=0.
Proof.
  intros; unfold combined_forcing_rate51.
  rewrite UFC21_ZERO_CRITICAL_FORCING_RATE, UFC23_ZERO_SOURCE_FORCING_RATE.
  unfold Rdiv; ring.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The existing GPSourceWitness51 is already an f=0 source witness. *)
(* ------------------------------------------------------------------ *)

Definition UnforcedGPClosed51 (D : GPSourceData51) : Prop :=
  GPSourceWitness51 D /\
  ForcedModalPath51 (ps_space (g51_packets D))
    (packet_lambda (g51_packets D)) (g51_table D) (g51_nu D)
    (g51_t0 D) (g51_t1 D) zero_forcing51 (g51_u D).

Theorem UFC30_EXISTING_GP_WITNESS_IS_UNFORCED_CLOSED : forall D,
  GPSourceWitness51 D -> UnforcedGPClosed51 D.
Proof.
  intros D HW; split; [exact HW|].
  apply (proj2 (UFC02_LITERAL_ZERO_PATH_IFF_MODAL_PATH
    (ps_space (g51_packets D)) (packet_lambda (g51_packets D))
    (g51_table D) (g51_nu D) (g51_t0 D) (g51_t1 D) (g51_u D))).
  exact (gw51_path D HW).
Qed.

Theorem UFC31_UNFORCED_CLOSED_RECOVERS_EXISTING_MODAL_PATH : forall D,
  UnforcedGPClosed51 D ->
  ModalPath (ps_space (g51_packets D)) (packet_lambda (g51_packets D))
    (g51_table D) (g51_nu D) (g51_t0 D) (g51_t1 D) (g51_u D).
Proof. intros D H; exact (gw51_path D (proj1 H)). Qed.

(* ------------------------------------------------------------------ *)
(* 5. Closed f=0 regularity certificate: no external forcing premise.  *)
(*    The remaining research input is the INTERNAL signed GP payment.  *)
(* ------------------------------------------------------------------ *)

Definition UnforcedM7RegularityCertificate51 D theta Qstar : Prop :=
  UnforcedGPClosed51 D /\
  0<=theta /\ theta<1 /\ 0<=Qstar /\
  SignedProductionBudget51 D theta Qstar.

Theorem UFC40_UNFORCED_CERTIFICATE_GIVES_CONTINUOUS_CRITICAL_BOUND :
  forall D theta Qstar,
  UnforcedM7RegularityCertificate51 D theta Qstar ->
  Energy.UniformCriticalEnergy (Join.TimePoint51 D)
    (fun t => g_mass D (proj1_sig t))
    (fun t => g51_Dcum D (proj1_sig t)).
Proof.
  intros D theta Qstar [HC [Hth0 [Hth1 [HQ HB]]]].
  exact (Join.NSSJ50_ALL_CONTINUOUS_ENDPOINTS_CRITICAL_BOUND
    D theta Qstar (proj1 HC) Hth0 Hth1 HQ HB).
Qed.

Theorem UFC41_UNFORCED_CERTIFICATE_GIVES_GRID_M7_AND_CRITICAL_TARGET :
  forall D theta Qstar grid,
  UnforcedM7RegularityCertificate51 D theta Qstar ->
  Join.SourceGrid51 D grid ->
  Spine.GPSequenceM7 (Join.source_cell51 D grid) /\
  Energy.CriticalH12Bound nat (fun n => g_mass D (grid n)) /\
  Energy.CriticalH32Dissipation nat (fun n => g51_Dcum D (grid n)).
Proof.
  intros D theta Qstar grid [HC [Hth0 [Hth1 [HQ HB]]]] HG.
  exact (Join.NSSJ40_DIRECT_GP_SOURCE_TO_EXISTING_M7_CRITICAL_TARGET
    D theta Qstar grid (proj1 HC) Hth0 Hth1 HQ HB HG).
Qed.

(* The exact research frontier after setting f=0: f contributes no term;
   the only nontrivial closure premise left in this module is the internal
   SignedProductionBudget51. *)
Definition UnforcedInternalPaymentFrontier51 D theta Qstar : Prop :=
  SignedProductionBudget51 D theta Qstar.

Definition STATUS : string :=
  "NSE_GP_UNFORCED_OPERATOR_CLASS_V0_1_0_ZERO_FORCE_EXACT_FORCED_EXTENSION_AND_CONDITIONAL_INTERNAL_M7_NO_ADMITTED"%string.

End NSE_GP_UNFORCED_OPERATOR_CLASS.

Check NSE_GP_UNFORCED_OPERATOR_CLASS.UFC00_ZERO_FORCING_COLLAPSES_FORCED_PATH.
Check NSE_GP_UNFORCED_OPERATOR_CLASS.UFC10_FORCED_MODAL_CUT_DERIVATIVE.
Check NSE_GP_UNFORCED_OPERATOR_CLASS.UFC12_FORCED_PACKET_STORAGE_DERIVATIVE.
Check NSE_GP_UNFORCED_OPERATOR_CLASS.UFC14_FORCED_COMBINED_STORAGE_DERIVATIVE.
Check NSE_GP_UNFORCED_OPERATOR_CLASS.UFC24_ZERO_COMBINED_FORCING_RATE.
Check NSE_GP_UNFORCED_OPERATOR_CLASS.UFC30_EXISTING_GP_WITNESS_IS_UNFORCED_CLOSED.
Check NSE_GP_UNFORCED_OPERATOR_CLASS.UFC40_UNFORCED_CERTIFICATE_GIVES_CONTINUOUS_CRITICAL_BOUND.
Check NSE_GP_UNFORCED_OPERATOR_CLASS.UFC41_UNFORCED_CERTIFICATE_GIVES_GRID_M7_AND_CRITICAL_TARGET.

Print Assumptions NSE_GP_UNFORCED_OPERATOR_CLASS.UFC14_FORCED_COMBINED_STORAGE_DERIVATIVE.
Print Assumptions NSE_GP_UNFORCED_OPERATOR_CLASS.UFC24_ZERO_COMBINED_FORCING_RATE.
Print Assumptions NSE_GP_UNFORCED_OPERATOR_CLASS.UFC30_EXISTING_GP_WITNESS_IS_UNFORCED_CLOSED.
Print Assumptions NSE_GP_UNFORCED_OPERATOR_CLASS.UFC40_UNFORCED_CERTIFICATE_GIVES_CONTINUOUS_CRITICAL_BOUND.
Print Assumptions NSE_GP_UNFORCED_OPERATOR_CLASS.UFC41_UNFORCED_CERTIFICATE_GIVES_GRID_M7_AND_CRITICAL_TARGET.
