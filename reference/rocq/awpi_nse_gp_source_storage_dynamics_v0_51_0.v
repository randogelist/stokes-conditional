From Stdlib Require Import Reals Ranalysis1 Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.
Require Import awpi_nse_gp_pair_source_calculus_v0_51_0.
Require Import awpi_nse_gp_fixed_allocation_v0_51_0.

Module NSE_GP_SOURCE_STORAGE_DYNAMICS.
Import NSE_KQ_FINITE_ALGEBRA NSE_CONTINUOUS_TIME_CALCULUS.
Import NSE_GALERKIN_MODAL_CALCULUS NSE_GP_PAIR_SOURCE_CALCULUS NSE_GP_FIXED_ALLOCATION.
Open Scope R_scope.

Definition packet_regeneration P T (u : Vec) p :=
  modal_source (ps_space P) T u (ps_left P p)*u (ps_right P p)+
  u (ps_left P p)*modal_source (ps_space P) T u (ps_right P p).
Definition source_dissipation P nu Z (u : Vec) :=
  sum (ps_count P) (fun p => 2*nu*
    (packet_lambda P (ps_left P p)+packet_lambda P (ps_right P p))*
    packet_hcoef P nu Z p*packet_q P u p*packet_q P u p).
Definition source_production P nu Z T (u : Vec) :=
  sum (ps_count P) (fun p => -2*packet_hcoef P nu Z p*
    packet_q P u p*packet_regeneration P T u p).
Definition combined_storage P nu Z (u : Vec) :=
  critical_mass P u+packet_H P nu Z u/nu.
Definition critical_rate P nu T (u : Vec) :=
  2*cut_current (ps_space P) T (ps_radius P) u-2*nu*critical_dissipation P u.
Definition source_rate P nu Z T (u : Vec) :=
  source_production P nu Z T u-source_dissipation P nu Z u.
Definition combined_rate P nu Z T (u : Vec) :=
  critical_rate P nu T u+source_rate P nu Z T u/nu.

Lemma packet_rcoef_nonnegative51 : forall P Z p,
  0<Z -> PacketIndices51 P -> PacketPositive51 P -> (p<ps_count P)%nat ->
  0<=packet_rcoef P Z p.
Proof.
  intros P Z p HZ HI HP Hp; unfold packet_rcoef, Rdiv.
  apply Rmult_le_pos; [exact (Rle_0_sqr (ps_coeff P p))|].
  apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat.
  - exact (NSFA10_FIXED_ALLOCATION_POSITIVE P Z p HZ HI HP Hp).
  - exact (proj1 HP _ (proj1 (HI p Hp))).
Qed.
Lemma packet_hcoef_nonnegative51 : forall P nu Z p,
  0<nu -> 0<Z -> PacketIndices51 P -> PacketPositive51 P -> (p<ps_count P)%nat ->
  0<=packet_hcoef P nu Z p.
Proof.
  intros P nu Z p Hnu HZ HI HP Hp; unfold packet_hcoef, Rdiv.
  apply Rmult_le_pos.
  - exact (packet_rcoef_nonnegative51 P Z p HZ HI HP Hp).
  - apply Rlt_le; apply Rinv_0_lt_compat.
    pose proof (proj2 (proj2 HP p Hp)); nra.
Qed.
Lemma packet_R_nonnegative51 : forall P Z u p,
  0<Z -> PacketIndices51 P -> PacketPositive51 P -> (p<ps_count P)%nat ->
  0<=packet_R P Z u p.
Proof.
  intros P Z u p HZ HI HP Hp; unfold packet_R.
  replace (packet_rcoef P Z p*packet_q P u p*packet_q P u p) with
    (packet_rcoef P Z p*(packet_q P u p*packet_q P u p)) by ring.
  apply Rmult_le_pos; [exact (packet_rcoef_nonnegative51 P Z p HZ HI HP Hp)|
    exact (Rle_0_sqr (packet_q P u p))].
Qed.
Lemma packet_D_nonnegative51 : forall P Z u p,
  0<Z -> PacketIndices51 P -> PacketPositive51 P -> (p<ps_count P)%nat ->
  0<=packet_D P Z u p.
Proof.
  intros P Z u p HZ HI HP Hp.
  pose proof (NSFA10_FIXED_ALLOCATION_POSITIVE P Z p HZ HI HP Hp) as Hw.
  pose proof (proj1 HP _ (proj1 (HI p Hp))) as Hr.
  unfold packet_D.
  replace (packet_weight P Z p*ps_radius P (ps_out P p)*ps_radius P (ps_out P p)*
    ps_radius P (ps_out P p)*u (ps_out P p)*u (ps_out P p)) with
    ((packet_weight P Z p*ps_radius P (ps_out P p)*ps_radius P (ps_out P p)*
    ps_radius P (ps_out P p))*(u (ps_out P p)*u (ps_out P p))) by ring.
  (* Keep packet_weight as one factor: its positivity is already Hw. *)
  pose proof (Rlt_le _ _ Hw) as Hw0.
  pose proof (Rlt_le _ _ Hr) as Hr0.
  pose proof (Rmult_le_pos _ _ Hw0 Hr0) as Hwr.
  pose proof (Rmult_le_pos _ _ Hwr Hr0) as Hwr2.
  pose proof (Rmult_le_pos _ _ Hwr2 Hr0) as Hwr3.
  exact (Rmult_le_pos _ _ Hwr3 (Rle_0_sqr (u (ps_out P p)))).
Qed.

Theorem NSSD10_STORAGE_AND_RATES_NONNEGATIVE : forall P nu Z u,
  0<nu -> 0<Z -> PacketIndices51 P -> PacketPositive51 P ->
  0<=packet_H P nu Z u /\ 0<=source_mass P Z u /\
  0<=critical_mass P u /\ 0<=critical_dissipation P u.
Proof.
  intros P nu Z u Hnu HZ HI HP; split.
  - unfold packet_H; apply sum_nonneg; intros p Hp.
    replace (packet_hcoef P nu Z p*packet_q P u p*packet_q P u p) with
      (packet_hcoef P nu Z p*(packet_q P u p*packet_q P u p)) by ring.
    apply Rmult_le_pos; [exact (packet_hcoef_nonnegative51 P nu Z p Hnu HZ HI HP Hp)|
      exact (Rle_0_sqr (packet_q P u p))].
  - split.
    + unfold source_mass; apply sum_nonneg; intros p Hp.
      exact (packet_R_nonnegative51 P Z u p HZ HI HP Hp).
    + split.
      * unfold critical_mass, cut_mass; apply sum_nonneg; intros i Hi.
        replace (ps_radius P i*u i*u i) with (ps_radius P i*(u i*u i)) by ring.
        apply Rmult_le_pos; [apply Rlt_le; exact (proj1 HP i Hi)|exact (Rle_0_sqr (u i))].
      * unfold critical_dissipation; apply cut_dissipation_nonnegative.
        -- intros i Hi; unfold packet_lambda; exact (Rle_0_sqr (ps_radius P i)).
        -- intros i Hi; apply Rlt_le; exact (proj1 HP i Hi).
Qed.

Theorem NSSD11_PACKET_SOURCE_ACTION_IDENTITY : forall P Z u p,
  0<Z -> PacketIndices51 P -> PacketPositive51 P -> (p<ps_count P)%nat ->
  packet_phi P u p*packet_phi P u p=packet_R P Z u p*packet_D P Z u p.
Proof.
  intros P Z u p HZ HI HP Hp.
  pose proof (NSFA10_FIXED_ALLOCATION_POSITIVE P Z p HZ HI HP Hp) as Hw.
  pose proof (proj1 HP _ (proj1 (HI p Hp))) as Hr.
  unfold packet_phi, packet_R, packet_D, packet_rcoef; field; nra.
Qed.

Theorem NSSD12_SOURCE_RECONSTRUCTION_GIVES_ACTUAL_CURRENT : forall P T u,
  PacketIndices51 P -> PacketSourceReconstruction51 P T ->
  packet_current P u=cut_current (ps_space P) T (ps_radius P) u.
Proof.
  intros P T u HI HR.
  assert (He : packet_current P u=
    sum (ps_space P) (fun i => (-ps_radius P i*u i)*
      fiber (ps_count P) (ps_out P) i (fun p => ps_coeff P p*packet_q P u p))).
  { rewrite (weighted_fibers51 (ps_space P) (ps_count P) (ps_out P)
      (fun p => ps_coeff P p*packet_q P u p) (fun i => -ps_radius P i*u i)).
    - unfold packet_current, packet_phi; apply sum_ext; intros; ring.
    - intros p Hp; exact (proj1 (HI p Hp)). }
  rewrite He; unfold cut_current, dot, mul.
  replace (-sum (ps_space P) (fun i => modal_source (ps_space P) T u i*(ps_radius P i*u i)))
    with ((-1)*sum (ps_space P) (fun i => modal_source (ps_space P) T u i*(ps_radius P i*u i)))
    by ring.
  rewrite <- sum_scale; apply sum_ext; intros i Hi; rewrite (HR u i Hi); ring.
Qed.

Theorem NSSD20_NO_OVERLAP_ACTUAL_SOURCE_RECEIPT : forall P Z T u,
  0<Z -> PacketIndices51 P -> PacketPositive51 P ->
  PacketGeometricCensus51 P Z -> PacketSourceReconstruction51 P T ->
  cut_current (ps_space P) T (ps_radius P) u*
    cut_current (ps_space P) T (ps_radius P) u <=
  source_mass P Z u*critical_dissipation P u.
Proof.
  intros P Z T u HZ HI HP HC HR.
  assert (Hlocal : forall p, (p<ps_count P)%nat ->
    packet_phi P u p*packet_phi P u p<=packet_R P Z u p*packet_D P Z u p).
  { intros p Hp; rewrite (NSSD11_PACKET_SOURCE_ACTION_IDENTITY P Z u p HZ HI HP Hp);
    apply Rle_refl. }
  pose proof (NSKA20_WEIGHTED_CAUCHY (ps_count P) (fun _ => 1)
    (packet_R P Z u) (packet_D P Z u) (packet_phi P u)
    (fun p Hp => Rlt_le _ _ Rlt_0_1)
    (fun p Hp => packet_R_nonnegative51 P Z u p HZ HI HP Hp)
    (fun p Hp => packet_D_nonnegative51 P Z u p HZ HI HP Hp) Hlocal) as H.
  (* Expose the unit-weight specialization before rewriting.  Do not
     ask generic sum_scale matching to discover the instantiated function. *)
  change
    (sum (ps_count P) (fun p => 1*packet_phi P u p) *
     sum (ps_count P) (fun p => 1*packet_phi P u p) <=
     sum (ps_count P) (fun p => 1*packet_R P Z u p) *
     sum (ps_count P) (fun p => 1*packet_D P Z u p)) in H.
  assert (Hunit : forall f : nat -> R,
    sum (ps_count P) (fun p => 1*f p)=sum (ps_count P) f).
  { intro f; apply sum_ext; intros p Hp; apply Rmult_1_l. }
  rewrite !(Hunit (packet_phi P u)),
    (Hunit (packet_R P Z u)), (Hunit (packet_D P Z u)) in H.
  change (packet_current P u*packet_current P u<=
    source_mass P Z u*allocated_capacity P Z u) in H.
  rewrite (NSSD12_SOURCE_RECONSTRUCTION_GIVES_ACTUAL_CURRENT P T u HI HR) in H.
  pose proof (NSFA21_NO_REUSED_DETECTOR_CAPACITY P Z u HI HP
    (NSFA20_GEOMETRIC_CENSUS_ALLOCATES_CAPACITY P Z HZ HI HP HC)) as Hd.
  assert (HR0 : 0<=source_mass P Z u).
  { unfold source_mass; apply sum_nonneg; intros p Hp;
    exact (packet_R_nonnegative51 P Z u p HZ HI HP Hp). }
  eapply Rle_trans; [exact H|].
  exact (Rmult_le_compat_l (source_mass P Z u)
    (allocated_capacity P Z u) (critical_dissipation P u) HR0 Hd).
Qed.

Theorem NSSD21_ZERO_PHYSICAL_CAPACITY_ZERO_CURRENT : forall P Z T u,
  0<Z -> PacketIndices51 P -> PacketPositive51 P ->
  PacketGeometricCensus51 P Z -> PacketSourceReconstruction51 P T ->
  critical_dissipation P u=0 -> cut_current (ps_space P) T (ps_radius P) u=0.
Proof.
  intros P Z T u HZ HI HP HC HR HD.
  pose proof (NSSD20_NO_OVERLAP_ACTUAL_SOURCE_RECEIPT P Z T u HZ HI HP HC HR) as H.
  rewrite HD in H; nra.
Qed.

Theorem NSSD30_EXACT_PHYSICAL_PACKET_STORAGE_DERIVATIVE :
  forall P nu Z T a b u,
  PacketIndices51 P ->
  ModalPath (ps_space P) (packet_lambda P) T nu a b u ->
  DerivativeOn a b (fun t => packet_H P nu Z (u t))
    (fun t => source_rate P nu Z T (u t)).
Proof.
  intros P nu Z T a b u HI Hp t Ht.
  assert (HD : derivable_pt_lim
    (fun s => sum (ps_count P) (fun p => packet_hcoef P nu Z p*
      packet_q P (u s) p*packet_q P (u s) p)) t
    (2*sum (ps_count P) (fun p => packet_hcoef P nu Z p*packet_q P (u t) p*
      pair_rhs (ps_space P) (packet_lambda P) T nu (u t) (ps_left P p) (ps_right P p)))).
  { apply NSCT40_FINITE_WEIGHTED_ENERGY_DERIVATIVE; intros p Hpi.
    apply (NSPS10_ACTUAL_MODAL_PRODUCT_EQUATION
      (ps_space P) (packet_lambda P) T nu a b u (ps_left P p) (ps_right P p) t Hp).
    - exact (proj1 (proj2 (HI p Hpi))).
    - exact (proj2 (proj2 (HI p Hpi))).
    - exact Ht. }
  assert (He : 2*sum (ps_count P) (fun p => packet_hcoef P nu Z p*packet_q P (u t) p*
      pair_rhs (ps_space P) (packet_lambda P) T nu (u t) (ps_left P p) (ps_right P p))=
      source_rate P nu Z T (u t)).
  { unfold source_rate, source_production, source_dissipation.
    rewrite <- sum_scale, <- sum_sub; apply sum_ext; intros;
    unfold pair_rhs, pair_value, pair_regeneration, packet_q, packet_regeneration; ring. }
  rewrite He in HD; exact HD.
Qed.

Theorem NSSD31_DAMPING_FUNDS_ACTUAL_SOURCE_MASS : forall P nu Z u,
  0<nu -> 0<Z -> PacketIndices51 P -> PacketPositive51 P -> PacketDecayGeometry51 P ->
  source_mass P Z u<=source_dissipation P nu Z u.
Proof.
  intros P nu Z u Hnu HZ HI HP HG.
  unfold source_mass, source_dissipation; apply sum_mono; intros p Hp.
  assert (He : packet_R P Z u p=
    2*nu*ps_gamma P p*packet_hcoef P nu Z p*packet_q P u p*packet_q P u p).
  { unfold packet_R, packet_hcoef.
    pose proof (proj2 (proj2 HP p Hp)); field; nra. }
  rewrite He.
  assert (Hmult : 0<=2*nu*packet_hcoef P nu Z p*packet_q P u p*packet_q P u p).
  { replace (2*nu*packet_hcoef P nu Z p*packet_q P u p*packet_q P u p) with
      ((2*nu*packet_hcoef P nu Z p)*(packet_q P u p*packet_q P u p)) by ring.
    apply Rmult_le_pos.
    - apply Rmult_le_pos; [lra|exact (packet_hcoef_nonnegative51 P nu Z p Hnu HZ HI HP Hp)].
    - exact (Rle_0_sqr (packet_q P u p)). }
  pose proof (Rmult_le_compat_l
    (2*nu*packet_hcoef P nu Z p*packet_q P u p*packet_q P u p)
    (ps_gamma P p)
    (packet_lambda P (ps_left P p)+packet_lambda P (ps_right P p))
    Hmult (proj2 (HG p Hp))); nra.
Qed.

Theorem NSSD32_PACKET_PRODUCTION_IS_CONSTRUCTED_PAIR_PRODUCTION : forall P nu Z T u,
  PacketIndices51 P ->
  pair_production (ps_space P) T (packet_kernel P nu Z) u=
    source_production P nu Z T u.
Proof.
  intros P nu Z T u HI; unfold pair_production, packet_kernel.
  transitivity (sum2 (ps_space P) (fun j k =>
    (-2*pair_value u j k*pair_regeneration (ps_space P) T u j k)*
    pair_fiber P j k (packet_hcoef P nu Z))).
  - rewrite <- sum2_scale; apply sum2_ext; intros; ring.
  - rewrite (weighted_pair_fibers51 P (packet_hcoef P nu Z)
      (fun j k => -2*pair_value u j k*pair_regeneration (ps_space P) T u j k) HI).
    unfold source_production; apply sum_ext; intros;
      unfold packet_q, pair_value, packet_regeneration, pair_regeneration; ring.
Qed.

Theorem NSSD33_ACTUAL_PACKET_QUINTIC_COMMUTATOR : forall P nu Z T u,
  PacketIndices51 P -> SkewTable (ps_space P) T ->
  source_production P nu Z T u =
    -sum2 (ps_space P) (fun i k =>
      convection_matrix (ps_space P) T u i k*u i*u k*
      (modal_chi (ps_space P) (packet_kernel P nu Z) u i-
       modal_chi (ps_space P) (packet_kernel P nu Z) u k)).
Proof.
  intros P nu Z T u HI HT.
  rewrite <- (NSSD32_PACKET_PRODUCTION_IS_CONSTRUCTED_PAIR_PRODUCTION P nu Z T u HI).
  apply NSPS30_QUINTIC_SIGNED_COMMUTATOR; exact HT.
Qed.

Theorem NSSD40_CRITICAL_DERIVATIVE_FROM_SAME_MODAL_PATH : forall P nu T a b u,
  ModalPath (ps_space P) (packet_lambda P) T nu a b u ->
  DerivativeOn a b (fun t => critical_mass P (u t)) (fun t => critical_rate P nu T (u t)).
Proof.
  intros P nu T a b u Hp t Ht.
  exact (NSMG10_MODAL_ODE_GIVES_EXACT_CUT_DERIVATIVE
    (ps_space P) (packet_lambda P) T nu a b u (ps_radius P) t Hp Ht).
Qed.

Theorem NSSD41_ACTUAL_CRITICAL_ABSORPTION : forall P nu Z T u,
  0<nu -> 0<Z -> PacketIndices51 P -> PacketPositive51 P ->
  PacketGeometricCensus51 P Z -> PacketSourceReconstruction51 P T ->
  nu*critical_rate P nu T u+nu*nu*critical_dissipation P u<=source_mass P Z u.
Proof.
  intros P nu Z T u Hnu HZ HI HP HC HR.
  destruct (NSSD10_STORAGE_AND_RATES_NONNEGATIVE P nu Z u Hnu HZ HI HP)
    as [HH [HM [Hm HD]]].
  pose proof (cauchy_quadratic (source_mass P Z u) (critical_dissipation P u)
    (cut_current (ps_space P) T (ps_radius P) u) HM HD
    (NSSD20_NO_OVERLAP_ACTUAL_SOURCE_RECEIPT P Z T u HZ HI HP HC HR) nu) as H.
  unfold critical_rate; nra.
Qed.

Theorem NSSD50_COMBINED_STORAGE_DERIVATIVE : forall P nu Z T a b u,
  PacketIndices51 P ->
  ModalPath (ps_space P) (packet_lambda P) T nu a b u ->
  DerivativeOn a b (fun t => combined_storage P nu Z (u t))
    (fun t => combined_rate P nu Z T (u t)).
Proof.
  intros P nu Z T a b u HI Hp t Ht.
  pose proof (NSSD40_CRITICAL_DERIVATIVE_FROM_SAME_MODAL_PATH P nu T a b u Hp t Ht) as Hm.
  pose proof (NSSD30_EXACT_PHYSICAL_PACKET_STORAGE_DERIVATIVE P nu Z T a b u HI Hp t Ht) as HH.
  pose proof (derivable_pt_lim_scal (fun s => packet_H P nu Z (u s)) (/nu) t
    (source_rate P nu Z T (u t)) HH) as Hscaled.
  pose proof (derivable_pt_lim_plus (fun s => critical_mass P (u s))
    (fun s => (/nu)*packet_H P nu Z (u s)) t
    (critical_rate P nu T (u t)) ((/nu)*source_rate P nu Z T (u t)) Hm Hscaled) as H.
  replace (combined_rate P nu Z T (u t)) with
    (critical_rate P nu T (u t)+(/nu)*source_rate P nu Z T (u t))
    by (unfold combined_rate, Rdiv; ring).
  apply (derivable_pt_lim_ext
    (fun s => critical_mass P (u s)+(/nu)*packet_H P nu Z (u s))
    (fun s => combined_storage P nu Z (u s)) t
    (critical_rate P nu T (u t)+(/nu)*source_rate P nu Z T (u t))).
  - intro s; unfold combined_storage, Rdiv; ring.
  - exact H.
Qed.

Theorem NSSD51_COUPLED_RATE_HAS_ONLY_SIGNED_SOURCE_PRODUCTION : forall P nu Z T u,
  0<nu -> 0<Z -> PacketIndices51 P -> PacketPositive51 P ->
  PacketDecayGeometry51 P -> PacketGeometricCensus51 P Z -> PacketSourceReconstruction51 P T ->
  nu*combined_rate P nu Z T u+nu*nu*critical_dissipation P u<=source_production P nu Z T u.
Proof.
  intros P nu Z T u Hnu HZ HI HP HG HC HR.
  pose proof (NSSD41_ACTUAL_CRITICAL_ABSORPTION P nu Z T u Hnu HZ HI HP HC HR) as H1.
  pose proof (NSSD31_DAMPING_FUNDS_ACTUAL_SOURCE_MASS P nu Z u Hnu HZ HI HP HG) as H2.
  unfold combined_rate, source_rate.
  replace (nu*(critical_rate P nu T u+
    (source_production P nu Z T u-source_dissipation P nu Z u)/nu)) with
    (nu*critical_rate P nu T u+source_production P nu Z T u-source_dissipation P nu Z u)
    by (field; lra).
  lra.
Qed.

End NSE_GP_SOURCE_STORAGE_DYNAMICS.
