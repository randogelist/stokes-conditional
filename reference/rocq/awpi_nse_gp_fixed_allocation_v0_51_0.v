From Stdlib Require Import Reals Ranalysis1 Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.
Require Import awpi_nse_gp_pair_source_calculus_v0_51_0.

Module NSE_GP_FIXED_ALLOCATION.
Import NSE_KQ_FINITE_ALGEBRA NSE_CONTINUOUS_TIME_CALCULUS.
Import NSE_GALERKIN_MODAL_CALCULUS NSE_GP_PAIR_SOURCE_CALCULUS.
Open Scope R_scope.

(* Finite, directed packet channels.  A complete triad may have several
   channels.  Refining a complete packet into its channels keeps every
   signed term; no assumption of channelwise energy cancellation is made.
   The data are spatial and time independent.  The eventual solution space
   is not a field of this record. *)
Record PacketData51 : Type := {
  ps_space : nat;
  ps_count : nat;
  ps_radius : Vec;
  ps_out : nat -> nat;
  ps_left : nat -> nat;
  ps_right : nat -> nat;
  ps_coeff : Vec;
  ps_rho : Vec;
  ps_gamma : Vec
}.
Definition PacketIndices51 P : Prop :=
  forall p, (p<ps_count P)%nat ->
    (ps_out P p<ps_space P)%nat /\
    (ps_left P p<ps_space P)%nat /\
    (ps_right P p<ps_space P)%nat.
Definition PacketPositive51 P : Prop :=
  (forall i, (i<ps_space P)%nat -> 0<ps_radius P i) /\
  (forall p, (p<ps_count P)%nat -> 0<ps_rho P p /\ 0<ps_gamma P p).
Definition packet_lambda P i := ps_radius P i*ps_radius P i.
Definition allocation51 Z ri rj rk rho := ri/(Z*rho*rho*rj*rk).
Definition packet_weight P Z p := allocation51 Z
  (ps_radius P (ps_out P p)) (ps_radius P (ps_left P p))
  (ps_radius P (ps_right P p)) (ps_rho P p).
Definition geometric_charge P p :=
  ps_radius P (ps_out P p) /
  (ps_rho P p*ps_rho P p*ps_radius P (ps_left P p)*ps_radius P (ps_right P p)).
Definition packet_rcoef P Z p :=
  ps_coeff P p*ps_coeff P p/(packet_weight P Z p*ps_radius P (ps_out P p)).
Definition packet_hcoef P nu Z p := packet_rcoef P Z p/(2*nu*ps_gamma P p).
Definition packet_q P (u : Vec) p := u (ps_left P p)*u (ps_right P p).
Definition packet_R P Z (u : Vec) p := packet_rcoef P Z p*packet_q P u p*packet_q P u p.
Definition packet_D P Z (u : Vec) p := packet_weight P Z p*
  ps_radius P (ps_out P p)*ps_radius P (ps_out P p)*ps_radius P (ps_out P p)*
  u (ps_out P p)*u (ps_out P p).
Definition packet_phi P (u : Vec) p :=
  -ps_radius P (ps_out P p)*u (ps_out P p)*ps_coeff P p*packet_q P u p.
Definition packet_H P nu Z (u : Vec) :=
  sum (ps_count P) (fun p => packet_hcoef P nu Z p*packet_q P u p*packet_q P u p).
Definition source_mass P Z (u : Vec) := sum (ps_count P) (packet_R P Z u).
Definition allocated_capacity P Z (u : Vec) := sum (ps_count P) (packet_D P Z u).
Definition packet_current P (u : Vec) := sum (ps_count P) (packet_phi P u).
Definition critical_mass P (u : Vec) := cut_mass (ps_space P) (ps_radius P) u.
Definition critical_dissipation P (u : Vec) :=
  cut_dissipation (ps_space P) (packet_lambda P) (ps_radius P) u.

Definition fiber n (index : nat -> nat) i (f : Vec) :=
  sum n (fun p => if Nat.eq_dec (index p) i then f p else 0).
Definition pair_fiber P j k (f : Vec) :=
  sum (ps_count P) (fun p =>
    if Nat.eq_dec (ps_left P p) j then
      if Nat.eq_dec (ps_right P p) k then f p else 0
    else 0).
Definition packet_kernel P nu Z j k := pair_fiber P j k (packet_hcoef P nu Z).
Definition PacketGeometricCensus51 P Z : Prop :=
  forall i, (i<ps_space P)%nat -> fiber (ps_count P) (ps_out P) i (geometric_charge P)<=Z.
Definition PacketPairMultiplicity51 P L : Prop :=
  forall j k, (j<ps_space P)%nat -> (k<ps_space P)%nat ->
    pair_fiber P j k (fun _ => 1)<=L.
Definition PacketCoefficientBound51 P Cb : Prop :=
  forall p, (p<ps_count P)%nat ->
    ps_coeff P p*ps_coeff P p<=Cb*Cb*
      ps_radius P (ps_out P p)*ps_radius P (ps_out P p).
Definition PacketDecayGeometry51 P : Prop :=
  forall p, (p<ps_count P)%nat ->
    ps_rho P p*ps_rho P p<=2*ps_gamma P p /\
    ps_gamma P p<=packet_lambda P (ps_left P p)+packet_lambda P (ps_right P p).

(* This coefficient/source identification must be discharged by an actual
   packet enumeration of the same T.  It is not a free energy or M7 input. *)
Definition PacketSourceReconstruction51 P T : Prop :=
  forall u i, (i<ps_space P)%nat ->
    fiber (ps_count P) (ps_out P) i
      (fun p => ps_coeff P p*packet_q P u p)=modal_source (ps_space P) T u i.

Lemma sum_indicator51 : forall n j f,
  (j<n)%nat -> sum n (fun i => if Nat.eq_dec j i then f i else 0)=f j.
Proof.
  induction n as [|n IH]; intros j f Hj; [lia|].
  change (sum n (fun i => if Nat.eq_dec j i then f i else 0)+
    (if Nat.eq_dec j n then f n else 0)=f j).
  destruct (Nat.eq_dec j n) as [He|He].
  - subst j.
    assert (Hz : sum n (fun i => if Nat.eq_dec n i then f i else 0)=0).
    { transitivity (sum n (fun _ => 0)).
      - apply sum_ext; intros i Hi; destruct (Nat.eq_dec n i); [lia|reflexivity].
      - apply finite_sum_zero. }
    rewrite Hz; ring.
  - rewrite (IH j f) by lia; ring.
Qed.

Lemma scatter51 : forall n p (index : nat -> nat) F,
  (forall s, (s<p)%nat -> (index s<n)%nat) ->
  sum n (fun i => sum p (fun s => if Nat.eq_dec (index s) i then F i s else 0))=
  sum p (fun s => F (index s) s).
Proof.
  intros n p index F Hi.
  rewrite (finite_sum_swap n p (fun i s => if Nat.eq_dec (index s) i then F i s else 0)).
  apply sum_ext; intros s Hs.
  exact (@sum_indicator51 n (index s) (fun i => F i s) (Hi s Hs)).
Qed.

Lemma weighted_fibers51 : forall n p index f g,
  (forall s, (s<p)%nat -> (index s<n)%nat) ->
  sum n (fun i => g i*fiber p index i f)=sum p (fun s => g (index s)*f s).
Proof.
  intros n p index f g Hi.
  transitivity (sum n (fun i => sum p
    (fun s => if Nat.eq_dec (index s) i then g i*f s else 0))).
  - apply sum_ext; intros i Hit; unfold fiber; rewrite <- sum_scale.
    apply sum_ext; intros s Hs; destruct (Nat.eq_dec (index s) i); ring.
  - exact (@scatter51 n p index (fun i s => g i*f s) Hi).
Qed.

Lemma weighted_pair_fibers51 : forall P f G,
  PacketIndices51 P ->
  sum2 (ps_space P) (fun j k => G j k*pair_fiber P j k f)=
  sum (ps_count P) (fun p => G (ps_left P p) (ps_right P p)*f p).
Proof.
  intros P f G Hi; unfold sum2.
  transitivity (sum (ps_space P) (fun j =>
    sum (ps_count P) (fun p =>
      if Nat.eq_dec (ps_left P p) j then G j (ps_right P p)*f p else 0))).
  - apply sum_ext; intros j Hj.
    transitivity (sum (ps_space P) (fun k =>
      sum (ps_count P) (fun p => if Nat.eq_dec (ps_right P p) k then
        (if Nat.eq_dec (ps_left P p) j then G j k*f p else 0) else 0))).
    + apply sum_ext; intros k Hk; unfold pair_fiber; rewrite <- sum_scale.
      apply sum_ext; intros p Hp;
      destruct (Nat.eq_dec (ps_left P p) j);
      destruct (Nat.eq_dec (ps_right P p) k); ring.
    + exact (@scatter51 (ps_space P) (ps_count P) (ps_right P)
        (fun k p => if Nat.eq_dec (ps_left P p) j then G j k*f p else 0)
        (fun p Hp => proj2 (proj2 (Hi p Hp)))).
  - exact (@scatter51 (ps_space P) (ps_count P) (ps_left P)
      (fun j p => G j (ps_right P p)*f p)
      (fun p Hp => proj1 (proj2 (Hi p Hp)))).
Qed.

Theorem NSFA10_FIXED_ALLOCATION_POSITIVE : forall P Z p,
  0<Z -> PacketIndices51 P -> PacketPositive51 P ->
  (p<ps_count P)%nat -> 0<packet_weight P Z p.
Proof.
  intros P Z p HZ HI [Hr Hg] Hp.
  destruct (HI p Hp) as [Ho [Hl Hk]]; destruct (Hg p Hp) as [Hrho Hgamma].
  unfold packet_weight, allocation51, Rdiv.
  apply Rmult_lt_0_compat; [exact (Hr _ Ho)|].
  apply Rinv_0_lt_compat; repeat apply Rmult_lt_0_compat;
    try exact HZ; try exact Hrho; [exact (Hr _ Hl)|exact (Hr _ Hk)].
Qed.

Theorem NSFA11_STORAGE_COEFFICIENT_EXACT : forall P nu Z p,
  0<nu -> 0<Z -> PacketIndices51 P -> PacketPositive51 P ->
  (p<ps_count P)%nat ->
  packet_hcoef P nu Z p=
    (Z/(2*nu))*
    (ps_coeff P p*ps_coeff P p*ps_rho P p*ps_rho P p/
      (ps_gamma P p*ps_radius P (ps_out P p)*ps_radius P (ps_out P p)))*
    ps_radius P (ps_left P p)*ps_radius P (ps_right P p).
Proof.
  intros P nu Z p Hnu HZ HI [Hr Hg] Hp.
  destruct (HI p Hp) as [Ho [Hl Hk]]; destruct (Hg p Hp) as [Hrho Hgamma].
  pose proof (Hr _ Ho); pose proof (Hr _ Hl); pose proof (Hr _ Hk).
  unfold packet_hcoef, packet_rcoef, packet_weight, allocation51.
  field; nra.
Qed.

Theorem NSFA12_CANONICAL_LOCAL_STORAGE_BOUND : forall P nu Z Cb p,
  0<nu -> 0<Z -> PacketIndices51 P -> PacketPositive51 P ->
  PacketCoefficientBound51 P Cb -> PacketDecayGeometry51 P ->
  (p<ps_count P)%nat ->
  packet_hcoef P nu Z p <=
    (Z*Cb*Cb/nu)*ps_radius P (ps_left P p)*ps_radius P (ps_right P p).
Proof.
  intros P nu Z Cb p Hnu HZ HI HP HC HG Hp.
  destruct HP as [Hr Hpos]; destruct (HI p Hp) as [Ho [Hl Hk]].
  destruct (Hpos p Hp) as [Hrho Hgamma].
  pose proof (Hr _ Ho) as Hri; pose proof (Hr _ Hl) as Hrj; pose proof (Hr _ Hk) as Hrk.
  pose proof (HC p Hp) as Hc; pose proof (proj1 (HG p Hp)) as Hscale.
  assert (Hden : 0<ps_gamma P p*ps_radius P (ps_out P p)*ps_radius P (ps_out P p)).
  { repeat apply Rmult_lt_0_compat; assumption. }
  assert (Ha : ps_coeff P p*ps_coeff P p*ps_rho P p*ps_rho P p/
    (ps_gamma P p*ps_radius P (ps_out P p)*ps_radius P (ps_out P p))<=2*Cb*Cb).
  { apply (Rmult_le_reg_r (ps_gamma P p*ps_radius P (ps_out P p)*ps_radius P (ps_out P p)));
      [exact Hden|].
    replace ((ps_coeff P p*ps_coeff P p*ps_rho P p*ps_rho P p/
      (ps_gamma P p*ps_radius P (ps_out P p)*ps_radius P (ps_out P p)))*
      (ps_gamma P p*ps_radius P (ps_out P p)*ps_radius P (ps_out P p))) with
      (ps_coeff P p*ps_coeff P p*ps_rho P p*ps_rho P p) by (field; nra).
    pose proof (Rmult_le_compat_r (ps_rho P p*ps_rho P p)
      (ps_coeff P p*ps_coeff P p)
      (Cb*Cb*ps_radius P (ps_out P p)*ps_radius P (ps_out P p))
      (Rle_0_sqr (ps_rho P p)) Hc) as H1.
    assert (Hcoef : 0<=Cb*Cb*ps_radius P (ps_out P p)*ps_radius P (ps_out P p)).
    { replace (Cb*Cb*ps_radius P (ps_out P p)*ps_radius P (ps_out P p)) with
        ((Cb*Cb)*(ps_radius P (ps_out P p)*ps_radius P (ps_out P p))) by ring.
      apply Rmult_le_pos; apply Rle_0_sqr. }
    pose proof (Rmult_le_compat_l
      (Cb*Cb*ps_radius P (ps_out P p)*ps_radius P (ps_out P p))
      (ps_rho P p*ps_rho P p) (2*ps_gamma P p) Hcoef Hscale) as H2; nra. }
  rewrite (NSFA11_STORAGE_COEFFICIENT_EXACT P nu Z p Hnu HZ HI (conj Hr Hpos) Hp).
  assert (Hmult : 0<=(Z/(2*nu))*ps_radius P (ps_left P p)*ps_radius P (ps_right P p)).
  { apply Rlt_le; apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat.
      + unfold Rdiv; apply Rmult_lt_0_compat.
        * exact HZ.
        * apply Rinv_0_lt_compat; lra.
      + exact Hrj.
    - exact Hrk. }
  pose proof (Rmult_le_compat_l
    ((Z/(2*nu))*ps_radius P (ps_left P p)*ps_radius P (ps_right P p))
    (ps_coeff P p*ps_coeff P p*ps_rho P p*ps_rho P p/
      (ps_gamma P p*ps_radius P (ps_out P p)*ps_radius P (ps_out P p)))
    (2*Cb*Cb) Hmult Ha) as Hfin.
  replace ((Z*Cb*Cb/nu)*ps_radius P (ps_left P p)*ps_radius P (ps_right P p)) with
    (((Z/(2*nu))*ps_radius P (ps_left P p)*ps_radius P (ps_right P p))*(2*Cb*Cb))
    by (field; lra).
  nra.
Qed.

Lemma allocation_as_scaled_charge51 : forall P Z p,
  0<Z -> PacketIndices51 P -> PacketPositive51 P -> (p<ps_count P)%nat ->
  packet_weight P Z p=(/Z)*geometric_charge P p.
Proof.
  intros P Z p HZ HI [Hr Hg] Hp; destruct (HI p Hp) as [Ho [Hl Hk]].
  destruct (Hg p Hp) as [Hrho Hgamma].
  pose proof (Hr _ Hl); pose proof (Hr _ Hk).
  unfold packet_weight, allocation51, geometric_charge; field; nra.
Qed.

Theorem NSFA20_GEOMETRIC_CENSUS_ALLOCATES_CAPACITY : forall P Z,
  0<Z -> PacketIndices51 P -> PacketPositive51 P -> PacketGeometricCensus51 P Z ->
  forall i, (i<ps_space P)%nat ->
  fiber (ps_count P) (ps_out P) i (packet_weight P Z)<=1.
Proof.
  intros P Z HZ HI HP HC i Hi.
  assert (He : fiber (ps_count P) (ps_out P) i (packet_weight P Z)=
    (/Z)*fiber (ps_count P) (ps_out P) i (geometric_charge P)).
  { unfold fiber; rewrite <- sum_scale; apply sum_ext; intros p Hp.
    destruct (Nat.eq_dec (ps_out P p) i).
    - exact (allocation_as_scaled_charge51 P Z p HZ HI HP Hp).
    - ring. }
  rewrite He.
  pose proof (Rmult_le_compat_l (/Z)
    (fiber (ps_count P) (ps_out P) i (geometric_charge P)) Z
    (Rlt_le _ _ (Rinv_0_lt_compat Z HZ)) (HC i Hi)) as H.
  replace ((/Z)*Z) with 1 in H by (field; lra); exact H.
Qed.

Theorem NSFA21_NO_REUSED_DETECTOR_CAPACITY : forall P Z u,
  PacketIndices51 P -> PacketPositive51 P ->
  (forall i, (i<ps_space P)%nat ->
    fiber (ps_count P) (ps_out P) i (packet_weight P Z)<=1) ->
  allocated_capacity P Z u<=critical_dissipation P u.
Proof.
  intros P Z u HI [Hr Hg] Hfib.
  assert (He : allocated_capacity P Z u=
    sum (ps_space P) (fun i =>
      (ps_radius P i*ps_radius P i*ps_radius P i*u i*u i)*
      fiber (ps_count P) (ps_out P) i (packet_weight P Z))).
  { rewrite (weighted_fibers51 (ps_space P) (ps_count P) (ps_out P)
      (packet_weight P Z) (fun i => ps_radius P i*ps_radius P i*ps_radius P i*u i*u i)).
    - unfold allocated_capacity, packet_D; apply sum_ext; intros; ring.
    - intros p Hp; exact (proj1 (HI p Hp)). }
  rewrite He; unfold critical_dissipation, cut_dissipation, packet_lambda.
  apply sum_mono; intros i Hi.
  assert (Hnon : 0<=ps_radius P i*ps_radius P i*ps_radius P i*u i*u i).
  { replace (ps_radius P i*ps_radius P i*ps_radius P i*u i*u i) with
      ((ps_radius P i*ps_radius P i*ps_radius P i)*(u i*u i)) by ring.
    apply Rmult_le_pos; [repeat apply Rmult_le_pos; apply Rlt_le; exact (Hr i Hi)|
      exact (Rle_0_sqr (u i))]. }
  pose proof (Rmult_le_compat_l _ _ _ Hnon (Hfib i Hi)); nra.
Qed.

Theorem NSFA30_PACKET_STORAGE_IS_CONSTRUCTED_PAIR_METRIC : forall P nu Z u,
  PacketIndices51 P ->
  pair_storage (ps_space P) (packet_kernel P nu Z) u=packet_H P nu Z u.
Proof.
  intros P nu Z u HI; unfold pair_storage, packet_kernel.
  transitivity (sum2 (ps_space P) (fun j k =>
    (u j*u k)*(u j*u k)*pair_fiber P j k (packet_hcoef P nu Z))).
  - apply sum2_ext; intros; unfold pair_value; ring.
  - rewrite (weighted_pair_fibers51 P (packet_hcoef P nu Z)
      (fun j k => (u j*u k)*(u j*u k)) HI).
    unfold packet_H, packet_q; apply sum_ext; intros; ring.
Qed.

Theorem NSFA31_LOCAL_BOUND_AND_MULTIPLICITY_GIVE_KERNEL_BOUND : forall P nu Z B L,
  0<=B -> PacketIndices51 P -> PacketPositive51 P ->
  (forall p, (p<ps_count P)%nat ->
    packet_hcoef P nu Z p<=B*ps_radius P (ps_left P p)*ps_radius P (ps_right P p)) ->
  PacketPairMultiplicity51 P L ->
  forall j k, (j<ps_space P)%nat -> (k<ps_space P)%nat ->
    packet_kernel P nu Z j k<=B*L*ps_radius P j*ps_radius P k.
Proof.
  intros P nu Z B L HB HI [Hr Hg] Hlocal Hcount j k Hj Hk.
  assert (He : packet_kernel P nu Z j k<=
    (B*ps_radius P j*ps_radius P k)*pair_fiber P j k (fun _ => 1)).
  { unfold packet_kernel, pair_fiber; rewrite <- sum_scale.
    apply sum_mono; intros p Hp.
    destruct (Nat.eq_dec (ps_left P p) j) as [Hl|Hl];
    destruct (Nat.eq_dec (ps_right P p) k) as [Hrk|Hrk]; try lra.
    specialize (Hlocal p Hp); rewrite Hl, Hrk in Hlocal; nra. }
  assert (Hnon : 0<=B*ps_radius P j*ps_radius P k).
  { repeat apply Rmult_le_pos; try exact HB; apply Rlt_le; auto. }
  pose proof (Rmult_le_compat_l (B*ps_radius P j*ps_radius P k)
    (pair_fiber P j k (fun _ => 1)) L Hnon (Hcount j k Hj Hk)); nra.
Qed.

Theorem NSFA40_UNIFORM_STORAGE_FROM_FIXED_ALLOCATION : forall P nu Z Cb L u,
  0<nu -> 0<Z -> PacketIndices51 P -> PacketPositive51 P ->
  PacketCoefficientBound51 P Cb -> PacketDecayGeometry51 P ->
  PacketPairMultiplicity51 P L ->
  packet_H P nu Z u<=
    (Z*Cb*Cb*L/nu)*critical_mass P u*critical_mass P u.
Proof.
  intros P nu Z Cb L u Hnu HZ HI HP HC HG HM.
  rewrite <- (NSFA30_PACKET_STORAGE_IS_CONSTRUCTED_PAIR_METRIC P nu Z u HI).
  replace (Z*Cb*Cb*L/nu) with ((Z*Cb*Cb/nu)*L) by (field; lra).
  apply NSPS50_POINTWISE_KERNEL_BOUND_GIVES_UNIFORM_STORAGE.
  - intros i Hi; apply Rlt_le; exact (proj1 HP i Hi).
  - apply NSFA31_LOCAL_BOUND_AND_MULTIPLICITY_GIVE_KERNEL_BOUND; try assumption.
    + unfold Rdiv; apply Rmult_le_pos.
      * replace (Z*Cb*Cb) with (Z*(Cb*Cb)) by ring.
        apply Rmult_le_pos; [lra|exact (Rle_0_sqr Cb)].
      * apply Rlt_le; apply Rinv_0_lt_compat; exact Hnu.
    + intros p Hp; exact (NSFA12_CANONICAL_LOCAL_STORAGE_BOUND P nu Z Cb p
        Hnu HZ HI HP HC HG Hp).
Qed.

(* This is a finite identity between the packet coefficient list and T,
   independent of amplitudes, time, topology, or a solution class. *)
Definition PacketCoefficientIdentity51 P T : Prop :=
  forall i j k, (i<ps_space P)%nat -> (j<ps_space P)%nat -> (k<ps_space P)%nat ->
    pair_fiber P j k (fun p =>
      if Nat.eq_dec (ps_out P p) i then ps_coeff P p else 0)=T i j k.

Lemma modal_source_double_sum51 : forall n T u i,
  modal_source n T u i=sum2 n (fun j k => T i j k*u j*u k).
Proof.
  intros n T u i; unfold modal_source, matvec, convection_matrix.
  transitivity (sum2 n (fun k j => T i j k*u j*u k)).
  - unfold sum2; apply sum_ext; intros k Hk.
    transitivity (sum n (fun j => u k*(T i j k*u j))).
    + rewrite sum_scale; ring.
    + apply sum_ext; intros; ring.
  - apply sum2_swap.
Qed.

Theorem NSFA45_COEFFICIENT_IDENTITY_CONSTRUCTS_FULL_SOURCE : forall P T,
  PacketIndices51 P -> PacketCoefficientIdentity51 P T ->
  PacketSourceReconstruction51 P T.
Proof.
  intros P T HI HT u i Hi.
  transitivity (sum2 (ps_space P) (fun j k => (u j*u k)*
    pair_fiber P j k (fun p =>
      if Nat.eq_dec (ps_out P p) i then ps_coeff P p else 0))).
  - rewrite (weighted_pair_fibers51 P
      (fun p => if Nat.eq_dec (ps_out P p) i then ps_coeff P p else 0)
      (fun j k => u j*u k) HI).
    unfold fiber; apply sum_ext; intros p Hp;
      destruct (Nat.eq_dec (ps_out P p) i); unfold packet_q; ring.
  - rewrite modal_source_double_sum51; apply sum2_ext; intros j k Hj Hk.
    rewrite (HT i j k Hi Hj Hk); ring.
Qed.

End NSE_GP_FIXED_ALLOCATION.
