From Stdlib Require Import Reals Ranalysis1 Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_native_kq_ladder_v0_49_3.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_galerkin_modal_calculus_v0_50_0.

Module NSE_GP_PAIR_SOURCE_CALCULUS.
Import NSE_KQ_FINITE_ALGEBRA NSE_NATIVE_KQ_LADDER.
Import NSE_CONTINUOUS_TIME_CALCULUS NSE_GALERKIN_MODAL_CALCULUS.
Open Scope R_scope.

Definition PairMatrix := nat -> nat -> R.
Definition sum2 (n : nat) (f : PairMatrix) :=
  sum n (fun i => sum n (fun j => f i j)).

Lemma sum2_ext : forall n f g,
  (forall i j, (i<n)%nat -> (j<n)%nat -> f i j=g i j) ->
  sum2 n f=sum2 n g.
Proof.
  intros n f g H; unfold sum2; apply sum_ext; intros i Hi.
  apply sum_ext; intros j Hj; exact (H i j Hi Hj).
Qed.
Lemma sum2_nonneg : forall n f,
  (forall i j, (i<n)%nat -> (j<n)%nat -> 0<=f i j) -> 0<=sum2 n f.
Proof.
  intros n f H; unfold sum2; apply sum_nonneg; intros i Hi.
  apply sum_nonneg; intros j Hj; exact (H i j Hi Hj).
Qed.
Lemma sum2_mono : forall n f g,
  (forall i j, (i<n)%nat -> (j<n)%nat -> f i j<=g i j) ->
  sum2 n f<=sum2 n g.
Proof.
  intros n f g H; unfold sum2; apply sum_mono; intros i Hi.
  apply sum_mono; intros j Hj; exact (H i j Hi Hj).
Qed.
Lemma sum2_scale : forall n c f,
  sum2 n (fun i j => c*f i j)=c*sum2 n f.
Proof.
  intros n c f; unfold sum2.
  transitivity (sum n (fun i => c*sum n (fun j => f i j))).
  - apply sum_ext; intros i Hi; apply sum_scale.
  - apply sum_scale.
Qed.
Lemma sum2_add : forall n f g,
  sum2 n (fun i j => f i j+g i j)=sum2 n f+sum2 n g.
Proof.
  intros n f g; unfold sum2.
  transitivity (sum n (fun i => sum n (fun j => f i j)+sum n (fun j => g i j))).
  - apply sum_ext; intros i Hi; apply sum_add.
  - apply sum_add.
Qed.
Lemma sum2_sub : forall n f g,
  sum2 n (fun i j => f i j-g i j)=sum2 n f-sum2 n g.
Proof.
  intros n f g; unfold sum2.
  transitivity (sum n (fun i => sum n (fun j => f i j)-sum n (fun j => g i j))).
  - apply sum_ext; intros i Hi; apply sum_sub.
  - apply sum_sub.
Qed.
Lemma sum2_swap : forall n f,
  sum2 n (fun i j => f i j)=sum2 n (fun i j => f j i).
Proof. intros n f; unfold sum2; apply finite_sum_swap. Qed.
Lemma sum2_product : forall n f g,
  sum2 n (fun i j => f i*g j)=sum n f*sum n g.
Proof.
  intros n f g; unfold sum2.
  transitivity (sum n (fun i => f i*sum n g)).
  - apply sum_ext; intros i Hi; apply sum_scale.
  - transitivity (sum n (fun i => sum n g*f i)).
    + apply sum_ext; intros; ring.
    + rewrite sum_scale; ring.
Qed.

Definition pair_value (u : Vec) (i j : nat) := u i*u j.
Definition pair_regeneration n T (u : Vec) i j :=
  modal_source n T u i*u j+u i*modal_source n T u j.
Definition pair_rhs n lambda T nu (u : Vec) i j :=
  -nu*(lambda i+lambda j)*pair_value u i j-pair_regeneration n T u i j.
Definition pair_storage n (C : PairMatrix) (u : Vec) :=
  sum2 n (fun i j => C i j*pair_value u i j*pair_value u i j).
Definition pair_dissipation n lambda nu (C : PairMatrix) (u : Vec) :=
  2*nu*sum2 n (fun i j =>
    C i j*(lambda i+lambda j)*pair_value u i j*pair_value u i j).
Definition pair_production n T (C : PairMatrix) (u : Vec) :=
  -2*sum2 n (fun i j =>
    C i j*pair_value u i j*pair_regeneration n T u i j).

Theorem NSPS10_ACTUAL_MODAL_PRODUCT_EQUATION :
  forall n lambda T nu a b u i j t,
  ModalPath n lambda T nu a b u ->
  (i<n)%nat -> (j<n)%nat -> InTime a b t ->
  derivable_pt_lim (fun s => pair_value (u s) i j) t
    (pair_rhs n lambda T nu (u t) i j).
Proof.
  intros n lambda T nu a b u i j t Hp Hi Hj Ht.
  pose proof (derivable_pt_lim_mult
    (fun s => u s i) (fun s => u s j) t
    (modal_rhs n lambda T nu (u t) i)
    (modal_rhs n lambda T nu (u t) j)
    (Hp t Ht i Hi) (Hp t Ht j Hj)) as HD.
  change (derivable_pt_lim (fun s => pair_value (u s) i j) t
    (modal_rhs n lambda T nu (u t) i*u t j+
     u t i*modal_rhs n lambda T nu (u t) j)) in HD.
  replace (pair_rhs n lambda T nu (u t) i j) with
    (modal_rhs n lambda T nu (u t) i*u t j+
     u t i*modal_rhs n lambda T nu (u t) j).
  - exact HD.
  - unfold pair_rhs, pair_value, pair_regeneration, modal_rhs; ring.
Qed.

Lemma derivative_sum2 : forall n (F : nat -> nat -> R -> R) d t,
  (forall i j, (i<n)%nat -> (j<n)%nat ->
    derivable_pt_lim (F i j) t (d i j)) ->
  derivable_pt_lim (fun s => sum2 n (fun i j => F i j s)) t (sum2 n d).
Proof.
  intros n F d t HD; unfold sum2; apply derivative_finite_sum; intros i Hi.
  apply derivative_finite_sum; intros j Hj; exact (HD i j Hi Hj).
Qed.

Theorem NSPS20_ACTUAL_QUARTIC_STORAGE_DERIVATIVE :
  forall n lambda T nu a b u C,
  ModalPath n lambda T nu a b u ->
  DerivativeOn a b (fun t => pair_storage n C (u t))
    (fun t => pair_production n T C (u t)-pair_dissipation n lambda nu C (u t)).
Proof.
  intros n lambda T nu a b u C Hp t Ht.
  assert (HD : derivable_pt_lim
    (fun s => sum2 n (fun i j => C i j*(pair_value (u s) i j*pair_value (u s) i j))) t
    (sum2 n (fun i j => C i j*
      (pair_rhs n lambda T nu (u t) i j*pair_value (u t) i j+
       pair_value (u t) i j*pair_rhs n lambda T nu (u t) i j)))).
  { apply derivative_sum2; intros i j Hi Hj.
    apply (derivable_pt_lim_scal
      (fun s => pair_value (u s) i j*pair_value (u s) i j) (C i j) t
      (pair_rhs n lambda T nu (u t) i j*pair_value (u t) i j+
       pair_value (u t) i j*pair_rhs n lambda T nu (u t) i j)).
    apply (derivable_pt_lim_mult
      (fun s => pair_value (u s) i j) (fun s => pair_value (u s) i j) t
      (pair_rhs n lambda T nu (u t) i j) (pair_rhs n lambda T nu (u t) i j));
    exact (NSPS10_ACTUAL_MODAL_PRODUCT_EQUATION n lambda T nu a b u i j t Hp Hi Hj Ht). }
  assert (Hr : sum2 n (fun i j => C i j*
      (pair_rhs n lambda T nu (u t) i j*pair_value (u t) i j+
       pair_value (u t) i j*pair_rhs n lambda T nu (u t) i j)) =
    pair_production n T C (u t)-pair_dissipation n lambda nu C (u t)).
  { unfold pair_production, pair_dissipation.
    rewrite <- !sum2_scale, <- sum2_sub.
    apply sum2_ext; intros; unfold pair_rhs; ring. }
  rewrite Hr in HD.
  apply (derivable_pt_lim_ext
    (fun s => sum2 n (fun i j => C i j*(pair_value (u s) i j*pair_value (u s) i j)))
    (fun s => pair_storage n C (u s)) t
    (pair_production n T C (u t)-pair_dissipation n lambda nu C (u t))).
  - intro s; unfold pair_storage; apply sum2_ext; intros; ring.
  - exact HD.
Qed.

Theorem NSPS21_SOURCE_STORAGE_NONNEGATIVE : forall n C u,
  (forall i j, (i<n)%nat -> (j<n)%nat -> 0<=C i j) ->
  0<=pair_storage n C u.
Proof.
  intros n C u HC; unfold pair_storage; apply sum2_nonneg; intros i j Hi Hj.
  replace (C i j*pair_value u i j*pair_value u i j) with
    (C i j*(pair_value u i j*pair_value u i j)) by ring.
  apply Rmult_le_pos; [exact (HC i j Hi Hj)|exact (Rle_0_sqr (pair_value u i j))].
Qed.

Definition modal_chi n (C : PairMatrix) (u : Vec) i :=
  sum n (fun j => (C i j+C j i)*u j*u j).

Lemma pair_production_gradient : forall n T C u,
  pair_production n T C u =
  -2*dot n (modal_source n T u) (mul (modal_chi n C u) u).
Proof.
  intros n T C u.
  assert (He : sum2 n (fun i j =>
      C i j*pair_value u i j*pair_regeneration n T u i j) =
    dot n (modal_source n T u) (mul (modal_chi n C u) u)).
  { unfold pair_value, pair_regeneration.
    transitivity
      (sum2 n (fun i j => C i j*u i*u j*u j*modal_source n T u i)+
       sum2 n (fun i j => C i j*u i*u i*u j*modal_source n T u j)).
    - rewrite <- sum2_add; apply sum2_ext; intros; ring.
    - rewrite (sum2_swap n (fun i j => C i j*u i*u i*u j*modal_source n T u j)).
      rewrite <- sum2_add.
      unfold sum2, dot, mul, modal_chi; apply sum_ext; intros i Hi.
      transitivity (sum n (fun j =>
        (modal_source n T u i*u i)*((C i j+C j i)*u j*u j))).
      + apply sum_ext; intros; ring.
      + rewrite sum_scale; ring. }
  unfold pair_production; rewrite He; reflexivity.
Qed.

Theorem NSPS30_QUINTIC_SIGNED_COMMUTATOR : forall n T C u,
  SkewTable n T ->
  pair_production n T C u =
  -sum2 n (fun i k => convection_matrix n T u i k*u i*u k*
    (modal_chi n C u i-modal_chi n C u k)).
Proof.
  intros n T C u HT; rewrite pair_production_gradient.
  set (chi := modal_chi n C u).
  set (M := convection_matrix n T u).
  assert (Hs : dot n (matvec n M u) (mul chi u) =
      -dot n (matvec n M (mul chi u)) u).
  { apply NSMG00_SKEW_MATRIX_PAIRING.
    exact (NSMG01_COEFFICIENT_TABLE_GIVES_SKEW_CONVECTION n T u HT). }
  assert (Hd : sum2 n (fun i k => M i k*u i*u k*(chi i-chi k)) =
      dot n (matvec n M u) (mul chi u)-dot n (matvec n M (mul chi u)) u).
  { rewrite !dot_matvec_expansion.
    change (sum2 n (fun i k => M i k*u i*u k*(chi i-chi k)) =
      sum2 n (fun i k => M i k*u k*mul chi u i)-
      sum2 n (fun i k => M i k*mul chi u k*u i)).
    rewrite <- sum2_sub; apply sum2_ext; intros; unfold mul; ring. }
  change (-2*dot n (matvec n M u) (mul chi u) =
    -sum2 n (fun i k => M i k*u i*u k*(chi i-chi k))).
  rewrite Hd; lra.
Qed.

Theorem NSPS40_CONSTANT_STORAGE_SHIFT_IS_ENERGY_SQUARED : forall n C u sigma,
  pair_storage n (fun i j => C i j+sigma) u =
  pair_storage n C u+sigma*norm2 n u*norm2 n u.
Proof.
  intros n C u sigma; unfold pair_storage.
  transitivity (sum2 n (fun i j => C i j*pair_value u i j*pair_value u i j)+
    sigma*sum2 n (fun i j => (u i*u i)*(u j*u j))).
  - rewrite <- sum2_scale, <- sum2_add; apply sum2_ext; intros;
      unfold pair_value; ring.
  - rewrite sum2_product; unfold norm2, dot; ring.
Qed.

Theorem NSPS41_CONSTANT_STORAGE_SHIFT_HAS_NO_NEW_PRODUCTION : forall n T C u sigma,
  SkewTable n T ->
  pair_production n T (fun i j => C i j+sigma) u=pair_production n T C u.
Proof.
  intros n T C u sigma HT; rewrite !NSPS30_QUINTIC_SIGNED_COMMUTATOR by exact HT.
  f_equal; apply sum2_ext; intros i k Hi Hk.
  assert (Hchi : forall l,
    modal_chi n (fun p q => C p q+sigma) u l=
    modal_chi n C u l+2*sigma*norm2 n u).
  { intro l; unfold modal_chi, norm2, dot.
    rewrite <- sum_scale, <- sum_add; apply sum_ext; intros; ring. }
  rewrite !Hchi; ring.
Qed.

Theorem NSPS50_POINTWISE_KERNEL_BOUND_GIVES_UNIFORM_STORAGE :
  forall n C r u B,
  (forall i, (i<n)%nat -> 0<=r i) ->
  (forall i j, (i<n)%nat -> (j<n)%nat -> C i j<=B*r i*r j) ->
  pair_storage n C u<=B*cut_mass n r u*cut_mass n r u.
Proof.
  intros n C r u B Hr HC.
  assert (Hb : pair_storage n C u <=
    B*sum2 n (fun i j => (r i*u i*u i)*(r j*u j*u j))).
  { unfold pair_storage; rewrite <- sum2_scale; apply sum2_mono; intros i j Hi Hj.
    pose proof (Rmult_le_compat_r
      (pair_value u i j*pair_value u i j)
      (C i j) (B*r i*r j) (Rle_0_sqr (pair_value u i j)) (HC i j Hi Hj)) as H.
    unfold pair_value in H |- *; nra. }
  rewrite sum2_product in Hb.
  change (pair_storage n C u <=
    B * (cut_mass n r u * cut_mass n r u)) in Hb.
  replace (B * cut_mass n r u * cut_mass n r u)
    with (B * (cut_mass n r u * cut_mass n r u)) by ring.
  exact Hb.
Qed.

Theorem NSPS51_KERNEL_BOUND_GIVES_GRADIENT_BOUND : forall n C r u B i,
  (forall j, (j<n)%nat -> 0<=r j) ->
  (forall j k, (j<n)%nat -> (k<n)%nat -> 0<=C j k) ->
  (forall j k, (j<n)%nat -> (k<n)%nat -> C j k<=B*r j*r k) ->
  (i<n)%nat ->
  0<=modal_chi n C u i<=2*B*r i*cut_mass n r u.
Proof.
  intros n C r u B i Hr HC HB Hi; split.
  - unfold modal_chi; apply sum_nonneg; intros j Hj.
    replace ((C i j+C j i)*u j*u j) with ((C i j+C j i)*(u j*u j)) by ring.
    apply Rmult_le_pos; [pose proof (HC i j Hi Hj); pose proof (HC j i Hj Hi); lra|
      exact (Rle_0_sqr (u j))].
  - unfold modal_chi, cut_mass; rewrite <- sum_scale; apply sum_mono; intros j Hj.
    assert (Hc : C i j+C j i<=2*B*r i*r j).
    { pose proof (HB i j Hi Hj); pose proof (HB j i Hj Hi); nra. }
    pose proof (Rmult_le_compat_r (u j*u j)
      (C i j+C j i) (2*B*r i*r j) (Rle_0_sqr (u j)) Hc); nra.
Qed.

End NSE_GP_PAIR_SOURCE_CALCULUS.
