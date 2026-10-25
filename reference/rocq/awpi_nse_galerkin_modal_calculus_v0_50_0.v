From Stdlib Require Import Reals Ranalysis1 Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.
Require Import awpi_nse_native_kq_ladder_v0_49_3.
Require Import awpi_nse_schur_action_ledger_v0_49_3.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.

Module NSE_GALERKIN_MODAL_CALCULUS.
Import NSE_KQ_FINITE_ALGEBRA NSE_NATIVE_KQ_LADDER.
Import NSE_SCHUR_ACTION_LEDGER NSE_CONTINUOUS_TIME_CALCULUS.
Open Scope R_scope.

(* Real coordinates of a finite Galerkin carrier.  A concrete Fourier
   convection table must be bound to this table in the PDE realization.
   Skewness is the integration-by-parts property, not a regularity premise. *)
Definition CoefficientTable := nat -> nat -> nat -> R.
Definition SkewTable n (T : CoefficientTable) : Prop :=
  forall i j k, (i<n)%nat -> (j<n)%nat -> (k<n)%nat -> T i j k = -T k j i.
Definition convection_matrix n (T : CoefficientTable) (u : Vec) i k :=
  sum n (fun j => T i j k*u j).
Definition matvec n (C : nat -> nat -> R) (x : Vec) : Vec :=
  fun i => sum n (fun j => C i j*x j).
Definition modal_source n (T : CoefficientTable) (u : Vec) : Vec :=
  matvec n (convection_matrix n T u) u.
Definition modal_rhs n (lambda : Vec) T nu (u : Vec) : Vec :=
  fun i => -nu*lambda i*u i-modal_source n T u i.
Definition ModalPath n lambda T nu a b (u : R -> Vec) : Prop :=
  forall t, InTime a b t -> forall i, (i<n)%nat ->
    derivable_pt_lim (fun s => u s i) t (modal_rhs n lambda T nu (u t) i).

Lemma finite_sum_zero : forall n, sum n (fun _ => 0)=0.
Proof. induction n; cbn [sum]; [reflexivity|rewrite IHn; ring]. Qed.

Lemma finite_sum_swap : forall n m (F : nat -> nat -> R),
  sum n (fun i => sum m (fun j => F i j)) =
  sum m (fun j => sum n (fun i => F i j)).
Proof.
  induction n as [|n IH]; intros m F.
  - change (0=sum m (fun _ => 0)); symmetry; apply finite_sum_zero.
  - change (sum n (fun i => sum m (fun j => F i j))+
      sum m (fun j => F n j)=
      sum m (fun j => sum n (fun i => F i j)+F n j)).
    rewrite (IH m F); symmetry; apply sum_add.
Qed.

Lemma dot_matvec_expansion : forall n C x y,
  dot n (matvec n C x) y =
  sum n (fun i => sum n (fun j => C i j*x j*y i)).
Proof.
  intros n C x y; unfold dot, matvec; apply sum_ext; intros i Hi.
  transitivity (sum n (fun j => y i*(C i j*x j))).
  - rewrite sum_scale; ring.
  - apply sum_ext; intros; ring.
Qed.

Theorem NSMG00_SKEW_MATRIX_PAIRING : forall n C x y,
  (forall i j, (i<n)%nat -> (j<n)%nat -> C i j = -C j i) ->
  dot n (matvec n C x) y = -dot n (matvec n C y) x.
Proof.
  intros n C x y HC; rewrite !dot_matvec_expansion.
  rewrite (finite_sum_swap n n (fun i j => C i j*x j*y i)).
  replace (-sum n (fun i => sum n (fun j => C i j*y j*x i))) with
    ((-1)*sum n (fun i => sum n (fun j => C i j*y j*x i))) by ring.
  rewrite <- sum_scale; apply sum_ext; intros i Hi.
  rewrite <- sum_scale; apply sum_ext; intros j Hj.
  rewrite (HC j i Hj Hi); ring.
Qed.

Theorem NSMG01_COEFFICIENT_TABLE_GIVES_SKEW_CONVECTION : forall n T u,
  SkewTable n T -> forall i k, (i<n)%nat -> (k<n)%nat ->
  convection_matrix n T u i k = -convection_matrix n T u k i.
Proof.
  intros n T u HT i k Hi Hk; unfold convection_matrix.
  replace (-sum n (fun j => T k j i*u j)) with
    ((-1)*sum n (fun j => T k j i*u j)) by ring.
  rewrite <- sum_scale; apply sum_ext; intros j Hj.
  rewrite (HT i j k Hi Hj Hk); ring.
Qed.

Theorem NSMG02_ACTUAL_MODAL_SOURCE_ENERGY_CANCELLATION : forall n T u,
  SkewTable n T -> dot n (modal_source n T u) u=0.
Proof.
  intros n T u HT.
  pose proof (NSMG00_SKEW_MATRIX_PAIRING n (convection_matrix n T u) u u
    (NSMG01_COEFFICIENT_TABLE_GIVES_SKEW_CONVECTION n T u HT)) as H.
  change (dot n (modal_source n T u) u = -dot n (modal_source n T u) u) in H.
  lra.
Qed.

Definition cut_mass n (s u : Vec) := sum n (fun i => s i*u i*u i).
Definition cut_dissipation n (lambda s u : Vec) :=
  sum n (fun i => s i*lambda i*u i*u i).
Definition cut_current n T (s u : Vec) :=
  -dot n (modal_source n T u) (mul s u).
Definition finite_cut_action n T lambda J w (s : nat -> Vec) (u : Vec) :=
  sum J (fun N => w N*positive_action (cut_current n T (s N) u)
    (cut_dissipation n lambda (s N) u)).

Lemma cut_dissipation_nonnegative : forall n lambda s u,
  (forall i, (i<n)%nat -> 0 <= lambda i) ->
  (forall i, (i<n)%nat -> 0 <= s i) ->
  0 <= cut_dissipation n lambda s u.
Proof.
  intros n lambda s u Hlam Hs; unfold cut_dissipation.
  apply sum_nonneg; intros i Hi.
  replace (s i*lambda i*u i*u i) with ((s i*lambda i)*(u i*u i)) by ring.
  apply Rmult_le_pos.
  - apply Rmult_le_pos; auto.
  - exact (Rle_0_sqr (u i)).
Qed.

Theorem NSMG10_MODAL_ODE_GIVES_EXACT_CUT_DERIVATIVE :
  forall n lambda T nu a b u s t,
  ModalPath n lambda T nu a b u -> InTime a b t ->
  derivable_pt_lim (fun r => cut_mass n s (u r)) t
    (2*cut_current n T s (u t)-2*nu*cut_dissipation n lambda s (u t)).
Proof.
  intros n lambda T nu a b u s t Hpath Ht.
  pose proof (NSCT40_FINITE_WEIGHTED_ENERGY_DERIVATIVE n s u
    (modal_rhs n lambda T nu (u t)) t (Hpath t Ht)) as HD.
  assert (He : sum n (fun i => s i*u t i*modal_rhs n lambda T nu (u t) i) =
      -nu*cut_dissipation n lambda s (u t)+cut_current n T s (u t)).
  { unfold cut_dissipation, cut_current, dot, mul.
    transitivity (sum n (fun i =>
      (-nu)*(s i*lambda i*u t i*u t i)-
      modal_source n T (u t) i*(s i*u t i))).
    - apply sum_ext; intros; unfold modal_rhs; ring.
    - rewrite sum_sub, sum_scale; ring. }
  rewrite He in HD.
  replace (2*(-nu*cut_dissipation n lambda s (u t)+cut_current n T s (u t)))
    with (2*cut_current n T s (u t)-2*nu*cut_dissipation n lambda s (u t)) in HD by ring.
  exact HD.
Qed.

Lemma unit_cut_mass : forall n u,
  cut_mass n (fun _ => 1) u = norm2 n u.
Proof. intros; unfold cut_mass, norm2, dot; apply sum_ext; intros; ring. Qed.
Lemma unit_cut_dissipation : forall n lambda u,
  cut_dissipation n lambda (fun _ => 1) u = spectral_energy n lambda u.
Proof. intros; unfold cut_dissipation, spectral_energy; apply sum_ext; intros; ring. Qed.
Lemma unit_cut_current : forall n T u,
  SkewTable n T -> cut_current n T (fun _ => 1) u=0.
Proof.
  intros n T u HT; unfold cut_current.
  assert (He : dot n (modal_source n T u) (mul (fun _ => 1) u) =
    dot n (modal_source n T u) u).
  { apply dot_ext_r; intros; unfold mul; ring. }
  rewrite He, (NSMG02_ACTUAL_MODAL_SOURCE_ENERGY_CANCELLATION n T u HT); ring.
Qed.

Theorem NSMG11_MODAL_ODE_GIVES_LERAY_ENERGY_DERIVATIVE :
  forall n lambda T nu a b u,
  SkewTable n T -> ModalPath n lambda T nu a b u ->
  DerivativeOn a b (fun t => norm2 n (u t))
    (fun t => -2*nu*spectral_energy n lambda (u t)).
Proof.
  intros n lambda T nu a b u HT Hpath t Ht.
  pose proof (NSMG10_MODAL_ODE_GIVES_EXACT_CUT_DERIVATIVE
    n lambda T nu a b u (fun _ => 1) t Hpath Ht) as HD.
  rewrite (unit_cut_current n T (u t) HT), unit_cut_dissipation in HD.
  replace (2*0-2*nu*spectral_energy n lambda (u t))
    with (-2*nu*spectral_energy n lambda (u t)) in HD by ring.
  exact (derivable_pt_lim_ext (fun s => cut_mass n (fun _ => 1) (u s))
    (fun s => norm2 n (u s)) t (-2*nu*spectral_energy n lambda (u t))
    (fun s => unit_cut_mass n (u s)) HD).
Qed.

Lemma sum_term_at_most_sum : forall n f i,
  (forall j, (j<n)%nat -> 0 <= f j) -> (i<n)%nat -> f i <= sum n f.
Proof.
  induction n as [|n IH]; intros f i Hpos Hi; [lia|].
  change (f i <= sum n f+f n).
  assert (Hn : 0 <= f n) by (apply Hpos; lia).
  destruct (Nat.eq_dec i n) as [He|He].
  - subst i; pose proof (sum_nonneg n f) as Hp.
    assert (Hinner : forall j, (j<n)%nat -> 0 <= f j).
    { intros; apply Hpos; lia. }
    specialize (Hp Hinner); lra.
  - assert (Hin : (i<n)%nat) by lia.
    assert (Hinner : forall j, (j<n)%nat -> 0 <= f j).
    { intros; apply Hpos; lia. }
    pose proof (IH f i Hinner Hin); lra.
Qed.

(* The total real quotient never hides a nonzero physical current at a
   zero denominator: this is proved under positive Stokes eigenvalues. *)
Theorem NSMG20_ZERO_CUT_CAPACITY_HAS_ZERO_CURRENT : forall n lambda T s u,
  (forall i, (i<n)%nat -> 0 < lambda i) ->
  (forall i, (i<n)%nat -> 0 <= s i) ->
  cut_dissipation n lambda s u=0 -> cut_current n T s u=0.
Proof.
  intros n lambda T s u Hlam Hs HG.
  assert (Hterms : forall i, (i<n)%nat -> 0 <= s i*lambda i*u i*u i).
  { intros i Hi; replace (s i*lambda i*u i*u i)
      with ((s i*lambda i)*(u i*u i)) by ring.
    apply Rmult_le_pos.
    - apply Rmult_le_pos; [exact (Hs i Hi)|].
      apply Rlt_le; exact (Hlam i Hi).
    - exact (Rle_0_sqr (u i)). }
  assert (Hz : forall i, (i<n)%nat -> mul s u i=0).
  { intros i Hi.
    pose proof (sum_term_at_most_sum n
      (fun k => s k*lambda k*u k*u k) i Hterms Hi) as Hle.
    change (s i*lambda i*u i*u i <= cut_dissipation n lambda s u) in Hle.
    rewrite HG in Hle.
    destruct (Req_dec (s i) 0) as [Hs0|Hs0].
    - unfold mul; rewrite Hs0; ring.
    - assert (Hcoeff : 0 < s i*lambda i).
      { apply Rmult_lt_0_compat.
        - pose proof (Hs i Hi); lra.
        - exact (Hlam i Hi). }
      assert (Hprod : (s i*lambda i)*(u i*u i)=0).
      { pose proof (Hterms i Hi); nra. }
      destruct (Rmult_integral (s i*lambda i) (u i*u i) Hprod) as [Hc|Hu].
      + lra.
      + assert (Hu0 : u i=0) by nra; unfold mul; rewrite Hu0; ring. }
  unfold cut_current.
  assert (He : dot n (modal_source n T u) (mul s u) = 0).
  { unfold dot; transitivity (sum n (fun _ => 0)).
    - apply sum_ext; intros i Hi; rewrite (Hz i Hi); ring.
    - apply finite_sum_zero. }
  rewrite He; ring.
Qed.

Lemma positive_action_nonnegative : forall phi g,
  0 <= g -> 0 <= positive_action phi g.
Proof.
  intros phi g Hg; unfold positive_action, Rdiv.
  destruct (Req_dec g 0) as [Hg0|Hg0].
  - subst g; rewrite Rinv_0, Rmult_0_r; lra.
  - apply Rmult_le_pos.
    + exact (Rle_0_sqr (Rmax phi 0)).
    + apply Rlt_le; apply Rinv_0_lt_compat; lra.
Qed.

Theorem NSMG21_FINITE_PHYSICAL_CUT_ACTION_NONNEGATIVE :
  forall n lambda T J w s u,
  (forall i, (i<n)%nat -> 0 <= lambda i) ->
  (forall N, (N<J)%nat -> 0 <= w N) ->
  (forall N i, (N<J)%nat -> (i<n)%nat -> 0 <= s N i) ->
  0 <= finite_cut_action n T lambda J w s u.
Proof.
  intros n lambda T J w s u Hlam Hw Hs.
  unfold finite_cut_action; apply sum_nonneg; intros N HN.
  apply Rmult_le_pos; [exact (Hw N HN)|].
  apply positive_action_nonnegative; apply cut_dissipation_nonnegative.
  - exact Hlam.
  - intros i Hi; exact (Hs N i HN Hi).
Qed.

Theorem NSMG30_PHYSICAL_LADDER_NORMALIZATION_GIVES_BUDGET :
  forall n gdim ell lambda seed stages u d,
  (forall i, (i<n)%nat -> 0 <= lambda i) ->
  (forall i, (i<n)%nat -> clock_run ell lambda seed stages i=u i) ->
  norm2 gdim d = sum stages (fun j =>
    clock_cost n (ell j) lambda (clock_run ell lambda seed j)) ->
  2*norm2 gdim d <= spectral_energy n lambda u.
Proof.
  intros n gdim ell lambda seed stages u d Hlam Hend Hnorm.
  pose proof (NSKL11_FINITE_LADDER_NO_REUSE_BUDGET n ell lambda seed stages Hlam) as Hb.
  assert (He : spectral_energy n lambda (clock_run ell lambda seed stages) =
    spectral_energy n lambda u).
  { unfold spectral_energy; apply sum_ext; intros i Hi; rewrite (Hend i Hi); reflexivity. }
  rewrite He, <- Hnorm in Hb; exact Hb.
Qed.

Lemma modal_rhs_detector_pairing : forall n lambda T nu u K,
  dot n K (modal_rhs n lambda T nu u) =
  (-nu)*dot n K (mul lambda u)-dot n (modal_source n T u) K.
Proof.
  intros n lambda T nu u K.
  rewrite (dot_sym n (modal_source n T u) K).
  unfold dot, modal_rhs, mul.
  transitivity (sum n (fun i =>
    (-nu)*(K i*(lambda i*u i))-K i*modal_source n T u i)).
  - apply sum_ext; intros; ring.
  - rewrite sum_sub, sum_scale; reflexivity.
Qed.

(* This derives the time renewal identity from the gradient-along-path
   and heat-generator identities.  It does not claim to construct the
   infinite future-heat integral or its gradient. *)
Theorem NSMG40_POTENTIAL_CHAIN_AND_HEAT_GENERATOR_GIVE_RENEWAL :
  forall n lambda T nu a b (u : R -> Vec) (V : Vec -> R)
    (K : Vec -> Vec) (A : Vec -> R) (r : R -> R),
  (forall t, InTime a b t ->
    derivable_pt_lim (fun s => V (u s)) t
      (dot n (K (u t)) (modal_rhs n lambda T nu (u t)))) ->
  (forall t, InTime a b t ->
    (-nu)*dot n (K (u t)) (mul lambda (u t)) = -A (u t)) ->
  (forall t, InTime a b t -> r t = -dot n (modal_source n T (u t)) (K (u t))) ->
  DerivativeOn a b (fun t => V (u t)) (fun t => r t-A (u t)).
Proof.
  intros n lambda T nu a b u V K A r Hchain Hheat Hsource t Ht.
  pose proof (Hchain t Ht) as HD.
  assert (Hrate : dot n (K (u t)) (modal_rhs n lambda T nu (u t)) =
    r t-A (u t)).
  { rewrite modal_rhs_detector_pairing.
    pose proof (Hheat t Ht); pose proof (Hsource t Ht); lra. }
  rewrite Hrate in HD;
  exact HD.
Qed.

End NSE_GALERKIN_MODAL_CALCULUS.
