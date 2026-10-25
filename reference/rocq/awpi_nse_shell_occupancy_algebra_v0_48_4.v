From Stdlib Require Import Reals Lra Psatz Lia.
Require Import awpi_nse_finite_shell_algebra_v0_48_4.

Module NSE_SHELL_OCCUPANCY_ALGEBRA.
Import NSE_FINITE_SHELL_ALGEBRA.
Open Scope R_scope.

(* U is a shell L2 norm; A is its Fourier l1 norm. Empty-shell
   consistency is explicit: U=0 implies A=0. *)
Definition shell_cost (lambda A r : R) : R :=
  lambda*lambda*pos (A/lambda-r).
Definition shell_kinetic (lambda U : R) : R := lambda*lambda*U*U.
Definition effective_occupancy (A U : R) : R := (A*A)/(U*U).
Definition occupancy_ratio (lambda A U : R) : R :=
  (A*A)/(lambda*lambda*U*U).

(* The continuous, least scaled unpaid cost is preferable for the ODE
   interface to the discontinuous hard classification. It is bounded by
   4*r times the original crowded-shell remainder. *)
Definition unpaid (lambda A U r cap : R) : R :=
  pos (4*r*shell_cost lambda A r-cap*shell_kinetic lambda U).
Definition crowded (lambda A U r cap : R) : R :=
  if Rle_dec (A*A) (cap*shell_kinetic lambda U)
  then 0 else shell_cost lambda A r.

Lemma NSSO00_COST_NONNEG : forall lambda A r,
  0 <= shell_cost lambda A r.
Proof.
  intros; unfold shell_cost. apply Rmult_le_pos.
  - pose proof (Rle_0_sqr lambda); unfold Rsqr in *; lra.
  - apply NSFA10_POS_NONNEG.
Qed.
Lemma NSSO01_KINETIC_NONNEG : forall lambda U,
  0 <= shell_kinetic lambda U.
Proof.
  intros; unfold shell_kinetic.
  replace (lambda*lambda*U*U) with ((lambda*U)*(lambda*U)) by ring.
  pose proof (Rle_0_sqr (lambda*U)); unfold Rsqr in *; lra.
Qed.
Lemma NSSO02_CLIP_PAYMENT : forall lambda A r,
  0 < lambda -> 0 <= r ->
  4*r*shell_cost lambda A r <= A*A.
Proof.
  intros lambda A r Hl Hr.
  pose proof (NSFA16_QUADRATIC_CLIP (A/lambda) r Hr) as H.
  assert (Hsq : 0 <= lambda*lambda) by nra.
  pose proof (Rmult_le_compat_l (lambda*lambda) _ _ Hsq H) as HM.
  assert (Heq : lambda*lambda*((A/lambda)*(A/lambda)) = A*A).
  { field; repeat split; lra. }
  rewrite Heq in HM. unfold shell_cost; nra.
Qed.

Lemma NSSO03_OCCUPANCY_IDENTITY : forall lambda A U,
  0 < lambda -> U <> 0 ->
  occupancy_ratio lambda A U * shell_kinetic lambda U = A*A.
Proof. intros; unfold occupancy_ratio, shell_kinetic; field; repeat split; nra. Qed.

Lemma NSSO04_OCCUPANCY_PAYMENT : forall lambda A U r,
  0 < lambda -> 0 <= U -> 0 <= r -> (U=0 -> A=0) ->
  4*r*shell_cost lambda A r <=
  occupancy_ratio lambda A U * shell_kinetic lambda U.
Proof.
  intros lambda A U r Hl HU Hr Hz.
  destruct (Req_dec_T U 0) as [H0|H0].
  - subst U. specialize (Hz eq_refl). subst A.
    unfold shell_cost, occupancy_ratio, shell_kinetic.
    replace (0/lambda-r) with (-r) by (unfold Rdiv; ring).
    rewrite NSFA12_POS_ZERO by lra.
    (* The goal is an inequality, not a ring equation. *)
    repeat rewrite Rmult_0_r.
    apply Rle_refl.
  - rewrite NSSO03_OCCUPANCY_IDENTITY by assumption.
    apply NSSO02_CLIP_PAYMENT; assumption.
Qed.

Lemma NSSO05_RATIO_TEST : forall lambda A U cap,
  0 < lambda -> 0 < U ->
  (occupancy_ratio lambda A U <= cap <->
   A*A <= cap*shell_kinetic lambda U).
Proof.
  intros lambda A U cap Hl HU.
  assert (Hg : 0 < shell_kinetic lambda U).
  { unfold shell_kinetic.
    (* Build strict positivity factor by factor; do not ask nra to
       discover a positive quartic monomial from two linear hypotheses. *)
    repeat apply Rmult_lt_0_compat; assumption. }
  assert (HU0 : U <> 0) by lra.
  pose proof (NSSO03_OCCUPANCY_IDENTITY lambda A U Hl HU0) as Heq.
  split; intro H.
  - rewrite <- Heq.
    apply Rmult_le_compat_r.
    + exact (Rlt_le _ _ Hg).
    + exact H.
  - apply (Rmult_le_reg_r (shell_kinetic lambda U)).
    + exact Hg.
    + rewrite Heq. exact H.
Qed.

Lemma NSSO06_PAID_SHELL : forall lambda A U r cap,
  0 < lambda -> 0 <= r -> A*A <= cap*shell_kinetic lambda U ->
  4*r*shell_cost lambda A r <= cap*shell_kinetic lambda U.
Proof. intros; pose proof (NSSO02_CLIP_PAYMENT lambda A r H H0); lra. Qed.

Lemma NSSO07_UNPAID_NONNEG : forall lambda A U r cap,
  0 <= unpaid lambda A U r cap.
Proof. intros; unfold unpaid; apply NSFA10_POS_NONNEG. Qed.

Lemma NSSO08_MINIMAL_SHELL_SPLIT : forall lambda A U r cap,
  4*r*shell_cost lambda A r <=
  cap*shell_kinetic lambda U + unpaid lambda A U r cap.
Proof. intros; unfold unpaid; apply NSFA17_MINIMAL_UNPAID. Qed.

Lemma NSSO09_CROWDED_NONNEG : forall lambda A U r cap,
  0 <= crowded lambda A U r cap.
Proof.
  intros lambda A U r cap; unfold crowded.
  destruct (Rle_dec (A*A) (cap*shell_kinetic lambda U));
    [lra|apply NSSO00_COST_NONNEG].
Qed.

Lemma NSSO10_UNPAID_VANISHES_WHEN_PAID : forall lambda A U r cap,
  0 < lambda -> 0 <= r -> A*A <= cap*shell_kinetic lambda U ->
  unpaid lambda A U r cap = 0.
Proof.
  intros. unfold unpaid. apply NSFA12_POS_ZERO.
  pose proof (NSSO06_PAID_SHELL lambda A U r cap H H0 H1); lra.
Qed.

Lemma NSSO11_SMALL_SHELL_HAS_NO_DEBT : forall lambda A U r cap,
  0 <= r -> 0 <= cap -> A/lambda <= r ->
  shell_cost lambda A r = 0 /\ unpaid lambda A U r cap = 0.
Proof.
  intros lambda A U r cap Hr Hcap Hsmall.
  assert (Hz : shell_cost lambda A r = 0).
  { unfold shell_cost. rewrite NSFA12_POS_ZERO by lra. ring. }
  split; [exact Hz|]. unfold unpaid; rewrite Hz.
  pose proof (NSSO01_KINETIC_NONNEG lambda U).
  apply NSFA12_POS_ZERO; nra.
Qed.

Lemma NSSO12_HARD_REMAINDER_COVERS_DEBT : forall lambda A U r cap,
  0 < lambda -> 0 <= r -> 0 <= cap ->
  unpaid lambda A U r cap <= 4*r*crowded lambda A U r cap.
Proof.
  intros lambda A U r cap Hl Hr Hcap. unfold crowded.
  destruct (Rle_dec (A*A) (cap*shell_kinetic lambda U)) as [H|H].
  - rewrite NSSO10_UNPAID_VANISHES_WHEN_PAID by assumption. lra.
  - unfold unpaid. apply NSFA15_POS_UPPER.
    + pose proof (NSSO00_COST_NONNEG lambda A r); nra.
    + pose proof (NSSO01_KINETIC_NONNEG lambda U); nra.
Qed.

Lemma NSSO13_CLASSIFICATION : forall lambda A U r cap,
  A/lambda <= r \/
  (r < A/lambda /\ A*A <= cap*shell_kinetic lambda U) \/
  (r < A/lambda /\ cap*shell_kinetic lambda U < A*A).
Proof.
  intros. destruct (Rle_dec (A/lambda) r); [left; assumption|].
  destruct (Rle_dec (A*A) (cap*shell_kinetic lambda U));
    [right; left|right; right]; split; lra.
Qed.

Definition shell_L (A : nat -> R) r J :=
  total (fun j => shell_cost (wave j) (A j) r) J.
Definition shell_G (U : nat -> R) J :=
  total (fun j => shell_kinetic (wave j) (U j)) J.
Definition shell_unpaid (A U : nat -> R) r cap J :=
  total (fun j => unpaid (wave j) (A j) (U j) r cap) J.
Definition shell_crowded (A U : nat -> R) r cap J :=
  total (fun j => crowded (wave j) (A j) (U j) r cap) J.

Lemma NSSO20_FINITE_CONTINUOUS_SPLIT : forall A U r cap J,
  4*r*shell_L A r J <= cap*shell_G U J+shell_unpaid A U r cap J.
Proof.
  intros. unfold shell_L, shell_G, shell_unpaid.
  pose proof (NSFA01_TOTAL_LE
    (fun j => 4*r*shell_cost (wave j) (A j) r)
    (fun j => cap*shell_kinetic (wave j) (U j)+
      unpaid (wave j) (A j) (U j) r cap) J) as H.
  specialize (H ltac:(intros; apply NSSO08_MINIMAL_SHELL_SPLIT)).
  rewrite NSFA04_TOTAL_SCALE in H.
  replace (total (fun j => cap*shell_kinetic (wave j) (U j)+
     unpaid (wave j) (A j) (U j) r cap) J)
   with (cap*total (fun j => shell_kinetic (wave j) (U j)) J+
     total (fun j => unpaid (wave j) (A j) (U j) r cap) J) in H.
  - exact H.
  - pose proof (NSFA03B_TOTAL_AFFINE
      (fun j => shell_kinetic (wave j) (U j))
      (fun j => unpaid (wave j) (A j) (U j) r cap) cap J) as Heq.
    nra.
Qed.

Lemma NSSO21_FINITE_HARD_SPLIT : forall A U r cap J,
  0 <= r -> 0 <= cap ->
  4*r*shell_L A r J <= cap*shell_G U J+4*r*shell_crowded A U r cap J.
Proof.
  intros A U r cap J Hr Hcap.
  pose proof (NSSO20_FINITE_CONTINUOUS_SPLIT A U r cap J) as Hbase.
  assert (Hrem : shell_unpaid A U r cap J <= 4*r*shell_crowded A U r cap J).
  { unfold shell_unpaid, shell_crowded.
    rewrite <- NSFA04_TOTAL_SCALE.
    apply NSFA01_TOTAL_LE. intros j Hj.
    apply NSSO12_HARD_REMAINDER_COVERS_DEBT; try assumption.
    apply NSFA20_WAVE_POS. }
  lra.
Qed.

Lemma NSSO22_NONCROWDED_HAS_ZERO_DEBT : forall A U r cap J,
  0 <= r ->
  (forall j, (j < J)%nat -> A j*A j <= cap*shell_kinetic (wave j) (U j)) ->
  shell_unpaid A U r cap J = 0.
Proof.
  intros A U r cap J Hr Hpay.
  unfold shell_unpaid.
  transitivity (total (fun _ => 0) J).
  - apply NSFA00_TOTAL_EXT. intros j Hj.
    apply NSSO10_UNPAID_VANISHES_WHEN_PAID;
      [apply NSFA20_WAVE_POS|exact Hr|apply Hpay; exact Hj].
  - apply NSFA07_TOTAL_ZERO.
Qed.

(* Canonical finite low-high majorant. Its domination of the actual
   Fourier critical flux remains a named input at the analytic seam. *)
Definition low_prefix (A : nat -> R) h :=
  total (fun l => wave l*A l) (S h).
Definition adjacent (U : nat -> R) j := U j*U j+U j*previous U j.
Definition triad_majorant (A U : nat -> R) J :=
  12*total (fun h => wave h*adjacent U h*low_prefix A h) J.
Definition shell_E (U : nat -> R) J :=
  total (fun j => wave j*U j*U j) J.
Definition shell_D (U : nat -> R) J :=
  total (fun j => wave j*wave j*wave j*U j*U j) J.

Lemma NSSO30_LOW_PREFIX_BOUND : forall A r J h,
  0 <= r -> (h < J)%nat ->
  low_prefix A h <= (4/3)*r*wave h*wave h+shell_L A r J.
Proof.
  intros A r J h Hr Hh.
  assert (Hpoint : forall j, wave j*A j <=
    r*(wave j*wave j)+shell_cost (wave j) (A j) r).
  { intro j. pose proof (NSFA11_POS_ABOVE (A j/wave j-r)) as Hp.
    pose proof (NSFA20_WAVE_POS j) as Hw.
    assert (Hsq : 0 <= wave j*wave j) by nra.
    pose proof (Rmult_le_compat_l (wave j*wave j) _ _ Hsq Hp) as HM.
    assert (Heq : wave j*wave j*(A j/wave j-r)=
       wave j*A j-r*(wave j*wave j)).
    { field; repeat split; lra. }
    rewrite Heq in HM. unfold shell_cost; lra. }
  assert (Hsum : low_prefix A h <=
    r*total (fun j => wave j*wave j) (S h)+
    shell_L A r (S h)).
  { unfold low_prefix, shell_L.
    pose proof (NSFA01_TOTAL_LE _ _ (S h)
      (fun j _ => Hpoint j)) as H.
    rewrite (NSFA03B_TOTAL_AFFINE (fun j => wave j*wave j)
      (fun j => shell_cost (wave j) (A j) r) r (S h)) in H.
    exact H. }
  assert (HL : shell_L A r (S h) <= shell_L A r J).
  { unfold shell_L. apply NSFA05_TOTAL_PREFIX; [lia|].
    intros; apply NSSO00_COST_NONNEG. }
  pose proof (NSFA22_DYADIC_SQUARE_PREFIX h) as Hg.
  pose proof (Rmult_le_compat_l r _ _ Hr Hg) as Hrg. nra.
Qed.

Lemma NSSO31_ADJACENT_NONNEG : forall U j,
  (forall k, 0 <= U k) -> 0 <= adjacent U j.
Proof.
  intros U j HU. unfold adjacent, previous.
  destruct j; [pose proof (HU O)|pose proof (HU (S j)); pose proof (HU j)]; nra.
Qed.

Lemma NSSO32_ADJACENT_ENERGY : forall U J,
  total (fun j => wave j*adjacent U j) J <= 3*shell_E U J.
Proof.
  intros U J.
  set (e := fun j => wave j*U j*U j).
  assert (Hpt : forall j, wave j*adjacent U j <= 2*e j+previous e j).
  { intro j; destruct j as [|j].
    - unfold adjacent, previous, e; simpl.
      pose proof (Rle_0_sqr (U O)); unfold Rsqr in *; nra.
    - unfold adjacent, previous, e; cbn [wave].
      pose proof (Rle_0_sqr (U (S j)-U j)) as Hsq.
      pose proof (Rle_0_sqr (U (S j))) as Hsq2.
      unfold Rsqr in *.
      assert (Hyoung : 2*U (S j)*U j <= 2*U (S j)*U (S j)+U j*U j) by nra.
      pose proof (Rmult_le_compat_l (wave j) _ _
        (Rlt_le _ _ (NSFA20_WAVE_POS j)) Hyoung) as Hw; nra. }
  pose proof (NSFA01_TOTAL_LE _ _ J (fun j _ => Hpt j)) as Hsum.
  pose proof (NSFA03B_TOTAL_AFFINE e (previous e) 2 J) as Hlin.
  simpl in Hlin.
  assert (Hs : total (previous e) J <= total e J).
  { apply NSFA06_PREVIOUS_SUM. intros j Hj; unfold e.
    pose proof (Rle_0_sqr (U j)) as Hsq. unfold Rsqr in Hsq.
    pose proof (Rmult_le_compat_l (wave j) _ _
      (Rlt_le _ _ (NSFA20_WAVE_POS j)) Hsq). nra. }
  change (total (fun j => wave j*adjacent U j) J <= 3*total e J).
  nra.
Qed.

Lemma NSSO33_ADJACENT_DISSIPATION : forall U J,
  total (fun j => wave j*wave j*wave j*adjacent U j) J <= 4*shell_D U J.
Proof.
  intros U J.
  set (d := fun j => wave j*wave j*wave j*U j*U j).
  assert (Hpt : forall j,
    wave j*wave j*wave j*adjacent U j <= (5/2)*d j+(3/2)*previous d j).
  { intro j; destruct j as [|j].
    - unfold adjacent, previous, d; simpl.
      pose proof (Rle_0_sqr (U O)); unfold Rsqr in *; nra.
    - unfold adjacent, previous, d; cbn [wave].
      pose proof (Rle_0_sqr (3*U (S j)-U j)) as Hsq.
      pose proof (Rle_0_sqr (U j)) as Hsq2. unfold Rsqr in *.
      assert (Hyoung : 8*U (S j)*U j <= 12*U (S j)*U (S j)+(3/2)*U j*U j) by nra.
      assert (Hw : 0 <= wave j*wave j*wave j).
      { repeat apply Rmult_le_pos; left; apply NSFA20_WAVE_POS. }
      pose proof (Rmult_le_compat_l (wave j*wave j*wave j) _ _ Hw Hyoung) as HM.
      nra. }
  pose proof (NSFA01_TOTAL_LE _ _ J (fun j _ => Hpt j)) as Hsum.
  pose proof (NSFA03_TOTAL_LINEAR d (previous d) (5/2) (3/2) J) as Hlin.
  assert (Hs : total (previous d) J <= total d J).
  { apply NSFA06_PREVIOUS_SUM. intros j Hj; unfold d.
    assert (Hw : 0 <= wave j*wave j*wave j).
    { repeat apply Rmult_le_pos; left; apply NSFA20_WAVE_POS. }
    pose proof (Rle_0_sqr (U j)) as Hsq. unfold Rsqr in Hsq.
    pose proof (Rmult_le_compat_l (wave j*wave j*wave j) _ _ Hw Hsq); nra. }
  change (total (fun j => wave j*wave j*wave j*adjacent U j) J <= 4*total d J).
  nra.
Qed.

Theorem NSSO40_FINITE_64_36_MAJORANT : forall A U r J,
  0 <= r -> (forall j, 0 <= U j) ->
  triad_majorant A U J <= 64*r*shell_D U J+36*shell_L A r J*shell_E U J.
Proof.
  intros A U r J Hr HU.
  set (H := fun j => wave j*adjacent U j).
  set (V := fun j => wave j*wave j*wave j*adjacent U j).
  assert (Hpt : forall h, (h < J)%nat ->
    H h*low_prefix A h <= (4/3)*r*V h+shell_L A r J*H h).
  { intros h Hh.
    pose proof (NSSO30_LOW_PREFIX_BOUND A r J h Hr Hh) as Hlow.
    assert (HH : 0 <= H h).
    { unfold H; apply Rmult_le_pos.
      - left; apply NSFA20_WAVE_POS.
      - apply NSSO31_ADJACENT_NONNEG; exact HU. }
    pose proof (Rmult_le_compat_l (H h) _ _ HH Hlow) as HM.
    unfold H, V in *; nra. }
  pose proof (NSFA01_TOTAL_LE _ _ J Hpt) as Hsum.
  pose proof (NSFA03_TOTAL_LINEAR V H ((4/3)*r) (shell_L A r J) J) as Hlin.
  pose proof (NSSO32_ADJACENT_ENERGY U J) as HE.
  pose proof (NSSO33_ADJACENT_DISSIPATION U J) as HD.
  assert (HL : 0 <= shell_L A r J).
  { unfold shell_L; apply NSFA02_TOTAL_NONNEG; intros; apply NSSO00_COST_NONNEG. }
  assert (HDm : (4/3)*r*total V J <= (4/3)*r*(4*shell_D U J)).
  { apply Rmult_le_compat_l; [lra|exact HD]. }
  assert (HEm : shell_L A r J*total H J <= shell_L A r J*(3*shell_E U J)).
  { apply Rmult_le_compat_l; assumption. }
  unfold triad_majorant. change
    (12*total (fun h => H h*low_prefix A h) J <=
     64*r*shell_D U J+36*shell_L A r J*shell_E U J).
  nra.
Qed.

Theorem NSSO41_ACTUAL_FLUX_SEAM_TO_64_36 : forall phi A U r J E D,
  0 <= r -> (forall j, 0 <= U j) ->
  shell_E U J <= E -> shell_D U J <= D ->
  Rabs phi <= triad_majorant A U J ->
  Rabs phi <= 64*r*D+36*shell_L A r J*E.
Proof.
  intros phi A U r J E D Hr HU HE HD HF.
  pose proof (NSSO40_FINITE_64_36_MAJORANT A U r J Hr HU) as H.
  assert (HL : 0 <= shell_L A r J).
  { unfold shell_L; apply NSFA02_TOTAL_NONNEG; intros; apply NSSO00_COST_NONNEG. }
  pose proof (Rmult_le_compat_l (64*r) _ _ ltac:(lra) HD).
  pose proof (Rmult_le_compat_l (36*shell_L A r J) _ _ ltac:(nra) HE).
  lra.
Qed.

Theorem NSSO50_VISCOSITY_ABSORPTION : forall nu E D L phi E_dot,
  0 < nu -> 0 <= D ->
  E_dot/2+nu*D=phi ->
  Rabs phi <= 64*(nu/128)*D+36*L*E ->
  E_dot+nu*D <= 72*L*E.
Proof.
  intros. pose proof (Rle_abs phi) as Hphi. nra.
Qed.

Theorem NSSO51_CLASSIFIED_DIFFERENTIAL_INEQUALITY :
  forall nu cap E D G L V phi E_dot,
  0 < nu -> 0 <= E -> 0 <= D ->
  E_dot/2+nu*D=phi ->
  Rabs phi <= 64*(nu/128)*D+36*L*E ->
  4*(nu/128)*L <= cap*G+4*(nu/128)*V ->
  E_dot+nu*D <= ((2304*cap/nu)*G+72*V)*E.
Proof.
  intros nu cap E D G L V phi E_dot Hnu HE HD Hbal Hflux Hsplit.
  pose proof (NSSO50_VISCOSITY_ABSORPTION nu E D L phi E_dot Hnu HD Hbal Hflux) as Habs.
  assert (Hscale : nu*((2304*cap/nu)*G+72*V)=2304*cap*G+72*nu*V).
  { field; repeat split; lra. }
  assert (Hpaid : nu*(72*L) <= 2304*cap*G+72*nu*V) by nra.
  pose proof (Rmult_le_compat_l E _ _ HE Hpaid) as HM.
  pose proof (Rmult_le_compat_l nu _ _ (Rlt_le _ _ Hnu) Habs) as HA.
  assert (Heq : nu*(((2304*cap/nu)*G+72*V)*E)=
     (2304*cap*G+72*nu*V)*E).
  { rewrite <- Hscale; ring. }
  nra.
Qed.

End NSE_SHELL_OCCUPANCY_ALGEBRA.
