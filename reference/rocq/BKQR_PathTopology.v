(* Countable weak topology built from explicit finite sums.  Pairings exist
   and are unique by proved countable-energy convergence and polarization.
   Shell pairings have both diagonal and independent-rectangle convergence.
   Relative time continuity uses actual epsilon-delta definitions.  This
   file does not assert a physical Fourier realization or an NSE equation. *)
From Stdlib Require Import Reals Lra Psatz Lia Field Classical Arith.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_StrongSynthesis.

Module BKQR_PATH_TOPOLOGY.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_STRONG_SYNTHESIS.
Open Scope R_scope.

Definition pairing_prefix (v w : nat -> R) (N : nat) : R :=
  gp_sum N (fun i => v i * w i).
Definition PairingLimit (v w : nat -> R) (p : R) : Prop :=
  SeqLimit (pairing_prefix v w) p.

Lemma gp_sum_plus : forall N f g,
  gp_sum N (fun i => f i + g i) = gp_sum N f + gp_sum N g.
Proof. induction N; intros; simpl; [ring|rewrite IHN; ring]. Qed.

Lemma finite_square_linear : forall v w N a b,
  physical_prefix (fun i => a*v i+b*w i) N =
  a*a*physical_prefix v N + 2*a*b*pairing_prefix v w N +
  b*b*physical_prefix w N.
Proof.
  intros v w N a b. unfold physical_prefix, pairing_prefix.
  induction N as [|N IH]; simpl; [ring|]. rewrite IH. ring.
Qed.

Lemma physical_prefix_nonneg : forall v N, 0 <= physical_prefix v N.
Proof. intros; apply gp_sum_nonneg. intro i. nra. Qed.

Lemma physical_bound_nonneg : forall v E, PhysicalBound v E -> 0 <= E.
Proof. intros v E H. exact (H O). Qed.

Lemma finite_pairing_cauchy_schwarz : forall v w N,
  pairing_prefix v w N * pairing_prefix v w N <=
  physical_prefix v N * physical_prefix w N.
Proof.
  intros v w N.
  set (A := physical_prefix v N).
  set (B := physical_prefix w N).
  set (P := pairing_prefix v w N).
  assert (HA : 0 <= A) by apply physical_prefix_nonneg.
  assert (HB : 0 <= B) by apply physical_prefix_nonneg.
  assert (Hquad : forall a b,
    0 <= a*a*A + 2*a*b*P + b*b*B).
  { intros a b. unfold A, B, P. rewrite <- finite_square_linear.
    apply physical_prefix_nonneg. }
  destruct (Req_dec B 0) as [HB0|HB0].
  - specialize (Hquad (2*P) (-(A+1))). rewrite HB0 in Hquad.
    assert (HP : P*P = 0) by nra. rewrite HB0, HP. lra.
  - assert (HBpos : 0 < B) by lra.
    specialize (Hquad B (-P)).
    assert (Hprod : 0 <= B*(A*B-P*P)) by nra.
    destruct (Rle_dec (P*P) (A*B)); [assumption|].
    assert (Hneg : B*(A*B-P*P) < 0).
    { apply Rmult_pos_neg; lra. } lra.
Qed.

Lemma physical_total_limit : forall v M,
  PhysicalTotal v M -> SeqLimit (physical_prefix v) M.
Proof.
  intros v M HM eps Heps.
  destruct (total_has_close_prefix v M HM eps Heps) as [J HJ].
  exists J. intros N HJN.
  assert (Hmono : physical_prefix v J <= physical_prefix v N).
  { apply gp_sum_prefix_le; [intro i; nra|exact HJN]. }
  pose proof (proj1 HM N) as Hbound.
  apply Rabs_def1; lra.
Qed.

Lemma physical_sum_summable : forall v w,
  PhysicalSquareSummable v -> PhysicalSquareSummable w ->
  PhysicalSquareSummable (fun i => v i+w i).
Proof.
  intros v w [E HE] [F HF]. exists (2*(E+F)). intro N.
  assert (Hpoint : physical_prefix (fun i => v i+w i) N <=
    2*(physical_prefix v N+physical_prefix w N)).
  { unfold physical_prefix. rewrite <- gp_sum_plus, <- gp_sum_scale.
    apply gp_sum_le. intros i Hi. pose proof (Rle_0_sqr (v i-w i)).
    unfold Rsqr in *. nra. }
  specialize (HE N). specialize (HF N). lra.
Qed.

Lemma seq_limit_unique : forall f a b,
  SeqLimit f a -> SeqLimit f b -> a=b.
Proof.
  intros f a b Ha Hb.
  destruct (Rtotal_order a b) as [Hab|[Hab|Hab]]; [|exact Hab|].
  - destruct (Ha ((b-a)/3)) as [N HN]; [lra|].
    destruct (Hb ((b-a)/3)) as [M HM]; [lra|].
    specialize (HN (Nat.max N M) (Nat.le_max_l _ _)).
    specialize (HM (Nat.max N M) (Nat.le_max_r _ _)).
    apply Rabs_def2 in HN. apply Rabs_def2 in HM.
    destruct HN; destruct HM. lra.
  - destruct (Ha ((a-b)/3)) as [N HN]; [lra|].
    destruct (Hb ((a-b)/3)) as [M HM]; [lra|].
    specialize (HN (Nat.max N M) (Nat.le_max_l _ _)).
    specialize (HM (Nat.max N M) (Nat.le_max_r _ _)).
    apply Rabs_def2 in HN. apply Rabs_def2 in HM.
    destruct HN; destruct HM. lra.
Qed.

Lemma pairing_limit_exists : forall v w,
  PhysicalSquareSummable v -> PhysicalSquareSummable w ->
  exists p, PairingLimit v w p.
Proof.
  intros v w Hv Hw.
  destruct (physical_total_exists v Hv) as [A HA].
  destruct (physical_total_exists w Hw) as [B HB].
  destruct (physical_total_exists (fun i => v i+w i)
    (physical_sum_summable v w Hv Hw)) as [C HC].
  exists ((C-A-B)/2). unfold PairingLimit.
  assert (Hlim : SeqLimit
    (fun N => /2*(physical_prefix (fun i=>v i+w i) N +
      (-1)*physical_prefix v N + (-1)*physical_prefix w N))
    (/2*(C+(-1)*A+(-1)*B))).
  { apply limit_scale. apply limit_plus; [apply limit_plus|].
    - apply physical_total_limit. exact HC.
    - apply limit_scale. apply physical_total_limit. exact HA.
    - apply limit_scale. apply physical_total_limit. exact HB. }
  replace ((C-A-B)/2) with (/2*(C+(-1)*A+(-1)*B)) by field.
  eapply limit_ext; [|exact Hlim]. intro N.
  pose proof (finite_square_linear v w N 1 1) as Hpol.
  assert (Heq : physical_prefix (fun i => v i+w i) N =
    physical_prefix (fun i=>1*v i+1*w i) N).
  { unfold physical_prefix. apply gp_sum_ext. intros i Hi. ring. }
  cbn beta. rewrite Heq, Hpol. field.
Qed.

Lemma pairing_limit_unique : forall v w p q,
  PairingLimit v w p -> PairingLimit v w q -> p=q.
Proof. intros. eapply seq_limit_unique; eassumption. Qed.

Lemma limit_square : forall f l,
  SeqLimit f l -> SeqLimit (fun n => f n*f n) (l*l).
Proof.
  intros f l H.
  pose proof (limit_difference_zero f l H) as Hz.
  pose proof (limit_square_zero _ Hz) as Hzz.
  pose proof (limit_scale _ 0 (2*l) Hz) as Hlin.
  pose proof (limit_plus _ _ 0 (2*l*0) Hzz Hlin) as Hsum.
  pose proof (limit_plus _ _ (0+2*l*0) (l*l) Hsum
    (limit_const (l*l))) as Hall.
  replace (0+2*l*0+l*l) with (l*l) in Hall by ring.
  eapply limit_ext; [|exact Hall]. intro n. cbn beta. ring.
Qed.

Lemma pairing_limit_bound : forall v w E F p,
  PhysicalBound v E -> PhysicalBound w F -> PairingLimit v w p ->
  p*p <= E*F.
Proof.
  intros v w E F p HE HF Hp.
  apply (limit_upper_bound (fun N=>pairing_prefix v w N *
    pairing_prefix v w N) (p*p) (E*F)).
  - apply limit_square. exact Hp.
  - intro N. eapply Rle_trans; [apply finite_pairing_cauchy_schwarz|].
    apply Rmult_le_compat; try apply physical_prefix_nonneg;
      [apply HE|apply HF].
Qed.

Definition shift (J : nat) (v : nat -> R) (i : nat) := v (J+i)%nat.

Lemma gp_sum_append : forall J N f,
  gp_sum (J+N) f = gp_sum J f + gp_sum N (shift J f).
Proof.
  intros J N f. induction N as [|N IH].
  - rewrite Nat.add_0_r. simpl. ring.
  - rewrite Nat.add_succ_r. simpl. rewrite IH. unfold shift. ring.
Qed.

Lemma physical_prefix_shift : forall v J N,
  physical_prefix (shift J v) N =
    physical_prefix v (J+N)%nat - physical_prefix v J.
Proof.
  intros. unfold physical_prefix. rewrite gp_sum_append.
  unfold shift. ring.
Qed.

Lemma pairing_prefix_shift : forall v w J N,
  pairing_prefix (shift J v) (shift J w) N =
    pairing_prefix v w (J+N)%nat - pairing_prefix v w J.
Proof.
  intros. unfold pairing_prefix. rewrite gp_sum_append.
  unfold shift. ring.
Qed.

Lemma pairing_shift_limit : forall v w J p,
  PairingLimit v w p ->
  PairingLimit (shift J v) (shift J w) (p-pairing_prefix v w J).
Proof.
  intros v w J p H eps Heps.
  destruct (H eps Heps) as [N HN]. exists N. intros n Hn.
  unfold pairing_prefix at 1.
  change (Rabs (pairing_prefix (shift J v) (shift J w) n -
    (p-pairing_prefix v w J)) < eps).
  rewrite pairing_prefix_shift.
  replace (pairing_prefix v w (J+n)%nat -pairing_prefix v w J -
    (p-pairing_prefix v w J)) with
    (pairing_prefix v w (J+n)%nat-p) by ring.
  apply HN. lia.
Qed.

Lemma physical_shift_bound : forall v E J,
  PhysicalBound v E ->
  PhysicalBound (shift J v) (E-physical_prefix v J).
Proof.
  intros v E J H N. rewrite physical_prefix_shift.
  specialize (H (J+N)%nat). lra.
Qed.

Lemma pairing_tail_bound : forall v w E M J p,
  PhysicalBound v E -> PhysicalTotal w M -> PairingLimit v w p ->
  (p-pairing_prefix v w J)*(p-pairing_prefix v w J) <=
    E*(M-physical_prefix w J).
Proof.
  intros v w E M J p HE HM Hp.
  apply pairing_limit_bound with (v:=shift J v) (w:=shift J w).
  - intro N. rewrite physical_prefix_shift.
    pose proof (physical_prefix_nonneg v J).
    specialize (HE (J+N)%nat). lra.
  - apply physical_shift_bound. exact (proj1 HM).
  - apply pairing_shift_limit. exact Hp.
Qed.

Lemma pairing_uniform_tail : forall w E,
  PhysicalSquareSummable w -> 0 <= E -> forall eps, 0 < eps ->
  exists J, forall x p, PhysicalBound x E -> PairingLimit x w p ->
    Rabs (p-pairing_prefix x w J) < eps.
Proof.
  intros w E Hw HE eps Heps.
  destruct (physical_total_exists w Hw) as [M HM].
  assert (Hd : 0 < eps*eps/(E+1)).
  { apply Rdiv_lt_0_compat; nra. }
  destruct (total_has_close_prefix w M HM (eps*eps/(E+1)) Hd)
    as [J HJ]. exists J. intros x p Hx Hp.
  pose proof (pairing_tail_bound x w E M J p Hx HM Hp) as Htail.
  pose proof (proj1 HM J) as HJupper.
  assert (Heq : (E+1)*(eps*eps/(E+1)) = eps*eps).
  { field. lra. }
  pose proof (Rmult_le_compat_l E (M-physical_prefix w J)
    (eps*eps/(E+1)) HE (Rlt_le _ _ HJ)) as Hmul.
  assert (Hsmall : E*(M-physical_prefix w J) < eps*eps) by nra.
  pose proof (Rsqr_abs (p-pairing_prefix x w J)) as Habs.
  unfold Rsqr in Habs.
  pose proof (Rabs_pos (p-pairing_prefix x w J)). nra.
Qed.

Print Assumptions finite_pairing_cauchy_schwarz.
Print Assumptions pairing_limit_exists.
Print Assumptions pairing_uniform_tail.

Definition shell_pairing_rectangle (U V : nat -> nat -> R) (K N : nat) : R :=
  gp_sum N (fun i => gp_sum K (fun k => U k i * V k i)).
Definition ShellPairingLimit (U V : nat -> nat -> R) (p : R) : Prop :=
  SeqLimit (fun J => shell_pairing_rectangle U V J J) p.

Lemma shell_rectangle_nonneg : forall U K N, 0 <= shell_rectangle U K N.
Proof.
  intros. unfold shell_rectangle. apply gp_sum_nonneg. intro i.
  apply gp_sum_nonneg. intro k. nra.
Qed.

Lemma shell_rectangle_mono : forall U K N L M,
  (K <= L)%nat -> (N <= M)%nat ->
  shell_rectangle U K N <= shell_rectangle U L M.
Proof.
  intros U K N L M HK HN. unfold shell_rectangle.
  eapply Rle_trans with
    (r2 := gp_sum N (fun i => gp_sum L (fun k => U k i * U k i))).
  - apply gp_sum_le. intros i Hi. apply gp_sum_prefix_le.
    + intro k. nra.
    + exact HK.
  - apply gp_sum_prefix_le.
    + intro i. apply gp_sum_nonneg. intro k. nra.
    + exact HN.
Qed.

Lemma shell_total_has_close_rectangle : forall U M,
  ShellTotal U M -> forall eps, 0 < eps ->
  exists K N, M - shell_rectangle U K N < eps.
Proof.
  intros U M [Hupper Hleast] eps Heps.
  destruct (classic (exists K N, M-shell_rectangle U K N < eps))
    as [Hex|Hnone]; [exact Hex|].
  assert (Hsmaller : ShellBound U (M-eps)).
  { intros K N.
    destruct (Rle_dec (shell_rectangle U K N) (M-eps)); [assumption|].
    exfalso. apply Hnone. exists K, N. lra. }
  specialize (Hleast (M-eps) Hsmaller). lra.
Qed.

Lemma shell_total_diagonal_limit : forall U M,
  ShellTotal U M -> SeqLimit (fun J => shell_rectangle U J J) M.
Proof.
  intros U M HM eps Heps.
  destruct (shell_total_has_close_rectangle U M HM eps Heps)
    as [K [N Hclose]].
  exists (Nat.max K N). intros J HJ.
  assert (Hmono : shell_rectangle U K N <= shell_rectangle U J J).
  { apply shell_rectangle_mono; lia. }
  pose proof (proj1 HM J J) as Hupper.
  apply Rabs_def1; lra.
Qed.

Lemma diagonal_limit_shell_total : forall U M,
  SeqLimit (fun J => shell_rectangle U J J) M -> ShellTotal U M.
Proof.
  intros U M Hlim. split.
  - intros K N. eapply Rle_trans with
      (r2 := shell_rectangle U (Nat.max K N) (Nat.max K N)).
    + apply shell_rectangle_mono; lia.
    + apply (monotone_limit_upper (fun J => shell_rectangle U J J) M).
      * intros m n Hmn. apply shell_rectangle_mono; assumption.
      * exact Hlim.
  - intros E HE. apply (limit_upper_bound
      (fun J => shell_rectangle U J J) M E Hlim).
    intro J. apply HE.
Qed.

Lemma encoded_diagonal_energy_limit : forall psi v M,
  ScalarPartition psi -> PhysicalTotal v M ->
  SeqLimit (fun J => shell_rectangle (gp_encode psi v) J J) M.
Proof.
  intros psi v M Hpsi HM. apply shell_total_diagonal_limit.
  apply (proj1 (GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY
    psi v (gp_encode psi v) Hpsi (fun k i => eq_refl) M)). exact HM.
Qed.

Lemma shell_pairing_polarization : forall U V K N,
  2 * shell_pairing_rectangle U V K N =
  shell_rectangle (fun k i => U k i + V k i) K N -
  shell_rectangle U K N - shell_rectangle V K N.
Proof.
  intros U V K N. unfold shell_pairing_rectangle, shell_rectangle.
  assert (Hinner : forall i,
    2 * gp_sum K (fun k => U k i * V k i) =
    gp_sum K (fun k => (U k i+V k i)*(U k i+V k i)) -
    gp_sum K (fun k => U k i*U k i) -
    gp_sum K (fun k => V k i*V k i)).
  { intro i. induction K as [|K IH]; simpl; [ring|]. nra. }
  induction N as [|N IH]; simpl; [ring|].
  specialize (Hinner N). lra.
Qed.

Lemma encoded_shell_pairing_polarization : forall psi v w K N,
  2 * shell_pairing_rectangle (gp_encode psi v) (gp_encode psi w) K N =
  shell_rectangle (gp_encode psi (fun i => v i+w i)) K N -
  shell_rectangle (gp_encode psi v) K N -
  shell_rectangle (gp_encode psi w) K N.
Proof.
  intros. rewrite shell_pairing_polarization.
  rewrite (shell_rectangle_ext
    (fun k i => gp_encode psi v k i+gp_encode psi w k i)
    (gp_encode psi (fun i => v i+w i))).
  - reflexivity.
  - intros. unfold gp_encode. ring.
Qed.

Lemma shell_pairing_rectangle_ext : forall U V U' V',
  (forall k i, U k i = U' k i) ->
  (forall k i, V k i = V' k i) ->
  forall K N, shell_pairing_rectangle U V K N =
    shell_pairing_rectangle U' V' K N.
Proof.
  intros U V U' V' HU HV K N. unfold shell_pairing_rectangle.
  apply gp_sum_ext. intros i Hi. apply gp_sum_ext. intros k Hk.
  rewrite HU, HV. reflexivity.
Qed.

Lemma shell_pairing_limit_ext : forall U V U' V' p,
  (forall k i, U k i = U' k i) ->
  (forall k i, V k i = V' k i) ->
  ShellPairingLimit U V p -> ShellPairingLimit U' V' p.
Proof.
  intros U V U' V' p HU HV Hlim. unfold ShellPairingLimit in *.
  eapply limit_ext; [|exact Hlim]. intro J.
  apply shell_pairing_rectangle_ext; assumption.
Qed.

Lemma shell_pairing_limit_unique : forall U V p q,
  ShellPairingLimit U V p -> ShellPairingLimit U V q -> p=q.
Proof. intros. eapply seq_limit_unique; eassumption. Qed.

Theorem encoded_shell_pairing_limit : forall psi v w p,
  ScalarPartition psi ->
  PhysicalSquareSummable v -> PhysicalSquareSummable w ->
  PairingLimit v w p ->
  ShellPairingLimit (gp_encode psi v) (gp_encode psi w) p.
Proof.
  intros psi v w p Hpsi Hv Hw Hp.
  destruct (physical_total_exists v Hv) as [A HA].
  destruct (physical_total_exists w Hw) as [B HB].
  destruct (physical_total_exists (fun i => v i+w i)
    (physical_sum_summable v w Hv Hw)) as [C HC].
  assert (Hphysical : PairingLimit v w (/2*(C+(-1)*A+(-1)*B))).
  { unfold PairingLimit.
    assert (Hlim : SeqLimit
      (fun N => /2*(physical_prefix (fun i=>v i+w i) N +
        (-1)*physical_prefix v N + (-1)*physical_prefix w N))
      (/2*(C+(-1)*A+(-1)*B))).
    { apply limit_scale. apply limit_plus; [apply limit_plus|].
      - apply physical_total_limit. exact HC.
      - apply limit_scale. apply physical_total_limit. exact HA.
      - apply limit_scale. apply physical_total_limit. exact HB. }
    eapply limit_ext; [|exact Hlim]. intro N.
    pose proof (finite_square_linear v w N 1 1) as Hpol.
    assert (Heq : physical_prefix (fun i => v i+w i) N =
      physical_prefix (fun i=>1*v i+1*w i) N).
    { unfold physical_prefix. apply gp_sum_ext. intros i Hi. ring. }
    cbn beta. rewrite Heq, Hpol. field. }
  assert (Heq : p = /2*(C+(-1)*A+(-1)*B)).
  { eapply pairing_limit_unique; eassumption. }
  rewrite Heq. unfold ShellPairingLimit.
  assert (Hlim : SeqLimit
    (fun J => /2*(shell_rectangle
        (gp_encode psi (fun i=>v i+w i)) J J +
      (-1)*shell_rectangle (gp_encode psi v) J J +
      (-1)*shell_rectangle (gp_encode psi w) J J))
    (/2*(C+(-1)*A+(-1)*B))).
  { apply limit_scale. apply limit_plus; [apply limit_plus|].
    - apply encoded_diagonal_energy_limit; assumption.
    - apply limit_scale. apply encoded_diagonal_energy_limit; assumption.
    - apply limit_scale. apply encoded_diagonal_energy_limit; assumption. }
  eapply limit_ext; [|exact Hlim]. intro J.
  cbn beta. pose proof (encoded_shell_pairing_polarization psi v w J J). lra.
Qed.

Theorem encoded_shell_pairing_iff : forall psi v w p,
  ScalarPartition psi ->
  PhysicalSquareSummable v -> PhysicalSquareSummable w ->
  (PairingLimit v w p <->
    ShellPairingLimit (gp_encode psi v) (gp_encode psi w) p).
Proof.
  intros psi v w p Hpsi Hv Hw. split.
  - apply encoded_shell_pairing_limit; assumption.
  - intro Hshell. destruct (pairing_limit_exists v w Hv Hw) as [q Hq].
    assert (Hencoded : ShellPairingLimit
      (gp_encode psi v) (gp_encode psi w) q).
    { apply encoded_shell_pairing_limit; assumption. }
    assert (Heq : p=q) by (eapply shell_pairing_limit_unique; eassumption).
    rewrite Heq. exact Hq.
Qed.

(* Independent cutoffs give the same pairing; the diagonal definition above
   is a cofinal presentation of this genuine rectangular sum. *)
Definition RectangularShellPairingLimit (U V : nat -> nat -> R) (p : R) : Prop :=
  forall eps, 0 < eps -> exists J, forall K N,
    (J <= K)%nat -> (J <= N)%nat ->
    Rabs (shell_pairing_rectangle U V K N-p) < eps.

Lemma shell_total_rectangle_limit : forall U M,
  ShellTotal U M -> forall eps, 0 < eps -> exists J, forall K N,
    (J <= K)%nat -> (J <= N)%nat ->
    Rabs (shell_rectangle U K N-M) < eps.
Proof.
  intros U M HM eps Heps.
  destruct (shell_total_has_close_rectangle U M HM eps Heps)
    as [K0 [N0 Hclose]].
  exists (Nat.max K0 N0). intros K N HK HN.
  assert (Hmono : shell_rectangle U K0 N0 <= shell_rectangle U K N).
  { apply shell_rectangle_mono; lia. }
  pose proof (proj1 HM K N). apply Rabs_def1; lra.
Qed.

Theorem encoded_shell_pairing_rectangular_limit : forall psi v w p,
  ScalarPartition psi ->
  PhysicalSquareSummable v -> PhysicalSquareSummable w ->
  PairingLimit v w p ->
  RectangularShellPairingLimit (gp_encode psi v) (gp_encode psi w) p.
Proof.
  intros psi v w p Hpsi Hv Hw Hp.
  destruct (GPR80_SHARED_TOTAL_ENERGY_EXISTS psi v (gp_encode psi v)
    Hpsi (fun k i=>eq_refl) Hv) as [A [HA HSA]].
  destruct (GPR80_SHARED_TOTAL_ENERGY_EXISTS psi w (gp_encode psi w)
    Hpsi (fun k i=>eq_refl) Hw) as [B [HB HSB]].
  destruct (GPR80_SHARED_TOTAL_ENERGY_EXISTS psi (fun i=>v i+w i)
    (gp_encode psi (fun i=>v i+w i)) Hpsi (fun k i=>eq_refl)
    (physical_sum_summable v w Hv Hw)) as [C [HC HSC]].
  assert (Hpolar : ShellPairingLimit (gp_encode psi v)
      (gp_encode psi w) (/2*(C+(-1)*A+(-1)*B))).
  { unfold ShellPairingLimit.
    assert (Hlim : SeqLimit
      (fun J => /2*(shell_rectangle
          (gp_encode psi (fun i=>v i+w i)) J J +
        (-1)*shell_rectangle (gp_encode psi v) J J +
        (-1)*shell_rectangle (gp_encode psi w) J J))
      (/2*(C+(-1)*A+(-1)*B))).
    { apply limit_scale. apply limit_plus; [apply limit_plus|].
      - apply shell_total_diagonal_limit. exact HSC.
      - apply limit_scale. apply shell_total_diagonal_limit. exact HSA.
      - apply limit_scale. apply shell_total_diagonal_limit. exact HSB. }
    eapply limit_ext; [|exact Hlim]. intro J. cbn beta.
    pose proof (encoded_shell_pairing_polarization psi v w J J). lra. }
  assert (Heq : p=/2*(C+(-1)*A+(-1)*B)).
  { eapply shell_pairing_limit_unique; [|exact Hpolar].
    apply encoded_shell_pairing_limit; assumption. }
  assert (Hvalue : 2*p=C-A-B) by (rewrite Heq; field).
  intros eps Heps.
  destruct (shell_total_rectangle_limit _ A HSA (eps/2))
    as [JA HJA]; [lra|].
  destruct (shell_total_rectangle_limit _ B HSB (eps/2))
    as [JB HJB]; [lra|].
  destruct (shell_total_rectangle_limit _ C HSC (eps/2))
    as [JC HJC]; [lra|].
  exists (Nat.max JA (Nat.max JB JC)). intros K N HK HN.
  assert (HKA : (JA <= K)%nat) by lia.
  assert (HNA : (JA <= N)%nat) by lia.
  assert (HKB : (JB <= K)%nat) by lia.
  assert (HNB : (JB <= N)%nat) by lia.
  assert (HKC : (JC <= K)%nat) by lia.
  assert (HNC : (JC <= N)%nat) by lia.
  specialize (HJA K N HKA HNA). specialize (HJB K N HKB HNB).
  specialize (HJC K N HKC HNC).
  apply Rabs_def2 in HJA. apply Rabs_def2 in HJB. apply Rabs_def2 in HJC.
  destruct HJA; destruct HJB; destruct HJC.
  pose proof (encoded_shell_pairing_polarization psi v w K N).
  apply Rabs_def1; lra.
Qed.

Print Assumptions encoded_shell_pairing_rectangular_limit.
Print Assumptions encoded_shell_pairing_limit.
Print Assumptions encoded_shell_pairing_iff.

Definition coordinate_test (j i : nat) : R :=
  if Nat.eq_dec i j then 1 else 0.

Lemma coordinate_pairing_prefix : forall x j N,
  pairing_prefix x (coordinate_test j) N =
  if lt_dec j N then x j else 0.
Proof.
  intros x j N. unfold pairing_prefix. induction N as [|N IH].
  - simpl. destruct (lt_dec j O); [lia|reflexivity].
  - change (gp_sum N (fun i => x i * coordinate_test j i) +
      x N * coordinate_test j N = if lt_dec j (S N) then x j else 0).
    rewrite IH. unfold coordinate_test at 1.
    destruct (Nat.eq_dec N j) as [Heq|Hneq].
    + subst N. destruct (lt_dec j j); [lia|].
      destruct (lt_dec j (S j)); [ring|lia].
    + destruct (lt_dec j N); destruct (lt_dec j (S N));
        try lia; ring.
Qed.

Lemma coordinate_test_square_summable : forall j,
  PhysicalSquareSummable (coordinate_test j).
Proof.
  intro j. exists 1. intro N.
  change (pairing_prefix (coordinate_test j) (coordinate_test j) N <= 1).
  rewrite coordinate_pairing_prefix.
  destruct (lt_dec j N); [unfold coordinate_test; destruct (Nat.eq_dec j j)|];
    try contradiction; lra.
Qed.

Lemma coordinate_pairing : forall x j,
  PairingLimit x (coordinate_test j) (x j).
Proof.
  intros x j eps Heps. exists (S j). intros N HN.
  rewrite coordinate_pairing_prefix.
  destruct (lt_dec j N); [|lia].
  replace (x j-x j) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

Definition WeakSeqLimit (X : nat -> nat -> R) (v : nat -> R) : Prop :=
  forall w, PhysicalSquareSummable w ->
  forall p, PairingLimit v w p ->
  forall eps, 0 < eps -> exists n0 : nat,
  forall n, (n0 <= n)%nat -> forall pn,
  PairingLimit (X n) w pn -> Rabs (pn-p) < eps.

Lemma finite_pairing_coordinate_limit : forall X v w,
  (forall i, SeqLimit (fun n => X n i) (v i)) -> forall J,
  SeqLimit (fun n => pairing_prefix (X n) w J) (pairing_prefix v w J).
Proof.
  intros X v w H J. unfold pairing_prefix. apply limit_gp_sum. intro i.
  eapply limit_ext with (f := fun n => w i * X n i).
  - intro n. ring.
  - replace (v i*w i) with (w i*v i) by ring. apply limit_scale. apply H.
Qed.

Lemma physical_bound_nonnegative : forall v E, PhysicalBound v E -> 0 <= E.
Proof. intros v E H. exact (H O). Qed.

Theorem BKPT10_BOUNDED_WEAK_SEQUENCE_IFF_COORDINATES : forall X v E,
  PhysicalBound v E -> (forall n, PhysicalBound (X n) E) ->
  (WeakSeqLimit X v <-> forall i, SeqLimit (fun n => X n i) (v i)).
Proof.
  intros X v E Hv HX. split.
  - intros H i eps Heps.
    destruct (H (coordinate_test i) (coordinate_test_square_summable i)
      (v i) (coordinate_pairing v i) eps Heps) as [n0 Hn0].
    exists n0. intros n Hn.
    exact (Hn0 n Hn (X n i) (coordinate_pairing (X n) i)).
  - intros Hcoord w Hw p Hp eps Heps.
    pose proof (physical_bound_nonnegative v E Hv) as HE.
    destruct (pairing_uniform_tail w E Hw HE (eps/3)) as [J Htail]; [lra|].
    destruct (finite_pairing_coordinate_limit X v w Hcoord J (eps/3))
      as [n0 Hn0]; [lra|].
    exists n0. intros n Hn pn Hpn. specialize (Hn0 n Hn).
    pose proof (Htail (X n) pn (HX n) Hpn) as Htailn.
    pose proof (Htail v p Hv Hp) as Htailv.
    apply Rabs_def2 in Hn0. apply Rabs_def2 in Htailn.
    apply Rabs_def2 in Htailv. destruct Hn0; destruct Htailn;
      destruct Htailv. apply Rabs_def1; lra.
Qed.

Definition ScalarContinuousOn (D : R -> Prop) (f : R -> R) : Prop :=
  forall t, D t -> forall eps, 0 < eps -> exists delta,
  0 < delta /\ forall s, D s -> Rabs (s-t) < delta -> Rabs (f s-f t) < eps.

Definition CoordinateContinuousOn (D : R -> Prop) (u : R -> nat -> R) : Prop :=
  forall i, ScalarContinuousOn D (fun t => u t i).

Definition WeakContinuousOn (D : R -> Prop) (u : R -> nat -> R) : Prop :=
  forall w, PhysicalSquareSummable w ->
  forall t, D t -> forall pt, PairingLimit (u t) w pt ->
  forall eps, 0 < eps -> exists delta,
  0 < delta /\ forall s, D s -> Rabs (s-t) < delta ->
  forall ps, PairingLimit (u s) w ps -> Rabs (ps-pt) < eps.

Lemma ordinary_continuity_implies_relative : forall D f,
  (forall t, D t -> continuity_pt f t) -> ScalarContinuousOn D f.
Proof.
  intros D f H t Dt eps Heps.
  specialize (H t Dt).
  unfold continuity_pt, continue_in, limit1_in, limit_in in H.
  destruct (H eps Heps) as [delta [Hdelta Hnear]].
  exists delta. split; [exact Hdelta|]. intros s Ds Hs.
  destruct (Req_dec t s) as [Heq|Hneq].
  - subst s. replace (f t-f t) with 0 by ring. rewrite Rabs_R0. exact Heps.
  - apply Hnear. split; [split; [exact I|exact Hneq]|exact Hs].
Qed.

Lemma scalar_continuous_const : forall D c,
  ScalarContinuousOn D (fun _ => c).
Proof.
  intros D c t Dt eps Heps. exists 1. split; [lra|].
  intros. replace (c-c) with 0 by ring. rewrite Rabs_R0. exact Heps.
Qed.

Lemma scalar_continuous_plus : forall D f g,
  ScalarContinuousOn D f -> ScalarContinuousOn D g ->
  ScalarContinuousOn D (fun t => f t+g t).
Proof.
  intros D f g Hf Hg t Dt eps Heps.
  destruct (Hf t Dt (eps/2)) as [df [Hdf Hfnear]]; [lra|].
  destruct (Hg t Dt (eps/2)) as [dg [Hdg Hgnear]]; [lra|].
  exists (Rmin df dg). split.
  - apply Rmin_Rgt_r. split; assumption.
  - intros s Ds Hs.
    assert (Hsf : Rabs(s-t)<df) by (pose proof (Rmin_l df dg); lra).
    assert (Hsg : Rabs(s-t)<dg) by (pose proof (Rmin_r df dg); lra).
    specialize (Hfnear s Ds Hsf). specialize (Hgnear s Ds Hsg).
    apply Rabs_def2 in Hfnear. apply Rabs_def2 in Hgnear.
    destruct Hfnear; destruct Hgnear. apply Rabs_def1; lra.
Qed.

Lemma scalar_continuous_scale : forall D f c,
  ScalarContinuousOn D f -> ScalarContinuousOn D (fun t => f t*c).
Proof.
  intros D f c H t Dt eps Heps.
  pose proof (Rabs_pos c) as Hc.
  assert (Hden : 0 < Rabs c+1) by lra.
  assert (Hd : 0 < eps/(Rabs c+1)) by (apply Rdiv_lt_0_compat; assumption).
  destruct (H t Dt (eps/(Rabs c+1)) Hd) as [delta [Hdelta Hnear]].
  exists delta. split; [exact Hdelta|]. intros s Ds Hs.
  specialize (Hnear s Ds Hs).
  replace (f s*c-f t*c) with (c*(f s-f t)) by ring. rewrite Rabs_mult.
  assert (Heq : (Rabs c+1)*(eps/(Rabs c+1))=eps) by (field; lra).
  pose proof (Rabs_pos (f s-f t)). nra.
Qed.

Lemma scalar_continuous_sum : forall D (f : R -> nat -> R),
  (forall i, ScalarContinuousOn D (fun t => f t i)) -> forall J,
  ScalarContinuousOn D (fun t => gp_sum J (f t)).
Proof.
  intros D f H J. induction J as [|J IH]; simpl.
  - apply scalar_continuous_const.
  - apply scalar_continuous_plus; [exact IH|apply H].
Qed.

Lemma finite_pairing_coordinate_continuous : forall D u w,
  CoordinateContinuousOn D u -> forall J,
  ScalarContinuousOn D (fun t => pairing_prefix (u t) w J).
Proof.
  intros D u w H J. unfold pairing_prefix. apply scalar_continuous_sum.
  intro i. apply scalar_continuous_scale. apply H.
Qed.

Theorem BKPT20_BOUNDED_WEAK_CONTINUITY_IFF_COORDINATES : forall D u E,
  (forall t, D t -> PhysicalBound (u t) E) ->
  (WeakContinuousOn D u <-> CoordinateContinuousOn D u).
Proof.
  intros D u E Hbound. split.
  - intros H i t Dt eps Heps.
    destruct (H (coordinate_test i) (coordinate_test_square_summable i)
      t Dt (u t i) (coordinate_pairing (u t) i) eps Heps)
      as [delta [Hdelta Hnear]].
    exists delta. split; [exact Hdelta|].
    intros s Ds Hs.
    exact (Hnear s Ds Hs (u s i) (coordinate_pairing (u s) i)).
  - intros Hcoord w Hw t Dt pt Hpt eps Heps.
    pose proof (physical_bound_nonnegative (u t) E (Hbound t Dt)) as HE.
    destruct (pairing_uniform_tail w E Hw HE (eps/3)) as [J Htail]; [lra|].
    destruct (finite_pairing_coordinate_continuous D u w Hcoord J t Dt (eps/3))
      as [delta [Hdelta Hnear]]; [lra|].
    exists delta. split; [exact Hdelta|]. intros s Ds Hs ps Hps.
    specialize (Hnear s Ds Hs).
    pose proof (Htail (u s) ps (Hbound s Ds) Hps) as Htails.
    pose proof (Htail (u t) pt (Hbound t Dt) Hpt) as Htailt.
    apply Rabs_def2 in Hnear. apply Rabs_def2 in Htails.
    apply Rabs_def2 in Htailt. destruct Hnear; destruct Htails;
      destruct Htailt. apply Rabs_def1; lra.
Qed.

Lemma scalar_continuity_gives_sequence_limit : forall D f t ts,
  ScalarContinuousOn D f -> D t -> (forall n, D (ts n)) ->
  SeqLimit ts t -> SeqLimit (fun n => f (ts n)) (f t).
Proof.
  intros D f t ts H Dt Dts Hts eps Heps.
  destruct (H t Dt eps Heps) as [delta [Hdelta Hnear]].
  destruct (Hts delta Hdelta) as [n0 Hn0]. exists n0. intros n Hn.
  apply Hnear; [apply Dts|apply Hn0; exact Hn].
Qed.

Corollary BKPT21_WEAK_CONTINUITY_GIVES_WEAK_TRACE : forall D u E t ts,
  (forall s, D s -> PhysicalBound (u s) E) ->
  WeakContinuousOn D u -> D t -> (forall n, D (ts n)) ->
  SeqLimit ts t -> WeakSeqLimit (fun n => u (ts n)) (u t).
Proof.
  intros D u E t ts Hbound Hweak Dt Dts Hts.
  apply (proj2 (BKPT10_BOUNDED_WEAK_SEQUENCE_IFF_COORDINATES
    (fun n => u (ts n)) (u t) E (Hbound t Dt) (fun n => Hbound (ts n) (Dts n)))).
  intro i. apply (scalar_continuity_gives_sequence_limit
    D (fun r => u r i) t ts); try assumption.
  apply (proj1 (BKPT20_BOUNDED_WEAK_CONTINUITY_IFF_COORDINATES D u E Hbound)).
  exact Hweak.
Qed.

Lemma intrinsic_reconstruction_summable : forall psi lambda ell U,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  IntrinsicState lambda ell U -> PhysicalSquareSummable (reconstruct psi U).
Proof.
  intros psi lambda ell U Hp Hr H0 He [HU [E HE]]. exists E.
  apply (proj2 (BKSC10_RECONSTRUCTION_PRESERVES_ALL_BOUNDS
    psi lambda ell U Hp Hr H0 He HU E)). exact HE.
Qed.

Lemma factorable_pairing_iff : forall psi u v U V p,
  ScalarPartition psi -> PhysicalSquareSummable u -> PhysicalSquareSummable v ->
  (forall k i, U k i = gp_encode psi u k i) ->
  (forall k i, V k i = gp_encode psi v k i) ->
  (PairingLimit u v p <-> ShellPairingLimit U V p).
Proof.
  intros psi u v U V p Hp Hu Hv Hfu Hfv. split.
  - intro Hpair. apply (shell_pairing_limit_ext
      (gp_encode psi u) (gp_encode psi v) U V p).
    + intros k i. symmetry. apply Hfu.
    + intros k i. symmetry. apply Hfv.
    + apply encoded_shell_pairing_limit; assumption.
  - intro Hpair. apply (proj2 (encoded_shell_pairing_iff psi u v p Hp Hu Hv)).
    apply (shell_pairing_limit_ext U V (gp_encode psi u) (gp_encode psi v) p);
      assumption.
Qed.

Theorem BKPT30_INTRINSIC_PAIRING_IS_PHYSICAL_PAIRING : forall psi lambda ell U V p,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  IntrinsicState lambda ell U -> IntrinsicState lambda ell V ->
  (PairingLimit (reconstruct psi U) (reconstruct psi V) p <->
    ShellPairingLimit U V p).
Proof.
  intros psi lambda ell U V p Hp Hr H0 He HU HV.
  apply factorable_pairing_iff with (psi := psi); [exact Hp| | | |].
  - apply intrinsic_reconstruction_summable with (lambda:=lambda) (ell:=ell);
      assumption.
  - apply intrinsic_reconstruction_summable with (lambda:=lambda) (ell:=ell);
      assumption.
  - apply BKSC03_ADJACENCY_FORCES_FACTORIZATION with (lambda:=lambda) (ell:=ell);
      try assumption. exact (proj1 HU).
  - apply BKSC03_ADJACENCY_FORCES_FACTORIZATION with (lambda:=lambda) (ell:=ell);
      try assumption. exact (proj1 HV).
Qed.

(* Tests range over the intrinsic Hilbert subspace.  Their scalar products
   are limits of actual signed shell sums, proved equal to physical pairings. *)
Definition ShellWeakSeqLimit (lambda ell : nat -> R)
  (X : nat -> nat -> nat -> R) (U : nat -> nat -> R) : Prop :=
  forall V, IntrinsicState lambda ell V ->
  forall p, ShellPairingLimit U V p -> forall eps, 0 < eps ->
  exists n0 : nat, forall n, (n0 <= n)%nat -> forall pn,
  ShellPairingLimit (X n) V pn -> Rabs (pn-p) < eps.

Theorem BKPT31_WEAK_SEQUENCE_TRANSPORT : forall psi lambda ell X U,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  IntrinsicState lambda ell U -> (forall n, IntrinsicState lambda ell (X n)) ->
  (ShellWeakSeqLimit lambda ell X U <->
    WeakSeqLimit (fun n => reconstruct psi (X n)) (reconstruct psi U)).
Proof.
  intros psi lambda ell X U Hp Hr H0 He HU HX.
  assert (Hfactor : forall V, IntrinsicState lambda ell V ->
    forall k i, V k i = gp_encode psi (reconstruct psi V) k i).
  { intros V HV. apply BKSC03_ADJACENCY_FORCES_FACTORIZATION
      with (lambda:=lambda) (ell:=ell); try assumption. exact (proj1 HV). }
  assert (Hsumm : forall V, IntrinsicState lambda ell V ->
      PhysicalSquareSummable (reconstruct psi V)).
  { intros V HV. apply intrinsic_reconstruction_summable
      with (lambda:=lambda) (ell:=ell); assumption. }
  split.
  - intros Hshell w Hw p Hpair eps Heps.
    assert (HwI : IntrinsicState lambda ell (gp_encode psi w)).
    { apply (proj2 (BKSC11_EXACT_INTRINSIC_RANGE psi lambda ell Hp Hr H0 He
        (gp_encode psi w))). exists w. split; [exact Hw|intros; reflexivity]. }
    assert (Hshellp : ShellPairingLimit U (gp_encode psi w) p).
    { apply (proj1 (factorable_pairing_iff psi (reconstruct psi U) w
        U (gp_encode psi w) p Hp (Hsumm U HU) Hw (Hfactor U HU)
        (fun k i => eq_refl))). exact Hpair. }
    destruct (Hshell (gp_encode psi w) HwI p Hshellp eps Heps) as [n0 Hn0].
    exists n0. intros n Hn pn Hpn. apply (Hn0 n Hn pn).
    apply (proj1 (factorable_pairing_iff psi (reconstruct psi (X n)) w
      (X n) (gp_encode psi w) pn Hp (Hsumm (X n) (HX n)) Hw
      (Hfactor (X n) (HX n)) (fun k i => eq_refl))). exact Hpn.
  - intros Hphysical V HV p Hpair eps Heps.
    assert (Hphysicalp : PairingLimit (reconstruct psi U) (reconstruct psi V) p).
    { apply (proj2 (BKPT30_INTRINSIC_PAIRING_IS_PHYSICAL_PAIRING
        psi lambda ell U V p Hp Hr H0 He HU HV)). exact Hpair. }
    destruct (Hphysical (reconstruct psi V) (Hsumm V HV) p Hphysicalp eps Heps)
      as [n0 Hn0]. exists n0. intros n Hn pn Hpn.
    apply (Hn0 n Hn pn).
    apply (proj2 (BKPT30_INTRINSIC_PAIRING_IS_PHYSICAL_PAIRING
      psi lambda ell (X n) V pn Hp Hr H0 He (HX n) HV)). exact Hpn.
Qed.

Definition ShellWeakContinuousOn (D : R -> Prop) (lambda ell : nat -> R)
  (U : R -> nat -> nat -> R) : Prop :=
  forall V, IntrinsicState lambda ell V -> forall t, D t ->
  forall pt, ShellPairingLimit (U t) V pt -> forall eps, 0 < eps ->
  exists delta, 0 < delta /\ forall s, D s -> Rabs (s-t) < delta ->
  forall ps, ShellPairingLimit (U s) V ps -> Rabs (ps-pt) < eps.

Theorem BKPT32_WEAK_CONTINUITY_TRANSPORT : forall psi lambda ell D U,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  (forall t, D t -> IntrinsicState lambda ell (U t)) ->
  (ShellWeakContinuousOn D lambda ell U <->
    WeakContinuousOn D (fun t => reconstruct psi (U t))).
Proof.
  intros psi lambda ell D U Hp Hr H0 He HU.
  assert (Hfactor : forall V, IntrinsicState lambda ell V ->
    forall k i, V k i = gp_encode psi (reconstruct psi V) k i).
  { intros V HV. apply BKSC03_ADJACENCY_FORCES_FACTORIZATION
      with (lambda:=lambda) (ell:=ell); try assumption. exact (proj1 HV). }
  assert (Hsumm : forall V, IntrinsicState lambda ell V ->
      PhysicalSquareSummable (reconstruct psi V)).
  { intros V HV. apply intrinsic_reconstruction_summable
      with (lambda:=lambda) (ell:=ell); assumption. }
  split.
  - intros Hshell w Hw t Dt pt Hpt eps Heps.
    assert (HwI : IntrinsicState lambda ell (gp_encode psi w)).
    { apply (proj2 (BKSC11_EXACT_INTRINSIC_RANGE psi lambda ell Hp Hr H0 He
        (gp_encode psi w))). exists w. split; [exact Hw|intros; reflexivity]. }
    assert (Hshellp : ShellPairingLimit (U t) (gp_encode psi w) pt).
    { apply (proj1 (factorable_pairing_iff psi (reconstruct psi (U t)) w
        (U t) (gp_encode psi w) pt Hp (Hsumm (U t) (HU t Dt)) Hw
        (Hfactor (U t) (HU t Dt)) (fun k i => eq_refl))). exact Hpt. }
    destruct (Hshell (gp_encode psi w) HwI t Dt pt Hshellp eps Heps)
      as [delta [Hdelta Hnear]]. exists delta. split; [exact Hdelta|].
    intros s Ds Hs ps Hps. apply (Hnear s Ds Hs ps).
    apply (proj1 (factorable_pairing_iff psi (reconstruct psi (U s)) w
      (U s) (gp_encode psi w) ps Hp (Hsumm (U s) (HU s Ds)) Hw
      (Hfactor (U s) (HU s Ds)) (fun k i => eq_refl))). exact Hps.
  - intros Hphysical V HV t Dt pt Hpt eps Heps.
    assert (Hphysicalp : PairingLimit
      (reconstruct psi (U t)) (reconstruct psi V) pt).
    { apply (proj2 (BKPT30_INTRINSIC_PAIRING_IS_PHYSICAL_PAIRING
        psi lambda ell (U t) V pt Hp Hr H0 He (HU t Dt) HV)). exact Hpt. }
    destruct (Hphysical (reconstruct psi V) (Hsumm V HV) t Dt pt
      Hphysicalp eps Heps) as [delta [Hdelta Hnear]].
    exists delta. split; [exact Hdelta|]. intros s Ds Hs ps Hps.
    apply (Hnear s Ds Hs ps).
    apply (proj2 (BKPT30_INTRINSIC_PAIRING_IS_PHYSICAL_PAIRING
      psi lambda ell (U s) V ps Hp Hr H0 He (HU s Ds) HV)). exact Hps.
Qed.

Lemma scalar_continuous_ext_on : forall D f g,
  (forall t, D t -> f t = g t) ->
  ScalarContinuousOn D f -> ScalarContinuousOn D g.
Proof.
  intros D f g Hfg Hf t Dt eps Heps.
  destruct (Hf t Dt eps Heps) as [delta [Hdelta Hnear]].
  exists delta. split; [exact Hdelta|]. intros s Ds Hs.
  rewrite <- (Hfg s Ds), <- (Hfg t Dt). apply Hnear; assumption.
Qed.

Definition ShellCoordinateContinuousOn (D : R -> Prop)
  (U : R -> nat -> nat -> R) : Prop :=
  forall k i, ScalarContinuousOn D (fun t => U t k i).

Lemma compatible_coordinate_continuity_iff : forall psi lambda ell D U,
  ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  (forall t, D t -> AdjacentCompatible lambda ell (U t)) ->
  (CoordinateContinuousOn D (fun t => reconstruct psi (U t)) <->
    ShellCoordinateContinuousOn D U).
Proof.
  intros psi lambda ell D U Hr H0 He HU. split.
  - intros H k i.
    apply (scalar_continuous_ext_on D
      (fun t => reconstruct psi (U t) i * psi k i)).
    + intros t Dt.
      rewrite (BKSC03_ADJACENCY_FORCES_FACTORIZATION
        psi lambda ell (U t) Hr H0 He (HU t Dt) k i).
      unfold gp_encode. ring.
    + apply scalar_continuous_scale. apply H.
  - intros H i. unfold reconstruct, Rdiv.
    apply scalar_continuous_scale. apply H.
Qed.

Theorem BKPT33_BOUNDED_NATIVE_WEAK_CONTINUITY_IFF_SHELL_COORDINATES :
  forall psi lambda ell D U E,
  ScalarPartition psi -> ScalarRaising psi lambda ell ->
  (forall i, psi 0%nat i <> 0) -> (forall k, ell k <> 0) ->
  (forall t, D t -> IntrinsicState lambda ell (U t)) ->
  (forall t, D t -> ShellBound (U t) E) ->
  (ShellWeakContinuousOn D lambda ell U <-> ShellCoordinateContinuousOn D U).
Proof.
  intros psi lambda ell D U E Hp Hr H0 He HU Hbound.
  assert (Hphysical : forall t, D t ->
    PhysicalBound (reconstruct psi (U t)) E).
  { intros t Dt. apply (proj2 (BKSC10_RECONSTRUCTION_PRESERVES_ALL_BOUNDS
      psi lambda ell (U t) Hp Hr H0 He (proj1 (HU t Dt)) E)).
    apply Hbound. exact Dt. }
  pose proof (BKPT32_WEAK_CONTINUITY_TRANSPORT
    psi lambda ell D U Hp Hr H0 He HU) as Htransport.
  pose proof (BKPT20_BOUNDED_WEAK_CONTINUITY_IFF_COORDINATES
    D (fun t => reconstruct psi (U t)) E Hphysical) as Hweakcoord.
  pose proof (compatible_coordinate_continuity_iff
    psi lambda ell D U Hr H0 He (fun t Dt => proj1 (HU t Dt))) as Hcoord.
  split; intro H.
  - apply (proj1 Hcoord). apply (proj1 Hweakcoord).
    apply (proj1 Htransport). exact H.
  - apply (proj2 Htransport). apply (proj2 Hweakcoord).
    apply (proj2 Hcoord). exact H.
Qed.

Print Assumptions BKPT10_BOUNDED_WEAK_SEQUENCE_IFF_COORDINATES.
Print Assumptions BKPT20_BOUNDED_WEAK_CONTINUITY_IFF_COORDINATES.
Print Assumptions BKPT21_WEAK_CONTINUITY_GIVES_WEAK_TRACE.
Print Assumptions BKPT30_INTRINSIC_PAIRING_IS_PHYSICAL_PAIRING.
Print Assumptions BKPT31_WEAK_SEQUENCE_TRANSPORT.
Print Assumptions BKPT32_WEAK_CONTINUITY_TRANSPORT.
Print Assumptions BKPT33_BOUNDED_NATIVE_WEAK_CONTINUITY_IFF_SHELL_COORDINATES.
End BKQR_PATH_TOPOLOGY.
