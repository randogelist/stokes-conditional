From Stdlib Require Import Reals Lra Psatz Lia.

Module NSE_FINITE_SHELL_ALGEBRA.
Open Scope R_scope.

(* Finite sums are exclusive: indices 0,...,N-1. *)
Fixpoint total (f : nat -> R) (N : nat) : R :=
  match N with O => 0 | S n => total f n + f n end.

Lemma NSFA00_TOTAL_EXT : forall f g N,
  (forall j, (j < N)%nat -> f j = g j) -> total f N = total g N.
Proof.
  intros f g N. induction N as [|N IH]; intro H; simpl.
  - reflexivity.
  - rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma NSFA01_TOTAL_LE : forall f g N,
  (forall j, (j < N)%nat -> f j <= g j) -> total f N <= total g N.
Proof.
  intros f g N. induction N as [|N IH]; intro H; simpl.
  - lra.
  - assert (HI : total f N <= total g N).
    { apply IH. intros; apply H; lia. }
    specialize (H N ltac:(lia)). lra.
Qed.

Lemma NSFA02_TOTAL_NONNEG : forall f N,
  (forall j, (j < N)%nat -> 0 <= f j) -> 0 <= total f N.
Proof.
  intros f N. induction N as [|N IH]; intro H; simpl.
  - lra.
  - assert (HI : 0 <= total f N).
    { apply IH. intros; apply H; lia. }
    specialize (H N ltac:(lia)). lra.
Qed.

Lemma NSFA03_TOTAL_LINEAR : forall f g a b N,
  total (fun j => a * f j + b * g j) N =
  a * total f N + b * total g N.
Proof. intros f g a b N. induction N; simpl; [ring|rewrite IHN; ring]. Qed.

Lemma NSFA03B_TOTAL_AFFINE : forall f g a N,
  total (fun j => a*f j+g j) N = a*total f N+total g N.
Proof. intros f g a N. induction N; simpl; [ring|rewrite IHN; ring]. Qed.

Lemma NSFA04_TOTAL_SCALE : forall f a N,
  total (fun j => a * f j) N = a * total f N.
Proof. intros f a N. induction N; simpl; [ring|rewrite IHN; ring]. Qed.

Lemma NSFA05_TOTAL_PREFIX : forall f m n,
  (m <= n)%nat ->
  (forall j, (j < n)%nat -> 0 <= f j) -> total f m <= total f n.
Proof.
  intros f m n Hmn. induction Hmn as [|n Hmn IH]; intro H.
  - lra.
  - simpl. assert (HI : total f m <= total f n).
    { apply IH. intros; apply H; lia. }
    specialize (H n ltac:(lia)). lra.
Qed.

Definition previous (f : nat -> R) (j : nat) : R :=
  match j with O => 0 | S i => f i end.

Lemma NSFA06_PREVIOUS_SUM : forall f N,
  (forall j, (j < N)%nat -> 0 <= f j) ->
  total (previous f) N <= total f N.
Proof.
  intros f N. destruct N as [|N]; intro H; [simpl; lra|].
  assert (Heq : forall k, total (previous f) (S k) = total f k).
  { intro k. induction k as [|k IH].
    - change (0+0=0); ring.
    - change (total (previous f) (S k)+f k=total f k+f k).
      rewrite IH; reflexivity. }
  rewrite Heq. simpl. specialize (H N ltac:(lia)). lra.
Qed.

Lemma NSFA07_TOTAL_ZERO : forall N, total (fun _ => 0) N=0.
Proof. induction N; simpl; lra. Qed.

Lemma NSFA08_DIV_NONNEG : forall a b,
  0 <= a -> 0 < b -> 0 <= a/b.
Proof.
  intros a b Ha Hb. unfold Rdiv. apply Rmult_le_pos.
  - exact Ha.
  - left; apply Rinv_0_lt_compat; exact Hb.
Qed.

Definition pos (x : R) : R := Rmax 0 x.
Lemma NSFA10_POS_NONNEG : forall x, 0 <= pos x.
Proof. intro x; unfold pos; apply Rmax_l. Qed.
Lemma NSFA11_POS_ABOVE : forall x, x <= pos x.
Proof. intro x; unfold pos; apply Rmax_r. Qed.
Lemma NSFA12_POS_ZERO : forall x, x <= 0 -> pos x = 0.
Proof.
  intros x H. apply Rle_antisym.
  - unfold pos; apply Rmax_lub; lra.
  - apply NSFA10_POS_NONNEG.
Qed.
Lemma NSFA13_POS_ID : forall x, 0 <= x -> pos x = x.
Proof.
  intros x H. apply Rle_antisym.
  - unfold pos; apply Rmax_lub; lra.
  - apply NSFA11_POS_ABOVE.
Qed.
Lemma NSFA14_POS_MONO : forall x y, x <= y -> pos x <= pos y.
Proof.
  intros x y H. unfold pos at 1. apply Rmax_lub.
  - apply NSFA10_POS_NONNEG.
  - pose proof (NSFA11_POS_ABOVE y); lra.
Qed.
Lemma NSFA15_POS_UPPER : forall x z,
  0 <= z -> x <= z -> pos x <= z.
Proof. intros; unfold pos; apply Rmax_lub; assumption. Qed.

Lemma NSFA16_QUADRATIC_CLIP : forall y r,
  0 <= r -> 4*r*pos (y-r) <= y*y.
Proof.
  intros y r Hr. destruct (Rle_dec y r) as [H|H].
  - rewrite NSFA12_POS_ZERO by lra.
    pose proof (Rle_0_sqr y). unfold Rsqr in *; nra.
  - rewrite NSFA13_POS_ID by lra.
    pose proof (Rle_0_sqr (y-2*r)). unfold Rsqr in *; nra.
Qed.

Lemma NSFA17_MINIMAL_UNPAID : forall cost paid,
  cost <= paid + pos (cost-paid).
Proof. intros; pose proof (NSFA11_POS_ABOVE (cost-paid)); lra. Qed.

Lemma NSFA18_RESISTANT_SQUARE : forall phi nu theta d,
  0 <= nu -> 0 <= theta -> 0 <= d ->
  pos (phi-theta*nu*d)*pos (phi-theta*nu*d) <= phi*phi.
Proof.
  intros phi nu theta d Hnu Hth Hd.
  assert (Ht : 0 <= theta*nu) by (apply Rmult_le_pos; assumption).
  assert (Hsub : 0 <= theta*nu*d) by (apply Rmult_le_pos; assumption).
  destruct (Rle_dec phi (theta*nu*d)) as [H|H].
  - rewrite NSFA12_POS_ZERO by lra.
    pose proof (Rle_0_sqr phi); unfold Rsqr in *; nra.
  - rewrite NSFA13_POS_ID by lra. nra.
Qed.

Fixpoint wave (j : nat) : R :=
  match j with O => 1 | S i => 2 * wave i end.
Lemma NSFA20_WAVE_POS : forall j, 0 < wave j.
Proof. induction j; simpl; lra. Qed.
Lemma NSFA21_WAVE_GE_ONE : forall j, 1 <= wave j.
Proof. induction j; simpl; lra. Qed.

Lemma NSFA22_DYADIC_SQUARE_PREFIX : forall h,
  3*total (fun j => wave j * wave j) (S h) <= 4*wave h*wave h.
Proof.
  induction h as [|h IH].
  - simpl; lra.
  - change (3*(total (fun j => wave j*wave j) (S h) +
                (2*wave h)*(2*wave h)) <= 4*(2*wave h)*(2*wave h)).
    nra.
Qed.

(* Real scalar polarization identity. The identification of these
   contractions with actual complex Fourier coefficients is a separate
   analytic/algebraic binding, not asserted by this lemma. *)
Lemma NSFA30_SIGNED_SYMMETRIZATION :
  forall ap aq bp bq ck cp ab bc ca rk rp rq,
    aq = -ap -> bp = -bq -> cp = -ck ->
    ap*bc*rq + aq*bc*rp + bq*ca*rk + bp*ca*rq +
    ck*ab*rp + cp*ab*rk =
    ap*bc*(rq-rp) + bq*ca*(rk-rq) + ck*ab*(rp-rk).
Proof. intros; subst; ring. Qed.

Lemma NSFA31_AFFINE_HELICAL_DETECTOR : forall a b z1 z2 z3,
  (a+b*z1)*(z2-z3)+(a+b*z2)*(z3-z1)+(a+b*z3)*(z1-z2)=0.
Proof. intros; ring. Qed.

Lemma NSFA32_TRIAD_HALF_FACTOR : forall t1 t2 t3 L,
  Rabs t1 <= L -> Rabs t2 <= L -> Rabs t3 <= L ->
  Rabs ((t1+t2+t3)/6) <= L/2.
Proof.
  intros t1 t2 t3 L H1 H2 H3.
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
  rewrite (Rabs_right 6) by lra.
  pose proof (Rabs_triang (t1+t2) t3) as Hsum.
  pose proof (Rabs_triang t1 t2) as Hpair. lra.
Qed.

(* Earlier two-annihilator GP factorization, retained as exact algebra. *)
Lemma NSFA40_HELICAL_RESIDUAL_FACTOR : forall Ep Em Gp Gm Dp Dm,
  let E := Ep+Em in let G := Gp+Gm in let D := Dp+Dm in
  let K := Gp-Gm in let L := Dp-Dm in
  D*(E*D-K*K)-D*G*G+2*K*G*L-E*L*L =
  4*(Dm*(Ep*Dp-Gp*Gp)+Dp*(Em*Dm-Gm*Gm)).
Proof.
  (* Introduce only the six quantified reals. Keep E,G,D,K,L as
     let-in expressions so zeta reduction expands them in the goal. *)
  intros Ep Em Gp Gm Dp Dm.
  cbv zeta.
  ring.
Qed.

Lemma NSFA41_PENALIZED_GRAM_DETERMINANT : forall E D K delta,
  0 <= E -> 0 <= D -> K*K <= E*D -> 0 < delta ->
  0 < (E+delta)*(D+delta)-K*K.
Proof. intros; nra. Qed.

End NSE_FINITE_SHELL_ALGEBRA.
