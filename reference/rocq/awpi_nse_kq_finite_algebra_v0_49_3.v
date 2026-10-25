From Stdlib Require Import Reals Lra Psatz Field Lia.

Module NSE_KQ_FINITE_ALGEBRA.
Open Scope R_scope.

(* Concrete finite real coordinates.  Values past n are deliberately ignored.
   No functional extensionality, positivity axiom, or Cauchy axiom is used. *)
Definition Vec := nat -> R.
Fixpoint sum (n : nat) (f : nat -> R) : R :=
  match n with O => 0 | S k => sum k f + f k end.
Definition dot (n : nat) (x y : Vec) := sum n (fun i => x i * y i).
Definition norm2 (n : nat) (x : Vec) := dot n x x.
Definition add (x y : Vec) : Vec := fun i => x i + y i.
Definition scale (a : R) (x : Vec) : Vec := fun i => a * x i.
Definition sub (x y : Vec) : Vec := fun i => x i - y i.
Definition mul (x y : Vec) : Vec := fun i => x i * y i.

Lemma sum_ext : forall n f g,
  (forall i, (i < n)%nat -> f i = g i) -> sum n f = sum n g.
Proof.
  induction n as [|n IH]; intros f g H; simpl.
  - reflexivity.
  - rewrite (IH f g); [rewrite H; [reflexivity | lia] | intros; apply H; lia].
Qed.

Lemma sum_nonneg : forall n f,
  (forall i, (i < n)%nat -> 0 <= f i) -> 0 <= sum n f.
Proof.
  induction n as [|n IH]; intros f H; simpl.
  - lra.
  - assert (Hn : 0 <= f n) by (apply H; lia).
    assert (Hp : 0 <= sum n f) by (apply IH; intros; apply H; lia).
    lra.
Qed.

Lemma sum_add : forall n f g,
  sum n (fun i => f i + g i) = sum n f + sum n g.
Proof. induction n; intros; simpl; [ring | rewrite IHn; ring]. Qed.
Lemma sum_sub : forall n f g,
  sum n (fun i => f i - g i) = sum n f - sum n g.
Proof. induction n; intros; simpl; [ring | rewrite IHn; ring]. Qed.
Lemma sum_scale : forall n a f,
  sum n (fun i => a * f i) = a * sum n f.
Proof. induction n; intros; simpl; [ring | rewrite IHn; ring]. Qed.

Lemma sum_mono : forall n f g,
  (forall i, (i < n)%nat -> f i <= g i) -> sum n f <= sum n g.
Proof.
  induction n as [|n IH]; intros f g H; simpl; [lra |].
  assert (Hn : f n <= g n) by (apply H; lia).
  assert (Hp : sum n f <= sum n g) by (apply IH; intros; apply H; lia).
  lra.
Qed.

Lemma sum_telescoping : forall n e,
  sum n (fun i => e (S i) - e i) = e n - e O.
Proof. induction n; intros; simpl; [ring | rewrite IHn; ring]. Qed.

Lemma dot_sym : forall n x y, dot n x y = dot n y x.
Proof. intros; unfold dot; apply sum_ext; intros; ring. Qed.
Lemma dot_ext_l : forall n x x' y,
  (forall i, (i < n)%nat -> x i = x' i) -> dot n x y = dot n x' y.
Proof. intros; unfold dot; apply sum_ext; intros; rewrite H by assumption; reflexivity. Qed.
Lemma dot_ext_r : forall n x y y',
  (forall i, (i < n)%nat -> y i = y' i) -> dot n x y = dot n x y'.
Proof. intros; unfold dot; apply sum_ext; intros; rewrite H by assumption; reflexivity. Qed.
Lemma norm2_ext : forall n x y,
  (forall i, (i < n)%nat -> x i = y i) -> norm2 n x = norm2 n y.
Proof. intros; unfold norm2; rewrite (dot_ext_l n x y x H); apply dot_ext_r; exact H. Qed.

Lemma dot_add_l : forall n x y z,
  dot n (add x y) z = dot n x z + dot n y z.
Proof.
  intros; unfold dot, add.
  transitivity (sum n (fun i => x i * z i + y i * z i)).
  - apply sum_ext; intros; ring.
  - apply sum_add.
Qed.
Lemma dot_add_r : forall n x y z,
  dot n x (add y z) = dot n x y + dot n x z.
Proof. intros; rewrite dot_sym, dot_add_l; rewrite (dot_sym n y x), (dot_sym n z x); reflexivity. Qed.
Lemma dot_scale_l : forall n a x y,
  dot n (scale a x) y = a * dot n x y.
Proof.
  intros; unfold dot, scale.
  transitivity (sum n (fun i => a * (x i * y i))).
  - apply sum_ext; intros; ring.
  - apply sum_scale.
Qed.
Lemma dot_scale_r : forall n a x y,
  dot n x (scale a y) = a * dot n x y.
Proof. intros; rewrite dot_sym, dot_scale_l, (dot_sym n y x); reflexivity. Qed.
Lemma dot_sub_l : forall n x y z,
  dot n (sub x y) z = dot n x z - dot n y z.
Proof.
  intros; unfold dot, sub.
  transitivity (sum n (fun i => x i * z i - y i * z i)).
  - apply sum_ext; intros; ring.
  - apply sum_sub.
Qed.
Lemma dot_sub_r : forall n x y z,
  dot n x (sub y z) = dot n x y - dot n x z.
Proof. intros; rewrite dot_sym, dot_sub_l; rewrite (dot_sym n y x), (dot_sym n z x); reflexivity. Qed.
Lemma norm2_nonneg : forall n x, 0 <= norm2 n x.
Proof. intros; unfold norm2, dot; apply sum_nonneg; intros; nra. Qed.
Lemma norm2_sub_scale : forall n x y a,
  norm2 n (sub x (scale a y)) =
  norm2 n x - 2*a*dot n x y + a*a*norm2 n y.
Proof.
  intros; unfold norm2.
  rewrite dot_sub_l, !dot_sub_r, !dot_scale_l, !dot_scale_r.
  rewrite (dot_sym n y x); ring.
Qed.
Lemma norm2_add : forall n x y,
  norm2 n (add x y) = norm2 n x + 2*dot n x y + norm2 n y.
Proof.
  intros; unfold norm2; rewrite dot_add_l, !dot_add_r.
  rewrite (dot_sym n y x); ring.
Qed.

(* Elementary discriminant lemma, including the zero-capacity case. *)
Lemma quadratic_cauchy : forall A B C : R,
  0 <= A -> 0 <= B ->
  (forall t : R, 0 <= A - 2*t*C + t*t*B) -> C*C <= A*B.
Proof.
  intros A B C HA HB Hquad.
  destruct (Req_dec B 0) as [HB0 | HB0].
  - subst B.
    destruct (Req_dec C 0) as [HC | HC]; [subst C; nra |].
    pose proof (Hquad ((A+1)/(2*C))) as Htest.
    assert (Hid : 2*((A+1)/(2*C))*C = A+1).
    { field; nra. }
    nra.
  - assert (HBpos : 0 < B) by lra.
    pose proof (Hquad (C/B)) as Htest.
    assert (Hid : B*(A-2*(C/B)*C+(C/B)*(C/B)*B) = A*B-C*C).
    { field; nra. }
    pose proof (Rmult_le_pos B (A-2*(C/B)*C+(C/B)*(C/B)*B) HB Htest) as Hp.
    rewrite Hid in Hp; nra.
Qed.

Lemma cauchy_quadratic : forall A B C : R,
  0 <= A -> 0 <= B -> C*C <= A*B ->
  forall t : R, 0 <= A - 2*t*C + t*t*B.
Proof.
  intros A B C HA HB HC t.
  destruct (Req_dec B 0) as [HB0 | HB0].
  - subst B; assert (C=0) by nra; subst C; nra.
  - assert (HBpos : 0 < B) by lra.
    (* Supply the composite square explicitly: nra need not discover it.
       The remaining step is an exact sum-of-squares identity. *)
    assert (Hsq : 0 <= (t*B-C)*(t*B-C)).
    { exact (Rle_0_sqr (t*B-C)). }
    assert (Hp : 0 <= B*(A-2*t*C+t*t*B)).
    { replace (B*(A-2*t*C+t*t*B)) with
        ((A*B-C*C)+(t*B-C)*(t*B-C)) by ring.
      lra. }
    apply (Rmult_le_reg_l B); [exact HBpos |].
    rewrite Rmult_0_r; exact Hp.
Qed.

Theorem NSKA10_FINITE_CAUCHY : forall n x y,
  dot n x y * dot n x y <= norm2 n x * norm2 n y.
Proof.
  intros n x y; apply quadratic_cauchy.
  - apply norm2_nonneg.
  - apply norm2_nonneg.
  - intro t; rewrite <- norm2_sub_scale; apply norm2_nonneg.
Qed.

Lemma norm2_zero_dot : forall n x y,
  norm2 n y = 0 -> dot n x y = 0.
Proof. intros; pose proof (NSKA10_FINITE_CAUCHY n x y); rewrite H in H0; nra. Qed.

Lemma sum_weighted_quadratic : forall n w q z r t,
  sum n (fun i => w i*(q i-2*t*r i+t*t*z i)) =
  sum n (fun i => w i*q i) - 2*t*sum n (fun i => w i*r i) +
  t*t*sum n (fun i => w i*z i).
Proof. induction n; intros; simpl; [ring | rewrite IHn; ring]. Qed.

Theorem NSKA20_WEIGHTED_CAUCHY : forall n w q z r,
  (forall i, (i<n)%nat -> 0 <= w i) ->
  (forall i, (i<n)%nat -> 0 <= q i) ->
  (forall i, (i<n)%nat -> 0 <= z i) ->
  (forall i, (i<n)%nat -> r i*r i <= q i*z i) ->
  let Q := sum n (fun i => w i*q i) in
  let Z := sum n (fun i => w i*z i) in
  let Rr := sum n (fun i => w i*r i) in
  Rr*Rr <= Q*Z.
Proof.
  intros n w q z r Hw Hq Hz Hr; cbv zeta; apply quadratic_cauchy.
  - apply sum_nonneg; intros; apply Rmult_le_pos; auto.
  - apply sum_nonneg; intros; apply Rmult_le_pos; auto.
  - intro t.
    assert (Hpos : 0 <= sum n (fun i => w i*(q i-2*t*r i+t*t*z i))).
    { apply sum_nonneg; intros i Hi; apply Rmult_le_pos; [auto |].
      apply cauchy_quadratic; auto. }
    assert (Hid : sum n (fun i => w i*(q i-2*t*r i+t*t*z i)) =
      sum n (fun i => w i*q i) - 2*t*sum n (fun i => w i*r i) +
      t*t*sum n (fun i => w i*z i)).
    { apply sum_weighted_quadratic. }
    rewrite Hid in Hpos; exact Hpos.
Qed.

End NSE_KQ_FINITE_ALGEBRA.
