From Stdlib Require Import Reals Lra Psatz Lia.
Require Import LHGP_Coordinates LHGP_Readouts.

Open Scope R_scope.

(* A bounded bilinear realization supplies genuine quadratic convergence.
   All vector operations, bilinearity, and the operator bound are explicit
   hypotheses. No arbitrary coefficient matrix is asserted to converge.
   The physical L2/tensor-integral realization is a separate instantiation. *)

Fixpoint BilinearFinite {H : Type}
  (zero : H) (add : H -> H -> H) (scale : R -> H -> H)
  (e : nat -> H) (a : Seq) (n : nat) : H :=
  match n with
  | O => zero
  | S k => add (BilinearFinite zero add scale e a k) (scale (a k) (e k))
  end.

Lemma nonnegative_square_limit : forall f : Seq,
  (forall n, 0 <= f n) ->
  SeqLimit (fun n => f n * f n) 0 -> SeqLimit f 0.
Proof.
  intros f Hnonneg Hsquare eps Heps.
  assert (Heps2 : 0 < eps * eps) by nra.
  destruct (Hsquare (eps * eps) Heps2) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  destruct (Rabs_def2 _ _ HN) as [Hupper _].
  specialize (Hnonneg n).
  apply Rabs_def1; nra.
Qed.

Section BilinearAlgebra.
  Context {H : Type}.
  Variable zero : H.
  Variable add : H -> H -> H.
  Variable scale : R -> H -> H.
  Variable sub : H -> H -> H.
  Variable norm : H -> R.
  Variable B : H -> H -> R.

  Hypothesis zero_add : forall x, add zero x = x.
  Hypothesis sub_restore : forall x y, add (sub x y) y = x.
  Hypothesis norm_nonnegative : forall x, 0 <= norm x.
  Hypothesis norm_add : forall x y, norm (add x y) <= norm x + norm y.
  Hypothesis B_add_left : forall x y z, B (add x y) z = B x z + B y z.
  Hypothesis B_add_right : forall x y z, B x (add y z) = B x y + B x z.
  Hypothesis B_scale_left : forall c x y, B (scale c x) y = c * B x y.
  Hypothesis B_scale_right : forall c x y, B x (scale c y) = c * B x y.
  Variable C : R.
  Hypothesis C_nonnegative : 0 <= C.
  Hypothesis B_bound : forall x y, Rabs (B x y) <= C * norm x * norm y.

  Definition NormConverges (u : nat -> H) (x : H) : Prop :=
    SeqLimit (fun n => norm (sub (u n) x)) 0.

  Lemma B_zero_left : forall x, B zero x = 0.
  Proof.
    intro x. pose proof (B_add_left zero x x) as Hzero.
    rewrite zero_add in Hzero. lra.
  Qed.

  Lemma B_zero_right : forall x, B x zero = 0.
  Proof.
    intro x. pose proof (B_add_right x zero x) as Hzero.
    rewrite zero_add in Hzero. lra.
  Qed.

  Lemma bilinear_diagonal_difference : forall x y,
    B x x - B y y = B (sub x y) x + B y (sub x y).
  Proof.
    intros x y.
    pose proof (B_add_left (sub x y) y x) as Hleft.
    pose proof (B_add_right y (sub x y) y) as Hright.
    rewrite sub_restore in Hleft, Hright. lra.
  Qed.

  Theorem quadratic_stability_bound : forall x y,
    Rabs (B x x - B y y) <=
    C * (norm x + norm y) * norm (sub x y).
  Proof.
    intros x y. rewrite bilinear_diagonal_difference.
    eapply Rle_trans; [apply Rabs_triang |].
    pose proof (B_bound (sub x y) x) as Hleft.
    pose proof (B_bound y (sub x y)) as Hright.
    nra.
  Qed.

  Lemma norm_difference_control : forall x y,
    norm x <= norm y + norm (sub x y).
  Proof.
    intros x y. pose proof (norm_add (sub x y) y) as Hbound.
    rewrite sub_restore in Hbound. lra.
  Qed.

  Lemma norm_converges_from_square : forall u x,
    SeqLimit (fun n => norm (sub (u n) x) * norm (sub (u n) x)) 0 ->
    NormConverges u x.
  Proof.
    intros u x Hsquare. unfold NormConverges.
    apply nonnegative_square_limit; [intro n; apply norm_nonnegative | exact Hsquare].
  Qed.

  (* This form needs only an eventual norm bound, and therefore does not
     depend on the triangle inequality supplied above. *)
  Theorem quadratic_readout_converges_with_bound : forall u x M N0,
    0 <= M ->
    (forall n, (N0 <= n)%nat -> norm (u n) + norm x <= M) ->
    NormConverges u x ->
    SeqLimit (fun n => B (u n) (u n)) (B x x).
  Proof.
    intros u x M N0 HM Hbound Hconv eps Heps.
    set (K := C * M).
    assert (HK : 0 <= K) by (unfold K; nra).
    assert (HK1 : 0 < K + 1) by lra.
    assert (Hdelta : 0 < eps / (K + 1)).
    { apply Rdiv_lt_0_compat; assumption. }
    destruct (Hconv _ Hdelta) as [N HN].
    exists (Nat.max N0 N). intros n Hn.
    specialize (HN n ltac:(lia)).
    specialize (Hbound n ltac:(lia)).
    destruct (Rabs_def2 _ _ HN) as [Hsmall _].
    pose proof (norm_nonnegative (sub (u n) x)) as Hd.
    assert (Hprod : (K + 1) * norm (sub (u n) x) < eps).
    { assert (Hmul : (K + 1) * norm (sub (u n) x) <
        (K + 1) * (eps / (K + 1))).
      { apply Rmult_lt_compat_l; [exact HK1 | lra]. }
      replace ((K + 1) * (eps / (K + 1))) with eps in Hmul
        by (field; lra).
      exact Hmul. }
    pose proof (quadratic_stability_bound (u n) x) as Hstable.
    assert (Hcap : C * (norm (u n) + norm x) * norm (sub (u n) x)
      <= K * norm (sub (u n) x)).
    { apply Rmult_le_compat_r; [exact Hd |].
      unfold K. apply Rmult_le_compat_l; assumption. }
    eapply Rle_lt_trans; [exact Hstable |].
    eapply Rle_lt_trans; [exact Hcap |].
    nra.
  Qed.

  Theorem quadratic_readout_converges : forall u x,
    NormConverges u x ->
    SeqLimit (fun n => B (u n) (u n)) (B x x).
  Proof.
    intros u x Hconv.
    destruct (Hconv 1 Rlt_0_1) as [N HN].
    eapply quadratic_readout_converges_with_bound
      with (M := 2 * norm x + 1) (N0 := N).
    - pose proof (norm_nonnegative x). lra.
    - intros n Hn. specialize (HN n Hn).
      destruct (Rabs_def2 _ _ HN) as [Hsmall _].
      pose proof (norm_difference_control (u n) x). lra.
    - exact Hconv.
  Qed.

  Theorem quadratic_readout_converges_squared_with_bound : forall u x M N0,
    0 <= M ->
    (forall n, (N0 <= n)%nat -> norm (u n) + norm x <= M) ->
    SeqLimit (fun n => norm (sub (u n) x) * norm (sub (u n) x)) 0 ->
    SeqLimit (fun n => B (u n) (u n)) (B x x).
  Proof.
    intros u x M N0 HM Hbound Hsquare.
    eapply quadratic_readout_converges_with_bound; [exact HM | exact Hbound |].
    apply norm_converges_from_square. exact Hsquare.
  Qed.

  Lemma bilinear_finite_left : forall e a n y,
    B (BilinearFinite zero add scale e a n) y =
    prefix (fun i => a i * B (e i) y) n.
  Proof.
    intros e a n y. induction n as [|n IH]; simpl.
    - apply B_zero_left.
    - rewrite B_add_left, B_scale_left, IH. reflexivity.
  Qed.

  Lemma bilinear_finite_right : forall e a n x,
    B x (BilinearFinite zero add scale e a n) =
    prefix (fun i => a i * B x (e i)) n.
  Proof.
    intros e a n x. induction n as [|n IH]; simpl.
    - apply B_zero_right.
    - rewrite B_add_right, B_scale_right, IH. reflexivity.
  Qed.

  Theorem quadratic_prefix_realization : forall e a n,
    quadratic_prefix a (fun i j => B (e i) (e j)) n =
    B (BilinearFinite zero add scale e a n)
      (BilinearFinite zero add scale e a n).
  Proof.
    intros e a n. symmetry. rewrite bilinear_finite_left.
    unfold quadratic_prefix. apply prefix_ext. intro i.
    rewrite bilinear_finite_right.
    rewrite <- prefix_scale. apply prefix_ext. intro j. ring.
  Qed.

  Theorem quadratic_limit_from_synthesis : forall e a x,
    NormConverges (BilinearFinite zero add scale e a) x ->
    quadratic_limit a (fun i j => B (e i) (e j)) (B x x).
  Proof.
    intros e a x Hconv. unfold quadratic_limit.
    apply (proj2 (SeqLimit_ext
      (quadratic_prefix a (fun i j => B (e i) (e j)))
      (fun n => B (BilinearFinite zero add scale e a n)
                  (BilinearFinite zero add scale e a n))
      (B x x) (fun n => quadratic_prefix_realization e a n))).
    apply quadratic_readout_converges. exact Hconv.
  Qed.

  Theorem quadratic_limit_from_squared_synthesis_bound : forall e a x M N0,
    0 <= M ->
    (forall n, (N0 <= n)%nat ->
      norm (BilinearFinite zero add scale e a n) + norm x <= M) ->
    SeqLimit (fun n =>
      norm (sub (BilinearFinite zero add scale e a n) x) *
      norm (sub (BilinearFinite zero add scale e a n) x)) 0 ->
    quadratic_limit a (fun i j => B (e i) (e j)) (B x x).
  Proof.
    intros e a x M N0 HM Hbound Hsquare. unfold quadratic_limit.
    apply (proj2 (SeqLimit_ext
      (quadratic_prefix a (fun i j => B (e i) (e j)))
      (fun n => B (BilinearFinite zero add scale e a n)
                  (BilinearFinite zero add scale e a n))
      (B x x) (fun n => quadratic_prefix_realization e a n))).
    eapply quadratic_readout_converges_squared_with_bound;
      [exact HM | exact Hbound | exact Hsquare].
  Qed.
End BilinearAlgebra.

Print Assumptions quadratic_stability_bound.
Print Assumptions quadratic_readout_converges.
Print Assumptions quadratic_limit_from_synthesis.
Print Assumptions quadratic_limit_from_squared_synthesis_bound.
