From Stdlib Require Import Reals Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.

Module NSE_GP_GRAM_GEOMETRY.
Import NSE_KQ_FINITE_ALGEBRA.
Open Scope R_scope.

(* A one-direction projection with Rocq's total real division.
   The zero-norm branch is proved, not excluded. *)
Definition coefficient n (v x : Vec) := dot n x v / norm2 n v.
Definition remove n (v x : Vec) := sub x (scale (coefficient n v x) v).

Lemma dot_remove_l : forall n v x y,
  dot n (remove n v x) y = dot n x y - coefficient n v x * dot n v y.
Proof. intros; unfold remove; rewrite dot_sub_l, dot_scale_l; reflexivity. Qed.
Lemma dot_remove_r : forall n x v y,
  dot n x (remove n v y) = dot n x y - coefficient n v y * dot n x v.
Proof. intros; unfold remove; rewrite dot_sub_r, dot_scale_r; reflexivity. Qed.

Theorem NSGG00_REMOVE_IS_ORTHOGONAL : forall n v x,
  dot n (remove n v x) v = 0.
Proof.
  intros; rewrite dot_remove_l; fold (norm2 n v).
  unfold coefficient.
  destruct (Req_dec (norm2 n v) 0) as [Hz | Hz].
  - pose proof (norm2_zero_dot n x v Hz) as Hdot.
    rewrite Hdot, Hz; unfold Rdiv; ring.
  - field; nra.
Qed.

Lemma remove_preserves_annihilator : forall n d v x,
  dot n d v = 0 -> dot n d (remove n v x) = dot n d x.
Proof. intros; rewrite dot_remove_r, H; ring. Qed.

(* Two-direction Gram--Schmidt.  It remains defined when the directions
   vanish or are dependent.  No matrix-invertibility premise is used. *)
Definition second_direction n (n0 n1 : Vec) := remove n n0 n1.
Definition first_residual n (f n0 : Vec) := remove n n0 f.
Definition beta n (f n0 n1 : Vec) :=
  coefficient n (second_direction n n0 n1) (first_residual n f n0).
Definition alpha n (f n0 n1 : Vec) :=
  coefficient n n0 f - beta n f n0 n1 * coefficient n n0 n1.
Definition residual (f n0 n1 : Vec) (a b : R) : Vec :=
  sub (sub f (scale a n0)) (scale b n1).
Definition reduced n (f n0 n1 : Vec) :=
  residual f n0 n1 (alpha n f n0 n1) (beta n f n0 n1).
Definition reduced_capacity n (f n0 n1 : Vec) := norm2 n (reduced n f n0 n1).

Lemma dot_residual_l : forall n f n0 n1 a b y,
  dot n (residual f n0 n1 a b) y =
  dot n f y - a*dot n n0 y - b*dot n n1 y.
Proof. intros; unfold residual; rewrite !dot_sub_l, !dot_scale_l; reflexivity. Qed.
Lemma dot_residual_r : forall n x f n0 n1 a b,
  dot n x (residual f n0 n1 a b) =
  dot n x f - a*dot n x n0 - b*dot n x n1.
Proof. intros; unfold residual; rewrite !dot_sub_r, !dot_scale_r; reflexivity. Qed.

Lemma reduced_is_two_steps : forall n f n0 n1 i,
  reduced n f n0 n1 i =
  remove n (second_direction n n0 n1) (first_residual n f n0) i.
Proof.
  intros; unfold reduced, residual, alpha.
  unfold beta, first_residual, second_direction, remove, sub, scale.
  ring.
Qed.

Theorem NSGG10_RANK_SAFE_TWO_DIRECTION_ORTHOGONALITY : forall n f n0 n1,
  dot n (reduced n f n0 n1) n0 = 0 /\
  dot n (reduced n f n0 n1) n1 = 0.
Proof.
  intros n f n0 n1.
  set (w := second_direction n n0 n1).
  set (f0 := first_residual n f n0).
  set (r := remove n w f0).
  assert (Heq : forall i, reduced n f n0 n1 i = r i).
  { intro i; unfold r, w, f0; apply reduced_is_two_steps. }
  assert (Hw0 : dot n w n0 = 0).
  { unfold w, second_direction; apply NSGG00_REMOVE_IS_ORTHOGONAL. }
  assert (Hf0 : dot n f0 n0 = 0).
  { unfold f0, first_residual; apply NSGG00_REMOVE_IS_ORTHOGONAL. }
  assert (Hr0 : dot n r n0 = 0).
  { unfold r; rewrite dot_remove_l, Hf0, Hw0; ring. }
  assert (Hrw : dot n r w = 0).
  { unfold r; apply NSGG00_REMOVE_IS_ORTHOGONAL. }
  assert (Hr1 : dot n r n1 = 0).
  { unfold w, second_direction in Hrw.
    rewrite dot_remove_r, Hr0 in Hrw; lra. }
  split; rewrite (dot_ext_l n (reduced n f n0 n1) r);
    try (intros; apply Heq); assumption.
Qed.

Definition NormalEquations n (f n0 n1 : Vec) (a b : R) : Prop :=
  dot n f n0 = a*norm2 n n0 + b*dot n n1 n0 /\
  dot n f n1 = a*dot n n0 n1 + b*norm2 n n1.

Theorem NSGG11_CONSTRUCTED_NORMAL_EQUATIONS : forall n f n0 n1,
  NormalEquations n f n0 n1 (alpha n f n0 n1) (beta n f n0 n1).
Proof.
  intros; pose proof (NSGG10_RANK_SAFE_TWO_DIRECTION_ORTHOGONALITY n f n0 n1) as [H0 H1].
  unfold reduced in H0, H1; rewrite dot_residual_l in H0, H1.
  unfold NormalEquations, norm2; split; lra.
Qed.

Theorem NSGG12_REDUCED_PAIRING_IS_THE_SAME : forall n d f n0 n1,
  dot n d n0 = 0 -> dot n d n1 = 0 ->
  dot n d (reduced n f n0 n1) = dot n d f.
Proof.
  intros; unfold reduced; rewrite dot_residual_r, H, H0; ring.
Qed.

Lemma residual_norm_expansion : forall n f n0 n1 a b,
  norm2 n (residual f n0 n1 a b) =
  norm2 n f - 2*a*dot n f n0 - 2*b*dot n f n1 +
  a*a*norm2 n n0 + 2*a*b*dot n n0 n1 + b*b*norm2 n n1.
Proof.
  intros; unfold norm2; rewrite dot_residual_l, !dot_residual_r.
  rewrite (dot_sym n n0 f), (dot_sym n n1 f), (dot_sym n n1 n0); ring.
Qed.

Theorem NSGG13_NORMAL_EQUATIONS_GIVE_SCHUR_VALUE : forall n f n0 n1 a b,
  NormalEquations n f n0 n1 a b ->
  norm2 n (residual f n0 n1 a b) = norm2 n f - a*dot n f n0 - b*dot n f n1.
Proof.
  intros n f n0 n1 a b [H0 H1].
  rewrite (dot_sym n n1 n0) in H0.
  rewrite residual_norm_expansion, H0, H1; ring.
Qed.

Theorem NSGG14_CONSTRUCTED_SCHUR_VALUE : forall n f n0 n1,
  reduced_capacity n f n0 n1 = norm2 n f -
  alpha n f n0 n1 * dot n f n0 - beta n f n0 n1 * dot n f n1.
Proof.
  intros; unfold reduced_capacity, reduced.
  apply NSGG13_NORMAL_EQUATIONS_GIVE_SCHUR_VALUE.
  apply NSGG11_CONSTRUCTED_NORMAL_EQUATIONS.
Qed.

(* Optimality proves that this is the quotient norm, including singular G.
   A Moore--Penrose implementation is not postulated or needed. *)
Theorem NSGG15_REDUCED_CAPACITY_IS_MINIMAL : forall n f n0 n1 a b,
  reduced_capacity n f n0 n1 <= norm2 n (residual f n0 n1 a b).
Proof.
  intros n f n0 n1 a b.
  set (r := reduced n f n0 n1).
  set (v := add (scale (alpha n f n0 n1-a) n0)
                (scale (beta n f n0 n1-b) n1)).
  assert (Heq : forall i, residual f n0 n1 a b i = add r v i).
  { intro i; unfold r, v, reduced, residual, add, sub, scale; ring. }
  assert (Horth : dot n r v = 0).
  { pose proof (NSGG10_RANK_SAFE_TWO_DIRECTION_ORTHOGONALITY n f n0 n1) as [H0 H1].
    unfold v; rewrite dot_add_r, !dot_scale_r.
    unfold r; rewrite H0, H1; ring. }
  rewrite (norm2_ext n (residual f n0 n1 a b) (add r v));
    [| intros; apply Heq].
  rewrite norm2_add, Horth.
  pose proof (norm2_nonneg n v).
  unfold reduced_capacity; fold r; lra.
Qed.

Theorem NSGG16_REDUCED_CAPACITY_BOUNDS : forall n f n0 n1,
  0 <= reduced_capacity n f n0 n1 /\ reduced_capacity n f n0 n1 <= norm2 n f.
Proof.
  intros; split; [apply norm2_nonneg |].
  pose proof (NSGG15_REDUCED_CAPACITY_IS_MINIMAL n f n0 n1 0 0) as H.
  assert (Heq : norm2 n (residual f n0 n1 0 0) = norm2 n f).
  { apply norm2_ext; intros; unfold residual, sub, scale; ring. }
  rewrite Heq in H; exact H.
Qed.

Theorem NSGG20_RANK_SAFE_SCHUR_ACTION_BOUND : forall n d f n0 n1,
  dot n d n0 = 0 -> dot n d n1 = 0 ->
  dot n d f * dot n d f <= norm2 n d * reduced_capacity n f n0 n1.
Proof.
  intros n d f n0 n1 H0 H1.
  pose proof (NSKA10_FINITE_CAUCHY n d (reduced n f n0 n1)) as Hcs.
  rewrite (NSGG12_REDUCED_PAIRING_IS_THE_SAME n d f n0 n1 H0 H1) in Hcs.
  exact Hcs.
Qed.

Theorem NSGG21_ZERO_CAPACITY_IMPLIES_ZERO_RENEWAL : forall n d f n0 n1,
  dot n d n0 = 0 -> dot n d n1 = 0 -> reduced_capacity n f n0 n1 = 0 ->
  dot n d f = 0.
Proof.
  intros n d f n0 n1 H0 H1 Hz.
  pose proof (NSGG20_RANK_SAFE_SCHUR_ACTION_BOUND n d f n0 n1 H0 H1).
  rewrite Hz in H; nra.
Qed.

Inductive Axis4 := D | F | N0 | N1.
Definition sum4 (f : Axis4 -> R) := f D+f F+f N0+f N1.
Definition pick4 (d f n0 n1 : Vec) (i : Axis4) : Vec :=
  match i with D=>d | F=>f | N0=>n0 | N1=>n1 end.
Definition gram4 n (d f n0 n1 : Vec) (i j : Axis4) :=
  dot n (pick4 d f n0 n1 i) (pick4 d f n0 n1 j).
Definition quadratic4 (G : Axis4 -> Axis4 -> R) (c : Axis4 -> R) :=
  sum4 (fun i => sum4 (fun j => c i * G i j * c j)).
Definition combine4 (d f n0 n1 : Vec) (c : Axis4 -> R) :=
  add (add (scale (c D) d) (scale (c F) f))
      (add (scale (c N0) n0) (scale (c N1) n1)).
Definition PSD4 (G : Axis4 -> Axis4 -> R) : Prop :=
  forall c, 0 <= quadratic4 G c.

Lemma gram4_quadratic_is_norm : forall n d f n0 n1 c,
  quadratic4 (gram4 n d f n0 n1) c = norm2 n (combine4 d f n0 n1 c).
Proof.
  intros; unfold quadratic4, sum4, gram4, pick4, norm2, combine4.
  rewrite !dot_add_l, !dot_add_r, !dot_scale_l, !dot_scale_r; ring.
Qed.

Theorem NSGG30_CONCRETE_GRAM4_IS_PSD : forall n d f n0 n1,
  PSD4 (gram4 n d f n0 n1).
Proof.
  intros; unfold PSD4; intro c; rewrite gram4_quadratic_is_norm; apply norm2_nonneg.
Qed.

Theorem NSGG31_PHYSICAL_GRAM4_ZERO_BLOCK : forall n d f n0 n1,
  dot n d n0 = 0 -> dot n d n1 = 0 ->
  gram4 n d f n0 n1 D N0 = 0 /\ gram4 n d f n0 n1 D N1 = 0 /\
  gram4 n d f n0 n1 N0 D = 0 /\ gram4 n d f n0 n1 N1 D = 0.
Proof.
  intros; unfold gram4, pick4; repeat split; try assumption;
    rewrite dot_sym; assumption.
Qed.

Definition FiniteIsometry n m (T : Vec -> Vec) : Prop :=
  forall x y, dot m (T x) (T y) = dot n x y.

Theorem NSGG40_GP_ISOMETRY_PRESERVES_GRAM4 : forall n m T,
  FiniteIsometry n m T -> forall d f n0 n1 i j,
  gram4 m (T d) (T f) (T n0) (T n1) i j = gram4 n d f n0 n1 i j.
Proof.
  intros n m T H d f n0 n1 i j; destruct i, j;
    unfold gram4, pick4; apply H.
Qed.

(* Pairing preservation alone suffices: the coefficients solve the same
   two-by-two normal equations and the Schur value is uniquely determined. *)
Theorem NSGG41_NORMAL_EQUATIONS_TRANSPORT : forall n m T,
  FiniteIsometry n m T -> forall f n0 n1 a b,
  NormalEquations n f n0 n1 a b ->
  NormalEquations m (T f) (T n0) (T n1) a b.
Proof.
  intros n m T H f n0 n1 a b Hnormal.
  unfold NormalEquations, norm2 in *; rewrite !H; exact Hnormal.
Qed.

Theorem NSGG42_GP_PRESERVES_REDUCED_CAPACITY : forall n m T,
  FiniteIsometry n m T -> forall f n0 n1,
  reduced_capacity m (T f) (T n0) (T n1) = reduced_capacity n f n0 n1.
Proof.
  intros n m T H f n0 n1.
  set (a := alpha n f n0 n1); set (b := beta n f n0 n1).
  set (a' := alpha m (T f) (T n0) (T n1)).
  set (b' := beta m (T f) (T n0) (T n1)).
  assert (Hab : NormalEquations n f n0 n1 a b).
  { unfold a, b; apply NSGG11_CONSTRUCTED_NORMAL_EQUATIONS. }
  assert (Hab' : NormalEquations n f n0 n1 a' b').
  { pose proof (NSGG11_CONSTRUCTED_NORMAL_EQUATIONS m (T f) (T n0) (T n1)) as Hn.
    unfold NormalEquations, norm2 in Hn; rewrite !H in Hn; exact Hn. }
  assert (Hupper : reduced_capacity m (T f) (T n0) (T n1) <= reduced_capacity n f n0 n1).
  { pose proof (NSGG15_REDUCED_CAPACITY_IS_MINIMAL m (T f) (T n0) (T n1) a b) as Hmin.
    rewrite (NSGG13_NORMAL_EQUATIONS_GIVE_SCHUR_VALUE m (T f) (T n0) (T n1) a b
      (NSGG41_NORMAL_EQUATIONS_TRANSPORT n m T H f n0 n1 a b Hab)) in Hmin.
    unfold norm2 in Hmin; rewrite !H in Hmin.
    rewrite (NSGG14_CONSTRUCTED_SCHUR_VALUE n f n0 n1); unfold a, b in Hmin; exact Hmin. }
  assert (Hlower : reduced_capacity n f n0 n1 <= reduced_capacity m (T f) (T n0) (T n1)).
  { pose proof (NSGG15_REDUCED_CAPACITY_IS_MINIMAL n f n0 n1 a' b') as Hmin.
    rewrite (NSGG13_NORMAL_EQUATIONS_GIVE_SCHUR_VALUE n f n0 n1 a' b' Hab') in Hmin.
    rewrite (NSGG14_CONSTRUCTED_SCHUR_VALUE m (T f) (T n0) (T n1)); unfold norm2; rewrite !H.
    unfold a', b' in Hmin; exact Hmin. }
  lra.
Qed.

End NSE_GP_GRAM_GEOMETRY.
