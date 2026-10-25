From Stdlib Require Import Reals Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.

Module NSE_NATIVE_KQ_LADDER.
Import NSE_KQ_FINITE_ALGEBRA.
Open Scope R_scope.

(* Finite diagonal spectral carrier of the exact clock step.
   lambda is the eigenvalue vector, NOT a newly postulated PDE operator.
   Bilateral limits and identification with the infinite Kq product are
   deliberately outside this finite algebra module. *)
Definition step (h : R) (lambda v : Vec) : Vec :=
  fun k => v k + h*lambda k*v k.
Definition increment (h : R) (lambda v : Vec) : Vec :=
  fun k => h*lambda k*v k.
Definition spectral_energy n (lambda v : Vec) :=
  sum n (fun k => lambda k*v k*v k).
Definition clock_cost n h (lambda v : Vec) := h*norm2 n (mul lambda v).

Fixpoint clock_run (ell : nat -> R) (lambda seed : Vec) (j : nat) : Vec :=
  match j with
  | O => seed
  | S i => step (ell i) lambda (clock_run ell lambda seed i)
  end.

Theorem NSKL00_CONSTRUCTED_CLOCK_STEP : forall ell lambda seed j k,
  clock_run ell lambda seed (S j) k =
  clock_run ell lambda seed j k + ell j*lambda k*clock_run ell lambda seed j k.
Proof. reflexivity. Qed.

Lemma spectral_energy_nonneg : forall n lambda v,
  (forall k, (k<n)%nat -> 0 <= lambda k) -> 0 <= spectral_energy n lambda v.
Proof.
  intros; unfold spectral_energy; apply sum_nonneg; intros k Hk.
  replace (lambda k*v k*v k) with (lambda k*(v k*v k)) by ring.
  apply Rmult_le_pos; [auto | nra].
Qed.

Theorem NSKL01_EXACT_ENSTROPHY_STEP : forall n h lambda v,
  spectral_energy n lambda (step h lambda v) - spectral_energy n lambda v =
  2*clock_cost n h lambda v + spectral_energy n lambda (increment h lambda v).
Proof.
  induction n as [|n IH]; intros h lambda v.
  - unfold spectral_energy, clock_cost, norm2, dot; simpl; ring.
  - specialize (IH h lambda v).
    unfold spectral_energy, clock_cost, norm2, dot in *.
    simpl in *; unfold step, increment, mul in *; nra.
Qed.

Theorem NSKL02_CLOCK_COST_IS_QUOTIENT : forall n h lambda v,
  0 < h -> clock_cost n h lambda v = norm2 n (increment h lambda v)/h.
Proof.
  intros n h lambda v Hh.
  assert (Hi : norm2 n (increment h lambda v) = h*h*norm2 n (mul lambda v)).
  { unfold norm2, dot, increment, mul.
    transitivity (sum n (fun k => (h*h)*((lambda k*v k)*(lambda k*v k)))).
    - apply sum_ext; intros; ring.
    - apply sum_scale. }
  rewrite Hi; unfold clock_cost; field; lra.
Qed.

Theorem NSKL10_EXACT_FINITE_LADDER_TELESCOPE : forall n ell lambda seed m,
  spectral_energy n lambda (clock_run ell lambda seed m) - spectral_energy n lambda seed =
  2*sum m (fun j => clock_cost n (ell j) lambda (clock_run ell lambda seed j)) +
  sum m (fun j => spectral_energy n lambda
    (increment (ell j) lambda (clock_run ell lambda seed j))).
Proof.
  intros n ell lambda seed m; induction m as [|m IH].
  - simpl; ring.
  - change (spectral_energy n lambda
      (step (ell m) lambda (clock_run ell lambda seed m)) - spectral_energy n lambda seed =
      2*(sum m (fun j => clock_cost n (ell j) lambda (clock_run ell lambda seed j)) +
         clock_cost n (ell m) lambda (clock_run ell lambda seed m)) +
      (sum m (fun j => spectral_energy n lambda
         (increment (ell j) lambda (clock_run ell lambda seed j))) +
       spectral_energy n lambda (increment (ell m) lambda (clock_run ell lambda seed m)))).
    pose proof (NSKL01_EXACT_ENSTROPHY_STEP n (ell m) lambda (clock_run ell lambda seed m)).
    lra.
Qed.

Theorem NSKL11_FINITE_LADDER_NO_REUSE_BUDGET : forall n ell lambda seed m,
  (forall k, (k<n)%nat -> 0 <= lambda k) ->
  2*sum m (fun j => clock_cost n (ell j) lambda (clock_run ell lambda seed j)) <=
  spectral_energy n lambda (clock_run ell lambda seed m).
Proof.
  intros n ell lambda seed m Hlam.
  pose proof (NSKL10_EXACT_FINITE_LADDER_TELESCOPE n ell lambda seed m) as Htel.
  pose proof (spectral_energy_nonneg n lambda seed Hlam) as Hseed.
  assert (Hcorr : 0 <= sum m (fun j => spectral_energy n lambda
    (increment (ell j) lambda (clock_run ell lambda seed j)))).
  { apply sum_nonneg; intros; apply spectral_energy_nonneg; exact Hlam. }
  lra.
Qed.

(* L2 telescope provides the companion b_j budget after the analytic
   scale endpoints have been supplied. *)
Theorem NSKL12_EXACT_L2_STEP : forall n h lambda v,
  norm2 n (step h lambda v) - norm2 n v =
  2*h*spectral_energy n lambda v + norm2 n (increment h lambda v).
Proof.
  induction n as [|n IH]; intros h lambda v.
  - unfold spectral_energy, norm2, dot; simpl; ring.
  - specialize (IH h lambda v).
    unfold spectral_energy, norm2, dot in *.
    simpl in *; unfold step, increment in *; nra.
Qed.

Definition two_scale (q : R) (v w : Vec) : Vec := fun k => (w k-q*v k)/(1-q).

Theorem NSKL20_CANDIDATE_F_NEIGHBOR_IDENTITY : forall q v w k,
  q <> 1 -> w k+v k =
  2*two_scale q v w k - ((1+q)/(1-q))*(w k-v k).
Proof. intros; unfold two_scale; field; lra. Qed.

Theorem NSKL21_CANDIDATE_F_TENSOR_COVARIANCE : forall q v w i j,
  q <> 1 ->
  (w i*w j-q*(v i*v j))/(1-q) =
  two_scale q v w i*two_scale q v w j -
  (q/((1-q)*(1-q)))*((w i-v i)*(w j-v j)).
Proof. intros; unfold two_scale; field; lra. Qed.

Definition tensor_step (v w : Vec) i j :=
  ((w i-v i)*(w j+v j)+(w i+v i)*(w j-v j))/2.

Theorem NSKL30_EXACT_TENSOR_INCREMENT : forall v w i j,
  tensor_step v w i j = w i*w j-v i*v j.
Proof. intros; unfold tensor_step; unfold Rdiv; field. Qed.

Theorem NSKL31_FULL_SOURCE_TENSOR_TELESCOPE : forall (v : nat -> Vec) m i j,
  sum m (fun k => tensor_step (v k) (v (S k)) i j) =
  v m i*v m j-v O i*v O j.
Proof.
  intros v m i j.
  transitivity (sum m (fun k => v (S k) i*v (S k) j-v k i*v k j)).
  - apply sum_ext; intros; apply NSKL30_EXACT_TENSOR_INCREMENT.
  (* Supply the nonlinear scalar sequence explicitly: plain [apply] does
     not infer e k := v k i * v k j from this higher-order pattern. *)
  - exact (sum_telescoping m (fun k => v k i * v k j)).
Qed.

(* This is a finite-coordinate source identity.  Choosing the physical
   tensor detector still requires its actual PDE binding. *)
Theorem NSKL32_SIGNED_WORK_TELESCOPE : forall n m (v : nat -> Vec) (W : nat -> nat -> R),
  sum m (fun k => sum n (fun i => sum n (fun j =>
    W i j*(v (S k) i*v (S k) j-v k i*v k j)))) =
  sum n (fun i => sum n (fun j => W i j*(v m i*v m j-v O i*v O j))).
Proof.
  intros n m v W.
  transitivity (sum m (fun k =>
    sum n (fun i => sum n (fun j => W i j*v (S k) i*v (S k) j)) -
    sum n (fun i => sum n (fun j => W i j*v k i*v k j)))).
  - apply sum_ext; intros k Hk; rewrite <- sum_sub.
    apply sum_ext; intros i Hi; rewrite <- sum_sub.
    apply sum_ext; intros j Hj; ring.
  (* Telescope the fully contracted scalar sequence, not an inferred
     function hidden beneath the two coordinate sums. *)
  - rewrite (sum_telescoping m
      (fun k => sum n (fun i => sum n (fun j => W i j*v k i*v k j)))).
    rewrite <- sum_sub.
    apply sum_ext; intros i Hi; rewrite <- sum_sub.
    apply sum_ext; intros j Hj; ring.
Qed.

End NSE_NATIVE_KQ_LADDER.
