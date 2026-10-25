From Stdlib Require Import Reals Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.

Module NSE_HELICITY_DEFECT_GEOMETRY.
Import NSE_KQ_FINITE_ALGEBRA.
Open Scope R_scope.

(* Concrete finite real coordinates.  omega is an input vector; identifying
   it with the physical curl is NOT built into this definition. *)
Definition hd_coefficient n (u omega : Vec) := dot n u omega / norm2 n u.
Definition hd_residual n (u omega : Vec) :=
  sub omega (scale (hd_coefficient n u omega) u).
Definition hd_defect n (u omega : Vec) := norm2 n (hd_residual n u omega).

Theorem NSHD00_DEFECT_NONNEGATIVE : forall n u omega,
  0 <= hd_defect n u omega.
Proof. intros; apply norm2_nonneg. Qed.

Theorem NSHD01_OPTIMAL_COEFFICIENT_EQUATION : forall n u omega,
  0 < norm2 n u ->
  hd_coefficient n u omega * norm2 n u = dot n u omega.
Proof. intros n u omega HE; unfold hd_coefficient; field; lra. Qed.

Theorem NSHD02_OPTIMAL_RESIDUAL_ORTHOGONAL : forall n u omega,
  0 < norm2 n u -> dot n u (hd_residual n u omega) = 0.
Proof.
  intros n u omega HE.
  pose proof (NSHD01_OPTIMAL_COEFFICIENT_EQUATION n u omega HE) as Hc.
  unfold hd_residual; rewrite dot_sub_r, dot_scale_r.
  change (dot n u omega-hd_coefficient n u omega*norm2 n u=0).
  lra.
Qed.

Theorem NSHD03_DEFECT_CLOSED_FORM : forall n u omega,
  0 < norm2 n u ->
  hd_defect n u omega = norm2 n omega -
    dot n u omega * dot n u omega / norm2 n u.
Proof.
  intros n u omega HE; unfold hd_defect, hd_residual.
  rewrite norm2_sub_scale, (dot_sym n omega u).
  unfold hd_coefficient; field; lra.
Qed.

Theorem NSHD04_COMPLETE_SQUARE_MINIMIZER : forall n u omega b,
  0 < norm2 n u ->
  norm2 n (sub omega (scale b u)) = hd_defect n u omega +
    norm2 n u * (b-hd_coefficient n u omega)*(b-hd_coefficient n u omega).
Proof.
  intros n u omega b HE.
  pose proof (NSHD01_OPTIMAL_COEFFICIENT_EQUATION n u omega HE) as Hc.
  unfold hd_defect, hd_residual.
  rewrite !norm2_sub_scale, (dot_sym n omega u).
  rewrite <- Hc; ring.
Qed.

Theorem NSHD05_RESIDUAL_IS_MINIMIZER : forall n u omega b,
  0 < norm2 n u ->
  hd_defect n u omega <= norm2 n (sub omega (scale b u)).
Proof.
  intros n u omega b HE.
  rewrite (NSHD04_COMPLETE_SQUARE_MINIMIZER n u omega b HE).
  assert (Hprod : 0 <= norm2 n u *
    ((b-hd_coefficient n u omega)*(b-hd_coefficient n u omega))).
  { apply Rmult_le_pos; [lra|exact (Rle_0_sqr (b-hd_coefficient n u omega))]. }
  nra.
Qed.

Theorem NSHD06_GRAM_DETERMINANT : forall n u omega,
  0 < norm2 n u ->
  norm2 n u * norm2 n omega - dot n u omega * dot n u omega =
  norm2 n u * hd_defect n u omega.
Proof.
  intros n u omega HE; rewrite (NSHD03_DEFECT_CLOSED_FORM n u omega HE).
  field; lra.
Qed.

Theorem NSHD07_DEFECT_AT_MOST_VORTICITY_ENERGY : forall n u omega,
  0 < norm2 n u -> hd_defect n u omega <= norm2 n omega.
Proof.
  intros n u omega HE.
  pose proof (NSHD06_GRAM_DETERMINANT n u omega HE) as HG.
  pose proof (Rle_0_sqr (dot n u omega)) as HS.
  apply (Rmult_le_reg_l (norm2 n u)); [exact HE|]; nra.
Qed.

(* Exact zero-energy branch; no artificial positive denominator. *)
Theorem NSHD08_ZERO_ENERGY_BRANCH : forall n u omega,
  norm2 n u=0 ->
  dot n u omega=0 /\ hd_defect n u omega=norm2 n omega.
Proof.
  intros n u omega HE.
  assert (HH : dot n u omega=0).
  { rewrite dot_sym; apply norm2_zero_dot; exact HE. }
  split; [exact HH|].
  unfold hd_defect, hd_residual, hd_coefficient.
  rewrite HH, HE; unfold Rdiv; rewrite Rinv_0.
  apply norm2_ext; intros; unfold sub, scale; ring.
Qed.

Theorem NSHD09_SIGNED_CURL_VARIANCE : forall n u xi,
  hd_defect n u (mul xi u) =
  sum n (fun i =>
    (xi i-hd_coefficient n u (mul xi u))*
    (xi i-hd_coefficient n u (mul xi u))*u i*u i).
Proof.
  intros; unfold hd_defect, hd_residual, norm2, dot, sub, scale, mul.
  apply sum_ext; intros; ring.
Qed.

(* Literal three-component cross-product algebra.  No PDE source or
   torus quadrature is postulated by these identities. *)
Record HDVec3 := HDv3 { hdx : R; hdy : R; hdz : R }.
Definition hd3_sub (v w : HDVec3) :=
  HDv3 (hdx v-hdx w) (hdy v-hdy w) (hdz v-hdz w).
Definition hd3_scale (c : R) (v : HDVec3) :=
  HDv3 (c*hdx v) (c*hdy v) (c*hdz v).
Definition hd3_cross (v w : HDVec3) :=
  HDv3 (hdy v*hdz w-hdz v*hdy w)
       (hdz v*hdx w-hdx v*hdz w)
       (hdx v*hdy w-hdy v*hdx w).
Definition hd3_dot (v w : HDVec3) :=
  hdx v*hdx w+hdy v*hdy w+hdz v*hdz w.

Theorem NSHD10_LITERAL_LAMB_RESIDUAL_FACTOR : forall u omega c,
  hd3_cross u omega = hd3_cross u (hd3_sub omega (hd3_scale c u)).
Proof.
  intros [ux uy uz] [ox oy oz] c.
  unfold hd3_cross, hd3_sub, hd3_scale; simpl; f_equal; ring.
Qed.

Theorem NSHD11_LITERAL_CROSS_ORTHOGONAL : forall u w,
  hd3_dot (hd3_cross u w) u=0 /\ hd3_dot (hd3_cross u w) w=0.
Proof.
  intros [ux uy uz] [wx wy wz]; unfold hd3_dot, hd3_cross; simpl; split; ring.
Qed.

Theorem NSHD12_BELTRAMI_POINTWISE_SOURCE_ZERO : forall u c,
  hd3_cross u (hd3_scale c u) = HDv3 0 0 0.
Proof.
  intros [ux uy uz] c; unfold hd3_cross, hd3_scale; simpl; f_equal; ring.
Qed.

End NSE_HELICITY_DEFECT_GEOMETRY.
