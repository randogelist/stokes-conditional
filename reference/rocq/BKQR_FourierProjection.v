(* Algebraic verification of the explicit Leray matrix.  ComplexVector uses
   natural coordinate labels; only labels 0,1,2 represent vector components. *)
From Stdlib Require Import Reals Lra Psatz Lia ZArith Field.
Require Import BKQR_FourierIndices BKQR_FourierConvection.

Module BKQR_FOURIER_PROJECTION.
Import BKQR_FOURIER_INDICES BKQR_FOURIER_CONVECTION.
Open Scope R_scope.

Theorem leray_component_formula : forall m v r, (r<3)%nat ->
  leray_apply m v r = cadd (v r)
    (cscale (- wave m r / mode_norm2 m) (complex_dot m v)).
Proof.
  intros m v [|[|[|r]]] Hr; try lia;
    unfold leray_apply, complex_dot, csum3, cadd, cscale, leray_entry,
      delta_axis, cre, cim;
    cbn; unfold Rdiv; f_equal; ring.
Qed.

Theorem leray_dot_formula : forall m v,
  complex_dot m (leray_apply m v) =
  cscale (1 - mode_norm2 m / mode_norm2 m) (complex_dot m v).
Proof.
  intros m v. unfold complex_dot, leray_apply, csum3, cadd, cscale,
    leray_entry, delta_axis, cre, cim.
  unfold mode_norm2, Rdiv. cbn. f_equal; ring.
Qed.

Theorem LERAY_PROJECTS_TO_SOLENOIDAL : forall m v,
  0 < mode_norm2 m -> complex_dot m (leray_apply m v) = czero.
Proof.
  intros m v Hm. rewrite leray_dot_formula.
  assert (Hcancel : mode_norm2 m / mode_norm2 m = 1) by (field; lra).
  rewrite Hcancel. unfold cscale, czero. f_equal; ring.
Qed.

Theorem LERAY_IDENTITY_ON_SOLENOIDAL : forall m v,
  complex_dot m v = czero -> forall r, (r<3)%nat -> leray_apply m v r = v r.
Proof.
  intros m v Hdiv r Hr. rewrite leray_component_formula by exact Hr.
  rewrite Hdiv. destruct (v r) as [vr vi].
  unfold cadd, cscale, czero, cre, cim. cbn. f_equal; ring.
Qed.

Theorem LERAY_IDEMPOTENT : forall m v,
  0 < mode_norm2 m -> forall r, (r<3)%nat ->
  leray_apply m (leray_apply m v) r = leray_apply m v r.
Proof.
  intros m v Hm r Hr. apply LERAY_IDENTITY_ON_SOLENOIDAL.
  - apply LERAY_PROJECTS_TO_SOLENOIDAL. exact Hm.
  - exact Hr.
Qed.

Theorem zero_mode_complex_dot : forall v, complex_dot mode_zero v = czero.
Proof.
  intro v. unfold complex_dot, wave, mode_zero, csum3, cadd, cscale,
    czero, cre, cim. cbn. f_equal; ring.
Qed.

Theorem ZERO_MODE_CONVECTION : forall u v r,
  projected_convection mode_zero u v r = czero.
Proof.
  intros u v r. unfold projected_convection. rewrite zero_mode_complex_dot.
  unfold cmul, ci, czero, cre, cim. cbn. f_equal; ring.
Qed.

Print Assumptions LERAY_PROJECTS_TO_SOLENOIDAL.
Print Assumptions LERAY_IDENTITY_ON_SOLENOIDAL.
Print Assumptions LERAY_IDEMPOTENT.
Print Assumptions ZERO_MODE_CONVECTION.
End BKQR_FOURIER_PROJECTION.
