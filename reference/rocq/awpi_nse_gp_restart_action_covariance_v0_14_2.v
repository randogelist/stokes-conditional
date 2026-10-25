From Stdlib Require Import Reals Lra Psatz Field String.

Module NSE_GP_RESTART_ACTION_COVARIANCE.

Open Scope R_scope.

(*
  Finite algebraic covariance layer for GP/restart action currency.

  A positive GP multiplier s rescales a physical cut psi by s and its
  quadratic capacity denominator D by s^2.  The positive-action quotient,
  canonical detector pairing, inherited pairing and source pairing are then
  unchanged when the detector is transformed dually by 1/s.

  This is the scalar/atom-level algebra used componentwise in the
  detector--Duhamel genealogy.  No PDE source-realization theorem is claimed.
*)

Definition action (psi D : R) : R := psi * psi / D.
Definition detector (psi D : R) : R := psi / D.
Definition gp_cut (s psi : R) : R := s * psi.
Definition gp_cap (s D : R) : R := s * s * D.
Definition gp_dual (s g : R) : R := g / s.

Theorem NSAC01_ACTION_NUMERATOR_CAPACITY_COVARIANCE :
  forall s psi D : R,
    (gp_cut s psi) * (gp_cut s psi) * D =
    psi * psi * (gp_cap s D).
Proof.
  intros s psi D.
  unfold gp_cut, gp_cap.
  ring.
Qed.

Theorem NSAC02_ACTION_QUOTIENT_INVARIANT :
  forall s psi D : R,
    s <> 0 ->
    D <> 0 ->
    action (gp_cut s psi) (gp_cap s D) = action psi D.
Proof.
  intros s psi D Hs HD.
  unfold action, gp_cut, gp_cap.
  field; nra.
Qed.

Theorem NSAC03_CANONICAL_DETECTOR_TRANSFORMS_DUALLY :
  forall s psi D : R,
    s <> 0 ->
    D <> 0 ->
    detector (gp_cut s psi) (gp_cap s D) =
    gp_dual s (detector psi D).
Proof.
  intros s psi D Hs HD.
  unfold detector, gp_cut, gp_cap, gp_dual.
  field; nra.
Qed.

Theorem NSAC04_CANONICAL_PAIRING_INVARIANT :
  forall s psi D : R,
    s <> 0 ->
    D <> 0 ->
    detector (gp_cut s psi) (gp_cap s D) * gp_cut s psi =
    detector psi D * psi.
Proof.
  intros s psi D Hs HD.
  rewrite (NSAC03_CANONICAL_DETECTOR_TRANSFORMS_DUALLY s psi D Hs HD).
  unfold gp_dual, gp_cut.
  field; nra.
Qed.

Theorem NSAC05_DUAL_SOURCE_PAIRING_INVARIANT :
  forall s source g : R,
    s <> 0 ->
    gp_cut s source * gp_dual s g = source * g.
Proof.
  intros s source g Hs.
  unfold gp_cut, gp_dual.
  field; nra.
Qed.

Theorem NSAC06_DUAL_INHERITED_PAIRING_INVARIANT :
  forall s inherited g : R,
    s <> 0 ->
    gp_cut s inherited * gp_dual s g = inherited * g.
Proof.
  intros s inherited g Hs.
  exact (NSAC05_DUAL_SOURCE_PAIRING_INVARIANT s inherited g Hs).
Qed.

Theorem NSAC07_SOURCE_CAPACITY_INVARIANT :
  forall s source D : R,
    s <> 0 ->
    D <> 0 ->
    action (gp_cut s source) (gp_cap s D) = action source D.
Proof.
  intros s source D Hs HD.
  exact (NSAC02_ACTION_QUOTIENT_INVARIANT s source D Hs HD).
Qed.

(* Composition law for positive spectral/GP rescalings. *)
Theorem NSAC10_GP_CUT_COMPOSITION :
  forall s1 s2 psi : R,
    gp_cut s1 (gp_cut s2 psi) = gp_cut (s1 * s2) psi.
Proof.
  intros s1 s2 psi.
  unfold gp_cut.
  ring.
Qed.

Theorem NSAC11_GP_CAP_COMPOSITION :
  forall s1 s2 D : R,
    gp_cap s1 (gp_cap s2 D) = gp_cap (s1 * s2) D.
Proof.
  intros s1 s2 D.
  unfold gp_cap.
  ring.
Qed.

Theorem NSAC12_GP_DUAL_COMPOSITION :
  forall s1 s2 g : R,
    s1 <> 0 ->
    s2 <> 0 ->
    gp_dual s1 (gp_dual s2 g) = gp_dual (s1 * s2) g.
Proof.
  intros s1 s2 g H1 H2.
  unfold gp_dual.
  field; nra.
Qed.

(* Restart-local detector--Duhamel balance is algebraically unchanged once
   each source/inherited pairing is transported by the dual GP scaling. *)
Theorem NSAC20_DUHAMEL_BALANCE_COVARIANT :
  forall M I R1 R2 R3 M' I' R1' R2' R3' : R,
    M = I + R1 + R2 + R3 ->
    M' = M ->
    I' = I ->
    R1' = R1 ->
    R2' = R2 ->
    R3' = R3 ->
    M' = I' + R1' + R2' + R3'.
Proof.
  intros M I R1 R2 R3 M' I' R1' R2' R3' Hbal HM HI H1 H2 H3.
  lra.
Qed.

(* A convenient cross-multiplied form: if a source pairing owns a fraction
   delta of parent action before GP scaling, the same statement holds after
   dual GP scaling because both pairings are invariant. *)
Theorem NSAC21_FIXED_FRACTION_OWNERSHIP_PRESERVED :
  forall delta M R M' R' : R,
    delta * M <= R ->
    M' = M ->
    R' = R ->
    delta * M' <= R'.
Proof.
  intros delta M R M' R' H HM HR.
  subst.
  exact H.
Qed.

(* Interface to the physical theorem: a positive componentwise GP scaling
   with the denominator scaled quadratically preserves the exact A_+ currency.
   Source labels/restart windows may therefore be constructed before or after
   the GP coordinate change without changing their scalar action masses. *)
Section PHYSICAL_FRONTIER.

Variable PhysicalRestartGPRealizationPrinciple : Prop.

Theorem NSAC90_RESTART_GP_CURRENCY_EXPOSES_ONLY_PHYSICAL_REALIZATION :
  PhysicalRestartGPRealizationPrinciple ->
  PhysicalRestartGPRealizationPrinciple.
Proof.
  intro H.
  exact H.
Qed.

End PHYSICAL_FRONTIER.

Definition STATUS : string :=
  "NSE_GP_RESTART_ACTION_CURRENCY_COVARIANCE_NO_ADMITTED"%string.

End NSE_GP_RESTART_ACTION_COVARIANCE.

Print Assumptions NSE_GP_RESTART_ACTION_COVARIANCE.NSAC02_ACTION_QUOTIENT_INVARIANT.
Print Assumptions NSE_GP_RESTART_ACTION_COVARIANCE.NSAC03_CANONICAL_DETECTOR_TRANSFORMS_DUALLY.
Print Assumptions NSE_GP_RESTART_ACTION_COVARIANCE.NSAC05_DUAL_SOURCE_PAIRING_INVARIANT.
Print Assumptions NSE_GP_RESTART_ACTION_COVARIANCE.NSAC20_DUHAMEL_BALANCE_COVARIANT.
