From Stdlib Require Import Reals Lra Psatz.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_ClassificationAudit.
Require Import BKQR_TimeIntegrals BKQR_EnergyPaths BKQR_QuadraticTransport.
Require Import BKQR_BilinearKernel BKQR_NonlinearTimeSource BKQR_SourceConstruction.

Module BKQR_NONLINEAR_CLASSIFICATION.
Import GP_COUNTABLE_RANGE BKQR_SHELL_COORDINATES BKQR_TIME_INTEGRALS.
Import BKQR_ENERGY_PATHS BKQR_QUADRATIC_TRANSPORT.
Module C := BKQR_CLASSIFICATION.
Open Scope R_scope.

Section CanonicalQuadraticPaths.
Variables q h nu T : R.
Variable lambda : nat -> R.
Variable K : nat -> nat -> nat -> R.
Hypothesis Hq : 0 < q < 1.
Hypothesis Hh : 0 < h.
Hypothesis Hl : forall i, 0 <= lambda i.
Hypothesis HT : 0 <= T.
Variable Start : R -> Prop.
Let psi := C.bkqr_weights q h lambda Hq Hh.
Let ell := C.bkqr_ell q h.

Theorem BKQN10_CANONICAL_ENCODE_QUADRATIC_ENERGY_PATH : forall u v0 E0,
  SpectralQuadraticEnergyPath K lambda nu T Start u v0 E0 ->
  NativeQuadraticEnergyPath K psi lambda ell nu T Start
    (fun t => gp_encode psi (u t)) (gp_encode psi v0) E0.
Proof.
  intros u v0 E0 Hpath.
  pose proof (proj1 (proj1 Hpath)) as Hu.
  apply (proj1 (BKQT30_EXACT_QUADRATIC_ENERGY_PATH K psi lambda ell nu T Start
    u (fun t => gp_encode psi (u t)) v0 E0 HT
    (C.BKCL01_SCALAR_PARTITION q h lambda Hq Hh)
    (C.BKCL02_ZERO_WEIGHT_NONZERO q h lambda Hq Hh)
    Hu (shell_encode_continuous psi u 0 T Hu)
    (fun t _ => BKSC01_ENCODE_ADJACENT psi lambda ell (u t)
      (C.BKCL04_SCALAR_RAISING q h lambda Hq Hh Hl))
    (fun t k i _ => eq_refl))). exact Hpath.
Qed.

Theorem BKQN11_CANONICAL_DECODE_QUADRATIC_ENERGY_PATH : forall U v0 E0,
  NativeQuadraticEnergyPath K psi lambda ell nu T Start U (gp_encode psi v0) E0 ->
  SpectralQuadraticEnergyPath K lambda nu T Start
    (fun t => reconstruct psi (U t)) v0 E0.
Proof.
  intros U v0 E0 Hpath.
  pose proof (proj1 (proj1 Hpath)) as HU.
  pose proof (proj1 (proj2 (proj1 Hpath))) as HA.
  assert (HF : forall t k i, 0 <= t <= T ->
    U t k i=gp_encode psi (reconstruct psi (U t)) k i).
  { intros t k i Ht. eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION.
    - apply C.BKCL04_SCALAR_RAISING. exact Hl.
    - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
    - apply C.BKCL03_ELL_NONZERO. exact Hq. exact Hh.
    - apply HA. exact Ht. }
  apply (proj2 (BKQT30_EXACT_QUADRATIC_ENERGY_PATH K psi lambda ell nu T Start
    (fun t => reconstruct psi (U t)) U v0 E0 HT
    (C.BKCL01_SCALAR_PARTITION q h lambda Hq Hh)
    (C.BKCL02_ZERO_WEIGHT_NONZERO q h lambda Hq Hh)
    (reconstruct_path_continuous psi U 0 T HU) HU HA HF)). exact Hpath.
Qed.

Theorem BKQN12_EXACT_CANONICAL_QUADRATIC_ENERGY_PATH_CLASSIFICATION :
  forall U (HU : ShellCoordinateContinuous U 0 T),
  (forall t, 0 <= t <= T -> C.BKQRCompatible q h lambda (U t)) ->
  forall v0 E0,
  NativeQuadraticEnergyPath K psi lambda ell nu T Start U (gp_encode psi v0) E0 <->
  SpectralQuadraticEnergyPath K lambda nu T Start
    (fun t => reconstruct psi (U t)) v0 E0.
Proof.
  intros U HU Hcompat v0 E0.
  assert (HA : forall t, 0 <= t <= T -> AdjacentCompatible lambda ell (U t)).
  { intros t Ht. apply (proj1 (C.BKCL05_ADJACENCY_EQUIVALENCE q h lambda Hq Hh (U t))).
    apply Hcompat. exact Ht. }
  assert (HF : forall t k i, 0 <= t <= T ->
    U t k i=gp_encode psi (reconstruct psi (U t)) k i).
  { intros t k i Ht. eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION.
    - apply C.BKCL04_SCALAR_RAISING. exact Hl.
    - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
    - apply C.BKCL03_ELL_NONZERO. exact Hq. exact Hh.
    - apply HA. exact Ht. }
  symmetry. apply BKQT30_EXACT_QUADRATIC_ENERGY_PATH.
  - exact HT.
  - apply C.BKCL01_SCALAR_PARTITION.
  - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
  - apply reconstruct_path_continuous. exact HU.
  - exact HU.
  - exact HA.
  - exact HF.
Qed.
End CanonicalQuadraticPaths.

Theorem BKQN40_CANONICAL_ENERGY_PATH_HAS_OWN_NONLINEAR_SOURCE :
  forall q h nu T lambda K C (Hq : 0 < q < 1) (Hh : 0 < h)
    (HT : 0 <= T) Start U v0 E0,
  (forall i, 0 <= lambda i) -> 0 <= nu ->
  (forall i, BKQR_BILINEAR_KERNEL.SchurBound (K i) (C i)) ->
  forall Hpath : NativeEnergyPath lambda (C.bkqr_ell q h) nu T Start U
    (gp_encode (C.bkqr_weights q h lambda Hq Hh) v0) E0,
  let psi := C.bkqr_weights q h lambda Hq Hh in
  let u := fun t => reconstruct psi (U t) in
  let HU := proj1 Hpath in
  let Hu := reconstruct_path_continuous psi U 0 T HU in
  forall eta k i, exists L,
    SeqLimit (coordinate_source K u 0 T HT Hu eta i) L /\
    SeqLimit (native_source K psi U 0 T HT HU eta k i) (psi k i*L).
Proof.
  intros q h nu T lambda K Cbound Hq Hh HT Start U v0 E0 Hl Hnu HK Hpath.
  cbv zeta. set (psi := C.bkqr_weights q h lambda Hq Hh).
  assert (Hdecoded : SpectralEnergyPath lambda nu T Start
      (fun t => reconstruct psi (U t)) v0 E0).
  { apply (BKEP31_DECODE_ENERGY_PATH psi lambda (C.bkqr_ell q h)
      nu T Start U v0 E0 HT).
    - apply C.BKCL01_SCALAR_PARTITION.
    - apply C.BKCL04_SCALAR_RAISING. exact Hl.
    - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
    - apply C.BKCL03_ELL_NONZERO. exact Hq. exact Hh.
    - exact Hpath. }
  pose proof (BKEP10_ENERGY_INEQUALITY_DERIVES_UNIFORM_CAP lambda nu T Start
    (fun t => reconstruct psi (U t)) v0 E0 Hnu Hdecoded) as Hcap.
  apply (BKQR_SOURCE_CONSTRUCTION.BKQS31_NATIVE_SOURCE_EXISTS_ON_COMPATIBLE_RANGE
    K Cbound psi (fun t => reconstruct psi (U t)) U 0 T E0 HT
    (reconstruct_path_continuous psi U 0 T (proj1 Hpath)) (proj1 Hpath) HK Hcap).
  - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
  - intros t k i Ht. eapply BKSC03_ADJACENCY_FORCES_FACTORIZATION.
    + apply C.BKCL04_SCALAR_RAISING. exact Hl.
    + apply C.BKCL02_ZERO_WEIGHT_NONZERO.
    + apply C.BKCL03_ELL_NONZERO. exact Hq. exact Hh.
    + apply (proj1 (proj2 Hpath)). exact Ht.
Qed.

Check BKQN10_CANONICAL_ENCODE_QUADRATIC_ENERGY_PATH.
Check BKQN11_CANONICAL_DECODE_QUADRATIC_ENERGY_PATH.
Check BKQN12_EXACT_CANONICAL_QUADRATIC_ENERGY_PATH_CLASSIFICATION.
Check BKQN40_CANONICAL_ENERGY_PATH_HAS_OWN_NONLINEAR_SOURCE.
Print Assumptions BKQN10_CANONICAL_ENCODE_QUADRATIC_ENERGY_PATH.
Print Assumptions BKQN11_CANONICAL_DECODE_QUADRATIC_ENERGY_PATH.
Print Assumptions BKQN12_EXACT_CANONICAL_QUADRATIC_ENERGY_PATH_CLASSIFICATION.
Print Assumptions BKQN40_CANONICAL_ENERGY_PATH_HAS_OWN_NONLINEAR_SOURCE.
End BKQR_NONLINEAR_CLASSIFICATION.
