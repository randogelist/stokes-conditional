From Stdlib Require Import Reals Lra.
Require Import LHGP_Transport LHGP_InitialEnergy.
Require Import BKQR_CountableRange BKQR_EnergyPaths.

Module BKQR_LHGP_TIME_BOUNDARY.
Open Scope R_scope.

(* The zero-start specialization is exact.  This theorem adds no later
   restart time and supplies no integration or full-measure semantics. *)
Theorem BKLT10_INITIAL_IS_EXACT_ZERO_START : forall nu T I E D,
  InitialEnergyInequality nu T I E D <->
  RestartEnergyInequality nu T (fun _ => False) I E D.
Proof.
  intros nu T I E D. split.
  - intros H s t Hst Ht [Hs | Hfalse].
    + subst s. apply H. lra.
    + contradiction.
  - apply RESTART_ENERGY_IMPLIES_INITIAL_ENERGY.
Qed.

(* Here the dissipation is the existing BKQR countable sum of actual
   coordinate Riemann integrals.  Its value is not identified with the
   supplied donor TimeData integral by any definition or theorem here. *)
Definition InitialSpectralEnergy (lambda : nat -> R) (nu T : R)
    (u : R -> nat -> R) : Prop :=
  forall t (H0t : 0 <= t), t <= T ->
    exists E0 Et D,
      GP_COUNTABLE_RANGE.PhysicalTotal (u 0) E0 /\
      GP_COUNTABLE_RANGE.PhysicalTotal (u t) Et /\
      BKQR_ENERGY_PATHS.DissipationTotal lambda u 0 t H0t D /\
      Et + 2 * nu * D <= E0.

Definition InitialNativeEnergy (ell : nat -> R) (nu T : R)
    (U : R -> nat -> nat -> R) : Prop :=
  forall t (H0t : 0 <= t), t <= T ->
    exists E0 Et D,
      GP_COUNTABLE_RANGE.ShellTotal (U 0) E0 /\
      GP_COUNTABLE_RANGE.ShellTotal (U t) Et /\
      BKQR_ENERGY_PATHS.NativeDissipationTotal ell U 0 t H0t D /\
      Et + 2 * nu * D <= E0.

Theorem BKLT20_SPECTRAL_INITIAL_IS_EXACT_ZERO_START :
  forall lambda nu T u,
  InitialSpectralEnergy lambda nu T u <->
  BKQR_ENERGY_PATHS.IntervalEnergy lambda nu T (fun _ => False) u.
Proof.
  intros lambda nu T u. split.
  - intros H s t Hst Hs Ht [Hstart | Hfalse].
    + subst s. exact (H t Hst Ht).
    + contradiction.
  - intros H t H0t Ht.
    exact (H 0 t H0t (Rle_refl 0) Ht (or_introl eq_refl)).
Qed.

Theorem BKLT21_NATIVE_INITIAL_IS_EXACT_ZERO_START :
  forall ell nu T U,
  InitialNativeEnergy ell nu T U <->
  BKQR_ENERGY_PATHS.NativeIntervalEnergy ell nu T (fun _ => False) U.
Proof.
  intros ell nu T U. split.
  - intros H s t Hst Hs Ht [Hstart | Hfalse].
    + subst s. exact (H t Hst Ht).
    + contradiction.
  - intros H t H0t Ht.
    exact (H 0 t H0t (Rle_refl 0) Ht (or_introl eq_refl)).
Qed.

Print Assumptions BKLT10_INITIAL_IS_EXACT_ZERO_START.
Print Assumptions BKLT20_SPECTRAL_INITIAL_IS_EXACT_ZERO_START.
Print Assumptions BKLT21_NATIVE_INITIAL_IS_EXACT_ZERO_START.

End BKQR_LHGP_TIME_BOUNDARY.
