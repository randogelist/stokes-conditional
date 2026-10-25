
From Stdlib Require Import Reals Lra Psatz Lists.List ZArith Lia Rtrigo1.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Require Import awpi_nse_lh_torus_fourier_tests_v0_44_3.

Import ListNotations.
Open Scope R_scope.

Module NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.

Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.
Module L44 := NSE_LH_TORUS_FOURIER_TESTS.

(* ===================================================================== *)
(* Concrete scalar Fourier atoms on T^3                                   *)
(* ===================================================================== *)

Record R3 : Type := {
  rx : R;
  ry : R;
  rz : R
}.

Definition phase (k : L44.Z3) (x : R3) : R :=
  IZR (L44.kx k) * rx x
  + IZR (L44.ky k) * ry x
  + IZR (L44.kz k) * rz x.

Definition torus_atom (k : L44.Z3) (x : R3) : CH.C2 :=
  (cos (phase k x), sin (phase k x)).

Theorem LH45_00_PHASE_ADD :
  forall p q : L44.Z3,
  forall x : R3,
    phase (L44.z3_add p q) x
    =
    phase p x + phase q x.
Proof.
  intros [px py pz] [qx qy qz] [x y z].
  unfold phase, L44.z3_add.
  simpl.
  repeat rewrite plus_IZR.
  ring.
Qed.

Theorem LH45_01_TORUS_ATOM_PRODUCT :
  forall p q : L44.Z3,
  forall x : R3,
    CH.cmul (torus_atom p x) (torus_atom q x)
    =
    torus_atom (L44.z3_add p q) x.
Proof.
  intros p q x.
  unfold torus_atom.
  rewrite LH45_00_PHASE_ADD.
  unfold CH.cmul, CH.cre, CH.cim.
  simpl.
  rewrite cos_plus.
  rewrite sin_plus.
  f_equal; ring.
Qed.

Definition cabs2 (z : CH.C2) : R :=
  CH.cre z * CH.cre z + CH.cim z * CH.cim z.

Theorem LH45_02_TORUS_ATOM_UNIT_NORM :
  forall k : L44.Z3,
  forall x : R3,
    cabs2 (torus_atom k x) = 1.
Proof.
  intros k x.
  unfold cabs2, torus_atom, CH.cre, CH.cim.
  simpl.
  pose proof (sin2_cos2 (phase k x)) as H.
  unfold Rsqr in H.
  nra.
Qed.

(* ===================================================================== *)
(* Small exact C2 algebra used by finite polynomial convolution            *)
(* ===================================================================== *)

Definition czero : CH.C2 := (0, 0).

Theorem LH45_10_CADD_ASSOC :
  forall a b c : CH.C2,
    CH.cadd (CH.cadd a b) c
    =
    CH.cadd a (CH.cadd b c).
Proof.
  intros [ar ai] [br bi] [cr ci].
  unfold CH.cadd, CH.cre, CH.cim.
  simpl.
  f_equal; ring.
Qed.

Theorem LH45_11_CMUL_ASSOC :
  forall a b c : CH.C2,
    CH.cmul (CH.cmul a b) c
    =
    CH.cmul a (CH.cmul b c).
Proof.
  intros [ar ai] [br bi] [cr ci].
  unfold CH.cmul, CH.cre, CH.cim.
  simpl.
  f_equal; ring.
Qed.

Theorem LH45_12_CMUL_COMM :
  forall a b : CH.C2,
    CH.cmul a b = CH.cmul b a.
Proof.
  intros [ar ai] [br bi].
  unfold CH.cmul, CH.cre, CH.cim.
  simpl.
  f_equal; ring.
Qed.

Theorem LH45_13_CMUL_ADD_DISTR_L :
  forall a b c : CH.C2,
    CH.cmul a (CH.cadd b c)
    =
    CH.cadd (CH.cmul a b) (CH.cmul a c).
Proof.
  intros [ar ai] [br bi] [cr ci].
  unfold CH.cmul, CH.cadd, CH.cre, CH.cim.
  simpl.
  f_equal; ring.
Qed.

Theorem LH45_14_CMUL_ADD_DISTR_R :
  forall a b c : CH.C2,
    CH.cmul (CH.cadd a b) c
    =
    CH.cadd (CH.cmul a c) (CH.cmul b c).
Proof.
  intros.
  rewrite (LH45_12_CMUL_COMM (CH.cadd a b) c).
  rewrite LH45_13_CMUL_ADD_DISTR_L.
  rewrite (LH45_12_CMUL_COMM c a).
  rewrite (LH45_12_CMUL_COMM c b).
  reflexivity.
Qed.

Theorem LH45_15_CMUL_ZERO_R :
  forall a : CH.C2,
    CH.cmul a czero = czero.
Proof.
  intros [ar ai].
  unfold CH.cmul, CH.cre, CH.cim, czero.
  simpl.
  f_equal; ring.
Qed.

Theorem LH45_16_CMUL_ZERO_L :
  forall a : CH.C2,
    CH.cmul czero a = czero.
Proof.
  intro a.
  rewrite LH45_12_CMUL_COMM.
  apply LH45_15_CMUL_ZERO_R.
Qed.

Theorem LH45_17_CMUL_FOUR_REARRANGE :
  forall a b c d : CH.C2,
    CH.cmul (CH.cmul a b) (CH.cmul c d)
    =
    CH.cmul (CH.cmul a c) (CH.cmul b d).
Proof.
  intros [ar ai] [br bi] [cr ci] [dr di].
  unfold CH.cmul, CH.cre, CH.cim.
  simpl.
  f_equal; ring.
Qed.

(* ===================================================================== *)
(* Finite scalar Fourier polynomials                                      *)
(* ===================================================================== *)

Definition FourierTerm : Type := (L44.Z3 * CH.C2)%type.

Definition term_mode (t : FourierTerm) : L44.Z3 := fst t.
Definition term_coeff (t : FourierTerm) : CH.C2 := snd t.

Definition eval_term (t : FourierTerm) (x : R3) : CH.C2 :=
  CH.cmul (term_coeff t) (torus_atom (term_mode t) x).

Definition term_mul (a b : FourierTerm) : FourierTerm :=
  (L44.z3_add (term_mode a) (term_mode b),
   CH.cmul (term_coeff a) (term_coeff b)).

Theorem LH45_20_TERM_MUL_MODE :
  forall a b : FourierTerm,
    term_mode (term_mul a b)
    =
    L44.z3_add (term_mode a) (term_mode b).
Proof.
  intros [ak ac] [bk bc].
  reflexivity.
Qed.

Theorem LH45_21_TERM_MUL_EVAL :
  forall a b : FourierTerm,
  forall x : R3,
    eval_term (term_mul a b) x
    =
    CH.cmul (eval_term a x) (eval_term b x).
Proof.
  intros [ak ac] [bk bc] x.
  unfold eval_term, term_mul, term_mode, term_coeff.
  simpl.
  rewrite <- LH45_01_TORUS_ATOM_PRODUCT.
  apply LH45_17_CMUL_FOUR_REARRANGE.
Qed.

Fixpoint poly_eval
  (P : list FourierTerm)
  (x : R3) : CH.C2 :=
  match P with
  | [] => czero
  | a :: P' =>
      CH.cadd (eval_term a x) (poly_eval P' x)
  end.

Fixpoint left_products
  (a : FourierTerm)
  (Q : list FourierTerm) : list FourierTerm :=
  match Q with
  | [] => []
  | b :: Q' =>
      term_mul a b :: left_products a Q'
  end.

Fixpoint product_terms
  (P Q : list FourierTerm) : list FourierTerm :=
  match P with
  | [] => []
  | a :: P' =>
      left_products a Q ++ product_terms P' Q
  end.

Theorem LH45_22_POLY_EVAL_APPEND :
  forall P Q : list FourierTerm,
  forall x : R3,
    poly_eval (P ++ Q) x
    =
    CH.cadd (poly_eval P x) (poly_eval Q x).
Proof.
  intros P Q x.
  induction P as [|a P IH].
  - simpl.
    unfold czero, CH.cadd, CH.cre, CH.cim.
    destruct (poly_eval Q x) as [qr qi].
    simpl.
    f_equal; ring.
  - simpl.
    rewrite IH.
    symmetry.
    apply LH45_10_CADD_ASSOC.
Qed.

Theorem LH45_23_LEFT_PRODUCTS_EVAL :
  forall a : FourierTerm,
  forall Q : list FourierTerm,
  forall x : R3,
    poly_eval (left_products a Q) x
    =
    CH.cmul (eval_term a x) (poly_eval Q x).
Proof.
  intros a Q x.
  induction Q as [|b Q IH].
  - simpl.
    symmetry.
    apply LH45_15_CMUL_ZERO_R.
  - simpl.
    rewrite LH45_21_TERM_MUL_EVAL.
    rewrite IH.
    symmetry.
    apply LH45_13_CMUL_ADD_DISTR_L.
Qed.

Theorem LH45_24_FINITE_FOURIER_PRODUCT_IS_CONVOLUTION :
  forall P Q : list FourierTerm,
  forall x : R3,
    poly_eval (product_terms P Q) x
    =
    CH.cmul (poly_eval P x) (poly_eval Q x).
Proof.
  intros P Q x.
  induction P as [|a P IH].
  - simpl.
    symmetry.
    apply LH45_16_CMUL_ZERO_L.
  - simpl.
    rewrite LH45_22_POLY_EVAL_APPEND.
    rewrite LH45_23_LEFT_PRODUCTS_EVAL.
    rewrite IH.
    symmetry.
    apply LH45_14_CMUL_ADD_DISTR_R.
Qed.

(* Each generated product term has the exact lattice support p+q by
   construction, while LH45_24 proves that the finite sum of those terms is
   literally the pointwise product of the two Fourier polynomials.

   This is the finite algebraic convolution theorem required by the
   Galerkin/Fourier frontend.  What still remains for NSE is the vector
   derivative/Leray-projection decoration and the analytic L2 completion
   (Parseval/Plancherel). *)

Definition RemainingVectorNSEConvolutionAndParsevalFrontier : Prop := True.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.

Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.R3.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.phase.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.torus_atom.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.LH45_00_PHASE_ADD.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.LH45_01_TORUS_ATOM_PRODUCT.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.LH45_02_TORUS_ATOM_UNIT_NORM.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.FourierTerm.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.term_mul.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.LH45_20_TERM_MUL_MODE.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.LH45_21_TERM_MUL_EVAL.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.poly_eval.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.left_products.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.product_terms.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.LH45_24_FINITE_FOURIER_PRODUCT_IS_CONVOLUTION.
Check NSE_LH_FOURIER_POLYNOMIAL_CONVOLUTION.RemainingVectorNSEConvolutionAndParsevalFrontier.
