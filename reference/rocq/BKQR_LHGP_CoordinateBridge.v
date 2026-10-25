(* Domain-independent merge of the two actual coordinate constructions.
   The donor diagonal GP coordinate is the zero row of the BKQR shell array.
   Its decoded metric equals the full shell metric because the constructed
   BKQR profile is a countable partition.  No spatial domains or bases are
   identified by this bridge.  All donor sources remain unchanged. *)
From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport LHGP_Hilbert.
Require Import LHGP_Realization LHGP_NativeKQ.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_ClassificationAudit.
Require Import BKQR_PathTopology BKQR_BilinearKernel.

Module BKQR_LHGP_COORDINATE_BRIDGE.
Module D := LHGP_Coordinates.
Module L := LHGP_Readouts.
Module T := LHGP_Transport.
Module H := LHGP_Hilbert.
Module B := GP_COUNTABLE_RANGE.
Module S := BKQR_SHELL_COORDINATES.
Module C := BKQR_CLASSIFICATION.
Module P := BKQR_PATH_TOPOLOGY.
Module K := BKQR_BILINEAR_KERNEL.
Open Scope R_scope.

Lemma PREFIX_BRIDGE : forall f N,D.prefix f N=B.gp_sum N f.
Proof. intros f N. induction N; cbn; [reflexivity|rewrite IHN; reflexivity]. Qed.

Lemma ENERGY_PREFIX_BRIDGE : forall a N,
  D.energy_prefix a N=B.physical_prefix a N.
Proof. intros. apply PREFIX_BRIDGE. Qed.

Theorem COORDINATE_L2_BRIDGE : forall a,
  D.CoordinateL2 a <->B.PhysicalSquareSummable a.
Proof.
  intro a. split; intros[E HE];exists E;intro N.
  - rewrite <-ENERGY_PREFIX_BRIDGE. apply HE.
  - rewrite ENERGY_PREFIX_BRIDGE. apply HE.
Qed.

Theorem ENERGY_VALUE_BRIDGE : forall a E,
  D.EnergyValue a E <->B.PhysicalTotal a E.
Proof.
  intros a E. split;intros[HE Hleast];split.
  - intro N. rewrite <-ENERGY_PREFIX_BRIDGE. apply HE.
  - intros F HF. apply Hleast. intro N. rewrite ENERGY_PREFIX_BRIDGE. apply HF.
  - intro N. rewrite ENERGY_PREFIX_BRIDGE. apply HE.
  - intros F HF. apply Hleast. intro N. rewrite <-ENERGY_PREFIX_BRIDGE. apply HF.
Qed.

Lemma LINEAR_PREFIX_BRIDGE : forall a f N,
  L.linear_prefix a f N=P.pairing_prefix a f N.
Proof. intros. apply PREFIX_BRIDGE. Qed.

Theorem LINEAR_LIMIT_BRIDGE : forall a f l,
  L.linear_limit a f l <->P.PairingLimit a f l.
Proof.
  intros a f l. split;intros Hlim eps Heps;
    destruct(Hlim eps Heps)as[N HN];exists N;intros n Hn.
  - unfold P.pairing_prefix. rewrite <-PREFIX_BRIDGE. apply HN. exact Hn.
  - unfold L.linear_prefix. rewrite PREFIX_BRIDGE. apply HN. exact Hn.
Qed.

Lemma QUADRATIC_PREFIX_BRIDGE : forall a kernel N,
  L.quadratic_prefix a kernel N=K.quadratic_form kernel N a.
Proof.
  intros a kernel N. unfold L.quadratic_prefix,K.quadratic_form,
    K.bilinear_form,K.bilinear_rectangle. rewrite PREFIX_BRIDGE.
  apply B.gp_sum_ext. intros i Hi. rewrite PREFIX_BRIDGE.
  apply B.gp_sum_ext. intros j Hj. ring.
Qed.

Theorem QUADRATIC_LIMIT_BRIDGE : forall a kernel l,
  L.quadratic_limit a kernel l <->
  B.SeqLimit(fun N=>K.quadratic_form kernel N a)l.
Proof.
  intros a kernel l. split;intros Hlim eps Heps;
    destruct(Hlim eps Heps)as[N HN];exists N;intros n Hn.
  - rewrite <-QUADRATIC_PREFIX_BRIDGE. apply HN. exact Hn.
  - unfold L.quadratic_limit in Hlim. rewrite QUADRATIC_PREFIX_BRIDGE. apply HN. exact Hn.
Qed.

Definition zero_row (U:nat->nat->R) : D.Seq := U 0%nat.
Definition zero_weight (psi:nat->nat->R) : D.Seq := psi 0%nat.

Theorem ZERO_ROW_IS_DONOR_ENCODING : forall psi a,
  D.seq_eq(zero_row(B.gp_encode psi a))(D.encode(zero_weight psi)a).
Proof. intros psi a i. reflexivity. Qed.

Theorem ZERO_ROW_DECODE_IS_BKQR_RECONSTRUCTION : forall psi U,
  D.seq_eq(D.decode(zero_weight psi)(zero_row U))(S.reconstruct psi U).
Proof. intros psi U i. reflexivity. Qed.

Theorem ZERO_ROW_NATIVE_METRIC_IS_RECONSTRUCTED_PAIRING : forall psi U V N,
  LHGP_NativeKQ.NativeGPMetric N(zero_weight psi)(zero_row U)(zero_row V)=
  P.pairing_prefix(S.reconstruct psi U)(S.reconstruct psi V)N.
Proof.
  intros. unfold LHGP_NativeKQ.NativeGPMetric.
  rewrite LHGP_NativeKQ.NativeDot_linear_prefix. apply LINEAR_PREFIX_BRIDGE.
Qed.

Section CanonicalProfile.
Variables q h : R.
Variable lambda:nat->R.
Hypothesis Hq:0<q<1.
Hypothesis Hh:0<h.
Hypothesis Hlambda:forall i,0<=lambda i.
Let psi:=C.bkqr_weights q h lambda Hq Hh.
Let g:=zero_weight psi.

Theorem CANONICAL_ZERO_WEIGHT_IS_DONOR_ADMISSIBLE : D.GPNonzero g.
Proof. intro i. apply C.BKCL02_ZERO_WEIGHT_NONZERO. Qed.

Theorem CANONICAL_ZERO_ROW_ALL_ENERGY_BOUNDS : forall U,
  C.BKQRCompatible q h lambda U ->forall E,
  (forall N,D.energy_prefix(D.decode g(zero_row U))N<=E) <->B.ShellBound U E.
Proof.
  intros U HU E.
  assert (Hbounds: B.PhysicalBound(S.reconstruct psi U)E <->B.ShellBound U E).
  { apply C.BKCL12_ALL_ENERGY_BOUNDS; assumption. }
  split;intro Hbound.
  - apply(proj1 Hbounds). intro N. rewrite <-ENERGY_PREFIX_BRIDGE. apply Hbound.
  - intro N. rewrite ENERGY_PREFIX_BRIDGE. apply(proj2 Hbounds). exact Hbound.
Qed.

Theorem CANONICAL_ZERO_ROW_L2_IFF_FULL_SHELL_L2 : forall U,
  C.BKQRCompatible q h lambda U ->
  (D.GPL2 g(zero_row U) <->B.ShellSquareSummable U).
Proof.
  intros U HU. split;intros[E HE];exists E.
  - apply(proj1(CANONICAL_ZERO_ROW_ALL_ENERGY_BOUNDS U HU E)). exact HE.
  - apply(proj2(CANONICAL_ZERO_ROW_ALL_ENERGY_BOUNDS U HU E)). exact HE.
Qed.

Theorem CANONICAL_ZERO_ROW_ENERGY_IS_FULL_SHELL_ENERGY : forall U,
  C.BKQRCompatible q h lambda U ->forall E,
  D.EnergyValue(D.decode g(zero_row U))E <->B.ShellTotal U E.
Proof.
  intros U HU E. split;intros[HE Hleast];split.
  - apply(proj1(CANONICAL_ZERO_ROW_ALL_ENERGY_BOUNDS U HU E)). exact HE.
  - intros F HF. apply Hleast.
    apply(proj2(CANONICAL_ZERO_ROW_ALL_ENERGY_BOUNDS U HU F)). exact HF.
  - apply(proj2(CANONICAL_ZERO_ROW_ALL_ENERGY_BOUNDS U HU E)). exact HE.
  - intros F HF. apply Hleast.
    apply(proj1(CANONICAL_ZERO_ROW_ALL_ENERGY_BOUNDS U HU F)). exact HF.
Qed.

Definition canonical_lift (p:D.Seq) : nat->nat->R :=
  B.gp_encode psi(D.decode g p).

Theorem CANONICAL_LIFT_FROM_DONOR_L2 : forall p,
  D.GPL2 g p ->C.BKQRState q h lambda(canonical_lift p) /\
  D.seq_eq(zero_row(canonical_lift p))p.
Proof.
  intros p Hp. split.
  - apply(proj2(C.BKCL10_EXACT_BKQR_STATE_CLASSIFICATION q h lambda Hq Hh Hlambda
      (canonical_lift p))). exists(D.decode g p). split.
    + apply(proj1(COORDINATE_L2_BRIDGE _)). exact Hp.
    + intros k i. reflexivity.
  - apply D.encode_decode. apply CANONICAL_ZERO_WEIGHT_IS_DONOR_ADMISSIBLE.
Qed.

Theorem CANONICAL_ZERO_ROW_RETAINS_EVERY_SHELL : forall U,
  C.BKQRCompatible q h lambda U ->forall k i,
  canonical_lift(zero_row U)k i=U k i.
Proof.
  intros U HU k i. symmetry.
  exact(proj1(C.BKCL11_RECONSTRUCTION_AND_UNIQUENESS q h lambda Hq Hh Hlambda U HU)k i).
Qed.

Theorem CANONICAL_STATE_IFF_DONOR_ZERO_ROW : forall U,
  C.BKQRState q h lambda U <->
  C.BKQRCompatible q h lambda U /\D.GPL2 g(zero_row U).
Proof.
  intro U. split;intros[HU HE];split;try exact HU.
  - apply(proj2(CANONICAL_ZERO_ROW_L2_IFF_FULL_SHELL_L2 U HU)). exact HE.
  - apply(proj1(CANONICAL_ZERO_ROW_L2_IFF_FULL_SHELL_L2 U HU)). exact HE.
Qed.

Theorem CANONICAL_DONOR_PAIRING_IS_FULL_SHELL_PAIRING : forall U V l,
  C.BKQRState q h lambda U ->C.BKQRState q h lambda V ->
  (L.linear_limit(D.decode g(zero_row U))(D.decode g(zero_row V))l <->
   P.ShellPairingLimit U V l).
Proof.
  intros U V l [HU HUE] [HV HVE]. rewrite LINEAR_LIMIT_BRIDGE.
  apply(P.factorable_pairing_iff psi(S.reconstruct psi U)(S.reconstruct psi V)U V l).
  - apply C.BKCL01_SCALAR_PARTITION.
  - apply(proj1(COORDINATE_L2_BRIDGE _)).
    apply(proj2(CANONICAL_ZERO_ROW_L2_IFF_FULL_SHELL_L2 U HU)). exact HUE.
  - apply(proj1(COORDINATE_L2_BRIDGE _)).
    apply(proj2(CANONICAL_ZERO_ROW_L2_IFF_FULL_SHELL_L2 V HV)). exact HVE.
  - intros k i. symmetry. apply CANONICAL_ZERO_ROW_RETAINS_EVERY_SHELL. exact HU.
  - intros k i. symmetry. apply CANONICAL_ZERO_ROW_RETAINS_EVERY_SHELL. exact HV.
Qed.

Theorem CANONICAL_DONOR_QUADRATIC_READOUT : forall U kernel N,
  L.quadratic_prefix(D.decode g(zero_row U))kernel N=
  K.quadratic_form kernel N(S.reconstruct psi U).
Proof. intros. apply QUADRATIC_PREFIX_BRIDGE. Qed.

Theorem CANONICAL_PATH_UNIFORM_ENERGY_EXACT : forall U Tbound E,
  (forall t,0<=t<=Tbound ->C.BKQRCompatible q h lambda(U t)) ->
  (T.GPEnergyBound g(fun t=>zero_row(U t))Tbound E <->
    forall t,0<=t<=Tbound ->B.ShellBound(U t)E).
Proof.
  intros U Tbound E Hcomp. split;intros HE t Ht.
  - apply(proj1(CANONICAL_ZERO_ROW_ALL_ENERGY_BOUNDS(U t)(Hcomp t Ht)E)).
    apply HE. exact Ht.
  - apply(proj2(CANONICAL_ZERO_ROW_ALL_ENERGY_BOUNDS(U t)(Hcomp t Ht)E)).
    apply HE. exact Ht.
Qed.

(* This last theorem is intentionally conditional on the donor's abstract
   Hilbert carrier, orthonormal separating family, and completeness. *)
Theorem CANONICAL_HILBERT_NORM_IS_FULL_SHELL_ENERGY : forall hd
  (basis:H.OrthonormalBasis hd),H.HComplete hd ->forall x:H.HCarrier hd,
  B.ShellTotal(B.gp_encode psi(H.HAnalysis basis x))(H.HNorm hd x).
Proof.
  intros hd basis Hcomplete x.
  apply(proj1(B.GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY psi(H.HAnalysis basis x)
    (B.gp_encode psi(H.HAnalysis basis x))
    (C.BKCL01_SCALAR_PARTITION q h lambda Hq Hh)(fun k i=>eq_refl)(H.HNorm hd x))).
  apply(proj1(ENERGY_VALUE_BRIDGE _ _)). apply H.HAnalysis_parseval. exact Hcomplete.
Qed.

End CanonicalProfile.

Print Assumptions CANONICAL_ZERO_ROW_ENERGY_IS_FULL_SHELL_ENERGY.
Print Assumptions CANONICAL_LIFT_FROM_DONOR_L2.
Print Assumptions CANONICAL_DONOR_PAIRING_IS_FULL_SHELL_PAIRING.
Print Assumptions CANONICAL_HILBERT_NORM_IS_FULL_SHELL_ENERGY.
End BKQR_LHGP_COORDINATE_BRIDGE.
