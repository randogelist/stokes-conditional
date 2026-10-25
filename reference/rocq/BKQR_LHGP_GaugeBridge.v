(* The user's donor gauge is preserved verbatim.  The maps change coordinate
   representation through the same decoded coefficient sequence; they do not
   replace the given gauge by the canonical BKQR ground weight. *)
From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import LHGP_Coordinates LHGP_Readouts.
Require Import BKQR_CountableRange BKQR_ShellCoordinates BKQR_ClassificationAudit.
Require Import BKQR_LHGP_CoordinateBridge.

Module BKQR_LHGP_GAUGE_BRIDGE.
Module D := LHGP_Coordinates.
Module L := LHGP_Readouts.
Module B := GP_COUNTABLE_RANGE.
Module S := BKQR_SHELL_COORDINATES.
Module C := BKQR_CLASSIFICATION.
Module Bridge := BKQR_LHGP_COORDINATE_BRIDGE.
Open Scope R_scope.

Definition donor_to_shell (psi:nat->nat->R)(g p:D.Seq) : nat->nat->R :=
  B.gp_encode psi(D.decode g p).
Definition shell_to_donor (psi:nat->nat->R)(g:D.Seq)(U:nat->nat->R) : D.Seq :=
  D.encode g(S.reconstruct psi U).

Section ArbitraryGauge.
Variables q h:R.
Variable lambda:nat->R.
Hypothesis Hq:0<q<1.
Hypothesis Hh:0<h.
Hypothesis Hlambda:forall i,0<=lambda i.
Variable g:D.Seq.
Hypothesis Hg:D.GPNonzero g.
Let psi:=C.bkqr_weights q h lambda Hq Hh.

Theorem ARBITRARY_GAUGE_DONOR_ROUNDTRIP : forall p,
  D.seq_eq(shell_to_donor psi g(donor_to_shell psi g p))p.
Proof.
  intros p i. unfold shell_to_donor,donor_to_shell,D.encode.
  rewrite S.BKSC02_RECONSTRUCT_ENCODE.
  - exact(D.encode_decode g p Hg i).
  - apply C.BKCL02_ZERO_WEIGHT_NONZERO.
Qed.

Theorem ARBITRARY_GAUGE_SHELL_ROUNDTRIP : forall U,
  C.BKQRCompatible q h lambda U ->forall k i,
  donor_to_shell psi g(shell_to_donor psi g U)k i=U k i.
Proof.
  intros U HU k i. unfold donor_to_shell,shell_to_donor,B.gp_encode.
  rewrite(D.decode_encode g(S.reconstruct psi U)Hg i).
  symmetry. exact(proj1(C.BKCL11_RECONSTRUCTION_AND_UNIQUENESS
    q h lambda Hq Hh Hlambda U HU)k i).
Qed.

Theorem ARBITRARY_GAUGE_DONOR_TO_SHELL_L2 : forall p,
  D.GPL2 g p <->C.BKQRState q h lambda(donor_to_shell psi g p).
Proof.
  intro p. split.
  - intro Hp. apply(proj2(C.BKCL10_EXACT_BKQR_STATE_CLASSIFICATION
      q h lambda Hq Hh Hlambda(donor_to_shell psi g p))).
    exists(D.decode g p). split.
    + apply(proj1(Bridge.COORDINATE_L2_BRIDGE _)). exact Hp.
    + intros k i. reflexivity.
  - intros[_ HE]. apply(proj2(Bridge.COORDINATE_L2_BRIDGE _)).
    apply(proj2(B.GPR60_COUNTABLE_SQUARE_SUMMABILITY psi(D.decode g p)
      (donor_to_shell psi g p)(C.BKCL01_SCALAR_PARTITION q h lambda Hq Hh)
      (fun k i=>eq_refl))). exact HE.
Qed.

Theorem ARBITRARY_GAUGE_SHELL_TO_DONOR_L2 : forall U,
  C.BKQRCompatible q h lambda U ->
  (C.BKQRState q h lambda U <->D.GPL2 g(shell_to_donor psi g U)).
Proof.
  intros U HU. unfold shell_to_donor. rewrite D.GP_L2_exact by exact Hg.
  rewrite Bridge.COORDINATE_L2_BRIDGE. split.
  - intros[_ [E HE]]. exists E.
    apply(proj2(C.BKCL12_ALL_ENERGY_BOUNDS q h lambda Hq Hh Hlambda U HU E)). exact HE.
  - intros[E HE]. split;[exact HU|]. exists E.
    apply(proj1(C.BKCL12_ALL_ENERGY_BOUNDS q h lambda Hq Hh Hlambda U HU E)). exact HE.
Qed.

Theorem ARBITRARY_GAUGE_ALL_ENERGY_BOUNDS : forall p E,
  (forall N,D.energy_prefix(D.decode g p)N<=E) <->
  B.ShellBound(donor_to_shell psi g p)E.
Proof.
  intros p E. split;intro HE.
  - apply(proj1(B.GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY psi(D.decode g p)
      (donor_to_shell psi g p)(C.BKCL01_SCALAR_PARTITION q h lambda Hq Hh)
      (fun k i=>eq_refl)E)). intro N. rewrite <-Bridge.ENERGY_PREFIX_BRIDGE. apply HE.
  - intro N. rewrite Bridge.ENERGY_PREFIX_BRIDGE.
    apply(proj2(B.GPR50_FACTORABLE_SHELLS_HAVE_EXACT_ENERGY psi(D.decode g p)
      (donor_to_shell psi g p)(C.BKCL01_SCALAR_PARTITION q h lambda Hq Hh)
      (fun k i=>eq_refl)E)). exact HE.
Qed.

Theorem ARBITRARY_GAUGE_TOTAL_ENERGY_EXACT : forall p E,
  D.EnergyValue(D.decode g p)E <->B.ShellTotal(donor_to_shell psi g p)E.
Proof.
  intros p E. rewrite Bridge.ENERGY_VALUE_BRIDGE.
  apply(B.GPR70_COUNTABLE_TOTAL_ENERGY_EQUALITY psi(D.decode g p)
    (donor_to_shell psi g p)(C.BKCL01_SCALAR_PARTITION q h lambda Hq Hh)
    (fun k i=>eq_refl)).
Qed.

Theorem ARBITRARY_GAUGE_COMPATIBLE_SHELL_ENERGY_EXACT : forall U,
  C.BKQRCompatible q h lambda U ->forall E,
  D.EnergyValue(D.decode g(shell_to_donor psi g U))E <->B.ShellTotal U E.
Proof.
  intros U HU E. unfold shell_to_donor. rewrite D.GP_energy_value_exact by exact Hg.
  change(D.EnergyValue
    (D.decode(Bridge.zero_weight psi)(Bridge.zero_row U))E <->B.ShellTotal U E).
  apply Bridge.CANONICAL_ZERO_ROW_ENERGY_IS_FULL_SHELL_ENERGY; assumption.
Qed.

Theorem ARBITRARY_GAUGE_EXACT_STATE_CLASSIFICATION : forall U,
  C.BKQRState q h lambda U <->exists p,
  D.GPL2 g p /\forall k i,U k i=donor_to_shell psi g p k i.
Proof.
  intro U. split.
  - intro HU. exists(shell_to_donor psi g U). split.
    + apply(proj1(ARBITRARY_GAUGE_SHELL_TO_DONOR_L2 U(proj1 HU))). exact HU.
    + intros k i. symmetry. apply ARBITRARY_GAUGE_SHELL_ROUNDTRIP. exact(proj1 HU).
  - intros[p[Hp HU]].
    apply(proj2(C.BKCL10_EXACT_BKQR_STATE_CLASSIFICATION
      q h lambda Hq Hh Hlambda U)). exists(D.decode g p). split.
    + apply(proj1(Bridge.COORDINATE_L2_BRIDGE _)). exact Hp.
    + exact HU.
Qed.

Theorem ARBITRARY_GAUGE_REPRESENTATIVE_UNIQUE : forall p r,
  (forall k i,donor_to_shell psi g p k i=donor_to_shell psi g r k i) ->D.seq_eq p r.
Proof.
  intros p r Hsame i.
  pose proof(ARBITRARY_GAUGE_DONOR_ROUNDTRIP p i)as Hp.
  pose proof(ARBITRARY_GAUGE_DONOR_ROUNDTRIP r i)as Hr.
  rewrite <-Hp,<-Hr. unfold shell_to_donor,D.encode,S.reconstruct.
  rewrite Hsame. reflexivity.
Qed.

End ArbitraryGauge.

Print Assumptions ARBITRARY_GAUGE_DONOR_ROUNDTRIP.
Print Assumptions ARBITRARY_GAUGE_SHELL_ROUNDTRIP.
Print Assumptions ARBITRARY_GAUGE_TOTAL_ENERGY_EXACT.
Print Assumptions ARBITRARY_GAUGE_EXACT_STATE_CLASSIFICATION.
Print Assumptions ARBITRARY_GAUGE_REPRESENTATIVE_UNIQUE.
End BKQR_LHGP_GAUGE_BRIDGE.
