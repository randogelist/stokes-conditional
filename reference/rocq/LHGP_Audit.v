From Stdlib Require Import Reals Lra.
Require Import LHGP_Coordinates LHGP_Readouts LHGP_Transport.

Open Scope R_scope.

(* The principal image theorem has a concrete domain: square-summable real
   sequences. Physical R3 fields are not substituted for this domain here. *)
Theorem LHGP_EXACT_COORDINATE_IMAGE : forall g,
  GPNonzero g -> forall p,
  GPL2 g p <-> exists a,
    CoordinateL2 a /\ seq_eq (encode g a) p.
Proof.
  intros g Hg p. split.
  - apply GP_L2_surjective; exact Hg.
  - intros [a [Ha Henc]]. unfold GPL2.
    assert (Hdec : seq_eq (decode g p) a).
    { intro i. unfold decode. rewrite <- (Henc i).
      unfold encode. field. apply Hg. }
    apply (proj2 (CoordinateL2_ext (decode g p) a Hdec)). exact Ha.
Qed.

Theorem LHGP_L2_HAS_UNIQUE_EXACT_ENERGY : forall a,
  CoordinateL2 a -> exists E,
    EnergyValue a E /\ forall F, EnergyValue a F -> F = E.
Proof.
  intros a Ha. destruct (EnergyValue_exists a Ha) as [E HE].
  exists E. split; [exact HE |].
  intros F HF. apply (EnergyValue_unique a F E); assumption.
Qed.

(* Exact counterexample to reconstructing a state from energy alone. *)
Definition first_coordinate : Seq :=
  fun i => match i with O => 1 | S _ => 0 end.

Theorem LHGP_ENERGY_READOUT_IS_NOT_INJECTIVE :
  (forall n, energy_prefix first_coordinate n =
    energy_prefix (fun i => -first_coordinate i) n) /\
  ~ seq_eq first_coordinate (fun i => -first_coordinate i).
Proof.
  split.
  - intro n. unfold energy_prefix. apply prefix_ext.
    intro i. ring.
  - intro H. specialize (H O). unfold first_coordinate in H. lra.
Qed.

(* These commands expose theorem inputs and transitive foundational axioms.
   Print Assumptions alone does not display explicit theorem premises. *)
Check LHGP_EXACT_COORDINATE_IMAGE.
Check GP_energy_value_exact.
Check CoordinateL2_tail.
Check linear_limit_exists_L2.
Check gp_dissipation_value_transport.
Check LHGP_WEAK_READOUT_IDENTITY_EXACT.
Check LHGP_RESTART_LEDGER_EXACT.
Check LHGP_IMAGE_IFF_DECODED_PROPERTY.

Print Assumptions LHGP_EXACT_COORDINATE_IMAGE.
Print Assumptions LHGP_L2_HAS_UNIQUE_EXACT_ENERGY.
Print Assumptions CoordinateL2_tail.
Print Assumptions linear_limit_exists_L2.
Print Assumptions gp_linear_limit_transport.
Print Assumptions gp_quadratic_limit_transport.
Print Assumptions gp_dissipation_value_transport.
Print Assumptions LHGP_STRONG_INITIAL_TRACE_EXACT.
Print Assumptions LHGP_WEAK_READOUT_IDENTITY_EXACT.
Print Assumptions LHGP_RESTART_LEDGER_EXACT.
Print Assumptions LHGP_IMAGE_IFF_DECODED_PROPERTY.
Print Assumptions LHGP_ENERGY_READOUT_IS_NOT_INJECTIVE.
