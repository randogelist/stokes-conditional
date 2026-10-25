From Stdlib Require Import Reals List Lra Psatz.
Import ListNotations.
Open Scope R_scope.

(* Actual real coordinate fields and compactly supported smooth scalar tests.
   Smoothness is certified by jointly continuous iterated coordinate partials.
   No spatial integral, L2 completion, or PDE realization is assumed here. *)
Record R3Point := { R3x : R; R3y : R; R3z : R }.
Inductive Axis3 := R3AxisX | R3AxisY | R3AxisZ.
Definition R3ScalarField := R3Point -> R.

Definition R3Shift (p : R3Point) (a : Axis3) (t : R) : R3Point :=
  match a with
  | R3AxisX => {| R3x := R3x p + t; R3y := R3y p; R3z := R3z p |}
  | R3AxisY => {| R3x := R3x p; R3y := R3y p + t; R3z := R3z p |}
  | R3AxisZ => {| R3x := R3x p; R3y := R3y p; R3z := R3z p + t |}
  end.

Definition R3Close (p q : R3Point) (delta : R) : Prop :=
  Rabs (R3x p - R3x q) < delta /\
  Rabs (R3y p - R3y q) < delta /\
  Rabs (R3z p - R3z q) < delta.
Definition R3Continuous (f : R3ScalarField) : Prop :=
  forall p epsilon, 0 < epsilon ->
  exists delta, 0 < delta /\
    forall q, R3Close q p delta -> Rabs (f q - f p) < epsilon.
Definition R3Outside (radius : R) (p : R3Point) : Prop :=
  radius < Rabs (R3x p) \/ radius < Rabs (R3y p) \/
  radius < Rabs (R3z p).
Definition R3Supported (radius : R) (f : R3ScalarField) : Prop :=
  forall p, R3Outside radius p -> f p = 0.

Lemma R3_SHIFT_ZERO : forall p a, R3Shift p a 0 = p.
Proof. intros [x y z] a; destruct a; simpl; f_equal; apply Rplus_0_r. Qed.

Lemma R3_CLOSE_MONO : forall p q d e,
  d <= e -> R3Close p q d -> R3Close p q e.
Proof. unfold R3Close; intros p q d e H [Hx [Hy Hz]]; repeat split; lra. Qed.

Lemma R3_CONTINUOUS_ZERO : R3Continuous (fun _ => 0).
Proof.
  intros p e He; exists 1; split; [lra|].
  intros q Hq; replace (0-0) with 0 by ring; rewrite Rabs_R0; exact He.
Qed.

Lemma R3_CONTINUOUS_ADD : forall f g,
  R3Continuous f -> R3Continuous g ->
  R3Continuous (fun p => f p + g p).
Proof.
  intros f g Hf Hg p e He.
  destruct (Hf p (e/2)) as [df [Hdf Hf']]; [lra|].
  destruct (Hg p (e/2)) as [dg [Hdg Hg']]; [lra|].
  exists (Rmin df dg); split.
  - unfold Rmin; destruct (Rle_dec df dg); lra.
  - intros q Hq.
    assert (Hqf : R3Close q p df).
    { eapply R3_CLOSE_MONO; [apply Rmin_l|exact Hq]. }
    assert (Hqg : R3Close q p dg).
    { eapply R3_CLOSE_MONO; [apply Rmin_r|exact Hq]. }
    specialize (Hf' q Hqf); specialize (Hg' q Hqg).
    replace (f q + g q - (f p + g p))
      with ((f q - f p) + (g q - g p)) by ring.
    eapply Rle_lt_trans; [apply Rabs_triang|lra].
Qed.

Lemma R3_CONTINUOUS_SCALE : forall c f,
  R3Continuous f -> R3Continuous (fun p => c * f p).
Proof.
  intros c f Hf p e He.
  assert (Hc : 0 <= Rabs c) by apply Rabs_pos.
  assert (Hden : 0 < Rabs c + 1) by lra.
  assert (He' : 0 < e / (Rabs c + 1)) by (apply Rdiv_lt_0_compat; assumption).
  destruct (Hf p (e/(Rabs c+1)) He') as [d [Hd Hf']].
  exists d; split; [exact Hd|].
  intros q Hq; specialize (Hf' q Hq).
  replace (c * f q - c * f p) with (c * (f q - f p)) by ring.
  rewrite Rabs_mult.
  assert (Habs : 0 <= Rabs (f q - f p)) by apply Rabs_pos.
  assert (Hcancel : (Rabs c+1)*(e/(Rabs c+1))=e).
  { field; lra. }
  nra.
Qed.

Lemma R3_SUPPORTED_MONO : forall r s f,
  r <= s -> R3Supported r f -> R3Supported s f.
Proof.
  unfold R3Supported, R3Outside.
  intros r s f Hrs Hf p [Hx|[Hy|Hz]]; apply Hf;
    [left|right; left|right; right]; lra.
Qed.

(* Lists are read from their tail: a::w differentiates the w-jet along a.
   Appending [a] therefore represents differentiating the base test along a
   first, without assuming equality of mixed derivatives. *)
Record R3SmoothTest := {
  R3Jet : list Axis3 -> R3ScalarField;
  R3JetContinuous : forall w, R3Continuous (R3Jet w);
  R3JetDerivative : forall w a p,
    derivable_pt_lim (fun t => R3Jet w (R3Shift p a t)) 0
      (R3Jet (a :: w) p);
  R3Radius : R;
  R3RadiusPositive : 0 < R3Radius;
  R3JetSupport : forall w, R3Supported R3Radius (R3Jet w)
}.

Definition R3TestValue (f : R3SmoothTest) : R3ScalarField := R3Jet f [].

Definition R3TestZero : R3SmoothTest.
Proof.
  refine {| R3Jet := fun _ _ => 0; R3Radius := 1 |}.
  - intro w; apply R3_CONTINUOUS_ZERO.
  - intros w a p; apply derivable_pt_lim_const.
  - lra.
  - intros w p Hp; reflexivity.
Defined.

Definition R3TestAdd (f g : R3SmoothTest) : R3SmoothTest.
Proof.
  refine {| R3Jet := fun w p => R3Jet f w p + R3Jet g w p;
            R3Radius := Rmax (R3Radius f) (R3Radius g) |}.
  - intro w; apply R3_CONTINUOUS_ADD; apply R3JetContinuous.
  - intros w a p; apply derivable_pt_lim_plus; apply R3JetDerivative.
  - eapply Rlt_le_trans; [apply (R3RadiusPositive f)|apply Rmax_l].
  - intros w p Hp.
    assert (Hf : R3Jet f w p = 0).
    { eapply R3_SUPPORTED_MONO; [apply Rmax_l|apply R3JetSupport|exact Hp]. }
    assert (Hg : R3Jet g w p = 0).
    { eapply R3_SUPPORTED_MONO; [apply Rmax_r|apply R3JetSupport|exact Hp]. }
    rewrite Hf, Hg; ring.
Defined.

Definition R3TestScale (c : R) (f : R3SmoothTest) : R3SmoothTest.
Proof.
  refine {| R3Jet := fun w p => c * R3Jet f w p;
            R3Radius := R3Radius f |}.
  - intro w; apply R3_CONTINUOUS_SCALE; apply R3JetContinuous.
  - intros w a p; apply derivable_pt_lim_scal; apply R3JetDerivative.
  - apply R3RadiusPositive.
  - intros w p Hp; rewrite (R3JetSupport f w p Hp); ring.
Defined.

Definition R3TestDerivative (a : Axis3) (f : R3SmoothTest) : R3SmoothTest.
Proof.
  refine {| R3Jet := fun w => R3Jet f (w ++ [a]);
            R3Radius := R3Radius f |}.
  - intro w; apply R3JetContinuous.
  - intros w b p; simpl; apply R3JetDerivative.
  - apply R3RadiusPositive.
  - intro w; apply R3JetSupport.
Defined.

Theorem R3_TEST_CONTINUOUS : forall f, R3Continuous (R3TestValue f).
Proof. intro f; apply R3JetContinuous. Qed.
Theorem R3_TEST_COMPACT_BOX_SUPPORT : forall f,
  0 < R3Radius f /\ R3Supported (R3Radius f) (R3TestValue f).
Proof. intro f; split; [apply R3RadiusPositive|apply R3JetSupport]. Qed.
Theorem R3_TEST_ACTUAL_PARTIAL : forall f a p,
  derivable_pt_lim (fun t => R3TestValue f (R3Shift p a t)) 0
    (R3TestValue (R3TestDerivative a f) p).
Proof. intros f a p; apply (R3JetDerivative f [] a p). Qed.
Theorem R3_TEST_ZERO_VALUE : forall p, R3TestValue R3TestZero p = 0.
Proof. reflexivity. Qed.
Theorem R3_TEST_ADD_VALUE : forall f g p,
  R3TestValue (R3TestAdd f g) p = R3TestValue f p + R3TestValue g p.
Proof. reflexivity. Qed.
Theorem R3_TEST_SCALE_VALUE : forall c f p,
  R3TestValue (R3TestScale c f) p = c * R3TestValue f p.
Proof. reflexivity. Qed.
Theorem R3_TEST_DERIVATIVE_VALUE : forall a f p,
  R3TestValue (R3TestDerivative a f) p = R3Jet f [a] p.
Proof. reflexivity. Qed.
Theorem R3_TEST_DERIVATIVE_ZERO : forall a p,
  R3TestValue (R3TestDerivative a R3TestZero) p = 0.
Proof. reflexivity. Qed.
Theorem R3_TEST_DERIVATIVE_ADD : forall a f g p,
  R3TestValue (R3TestDerivative a (R3TestAdd f g)) p =
  R3TestValue (R3TestDerivative a f) p +
  R3TestValue (R3TestDerivative a g) p.
Proof. reflexivity. Qed.
Theorem R3_TEST_DERIVATIVE_SCALE : forall a c f p,
  R3TestValue (R3TestDerivative a (R3TestScale c f)) p =
  c * R3TestValue (R3TestDerivative a f) p.
Proof. reflexivity. Qed.
Theorem R3_TEST_DERIVATIVE_RADIUS : forall a f,
  R3Radius (R3TestDerivative a f) = R3Radius f.
Proof. reflexivity. Qed.
Theorem R3_TEST_ALL_ITERATED_PARTIALS_CONTINUOUS : forall f w,
  R3Continuous (R3Jet f w).
Proof. apply R3JetContinuous. Qed.
Theorem R3_TEST_ALL_ITERATED_PARTIALS_SUPPORTED : forall f w,
  R3Supported (R3Radius f) (R3Jet f w).
Proof. apply R3JetSupport. Qed.
Theorem R3_TEST_DERIVATIVE_JET : forall a f w p,
  R3Jet (R3TestDerivative a f) w p = R3Jet f (w ++ [a]) p.
Proof. reflexivity. Qed.
