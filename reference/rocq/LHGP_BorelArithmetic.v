From Stdlib Require Import Reals Lra Psatz Lia.
Require Import LHGP_Coordinates LHGP_TimeBorel.

Open Scope R_scope.

(* Arithmetic closure of scalar Borel measurability is derived from genuine
   relative Borel sets. No arithmetic closure axiom is introduced. *)

Definition BorelRationalGrid (z : Z) (n : nat) : R :=
  IZR z / INR (S n).

Lemma borel_rational_grid_dense : forall x y : R,
  x < y -> exists n z, x < BorelRationalGrid z n < y.
Proof.
  intros x y Hxy.
  destruct (archimed_cor1 (y-x)) as [N [Hsmall HN]]; [lra|].
  destruct N as [|n]; [lia|].
  set (d := INR (S n)) in *.
  assert (Hd : 0 < d) by (unfold d; apply lt_0_INR; lia).
  set (z := up (d*x)).
  destruct (archimed (d*x)) as [Hz1 Hz2].
  change (d*x < IZR z) in Hz1.
  change (IZR z - d*x <= 1) in Hz2.
  exists n,z; unfold BorelRationalGrid; change (x < IZR z / d < y).
  split.
  - apply (Rmult_lt_reg_r d); [exact Hd|].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra.
  - assert (Hprod : /d * d < (y-x)*d).
    { apply Rmult_lt_compat_r; assumption. }
    rewrite Rinv_l in Hprod by lra.
    apply (Rmult_lt_reg_r d); [exact Hd|].
    unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; nra.
Qed.

Lemma TimeBorel_integer_union : forall T (A : Z -> R -> Prop),
  (forall z, TimeBorel T (A z)) ->
  TimeBorel T (fun t => exists z, A z t).
Proof.
  intros T A HA.
  eapply (TB_ext T
    (fun t => exists n : nat, A (Z.of_nat n) t \/ A (-Z.of_nat n)%Z t)).
  - apply TB_union; intro n.
    apply TimeBorel_union; apply HA.
  - intros t Ht; split.
    + intros [n [Hn|Hn]]; eexists; exact Hn.
    + intros [z Hz]; destruct z as [|p|p].
      * exists O; left; exact Hz.
      * exists (Pos.to_nat p); left; rewrite positive_nat_Z; exact Hz.
      * exists (Pos.to_nat p); right; rewrite positive_nat_Z; exact Hz.
Qed.

Theorem SCALAR_BOREL_ADD : forall T f g,
  ScalarBorelOn T f -> ScalarBorelOn T g ->
  ScalarBorelOn T (fun t => f t + g t).
Proof.
  intros T f g Hf Hg c.
  eapply (TB_ext T
    (fun t => exists n : nat, exists z : Z,
       f t < BorelRationalGrid z n /\
       g t < c - BorelRationalGrid z n)).
  - apply TB_union; intro n.
    apply TimeBorel_integer_union; intro z.
    apply TimeBorel_intersection; [apply Hf|apply Hg].
  - intros t Ht; split.
    + intros [n [z [H1 H2]]]; lra.
    + intro H.
      destruct (borel_rational_grid_dense (f t) (c-g t))
        as [n [z [H1 H2]]]; [lra|].
      exists n,z; split; lra.
Qed.

Theorem SCALAR_BOREL_OPP : forall T f,
  ScalarBorelOn T f -> ScalarBorelOn T (fun t => -f t).
Proof.
  intros T f Hf c.
  eapply (TB_ext T (fun t => -c < f t)).
  - apply TimeBorel_scalar_gt; exact Hf.
  - intros t Ht; lra.
Qed.

Theorem SCALAR_BOREL_SUB : forall T f g,
  ScalarBorelOn T f -> ScalarBorelOn T g ->
  ScalarBorelOn T (fun t => f t - g t).
Proof.
  intros T f g Hf Hg.
  unfold Rminus; apply SCALAR_BOREL_ADD; [exact Hf|].
  apply SCALAR_BOREL_OPP; exact Hg.
Qed.

Lemma borel_square_interval : forall x c,
  0 < c -> (x*x < c <-> -sqrt c < x /\ x < sqrt c).
Proof.
  intros x c Hc.
  pose proof (sqrt_def c (Rlt_le _ _ Hc)) as Hsq.
  pose proof (sqrt_lt_R0 c Hc) as Hpos.
  split.
  - intro H; split; nra.
  - intros [Hlo Hhi]; nra.
Qed.

Theorem SCALAR_BOREL_SQUARE : forall T f,
  ScalarBorelOn T f -> ScalarBorelOn T (fun t => f t*f t).
Proof.
  intros T f Hf c.
  destruct (Rlt_dec 0 c) as [Hc|Hc].
  - eapply (TB_ext T (fun t => -sqrt c < f t /\ f t < sqrt c)).
    + apply TimeBorel_intersection.
      * apply TimeBorel_scalar_gt; exact Hf.
      * apply Hf.
    + intros t Ht; symmetry; apply borel_square_interval; exact Hc.
  - eapply (TB_ext T (fun _ => False)).
    + apply TimeBorel_empty.
    + intros t Ht; split; [contradiction|intro H; nra].
Qed.

Lemma borel_scale_positive : forall a x c,
  0<a -> (x<c/a <-> a*x<c).
Proof.
  intros a x c Ha.
  assert (Hcancel : a*(c/a)=c) by (field; lra).
  split; intro H; nra.
Qed.

Lemma borel_scale_negative : forall a x c,
  a<0 -> (c/a<x <-> a*x<c).
Proof.
  intros a x c Ha.
  assert (Hcancel : a*(c/a)=c) by (field; lra).
  split; intro H; nra.
Qed.

Theorem SCALAR_BOREL_SCALE : forall T f a,
  ScalarBorelOn T f -> ScalarBorelOn T (fun t => a*f t).
Proof.
  intros T f a Hf.
  destruct (Rtotal_order a 0) as [Ha|[Ha|Ha]].
  - intro c; eapply (TB_ext T (fun t => c/a < f t)).
    + apply TimeBorel_scalar_gt; exact Hf.
    + intros t Ht; apply borel_scale_negative; exact Ha.
  - subst a.
    eapply ScalarBorelOn_ext with (f := fun _ => 0).
    + intros t Ht; ring.
    + apply SCALAR_BOREL_CONSTANT.
  - intro c; eapply (TB_ext T (fun t => f t < c/a)).
    + apply Hf.
    + intros t Ht; apply borel_scale_positive; exact Ha.
Qed.

Theorem SCALAR_BOREL_MUL : forall T f g,
  ScalarBorelOn T f -> ScalarBorelOn T g ->
  ScalarBorelOn T (fun t => f t*g t).
Proof.
  intros T f g Hf Hg.
  eapply ScalarBorelOn_ext with
    (f := fun t => (/2)*((f t+g t)*(f t+g t)-f t*f t-g t*g t)).
  - intros t Ht; field.
  - apply SCALAR_BOREL_SCALE.
    apply SCALAR_BOREL_SUB.
    + apply SCALAR_BOREL_SUB.
      * apply SCALAR_BOREL_SQUARE; apply SCALAR_BOREL_ADD; assumption.
      * apply SCALAR_BOREL_SQUARE; exact Hf.
    + apply SCALAR_BOREL_SQUARE; exact Hg.
Qed.

Theorem SCALAR_BOREL_PREFIX : forall T (a : R -> Seq),
  (forall i, ScalarBorelOn T (fun t => a t i)) ->
  forall n, ScalarBorelOn T (fun t => prefix (a t) n).
Proof.
  intros T a Ha n; induction n as [|n IH]; simpl.
  - apply SCALAR_BOREL_CONSTANT.
  - apply SCALAR_BOREL_ADD; [exact IH|apply Ha].
Qed.

Theorem SCALAR_BOREL_ENERGY_PREFIX : forall T (a : R -> Seq),
  (forall i, ScalarBorelOn T (fun t => a t i)) ->
  forall n, ScalarBorelOn T (fun t => energy_prefix (a t) n).
Proof.
  intros T a Ha n; unfold energy_prefix.
  apply SCALAR_BOREL_PREFIX; intro i.
  apply SCALAR_BOREL_SQUARE; apply Ha.
Qed.

Theorem SCALAR_BOREL_DECODE : forall T g (p : R -> Seq),
  (forall i, ScalarBorelOn T (fun t => p t i)) ->
  forall i, ScalarBorelOn T (fun t => decode g (p t) i).
Proof.
  intros T g p Hp i; unfold decode, Rdiv.
  eapply ScalarBorelOn_ext with (f := fun t => /g i * p t i).
  - intros t Ht; ring.
  - apply SCALAR_BOREL_SCALE; apply Hp.
Qed.

Theorem SCALAR_BOREL_ENCODE : forall T g (a : R -> Seq),
  (forall i, ScalarBorelOn T (fun t => a t i)) ->
  forall i, ScalarBorelOn T (fun t => encode g (a t) i).
Proof.
  intros T g a Ha i; unfold encode.
  apply SCALAR_BOREL_SCALE; apply Ha.
Qed.
