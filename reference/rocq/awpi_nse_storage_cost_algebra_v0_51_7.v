From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import awpi_nse_finite_shell_algebra_v0_48_4.
Require Import awpi_nse_shell_occupancy_algebra_v0_48_4.
Require Import awpi_nse_direct_gp_shell_occupancy_v0_48_4.

Module NSE_STORAGE_COST_ALGEBRA.
Import NSE_FINITE_SHELL_ALGEBRA NSE_SHELL_OCCUPANCY_ALGEBRA.
Module O := NSE_DIRECT_GP_SHELL_OCCUPANCY.
Open Scope R_scope.

Definition profile y r beta S z := z*y-r-beta*z*z*S.
Definition folded_cost lambda y S r beta :=
  lambda*lambda*pos (y-r-beta*S).
Definition passage_integrand y r beta S z := pos (profile y r beta S z)/z.

Lemma NSST00_POS_SCALE : forall c x,
  0 <= c -> pos (c*x)=c*pos x.
Proof.
  intros c x Hc. destruct (Rle_dec x 0) as [Hx|Hx].
  - rewrite (NSFA12_POS_ZERO x Hx).
    rewrite NSFA12_POS_ZERO; [ring|].
    pose proof (Rmult_le_compat_l c x 0 Hc Hx); lra.
  - rewrite (NSFA13_POS_ID x ltac:(lra)).
    apply NSFA13_POS_ID. apply Rmult_le_pos; lra.
Qed.

Lemma NSST01_POS_NESTED : forall x b,
  0 <= b -> pos (pos x-b)=pos (x-b).
Proof.
  intros x b Hb. destruct (Rle_dec x 0) as [Hx|Hx].
  - rewrite (NSFA12_POS_ZERO x Hx).
    rewrite (NSFA12_POS_ZERO (0-b)) by lra.
    rewrite (NSFA12_POS_ZERO (x-b)) by lra. reflexivity.
  - rewrite (NSFA13_POS_ID x) by lra. reflexivity.
Qed.

Lemma NSST02_TOTAL_DIV : forall f n c,
  total f n/c=total (fun j => f j/c) n.
Proof.
  intros f n c. induction n as [|n IH]; simpl.
  - unfold Rdiv; ring.
  - unfold Rdiv in *; rewrite Rmult_plus_distr_r, IH; reflexivity.
Qed.

Theorem NSST10_EXACT_OLD_UNPAID_IDENTITY : forall lambda A U r cap,
  0 < r -> 0 <= cap ->
  unpaid lambda A U r cap/(4*r)=
  folded_cost lambda (A/lambda) (U*U) r (cap/(4*r)).
Proof.
  intros lambda A U r cap Hr Hcap.
  assert (Hsq : 0 <= lambda*lambda) by exact (Rle_0_sqr lambda).
  assert (HU : 0 <= U*U) by exact (Rle_0_sqr U).
  assert (Hbeta : 0 <= cap/(4*r)).
  { apply NSFA08_DIV_NONNEG; lra. }
  assert (Hbs : 0 <= (cap/(4*r))*(U*U)).
  { apply Rmult_le_pos; assumption. }
  assert (Hscale : 0 <= (4*r)*(lambda*lambda)).
  { apply Rmult_le_pos; lra. }
  unfold unpaid, shell_cost, shell_kinetic.
  replace (4*r*(lambda*lambda*pos (A/lambda-r))-cap*(lambda*lambda*U*U))
    with (((4*r)*(lambda*lambda))*(pos (A/lambda-r)-(cap/(4*r))*(U*U)))
    by (field; repeat split; lra).
  rewrite (NSST00_POS_SCALE _ _ Hscale).
  rewrite (NSST01_POS_NESTED _ _ Hbs).
  unfold folded_cost. field; repeat split; lra.
Qed.

Theorem NSST11_EXACT_EXISTING_CROWD_RATE : forall nu cap d t,
  0 < nu -> 0 <= cap ->
  O.crowd_rate nu cap d t =
  total (fun j => folded_cost (wave j) (O.ev_A d t j/wave j)
    (O.ev_U d t j*O.ev_U d t j) (O.threshold nu)
    (cap/(4*O.threshold nu))) (O.ev_count d).
Proof.
  intros nu cap d t Hnu Hcap.
  unfold O.crowd_rate, shell_unpaid. rewrite NSST02_TOTAL_DIV.
  apply NSFA00_TOTAL_EXT; intros j Hj.
  apply NSST10_EXACT_OLD_UNPAID_IDENTITY; [unfold O.threshold; lra|exact Hcap].
Qed.

Lemma NSST12_FOLDED_NONNEG : forall lambda y S r beta,
  0 <= folded_cost lambda y S r beta.
Proof.
  intros. unfold folded_cost. apply Rmult_le_pos.
  - exact (Rle_0_sqr lambda).
  - apply NSFA10_POS_NONNEG.
Qed.

Theorem NSST13_DISCRIMINANT_SAFE : forall y r b,
  0 <= r -> 0 <= b -> y*y <= 4*r*b -> pos (y-r-b)=0.
Proof.
  intros y r b Hr Hb Hd. apply NSFA12_POS_ZERO.
  pose proof (Rle_0_sqr (r-b)) as Hsq. unfold Rsqr in Hsq.
  destruct (Rle_dec y 0); [lra|].
  destruct (Rle_dec (y-r-b) 0); [assumption|].
  assert (Hp : 0 < (y-(r+b))*(y+(r+b))).
  { apply Rmult_lt_0_compat; lra. }
  nra.
Qed.

Theorem NSST14_POSITIVE_COST_REQUIRES_DISCRIMINANT : forall y r b,
  0 <= r -> 0 <= b -> 0 < pos (y-r-b) -> 4*r*b < y*y.
Proof.
  intros y r b Hr Hb Hp.
  destruct (Rle_dec (y*y) (4*r*b)) as [H|H]; [|lra].
  rewrite (NSST13_DISCRIMINANT_SAFE y r b Hr Hb H) in Hp; lra.
Qed.

Lemma NSST15_PASSAGE_NONNEG : forall y r beta S z,
  0 < z -> 0 <= passage_integrand y r beta S z.
Proof. intros; unfold passage_integrand; apply NSFA08_DIV_NONNEG;
  [apply NSFA10_POS_NONNEG|assumption]. Qed.

Theorem NSST16_PASSAGE_QUADRATIC_BOUND : forall y r beta S z,
  0 < r -> 0 <= beta -> 0 <= S -> 0 < z ->
  passage_integrand y r beta S z <= (y*y/(4*r))*z.
Proof.
  intros y r beta S z Hr Hb HS Hz.
  assert (Hsub : 0 <= beta*z*z*S).
  { replace (beta*z*z*S) with ((beta*S)*(z*z)) by ring.
    apply Rmult_le_pos; [apply Rmult_le_pos; assumption|exact (Rle_0_sqr z)]. }
  assert (Hclip : pos (profile y r beta S z) <= pos (z*y-r)).
  { apply NSFA14_POS_MONO; unfold profile; lra. }
  pose proof (NSFA16_QUADRATIC_CLIP (z*y) r ltac:(lra)) as Hquad.
  pose proof (Rmult_le_compat_l (4*r) _ _ ltac:(lra) Hclip) as Hmul.
  assert (Hden : 0 < (4*r)*z) by (apply Rmult_lt_0_compat; lra).
  apply (Rmult_le_reg_l ((4*r)*z)); [exact Hden|].
  unfold passage_integrand.
  replace (((4*r)*z)*(pos (profile y r beta S z)/z))
    with (4*r*pos (profile y r beta S z)) by (field; repeat split; lra).
  replace (((4*r)*z)*((y*y/(4*r))*z)) with ((z*y)*(z*y)) by (field; repeat split; lra).
  lra.
Qed.

Lemma NSST17_PROFILE_SCALING : forall y r beta S z q,
  profile (q*y) r beta (q*q*S) z=profile y r beta S (q*z).
Proof. intros; unfold profile; ring. Qed.

(* The active interval moments are concrete endpoint expressions. *)
Definition active_width a b := b-a.
Definition active_moment a b := (b*b-a*a)/2.

Lemma NSST20_ACTIVE_MOMENT_BOUNDS : forall a b,
  0 <= a -> a <= b -> b <= 1 ->
  0 <= active_width a b /\ active_width a b <= 1 /\
  0 <= active_moment a b /\ active_moment a b <= /2.
Proof.
  intros a b Ha Hab Hb. unfold active_width, active_moment.
  assert (Hprod : 0 <= (b-a)*(b+a)) by (apply Rmult_le_pos; lra).
  assert (Hb2 : 0 <= (1-b)*(1+b)) by (apply Rmult_le_pos; lra).
  pose proof (Rle_0_sqr a) as Ha2; unfold Rsqr in Ha2.
  repeat split; nra.
Qed.

Theorem NSST21_ENDPOINT_EULER_IDENTITY : forall y r beta S a b,
  profile y r beta S a=0 ->
  profile y r beta S b=pos (y-r-beta*S) ->
  y*active_width a b-2*beta*S*active_moment a b=pos (y-r-beta*S).
Proof.
  intros y r beta S a b Ha Hb.
  unfold profile in Ha,Hb. unfold active_width, active_moment. nra.
Qed.

Lemma NSST22_CLIPPED_UPPER_ENDPOINT : forall y r beta S b,
  (b=1 /\ 0 <= y-r-beta*S) \/
  (profile y r beta S b=0 /\ y-r-beta*S <= 0) ->
  profile y r beta S b=pos (y-r-beta*S).
Proof.
  intros y r beta S b [[Hb Hg]|[Hb Hg]].
  - subst b; unfold profile; rewrite NSFA13_POS_ID by exact Hg; ring.
  - rewrite NSFA12_POS_ZERO by exact Hg; exact Hb.
Qed.

Theorem NSST30_FINITE_INITIAL_STORAGE_BOUND :
  forall n (H y lambda S : nat -> R) r nu E0,
  0 < r -> 0 < nu ->
  (forall j, (j<n)%nat -> 0 <= H j /\ H j <= y j*y j/(8*r*nu)) ->
  (forall j, (j<n)%nat -> y j*y j <= 125*lambda j*S j) ->
  total (fun j => lambda j*S j) n <= E0 ->
  0 <= total H n /\ total H n <= 125*E0/(8*r*nu).
Proof.
  intros n H y lambda S r nu E0 Hr Hnu HH Hy HE.
  assert (Hden : 0 < 8*r*nu) by (repeat apply Rmult_lt_0_compat; lra).
  assert (Hi : 0 <= /(8*r*nu)) by (left; apply Rinv_0_lt_compat; exact Hden).
  split.
  - apply NSFA02_TOTAL_NONNEG; intros j Hj; exact (proj1 (HH j Hj)).
  - transitivity (total (fun j => (125/(8*r*nu))*(lambda j*S j)) n).
    + apply NSFA01_TOTAL_LE; intros j Hj.
      pose proof (proj2 (HH j Hj)) as Hh.
      pose proof (Rmult_le_compat_r (/(8*r*nu)) _ _ Hi (Hy j Hj)) as Hm.
      unfold Rdiv in *; nra.
    + rewrite NSFA04_TOTAL_SCALE.
      assert (Hc : 0 <= 125/(8*r*nu)) by (apply NSFA08_DIV_NONNEG; lra).
      pose proof (Rmult_le_compat_l (125/(8*r*nu)) _ _ Hc HE) as Hm.
      unfold Rdiv in *; nra.
Qed.

End NSE_STORAGE_COST_ALGEBRA.
