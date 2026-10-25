From Stdlib Require Import Reals Ranalysis1 MVT Lra Psatz Field Lia.
Require Import awpi_nse_kq_finite_algebra_v0_49_3.

Module NSE_CONTINUOUS_TIME_CALCULUS.
Import NSE_KQ_FINITE_ALGEBRA.
Open Scope R_scope.

(* Actual Stdlib real derivatives, not an axiomatized integral algebra.
   All derivatives below are required on the closed interval.  Applications
   at nonsmooth/rank-changing rates must supply these premises, or use a
   separate almost-everywhere/integration extension. *)
Definition InTime (a b t : R) : Prop := a <= t <= b.
Definition DerivativeOn (a b : R) (F f : R -> R) : Prop :=
  forall t, InTime a b t -> derivable_pt_lim F t (f t).
Definition PrimitiveOn (a b : R) (f F : R -> R) : Prop :=
  F a = 0 /\ DerivativeOn a b F f.

Lemma derivative_on_plus : forall a b F G f g,
  DerivativeOn a b F f -> DerivativeOn a b G g ->
  DerivativeOn a b (fun t => F t+G t) (fun t => f t+g t).
Proof.
  intros a b F G f g HF HG t Ht.
  exact (derivable_pt_lim_plus F G t (f t) (g t) (HF t Ht) (HG t Ht)).
Qed.
Lemma derivative_on_minus : forall a b F G f g,
  DerivativeOn a b F f -> DerivativeOn a b G g ->
  DerivativeOn a b (fun t => F t-G t) (fun t => f t-g t).
Proof.
  intros a b F G f g HF HG t Ht.
  exact (derivable_pt_lim_minus F G t (f t) (g t) (HF t Ht) (HG t Ht)).
Qed.
Lemma derivative_on_scale : forall a b F f c,
  DerivativeOn a b F f ->
  DerivativeOn a b (fun t => c*F t) (fun t => c*f t).
Proof.
  intros a b F f c HF t Ht.
  exact (derivable_pt_lim_scal F c t (f t) (HF t Ht)).
Qed.
Lemma derivative_on_ext_rate : forall a b F f g,
  DerivativeOn a b F f ->
  (forall t, InTime a b t -> f t=g t) -> DerivativeOn a b F g.
Proof.
  intros a b F f g HF He t Ht; rewrite <- (He t Ht); exact (HF t Ht).
Qed.

Theorem NSCT00_NONNEGATIVE_DERIVATIVE_GIVES_ORDER : forall a b F f,
  a <= b -> DerivativeOn a b F f ->
  (forall t, InTime a b t -> 0 <= f t) -> F a <= F b.
Proof.
  intros a b F f Hab HD Hpos.
  destruct (Rlt_dec a b) as [Hlt|Hlt].
  - destruct (MVT_cor2 F f a b Hlt HD) as [t [Heq Ht]].
    assert (Hclosed : InTime a b t) by (unfold InTime; lra).
    pose proof (Hpos t Hclosed) as Hp.
    assert (Hprod : 0 <= f t*(b-a)) by (apply Rmult_le_pos; lra).
    lra.
  - assert (a=b) by lra; subst b; apply Rle_refl.
Qed.

Theorem NSCT01_NONPOSITIVE_DERIVATIVE_GIVES_ORDER : forall a b F f,
  a <= b -> DerivativeOn a b F f ->
  (forall t, InTime a b t -> f t <= 0) -> F b <= F a.
Proof.
  intros a b F f Hab HD Hneg.
  destruct (Rlt_dec a b) as [Hlt|Hlt].
  - destruct (MVT_cor2 F f a b Hlt HD) as [t [Heq Ht]].
    assert (Hclosed : InTime a b t) by (unfold InTime; lra).
    pose proof (Hneg t Hclosed) as Hn.
    assert (Hprod : 0 <= (-f t)*(b-a)) by (apply Rmult_le_pos; lra).
    nra.
  - assert (a=b) by lra; subst b; apply Rle_refl.
Qed.

Theorem NSCT02_ZERO_DERIVATIVE_GIVES_EQUALITY : forall a b F,
  a <= b -> DerivativeOn a b F (fun _ => 0) -> F b=F a.
Proof.
  intros a b F Hab HD; apply Rle_antisym.
  - exact (NSCT01_NONPOSITIVE_DERIVATIVE_GIVES_ORDER a b F (fun _ => 0)
      Hab HD (fun t Ht => Rle_refl 0)).
  - exact (NSCT00_NONNEGATIVE_DERIVATIVE_GIVES_ORDER a b F (fun _ => 0)
      Hab HD (fun t Ht => Rle_refl 0)).
Qed.

Lemma derivative_on_restrict : forall a b c F f,
  a <= c <= b -> DerivativeOn a b F f -> DerivativeOn a c F f.
Proof.
  intros a b c F f Hc HD t Ht; apply HD; unfold InTime in *; lra.
Qed.

Theorem NSCT10_PRIMITIVE_NONNEGATIVE : forall a b f F t,
  PrimitiveOn a b f F ->
  (forall s, InTime a b s -> 0 <= f s) ->
  InTime a b t -> 0 <= F t.
Proof.
  intros a b f F t [Hinit HD] Hpos Ht.
  assert (HDt : DerivativeOn a t F f).
  { apply (derivative_on_restrict a b t F f Ht HD). }
  assert (HF : F a <= F t).
  { apply (NSCT00_NONNEGATIVE_DERIVATIVE_GIVES_ORDER a t F f).
    - unfold InTime in Ht; lra.
    - exact HDt.
    - intros s Hs; apply Hpos; unfold InTime in *; lra. }
  rewrite Hinit in HF; exact HF.
Qed.

Theorem NSCT11_PRIMITIVE_COMPARISON : forall a b f g F G t,
  PrimitiveOn a b f F -> PrimitiveOn a b g G ->
  (forall s, InTime a b s -> f s <= g s) ->
  InTime a b t -> F t <= G t.
Proof.
  intros a b f g F G t [HF0 HF] [HG0 HG] Hfg Ht.
  assert (HP : PrimitiveOn a b (fun s => g s-f s) (fun s => G s-F s)).
  { split.
    - rewrite HG0, HF0; ring.
    - exact (derivative_on_minus a b G F g f HG HF). }
  pose proof (NSCT10_PRIMITIVE_NONNEGATIVE a b
    (fun s => g s-f s) (fun s => G s-F s) t HP) as H.
  assert (Hpos : forall s, InTime a b s -> 0 <= g s-f s).
  { intros s Hs; specialize (Hfg s Hs); lra. }
  specialize (H Hpos Ht); cbn beta in H; lra.
Qed.

Theorem NSCT12_PRIMITIVE_UNIQUENESS : forall a b f F G t,
  PrimitiveOn a b f F -> PrimitiveOn a b f G ->
  InTime a b t -> F t=G t.
Proof.
  intros a b f F G t HF HG Ht; apply Rle_antisym.
  - exact (NSCT11_PRIMITIVE_COMPARISON a b f f F G t HF HG
      (fun s Hs => Rle_refl (f s)) Ht).
  - exact (NSCT11_PRIMITIVE_COMPARISON a b f f G F t HG HF
      (fun s Hs => Rle_refl (f s)) Ht).
Qed.

(* The sign of r is unrestricted.  Positivity is integrated via MVT for
   every constant quadratic test, so no integral Cauchy axiom is supplied. *)
Theorem NSCT20_CONTINUOUS_SIGNED_CAUCHY : forall a b q z r Q Z net t,
  PrimitiveOn a b q Q -> PrimitiveOn a b z Z -> PrimitiveOn a b r net ->
  (forall s, InTime a b s -> 0 <= q s) ->
  (forall s, InTime a b s -> 0 <= z s) ->
  (forall s, InTime a b s -> r s*r s <= q s*z s) ->
  InTime a b t -> net t*net t <= Q t*Z t.
Proof.
  intros a b q z r Q Z net t HQ HZ HR Hq Hz Hcs Ht.
  apply quadratic_cauchy.
  - exact (NSCT10_PRIMITIVE_NONNEGATIVE a b q Q t HQ Hq Ht).
  - exact (NSCT10_PRIMITIVE_NONNEGATIVE a b z Z t HZ Hz Ht).
  - intro x.
    assert (HP : PrimitiveOn a b
      (fun s => q s-2*x*r s+x*x*z s)
      (fun s => Q s-2*x*net s+x*x*Z s)).
    { destruct HQ as [HQ0 HDQ]; destruct HZ as [HZ0 HDZ]; destruct HR as [HR0 HDR].
      split.
      - rewrite HQ0, HR0, HZ0; ring.
      - apply (derivative_on_plus a b
          (fun s => Q s-2*x*net s) (fun s => x*x*Z s)
          (fun s => q s-2*x*r s) (fun s => x*x*z s)).
        + apply (derivative_on_minus a b Q (fun s => 2*x*net s)
            q (fun s => 2*x*r s)); [exact HDQ|].
          exact (derivative_on_scale a b net r (2*x) HDR).
        + exact (derivative_on_scale a b Z z (x*x) HDZ). }
    apply (NSCT10_PRIMITIVE_NONNEGATIVE a b
      (fun s => q s-2*x*r s+x*x*z s)
      (fun s => Q s-2*x*net s+x*x*Z s) t HP).
    + intros s Hs; exact (cauchy_quadratic (q s) (z s) (r s)
        (Hq s Hs) (Hz s Hs) (Hcs s Hs) x).
    + exact Ht.
Qed.

Theorem NSCT30_CONTINUOUS_SIGNED_BALANCE : forall a b V A r Y net t,
  DerivativeOn a b V (fun s => r s-A s) ->
  PrimitiveOn a b A Y -> PrimitiveOn a b r net ->
  InTime a b t -> V t+Y t=V a+net t.
Proof.
  intros a b V A r Y net t HV [HY0 HY] [HN0 HN] Ht.
  assert (HD : DerivativeOn a b
    (fun s => V s+Y s-net s) (fun _ => 0)).
  { apply (derivative_on_ext_rate a b
      (fun s => V s+Y s-net s)
      (fun s => (r s-A s)+A s-r s) (fun _ => 0)).
    - apply (derivative_on_minus a b
        (fun s => V s+Y s) net (fun s => (r s-A s)+A s) r).
      + exact (derivative_on_plus a b V Y (fun s => r s-A s) A HV HY).
      + exact HN.
    - intros; ring. }
  pose proof (NSCT02_ZERO_DERIVATIVE_GIVES_EQUALITY a t
    (fun s => V s+Y s-net s)) as Hconst.
  assert (Hat : a<=t) by (unfold InTime in Ht; lra).
  specialize (Hconst Hat (derivative_on_restrict a b t
    (fun s => V s+Y s-net s) (fun _ => 0) Ht HD)).
  cbn beta in Hconst; rewrite HY0, HN0 in Hconst; lra.
Qed.

Lemma derivative_finite_sum : forall n (F : nat -> R -> R) d t,
  (forall i, (i<n)%nat -> derivable_pt_lim (F i) t (d i)) ->
  derivable_pt_lim (fun s => sum n (fun i => F i s)) t (sum n d).
Proof.
  induction n as [|n IH]; intros F d t H.
  - change (derivable_pt_lim (fun _ : R => 0) t 0).
    exact (derivable_pt_lim_const 0 t).
  - change (derivable_pt_lim
      (fun s => sum n (fun i => F i s)+F n s) t (sum n d+d n)).
    apply (derivable_pt_lim_plus (fun s => sum n (fun i => F i s))
      (F n) t (sum n d) (d n)).
    + apply IH; intros i Hi; apply H; lia.
    + apply H; lia.
Qed.

Theorem NSCT40_FINITE_WEIGHTED_ENERGY_DERIVATIVE : forall n w
  (u : R -> Vec) du t,
  (forall i, (i<n)%nat -> derivable_pt_lim (fun s => u s i) t (du i)) ->
  derivable_pt_lim
    (fun s => sum n (fun i => w i*u s i*u s i)) t
    (2*sum n (fun i => w i*u t i*du i)).
Proof.
  intros n w u du t Hu.
  assert (Hd : derivable_pt_lim
    (fun s => sum n (fun i => w i*u s i*u s i)) t
    (sum n (fun i => w i*(du i*u t i+u t i*du i)))).
  { apply (derivable_pt_lim_ext
      (fun s => sum n (fun i => w i*(u s i*u s i)))
      (fun s => sum n (fun i => w i*u s i*u s i)) t
      (sum n (fun i => w i*(du i*u t i+u t i*du i)))).
    - intro s; apply sum_ext; intros; ring.
    - apply derivative_finite_sum; intros i Hi.
      apply (derivable_pt_lim_scal (fun s => u s i*u s i)
        (w i) t (du i*u t i+u t i*du i)).
      exact (derivable_pt_lim_mult (fun s => u s i) (fun s => u s i)
        t (du i) (du i) (Hu i Hi) (Hu i Hi)). }
  assert (He : sum n (fun i => w i*(du i*u t i+u t i*du i)) =
      2*sum n (fun i => w i*u t i*du i)).
  { rewrite <- sum_scale; apply sum_ext; intros; ring. }
  rewrite He in Hd; exact Hd.
Qed.

End NSE_CONTINUOUS_TIME_CALCULUS.
