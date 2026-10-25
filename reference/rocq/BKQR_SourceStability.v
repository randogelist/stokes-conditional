From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import BKQR_CountableRange BKQR_TimeIntegrals BKQR_BilinearKernel.
Require Import BKQR_NonlinearTimeSource.

Module BKQR_SOURCE_STABILITY.
Import GP_COUNTABLE_RANGE BKQR_TIME_INTEGRALS BKQR_BILINEAR_KERNEL.
Import BKQR_NONLINEAR_TIME_SOURCE.
Open Scope R_scope.

Definition path_difference (u v:R->nat->R) t i := u t i-v t i.

Lemma sum_minus : forall N f g,
  gp_sum N (fun i=>f i-g i)=gp_sum N f-gp_sum N g.
Proof. induction N; intros; simpl; [ring|rewrite IHN; ring]. Qed.

Lemma difference_continuous : forall u v a b,
  CoordinateContinuous u a b -> CoordinateContinuous v a b ->
  CoordinateContinuous (path_difference u v) a b.
Proof. intros u v a b Hu Hv i. apply continuous_minus; [apply Hu|apply Hv]. Qed.

Lemma quadratic_perturbation_identity : forall K N x y,
  quadratic_form K N x-quadratic_form K N y=
  bilinear_form K N x (fun i=>x i-y i)+
  bilinear_form K N (fun i=>x i-y i) y.
Proof.
  intros. unfold quadratic_form,bilinear_form,bilinear_rectangle.
  transitivity (gp_sum N (fun j=>gp_sum N (fun k=>
    K j k*x j*x k-K j k*y j*y k))).
  - rewrite <- sum_minus. apply gp_sum_ext. intros j Hj.
    symmetry. apply sum_minus.
  - rewrite <- sum_plus. apply gp_sum_ext. intros j Hj.
    rewrite <- sum_plus. apply gp_sum_ext. intros. ring.
Qed.

Theorem quadratic_perturbation_young : forall K C,
  SchurBound K C -> forall N x y E delta,
  PhysicalBound x E -> PhysicalBound y E -> 0<delta ->
  Rabs(quadratic_form K N x-quadratic_form K N y)<=
    C*delta*E+(C/delta)*physical_prefix (fun i=>x i-y i) N.
Proof.
  intros K C HK N x y E delta Hx Hy Hd.
  pose proof (proj1 HK) as HC.
  assert (Hi:0</delta) by (apply Rinv_0_lt_compat; exact Hd).
  pose proof (bilinear_form_young K C HK N x (fun i=>x i-y i) delta Hd) as H1.
  pose proof (bilinear_form_young K C HK N (fun i=>x i-y i) y (/delta) Hi) as H2.
  rewrite Rinv_inv in H2.
  rewrite quadratic_perturbation_identity.
  eapply Rle_trans; [apply Rabs_triang|].
  specialize (Hx N). specialize (Hy N).
  assert (Hscale:0<=C*delta) by nra.
  assert (Hsum:C*delta*(physical_prefix x N+physical_prefix y N)<=C*delta*(2*E)).
  { apply Rmult_le_compat_l; lra. }
  unfold Rdiv. nra.
Qed.

Theorem tested_source_perturbation_bound :
  forall K C u v a b Hab Hu Hv eta Heta E A D,
  SchurBound K C ->
  (forall t,a<=t<=b -> PhysicalBound (u t) E) ->
  (forall t,a<=t<=b -> PhysicalBound (v t) E) ->
  0<=A -> (forall t,a<=t<=b -> Rabs(eta t)<=A) ->
  TimeBound (fun _=>1) (path_difference u v) a b Hab
    (difference_continuous u v a b Hu Hv) D ->
  forall delta,0<delta -> forall N,
  Rabs(tested_source K u a b Hab Hu eta Heta N-
       tested_source K v a b Hab Hv eta Heta N)<=
    A*C*delta*E*(b-a)+(A*C/delta)*D.
Proof.
  intros K C u v a b Hab Hu Hv eta Heta E A D HK Huc Hvc HA Hetab HD delta Hd N.
  pose proof (proj1 HK) as HC.
  pose (HF:=tested_integrand_continuous K u a b Hu eta Heta N).
  pose (HG:=tested_integrand_continuous K v a b Hv eta Heta N).
  pose proof (continuous_minus a b _ _ HF HG) as Hdiff.
  pose (Huv:=difference_continuous u v a b Hu Hv).
  pose proof (energy_integrand_continuous a b (path_difference u v) Huv N) as HE.
  set (alpha:=A*C*delta*E).
  set (beta:=A*C/delta).
  pose proof (continuous_plus a b (fun _=>alpha)
    (fun t=>beta*energy_integrand N (path_difference u v) t)
    (continuous_const a b alpha)
    (continuous_scale a b beta _ HE)) as Hboundcont.
  assert (Hpoint:forall t,a<=t<=b ->
    Rabs(tested_integrand K u eta N t-tested_integrand K v eta N t)<=
    alpha+beta*energy_integrand N (path_difference u v) t).
  { intros t Ht. unfold tested_integrand,quadratic_integrand.
    replace (eta t*quadratic_form K N (u t)-eta t*quadratic_form K N (v t))
      with (eta t*(quadratic_form K N (u t)-quadratic_form K N (v t))) by ring.
    rewrite Rabs_mult.
    pose proof (quadratic_perturbation_young K C HK N (u t) (v t) E delta
      (Huc t Ht) (Hvc t Ht) Hd) as HQ.
    eapply Rle_trans.
    - apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|apply Hetab; exact Ht|exact HQ].
    - right. unfold alpha,beta,energy_integrand,path_difference,Rdiv. ring. }
  pose proof (integral_absolute_bound a b Hab _ _ Hdiff Hboundcont Hpoint) as HB.
  rewrite (integral_minus a b Hab _ _ HF HG Hdiff) in HB.
  rewrite (integral_linear a b Hab (fun _=>alpha)
    (energy_integrand N (path_difference u v)) beta
    (continuous_const a b alpha) HE Hboundcont) in HB.
  rewrite integral_constant in HB.
  rewrite (energy_integral_formula a b Hab (path_difference u v) Huv N HE) in HB.
  change (Rabs(tested_source K u a b Hab Hu eta Heta N-
    tested_source K v a b Hab Hv eta Heta N)<=
    alpha*(b-a)+beta*time_prefix (fun _=>1) (path_difference u v) a b Hab Huv N) in HB.
  assert (Hbeta:0<=beta).
  { unfold beta,Rdiv. apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; exact Hd]. }
  pose proof (HD N) as HDN. change (time_prefix (fun _=>1)
    (path_difference u v) a b Hab Huv N<=D) in HDN.
  assert (Hpaid:beta*time_prefix (fun _=>1) (path_difference u v) a b Hab Huv N<=beta*D).
  { apply Rmult_le_compat_l; assumption. }
  unfold alpha,beta in *. lra.
Qed.

Theorem completed_source_perturbation_bound :
  forall K C u v a b Hab Hu Hv eta Heta E A D L M,
  SchurBound K C ->
  (forall t,a<=t<=b -> PhysicalBound (u t) E) ->
  (forall t,a<=t<=b -> PhysicalBound (v t) E) ->
  0<=A -> (forall t,a<=t<=b -> Rabs(eta t)<=A) ->
  TimeBound (fun _=>1) (path_difference u v) a b Hab
    (difference_continuous u v a b Hu Hv) D ->
  SeqLimit (tested_source K u a b Hab Hu eta Heta) L ->
  SeqLimit (tested_source K v a b Hab Hv eta Heta) M ->
  forall delta,0<delta -> Rabs(L-M)<=A*C*delta*E*(b-a)+(A*C/delta)*D.
Proof.
  intros K C u v a b Hab Hu Hv eta Heta E A D L M HK Huc Hvc HA Hetab HD HL HM delta Hd.
  apply (sequence_absolute_bound (fun N=>tested_source K u a b Hab Hu eta Heta N-
    tested_source K v a b Hab Hv eta Heta N) (L-M)).
  - replace (L-M) with (L+(-1)*M) by ring.
    apply (limit_ext (fun N=>tested_source K u a b Hab Hu eta Heta N+
      (-1)*tested_source K v a b Hab Hv eta Heta N) _ (L+(-1)*M)).
    + intro N. ring.
    + apply limit_plus; [exact HL|apply limit_scale; exact HM].
  - intro N. apply tested_source_perturbation_bound; assumption.
Qed.

Definition StrongTimeL2 (us:nat->R->nat->R) (u:R->nat->R) a b Hab
  (Hus:forall n,CoordinateContinuous (us n) a b) (Hu:CoordinateContinuous u a b) : Prop :=
  forall eps,0<eps -> exists J,forall n,(J<=n)%nat ->
    TimeBound (fun _=>1) (path_difference (us n) u) a b Hab
      (difference_continuous (us n) u a b (Hus n) Hu) eps.

Theorem STRONG_TIME_L2_PRESERVES_NONLINEAR_SOURCE :
  forall K C us u a b Hab Hus Hu eta Heta E Ls L,
  SchurBound K C ->
  (forall n t,a<=t<=b -> PhysicalBound (us n t) E) ->
  (forall t,a<=t<=b -> PhysicalBound (u t) E) ->
  StrongTimeL2 us u a b Hab Hus Hu ->
  (forall n,SeqLimit (tested_source K (us n) a b Hab (Hus n) eta Heta) (Ls n)) ->
  SeqLimit (tested_source K u a b Hab Hu eta Heta) L ->
  SeqLimit Ls L.
Proof.
  intros K C us u a b Hab Hus Hu eta Heta E Ls L HK Husc Huc Hstrong Hsources Hsource.
  destruct (continuous_has_absolute_bound a b Hab eta Heta) as [A [HA Hetab]].
  pose proof (proj1 HK) as HC.
  assert (HE:0<=E) by (exact (Huc a (ltac:(lra)) O)).
  set (B:=A*C*E*(b-a)).
  assert (HB:0<=B) by (unfold B; repeat apply Rmult_le_pos; lra).
  intros eps Heps.
  set (delta:=eps/(4*(B+1))).
  assert (Hd:0<delta) by (unfold delta; apply Rdiv_lt_0_compat; lra).
  assert (Hdeq:4*(B+1)*delta=eps) by (unfold delta; field; lra).
  assert (Hsmall:B*delta<eps/4) by nra.
  set (K0:=A*C/delta).
  assert (HK0:0<=K0).
  { unfold K0,Rdiv. apply Rmult_le_pos; [nra|left; apply Rinv_0_lt_compat; exact Hd]. }
  set (D:=eps/(4*(K0+1))).
  assert (HD:0<D) by (unfold D; apply Rdiv_lt_0_compat; lra).
  assert (HDeq:4*(K0+1)*D=eps) by (unfold D; field; lra).
  assert (HDsmall:K0*D<eps/4) by nra.
  destruct (Hstrong D HD) as [J HJ]. exists J. intros n Hn.
  pose proof (completed_source_perturbation_bound K C (us n) u a b Hab (Hus n) Hu
    eta Heta E A D (Ls n) L HK (Husc n) Huc HA Hetab (HJ n Hn)
    (Hsources n) Hsource delta Hd) as Hbound.
  change (Rabs(Ls n-L)<=A*C*delta*E*(b-a)+K0*D) in Hbound.
  assert (Heq:A*C*delta*E*(b-a)=B*delta) by (unfold B; ring).
  rewrite Heq in Hbound. lra.
Qed.

Print Assumptions quadratic_perturbation_young.
Print Assumptions completed_source_perturbation_bound.
Print Assumptions STRONG_TIME_L2_PRESERVES_NONLINEAR_SOURCE.
End BKQR_SOURCE_STABILITY.
