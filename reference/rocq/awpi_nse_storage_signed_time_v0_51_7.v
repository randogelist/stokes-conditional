From Stdlib Require Import Reals Lra Psatz Lia Field.
Require Import awpi_nse_finite_shell_algebra_v0_48_4.
Require Import awpi_nse_scalar_comparison_v0_48_4.
Require Import awpi_nse_continuous_time_calculus_v0_50_0.
Require Import awpi_nse_storage_modal_ledger_v0_51_7.

Module NSE_STORAGE_SIGNED_TIME.
Import NSE_FINITE_SHELL_ALGEBRA NSE_SCALAR_COMPARISON.
Module CT := NSE_CONTINUOUS_TIME_CALCULUS.
Open Scope R_scope.

Definition ZeroPrimitive T (F f : R -> R) : Prop :=
  F 0=0 /\ forall t, within T t -> derivable_pt_lim F t (f t).

Theorem NSSP00_SIGNED_PRIMITIVE_COMPARISON : forall T F f J g c t,
  ZeroPrimitive T F f -> ZeroPrimitive T J g ->
  (forall x, within T x -> f x <= c*g x) ->
  within T t -> F t <= c*J t.
Proof.
  intros T F f J g c t [HF0 HF] [HJ0 HJ] Hle Ht.
  exact (NSCP20_PRIMITIVE_COMPARISON F f J g T t c Ht HF0 HJ0 HF HJ Hle).
Qed.

Theorem NSSP01_POINTWISE_HEAT_PAYMENT_INTEGRATES : forall T EI e GI g beta t,
  ZeroPrimitive T EI e -> ZeroPrimitive T GI g ->
  (forall x, within T x -> e x <= beta*g x) ->
  within T t -> EI t <= beta*GI t.
Proof. exact NSSP00_SIGNED_PRIMITIVE_COMPARISON. Qed.

Theorem NSSP02_ABSOLUTE_LOW_PAYMENT_INTEGRATES : forall T PL p GI g kappa t,
  ZeroPrimitive T PL p -> ZeroPrimitive T GI g ->
  (forall x, within T x -> Rabs (p x) <= kappa*g x) ->
  within T t -> PL t <= kappa*GI t.
Proof.
  intros T PL p GI g kappa t HP HG Hle Ht.
  apply (NSSP00_SIGNED_PRIMITIVE_COMPARISON T PL p GI g kappa t HP HG).
  - intros x Hx; pose proof (Hle x Hx).
    pose proof (Rle_abs (p x)); lra.
  - exact Ht.
Qed.

Theorem NSSP10_CONTINUOUS_STORAGE_BALANCE :
  forall T H V VI plo PL phi PH e EI t,
  (forall x, within T x -> derivable_pt_lim H x (plo x+phi x+e x-V x)) ->
  ZeroPrimitive T VI V -> ZeroPrimitive T PL plo ->
  ZeroPrimitive T PH phi -> ZeroPrimitive T EI e ->
  within T t ->
  H t+VI t=H 0+PL t+PH t+EI t.
Proof.
  intros T H V VI plo PL phi PH e EI t HH
    [HV0 HV] [HL0 HL] [HH0 HP] [HE0 HE] Ht.
  assert (Hnet : CT.PrimitiveOn 0 T (fun x => plo x+phi x+e x)
      (fun x => PL x+PH x+EI x)).
  { split.
    - rewrite HL0, HH0, HE0; ring.
    - intros x Hx. apply derivable_pt_lim_plus.
      + apply derivable_pt_lim_plus; [apply HL|apply HP]; exact Hx.
      + apply HE; exact Hx. }
  assert (Hvp : CT.PrimitiveOn 0 T V VI) by (split; assumption).
  pose proof (CT.NSCT30_CONTINUOUS_SIGNED_BALANCE 0 T H V
    (fun x => plo x+phi x+e x) VI (fun x => PL x+PH x+EI x) t
    HH Hvp Hnet Ht) as Hbal.
  cbn beta in Hbal; lra.
Qed.

(* This finite telescope does not require differentiability at partition
   knots.  It also does not assert that an almost-everywhere balance has
   already been integrated: that analytic construction must supply the
   exact local cell equalities, or use the C1 constructor above. *)
Theorem NSSP11_FINITE_CELL_BALANCE_TELESCOPE :
  forall n (H VI PL PH EI : nat -> R),
  (forall i, (i<n)%nat ->
    H (S i)-H i+VI (S i)-VI i=
    PL (S i)-PL i+PH (S i)-PH i+EI (S i)-EI i) ->
  H n-H O+VI n-VI O=PL n-PL O+PH n-PH O+EI n-EI O.
Proof.
  intros n H VI PL PH EI; induction n as [|n IH]; intro Hcell.
  - ring.
  - assert (Hpre : H n-H O+VI n-VI O=PL n-PL O+PH n-PH O+EI n-EI O).
    { apply IH; intros i Hi; apply Hcell; lia. }
    pose proof (Hcell n ltac:(lia)); lra.
Qed.

Theorem NSSP12_PARTITION_CONSTRUCTS_INTEGRATED_BALANCE :
  forall n (cut : nat -> R) H VI PL PH EI t,
  cut O=0 -> cut n=t -> VI 0=0 -> PL 0=0 -> PH 0=0 -> EI 0=0 ->
  (forall i, (i<n)%nat ->
    H (cut (S i))-H (cut i)+VI (cut (S i))-VI (cut i)=
    PL (cut (S i))-PL (cut i)+PH (cut (S i))-PH (cut i)+
    EI (cut (S i))-EI (cut i)) ->
  H t+VI t=H 0+PL t+PH t+EI t.
Proof.
  intros n cut H VI PL PH EI t H0 Hn HV HL HP HE Hcell.
  pose proof (NSSP11_FINITE_CELL_BALANCE_TELESCOPE n
    (fun i => H (cut i)) (fun i => VI (cut i)) (fun i => PL (cut i))
    (fun i => PH (cut i)) (fun i => EI (cut i)) Hcell) as Hbal.
  cbn beta in Hbal. rewrite H0,Hn,HV,HL,HP,HE in Hbal; lra.
Qed.

Definition replenishment_budget nu beta kappa Hinit M0 gamma Chigh :=
  (Hinit+(beta+kappa)*(M0/(2*nu))+Chigh)/(1-gamma).

Theorem NSSP20_STRICT_HIGH_OUTPUT_ABSORPTION :
  forall nu beta kappa Hinit M0 gamma Chigh H H0 VI GI PL PH EI,
  0 < nu -> 0 <= beta -> 0 <= kappa -> gamma < 1 ->
  0 <= H -> H0 <= Hinit -> 2*nu*GI <= M0 ->
  H+VI=H0+PL+PH+EI ->
  EI <= beta*GI -> PL <= kappa*GI -> PH <= gamma*VI+Chigh ->
  VI <= replenishment_budget nu beta kappa Hinit M0 gamma Chigh.
Proof.
  intros nu beta kappa Hinit M0 gamma Chigh H H0 VI GI PL PH EI
    Hnu Hb Hk Hg Hpos Hinit0 Hkin Hbal Hheat Hlow Hhigh.
  assert (Hcancel : (2*nu)*(M0/(2*nu))=M0) by (field; repeat split; lra).
  assert (HGI : GI <= M0/(2*nu)).
  { apply (Rmult_le_reg_l (2*nu)); [lra|]. rewrite Hcancel; exact Hkin. }
  pose proof (Rmult_le_compat_l (beta+kappa) _ _ ltac:(lra) HGI) as Hpay.
  assert (Hres : (1-gamma)*VI <= Hinit+(beta+kappa)*(M0/(2*nu))+Chigh)
    by nra.
  unfold replenishment_budget.
  apply (Rmult_le_reg_l (1-gamma)); [lra|].
  replace ((1-gamma)*((Hinit+(beta+kappa)*(M0/(2*nu))+Chigh)/(1-gamma)))
    with (Hinit+(beta+kappa)*(M0/(2*nu))+Chigh) by (field; repeat split; lra).
  exact Hres.
Qed.

Lemma NSSP21_REPLENISHMENT_BUDGET_NONNEG :
  forall nu beta kappa Hinit M0 gamma Chigh,
  0 < nu -> 0 <= beta -> 0 <= kappa -> 0 <= Hinit ->
  0 <= M0 -> gamma < 1 -> 0 <= Chigh ->
  0 <= replenishment_budget nu beta kappa Hinit M0 gamma Chigh.
Proof.
  intros nu beta kappa Hinit M0 gamma Chigh Hnu Hb Hk HH HM Hg HC.
  unfold replenishment_budget. apply NSFA08_DIV_NONNEG; [|lra].
  assert (Hq : 0 <= M0/(2*nu)) by (apply NSFA08_DIV_NONNEG; lra).
  assert (Hp : 0 <= (beta+kappa)*(M0/(2*nu))) by (apply Rmult_le_pos; lra).
  lra.
Qed.

Theorem NSSP22_UNIFORM_STORAGE_TO_UNPAID_BUDGET :
  forall (Reg : Type) T (H VI GI PL PH EI : Reg -> R -> R)
    nu beta kappa Hinit M0 gamma Chigh,
  0 < nu -> 0 <= beta -> 0 <= kappa -> gamma < 1 ->
  (forall eps t, within T t -> 0 <= H eps t) ->
  (forall eps, H eps 0 <= Hinit) ->
  (forall eps t, within T t -> 2*nu*GI eps t <= M0) ->
  (forall eps t, within T t -> H eps t+VI eps t=
    H eps 0+PL eps t+PH eps t+EI eps t) ->
  (forall eps t, within T t -> EI eps t <= beta*GI eps t) ->
  (forall eps t, within T t -> PL eps t <= kappa*GI eps t) ->
  (forall eps t, within T t -> PH eps t <= gamma*VI eps t+Chigh) ->
  forall eps t, within T t ->
    VI eps t <= replenishment_budget nu beta kappa Hinit M0 gamma Chigh.
Proof.
  intros Reg T H VI GI PL PH EI nu beta kappa Hinit M0 gamma Chigh
    Hnu Hb Hk Hg Hpos Hseed Hkin Hbal Hheat Hlow Hhigh eps t Ht.
  exact (NSSP20_STRICT_HIGH_OUTPUT_ABSORPTION
    nu beta kappa Hinit M0 gamma Chigh (H eps t) (H eps 0)
    (VI eps t) (GI eps t) (PL eps t) (PH eps t) (EI eps t)
    Hnu Hb Hk Hg (Hpos eps t Ht) (Hseed eps) (Hkin eps t Ht)
    (Hbal eps t Ht) (Hheat eps t Ht) (Hlow eps t Ht) (Hhigh eps t Ht)).
Qed.

Theorem NSSP23_UNIT_RETENTION_HAS_NO_UNIFORM_BOUND :
  forall B : R, exists VI PH : R,
  0 <= VI /\ 0+VI=0+0+PH+0 /\ PH <= 1*VI+0 /\ B < VI.
Proof.
  intro B. exists (pos B+1), (pos B+1).
  pose proof (NSFA10_POS_NONNEG B); pose proof (NSFA11_POS_ABOVE B).
  repeat split; lra.
Qed.

Theorem NSSP24_SIGNED_PAYMENT_IS_NOT_TOTAL_VARIATION :
  exists p0 p1 : R, p0+p1=0 /\ 0 < pos p0+pos p1.
Proof.
  exists 1, (-1). rewrite (NSFA13_POS_ID 1 ltac:(lra)).
  rewrite (NSFA12_POS_ZERO (-1) ltac:(lra)); split; lra.
Qed.

End NSE_STORAGE_SIGNED_TIME.
