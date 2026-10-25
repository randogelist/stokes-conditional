(* Genuine cutoff convergence of the cumulative critical dissipation.
   The primitives are the same ordinary derivatives supplied by the
   critical-calculus branch. Nonnegative added modal densities imply
   monotonicity in the spatial cutoff; no monotonicity or desired limit
   is an extra hypothesis. This does not exchange an abstract TimeData
   integral with a countable sum or identify a physical Sobolev norm. *)
From Stdlib Require Import Reals Ranalysis1 Lra Psatz Lia.
Require Import BKQR_CountableRange BKQR_ScalarProfile.
Require Import BKQR_M7_CriticalCalculus BKQR_M7_WeightedCompletion.

Module BKQR_M7_DISSIPATION_LIMIT.
Module B := GP_COUNTABLE_RANGE.
Module SP := BKQR_SCALAR_PROFILE.
Module M := BKQR_M7_CRITICAL_CALCULUS.
Module W := BKQR_M7_WEIGHTED_COMPLETION.
Open Scope R_scope.

Lemma critical_density_cutoff_monotone : forall lambda a,
  (forall i, 0 <= lambda i) -> forall N K t, (N <= K)%nat ->
  M.critical_density lambda a N t <= M.critical_density lambda a K t.
Proof.
  intros lambda a Hlambda N K t HNK.
  induction HNK as [|K HNK IH]; [lra|].
  change (M.critical_density lambda a N t <=
    M.critical_density lambda a K t+
      lambda K*lambda K*lambda K*a t K*a t K).
  assert (Hterm : 0 <= lambda K*lambda K*lambda K*a t K*a t K).
  { replace (lambda K*lambda K*lambda K*a t K*a t K) with
      (lambda K*((lambda K*a t K)*(lambda K*a t K))) by ring.
    apply Rmult_le_pos; [apply Hlambda|nra]. }
  lra.
Qed.

Lemma open_primitive_difference : forall T f g F G,
  M.OpenPrimitive T f F -> M.OpenPrimitive T g G ->
  M.OpenPrimitive T (fun t => f t-g t) (fun t => F t-G t).
Proof.
  intros T f g F G [HF0 HF] [HG0 HG]. split.
  - rewrite HF0, HG0. ring.
  - intros t Ht. apply derivable_pt_lim_minus; [apply HF|apply HG]; exact Ht.
Qed.

Theorem BKDL10_DISSIPATION_CUMULATIVE_NONNEGATIVE :
  forall T lambda a Dcum,
  (forall i, 0 <= lambda i) ->
  (forall N, M.OpenPrimitive T (M.critical_density lambda a N) (Dcum N)) ->
  forall N t, M.OpenTime T t -> 0 <= Dcum N t.
Proof.
  intros T lambda a Dcum Hlambda HD N t Ht.
  apply (M.BKMC30_OPEN_PRIMITIVE_NONNEGATIVE T
    (M.critical_density lambda a N) (Dcum N) (HD N)).
  - intros s Hs. apply M.critical_density_nonnegative. exact Hlambda.
  - exact Ht.
Qed.

Theorem BKDL20_DISSIPATION_CUTOFF_MONOTONE :
  forall T lambda a Dcum,
  (forall i, 0 <= lambda i) ->
  (forall N, M.OpenPrimitive T (M.critical_density lambda a N) (Dcum N)) ->
  forall N K t, (N <= K)%nat -> M.OpenTime T t -> Dcum N t <= Dcum K t.
Proof.
  intros T lambda a Dcum Hlambda HD N K t HNK Ht.
  assert (Hdiff : M.OpenPrimitive T
    (fun s => M.critical_density lambda a K s-M.critical_density lambda a N s)
    (fun s => Dcum K s-Dcum N s)).
  { apply open_primitive_difference; apply HD. }
  pose proof (M.BKMC30_OPEN_PRIMITIVE_NONNEGATIVE T
    (fun s => M.critical_density lambda a K s-M.critical_density lambda a N s)
    (fun s => Dcum K s-Dcum N s) Hdiff) as Hpos.
  assert (Hrate : forall s, M.OpenTime T s ->
    0 <= M.critical_density lambda a K s-M.critical_density lambda a N s).
  { intros s Hs. pose proof (critical_density_cutoff_monotone
      lambda a Hlambda N K s HNK). lra. }
  specialize (Hpos Hrate t Ht). lra.
Qed.

Lemma monotone_prefix_total_is_limit : forall f L,
  (forall N K, (N <= K)%nat -> f N <= f K) ->
  W.PrefixTotal f L -> B.SeqLimit f L.
Proof.
  intros f L Hmono [Hupper Hleast].
  apply SP.monotone_sup_limit; [exact Hmono|]. split.
  - intros x [N Hx]. rewrite Hx. apply Hupper.
  - intros E HE. apply Hleast. intro N. apply HE. exists N. reflexivity.
Qed.

Theorem BKDL30_DISSIPATION_PREFIX_TOTAL_IS_ACTUAL_LIMIT :
  forall T lambda a Dcum,
  (forall i, 0 <= lambda i) ->
  (forall N, M.OpenPrimitive T (M.critical_density lambda a N) (Dcum N)) ->
  forall t L, M.OpenTime T t ->
  W.PrefixTotal (fun N => Dcum N t) L ->
  B.SeqLimit (fun N => Dcum N t) L.
Proof.
  intros T lambda a Dcum Hlambda HD t L Ht HL.
  apply monotone_prefix_total_is_limit; [|exact HL].
  intros N K HNK. eapply BKDL20_DISSIPATION_CUTOFF_MONOTONE; eassumption.
Qed.

Theorem BKDL40_BOUNDED_DISSIPATION_PREFIXES_CONVERGE :
  forall T lambda a Dcum Cbound,
  (forall i, 0 <= lambda i) ->
  (forall N, M.OpenPrimitive T (M.critical_density lambda a N) (Dcum N)) ->
  (forall N t, M.OpenTime T t -> Dcum N t <= Cbound) ->
  forall t, M.OpenTime T t -> exists D,
    0 <= D <= Cbound /\
    W.PrefixTotal (fun N => Dcum N t) D /\
    B.SeqLimit (fun N => Dcum N t) D.
Proof.
  intros T lambda a Dcum Cbound Hlambda HD Hbound t Ht.
  destruct (W.CUMULATIVE_NONNEGATIVE_COMPLETION (fun N => Dcum N t) Cbound)
    as [D [HDbound Htotal]].
  - intro N. eapply BKDL10_DISSIPATION_CUMULATIVE_NONNEGATIVE; eassumption.
  - intro N. apply Hbound. exact Ht.
  - exists D. split; [exact HDbound|]. split; [exact Htotal|].
    eapply BKDL30_DISSIPATION_PREFIX_TOTAL_IS_ACTUAL_LIMIT; eassumption.
Qed.

(* The same cumulative total increases with physical time wherever both
   endpoint totals exist. This is a relation-level statement and does not
   select or assume an unrelated full dissipation function. *)
Theorem BKDL50_FULL_DISSIPATION_TIME_MONOTONE :
  forall T lambda a Dcum,
  (forall i, 0 <= lambda i) ->
  (forall N, M.OpenPrimitive T (M.critical_density lambda a N) (Dcum N)) ->
  forall s t Ds Dt, M.OpenTime T s -> M.OpenTime T t -> s <= t ->
  W.PrefixTotal (fun N => Dcum N s) Ds ->
  W.PrefixTotal (fun N => Dcum N t) Dt -> Ds <= Dt.
Proof.
  intros T lambda a Dcum Hlambda HD s t Ds Dt Hs Ht Hst HS HT.
  apply (proj2 HS). intro N. eapply Rle_trans; [|apply (proj1 HT)].
  apply (M.BKMC31_OPEN_PRIMITIVE_MONOTONE T
    (M.critical_density lambda a N) (Dcum N) (HD N)).
  - intros r Hr. apply M.critical_density_nonnegative. exact Hlambda.
  - exact Hs.
  - exact Ht.
  - exact Hst.
Qed.

Print Assumptions BKDL20_DISSIPATION_CUTOFF_MONOTONE.
Print Assumptions BKDL30_DISSIPATION_PREFIX_TOTAL_IS_ACTUAL_LIMIT.
Print Assumptions BKDL40_BOUNDED_DISSIPATION_PREFIXES_CONVERGE.
End BKQR_M7_DISSIPATION_LIMIT.
