(* Derived Fourier Schur bounds.  Generic closure properties are proved
   from the actual finite row/column absolute sums.  Six partner candidates
   come from the lattice convolution equation and the proved mode/tag
   encoder bijection.  The concrete convection coefficient bound then gives
   the Schur constant; no desired Schur property is assumed for that kernel. *)
From Stdlib Require Import Reals Arith Lra Psatz Lia Field.
Require Import BKQR_CountableRange BKQR_BilinearKernel
  BKQR_FourierIndices BKQR_FourierConvection.

Module BKQR_FOURIER_SCHUR.
Import GP_COUNTABLE_RANGE BKQR_BILINEAR_KERNEL
  BKQR_FOURIER_INDICES BKQR_FOURIER_CONVECTION.
Open Scope R_scope.

Lemma schur_bound_ext : forall K L C,
  (forall j k, K j k=L j k) -> SchurBound K C -> SchurBound L C.
Proof.
  intros K L C Hext [HC [Hrow Hcol]]. split; [exact HC|]. split.
  - intros j M. transitivity (gp_sum M (fun k=>Rabs (K j k))).
    + apply Req_le. apply gp_sum_ext. intros k Hk. rewrite Hext. reflexivity.
    + apply Hrow.
  - intros k N. transitivity (gp_sum N (fun j=>Rabs (K j k))).
    + apply Req_le. apply gp_sum_ext. intros j Hj. rewrite Hext. reflexivity.
    + apply Hcol.
Qed.

Lemma schur_bound_ext_iff : forall K L C,
  (forall j k, K j k=L j k) -> (SchurBound K C <-> SchurBound L C).
Proof.
  intros K L C Hext. split.
  - apply schur_bound_ext. exact Hext.
  - apply schur_bound_ext. intros j k. symmetry. apply Hext.
Qed.

Lemma schur_bound_dominate : forall K L C,
  SchurBound K C -> (forall j k, Rabs (L j k) <= Rabs (K j k)) ->
  SchurBound L C.
Proof.
  intros K L C [HC [Hrow Hcol]] Hdom. split; [exact HC|]. split.
  - intros j M. eapply Rle_trans; [apply gp_sum_le|apply Hrow].
    intros k Hk. apply Hdom.
  - intros k N. eapply Rle_trans; [apply gp_sum_le|apply Hcol].
    intros j Hj. apply Hdom.
Qed.

Lemma schur_bound_weaken : forall K C D,
  SchurBound K C -> C <= D -> SchurBound K D.
Proof.
  intros K C D [HC [Hrow Hcol]] HCD. split; [lra|]. split.
  - intros j M. eapply Rle_trans; [apply Hrow|exact HCD].
  - intros k N. eapply Rle_trans; [apply Hcol|exact HCD].
Qed.

Lemma schur_bound_zero : SchurBound (fun _ _=>0) 0.
Proof.
  split; [lra|]. split; intros i N;
    transitivity (gp_sum N (fun _=>0));
    try (apply Req_le; apply gp_sum_ext; intros; apply Rabs_R0);
    rewrite sum_zero; lra.
Qed.

Lemma schur_bound_scale : forall K C c,
  SchurBound K C -> SchurBound (fun j k=>c*K j k) (Rabs c*C).
Proof.
  intros K C c [HC [Hrow Hcol]]. split.
  - apply Rmult_le_pos; [apply Rabs_pos|exact HC].
  - split.
    + intros j M. transitivity (Rabs c*gp_sum M (fun k=>Rabs (K j k))).
      * apply Req_le. rewrite <- gp_sum_scale. apply gp_sum_ext.
        intros k Hk. apply Rabs_mult.
      * apply Rmult_le_compat_l; [apply Rabs_pos|apply Hrow].
    + intros k N. transitivity (Rabs c*gp_sum N (fun j=>Rabs (K j k))).
      * apply Req_le. rewrite <- gp_sum_scale. apply gp_sum_ext.
        intros j Hj. apply Rabs_mult.
      * apply Rmult_le_compat_l; [apply Rabs_pos|apply Hcol].
Qed.

Lemma schur_bound_add : forall K L C D,
  SchurBound K C -> SchurBound L D ->
  SchurBound (fun j k=>K j k+L j k) (C+D).
Proof.
  intros K L C D [HC [HKrow HKcol]] [HD [HLrow HLcol]].
  split; [lra|]. split.
  - intros j M.
    transitivity (gp_sum M (fun k=>Rabs (K j k)+Rabs (L j k))).
    + apply gp_sum_le. intros k Hk. apply Rabs_triang.
    + rewrite sum_plus. specialize (HKrow j M). specialize (HLrow j M). lra.
  - intros k N.
    transitivity (gp_sum N (fun j=>Rabs (K j k)+Rabs (L j k))).
    + apply gp_sum_le. intros j Hj. apply Rabs_triang.
    + rewrite sum_plus. specialize (HKcol k N). specialize (HLcol k N). lra.
Qed.

Lemma schur_bound_finite_sum : forall n
  (K : nat -> nat -> nat -> R) (C : nat -> R),
  (forall t, (t<n)%nat -> SchurBound (K t) (C t)) ->
  SchurBound (fun j k=>gp_sum n (fun t=>K t j k)) (gp_sum n C).
Proof.
  induction n as [|n IH]; intros K C HK; simpl.
  - exact schur_bound_zero.
  - apply schur_bound_add.
    + apply IH. intros t Ht. apply HK. lia.
    + apply HK. lia.
Qed.

Lemma schur_bound_transpose : forall K C,
  SchurBound K C -> SchurBound (fun j k=>K k j) C.
Proof. intros K C [HC [Hrow Hcol]]. repeat split; assumption. Qed.

Lemma schur_bound_transpose_iff : forall K C,
  SchurBound K C <-> SchurBound (fun j k=>K k j) C.
Proof.
  intros K C. split; intro H.
  - apply schur_bound_transpose. exact H.
  - exact (schur_bound_transpose (fun j k=>K k j) C H).
Qed.

Print Assumptions schur_bound_dominate.
Print Assumptions schur_bound_scale.
Print Assumptions schur_bound_finite_sum.

Definition index_indicator (target i : nat) : R :=
  if Nat.eq_dec i target then 1 else 0.

Lemma index_indicator_nonnegative : forall target i,
  0 <= index_indicator target i.
Proof. intros; unfold index_indicator; destruct (Nat.eq_dec i target); lra. Qed.

Lemma indicator_prefix_formula : forall target N,
  gp_sum N (index_indicator target) = if lt_dec target N then 1 else 0.
Proof.
  intros target N. induction N as [|N IH].
  - simpl. destruct (lt_dec target O); [lia|reflexivity].
  - change (gp_sum N (index_indicator target)+index_indicator target N =
      if lt_dec target (S N) then 1 else 0).
    rewrite IH. unfold index_indicator.
    destruct (Nat.eq_dec N target) as [Heq|Hneq].
    + subst N. destruct (lt_dec target target); [lia|].
      destruct (lt_dec target (S target)); [ring|lia].
    + destruct (lt_dec target N); destruct (lt_dec target (S N)); try lia; ring.
Qed.

Lemma indicator_prefix_bound : forall target N,
  gp_sum N (index_indicator target) <= 1.
Proof. intros; rewrite indicator_prefix_formula; destruct (lt_dec target N); lra. Qed.

Lemma sum_term_bounded_by_prefix : forall N f i,
  (forall j, 0 <= f j) -> (i < N)%nat -> f i <= gp_sum N f.
Proof.
  induction N as [|N IH]; intros f i Hpos Hi; [lia|]. simpl.
  destruct (Nat.eq_dec i N) as [Heq|Hneq].
  - subst i. pose proof (gp_sum_nonneg N f Hpos). lra.
  - assert (HiN : (i < N)%nat) by lia.
    specialize (IH f i Hpos HiN). specialize (Hpos N). lra.
Qed.

Lemma sum_constant_one : forall N, gp_sum N (fun _=>1)=INR N.
Proof.
  induction N as [|N IH]; [reflexivity|].
  change (gp_sum N (fun _=>1)+1=INR (S N)). rewrite IH, S_INR. ring.
Qed.

Lemma covered_entry_domination : forall (f : nat -> R) candidates degree A,
  0 <= A -> (forall i, Rabs (f i) <= A) ->
  (forall i, f i <> 0 -> exists tag, (tag < degree)%nat /\ i=candidates tag) ->
  forall i, Rabs (f i) <=
    A * gp_sum degree (fun tag => index_indicator (candidates tag) i).
Proof.
  intros f candidates degree A HA Hf Hcover i.
  assert (Hsumpos : 0 <= gp_sum degree
    (fun tag => index_indicator (candidates tag) i)).
  { apply gp_sum_nonneg. intro tag. apply index_indicator_nonnegative. }
  destruct (Req_dec (f i) 0) as [Hz|Hnz].
  - rewrite Hz, Rabs_R0. apply Rmult_le_pos; assumption.
  - destruct (Hcover i Hnz) as [tag [Htag Heq]].
    assert (Hterm : index_indicator (candidates tag) i=1).
    { unfold index_indicator. destruct (Nat.eq_dec i (candidates tag));
        [reflexivity|contradiction]. }
    pose proof (sum_term_bounded_by_prefix degree
      (fun t => index_indicator (candidates t) i) tag
      (fun t => index_indicator_nonnegative (candidates t) i) Htag) as Hone.
    cbn beta in Hone. rewrite Hterm in Hone. specialize (Hf i). nra.
Qed.

Lemma finite_branch_absolute_sum_bound : forall (f : nat -> R) candidates degree A,
  0 <= A -> (forall i, Rabs (f i) <= A) ->
  (forall i, f i <> 0 -> exists tag, (tag < degree)%nat /\ i=candidates tag) ->
  forall N, gp_sum N (fun i => Rabs (f i)) <= INR degree*A.
Proof.
  intros f candidates degree A HA Hf Hcover N.
  eapply Rle_trans with (r2:=gp_sum N
    (fun i => A*gp_sum degree (fun tag => index_indicator (candidates tag) i))).
  - apply gp_sum_le. intros i Hi. apply covered_entry_domination; assumption.
  - rewrite gp_sum_scale, sum_swap.
    assert (Hsum : gp_sum degree (fun tag =>
      gp_sum N (fun i => index_indicator (candidates tag) i)) <= INR degree).
    { rewrite <- sum_constant_one. apply gp_sum_le. intros tag Htag.
      apply indicator_prefix_bound. }
    pose proof (Rmult_le_compat_l A
      (gp_sum degree (fun tag => gp_sum N (fun i => index_indicator (candidates tag) i)))
      (INR degree) HA Hsum). nra.
Qed.

Theorem BKFS20_FINITE_BRANCH_COVERS_DERIVE_SCHUR :
  forall K (row_partner column_partner : nat -> nat -> nat) degree A,
  0 <= A -> (forall j l, Rabs (K j l) <= A) ->
  (forall j l, K j l <> 0 ->
    exists tag, (tag < degree)%nat /\ l=row_partner j tag) ->
  (forall j l, K j l <> 0 ->
    exists tag, (tag < degree)%nat /\ j=column_partner l tag) ->
  SchurBound K (INR degree*A).
Proof.
  intros K row_partner column_partner degree A HA Hbound Hrow Hcolumn.
  split.
  - apply Rmult_le_pos; [apply pos_INR|exact HA].
  - split.
    + intros j N. apply finite_branch_absolute_sum_bound
        with (candidates:=row_partner j); [exact HA|apply Hbound|].
      intros l Hnz. apply Hrow. exact Hnz.
    + intros l N. apply finite_branch_absolute_sum_bound
        with (candidates:=column_partner l); [exact HA|intro j; apply Hbound|].
      intros j Hnz. apply Hcolumn. exact Hnz.
Qed.

Definition mode_partner_index (m : Z3) (j tag : nat) : nat :=
  encode_index (partner m (decode_mode j)) tag.

Lemma convolution_support_partner_indices : forall m j l,
  mode_add (decode_mode j) (decode_mode l)=m ->
  l=mode_partner_index m j (decode_tag l) /\
  j=mode_partner_index m l (decode_tag j).
Proof.
  intros m j l Hsum. unfold mode_partner_index. split.
  - pose proof (mode_sum_partner m (decode_mode j) (decode_mode l) Hsum) as Hmode.
    pose proof (encode_decode_index l) as Hindex. rewrite Hmode in Hindex.
    symmetry. exact Hindex.
  - assert (Hsum' : mode_add (decode_mode l) (decode_mode j)=m).
    { rewrite mode_add_comm. exact Hsum. }
    pose proof (mode_sum_partner m (decode_mode l) (decode_mode j) Hsum') as Hmode.
    pose proof (encode_decode_index j) as Hindex. rewrite Hmode in Hindex.
    symmetry. exact Hindex.
Qed.

Theorem BKFS30_CONVOLUTION_SUPPORT_SCHUR : forall m K A,
  0 <= A -> (forall j l, Rabs (K j l) <= A) ->
  (forall j l, K j l <> 0 -> mode_add (decode_mode j) (decode_mode l)=m) ->
  SchurBound K (6*A).
Proof.
  intros m K A HA Hbound Hsupport.
  replace (6*A) with (INR 6*A) by (simpl; ring).
  apply BKFS20_FINITE_BRANCH_COVERS_DERIVE_SCHUR
    with (row_partner:=mode_partner_index m) (column_partner:=mode_partner_index m).
  - exact HA.
  - exact Hbound.
  - intros j l Hnz. exists (decode_tag l). split; [apply decode_tag_bound|].
    apply (proj1 (convolution_support_partner_indices m j l (Hsupport j l Hnz))).
  - intros j l Hnz. exists (decode_tag j). split; [apply decode_tag_bound|].
    apply (proj2 (convolution_support_partner_indices m j l (Hsupport j l Hnz))).
Qed.

Definition mode_matched_kernel (m : Z3) (amplitude : nat -> nat -> R)
  (j l : nat) : R :=
  if mode_eq_dec (mode_add (decode_mode j) (decode_mode l)) m
  then amplitude j l else 0.

Theorem BKFS31_MODE_MATCHED_KERNEL_SCHUR : forall m amplitude A,
  0 <= A -> (forall j l, Rabs (amplitude j l) <= A) ->
  SchurBound (mode_matched_kernel m amplitude) (6*A).
Proof.
  intros m amplitude A HA Hamp.
  apply BKFS30_CONVOLUTION_SUPPORT_SCHUR with (m:=m).
  - exact HA.
  - intros j l. unfold mode_matched_kernel.
    destruct (mode_eq_dec (mode_add (decode_mode j) (decode_mode l)) m).
    + apply Hamp.
    + rewrite Rabs_R0. exact HA.
  - intros j l Hnz. unfold mode_matched_kernel in Hnz.
    destruct (mode_eq_dec (mode_add (decode_mode j) (decode_mode l)) m)
      as [Heq|Hneq]; [exact Heq|]. contradiction.
Qed.

(* This is one fixed, explicit three-index tensor.  Both input tags and
   their lattice modes are decoded from the actual natural-number indices. *)
Definition indexed_convection_kernel (i j l : nat) : R :=
  mode_matched_kernel (decode_mode i)
    (fun a b => convection_coefficient (decode_mode i) (decode_tag i)
      (decode_tag a) (decode_tag b)) j l.

Definition indexed_convection_bound (i : nat) : R :=
  6 * coefficient_bound (decode_mode i) (decode_tag i).

Theorem BKFS40_INDEXED_CONVECTION_HAS_DERIVED_SCHUR_BOUND : forall i,
  SchurBound (indexed_convection_kernel i) (indexed_convection_bound i).
Proof.
  intro i. unfold indexed_convection_kernel, indexed_convection_bound.
  apply BKFS31_MODE_MATCHED_KERNEL_SCHUR.
  - apply coefficient_bound_nonnegative.
  - intros j l. apply convection_coefficient_abs_bound;
      apply decode_tag_bound.
Qed.

Lemma indexed_convection_bound_nonnegative : forall i,
  0 <= indexed_convection_bound i.
Proof. intro i. exact (proj1 (BKFS40_INDEXED_CONVECTION_HAS_DERIVED_SCHUR_BOUND i)). Qed.

Lemma indexed_convection_supported : forall i j l,
  indexed_convection_kernel i j l <> 0 ->
  mode_add (decode_mode j) (decode_mode l)=decode_mode i.
Proof.
  intros i j l Hnz. unfold indexed_convection_kernel, mode_matched_kernel in Hnz.
  destruct (mode_eq_dec (mode_add (decode_mode j) (decode_mode l)) (decode_mode i))
    as [Heq|Hneq]; [exact Heq|contradiction].
Qed.

Theorem indexed_convection_at_encoded_indices : forall m p q out left right,
  (out < 6)%nat -> (left < 6)%nat -> (right < 6)%nat ->
  indexed_convection_kernel (encode_index m out)
    (encode_index p left) (encode_index q right) =
  if mode_eq_dec (mode_add p q) m
  then convection_coefficient m out left right else 0.
Proof.
  intros m p q out left right Hout Hleft Hright.
  unfold indexed_convection_kernel, mode_matched_kernel.
  rewrite !decode_mode_encode, !decode_tag_encode by assumption. reflexivity.
Qed.

Corollary indexed_convection_on_matching_modes : forall m p q out left right,
  (out < 6)%nat -> (left < 6)%nat -> (right < 6)%nat -> mode_add p q=m ->
  indexed_convection_kernel (encode_index m out)
    (encode_index p left) (encode_index q right) =
  convection_coefficient m out left right.
Proof.
  intros m p q out left right Hout Hleft Hright Hsum.
  rewrite indexed_convection_at_encoded_indices by assumption.
  destruct (mode_eq_dec (mode_add p q) m); [reflexivity|contradiction].
Qed.

Print Assumptions BKFS20_FINITE_BRANCH_COVERS_DERIVE_SCHUR.
Print Assumptions BKFS30_CONVOLUTION_SUPPORT_SCHUR.
Print Assumptions BKFS31_MODE_MATCHED_KERNEL_SCHUR.
Print Assumptions BKFS40_INDEXED_CONVECTION_HAS_DERIVED_SCHUR_BOUND.
Print Assumptions indexed_convection_at_encoded_indices.
End BKQR_FOURIER_SCHUR.
