From Stdlib Require Import Reals Lia Lra Psatz.
Require Import BKQR_CountableRange BKQR_BilinearKernel.
Require Import BKQR_FourierIndices.

Module BKQR_FOURIER_BLOCKS.
Import GP_COUNTABLE_RANGE BKQR_BILINEAR_KERNEL.
Import BKQR_FOURIER_INDICES.
Open Scope R_scope.

Lemma decode_mode_block : forall p tag, (tag<6)%nat ->
  decode_mode (6*p+tag)%nat=mode_decode p.
Proof.
  intros p tag Htag. unfold decode_mode.
  rewrite (proj1 (quotient_remainder p tag 6 ltac:(lia) Htag)). reflexivity.
Qed.

Lemma decode_tag_block : forall p tag, (tag<6)%nat ->
  decode_tag (6*p+tag)%nat=tag.
Proof.
  intros p tag Htag. unfold decode_tag.
  exact (proj2 (quotient_remainder p tag 6 ltac:(lia) Htag)).
Qed.

Lemma encode_mode_block : forall p tag,
  encode_index (mode_decode p) tag=(6*p+tag)%nat.
Proof. intros. unfold encode_index. rewrite mode_encode_decode. reflexivity. Qed.

Lemma block_sum_append : forall N M f,
  gp_sum (N+M) f=gp_sum N f+gp_sum M (fun j=>f (N+j)%nat).
Proof.
  intros N M. induction M; intros f.
  - rewrite Nat.add_0_r. simpl. ring.
  - rewrite Nat.add_succ_r. simpl. rewrite IHM. ring.
Qed.

Theorem BKFB10_EXACT_FINITE_BLOCK_SUM : forall width N f,
  gp_sum (width*N) f=
  gp_sum N (fun p=>gp_sum width (fun tag=>f (width*p+tag)%nat)).
Proof.
  intros width N. induction N; intros f.
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite Nat.mul_succ_r, block_sum_append, IHN. reflexivity.
Qed.

Theorem BKFB20_EXACT_DOUBLE_BLOCK_SUM : forall width N f,
  gp_sum (width*N) (fun j=>gp_sum (width*N) (f j))=
  gp_sum N (fun p=>gp_sum N (fun q=>
    gp_sum width (fun s=>gp_sum width (fun t=>
      f (width*p+s)%nat (width*q+t)%nat)))).
Proof.
  intros width N f. rewrite BKFB10_EXACT_FINITE_BLOCK_SUM.
  apply gp_sum_ext. intros p Hp.
  transitivity (gp_sum width (fun s=>gp_sum N (fun q=>
    gp_sum width (fun t=>f (width*p+s)%nat (width*q+t)%nat)))).
  - apply gp_sum_ext. intros s Hs. apply BKFB10_EXACT_FINITE_BLOCK_SUM.
  - apply sum_swap.
Qed.

Definition block_vector (x:nat->R) (p:nat) (axis:nat) : R*R :=
  (x (6*p+2*axis)%nat,x (6*p+2*axis+1)%nat).

Definition block_complex_energy (x:nat->R) (p:nat) : R :=
  gp_sum 3 (fun a=>
    fst(block_vector x p a)*fst(block_vector x p a)+
    snd(block_vector x p a)*snd(block_vector x p a)).

Theorem BKFB30_SIX_SCALARS_ARE_THREE_COMPLEX_COMPONENTS : forall x p,
  gp_sum 6 (fun tag=>x (6*p+tag)%nat*x (6*p+tag)%nat)=block_complex_energy x p.
Proof.
  intros x p. unfold block_complex_energy, block_vector. cbn [gp_sum fst snd].
  replace (6*p+2*0)%nat with (6*p+0)%nat by lia.
  replace (6*p+2*0+1)%nat with (6*p+1)%nat by lia.
  replace (6*p+2*1)%nat with (6*p+2)%nat by lia.
  replace (6*p+2*1+1)%nat with (6*p+3)%nat by lia.
  replace (6*p+2*2)%nat with (6*p+4)%nat by lia.
  replace (6*p+2*2+1)%nat with (6*p+5)%nat by lia.
  replace (6*p+0+1)%nat with (6*p+1)%nat by lia.
  replace (6*p+2+1)%nat with (6*p+3)%nat by lia.
  replace (6*p+4+1)%nat with (6*p+5)%nat by lia.
  ring.
Qed.

Theorem BKFB31_EXACT_FINITE_COMPLEX_ENERGY : forall x N,
  physical_prefix x (6*N)=gp_sum N (block_complex_energy x).
Proof.
  intros x N. unfold physical_prefix. rewrite BKFB10_EXACT_FINITE_BLOCK_SUM.
  apply gp_sum_ext. intros p Hp. apply BKFB30_SIX_SCALARS_ARE_THREE_COMPLEX_COMPONENTS.
Qed.

Theorem BKFB32_SCALAR_AND_COMPLEX_ENERGY_CAPS_EQUIVALENT : forall x E,
  PhysicalBound x E <-> forall N,gp_sum N (block_complex_energy x)<=E.
Proof.
  intros x E. split.
  - intros H N. rewrite <- BKFB31_EXACT_FINITE_COMPLEX_ENERGY. apply H.
  - intros H N. eapply Rle_trans with (r2:=physical_prefix x (6*N)).
    + apply prefix_monotone. lia.
    + rewrite BKFB31_EXACT_FINITE_COMPLEX_ENERGY. apply H.
Qed.

Theorem BKFB40_BLOCK_SUBSEQUENCE_PRESERVES_LIMIT : forall f L,
  SeqLimit f L -> SeqLimit (fun N=>f (6*N)%nat) L.
Proof.
  intros f L H eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. apply HN. lia.
Qed.

Print Assumptions BKFB20_EXACT_DOUBLE_BLOCK_SUM.
Print Assumptions BKFB32_SCALAR_AND_COMPLEX_ENERGY_CAPS_EQUIVALENT.
End BKQR_FOURIER_BLOCKS.
