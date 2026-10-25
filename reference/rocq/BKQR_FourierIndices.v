(* A concrete enumeration of every Fourier mode and all six real scalar
   components of a complex three-vector.  No enumeration is postulated. *)
From Stdlib Require Import Arith Cantor ZArith Lia.

Module BKQR_FOURIER_INDICES.

Definition signed_encode (z : Z) : nat :=
  if Z_le_dec 0 z then (2 * Z.to_nat z)%nat
  else S (2 * Z.to_nat (-z-1)).
Definition signed_decode (n : nat) : Z :=
  if Nat.eq_dec (n mod 2) 0 then Z.of_nat (n / 2)
  else (- Z.of_nat (n / 2) - 1)%Z.

Lemma quotient_remainder : forall n b d : nat,
  0 < d -> b < d ->
  (d*n+b)/d = n /\ (d*n+b) mod d = b.
Proof.
  intros n b d Hd Hb.
  split; symmetry.
  - apply Nat.div_unique with (r := b); [exact Hb|reflexivity].
  - apply Nat.mod_unique with (q := n); [exact Hb|reflexivity].
Qed.

Theorem signed_decode_encode : forall z, signed_decode (signed_encode z) = z.
Proof.
  intro z. unfold signed_encode. destruct (Z_le_dec 0 z) as [Hz|Hz].
  - unfold signed_decode.
    replace (2 * Z.to_nat z)%nat with (2 * Z.to_nat z + 0)%nat by lia.
    destruct (quotient_remainder (Z.to_nat z) 0 2 ltac:(lia) ltac:(lia)) as [Hq Hr].
    rewrite Hq, Hr. destruct (Nat.eq_dec 0 0); [|contradiction].
    apply Z2Nat.id. exact Hz.
  - unfold signed_decode.
    replace (S (2 * Z.to_nat (- z - 1))) with
      (2 * Z.to_nat (-z-1) + 1)%nat by lia.
    destruct (quotient_remainder (Z.to_nat (-z-1)) 1 2 ltac:(lia) ltac:(lia)) as [Hq Hr].
    rewrite Hq, Hr. destruct (Nat.eq_dec 1 0); [lia|].
    rewrite Z2Nat.id by lia. lia.
Qed.

Theorem signed_encode_decode : forall n, signed_encode (signed_decode n) = n.
Proof.
  intro n. pose proof (Nat.div_mod n 2 ltac:(lia)) as Hdiv.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as Hmod.
  unfold signed_decode. destruct (Nat.eq_dec (n mod 2) 0) as [Hr|Hr].
  - unfold signed_encode. destruct (Z_le_dec 0 (Z.of_nat (n/2))) as [Hz|Hz].
    + rewrite Nat2Z.id. lia.
    + pose proof (Nat2Z.is_nonneg (n/2)). lia.
  - unfold signed_encode.
    destruct (Z_le_dec 0 (- Z.of_nat (n/2)-1)) as [Hz|Hz].
    + pose proof (Nat2Z.is_nonneg (n/2)). lia.
    + replace (- (- Z.of_nat (n/2)-1)-1)%Z with (Z.of_nat (n/2)) by lia.
      rewrite Nat2Z.id. lia.
Qed.

Record Z3 := mkZ3 { mode_x : Z; mode_y : Z; mode_z : Z }.
Definition mode_zero := mkZ3 0 0 0.
Definition mode_add (p q : Z3) := mkZ3
  (mode_x p + mode_x q) (mode_y p + mode_y q) (mode_z p + mode_z q).
Definition mode_sub (p q : Z3) := mkZ3
  (mode_x p - mode_x q) (mode_y p - mode_y q) (mode_z p - mode_z q).
Definition mode_neg (p : Z3) := mode_sub mode_zero p.
Definition mode_eq_dec : forall p q : Z3, {p=q}+{p<>q}.
Proof. decide equality; apply Z.eq_dec. Defined.

Definition mode_encode (p : Z3) : nat := Cantor.to_nat
  (signed_encode (mode_x p), Cantor.to_nat
    (signed_encode (mode_y p), signed_encode (mode_z p))).
Definition mode_decode (n : nat) : Z3 :=
  let '(x,yz) := Cantor.of_nat n in
  let '(y,z) := Cantor.of_nat yz in
  mkZ3 (signed_decode x) (signed_decode y) (signed_decode z).

Theorem mode_decode_encode : forall p, mode_decode (mode_encode p) = p.
Proof.
  intros [x y z]. unfold mode_encode, mode_decode.
  cbn [mode_x mode_y mode_z]. rewrite !Cantor.cancel_of_to.
  cbn. rewrite !signed_decode_encode. reflexivity.
Qed.

Theorem mode_encode_decode : forall n, mode_encode (mode_decode n) = n.
Proof.
  intro n. unfold mode_decode.
  destruct (Cantor.of_nat n) as [x yz] eqn:Hxy.
  destruct (Cantor.of_nat yz) as [y z] eqn:Hyz.
  unfold mode_encode. cbn [mode_x mode_y mode_z]. rewrite !signed_encode_decode.
  pose proof (Cantor.cancel_to_of yz) as Hyz'. rewrite Hyz in Hyz'.
  rewrite Hyz'. pose proof (Cantor.cancel_to_of n) as Hn.
  rewrite Hxy in Hn. exact Hn.
Qed.

Theorem mode_encode_injective : forall p q, mode_encode p = mode_encode q -> p=q.
Proof.
  intros p q H. apply (f_equal mode_decode) in H.
  rewrite !mode_decode_encode in H. exact H.
Qed.
Theorem mode_decode_injective : forall n m, mode_decode n = mode_decode m -> n=m.
Proof.
  intros n m H. apply (f_equal mode_encode) in H.
  rewrite !mode_encode_decode in H. exact H.
Qed.

(* Tags 0,1 are Re/Im of the x component; 2,3 of y; 4,5 of z. *)
Definition tag_axis (tag : nat) : nat := tag / 2.
Definition tag_phase (tag : nat) : nat := tag mod 2.
Definition encode_index (p : Z3) (tag : nat) : nat := 6 * mode_encode p + tag.
Definition decode_mode (n : nat) : Z3 := mode_decode (n / 6).
Definition decode_tag (n : nat) : nat := n mod 6.

Theorem decode_tag_bound : forall n, decode_tag n < 6.
Proof. intro n. apply Nat.mod_upper_bound. lia. Qed.
Theorem tag_axis_bound : forall tag, tag < 6 -> tag_axis tag < 3.
Proof.
  intros tag Htag. unfold tag_axis.
  pose proof (Nat.div_mod tag 2 ltac:(lia)). lia.
Qed.
Theorem tag_phase_bound : forall tag, tag_phase tag < 2.
Proof. intro tag. apply Nat.mod_upper_bound. lia. Qed.
Theorem tag_reconstruction : forall tag,
  2 * tag_axis tag + tag_phase tag = tag.
Proof. intro tag. symmetry. apply Nat.div_mod. lia. Qed.

Theorem decode_mode_encode : forall p tag, tag < 6 ->
  decode_mode (encode_index p tag) = p.
Proof.
  intros p tag Htag. unfold decode_mode, encode_index.
  rewrite (proj1 (quotient_remainder (mode_encode p) tag 6 ltac:(lia) Htag)).
  apply mode_decode_encode.
Qed.
Theorem decode_tag_encode : forall p tag, tag < 6 ->
  decode_tag (encode_index p tag) = tag.
Proof.
  intros p tag Htag. unfold decode_tag, encode_index.
  exact (proj2 (quotient_remainder (mode_encode p) tag 6 ltac:(lia) Htag)).
Qed.
Theorem encode_decode_index : forall n,
  encode_index (decode_mode n) (decode_tag n) = n.
Proof.
  intro n. unfold encode_index, decode_mode, decode_tag.
  rewrite mode_encode_decode. symmetry. apply Nat.div_mod. lia.
Qed.

Theorem encode_index_injective : forall p q a b, a < 6 -> b < 6 ->
  encode_index p a = encode_index q b -> p=q /\ a=b.
Proof.
  intros p q a b Ha Hb H. split.
  - apply (f_equal decode_mode) in H. rewrite !decode_mode_encode in H by assumption.
    exact H.
  - apply (f_equal decode_tag) in H. rewrite !decode_tag_encode in H by assumption.
    exact H.
Qed.
Theorem decode_pair_injective : forall n m,
  decode_mode n = decode_mode m -> decode_tag n = decode_tag m -> n=m.
Proof.
  intros n m Hmode Htag. rewrite <- (encode_decode_index n), <- (encode_decode_index m).
  rewrite Hmode, Htag. reflexivity.
Qed.
Theorem index_surjective : forall p tag, tag < 6 -> exists n,
  decode_mode n = p /\ decode_tag n = tag.
Proof.
  intros p tag Htag. exists (encode_index p tag). split;
    [apply decode_mode_encode|apply decode_tag_encode]; exact Htag.
Qed.

Definition partner (m p : Z3) := mode_sub m p.
Theorem partner_involution : forall m p, partner m (partner m p) = p.
Proof. intros [mx my mz] [px py pz]. unfold partner, mode_sub; simpl.
  f_equal; lia. Qed.
Theorem partner_injective : forall m p q, partner m p = partner m q -> p=q.
Proof.
  intros m p q H. apply (f_equal (partner m)) in H.
  rewrite !partner_involution in H. exact H.
Qed.
Theorem mode_add_partner : forall m p, mode_add p (partner m p) = m.
Proof. intros [mx my mz] [px py pz]. unfold partner, mode_sub, mode_add; simpl.
  f_equal; lia. Qed.
Theorem mode_sum_partner : forall m p q, mode_add p q = m -> q = partner m p.
Proof.
  intros [mx my mz] [px py pz] [qx qy qz] H.
  unfold mode_add in H; simpl in H. inversion H.
  unfold partner, mode_sub; simpl. f_equal; lia.
Qed.
Theorem mode_add_comm : forall p q, mode_add p q = mode_add q p.
Proof. intros [px py pz] [qx qy qz]. unfold mode_add; simpl. f_equal; lia. Qed.
Theorem mode_sub_add : forall m p, mode_add (mode_sub m p) p = m.
Proof. intros. rewrite mode_add_comm. apply mode_add_partner. Qed.

End BKQR_FOURIER_INDICES.
