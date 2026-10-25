From Stdlib Require Import Reals Lra Psatz Lia ZArith Field.
Require Import BKQR_CountableRange BKQR_FourierIndices.

(* Literal vector/complex decoration of the supplied finite scalar Fourier
   product convention: exp(i*k.x), hence +i for a spatial derivative.
   The Leray matrix and all six real scalar coefficient tags are explicit.
   No physical source functional or coefficient bound is supplied. *)
Module BKQR_FOURIER_CONVECTION.
Import GP_COUNTABLE_RANGE BKQR_FOURIER_INDICES.
Open Scope R_scope.

Definition C2 := (R*R)%type.
Definition cre (z:C2) : R := fst z.
Definition cim (z:C2) : R := snd z.
Definition czero : C2 := (0,0).
Definition ci : C2 := (0,1).
Definition cadd (z w:C2) : C2 := (cre z+cre w,cim z+cim w).
Definition cmul (z w:C2) : C2 :=
  (cre z*cre w-cim z*cim w,cre z*cim w+cim z*cre w).
Definition cscale (a:R) (z:C2) : C2 := (a*cre z,a*cim z).
Definition csum3 (f:nat->C2) : C2 := cadd (cadd (f 0%nat) (f 1%nat)) (f 2%nat).
Definition ComplexVector := nat -> C2.

Definition wave (m:Z3) (a:nat) : R :=
  match a with O => IZR (mode_x m) | S O => IZR (mode_y m)
  | _ => IZR (mode_z m) end.
Definition mode_norm2 (m:Z3) : R :=
  wave m 0%nat*wave m 0%nat+wave m 1%nat*wave m 1%nat+
  wave m 2%nat*wave m 2%nat.
Definition delta_axis (a b:nat) : R := if Nat.eq_dec a b then 1 else 0.
Definition leray_entry (m:Z3) (a b:nat) : R :=
  delta_axis a b-wave m a*wave m b/mode_norm2 m.

Lemma mode_norm2_nonnegative : forall m, 0 <= mode_norm2 m.
Proof. intro m. unfold mode_norm2. nra. Qed.
Lemma mode_norm2_nonneg : forall m, 0 <= mode_norm2 m.
Proof. exact mode_norm2_nonnegative. Qed.

Definition complex_dot (m:Z3) (u:ComplexVector) : C2 :=
  csum3 (fun a=>cscale (wave m a) (u a)).
Definition leray_apply (m:Z3) (v:ComplexVector) : ComplexVector :=
  fun r=>csum3 (fun b=>cscale (leray_entry m r b) (v b)).
Definition projected_convection (m:Z3) (u v:ComplexVector) : ComplexVector :=
  fun r=>cmul ci (cmul (complex_dot m u) (leray_apply m v r)).

Definition vector_from_scalars (x:nat->R) (a:nat) : C2 :=
  (x (2*a)%nat,x (S (2*a))).
Definition scalar_tag (v:ComplexVector) (tag:nat) : R :=
  if Nat.eq_dec (tag_phase tag) O then cre (v (tag_axis tag))
  else cim (v (tag_axis tag)).

(* The real and imaginary components of i*z*w. *)
Definition iphase (r s t:nat) : R :=
  match r,s,t with
  | O,O,S O => -1 | O,S O,O => -1
  | S O,O,O => 1 | S O,S O,S O => -1
  | _,_,_ => 0
  end.

Definition convection_coefficient (m:Z3) (out left right:nat) : R :=
  wave m (tag_axis left)*leray_entry m (tag_axis out) (tag_axis right)*
    iphase (tag_phase out) (tag_phase left) (tag_phase right).

Definition coefficient_bound (m:Z3) (out:nat) : R :=
  gp_sum 3 (fun a=>Rabs (wave m a))*
  gp_sum 3 (fun b=>Rabs (leray_entry m (tag_axis out) b)).

Lemma scalar_tag_vector_from_scalars : forall x tag, (tag<6)%nat ->
  scalar_tag (vector_from_scalars x) tag=x tag.
Proof.
  intros x [|[|[|[|[|[|tag]]]]]] Htag;
    cbn [scalar_tag vector_from_scalars tag_axis tag_phase cre cim];
    try reflexivity; lia.
Qed.

Lemma tag_axis_lt_three : forall tag, (tag<6)%nat -> (tag_axis tag<3)%nat.
Proof.
  intros tag Htag. unfold tag_axis. apply Nat.Div0.div_lt_upper_bound; lia.
Qed.

Lemma iphase_absolute_bound : forall r s t, Rabs (iphase r s t) <= 1.
Proof.
  intros [|[|r]] [|[|s]] [|[|t]]; cbn [iphase];
    rewrite ?Rabs_Ropp, ?Rabs_R0, ?Rabs_R1; try lra;
    rewrite Rabs_left by lra; lra.
Qed.

Lemma component_absolute_bound : forall f a, (a<3)%nat ->
  Rabs (f a) <= gp_sum 3 (fun b=>Rabs (f b)).
Proof.
  intros f [|[|[|a]]] Ha; cbn [gp_sum];
    pose proof (Rabs_pos (f 0%nat)); pose proof (Rabs_pos (f 1%nat));
    pose proof (Rabs_pos (f 2%nat)); try lia; lra.
Qed.

Lemma coefficient_bound_nonnegative : forall m out, 0 <= coefficient_bound m out.
Proof.
  intros. unfold coefficient_bound. apply Rmult_le_pos;
    apply gp_sum_nonneg; intro; apply Rabs_pos.
Qed.

Theorem convection_coefficient_abs_bound : forall m out left right,
  (out<6)%nat -> (left<6)%nat -> (right<6)%nat ->
  Rabs (convection_coefficient m out left right) <= coefficient_bound m out.
Proof.
  intros m out left right Hout Hleft Hright.
  unfold convection_coefficient. rewrite !Rabs_mult.
  pose proof (iphase_absolute_bound (tag_phase out) (tag_phase left)
    (tag_phase right)) as Hphase.
  pose proof (component_absolute_bound (wave m) (tag_axis left)
    (tag_axis_lt_three left Hleft)) as Hwave.
  pose proof (component_absolute_bound (leray_entry m (tag_axis out))
    (tag_axis right) (tag_axis_lt_three right Hright)) as Hproj.
  eapply Rle_trans with (r2:=Rabs (wave m (tag_axis left))*
    Rabs (leray_entry m (tag_axis out) (tag_axis right))*1).
  - apply Rmult_le_compat_l; [apply Rmult_le_pos; apply Rabs_pos|exact Hphase].
  - rewrite Rmult_1_r. unfold coefficient_bound.
    apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Hwave|exact Hproj].
Qed.

Theorem CONVECTION_COMPLEX_REALIFICATION : forall m out u v,
  (out<6)%nat ->
  scalar_tag (projected_convection m u v) out =
  gp_sum 6 (fun s=>gp_sum 6 (fun t=>convection_coefficient m out s t*
    scalar_tag u s*scalar_tag v t)).
Proof.
  intros m [|[|[|[|[|[|out]]]]]] u v Hout; try lia;
    cbv [gp_sum convection_coefficient iphase scalar_tag tag_axis tag_phase
      Nat.div Nat.modulo Nat.divmod Nat.eq_dec
      projected_convection complex_dot leray_apply csum3 cadd cmul cscale ci cre cim fst snd];
    cbn; ring.
Qed.

Theorem CONVECTION_REALIFICATION : forall m out x y, (out<6)%nat ->
  scalar_tag (projected_convection m (vector_from_scalars x)
    (vector_from_scalars y)) out =
  gp_sum 6 (fun s=>gp_sum 6 (fun t=>convection_coefficient m out s t*x s*y t)).
Proof.
  intros m out x y Hout. rewrite CONVECTION_COMPLEX_REALIFICATION by exact Hout.
  apply gp_sum_ext. intros s Hs. apply gp_sum_ext. intros t Ht.
  rewrite !scalar_tag_vector_from_scalars by assumption. reflexivity.
Qed.

Lemma wave_add : forall p q a,
  wave (mode_add p q) a=wave p a+wave q a.
Proof.
  intros p q [|[|a]]; unfold wave, mode_add; cbn;
    rewrite plus_IZR; reflexivity.
Qed.

Lemma complex_dot_add : forall p q u,
  complex_dot (mode_add p q) u=cadd (complex_dot p u) (complex_dot q u).
Proof.
  intros p q u. unfold complex_dot, csum3.
  rewrite !wave_add. unfold cadd,cscale,cre,cim. cbn. f_equal; ring.
Qed.

Lemma complex_dot_derivative_shift : forall m p q u,
  mode_add p q=m -> complex_dot p u=czero -> complex_dot q u=complex_dot m u.
Proof.
  intros m p q u Htriad Hdiv. rewrite <- Htriad, complex_dot_add, Hdiv.
  destruct (complex_dot q u) as [r i]. unfold cadd,czero,cre,cim. cbn.
  f_equal; ring.
Qed.

Lemma leray_apply_complex_scale : forall m z v r,
  leray_apply m (fun a=>cmul z (v a)) r=cmul z (leray_apply m v r).
Proof.
  intros m [zr zi] v r.
  unfold leray_apply,csum3,cadd,cscale,cmul,cre,cim. cbn.
  f_equal; ring.
Qed.

Lemma cmul_associative : forall z w v, cmul (cmul z w) v=cmul z (cmul w v).
Proof.
  intros [zr zi] [wr wi] [vr vi]. unfold cmul,cre,cim. cbn. f_equal; ring.
Qed.

Definition advective_convection (m q:Z3) (u v:ComplexVector) : ComplexVector :=
  leray_apply m (fun r=>cmul ci (cmul (complex_dot q u) (v r))).

Theorem CONVECTION_DERIVATIVE_MOVES_TO_OUTPUT : forall m p q u v,
  mode_add p q=m -> complex_dot p u=czero -> forall r,
  advective_convection m q u v r=projected_convection m u v r.
Proof.
  intros m p q u v Htriad Hdiv r. unfold advective_convection.
  rewrite (complex_dot_derivative_shift m p q u Htriad Hdiv).
  unfold projected_convection.
  rewrite (leray_apply_complex_scale m ci
    (fun a=>cmul (complex_dot m u) (v a)) r).
  rewrite (leray_apply_complex_scale m (complex_dot m u) v r).
  reflexivity.
Qed.

Print Assumptions CONVECTION_REALIFICATION.
Print Assumptions convection_coefficient_abs_bound.
Print Assumptions CONVECTION_DERIVATIVE_MOVES_TO_OUTPUT.
End BKQR_FOURIER_CONVECTION.
