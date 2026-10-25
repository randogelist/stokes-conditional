
From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

Module NSE_GP_COMPLEX_HELICAL_ADAPTER.

Definition C2 := (R * R)%type.

Definition cre (z : C2) : R := fst z.
Definition cim (z : C2) : R := snd z.

Definition cadd (z w : C2) : C2 :=
  (cre z + cre w, cim z + cim w).

Definition cscale (a : R) (z : C2) : C2 :=
  (a * cre z, a * cim z).

Definition cconj (z : C2) : C2 :=
  (cre z, - cim z).

Definition cmul (z w : C2) : C2 :=
  (cre z * cre w - cim z * cim w,
   cre z * cim w + cim z * cre w).

Definition ceq (z w : C2) : Prop :=
  cre z = cre w /\ cim z = cim w.

Definition ctriad (C uk up uq : C2) : R :=
  cre (cmul (cmul (cmul C (cconj uk)) up) uq).

Definition csource1 (C Nk up uq : C2) : R :=
  cre (cmul (cmul (cmul C (cconj Nk)) up) uq).

Definition csource2 (C uk Np uq : C2) : R :=
  cre (cmul (cmul (cmul C (cconj uk)) Np) uq).

Definition csource3 (C uk up Nq : C2) : R :=
  cre (cmul (cmul (cmul C (cconj uk)) up) Nq).

Theorem GPCH00_CEQ_REFL :
  forall z : C2, ceq z z.
Proof.
  intro z.
  unfold ceq.
  split; reflexivity.
Qed.

Theorem GPCH01_CEQ_COMPONENTS :
  forall z w : C2,
    ceq z w ->
    cre z = cre w /\ cim z = cim w.
Proof.
  intros z w H.
  exact H.
Qed.

Theorem GPCH02_CMUL_REAL :
  forall z w : C2,
    cre (cmul z w) =
      cre z * cre w - cim z * cim w.
Proof.
  intros z w.
  reflexivity.
Qed.

Theorem GPCH03_CMUL_IMAG :
  forall z w : C2,
    cim (cmul z w) =
      cre z * cim w + cim z * cre w.
Proof.
  intros z w.
  reflexivity.
Qed.

(* Multilinearity in the interaction coefficient. *)
Theorem GPCH10_CTRIAD_SCALE_C :
  forall C uk up uq : C2, forall a : R,
    ctriad (cscale a C) uk up uq
      = a * ctriad C uk up uq.
Proof.
  intros [Cr Ci] [kr ki] [pr pi] [qr qi] a.
  unfold ctriad, cscale, cconj, cmul, cre, cim.
  simpl.
  ring.
Qed.

(* Multilinearity identities needed for the three-leg product rule. *)
Theorem GPCH11_CTRIAD_SCALE_UK :
  forall C uk up uq : C2, forall a : R,
    ctriad C (cscale a uk) up uq
      = a * ctriad C uk up uq.
Proof.
  intros [Cr Ci] [kr ki] [pr pi] [qr qi] a.
  unfold ctriad, cscale, cconj, cmul, cre, cim.
  simpl.
  ring.
Qed.

Theorem GPCH12_CTRIAD_SCALE_UP :
  forall C uk up uq : C2, forall a : R,
    ctriad C uk (cscale a up) uq
      = a * ctriad C uk up uq.
Proof.
  intros [Cr Ci] [kr ki] [pr pi] [qr qi] a.
  unfold ctriad, cscale, cconj, cmul, cre, cim.
  simpl.
  ring.
Qed.

Theorem GPCH13_CTRIAD_SCALE_UQ :
  forall C uk up uq : C2, forall a : R,
    ctriad C uk up (cscale a uq)
      = a * ctriad C uk up uq.
Proof.
  intros [Cr Ci] [kr ki] [pr pi] [qr qi] a.
  unfold ctriad, cscale, cconj, cmul, cre, cim.
  simpl.
  ring.
Qed.

(* Componentwise complex modal ODE certificate. *)
Definition CModalEq
  (nu lambda : R) (u du N : C2) : Prop :=
  ceq (cadd du (cscale (nu*lambda) u)) N.

(* Exact cubic real-part Leibniz relation supplied by absolute continuity. *)
Definition CTriadLeibniz
  (C uk up uq duk dup duq : C2) (dc : R) : Prop :=
  dc =
    ctriad C duk up uq
    + ctriad C uk dup uq
    + ctriad C uk up duq.

Theorem GPCH20_COMPLEX_THREE_LEG_SOURCE_SPLIT :
  forall
    (C uk up uq duk dup duq Nk Np Nq : C2)
    (nu lk lp lq dc : R),
    CModalEq nu lk uk duk Nk ->
    CModalEq nu lp up dup Np ->
    CModalEq nu lq uq duq Nq ->
    CTriadLeibniz C uk up uq duk dup duq dc ->
    dc + nu*(lk+lp+lq)*ctriad C uk up uq
      =
      csource1 C Nk up uq
      + csource2 C uk Np uq
      + csource3 C uk up Nq.
Proof.
  intros
    [Cr Ci] [kr ki] [pr pi] [qr qi]
    [dkr dki] [dpr dpi] [dqr dqi]
    [Nkr Nki] [Npr Npi] [Nqr Nqi]
    nu lk lp lq dc
    Hk Hp Hq Hdc.
  unfold CModalEq, ceq, cadd, cscale, cre, cim in Hk, Hp, Hq.
  simpl in Hk, Hp, Hq.
  destruct Hk as [Hkr Hki].
  destruct Hp as [Hpr Hpi].
  destruct Hq as [Hqr Hqi].
  unfold CTriadLeibniz, ctriad, csource1, csource2, csource3,
         cconj, cmul, cre, cim in Hdc |- *.
  simpl in Hdc |- *.
  assert (Hdkr : dkr = Nkr - (nu*lk)*kr) by lra.
  assert (Hdki : dki = Nki - (nu*lk)*ki) by lra.
  assert (Hdpr : dpr = Npr - (nu*lp)*pr) by lra.
  assert (Hdpi : dpi = Npi - (nu*lp)*pi) by lra.
  assert (Hdqr : dqr = Nqr - (nu*lq)*qr) by lra.
  assert (Hdqi : dqi = Nqi - (nu*lq)*qi) by lra.
  rewrite Hdc, Hdkr, Hdki, Hdpr, Hdpi, Hdqr, Hdqi.
  ring.
Qed.

(* The cubic work is invariant under representation as real/imaginary pairs:
   the theorem below freezes the exact polynomial form used by the adapter. *)
Theorem GPCH21_CTRIAD_POLYNOMIAL_FORM :
  forall Cr Ci kr ki pr pi qr qi : R,
    ctriad (Cr,Ci) (kr,ki) (pr,pi) (qr,qi)
    =
    (((Cr*kr + Ci*ki)*pr - (Ci*kr - Cr*ki)*pi)*qr
     -
     ((Cr*kr + Ci*ki)*pi + (Ci*kr - Cr*ki)*pr)*qi).
Proof.
  intros.
  unfold ctriad, cconj, cmul, cre, cim.
  simpl.
  ring.
Qed.

(* Rank-one one-leg source star in complex-pair coordinates:
   the real bilinear star coefficient is still outer-product generated. *)
Definition star_real (x y : C2) : R :=
  cre x * cre y + cim x * cim y.

Theorem GPCH30_STAR_REAL_SYMMETRIC :
  forall x y : C2,
    star_real x y = star_real y x.
Proof.
  intros [xr xi] [yr yi].
  unfold star_real, cre, cim.
  simpl.
  ring.
Qed.

Theorem GPCH31_STAR_RANK_ONE_MINOR :
  forall x1 x2 y1 y2 : R,
    (x1*y1)*(x2*y2) - (x1*y2)*(x2*y1) = 0.
Proof.
  intros; ring.
Qed.

(* Abstract certificate that the analytic Leray-Hopf layer must instantiate. *)
Definition ComplexTriadCertificate
  (C uk up uq duk dup duq Nk Np Nq : C2)
  (nu lk lp lq dc : R) : Prop :=
  CModalEq nu lk uk duk Nk /\
  CModalEq nu lp up dup Np /\
  CModalEq nu lq uq duq Nq /\
  CTriadLeibniz C uk up uq duk dup duq dc.

Theorem GPCH40_CERTIFICATE_GIVES_COMPLEX_THREE_SOURCE :
  forall
    (C uk up uq duk dup duq Nk Np Nq : C2)
    (nu lk lp lq dc : R),
    ComplexTriadCertificate
      C uk up uq duk dup duq Nk Np Nq nu lk lp lq dc ->
    dc + nu*(lk+lp+lq)*ctriad C uk up uq
      =
      csource1 C Nk up uq
      + csource2 C uk Np uq
      + csource3 C uk up Nq.
Proof.
  intros C uk up uq duk dup duq Nk Np Nq nu lk lp lq dc H.
  destruct H as [Hk [Hp [Hq Hdc]]].
  eapply GPCH20_COMPLEX_THREE_LEG_SOURCE_SPLIT; eauto.
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_COMPLEX_HELICAL_ADAPTER.

Check NSE_GP_COMPLEX_HELICAL_ADAPTER.GPCH10_CTRIAD_SCALE_C.
Check NSE_GP_COMPLEX_HELICAL_ADAPTER.GPCH11_CTRIAD_SCALE_UK.
Check NSE_GP_COMPLEX_HELICAL_ADAPTER.GPCH12_CTRIAD_SCALE_UP.
Check NSE_GP_COMPLEX_HELICAL_ADAPTER.GPCH13_CTRIAD_SCALE_UQ.
Check NSE_GP_COMPLEX_HELICAL_ADAPTER.GPCH20_COMPLEX_THREE_LEG_SOURCE_SPLIT.
Check NSE_GP_COMPLEX_HELICAL_ADAPTER.GPCH21_CTRIAD_POLYNOMIAL_FORM.
Check NSE_GP_COMPLEX_HELICAL_ADAPTER.GPCH30_STAR_REAL_SYMMETRIC.
Check NSE_GP_COMPLEX_HELICAL_ADAPTER.GPCH31_STAR_RANK_ONE_MINOR.
Check NSE_GP_COMPLEX_HELICAL_ADAPTER.GPCH40_CERTIFICATE_GIVES_COMPLEX_THREE_SOURCE.
