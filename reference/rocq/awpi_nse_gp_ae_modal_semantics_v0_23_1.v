
From Stdlib Require Import Reals Lra Psatz.
Require Import awpi_nse_gp_complex_helical_adapter_v0_14_1.
Open Scope R_scope.

Module NSE_GP_AE_MODAL_SEMANTICS.

Module CH := NSE_GP_COMPLEX_HELICAL_ADAPTER.

(* Abstract co-null calculus.  The analytic measure-theory layer supplies a
   concrete predicate CoNull; this file needs only monotonicity and finite
   intersection closure. *)
Record CoNullCalculus (CoNull : (R -> Prop) -> Prop) : Prop := {
  cn_all :
    CoNull (fun _ => True);
  cn_mono :
    forall P Q : R -> Prop,
      CoNull P ->
      (forall t : R, P t -> Q t) ->
      CoNull Q;
  cn_inter :
    forall P Q : R -> Prop,
      CoNull P ->
      CoNull Q ->
      CoNull (fun t => P t /\ Q t)
}.

Theorem GPAE00_INTER3 :
  forall CoNull : (R -> Prop) -> Prop,
    CoNullCalculus CoNull ->
    forall P Q S : R -> Prop,
      CoNull P ->
      CoNull Q ->
      CoNull S ->
      CoNull (fun t => P t /\ Q t /\ S t).
Proof.
  intros CoNull HC P Q S HP HQ HS.
  destruct HC as [Hall Hmono Hinter].
  pose proof (Hinter P Q HP HQ) as HPQ.
  pose proof (Hinter (fun t => P t /\ Q t) S HPQ HS) as HPQS.
  eapply Hmono.
  - exact HPQS.
  - intros t [[Hp Hq] Hs].
    exact (conj Hp (conj Hq Hs)).
Qed.

Theorem GPAE01_INTER4 :
  forall CoNull : (R -> Prop) -> Prop,
    CoNullCalculus CoNull ->
    forall P Q S T : R -> Prop,
      CoNull P ->
      CoNull Q ->
      CoNull S ->
      CoNull T ->
      CoNull (fun t => P t /\ Q t /\ S t /\ T t).
Proof.
  intros CoNull HC P Q S T HP HQ HS HT.
  destruct HC as [Hall Hmono Hinter].
  pose proof (Hinter P Q HP HQ) as HPQ.
  pose proof (Hinter (fun t => P t /\ Q t) S HPQ HS) as HPQS.
  pose proof
    (Hinter (fun t => (P t /\ Q t) /\ S t) T HPQS HT)
    as HPQST.
  eapply Hmono.
  - exact HPQST.
  - intros t [[[Hp Hq] Hs] Ht].
    exact (conj Hp (conj Hq (conj Hs Ht))).
Qed.

(* Semantic mode data.  The field dt_u is intended to be the genuine
   time-derivative representative supplied by the analytic layer.  This file
   does not manufacture or reinterpret it. *)
Record AEModalData
  (CoNull : (R -> Prop) -> Prop)
  (nu lambda : R) : Type := {
  ae_u : R -> CH.C2;
  ae_dt_u : R -> CH.C2;
  ae_N : R -> CH.C2;
  ae_modal_good : R -> Prop;
  ae_modal_conull : CoNull ae_modal_good;
  ae_modal_equation :
    forall t : R,
      ae_modal_good t ->
      CH.CModalEq nu lambda (ae_u t) (ae_dt_u t) (ae_N t)
}.

Theorem GPAE10_MODAL_EQUATION_ON_GOOD_TIME :
  forall CoNull : (R -> Prop) -> Prop,
  forall nu lambda : R,
  forall M : AEModalData CoNull nu lambda,
  forall t : R,
    ae_modal_good CoNull nu lambda M t ->
    CH.CModalEq nu lambda
      (ae_u CoNull nu lambda M t)
      (ae_dt_u CoNull nu lambda M t)
      (ae_N CoNull nu lambda M t).
Proof.
  intros CoNull nu lambda M t Hgood.
  exact (ae_modal_equation CoNull nu lambda M t Hgood).
Qed.

(* Three semantic modes and a separately certified cubic Leibniz derivative.
   The four laws may fail on four different null sets. *)
Record AETriadSemanticData
  (CoNull : (R -> Prop) -> Prop)
  (C : CH.C2) (nu lk lp lq : R) : Type := {
  ae_k : AEModalData CoNull nu lk;
  ae_p : AEModalData CoNull nu lp;
  ae_q : AEModalData CoNull nu lq;
  ae_dc : R -> R;
  ae_leibniz_good : R -> Prop;
  ae_leibniz_conull : CoNull ae_leibniz_good;
  ae_leibniz :
    forall t : R,
      ae_leibniz_good t ->
      CH.CTriadLeibniz
        C
        (ae_u CoNull nu lk ae_k t)
        (ae_u CoNull nu lp ae_p t)
        (ae_u CoNull nu lq ae_q t)
        (ae_dt_u CoNull nu lk ae_k t)
        (ae_dt_u CoNull nu lp ae_p t)
        (ae_dt_u CoNull nu lq ae_q t)
        (ae_dc t)
}.

Definition triad_good_time
  (CoNull : (R -> Prop) -> Prop)
  (C : CH.C2) (nu lk lp lq : R)
  (T : AETriadSemanticData CoNull C nu lk lp lq)
  (t : R) : Prop :=
  ae_modal_good CoNull nu lk (ae_k CoNull C nu lk lp lq T) t /\
  ae_modal_good CoNull nu lp (ae_p CoNull C nu lk lp lq T) t /\
  ae_modal_good CoNull nu lq (ae_q CoNull C nu lk lp lq T) t /\
  ae_leibniz_good CoNull C nu lk lp lq T t.

Theorem GPAE20_TRIAD_GOOD_TIME_IS_CONULL :
  forall CoNull : (R -> Prop) -> Prop,
    CoNullCalculus CoNull ->
    forall C : CH.C2,
    forall nu lk lp lq : R,
    forall T : AETriadSemanticData CoNull C nu lk lp lq,
      CoNull (triad_good_time CoNull C nu lk lp lq T).
Proof.
  intros CoNull HC C nu lk lp lq T.
  unfold triad_good_time.
  eapply GPAE01_INTER4.
  - exact HC.
  - exact
      (ae_modal_conull CoNull nu lk
        (ae_k CoNull C nu lk lp lq T)).
  - exact
      (ae_modal_conull CoNull nu lp
        (ae_p CoNull C nu lk lp lq T)).
  - exact
      (ae_modal_conull CoNull nu lq
        (ae_q CoNull C nu lk lp lq T)).
  - exact (ae_leibniz_conull CoNull C nu lk lp lq T).
Qed.

(* On every common good time the genuine semantic derivatives instantiate the
   already checked complex triad certificate. *)
Theorem GPAE21_GOOD_TIME_GIVES_COMPLEX_TRIAD_CERTIFICATE :
  forall CoNull : (R -> Prop) -> Prop,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : AETriadSemanticData CoNull C nu lk lp lq,
  forall t : R,
    triad_good_time CoNull C nu lk lp lq T t ->
    CH.ComplexTriadCertificate
      C
      (ae_u CoNull nu lk (ae_k CoNull C nu lk lp lq T) t)
      (ae_u CoNull nu lp (ae_p CoNull C nu lk lp lq T) t)
      (ae_u CoNull nu lq (ae_q CoNull C nu lk lp lq T) t)
      (ae_dt_u CoNull nu lk (ae_k CoNull C nu lk lp lq T) t)
      (ae_dt_u CoNull nu lp (ae_p CoNull C nu lk lp lq T) t)
      (ae_dt_u CoNull nu lq (ae_q CoNull C nu lk lp lq T) t)
      (ae_N CoNull nu lk (ae_k CoNull C nu lk lp lq T) t)
      (ae_N CoNull nu lp (ae_p CoNull C nu lk lp lq T) t)
      (ae_N CoNull nu lq (ae_q CoNull C nu lk lp lq T) t)
      nu lk lp lq
      (ae_dc CoNull C nu lk lp lq T t).
Proof.
  intros CoNull C nu lk lp lq T t Hgood.
  unfold triad_good_time in Hgood.
  destruct Hgood as [Hk [Hp [Hq Hdc]]].
  unfold CH.ComplexTriadCertificate.
  split.
  - exact
      (ae_modal_equation CoNull nu lk
        (ae_k CoNull C nu lk lp lq T) t Hk).
  - split.
    + exact
        (ae_modal_equation CoNull nu lp
          (ae_p CoNull C nu lk lp lq T) t Hp).
    + split.
      * exact
          (ae_modal_equation CoNull nu lq
            (ae_q CoNull C nu lk lp lq T) t Hq).
      * exact (ae_leibniz CoNull C nu lk lp lq T t Hdc).
Qed.

Definition triad_source_identity
  (CoNull : (R -> Prop) -> Prop)
  (C : CH.C2) (nu lk lp lq : R)
  (T : AETriadSemanticData CoNull C nu lk lp lq)
  (t : R) : Prop :=
  ae_dc CoNull C nu lk lp lq T t
  + nu*(lk+lp+lq)*
      CH.ctriad
        C
        (ae_u CoNull nu lk (ae_k CoNull C nu lk lp lq T) t)
        (ae_u CoNull nu lp (ae_p CoNull C nu lk lp lq T) t)
        (ae_u CoNull nu lq (ae_q CoNull C nu lk lp lq T) t)
  =
    CH.csource1
      C
      (ae_N CoNull nu lk (ae_k CoNull C nu lk lp lq T) t)
      (ae_u CoNull nu lp (ae_p CoNull C nu lk lp lq T) t)
      (ae_u CoNull nu lq (ae_q CoNull C nu lk lp lq T) t)
    +
    CH.csource2
      C
      (ae_u CoNull nu lk (ae_k CoNull C nu lk lp lq T) t)
      (ae_N CoNull nu lp (ae_p CoNull C nu lk lp lq T) t)
      (ae_u CoNull nu lq (ae_q CoNull C nu lk lp lq T) t)
    +
    CH.csource3
      C
      (ae_u CoNull nu lk (ae_k CoNull C nu lk lp lq T) t)
      (ae_u CoNull nu lp (ae_p CoNull C nu lk lp lq T) t)
      (ae_N CoNull nu lq (ae_q CoNull C nu lk lp lq T) t).

Theorem GPAE30_GOOD_TIME_GIVES_THREE_SOURCE_IDENTITY :
  forall CoNull : (R -> Prop) -> Prop,
  forall C : CH.C2,
  forall nu lk lp lq : R,
  forall T : AETriadSemanticData CoNull C nu lk lp lq,
  forall t : R,
    triad_good_time CoNull C nu lk lp lq T t ->
    triad_source_identity CoNull C nu lk lp lq T t.
Proof.
  intros CoNull C nu lk lp lq T t Hgood.
  unfold triad_source_identity.
  exact
    (CH.GPCH40_CERTIFICATE_GIVES_COMPLEX_THREE_SOURCE
      C
      (ae_u CoNull nu lk (ae_k CoNull C nu lk lp lq T) t)
      (ae_u CoNull nu lp (ae_p CoNull C nu lk lp lq T) t)
      (ae_u CoNull nu lq (ae_q CoNull C nu lk lp lq T) t)
      (ae_dt_u CoNull nu lk (ae_k CoNull C nu lk lp lq T) t)
      (ae_dt_u CoNull nu lp (ae_p CoNull C nu lk lp lq T) t)
      (ae_dt_u CoNull nu lq (ae_q CoNull C nu lk lp lq T) t)
      (ae_N CoNull nu lk (ae_k CoNull C nu lk lp lq T) t)
      (ae_N CoNull nu lp (ae_p CoNull C nu lk lp lq T) t)
      (ae_N CoNull nu lq (ae_q CoNull C nu lk lp lq T) t)
      nu lk lp lq
      (ae_dc CoNull C nu lk lp lq T t)
      (GPAE21_GOOD_TIME_GIVES_COMPLEX_TRIAD_CERTIFICATE
        CoNull C nu lk lp lq T t Hgood)).
Qed.

(* Main semantic result: the physical three-source identity holds on a co-null
   set once the analytic layer supplies the three a.e. modal equations and the
   a.e. cubic Leibniz rule. *)
Theorem GPAE31_THREE_SOURCE_IDENTITY_HOLDS_CONULL :
  forall CoNull : (R -> Prop) -> Prop,
    CoNullCalculus CoNull ->
    forall C : CH.C2,
    forall nu lk lp lq : R,
    forall T : AETriadSemanticData CoNull C nu lk lp lq,
      CoNull
        (triad_source_identity CoNull C nu lk lp lq T).
Proof.
  intros CoNull HC C nu lk lp lq T.
  destruct HC as [Hall Hmono Hinter].
  pose proof
    (GPAE20_TRIAD_GOOD_TIME_IS_CONULL
      CoNull
      {| cn_all := Hall; cn_mono := Hmono; cn_inter := Hinter |}
      C nu lk lp lq T) as Hgood.
  eapply Hmono.
  - exact Hgood.
  - intros t Ht.
    exact
      (GPAE30_GOOD_TIME_GIVES_THREE_SOURCE_IDENTITY
        CoNull C nu lk lp lq T t Ht).
Qed.

Definition STATUS : Prop := True.
Theorem STATUS_PROOF : STATUS.
Proof. exact I. Qed.

End NSE_GP_AE_MODAL_SEMANTICS.

Check NSE_GP_AE_MODAL_SEMANTICS.CoNullCalculus.
Check NSE_GP_AE_MODAL_SEMANTICS.GPAE00_INTER3.
Check NSE_GP_AE_MODAL_SEMANTICS.GPAE01_INTER4.
Check NSE_GP_AE_MODAL_SEMANTICS.AEModalData.
Check NSE_GP_AE_MODAL_SEMANTICS.GPAE10_MODAL_EQUATION_ON_GOOD_TIME.
Check NSE_GP_AE_MODAL_SEMANTICS.AETriadSemanticData.
Check NSE_GP_AE_MODAL_SEMANTICS.triad_good_time.
Check NSE_GP_AE_MODAL_SEMANTICS.GPAE20_TRIAD_GOOD_TIME_IS_CONULL.
Check NSE_GP_AE_MODAL_SEMANTICS.GPAE21_GOOD_TIME_GIVES_COMPLEX_TRIAD_CERTIFICATE.
Check NSE_GP_AE_MODAL_SEMANTICS.triad_source_identity.
Check NSE_GP_AE_MODAL_SEMANTICS.GPAE30_GOOD_TIME_GIVES_THREE_SOURCE_IDENTITY.
Check NSE_GP_AE_MODAL_SEMANTICS.GPAE31_THREE_SOURCE_IDENTITY_HOLDS_CONULL.
