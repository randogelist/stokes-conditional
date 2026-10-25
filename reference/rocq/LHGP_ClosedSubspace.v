From Stdlib Require Import Reals Lra Psatz Lia Logic.ProofIrrelevance.
Require Import LHGP_Hilbert.

Open Scope R_scope.

(* A closed subspace is represented by actual elements of the ambient
   inner-product space together with membership proofs. Completeness is
   derived below. This construction supplies no spatial measure or test
   realization: an application must define its ambient space and probes. *)

Record ClosedLinearSubspace (h : HilbertData) := {
  subspace_predicate : HCarrier h -> Prop;
  subspace_zero : subspace_predicate (HZero h);
  subspace_add : forall x y,
    subspace_predicate x -> subspace_predicate y ->
    subspace_predicate (HAdd h x y);
  subspace_scale : forall c x,
    subspace_predicate x -> subspace_predicate (HScale h c x);
  subspace_strong_closed : forall f x,
    (forall n, subspace_predicate (f n)) ->
    HConverges h f x -> subspace_predicate x
}.

Arguments subspace_predicate {h} _ _.
Arguments subspace_zero {h} _.
Arguments subspace_add {h} _ _ _ _ _.
Arguments subspace_scale {h} _ _ _ _.
Arguments subspace_strong_closed {h} _ _ _ _ _.

Definition SubspaceCarrier {h : HilbertData} (s : ClosedLinearSubspace h) :=
  { x : HCarrier h | subspace_predicate s x }.

Definition SubspaceInclude {h : HilbertData} (s : ClosedLinearSubspace h)
    (x : SubspaceCarrier s) : HCarrier h := proj1_sig x.

Lemma SubspaceInclude_member : forall h (s : ClosedLinearSubspace h) x,
  subspace_predicate s (SubspaceInclude s x).
Proof. intros h s [x Hx]; exact Hx. Qed.

Lemma SubspaceInclude_injective : forall h (s : ClosedLinearSubspace h) x y,
  SubspaceInclude s x = SubspaceInclude s y -> x = y.
Proof.
  intros h s [x Hx] [y Hy] Heq; simpl in Heq; subst y.
  f_equal; apply proof_irrelevance.
Qed.

Definition SubspaceHilbert {h : HilbertData} (s : ClosedLinearSubspace h)
    : HilbertData.
Proof.
  refine {| HCarrier := SubspaceCarrier s;
    HZero := exist _ (HZero h) (subspace_zero s);
    HAdd := fun x y => exist _ (HAdd h (SubspaceInclude s x) (SubspaceInclude s y))
      (subspace_add s _ _ (proj2_sig x) (proj2_sig y));
    HScale := fun c x => exist _ (HScale h c (SubspaceInclude s x))
      (subspace_scale s c _ (proj2_sig x));
    HInner := fun x y => HInner h (SubspaceInclude s x) (SubspaceInclude s y)
  |}.
  - intro x; apply HInner_zero_l.
  - intros x y z; apply HInner_add_l.
  - intros c x y; apply HInner_scale_l.
  - intros x y; apply HInner_sym.
  - intro x; apply HInner_pos.
  - intros x y Hdist; apply SubspaceInclude_injective.
    apply HInner_definite; exact Hdist.
Defined.

Lemma SubspaceInclude_zero : forall h (s : ClosedLinearSubspace h),
  SubspaceInclude s (HZero (SubspaceHilbert s)) = HZero h.
Proof. reflexivity. Qed.

Lemma SubspaceInclude_add : forall h (s : ClosedLinearSubspace h) x y,
  SubspaceInclude s (HAdd (SubspaceHilbert s) x y) =
  HAdd h (SubspaceInclude s x) (SubspaceInclude s y).
Proof. reflexivity. Qed.

Lemma SubspaceInclude_scale : forall h (s : ClosedLinearSubspace h) c x,
  SubspaceInclude s (HScale (SubspaceHilbert s) c x) =
  HScale h c (SubspaceInclude s x).
Proof. reflexivity. Qed.

Lemma SubspaceInclude_sub : forall h (s : ClosedLinearSubspace h) x y,
  SubspaceInclude s (HSub (SubspaceHilbert s) x y) =
  HSub h (SubspaceInclude s x) (SubspaceInclude s y).
Proof. reflexivity. Qed.

Lemma SubspaceInner : forall h (s : ClosedLinearSubspace h) x y,
  HInner (SubspaceHilbert s) x y =
  HInner h (SubspaceInclude s x) (SubspaceInclude s y).
Proof. reflexivity. Qed.

Lemma SubspaceNorm : forall h (s : ClosedLinearSubspace h) x,
  HNorm (SubspaceHilbert s) x = HNorm h (SubspaceInclude s x).
Proof. reflexivity. Qed.

Lemma SubspaceDistance : forall h (s : ClosedLinearSubspace h) x y,
  HDist (SubspaceHilbert s) x y =
  HDist h (SubspaceInclude s x) (SubspaceInclude s y).
Proof. reflexivity. Qed.

Theorem SubspaceConverges_iff : forall h (s : ClosedLinearSubspace h) f x,
  HConverges (SubspaceHilbert s) f x <->
  HConverges h (fun n => SubspaceInclude s (f n)) (SubspaceInclude s x).
Proof. reflexivity. Qed.

Theorem SubspaceCauchy_iff : forall h (s : ClosedLinearSubspace h) f,
  HCauchy (SubspaceHilbert s) f <->
  HCauchy h (fun n => SubspaceInclude s (f n)).
Proof. reflexivity. Qed.

Theorem SubspaceComplete : forall h (s : ClosedLinearSubspace h),
  HComplete h -> HComplete (SubspaceHilbert s).
Proof.
  intros h s Hcomplete f Hcauchy.
  destruct (Hcomplete (fun n => SubspaceInclude s (f n)) Hcauchy) as [x Hlimit].
  assert (Hx : subspace_predicate s x).
  { eapply subspace_strong_closed; [|exact Hlimit].
    intro n; apply SubspaceInclude_member. }
  exists (exist _ x Hx); exact Hlimit.
Qed.

Definition Annihilator (h : HilbertData) {Q : Type}
    (grad : Q -> HCarrier h) (x : HCarrier h) : Prop :=
  forall q, HInner h x (grad q) = 0.

Lemma Annihilator_zero : forall h Q (grad : Q -> HCarrier h),
  Annihilator h grad (HZero h).
Proof. intros h Q grad q; apply HInner_zero_l. Qed.

Lemma Annihilator_add : forall h Q (grad : Q -> HCarrier h) x y,
  Annihilator h grad x -> Annihilator h grad y ->
  Annihilator h grad (HAdd h x y).
Proof.
  intros h Q grad x y Hx Hy q; rewrite HInner_add_l, Hx, Hy; ring.
Qed.

Lemma Annihilator_scale : forall h Q (grad : Q -> HCarrier h) c x,
  Annihilator h grad x -> Annihilator h grad (HScale h c x).
Proof.
  intros h Q grad c x Hx q; rewrite HInner_scale_l, Hx; ring.
Qed.

(* No topology on Q, countability, ONB, or completeness is needed. Each
   single probe is strongly continuous by the derived Cauchy--Schwarz bound. *)
Theorem Annihilator_strong_closed : forall h Q (grad : Q -> HCarrier h) f x,
  (forall n, Annihilator h grad (f n)) -> HConverges h f x ->
  Annihilator h grad x.
Proof.
  intros h Q grad f x Hfn Hlimit q.
  destruct (Req_EM_T (HInner h x (grad q)) 0) as [Hz|Hnz]; [exact Hz|].
  pose proof (HNorm_nonnegative h (grad q)) as Hnorm.
  assert (Hsq : 0 < HInner h x (grad q) * HInner h x (grad q)) by nra.
  set (eps := (HInner h x (grad q) * HInner h x (grad q)) /
    (HNorm h (grad q) + 1)).
  assert (Heps : 0 < eps).
  { unfold eps; apply Rdiv_lt_0_compat; lra. }
  destruct (Hlimit eps Heps) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  pose proof (HInner_distance_bound h (f N) x (grad q)) as Hbound.
  rewrite (Hfn N q) in Hbound.
  pose proof (HDist_nonnegative h (f N) x) as Hdist.
  assert (Hidentity : eps * (HNorm h (grad q) + 1) =
    HInner h x (grad q) * HInner h x (grad q)).
  { unfold eps; field; lra. }
  assert (Hstrict : HDist h (f N) x * (HNorm h (grad q) + 1) <
    eps * (HNorm h (grad q) + 1)).
  { apply Rmult_lt_compat_r; lra. }
  nra.
Qed.

Definition AnnihilatorSubspace (h : HilbertData) {Q : Type}
    (grad : Q -> HCarrier h) : ClosedLinearSubspace h :=
  {| subspace_predicate := Annihilator h grad;
     subspace_zero := Annihilator_zero h Q grad;
     subspace_add := Annihilator_add h Q grad;
     subspace_scale := Annihilator_scale h Q grad;
     subspace_strong_closed := Annihilator_strong_closed h Q grad |}.

Definition AnnihilatorHilbert (h : HilbertData) {Q : Type}
    (grad : Q -> HCarrier h) : HilbertData :=
  SubspaceHilbert (AnnihilatorSubspace h grad).

Theorem AnnihilatorComplete : forall h Q (grad : Q -> HCarrier h),
  HComplete h -> HComplete (AnnihilatorHilbert h grad).
Proof. intros h Q grad Hcomplete; apply SubspaceComplete; exact Hcomplete. Qed.

Print Assumptions SubspaceComplete.
Print Assumptions Annihilator_strong_closed.
Print Assumptions AnnihilatorComplete.
