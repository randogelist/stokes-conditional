(* Actual normalized torus character integrals.  Proof structure is adapted
   from the supplied v0.50.2 integral-binding development, now self-contained
   over the current C2/Z3 types and Stdlib only.  Integer-character integrals
   are computed by Stdlib FTC_Riemann.  Three-dimensional means are literal
   iterated normalized Riemann means on [0,2*pi]^3, with proved integrability
   witnesses.  Total mean values use singleton completeness, preserving the
   existing four classical-real foundations; no integral or orthogonality
   oracle and no Coquelicot dependency are introduced. *)
From Stdlib Require Import Reals RiemannInt Ranalysis_reg Rtrigo1
  Lra Psatz Field ZArith ZArith.Znat Lia Classical.
Require Import BKQR_FourierIndices BKQR_FourierConvection.

Module BKQR_TORUS_ATOMS.
Import BKQR_FOURIER_INDICES BKQR_FOURIER_CONVECTION.
Open Scope R_scope.

Definition tau : R := 2*PI.
Definition cone : C2 := (1,0).
Definition RealAvg (f : R -> R) (a : R) : Prop :=
  exists H : Riemann_integrable f 0 tau, RiemannInt H=tau*a.

Lemma TAU_POS : 0 < tau.
Proof. unfold tau. pose proof PI_RGT_0. lra. Qed.
Lemma TAU_NONZERO : tau <> 0.
Proof. pose proof TAU_POS. lra. Qed.

Lemma REAL_AVG_EXT : forall (f g : R -> R) a,
  (forall x, f x=g x) -> RealAvg f a -> RealAvg g a.
Proof.
  intros f g a Heq [Hf Hvalue].
  assert (Hg : Riemann_integrable g 0 tau).
  { eapply Riemann_integrable_ext; [intros; apply Heq|exact Hf]. }
  exists Hg. rewrite <- Hvalue. symmetry. apply RiemannInt_P18.
  - left. apply TAU_POS.
  - intros x Hx. apply Heq.
Qed.

Lemma REAL_AVG_CONST : forall a, RealAvg (fun _=>a) a.
Proof.
  intro a. exists (RiemannInt_P14 0 tau a).
  pose proof (RiemannInt_P15 (RiemannInt_P14 0 tau a)) as Hvalue.
  cbn beta. transitivity (a*(tau-0)); [exact Hvalue|ring].
Qed.

Lemma REAL_AVG_LINEAR : forall (f g : R -> R) a b c,
  RealAvg f a -> RealAvg g b ->
  RealAvg (fun x=>f x+c*g x) (a+c*b).
Proof.
  intros f g a b c [Hf Hfv] [Hg Hgv].
  pose proof (RiemannInt_P10 c Hf Hg) as Hlinear.
  exists Hlinear. rewrite (RiemannInt_P13 Hf Hg Hlinear), Hfv, Hgv. ring.
Qed.

Lemma REAL_AVG_PLUS : forall (f g : R -> R) a b,
  RealAvg f a -> RealAvg g b -> RealAvg (fun x=>f x+g x) (a+b).
Proof.
  intros f g a b Hf Hg.
  replace (a+b) with (a+1*b) by ring.
  eapply REAL_AVG_EXT with (f:=fun x=>f x+1*g x).
  - intro x. ring.
  - apply REAL_AVG_LINEAR; assumption.
Qed.

Lemma REAL_AVG_MINUS : forall (f g : R -> R) a b,
  RealAvg f a -> RealAvg g b -> RealAvg (fun x=>f x-g x) (a-b).
Proof.
  intros f g a b Hf Hg.
  replace (a-b) with (a+(-1)*b) by ring.
  eapply REAL_AVG_EXT with (f:=fun x=>f x+(-1)*g x).
  - intro x. ring.
  - apply REAL_AVG_LINEAR; assumption.
Qed.

Lemma REAL_AVG_SCALE : forall (f : R -> R) a c,
  RealAvg f a -> RealAvg (fun x=>c*f x) (c*a).
Proof.
  intros f a c Hf. replace (c*a) with (0+c*a) by ring.
  eapply REAL_AVG_EXT with (f:=fun x=>0+c*f x).
  - intro x. ring.
  - apply REAL_AVG_LINEAR; [apply REAL_AVG_CONST|exact Hf].
Qed.

Lemma REAL_AVG_UNIQUE : forall f a b,
  RealAvg f a -> RealAvg f b -> a=b.
Proof.
  intros f a b [Ha Hva] [Hb Hvb].
  pose proof (RiemannInt_P5 Ha Hb) as Hsame.
  pose proof TAU_NONZERO. rewrite Hva, Hvb in Hsame. nra.
Qed.

Lemma real_avg_unique_exists : forall f,
  (exists a, RealAvg f a) -> exists! a, RealAvg f a.
Proof.
  intros f [a Ha]. exists a. split; [exact Ha|].
  intros b Hb. apply REAL_AVG_UNIQUE with (f:=f); assumption.
Qed.

Lemma real_avg_bounded : forall f,
  (exists a, RealAvg f a) -> bound (RealAvg f).
Proof.
  intros f [a Ha]. exists a. intros b Hb.
  assert (Heq : b=a) by (eapply REAL_AVG_UNIQUE; eassumption).
  rewrite Heq. right. reflexivity.
Qed.

(* Stdlib Riemann_integrable is Type-valued. The singleton of normalized
   integral values has a least upper bound equal to its unique member.
   This totalization uses only the existing standard real completeness and
   classical foundations, and returns zero in the nonintegrable case. *)
Definition RealMean (f : R -> R) : R :=
  match ClassicalDedekindReals.sig_not_dec (exists a, RealAvg f a) with
  | left H => proj1_sig (completeness (RealAvg f)
      (real_avg_bounded f (NNPP _ H)) (NNPP _ H))
  | right _ => 0
  end.

Lemma REAL_AVG_VALUE : forall f a, RealAvg f a -> RealMean f=a.
Proof.
  intros f a Ha. unfold RealMean.
  destruct (ClassicalDedekindReals.sig_not_dec (exists x, RealAvg f x))
    as [Hnn|Hno].
  - destruct (completeness (RealAvg f)
      (real_avg_bounded f (NNPP _ Hnn)) (NNPP _ Hnn)) as [M [Hupper Hleast]].
    simpl. assert (HaM : a <= M) by (apply Hupper; exact Ha).
    assert (HMa : M <= a).
    { apply Hleast. intros b Hb.
      assert (Heq : b=a) by (eapply REAL_AVG_UNIQUE; eassumption).
      rewrite Heq. right. reflexivity. }
    lra.
  - exfalso. apply Hno. exists a. exact Ha.
Qed.

Lemma REAL_MEAN_EXT : forall f g,
  (forall x, f x=g x) -> RealMean f=RealMean g.
Proof.
  intros f g Hfg.
  destruct (classic (exists a, RealAvg f a)) as [Hf|Hf].
  - destruct Hf as [a Ha]. rewrite (REAL_AVG_VALUE f a Ha).
    symmetry. apply REAL_AVG_VALUE. eapply REAL_AVG_EXT; eassumption.
  - assert (Hg : ~exists a, RealAvg g a).
    { intros [a Ha]. apply Hf. exists a.
      eapply REAL_AVG_EXT with (f:=g); [intro x; symmetry; apply Hfg|exact Ha]. }
    unfold RealMean.
    destruct (ClassicalDedekindReals.sig_not_dec (exists a, RealAvg f a))
      as [Hnnf|Hnf]; [exfalso; apply Hnnf; exact Hf|].
    destruct (ClassicalDedekindReals.sig_not_dec (exists a, RealAvg g a))
      as [Hnng|Hng]; [exfalso; apply Hnng; exact Hg|reflexivity].
Qed.

Definition Mean1 (f : R -> C2) : C2 :=
  (RealMean (fun x=>cre (f x)), RealMean (fun x=>cim (f x))).
Definition IsMean1 (f : R -> C2) (a : C2) : Prop :=
  RealAvg (fun x=>cre (f x)) (cre a) /\
  RealAvg (fun x=>cim (f x)) (cim a).

Lemma MEAN1_EXT : forall f g,
  (forall x, f x=g x) -> Mean1 f=Mean1 g.
Proof.
  intros f g Hfg. unfold Mean1. f_equal; apply REAL_MEAN_EXT;
    intro x; rewrite Hfg; reflexivity.
Qed.

Lemma MEAN1_VALUE : forall f a, IsMean1 f a -> Mean1 f=a.
Proof.
  intros f [ar ai] [Hr Hi]. unfold Mean1.
  rewrite (REAL_AVG_VALUE _ _ Hr), (REAL_AVG_VALUE _ _ Hi). reflexivity.
Qed.

Lemma ISMEAN1_EXT : forall f g a,
  (forall x, f x=g x) -> IsMean1 f a -> IsMean1 g a.
Proof.
  intros f g a Hfg [Hr Hi]. split.
  - eapply REAL_AVG_EXT with (f:=fun x=>cre (f x));
      [intro x; rewrite Hfg; reflexivity|exact Hr].
  - eapply REAL_AVG_EXT with (f:=fun x=>cim (f x));
      [intro x; rewrite Hfg; reflexivity|exact Hi].
Qed.

Lemma ISMEAN1_CONST : forall a, IsMean1 (fun _=>a) a.
Proof. intro a. split; apply REAL_AVG_CONST. Qed.

Lemma ISMEAN1_PLUS : forall f g a b,
  IsMean1 f a -> IsMean1 g b ->
  IsMean1 (fun x=>cadd (f x) (g x)) (cadd a b).
Proof.
  intros f g [ar ai] [br bi] [Hfr Hfi] [Hgr Hgi].
  split; unfold cadd, cre, cim; simpl in *; apply REAL_AVG_PLUS; assumption.
Qed.

Lemma ISMEAN1_CMUL_L : forall f a b,
  IsMean1 f b -> IsMean1 (fun x=>cmul a (f x)) (cmul a b).
Proof.
  intros f [ar ai] [br bi] [Hr Hi].
  split; unfold cmul, cre, cim; simpl in *.
  - apply REAL_AVG_MINUS; apply REAL_AVG_SCALE; assumption.
  - apply REAL_AVG_PLUS; apply REAL_AVG_SCALE; assumption.
Qed.

Lemma circle_cmul_comm : forall a b, cmul a b=cmul b a.
Proof. intros [ar ai] [br bi]. unfold cmul, cre, cim; simpl. f_equal; ring. Qed.

Lemma ISMEAN1_CMUL_R : forall f a b,
  IsMean1 f a -> IsMean1 (fun x=>cmul (f x) b) (cmul a b).
Proof.
  intros f a b Hf. rewrite (circle_cmul_comm a b).
  apply ISMEAN1_EXT with (f:=fun x=>cmul b (f x)).
  - intro x. apply circle_cmul_comm.
  - apply ISMEAN1_CMUL_L. exact Hf.
Qed.


Lemma COS_INTEGER_PERIOD : forall (x : R) (z : Z),
  cos (x + 2*IZR z*PI) = cos x.
Proof.
  intros x z. destruct z as [|p|p].
  - simpl. replace (x+2*0*PI) with x by ring. reflexivity.
  - rewrite <- (positive_nat_Z p). rewrite <- INR_IZR_INZ. apply cos_period.
  - rewrite IZR_NEG. rewrite <- (positive_nat_Z p). rewrite <- INR_IZR_INZ.
    replace (x+2*(-INR (Pos.to_nat p))*PI)
      with (x-2*INR (Pos.to_nat p)*PI) by ring.
    pose proof (cos_period (x-2*INR (Pos.to_nat p)*PI) (Pos.to_nat p)) as Hp.
    replace ((x-2*INR (Pos.to_nat p)*PI)+2*INR (Pos.to_nat p)*PI)
      with x in Hp by ring. symmetry. exact Hp.
Qed.
Lemma SIN_INTEGER_PERIOD : forall (x : R) (z : Z),
  sin (x + 2*IZR z*PI) = sin x.
Proof.
  intros x z. destruct z as [|p|p].
  - simpl. replace (x+2*0*PI) with x by ring. reflexivity.
  - rewrite <- (positive_nat_Z p). rewrite <- INR_IZR_INZ. apply sin_period.
  - rewrite IZR_NEG. rewrite <- (positive_nat_Z p). rewrite <- INR_IZR_INZ.
    replace (x+2*(-INR (Pos.to_nat p))*PI)
      with (x-2*INR (Pos.to_nat p)*PI) by ring.
    pose proof (sin_period (x-2*INR (Pos.to_nat p)*PI) (Pos.to_nat p)) as Hp.
    replace ((x-2*INR (Pos.to_nat p)*PI)+2*INR (Pos.to_nat p)*PI)
      with x in Hp by ring. symmetry. exact Hp.
Qed.
Lemma COS_INTEGER_ENDPOINT : forall n : Z, cos (IZR n*(2*PI)) = 1.
Proof.
  intro n. replace (IZR n*(2*PI)) with (0+2*IZR n*PI) by ring.
  rewrite COS_INTEGER_PERIOD, cos_0. reflexivity.
Qed.
Lemma SIN_INTEGER_ENDPOINT : forall n : Z, sin (IZR n*(2*PI)) = 0.
Proof.
  intro n. replace (IZR n*(2*PI)) with (0+2*IZR n*PI) by ring.
  rewrite SIN_INTEGER_PERIOD, sin_0. reflexivity.
Qed.

Lemma LINEAR_DERIVATIVE : forall c x,
  derivable_pt_lim (fun t => c*t) x c.
Proof.
  intros c x. change (derivable_pt_lim (mult_real_fct c id) x c).
  replace c with (c*1) at 2 by ring.
  apply derivable_pt_lim_scal. apply derivable_pt_lim_id.
Qed.
Lemma COS_LINEAR_DERIVATIVE : forall c x,
  derivable_pt_lim (fun t => cos (c*t)) x (-sin(c*x)*c).
Proof.
  intros c x.
  apply (derivable_pt_lim_comp (fun t => c*t) cos x c (-sin(c*x))).
  - apply LINEAR_DERIVATIVE.
  - apply derivable_pt_lim_cos.
Qed.
Lemma SIN_LINEAR_DERIVATIVE : forall c x,
  derivable_pt_lim (fun t => sin (c*t)) x (cos(c*x)*c).
Proof.
  intros c x.
  apply (derivable_pt_lim_comp (fun t => c*t) sin x c (cos(c*x))).
  - apply LINEAR_DERIVATIVE.
  - apply derivable_pt_lim_sin.
Qed.

Lemma COS_LINEAR_CONTINUOUS : forall c,
  continuity (fun t => cos(c*t)).
Proof.
  intros c x. apply derivable_continuous_pt.
  exists (-sin(c*x)*c). apply COS_LINEAR_DERIVATIVE.
Qed.
Lemma SIN_LINEAR_CONTINUOUS : forall c,
  continuity (fun t => sin(c*t)).
Proof.
  intros c x. apply derivable_continuous_pt.
  exists (cos(c*x)*c). apply SIN_LINEAR_DERIVATIVE.
Qed.

Definition COS_INTEGER_INTEGRABLE (n:Z) :
  Riemann_integrable (fun x => cos(IZR n*x)) 0 (2*PI).
Proof.
  apply continuity_implies_RiemannInt.
  - pose proof PI_RGT_0. lra.
  - intros x Hx. apply COS_LINEAR_CONTINUOUS.
Defined.
Definition SIN_INTEGER_INTEGRABLE (n:Z) :
  Riemann_integrable (fun x => sin(IZR n*x)) 0 (2*PI).
Proof.
  apply continuity_implies_RiemannInt.
  - pose proof PI_RGT_0. lra.
  - intros x Hx. apply SIN_LINEAR_CONTINUOUS.
Defined.

Lemma COS_PRIMITIVE_DERIVATIVE : forall c, c<>0 -> forall x,
  derivable_pt_lim (fun t => sin(c*t) * /c) x (cos(c*x)).
Proof.
  intros c Hc x.
  replace (cos(c*x)) with ((cos(c*x)*c) * /c) by (field; exact Hc).
  apply derivable_pt_lim_scal_right. apply SIN_LINEAR_DERIVATIVE.
Qed.
Lemma SIN_PRIMITIVE_DERIVATIVE : forall c, c<>0 -> forall x,
  derivable_pt_lim (fun t => cos(c*t) * (-/c)) x (sin(c*x)).
Proof.
  intros c Hc x.
  replace (sin(c*x)) with ((-sin(c*x)*c) * (-/c)) by (field; exact Hc).
  apply derivable_pt_lim_scal_right. apply COS_LINEAR_DERIVATIVE.
Qed.

Definition COS_PRIMITIVE_C1 (c:R) (Hc:c<>0) : C1_fun.
Proof.
  refine (@mkC1 (fun t => sin(c*t) * /c)
    (fun x => exist _ (cos(c*x)) (COS_PRIMITIVE_DERIVATIVE c Hc x)) _).
  change (continuity (fun x => cos(c*x))).
  apply COS_LINEAR_CONTINUOUS.
Defined.
Definition SIN_PRIMITIVE_C1 (c:R) (Hc:c<>0) : C1_fun.
Proof.
  refine (@mkC1 (fun t => cos(c*t) * (-/c))
    (fun x => exist _ (sin(c*x)) (SIN_PRIMITIVE_DERIVATIVE c Hc x)) _).
  change (continuity (fun x => sin(c*x))).
  apply SIN_LINEAR_CONTINUOUS.
Defined.

Theorem COS_INTEGER_INTEGRAL_ZERO : forall (n:Z)
  (H:Riemann_integrable (fun x => cos(IZR n*x)) 0 (2*PI)),
  n<>0%Z -> RiemannInt H=0.
Proof.
  intros n H Hn.
  assert (Hc:IZR n<>0) by (intro He; apply Hn; apply eq_IZR; exact He).
  pose proof (@FTC_Riemann (COS_PRIMITIVE_C1 (IZR n) Hc) 0 (2*PI) H) as Hi.
  change (RiemannInt H = sin(IZR n*(2*PI))*/IZR n -
    sin(IZR n*0)*/IZR n) in Hi.
  rewrite SIN_INTEGER_ENDPOINT, Rmult_0_r, sin_0 in Hi.
  rewrite Hi. ring.
Qed.
Theorem SIN_INTEGER_INTEGRAL_ZERO : forall (n:Z)
  (H:Riemann_integrable (fun x => sin(IZR n*x)) 0 (2*PI)),
  n<>0%Z -> RiemannInt H=0.
Proof.
  intros n H Hn.
  assert (Hc:IZR n<>0) by (intro He; apply Hn; apply eq_IZR; exact He).
  pose proof (@FTC_Riemann (SIN_PRIMITIVE_C1 (IZR n) Hc) 0 (2*PI) H) as Hi.
  change (RiemannInt H = cos(IZR n*(2*PI))*(-/IZR n) -
    cos(IZR n*0)*(-/IZR n)) in Hi.
  rewrite COS_INTEGER_ENDPOINT, Rmult_0_r, cos_0 in Hi.
  rewrite Hi. ring.
Qed.


Definition char1 (n : Z) (t : R) : C2 :=
  (cos (IZR n*t), sin (IZR n*t)).
Definition delta1 (n : Z) : C2 :=
  if Z.eq_dec n 0 then cone else czero.

Lemma REAL_AVG_COS_NONZERO : forall n : Z, n<>0%Z ->
  RealAvg (fun x=>cos (IZR n*x)) 0.
Proof.
  intros n Hn. exists (COS_INTEGER_INTEGRABLE n).
  transitivity 0; [apply COS_INTEGER_INTEGRAL_ZERO; exact Hn|ring].
Qed.

Lemma REAL_AVG_SIN_NONZERO : forall n : Z, n<>0%Z ->
  RealAvg (fun x=>sin (IZR n*x)) 0.
Proof.
  intros n Hn. exists (SIN_INTEGER_INTEGRABLE n).
  transitivity 0; [apply SIN_INTEGER_INTEGRAL_ZERO; exact Hn|ring].
Qed.

Theorem TORUS_INTEGER_CHARACTER_MEAN : forall n,
  IsMean1 (char1 n) (delta1 n).
Proof.
  intro n. unfold delta1. destruct (Z.eq_dec n 0) as [Heq|Hn].
  - subst n. apply ISMEAN1_EXT with (f:=fun _=>cone).
    + intro x. unfold char1, cone. simpl.
      rewrite Rmult_0_l, cos_0, sin_0. reflexivity.
    + apply ISMEAN1_CONST.
  - split; unfold char1, czero, cre, cim; simpl.
    + apply REAL_AVG_COS_NONZERO. exact Hn.
    + apply REAL_AVG_SIN_NONZERO. exact Hn.
Qed.

Print Assumptions REAL_AVG_VALUE.
Print Assumptions MEAN1_EXT.
Print Assumptions TORUS_INTEGER_CHARACTER_MEAN.

Record R3 := mkR3 { rx : R; ry : R; rz : R }.
Definition point (x y z : R) : R3 := mkR3 x y z.
Definition cconj (a : C2) : C2 := (cre a, -cim a).
Definition phase (m : Z3) (x : R3) : R :=
  IZR (mode_x m)*rx x + IZR (mode_y m)*ry x + IZR (mode_z m)*rz x.
Definition torus_atom (m : Z3) (x : R3) : C2 :=
  (cos (phase m x), sin (phase m x)).

Lemma torus_cmul_comm : forall a b, cmul a b=cmul b a.
Proof. intros [ar ai] [br bi]. unfold cmul, cre, cim; simpl. f_equal; ring. Qed.

Definition Mean3 (f : R3 -> C2) : C2 :=
  Mean1 (fun x => Mean1 (fun y => Mean1 (fun z => f (point x y z)))).

(* Each of the three iterated means carries actual one-dimensional
   Riemann-integrability certificates.  These are proved for all atoms and
   finite polynomials; they are not an assumed orthogonality operation. *)
Definition IsMean3 (f : R3 -> C2) (a : C2) : Prop :=
  exists (m2 : R -> R -> C2) (m1 : R -> C2),
    (forall x y, IsMean1 (fun z => f (point x y z)) (m2 x y)) /\
    (forall x, IsMean1 (m2 x) (m1 x)) /\ IsMean1 m1 a.

Lemma MEAN3_VALUE : forall f a, IsMean3 f a -> Mean3 f=a.
Proof.
  intros f a [m2 [m1 [Hz [Hy Hx]]]]. unfold Mean3.
  transitivity (Mean1 m1).
  - apply MEAN1_EXT. intro x. transitivity (Mean1 (m2 x)).
    + apply MEAN1_EXT. intro y. apply MEAN1_VALUE. apply Hz.
    + apply MEAN1_VALUE. apply Hy.
  - apply MEAN1_VALUE. exact Hx.
Qed.

Lemma MEAN3_EXT : forall f g,
  (forall x, f x=g x) -> Mean3 f=Mean3 g.
Proof.
  intros f g Heq. unfold Mean3. apply MEAN1_EXT. intro x.
  apply MEAN1_EXT. intro y. apply MEAN1_EXT. intro z. apply Heq.
Qed.

Lemma ISMEAN3_EXT : forall f g a,
  (forall x, f x=g x) -> IsMean3 f a -> IsMean3 g a.
Proof.
  intros f g a Heq [m2 [m1 [Hz [Hy Hx]]]]. exists m2, m1. split.
  - intros x y. apply ISMEAN1_EXT with (f:=fun z=>f (point x y z)).
    + intro z. apply Heq.
    + apply Hz.
  - split; assumption.
Qed.

Lemma ISMEAN3_CONST : forall a, IsMean3 (fun _=>a) a.
Proof.
  intro a. exists (fun _ _=>a), (fun _=>a).
  split; [intros; apply ISMEAN1_CONST|].
  split; [intro; apply ISMEAN1_CONST|apply ISMEAN1_CONST].
Qed.

Lemma ISMEAN3_PLUS : forall f g a b,
  IsMean3 f a -> IsMean3 g b ->
  IsMean3 (fun x=>cadd (f x) (g x)) (cadd a b).
Proof.
  intros f g a b [f2 [f1 [Hfz [Hfy Hfx]]]] [g2 [g1 [Hgz [Hgy Hgx]]]].
  exists (fun x y=>cadd (f2 x y) (g2 x y)), (fun x=>cadd (f1 x) (g1 x)). split.
  - intros x y. apply ISMEAN1_PLUS; [apply Hfz|apply Hgz].
  - split.
    + intro x. apply ISMEAN1_PLUS; [apply Hfy|apply Hgy].
    + apply ISMEAN1_PLUS; assumption.
Qed.

Lemma ISMEAN3_CMUL_L : forall f a b,
  IsMean3 f b -> IsMean3 (fun x=>cmul a (f x)) (cmul a b).
Proof.
  intros f a b [f2 [f1 [Hfz [Hfy Hfx]]]].
  exists (fun x y=>cmul a (f2 x y)), (fun x=>cmul a (f1 x)). split.
  - intros x y. apply ISMEAN1_CMUL_L. apply Hfz.
  - split.
    + intro x. apply ISMEAN1_CMUL_L. apply Hfy.
    + apply ISMEAN1_CMUL_L. exact Hfx.
Qed.

Lemma ISMEAN3_CMUL_R : forall f a b,
  IsMean3 f a -> IsMean3 (fun x=>cmul (f x) b) (cmul a b).
Proof.
  intros f a b Hf. rewrite (torus_cmul_comm a b).
  apply ISMEAN3_EXT with (f:=fun x=>cmul b (f x)).
  - intro x. apply torus_cmul_comm.
  - apply ISMEAN3_CMUL_L. exact Hf.
Qed.

Lemma ATOM_FACTOR : forall m x y z,
  torus_atom m (point x y z) = cmul (char1 (mode_x m) x)
    (cmul (char1 (mode_y m) y) (char1 (mode_z m) z)).
Proof.
  intros [mx my mz] x y z.
  unfold torus_atom, phase, point, char1, cmul, cre, cim. simpl.
  repeat (rewrite cos_plus || rewrite sin_plus). f_equal; ring.
Qed.

Theorem TORUS_ATOM_PRODUCT : forall p q x,
  cmul (torus_atom p x) (torus_atom q x)=torus_atom (mode_add p q) x.
Proof.
  intros p q x.
  assert (Hp : phase (mode_add p q) x=phase p x+phase q x).
  { unfold phase, mode_add. simpl. rewrite !plus_IZR. ring. }
  unfold torus_atom. rewrite Hp, cos_plus, sin_plus.
  unfold cmul, cre, cim. simpl. f_equal; ring.
Qed.

Lemma ATOM_TENSOR_INTEGRAL : forall m,
  IsMean3 (torus_atom m)
    (cmul (delta1 (mode_x m)) (cmul (delta1 (mode_y m)) (delta1 (mode_z m)))).
Proof.
  intro m.
  exists (fun x y=>cmul (char1 (mode_x m) x)
                    (cmul (char1 (mode_y m) y) (delta1 (mode_z m)))),
         (fun x=>cmul (char1 (mode_x m) x)
                    (cmul (delta1 (mode_y m)) (delta1 (mode_z m)))). split.
  - intros x y. apply ISMEAN1_EXT with
      (f:=fun z=>cmul (char1 (mode_x m) x)
        (cmul (char1 (mode_y m) y) (char1 (mode_z m) z))).
    + intro z. symmetry. apply ATOM_FACTOR.
    + apply ISMEAN1_CMUL_L. apply ISMEAN1_CMUL_L.
      apply TORUS_INTEGER_CHARACTER_MEAN.
  - split.
    + intro x. apply ISMEAN1_CMUL_L. apply ISMEAN1_CMUL_R.
      apply TORUS_INTEGER_CHARACTER_MEAN.
    + apply ISMEAN1_CMUL_R. apply TORUS_INTEGER_CHARACTER_MEAN.
Qed.

Definition delta3 (m : Z3) : C2 :=
  if mode_eq_dec m mode_zero then cone else czero.

Lemma DELTA_TENSOR : forall m,
  cmul (delta1 (mode_x m)) (cmul (delta1 (mode_y m)) (delta1 (mode_z m)))=delta3 m.
Proof.
  intros [mx my mz].
  change (cmul (if Z.eq_dec mx 0 then cone else czero)
    (cmul (if Z.eq_dec my 0 then cone else czero)
      (if Z.eq_dec mz 0 then cone else czero)) =
    if mode_eq_dec (mkZ3 mx my mz) mode_zero then cone else czero).
  destruct (Z.eq_dec mx 0) as [Hx|Hx]; destruct (Z.eq_dec my 0) as [Hy|Hy];
  destruct (Z.eq_dec mz 0) as [Hz|Hz];
  destruct (mode_eq_dec (mkZ3 mx my mz) mode_zero) as [H0|H0].
  all: try (exfalso; apply H0; subst; reflexivity).
  all: try (unfold mode_zero in H0; injection H0 as Ha Hb Hc; contradiction).
  all: unfold cone, czero, cmul, cre, cim; simpl; f_equal; ring.
Qed.

Theorem TORUS_ATOM_MEAN : forall m, IsMean3 (torus_atom m) (delta3 m).
Proof. intro m. rewrite <- DELTA_TENSOR. apply ATOM_TENSOR_INTEGRAL. Qed.

Lemma ATOM_NEG_CONJ : forall m x,
  torus_atom (mode_neg m) x=cconj (torus_atom m x).
Proof.
  intros [mx my mz] [x y z].
  assert (Hp : phase (mode_neg (mkZ3 mx my mz)) (mkR3 x y z)=
    -phase (mkZ3 mx my mz) (mkR3 x y z)).
  { unfold phase, mode_neg, mode_sub, mode_zero. simpl.
    repeat rewrite minus_IZR. repeat rewrite opp_IZR. simpl. ring. }
  unfold torus_atom. rewrite Hp, cos_neg, sin_neg.
  unfold cconj, cre, cim. simpl. reflexivity.
Qed.

Lemma SUM_NEG_ZERO_IFF : forall p q,
  mode_add p (mode_neg q)=mode_zero <-> p=q.
Proof.
  intros [px py pz] [qx qy qz]. unfold mode_add, mode_neg, mode_sub, mode_zero.
  simpl. split; intro He; injection He as Hx Hy Hz; f_equal; lia.
Qed.

Theorem TORUS_ATOM_ORTHOGONALITY : forall p q,
  IsMean3 (fun x=>cmul (torus_atom p x) (torus_atom (mode_neg q) x))
    (if mode_eq_dec p q then cone else czero).
Proof.
  intros p q.
  assert (Hd : delta3 (mode_add p (mode_neg q))=
    if mode_eq_dec p q then cone else czero).
  { unfold delta3.
    destruct (mode_eq_dec (mode_add p (mode_neg q)) mode_zero) as [Ha|Ha];
      destruct (mode_eq_dec p q) as [Hb|Hb]; try reflexivity.
    - exfalso. apply Hb. apply (proj1 (SUM_NEG_ZERO_IFF p q)). exact Ha.
    - exfalso. apply Ha. apply (proj2 (SUM_NEG_ZERO_IFF p q)). exact Hb. }
  rewrite <- Hd. apply ISMEAN3_EXT with (f:=torus_atom (mode_add p (mode_neg q))).
  - intro x. symmetry. apply TORUS_ATOM_PRODUCT.
  - apply TORUS_ATOM_MEAN.
Qed.

Theorem TORUS_ATOM_CONJUGATE_ORTHOGONALITY : forall p q,
  IsMean3 (fun x=>cmul (torus_atom p x) (cconj (torus_atom q x)))
    (if mode_eq_dec p q then cone else czero).
Proof.
  intros p q. apply ISMEAN3_EXT with
    (f:=fun x=>cmul (torus_atom p x) (torus_atom (mode_neg q) x)).
  - intro x. rewrite ATOM_NEG_CONJ. reflexivity.
  - apply TORUS_ATOM_ORTHOGONALITY.
Qed.

Print Assumptions MEAN3_VALUE.
Print Assumptions TORUS_ATOM_PRODUCT.
Print Assumptions TORUS_ATOM_MEAN.
Print Assumptions TORUS_ATOM_ORTHOGONALITY.
Print Assumptions TORUS_ATOM_CONJUGATE_ORTHOGONALITY.
End BKQR_TORUS_ATOMS.
