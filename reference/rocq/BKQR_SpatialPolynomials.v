(* Literal trigonometric polynomials indexed by the constructed Z^3 bijection.
   Every spatial energy below is an actual normalized iterated Riemann mean. *)
From Stdlib Require Import Reals Lra Psatz Lia Arith.
Require Import BKQR_CountableRange BKQR_BilinearKernel BKQR_FourierIndices BKQR_PathTopology.
Require Import BKQR_FourierConvection BKQR_FourierBlocks BKQR_NSEFourierKernel.
Require Import BKQR_TorusAtoms.

Module BKQR_SPATIAL_POLYNOMIALS.
Import GP_COUNTABLE_RANGE BKQR_BILINEAR_KERNEL BKQR_FOURIER_INDICES.
Import BKQR_FOURIER_CONVECTION BKQR_FOURIER_BLOCKS BKQR_NSE_FOURIER_KERNEL.
Import BKQR_TORUS_ATOMS.
Import BKQR_PATH_TOPOLOGY.
Open Scope R_scope.

Definition complex_sum (N:nat) (f:nat->C2) : C2 :=
  (gp_sum N (fun i=>cre(f i)),gp_sum N (fun i=>cim(f i))).
Definition cabs2 (z:C2) : R := cre z*cre z+cim z*cim z.
Definition csub (z w:C2) : C2 := cadd z (cscale (-1) w).

Lemma complex_sum_zero : forall N,complex_sum N (fun _=>czero)=czero.
Proof. intro N. unfold complex_sum,czero,cre,cim. cbn. rewrite !sum_zero. reflexivity. Qed.
Lemma complex_sum_succ : forall N f,
  complex_sum (S N) f=cadd (complex_sum N f) (f N).
Proof. reflexivity. Qed.
Lemma complex_sum_ext : forall N f g,
  (forall i,(i<N)%nat ->f i=g i) ->complex_sum N f=complex_sum N g.
Proof.
  intros N f g H. unfold complex_sum. f_equal; apply gp_sum_ext;
    intros i Hi; rewrite H by exact Hi; reflexivity.
Qed.
Lemma complex_sum_plus : forall N f g,
  complex_sum N(fun i=>cadd(f i)(g i))=cadd(complex_sum N f)(complex_sum N g).
Proof. intros. unfold complex_sum,cadd,cre,cim. cbn. rewrite !sum_plus. reflexivity. Qed.
Lemma complex_sum_cmul_left : forall N c f,
  cmul c (complex_sum N f)=complex_sum N(fun i=>cmul c(f i)).
Proof.
  induction N; intros c f; [unfold cmul,complex_sum,cre,cim; cbn; f_equal; ring|].
  rewrite !complex_sum_succ,<-IHN. unfold cmul,cadd,cre,cim; cbn; f_equal; ring.
Qed.
Lemma complex_sum_cmul_right : forall N c f,
  cmul (complex_sum N f) c=complex_sum N(fun i=>cmul(f i)c).
Proof.
  induction N; intros c f; [unfold cmul,complex_sum,cre,cim; cbn; f_equal; ring|].
  rewrite !complex_sum_succ,<-IHN. unfold cmul,cadd,cre,cim; cbn; f_equal; ring.
Qed.
Lemma complex_sum_conjugate : forall N f,
  cconj(complex_sum N f)=complex_sum N(fun i=>cconj(f i)).
Proof.
  induction N; intros f; [unfold cconj,complex_sum,cre,cim; cbn; f_equal; ring|].
  rewrite !complex_sum_succ,<-IHN. unfold cconj,cadd,cre,cim; cbn; f_equal; ring.
Qed.
Lemma complex_double_product : forall N M f g c,
  cmul(cmul(complex_sum N f)(complex_sum M g))c=
  complex_sum N(fun p=>complex_sum M(fun q=>cmul(cmul(f p)(g q))c)).
Proof.
  intros N M f g c.
  rewrite (complex_sum_cmul_right N (complex_sum M g) f).
  rewrite complex_sum_cmul_right. apply complex_sum_ext. intros p Hp.
  rewrite complex_sum_cmul_left,complex_sum_cmul_right. reflexivity.
Qed.
Lemma complex_sum_real : forall N f,
  complex_sum N(fun i=>(f i,0))=(gp_sum N f,0).
Proof. intros. unfold complex_sum,cre,cim; cbn. rewrite sum_zero. reflexivity. Qed.
Lemma cmul_self_conjugate : forall z,cmul z(cconj z)=(cabs2 z,0).
Proof. intros [r i]. unfold cmul,cconj,cabs2,cre,cim; cbn; f_equal; ring. Qed.
Lemma cmul_one_right : forall z,cmul z cone=z.
Proof. intros [r i]. unfold cmul,cone,cre,cim; cbn; f_equal; ring. Qed.
Lemma cmul_zero_right : forall z,cmul z czero=czero.
Proof. intros [r i]. unfold cmul,czero,cre,cim; cbn; f_equal; ring. Qed.

Lemma ISMEAN3_COMPLEX_SUM : forall N f a,
  (forall i,(i<N)%nat ->IsMean3(f i)(a i)) ->
  IsMean3(fun x=>complex_sum N(fun i=>f i x))(complex_sum N a).
Proof.
  induction N; intros f a H.
  - change (IsMean3(fun _:R3=>czero)czero). apply ISMEAN3_CONST.
  - apply ISMEAN3_EXT with
      (f:=fun x=>cadd(complex_sum N(fun i=>f i x))(f N x)).
    + intro x. symmetry. apply complex_sum_succ.
    + rewrite complex_sum_succ. apply ISMEAN3_PLUS.
      * apply IHN. intros; apply H; lia.
      * apply H. lia.
Qed.

Definition scalar_polynomial (N:nat) (a:nat->C2) (x:R3) : C2 :=
  complex_sum N(fun p=>cmul(a p)(torus_atom(mode_decode p)x)).

Theorem SPATIAL_POLYNOMIAL_PRODUCT_COEFFICIENT : forall N M a b m,
  IsMean3(fun x=>cmul(cmul(scalar_polynomial N a x)(scalar_polynomial M b x))
    (cconj(torus_atom m x)))
    (complex_sum N(fun p=>complex_sum M(fun q=>
      if mode_eq_dec(mode_add(mode_decode p)(mode_decode q))m
      then cmul(a p)(b q) else czero))).
Proof.
  intros N M a b m. apply ISMEAN3_EXT with (f:=fun x=>
    complex_sum N(fun p=>complex_sum M(fun q=>
      cmul(cmul(a p)(b q))
        (cmul(torus_atom(mode_add(mode_decode p)(mode_decode q))x)
          (cconj(torus_atom m x)))))).
  - intro x. unfold scalar_polynomial. rewrite complex_double_product.
    apply complex_sum_ext. intros p Hp. apply complex_sum_ext. intros q Hq.
    rewrite <-TORUS_ATOM_PRODUCT.
    unfold cmul,cconj,cre,cim; cbn; f_equal; ring.
  - apply ISMEAN3_COMPLEX_SUM. intros p Hp. apply ISMEAN3_COMPLEX_SUM. intros q Hq.
    pose proof (TORUS_ATOM_CONJUGATE_ORTHOGONALITY
      (mode_add(mode_decode p)(mode_decode q))m) as Horth.
    pose proof (ISMEAN3_CMUL_L _ (cmul(a p)(b q)) _ Horth) as H.
    destruct(mode_eq_dec(mode_add(mode_decode p)(mode_decode q))m).
    + rewrite cmul_one_right in H. exact H.
    + rewrite cmul_zero_right in H. exact H.
Qed.

Theorem SPATIAL_PRODUCT_ACTUAL_MEAN : forall N M a b m,
  Mean3(fun x=>cmul(cmul(scalar_polynomial N a x)(scalar_polynomial M b x))
    (cconj(torus_atom m x)))=
  complex_sum N(fun p=>complex_sum M(fun q=>
    if mode_eq_dec(mode_add(mode_decode p)(mode_decode q))m
    then cmul(a p)(b q) else czero)).
Proof. intros. apply MEAN3_VALUE. apply SPATIAL_POLYNOMIAL_PRODUCT_COEFFICIENT. Qed.

Theorem SPATIAL_POLYNOMIAL_GRAM : forall N M a b,
  IsMean3(fun x=>cmul(scalar_polynomial N a x)(cconj(scalar_polynomial M b x)))
    (complex_sum N(fun p=>complex_sum M(fun q=>
      if Nat.eq_dec p q then cmul(a p)(cconj(b q)) else czero))).
Proof.
  intros N M a b. apply ISMEAN3_EXT with (f:=fun x=>
    complex_sum N(fun p=>complex_sum M(fun q=>
      cmul (cmul(a p)(cconj(b q)))
        (cmul(torus_atom(mode_decode p)x)(cconj(torus_atom(mode_decode q)x)))))).
  - intro x. unfold scalar_polynomial. rewrite complex_sum_conjugate.
    rewrite complex_sum_cmul_right. apply complex_sum_ext. intros p Hp.
    rewrite complex_sum_cmul_left. apply complex_sum_ext. intros q Hq.
    unfold cmul,cconj,cre,cim; cbn; f_equal; ring.
  - apply ISMEAN3_COMPLEX_SUM. intros p Hp. apply ISMEAN3_COMPLEX_SUM. intros q Hq.
    assert (Horth : IsMean3(fun x=>cmul(torus_atom(mode_decode p)x)
      (cconj(torus_atom(mode_decode q)x)))
      (if Nat.eq_dec p q then cone else czero)).
    { pose proof (TORUS_ATOM_CONJUGATE_ORTHOGONALITY (mode_decode p)(mode_decode q)) as H.
      destruct (Nat.eq_dec p q) as [Heq|Hneq];
        destruct(mode_eq_dec(mode_decode p)(mode_decode q)) as [Hmode|Hmode];
        try assumption.
      - exfalso. apply Hmode. now subst q.
      - exfalso. apply Hneq. apply mode_decode_injective. exact Hmode. }
    pose proof (ISMEAN3_CMUL_L _ (cmul(a p)(cconj(b q))) _ Horth) as H.
    destruct(Nat.eq_dec p q).
    + rewrite cmul_one_right in H. exact H.
    + rewrite cmul_zero_right in H. exact H.
Qed.

Lemma complex_sum_spike : forall N i z,
  complex_sum N(fun j=>if Nat.eq_dec i j then z else czero)=
  if lt_dec i N then z else czero.
Proof.
  induction N; intros i z.
  - cbn [complex_sum gp_sum]. destruct(lt_dec i 0); [lia|reflexivity].
  - rewrite complex_sum_succ,IHN.
    destruct(Nat.eq_dec i N) as [Heq|Hneq];
      destruct(lt_dec i N) as [Hi|Hi]; destruct(lt_dec i(S N)) as [HiS|HiS];
      try lia; unfold cadd,czero,cre,cim; cbn; destruct z; cbn; f_equal; ring.
Qed.

Lemma gram_diagonal : forall N a,
  complex_sum N(fun p=>complex_sum N(fun q=>
    if Nat.eq_dec p q then cmul(a p)(cconj(a q)) else czero))=
  (gp_sum N(fun p=>cabs2(a p)),0).
Proof.
  intros N a. rewrite <-complex_sum_real. apply complex_sum_ext. intros p Hp.
  transitivity (complex_sum N(fun q=>if Nat.eq_dec p q then
    cmul(a p)(cconj(a p)) else czero)).
  - apply complex_sum_ext. intros q Hq. destruct(Nat.eq_dec p q); [now subst q|reflexivity].
  - rewrite complex_sum_spike. destruct(lt_dec p N); [apply cmul_self_conjugate|lia].
Qed.

Definition scalar_energy (f:R3->C2) : R :=
  cre(Mean3(fun x=>(cabs2(f x),0))).

Theorem SPATIAL_SCALAR_PARSEVAL : forall N a,
  scalar_energy(scalar_polynomial N a)=gp_sum N(fun p=>cabs2(a p)).
Proof.
  intros N a. unfold scalar_energy.
  assert (H:IsMean3(fun x=>(cabs2(scalar_polynomial N a x),0))
    (gp_sum N(fun p=>cabs2(a p)),0)).
  { rewrite <-gram_diagonal. apply ISMEAN3_EXT with
      (f:=fun x=>cmul(scalar_polynomial N a x)(cconj(scalar_polynomial N a x))).
    - intro x. apply cmul_self_conjugate.
    - apply SPATIAL_POLYNOMIAL_GRAM. }
  rewrite (MEAN3_VALUE _ _ H). reflexivity.
Qed.

Definition vector_polynomial (x:nat->R) (N:nat) (p:R3) : ComplexVector :=
  fun axis=>scalar_polynomial N(fun m=>mode_vector x m axis)p.
Definition vector_energy (f:R3->ComplexVector) : R :=
  gp_sum 3(fun axis=>scalar_energy(fun p=>f p axis)).

Lemma mode_vector_block_energy : forall x p,
  gp_sum 3(fun a=>cabs2(mode_vector x p a))=block_complex_energy x p.
Proof.
  intros x p. unfold block_complex_energy. apply gp_sum_ext. intros a Ha.
  unfold cabs2,mode_vector,vector_from_scalars,block_vector,cre,cim; cbn [fst snd].
  replace (6*p+S(2*a))%nat with (6*p+2*a+1)%nat by lia. reflexivity.
Qed.

Theorem SPATIAL_VECTOR_PARSEVAL : forall x N,
  vector_energy(vector_polynomial x N)=physical_prefix x (6*N)%nat.
Proof.
  intros x N. unfold vector_energy,vector_polynomial.
  transitivity (gp_sum 3(fun a=>gp_sum N(fun p=>cabs2(mode_vector x p a)))).
  - apply gp_sum_ext. intros a Ha. apply SPATIAL_SCALAR_PARSEVAL.
  - rewrite sum_swap, BKFB31_EXACT_FINITE_COMPLEX_ENERGY.
    apply gp_sum_ext. intros p Hp. apply mode_vector_block_energy.
Qed.

Lemma scalar_energy_ext : forall f g,
  (forall x,f x=g x) ->scalar_energy f=scalar_energy g.
Proof.
  intros f g H. unfold scalar_energy. f_equal. apply MEAN3_EXT. intro x.
  rewrite H. reflexivity.
Qed.

Lemma complex_sum_cutoff : forall N M a,(N<=M)%nat ->
  complex_sum M(fun p=>if lt_dec p N then a p else czero)=complex_sum N a.
Proof.
  intros N M a HNM. unfold complex_sum,czero,cre,cim. f_equal.
  - transitivity (gp_sum M(fun p=>if lt_dec p N then fst(a p) else 0)).
    + apply gp_sum_ext. intros p Hp. destruct(lt_dec p N); reflexivity.
    + apply sum_cutoff. exact HNM.
  - transitivity (gp_sum M(fun p=>if lt_dec p N then snd(a p) else 0)).
    + apply gp_sum_ext. intros p Hp. destruct(lt_dec p N); reflexivity.
    + apply sum_cutoff. exact HNM.
Qed.
Lemma complex_sum_subtract : forall N f g,
  csub(complex_sum N f)(complex_sum N g)=complex_sum N(fun i=>csub(f i)(g i)).
Proof.
  induction N; intros f g.
  - unfold csub,complex_sum,cadd,cscale,cre,cim; cbn; f_equal; ring.
  - rewrite !complex_sum_succ,<-IHN.
    unfold csub,cadd,cscale,cre,cim; cbn; f_equal; ring.
Qed.
Lemma scalar_polynomial_cutoff : forall N M a,(N<=M)%nat ->forall x,
  scalar_polynomial M(fun p=>if lt_dec p N then a p else czero)x=
  scalar_polynomial N a x.
Proof.
  intros N M a HNM x. unfold scalar_polynomial.
  rewrite <- (complex_sum_cutoff N M
    (fun p=>cmul(a p)(torus_atom(mode_decode p)x)) HNM).
  apply complex_sum_ext. intros p Hp. destruct(lt_dec p N); [reflexivity|].
  unfold cmul,czero,cre,cim; cbn; f_equal; ring.
Qed.
Lemma scalar_polynomial_difference : forall N M a,(N<=M)%nat ->forall x,
  csub(scalar_polynomial M a x)(scalar_polynomial N a x)=
  scalar_polynomial M(fun p=>if lt_dec p N then czero else a p)x.
Proof.
  intros N M a HNM x. rewrite <- (scalar_polynomial_cutoff N M a HNM x).
  unfold scalar_polynomial. rewrite complex_sum_subtract.
  apply complex_sum_ext. intros p Hp. destruct(lt_dec p N);
    unfold cmul,csub,cadd,cscale,czero,cre,cim; cbn; f_equal; ring.
Qed.

Lemma sum_tail_difference : forall N M f,(N<=M)%nat ->
  gp_sum M(fun p=>if lt_dec p N then 0 else f p)=gp_sum M f-gp_sum N f.
Proof.
  intros N M f HNM. apply Rplus_eq_reg_r with (r:=gp_sum N f).
  replace (gp_sum M f-gp_sum N f+gp_sum N f) with (gp_sum M f) by ring.
  rewrite <- (sum_cutoff N M f HNM),<-sum_plus.
  apply gp_sum_ext. intros p Hp. destruct(lt_dec p N); ring.
Qed.

Theorem SPATIAL_SCALAR_PREFIX_ERROR : forall N M a,(N<=M)%nat ->
  scalar_energy(fun x=>csub(scalar_polynomial M a x)(scalar_polynomial N a x))=
  gp_sum M(fun p=>cabs2(a p))-gp_sum N(fun p=>cabs2(a p)).
Proof.
  intros N M a HNM.
  transitivity (scalar_energy(scalar_polynomial M(fun p=>if lt_dec p N then czero else a p))).
  - apply scalar_energy_ext. intro x. apply scalar_polynomial_difference. exact HNM.
  - rewrite SPATIAL_SCALAR_PARSEVAL.
    rewrite <- (sum_tail_difference N M(fun p=>cabs2(a p)) HNM).
    apply gp_sum_ext. intros p Hp. destruct(lt_dec p N); [unfold cabs2,czero,cre,cim; cbn; ring|reflexivity].
Qed.

Lemma sum_minus : forall N f g,
  gp_sum N(fun i=>f i-g i)=gp_sum N f-gp_sum N g.
Proof. induction N; intros; cbn [gp_sum]; [ring|rewrite IHN; ring]. Qed.

Theorem SPATIAL_VECTOR_PREFIX_ERROR : forall x N M,(N<=M)%nat ->
  vector_energy(fun p a=>csub(vector_polynomial x M p a)(vector_polynomial x N p a))=
  physical_prefix x (6*M)%nat-physical_prefix x (6*N)%nat.
Proof.
  intros x N M HNM. unfold vector_energy,vector_polynomial.
  transitivity (gp_sum 3(fun a=>
    gp_sum M(fun p=>cabs2(mode_vector x p a))-
    gp_sum N(fun p=>cabs2(mode_vector x p a)))).
  - apply gp_sum_ext. intros a Ha. apply SPATIAL_SCALAR_PREFIX_ERROR. exact HNM.
  - rewrite sum_minus. rewrite (sum_swap 3 M),(sum_swap 3 N).
    rewrite !BKFB31_EXACT_FINITE_COMPLEX_ENERGY.
    f_equal; apply gp_sum_ext; intros p Hp; apply mode_vector_block_energy.
Qed.

Lemma vector_error_symmetric : forall f g,
  vector_energy(fun p a=>csub(f p a)(g p a))=
  vector_energy(fun p a=>csub(g p a)(f p a)).
Proof.
  intros f g. unfold vector_energy. apply gp_sum_ext. intros a Ha.
  unfold scalar_energy. f_equal. apply MEAN3_EXT. intro p.
  unfold cabs2,csub,cadd,cscale,cre,cim; cbn; f_equal; ring.
Qed.

Definition SpatialPolynomialL2Cauchy (P:nat->R3->ComplexVector) : Prop :=
  forall eps,0<eps ->exists J,forall N M,(J<=N)%nat ->(J<=M)%nat ->
    vector_energy(fun p a=>csub(P M p a)(P N p a))<eps.

Theorem SPATIAL_FOURIER_PREFIXES_ARE_L2_CAUCHY : forall x E,
  PhysicalBound x E ->SpatialPolynomialL2Cauchy(vector_polynomial x).
Proof.
  intros x E HE eps Heps.
  destruct (physical_total_exists x (ex_intro _ E HE)) as [L HL].
  destruct (physical_total_limit x L HL eps Heps) as [J HJ].
  exists J. intros N M HN HM.
  destruct(Nat.le_ge_cases N M) as [HNM|HMN].
  - rewrite SPATIAL_VECTOR_PREFIX_ERROR by exact HNM.
    specialize (HJ (6*N)%nat ltac:(lia)).
    pose proof (proj1 HL (6*M)%nat). apply Rabs_def2 in HJ. lra.
  - rewrite vector_error_symmetric,SPATIAL_VECTOR_PREFIX_ERROR by exact HMN.
    specialize (HJ (6*M)%nat ltac:(lia)).
    pose proof (proj1 HL (6*N)%nat). apply Rabs_def2 in HJ. lra.
Qed.

Print Assumptions SPATIAL_POLYNOMIAL_GRAM.
Print Assumptions SPATIAL_VECTOR_PARSEVAL.
Print Assumptions SPATIAL_PRODUCT_ACTUAL_MEAN.
Print Assumptions SPATIAL_FOURIER_PREFIXES_ARE_L2_CAUCHY.
End BKQR_SPATIAL_POLYNOMIALS.
