From Stdlib Require Import Reals Lra Psatz Lia Field Reals.Rpower.
Require Import awpi_nse_finite_shell_algebra_v0_48_4.
Require Import awpi_nse_scalar_comparison_v0_48_4.
Require Import awpi_nse_storage_cost_algebra_v0_51_7.

Module NSE_STORAGE_INTERVAL_CALCULUS.
Import NSE_FINITE_SHELL_ALGEBRA NSE_SCALAR_COMPARISON NSE_STORAGE_COST_ALGEBRA.
Open Scope R_scope.

(* A concrete antiderivative on the positive z-axis.  No abstract
   integration operator, positivity axiom, or storage budget is used. *)
Definition passage_primitive y r beta S z :=
  y*z-r*ln z-(beta/2)*(S*(z*z)).
Definition closed_storage nu y r beta S a b :=
  /nu*(passage_primitive y r beta S b-passage_primitive y r beta S a).

Theorem NSSC00_PASSAGE_PRIMITIVE_DERIVATIVE : forall y r beta S z,
  0 < z -> derivable_pt_lim (passage_primitive y r beta S) z
    (profile y r beta S z/z).
Proof.
  intros y r beta S z Hz. unfold passage_primitive.
  replace (profile y r beta S z/z) with
    (y*1-r*(/z)-(beta/2)*(S*(1*z+z*1)))
    by (unfold profile; field; repeat split; lra).
  apply derivable_pt_lim_minus.
  - apply derivable_pt_lim_minus.
    + exact (@derivable_pt_lim_scal id y z 1 (derivable_pt_lim_id z)).
    + exact (@derivable_pt_lim_scal ln r z (/z) (derivable_pt_lim_ln z Hz)).
  - apply derivable_pt_lim_scal. apply derivable_pt_lim_scal.
    exact (@derivable_pt_lim_mult id id z 1 1
      (derivable_pt_lim_id z) (derivable_pt_lim_id z)).
Qed.

Lemma NSSC01_CLOSED_STORAGE_FORMULA : forall nu y r beta S a b,
  closed_storage nu y r beta S a b =
  (y*(b-a)-r*(ln b-ln a)-(beta*S/2)*(b*b-a*a))/nu.
Proof. intros; unfold closed_storage, passage_primitive, Rdiv; ring. Qed.

Lemma NSSC02_EMPTY_INTERVAL : forall nu y r beta S a,
  closed_storage nu y r beta S a a=0.
Proof. intros; unfold closed_storage; ring. Qed.

Theorem NSSC10_CLOSED_STORAGE_NONNEG : forall nu y r beta S a b,
  0 < nu -> 0 < a -> a <= b ->
  (forall z, a <= z <= b -> 0 <= profile y r beta S z) ->
  0 <= closed_storage nu y r beta S a b.
Proof.
  intros nu y r beta S a b Hnu Ha Hab Hg.
  assert (Hmon : -passage_primitive y r beta S b <=
                 -passage_primitive y r beta S a).
  { apply (NSCP00_NONPOS_DERIVATIVE
      (fun z => -passage_primitive y r beta S z)
      (fun z => -(profile y r beta S z/z)) a b Hab).
    - intros z Hz. apply derivable_pt_lim_opp.
      apply NSSC00_PASSAGE_PRIMITIVE_DERIVATIVE; lra.
    - intros z Hz. pose proof (NSFA08_DIV_NONNEG
        (profile y r beta S z) z (Hg z Hz) ltac:(lra)); lra. }
  unfold closed_storage. apply Rmult_le_pos.
  - left; apply Rinv_0_lt_compat; exact Hnu.
  - lra.
Qed.

Theorem NSSC11_CLOSED_STORAGE_QUADRATIC_BOUND : forall nu y r beta S a b,
  0 < nu -> 0 < r -> 0 <= beta -> 0 <= S ->
  0 < a -> a <= b -> b <= 1 ->
  (forall z, a <= z <= b -> 0 <= profile y r beta S z) ->
  closed_storage nu y r beta S a b <= y*y/(8*r*nu).
Proof.
  intros nu y r beta S a b Hnu Hr Hb HS Ha Hab Hb1 Hg.
  set (c := y*y/(4*r)).
  assert (Hc : 0 <= c).
  { unfold c; apply NSFA08_DIV_NONNEG; [exact (Rle_0_sqr y)|lra]. }
  assert (Hmon : passage_primitive y r beta S b-(c/2)*(b*b) <=
                 passage_primitive y r beta S a-(c/2)*(a*a)).
  { apply (NSCP00_NONPOS_DERIVATIVE
      (fun z => passage_primitive y r beta S z-(c/2)*(z*z))
      (fun z => profile y r beta S z/z-c*z) a b Hab).
    - intros z Hz.
      (* Normalize only the rational coefficient.  The common profile/z
         term is left untouched, so no new symbolic denominator is cleared. *)
      replace (c*z) with ((c/2)*(1*z+z*1)) by field.
      apply derivable_pt_lim_minus.
      + apply NSSC00_PASSAGE_PRIMITIVE_DERIVATIVE; lra.
      + apply derivable_pt_lim_scal.
        exact (@derivable_pt_lim_mult id id z 1 1
          (derivable_pt_lim_id z) (derivable_pt_lim_id z)).
    - intros z Hz.
      pose proof (NSST16_PASSAGE_QUADRATIC_BOUND y r beta S z
        Hr Hb HS ltac:(lra)) as Hq.
      unfold passage_integrand in Hq.
      rewrite (NSFA13_POS_ID _ (Hg z Hz)) in Hq.
      unfold c; lra. }
  assert (Hbs : b*b-a*a <= 1).
  { pose proof (Rle_0_sqr a) as Has; unfold Rsqr in Has.
    assert (Hone : 0 <= (1-b)*(1+b)) by (apply Rmult_le_pos; lra).
    nra. }
  pose proof (Rmult_le_compat_l c _ _ Hc Hbs) as Hmul.
  assert (Hd : passage_primitive y r beta S b-passage_primitive y r beta S a <= c/2)
    by nra.
  assert (Hinv : 0 <= /nu) by (left; apply Rinv_0_lt_compat; exact Hnu).
  pose proof (Rmult_le_compat_l (/nu) _ _ Hinv Hd) as Hscaled.
  assert (He : /nu*(c/2)=y*y/(8*r*nu)) by (unfold c; field; repeat split; lra).
  rewrite He in Hscaled; exact Hscaled.
Qed.

(* Endpoint representation: construction of a piece for every state and
   its compatibility through switches are separate analytic obligations. *)
Inductive PassagePiece : Type :=
| EmptyPassage
| ActivePassage (lower upper : R).
Definition PieceValid y r beta S (p : PassagePiece) : Prop :=
  match p with
  | EmptyPassage => forall z, 0 <= z <= 1 -> profile y r beta S z <= 0
  | ActivePassage a b =>
      0 < a /\ a <= b /\ b <= 1 /\
      profile y r beta S a=0 /\
      profile y r beta S b=pos (y-r-beta*S) /\
      (forall z, a <= z <= b -> 0 <= profile y r beta S z) /\
      (forall z, 0 <= z <= 1 -> z < a \/ b < z -> profile y r beta S z <= 0)
  end.
Definition piece_storage nu y r beta S p :=
  match p with EmptyPassage => 0
  | ActivePassage a b => closed_storage nu y r beta S a b end.
Definition piece_alpha p :=
  match p with EmptyPassage => 0 | ActivePassage a b => active_width a b end.
Definition piece_zeta p :=
  match p with EmptyPassage => 0 | ActivePassage a b => active_moment a b end.

Theorem NSSC20_VALID_PIECE_MOMENTS : forall y r beta S p,
  PieceValid y r beta S p ->
  0 <= piece_alpha p /\ piece_alpha p <= 1 /\
  0 <= piece_zeta p /\ piece_zeta p <= /2 /\
  y*piece_alpha p-2*beta*S*piece_zeta p=pos (y-r-beta*S).
Proof.
  intros y r beta S p Hp; destruct p as [|a b].
  - unfold PieceValid in Hp.
    specialize (Hp 1 ltac:(lra)). unfold profile in Hp.
    cbn [piece_alpha piece_zeta].
    rewrite NSFA12_POS_ZERO by lra; repeat split; lra.
  - destruct Hp as [Ha [Hab [Hb [Hpa [Hpb [Hg Hout]]]]]].
    cbn [piece_alpha piece_zeta].
    destruct (NSST20_ACTIVE_MOMENT_BOUNDS a b ltac:(lra) Hab Hb)
      as [Haw [Haw1 [Haz Haz1]]].
    repeat split; try assumption.
    exact (NSST21_ENDPOINT_EULER_IDENTITY y r beta S a b Hpa Hpb).
Qed.

Theorem NSSC21_VALID_PIECE_STORAGE_BOUND : forall nu y r beta S p,
  0 < nu -> 0 < r -> 0 <= beta -> 0 <= S -> PieceValid y r beta S p ->
  0 <= piece_storage nu y r beta S p /\
  piece_storage nu y r beta S p <= y*y/(8*r*nu).
Proof.
  intros nu y r beta S p Hnu Hr Hb HS Hp; destruct p as [|a b].
  - cbn [piece_storage]. split; [lra|]. apply NSFA08_DIV_NONNEG.
    + exact (Rle_0_sqr y).
    + repeat apply Rmult_lt_0_compat; lra.
  - destruct Hp as [Ha [Hab [Hb1 [Hpa [Hpb [Hg Hout]]]]]].
    cbn [piece_storage]. split.
    + exact (NSSC10_CLOSED_STORAGE_NONNEG nu y r beta S a b Hnu Ha Hab Hg).
    + exact (NSSC11_CLOSED_STORAGE_QUADRATIC_BOUND nu y r beta S a b
        Hnu Hr Hb HS Ha Hab Hb1 Hg).
Qed.

Theorem NSSC30_MOVING_PRIMITIVE_DERIVATIVE :
  forall (y S z : R -> R) yd Sd zd r beta t,
  derivable_pt_lim y t yd -> derivable_pt_lim S t Sd ->
  derivable_pt_lim z t zd -> 0 < z t ->
  derivable_pt_lim (fun s => passage_primitive (y s) r beta (S s) (z s)) t
    (yd*z t-(beta/2)*Sd*(z t*z t)+
      (profile (y t) r beta (S t) (z t)/z t)*zd).
Proof.
  intros y S z yd Sd zd r beta t Hy HS Hz Hzt.
  (* All derivative rules below receive their functions and evaluation
     point explicitly.  In particular, ln is differentiated at z t,
     while the composed function (fun s => ln (z s)) is differentiated
     at t.  No higher-order apply inference is used in this proof. *)
  pose proof (@derivable_pt_lim_comp z ln t zd (/z t) Hz
    (derivable_pt_lim_ln (z t) Hzt)) as Hln.
  pose proof (@derivable_pt_lim_mult y z t yd zd Hy Hz) as Hyz.
  pose proof (@derivable_pt_lim_mult z z t zd zd Hz Hz) as Hzz.
  pose proof (@derivable_pt_lim_mult
    S (fun s => z s*z s) t Sd (zd*z t+z t*zd) HS Hzz) as HSzz.
  pose proof (@derivable_pt_lim_scal
    (fun s => ln (z s)) r t ((/z t)*zd) Hln) as Hrln.
  pose proof (@derivable_pt_lim_scal
    (fun s => S s*(z s*z s)) (beta/2) t
    (Sd*(z t*z t)+S t*(zd*z t+z t*zd)) HSzz) as HbetaSzz.
  pose proof (@derivable_pt_lim_minus
    (fun s => y s*z s) (fun s => r*ln (z s)) t
    (yd*z t+y t*zd) (r*((/z t)*zd)) Hyz Hrln) as Hlinear.
  unfold passage_primitive.
  replace (yd*z t-(beta/2)*Sd*(z t*z t)+
      (profile (y t) r beta (S t) (z t)/z t)*zd) with
    ((yd*z t+y t*zd)-r*((/z t)*zd)-
      (beta/2)*(Sd*(z t*z t)+S t*(zd*z t+z t*zd)))
    by (unfold profile; field; repeat split; lra).
  exact (@derivable_pt_lim_minus
    (fun s => y s*z s-r*ln (z s))
    (fun s => (beta/2)*(S s*(z s*z s))) t
    ((yd*z t+y t*zd)-r*((/z t)*zd))
    ((beta/2)*(Sd*(z t*z t)+S t*(zd*z t+z t*zd)))
    Hlinear HbetaSzz).
Qed.

Theorem NSSC31_MOVING_ENDPOINTS_CANCEL :
  forall (y S a b : R -> R) yd Sd ad bd nu r beta t,
  derivable_pt_lim y t yd -> derivable_pt_lim S t Sd ->
  derivable_pt_lim a t ad -> derivable_pt_lim b t bd ->
  0 < a t -> 0 < b t ->
  profile (y t) r beta (S t) (a t)*ad=0 ->
  profile (y t) r beta (S t) (b t)*bd=0 ->
  derivable_pt_lim (fun s => closed_storage nu (y s) r beta (S s) (a s) (b s)) t
    (/nu*(active_width (a t) (b t)*yd-beta*active_moment (a t) (b t)*Sd)).
Proof.
  intros y S a b yd Sd ad bd nu r beta t Hy HS Ha Hb Hat Hbt Hac Hbc.
  pose proof (NSSC30_MOVING_PRIMITIVE_DERIVATIVE y S a yd Sd ad r beta t
    Hy HS Ha Hat) as Hpa.
  pose proof (NSSC30_MOVING_PRIMITIVE_DERIVATIVE y S b yd Sd bd r beta t
    Hy HS Hb Hbt) as Hpb.
  assert (Hac' : profile (y t) r beta (S t) (a t)/a t*ad=0).
  { replace (profile (y t) r beta (S t) (a t)/a t*ad)
      with ((profile (y t) r beta (S t) (a t)*ad)/a t) by (field; repeat split; lra).
    rewrite Hac; unfold Rdiv; ring. }
  assert (Hbc' : profile (y t) r beta (S t) (b t)/b t*bd=0).
  { replace (profile (y t) r beta (S t) (b t)/b t*bd)
      with ((profile (y t) r beta (S t) (b t)*bd)/b t) by (field; repeat split; lra).
    rewrite Hbc; unfold Rdiv; ring. }
  rewrite Hac' in Hpa; rewrite Hbc' in Hpb.
  unfold closed_storage.
  replace (/nu*(active_width (a t) (b t)*yd-beta*active_moment (a t) (b t)*Sd))
    with (/nu*((yd*b t-(beta/2)*Sd*(b t*b t)+0)-
               (yd*a t-(beta/2)*Sd*(a t*a t)+0)))
    (* Keep /nu as an unchanged factor: nu is not assumed nonzero here. *)
    by (unfold active_width, active_moment, Rdiv; ring).
  exact (@derivable_pt_lim_scal
    (fun s => passage_primitive (y s) r beta (S s) (b s)-
              passage_primitive (y s) r beta (S s) (a s))
    (/nu) t
    ((yd*b t-(beta/2)*Sd*(b t*b t)+0)-
     (yd*a t-(beta/2)*Sd*(a t*a t)+0))
    (@derivable_pt_lim_minus
      (fun s => passage_primitive (y s) r beta (S s) (b s))
      (fun s => passage_primitive (y s) r beta (S s) (a s)) t
      (yd*b t-(beta/2)*Sd*(b t*b t)+0)
      (yd*a t-(beta/2)*Sd*(a t*a t)+0)
      Hpb Hpa)).
Qed.


Theorem NSSC40_FINITE_VALID_PIECES_INITIAL_STORAGE_BOUND :
  forall n nu r beta (y S lambda : nat -> R) (pieces : nat -> PassagePiece) E0,
  0 < nu -> 0 < r -> 0 <= beta ->
  (forall j, (j<n)%nat -> 0 <= S j) ->
  (forall j, (j<n)%nat -> PieceValid (y j) r beta (S j) (pieces j)) ->
  (forall j, (j<n)%nat -> y j*y j <= 125*lambda j*S j) ->
  total (fun j => lambda j*S j) n <= E0 ->
  0 <= total (fun j => piece_storage nu (y j) r beta (S j) (pieces j)) n /\
  total (fun j => piece_storage nu (y j) r beta (S j) (pieces j)) n
    <= 125*E0/(8*r*nu).
Proof.
  intros n nu r beta y S lambda pieces E0 Hnu Hr Hb HS Hp Hl HE.
  apply (NSST30_FINITE_INITIAL_STORAGE_BOUND n
    (fun j => piece_storage nu (y j) r beta (S j) (pieces j))
    y lambda S r nu E0 Hr Hnu).
  - intros j Hj; exact (NSSC21_VALID_PIECE_STORAGE_BOUND nu (y j) r beta
      (S j) (pieces j) Hnu Hr Hb (HS j Hj) (Hp j Hj)).
  - exact Hl.
  - exact HE.
Qed.

End NSE_STORAGE_INTERVAL_CALCULUS.
