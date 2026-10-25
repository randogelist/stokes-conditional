import Fefferman.FiniteSpectral

set_option autoImplicit false

namespace Fefferman

/- Additional ordinary ordered-field laws. No renewal, PDE, capacity,
   source-payment, or continuation assertion occurs in this structure. -/
structure KernelArithmetic (a : Analysis) extends SourceArithmetic a where
  leAntisymm : ∀ {x y}, a.le x y → a.le y x → x = y
  leTotal : ∀ x y, a.le x y ∨ a.le y x
  ltLeTrans : ∀ {x y z}, a.lt x y → a.le y z → a.lt x z
  ltOfNotLe : ∀ {x y}, (¬ a.le y x) → a.lt x y
  squareNonneg : ∀ x, a.le a.zero (a.mul x x)
  nat : Nat → a.Scalar
  natZero : nat 0 = a.zero
  natOne : nat 1 = a.one
  natAdd : ∀ m n, nat (m + n) = a.add (nat m) (nat n)
  natMul : ∀ m n, nat (m * n) = a.mul (nat m) (nat n)
  natNonneg : ∀ n, a.le a.zero (nat n)
  natPositive : ∀ n, 0 < n → a.lt a.zero (nat n)

def KSub (a : Analysis) (x y : a.Scalar) : a.Scalar := a.add x (a.neg y)
def KScale {a : Analysis} (o : KernelArithmetic a) (n : Nat) (x : a.Scalar) :=
  a.mul (o.nat n) x

theorem k_one_nonneg {a : Analysis} (o : KernelArithmetic a) : a.le a.zero a.one := by
  simpa only [o.natOne] using o.natNonneg 1

theorem k_mul_one {a : Analysis} (o : KernelArithmetic a) (x : a.Scalar) :
    a.mul x a.one = x := (o.mulComm x a.one).trans (o.oneMul x)

theorem k_zero_mul {a : Analysis} (o : KernelArithmetic a) (x : a.Scalar) :
    a.mul a.zero x = a.zero := (o.mulComm a.zero x).trans (o.mulZero x)

theorem k_add_nonneg {a : Analysis} (o : KernelArithmetic a) {x y : a.Scalar}
    (hx : a.le a.zero x) (hy : a.le a.zero y) : a.le a.zero (a.add x y) := by
  simpa only [o.addZero] using o.addLeAdd hx hy

theorem k_mul_le_right {a : Analysis} (o : KernelArithmetic a) {x y c : a.Scalar}
    (hc : a.le a.zero c) (h : a.le x y) : a.le (a.mul x c) (a.mul y c) := by
  simpa only [o.mulComm] using o.mulLeLeft hc h

theorem k_add_left_comm {a : Analysis} (o : KernelArithmetic a) (x y z : a.Scalar) :
    a.add x (a.add y z) = a.add y (a.add x z) := by
  rw [← o.addAssoc, o.addComm x y, o.addAssoc]

theorem k_neg_zero {a : Analysis} (o : KernelArithmetic a) : a.neg a.zero = a.zero := by
  have h := o.addNeg a.zero
  rw [ledger_zero_add o.toLedgerArithmetic] at h
  exact h

theorem k_neg_neg {a : Analysis} (o : KernelArithmetic a) (x : a.Scalar) :
    a.neg (a.neg x) = x :=
  (spectral_neg_of_add_zero o.toLedgerArithmetic (a.neg x) x
    (ledger_neg_add o.toLedgerArithmetic x)).symm

theorem k_neg_add {a : Analysis} (o : KernelArithmetic a) (x y : a.Scalar) :
    a.neg (a.add x y) = a.add (a.neg x) (a.neg y) := by
  apply Eq.symm
  apply spectral_neg_of_add_zero o.toLedgerArithmetic (a.add x y)
  rw [spectral_add_shuffle o.toLedgerArithmetic, o.addNeg, o.addNeg, o.addZero]

theorem k_add_neg_cancel {a : Analysis} (o : KernelArithmetic a) (x y : a.Scalar) :
    a.add x (a.add (a.neg x) y) = y := by
  rw [← o.addAssoc, o.addNeg, ledger_zero_add o.toLedgerArithmetic]

theorem k_neg_add_cancel {a : Analysis} (o : KernelArithmetic a) (x y : a.Scalar) :
    a.add (a.neg x) (a.add x y) = y := by
  rw [← o.addAssoc, ledger_neg_add o.toLedgerArithmetic, ledger_zero_add o.toLedgerArithmetic]

theorem k_sub_add {a : Analysis} (o : KernelArithmetic a) (x y : a.Scalar) :
    a.add (KSub a x y) y = x := by
  rw [KSub, o.addAssoc, ledger_neg_add o.toLedgerArithmetic, o.addZero]

theorem k_add_sub {a : Analysis} (o : KernelArithmetic a) (x y : a.Scalar) :
    a.add x (KSub a y x) = y := by
  rw [o.addComm x, k_sub_add o]

theorem k_sub_self {a : Analysis} (o : KernelArithmetic a) (x : a.Scalar) :
    KSub a x x = a.zero := o.addNeg x

theorem k_sub_zero {a : Analysis} (o : KernelArithmetic a) (x : a.Scalar) :
    KSub a x a.zero = x := by rw [KSub, k_neg_zero o, o.addZero]

theorem k_sub_nonneg {a : Analysis} (o : KernelArithmetic a) {x y : a.Scalar}
    (h : a.le x y) : a.le a.zero (KSub a y x) := by
  simpa only [KSub, o.addNeg] using o.addLeAdd h (o.leRefl (a.neg x))

theorem k_sub_nonpos {a : Analysis} (o : KernelArithmetic a) {x y : a.Scalar}
    (h : a.le x y) : a.le (KSub a x y) a.zero := by
  simpa only [KSub, o.addNeg] using o.addLeAdd h (o.leRefl (a.neg y))

theorem k_sub_le_to_le_add {a : Analysis} (o : KernelArithmetic a) {x y z : a.Scalar}
    (h : a.le (KSub a x y) z) : a.le x (a.add z y) := by
  simpa only [k_sub_add o] using o.addLeAdd h (o.leRefl y)

theorem k_le_add_to_sub_le {a : Analysis} (o : KernelArithmetic a) {x y z : a.Scalar}
    (h : a.le x (a.add z y)) : a.le (KSub a x y) z := by
  have hp := o.addLeAdd h (o.leRefl (a.neg y))
  rw [o.addAssoc z y (a.neg y), o.addNeg, o.addZero] at hp
  exact hp

theorem k_le_of_sub_nonpos {a : Analysis} (o : KernelArithmetic a) {x y : a.Scalar}
    (h : a.le (KSub a x y) a.zero) : a.le x y := by
  simpa only [ledger_zero_add o.toLedgerArithmetic] using k_sub_le_to_le_add o h

theorem k_sub_mono_left {a : Analysis} (o : KernelArithmetic a) {x y : a.Scalar}
    (z : a.Scalar) (h : a.le x y) : a.le (KSub a x z) (KSub a y z) :=
  o.addLeAdd h (o.leRefl (a.neg z))

theorem k_div_nonneg {a : Analysis} (o : KernelArithmetic a) {x c : a.Scalar}
    (hx : a.le a.zero x) (hc : a.lt a.zero c) : a.le a.zero (o.divide x c) := by
  apply o.mulLeCancelLeft hc
  rw [o.mulZero, o.mulDivide c x hc]
  exact hx

theorem k_scale_zero {a : Analysis} (o : KernelArithmetic a) (n : Nat) :
    KScale o n a.zero = a.zero := o.mulZero (o.nat n)

theorem k_scale_one {a : Analysis} (o : KernelArithmetic a) (x : a.Scalar) :
    KScale o 1 x = x := by rw [KScale, o.natOne, o.oneMul]

theorem k_scale_add {a : Analysis} (o : KernelArithmetic a) (n : Nat) (x y : a.Scalar) :
    KScale o n (a.add x y) = a.add (KScale o n x) (KScale o n y) :=
  o.mulAdd (o.nat n) x y

theorem k_scale_nat_add {a : Analysis} (o : KernelArithmetic a) (m n : Nat) (x : a.Scalar) :
    KScale o (m+n) x = a.add (KScale o m x) (KScale o n x) := by
  simp only [KScale, o.natAdd, o.addMul]

theorem k_scale_comp {a : Analysis} (o : KernelArithmetic a) (m n : Nat) (x : a.Scalar) :
    KScale o m (KScale o n x) = KScale o (m*n) x := by
  unfold KScale
  rw [o.natMul, o.mulAssoc]

theorem k_scale_sub {a : Analysis} (o : KernelArithmetic a) (n : Nat) (x y : a.Scalar) :
    KScale o n (KSub a x y) = KSub a (KScale o n x) (KScale o n y) := by
  unfold KScale KSub
  rw [o.mulAdd, spectral_mul_neg o.toLedgerArithmetic]

theorem k_sub_add_le {a : Analysis} (o : KernelArithmetic a) (z : a.Scalar)
    {x y : a.Scalar} (h : a.le x y) : a.le (a.add (KSub a z y) x) z := by
  have hp := o.addLeAdd (o.leRefl (KSub a z y)) h
  rw [k_sub_add o] at hp
  exact hp

theorem k_scale_two {a : Analysis} (o : KernelArithmetic a) (x : a.Scalar) :
    KScale o 2 x = a.add x x := by
  exact (k_scale_nat_add o 1 1 x).trans (source_congr_arg_two a.add (k_scale_one o x) (k_scale_one o x))

theorem k_scale_le {a : Analysis} (o : KernelArithmetic a) (n : Nat) {x y : a.Scalar}
    (h : a.le x y) : a.le (KScale o n x) (KScale o n y) := o.mulLeLeft (o.natNonneg n) h

theorem k_scale_cancel {a : Analysis} (o : KernelArithmetic a) (n : Nat) (hn : 0 < n)
    {x y : a.Scalar} (h : a.le (KScale o n x) (KScale o n y)) : a.le x y :=
  o.mulLeCancelLeft (o.natPositive n hn) h

theorem k_prefix_mono {a : Analysis} (o : KernelArithmetic a) (n : Nat)
    (f g : Nat → a.Scalar) (h : ∀ i, i < n → a.le (f i) (g i)) :
    a.le (ledgerPrefix a f n) (ledgerPrefix a g n) := by
  revert h
  induction n with
  | zero => intro _; exact o.leRefl a.zero
  | succ n ih =>
    intro h
    exact o.addLeAdd (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))))
      (h n (Nat.lt_succ_self n))

theorem k_prefix_nonneg {a : Analysis} (o : KernelArithmetic a) (n : Nat)
    (f : Nat → a.Scalar) (h : ∀ i, i < n → a.le a.zero (f i)) :
    a.le a.zero (ledgerPrefix a f n) := by
  have hp := k_prefix_mono o n (fun _ => a.zero) f h
  rw [spectral_prefix_zero o.toLedgerArithmetic] at hp
  exact hp

theorem k_prefix_telescope {a : Analysis} (o : KernelArithmetic a)
    (f : Nat → a.Scalar) (n : Nat) :
    ledgerPrefix a (fun k => KSub a (f (k+1)) (f k)) n = KSub a (f n) (f 0) := by
  induction n with
  | zero => exact (k_sub_self o (f 0)).symm
  | succ n ih =>
    change a.add (ledgerPrefix a (fun k => KSub a (f (k+1)) (f k)) n)
      (KSub a (f (n+1)) (f n)) = _
    rw [ih]
    unfold KSub
    rw [spectral_add_shuffle o.toLedgerArithmetic,
      o.addComm (a.neg (f 0)) (a.neg (f n)),
      spectral_add_shuffle o.toLedgerArithmetic,
      o.addNeg, ledger_zero_add o.toLedgerArithmetic]

noncomputable def KPositivePart (a : Analysis) (x : a.Scalar) : a.Scalar := by
  classical
  exact if a.le x a.zero then a.zero else x

theorem k_positive_nonneg {a : Analysis} (o : KernelArithmetic a) (x : a.Scalar) :
    a.le a.zero (KPositivePart a x) := by
  classical
  unfold KPositivePart
  split
  · exact o.leRefl a.zero
  · rename_i h
    exact o.ltToLe (o.ltOfNotLe h)

theorem k_le_positive {a : Analysis} (o : KernelArithmetic a) (x : a.Scalar) :
    a.le x (KPositivePart a x) := by
  classical
  unfold KPositivePart
  split
  · assumption
  · exact o.leRefl x

theorem k_positive_le {a : Analysis} (o : KernelArithmetic a) {x b : a.Scalar}
    (hb : a.le a.zero b) (hx : a.le x b) : a.le (KPositivePart a x) b := by
  classical
  unfold KPositivePart
  split
  · exact hb
  · exact hx

end Fefferman
