import Fefferman.KernelRenewal

set_option autoImplicit false

namespace Fefferman

theorem k_prefix_sub {a : Analysis} (o : KernelArithmetic a) (f g : Nat → a.Scalar) (n : Nat) :
    ledgerPrefix a (fun i => KSub a (f i) (g i)) n =
      KSub a (ledgerPrefix a f n) (ledgerPrefix a g n) := by
  unfold KSub
  rw [spectral_prefix_add o.toLedgerArithmetic, spectral_prefix_neg o.toLedgerArithmetic]

theorem k_mul_sub {a : Analysis} (o : KernelArithmetic a) (x y z : a.Scalar) :
    a.mul x (KSub a y z) = KSub a (a.mul x y) (a.mul x z) := by
  unfold KSub
  rw [o.mulAdd, spectral_mul_neg o.toLedgerArithmetic]

theorem k_cancel_two {a : Analysis} (o : KernelArithmetic a) (x y z : a.Scalar) :
    a.add (a.add (a.add x (a.neg z)) (a.add (a.neg z) y)) (a.add z z) = a.add x y := by
  rw [spectral_add_shuffle o.toLedgerArithmetic (a.add x (a.neg z)) (a.add (a.neg z) y) z z,
    o.addAssoc x (a.neg z) z, ledger_neg_add o.toLedgerArithmetic, o.addZero,
    ledger_add_rotate o.toLedgerArithmetic (a.neg z) y z,
    ledger_neg_add o.toLedgerArithmetic, ledger_zero_add o.toLedgerArithmetic]

theorem kernel_square_completion {a : Analysis} (o : KernelArithmetic a) (x y : a.Scalar) :
    a.add (a.mul (KSub a x y) (KSub a x y)) (KScale o 2 (a.mul x y)) =
      a.add (a.mul x x) (a.mul y y) := by
  simp only [KSub, k_scale_two o, o.addMul, o.mulAdd,
    spectral_mul_neg o.toLedgerArithmetic, spectral_neg_mul o.toSourceArithmetic, k_neg_neg o]
  rw [o.mulComm y x]
  exact k_cancel_two o (a.mul x x) (a.mul y y) (a.mul x y)

def KernelDual (a : Analysis) (two : a.Scalar) (work energy detector : a.Scalar) : a.Scalar :=
  KSub a (a.mul two (a.mul detector work)) (a.mul (a.mul detector detector) energy)

theorem kernel_pointwise_dual_bound {a : Analysis} (o : KernelArithmetic a) (x y t : a.Scalar) :
    a.le (KernelDual a (o.nat 2) (a.mul x y) (a.mul y y) t) (a.mul x x) := by
  have hp := ledger_drop_left o.toLedgerArithmetic (KScale o 2 (a.mul x (a.mul t y)))
    (o.squareNonneg (KSub a x (a.mul t y)))
  rw [kernel_square_completion o] at hp
  have hs := k_le_add_to_sub_le o hp
  have hwork : a.mul x (a.mul t y) = a.mul t (a.mul x y) := source_mul_interchange o.toSourceArithmetic x t y
  have henergy : a.mul (a.mul t y) (a.mul t y) = a.mul (a.mul t t) (a.mul y y) :=
    spectral_square_product o.toSourceArithmetic t y
  rw [hwork, henergy] at hs
  exact hs

noncomputable def KernelPositiveAction {a : Analysis} (o : KernelArithmetic a)
    (work energy : a.Scalar) : a.Scalar := by
  classical
  exact if a.lt a.zero energy then
    if a.lt a.zero work then o.divide (a.mul work work) energy else a.zero
    else a.zero

theorem kernel_positive_action_nonnegative {a : Analysis} (o : KernelArithmetic a)
    (work energy : a.Scalar) : a.le a.zero (KernelPositiveAction o work energy) := by
  classical
  unfold KernelPositiveAction
  split
  · rename_i he
    split
    · exact k_div_nonneg o (o.squareNonneg work) he
    · exact o.leRefl a.zero
  · exact o.leRefl a.zero

theorem kernel_positive_action_of_dual_bound {a : Analysis} (o : KernelArithmetic a)
    (work energy bound : a.Scalar) (hb : a.le a.zero bound)
    (hd : ∀ t, a.le (KernelDual a (o.nat 2) work energy t) bound) :
    a.le (KernelPositiveAction o work energy) bound := by
  classical
  unfold KernelPositiveAction
  split
  · rename_i he
    split
    · let t := o.divide work energy
      have ht : a.mul energy t = work := o.mulDivide energy work he
      have hquad : a.mul (a.mul t t) energy = a.mul t work := by
        rw [o.mulAssoc, o.mulComm t energy, ht]
      have hdual : KernelDual a (o.nat 2) work energy t = a.mul t work := by
        change KSub a (KScale o 2 (a.mul t work)) (a.mul (a.mul t t) energy) = _
        rw [k_scale_two o, hquad, KSub, o.addAssoc, o.addNeg, o.addZero]
      have hnorm : a.mul energy (a.mul t work) = a.mul work work := by
        rw [← o.mulAssoc, ht]
      have heq : o.divide (a.mul work work) energy = a.mul t work := by
        apply o.leAntisymm
        · apply o.mulLeCancelLeft he
          rw [o.mulDivide energy _ he, hnorm]
          exact o.leRefl _
        · apply o.mulLeCancelLeft he
          rw [o.mulDivide energy _ he, hnorm]
          exact o.leRefl _
      rw [heq]
      simpa only [hdual] using hd t
    · exact hb
  · exact hb

def KernelWeightedDot (a : Analysis) (w f g : Nat → a.Scalar) (n : Nat) : a.Scalar :=
  ledgerPrefix a (fun i => a.mul (w i) (a.mul (f i) (g i))) n

theorem kernel_weighted_dual_identity {a : Analysis} (o : KernelArithmetic a)
    (w f g : Nat → a.Scalar) (n : Nat) (t : a.Scalar) :
    ledgerPrefix a (fun i => a.mul (w i)
      (KernelDual a (o.nat 2) (a.mul (f i) (g i)) (a.mul (g i) (g i)) t)) n =
    KernelDual a (o.nat 2) (KernelWeightedDot a w f g n) (KernelWeightedDot a w g g n) t := by
  have hp : ledgerPrefix a (fun i => a.mul (w i)
      (KernelDual a (o.nat 2) (a.mul (f i) (g i)) (a.mul (g i) (g i)) t)) n =
      ledgerPrefix a (fun i => KSub a
        (a.mul (a.mul (o.nat 2) t) (a.mul (w i) (a.mul (f i) (g i))))
        (a.mul (a.mul t t) (a.mul (w i) (a.mul (g i) (g i))))) n := by
    apply spectral_prefix_congr a n
    intro i _
    unfold KernelDual
    rw [k_mul_sub o]
    apply source_congr_arg_two (KSub a)
    · simp only [o.mulAssoc, o.mulComm, source_mul_interchange o.toSourceArithmetic]
    · exact source_mul_interchange o.toSourceArithmetic _ _ _
  rw [hp, k_prefix_sub o, ledger_prefix_scale o.toLedgerArithmetic,
    ledger_prefix_scale o.toLedgerArithmetic]
  unfold KernelDual KernelWeightedDot
  rw [o.mulAssoc]

theorem kernel_finite_action_bound {a : Analysis} (o : KernelArithmetic a)
    (w f g : Nat → a.Scalar) (n : Nat) (hw : ∀ i, i < n → a.le a.zero (w i)) :
    a.le (KernelPositiveAction o (KernelWeightedDot a w f g n) (KernelWeightedDot a w g g n))
      (KernelWeightedDot a w f f n) := by
  apply kernel_positive_action_of_dual_bound o
  · exact k_prefix_nonneg o n _ (fun i hi => o.mulNonneg (hw i hi) (o.squareNonneg (f i)))
  · intro t
    rw [← kernel_weighted_dual_identity o]
    exact k_prefix_mono o n _ _ (fun i hi => o.mulLeLeft (hw i hi) (kernel_pointwise_dual_bound o _ _ _))

theorem kernel_double_sum_swap {a : Analysis} (o : KernelArithmetic a)
    (f : Nat → Nat → a.Scalar) (m n : Nat) :
    ledgerPrefix a (fun i => ledgerPrefix a (f i) n) m =
      ledgerPrefix a (fun j => ledgerPrefix a (fun i => f i j) m) n := by
  induction m with
  | zero => exact (spectral_prefix_zero o.toLedgerArithmetic n).symm
  | succ m ih =>
    change a.add (ledgerPrefix a (fun i => ledgerPrefix a (f i) n) m) (ledgerPrefix a (f m) n) = _
    rw [ih]
    exact (spectral_prefix_add o.toLedgerArithmetic (fun j => ledgerPrefix a (fun i => f i j) m) (f m) n).symm

def KernelBoundaryBudget (a : Analysis) (rho source : Nat → a.Scalar) (n : Nat) : a.Scalar :=
  KernelWeightedDot a rho source source n

noncomputable def KernelUVAction {a : Analysis} (o : KernelArithmetic a)
    (weight : Nat → a.Scalar) (column : Nat → Nat → a.Scalar)
    (source : Nat → a.Scalar) (detector : Nat → Nat → a.Scalar) (m n : Nat) : a.Scalar :=
  ledgerPrefix a (fun j => a.mul (weight j)
    (KernelPositiveAction o (KernelWeightedDot a (column j) source (detector j) n)
      (KernelWeightedDot a (column j) (detector j) (detector j) n))) m

theorem kernel_column_action_bound {a : Analysis} (o : KernelArithmetic a)
    (weight : Nat → a.Scalar) (column : Nat → Nat → a.Scalar)
    (source : Nat → a.Scalar) (detector : Nat → Nat → a.Scalar) (rho : Nat → a.Scalar)
    (m n : Nat) (hw : ∀ j, j < m → a.le a.zero (weight j))
    (hc : ∀ j i, j < m → i < n → a.le a.zero (column j i))
    (hcol : ∀ i, i < n → a.le
      (KScale o 5 (ledgerPrefix a (fun j => a.mul (weight j) (column j i)) m)) (KScale o 4 (rho i))) :
    a.le (KScale o 5 (KernelUVAction o weight column source detector m n))
      (KScale o 4 (KernelBoundaryBudget a rho source n)) := by
  have hr := k_prefix_mono o m _ _ (fun j hj =>
    o.mulLeLeft (hw j hj) (kernel_finite_action_bound o (column j) source (detector j) n (fun i hi => hc j i hj hi)))
  have hid : ledgerPrefix a (fun j => a.mul (weight j) (KernelWeightedDot a (column j) source source n)) m =
      ledgerPrefix a (fun i => a.mul (a.mul (source i) (source i))
        (ledgerPrefix a (fun j => a.mul (weight j) (column j i)) m)) n := by
    calc
      _ = ledgerPrefix a (fun j => ledgerPrefix a (fun i =>
          a.mul (a.mul (source i) (source i)) (a.mul (weight j) (column j i))) n) m := by
        apply spectral_prefix_congr a m
        intro j _
        unfold KernelWeightedDot
        rw [← ledger_prefix_scale o.toLedgerArithmetic]
        apply spectral_prefix_congr a n
        intro i _
        simp only [o.mulAssoc, o.mulComm, source_mul_interchange o.toSourceArithmetic]
      _ = _ := by
        rw [kernel_double_sum_swap o]
        apply spectral_prefix_congr a n
        intro i _
        exact ledger_prefix_scale o.toLedgerArithmetic _ _ m
  rw [hid] at hr
  have hs := k_scale_le o 5 hr
  have hpoint : ∀ i, i < n → a.le
      (a.mul (o.nat 5) (a.mul (a.mul (source i) (source i))
        (ledgerPrefix a (fun j => a.mul (weight j) (column j i)) m)))
      (a.mul (o.nat 4) (a.mul (rho i) (a.mul (source i) (source i)))) := by
    intro i hi
    have hp := o.mulLeLeft (o.squareNonneg (source i)) (hcol i hi)
    simpa only [KScale, o.mulAssoc, o.mulComm, source_mul_interchange o.toSourceArithmetic] using hp
  have hp := k_prefix_mono o n _ _ hpoint
  rw [ledger_prefix_scale o.toLedgerArithmetic, ledger_prefix_scale o.toLedgerArithmetic] at hp
  exact o.leTrans hs hp

def KernelSurvival (a : Analysis) (take : Nat → a.Scalar) : Nat → a.Scalar
  | 0 => a.one
  | n+1 => KSub a (KernelSurvival a take n) (take n)

theorem kernel_survival_telescope {a : Analysis} (o : KernelArithmetic a)
    (take : Nat → a.Scalar) (n : Nat) :
    a.add (KernelSurvival a take n) (ledgerPrefix a take n) = a.one := by
  induction n with
  | zero => exact o.addZero a.one
  | succ n ih =>
    change a.add (KSub a (KernelSurvival a take n) (take n))
      (a.add (ledgerPrefix a take n) (take n)) = _
    rw [o.addComm (ledgerPrefix a take n) (take n), ← o.addAssoc, k_sub_add o]
    exact ih

theorem kernel_fraction_survival_step {a : Analysis} (o : KernelArithmetic a)
    (survival take child settled continuing : a.Scalar)
    (partition : a.add (a.add child settled) continuing = a.one)
    (route : take = a.mul survival (a.add child settled)) :
    KSub a survival take = a.mul survival continuing := by
  have hp := congrArg (a.mul survival) partition
  rw [o.mulAdd, k_mul_one o, ← route] at hp
  calc
    KSub a survival take = KSub a (a.add take (a.mul survival continuing)) take :=
      congrArg (fun z => KSub a z take) hp.symm
    _ = a.mul survival continuing := by
      rw [KSub, ledger_add_rotate o.toLedgerArithmetic, o.addNeg,
        ledger_zero_add o.toLedgerArithmetic]

theorem kernel_fraction_survival_nonnegative {a : Analysis} (o : KernelArithmetic a)
    (take child settled continuing : Nat → a.Scalar) (m : Nat)
    (hn : ∀ j, j < m → a.le a.zero (continuing j))
    (hp : ∀ j, j < m → a.add (a.add (child j) (settled j)) (continuing j) = a.one)
    (hr : ∀ j, j < m → take j = a.mul (KernelSurvival a take j) (a.add (child j) (settled j))) :
    ∀ k, k ≤ m → a.le a.zero (KernelSurvival a take k) := by
  intro k
  induction k with
  | zero => intro _; exact k_one_nonneg o
  | succ k ih =>
    intro hk
    have hkm : k < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
    change a.le a.zero (KSub a (KernelSurvival a take k) (take k))
    rw [kernel_fraction_survival_step o _ _ _ _ _ (hp k hkm) (hr k hkm)]
    exact o.mulNonneg (ih (Nat.le_trans (Nat.le_succ k) hk)) (hn k hkm)

theorem kernel_fraction_ownership {a : Analysis} (o : KernelArithmetic a)
    (take child settled continuing : Nat → a.Scalar) (m : Nat)
    (hn : ∀ j, j < m → a.le a.zero (continuing j))
    (hp : ∀ j, j < m → a.add (a.add (child j) (settled j)) (continuing j) = a.one)
    (hr : ∀ j, j < m → take j = a.mul (KernelSurvival a take j) (a.add (child j) (settled j))) :
    a.le (ledgerPrefix a take m) a.one := by
  have hs := kernel_fraction_survival_nonnegative o take child settled continuing m hn hp hr m (Nat.le_refl m)
  have h := ledger_drop_left o.toLedgerArithmetic (ledgerPrefix a take m) hs
  rw [kernel_survival_telescope o] at h
  exact h

def KernelOwnedColumn (a : Analysis) (retention rho : Nat → a.Scalar)
    (share : Nat → Nat → a.Scalar) (j i : Nat) : a.Scalar :=
  a.mul (a.mul (retention i) (share j i)) (rho i)

theorem kernel_capacity_no_reuse {a : Analysis} (o : KernelArithmetic a)
    (weight : Nat → a.Scalar) (share : Nat → Nat → a.Scalar) (rho retention : Nat → a.Scalar)
    (m i : Nat) (hr : a.le a.zero (retention i)) (hc : a.le a.zero (rho i))
    (ho : a.le (ledgerPrefix a (fun j => a.mul (weight j) (share j i)) m) a.one) :
    a.le (ledgerPrefix a (fun j => a.mul (weight j) (KernelOwnedColumn a retention rho share j i)) m)
      (a.mul (retention i) (rho i)) := by
  have he : ledgerPrefix a (fun j => a.mul (weight j) (KernelOwnedColumn a retention rho share j i)) m =
      a.mul (a.mul (retention i) (rho i)) (ledgerPrefix a (fun j => a.mul (weight j) (share j i)) m) := by
    rw [← ledger_prefix_scale o.toLedgerArithmetic]
    apply spectral_prefix_congr a m
    intro j _
    simp only [KernelOwnedColumn, o.mulAssoc, o.mulComm, source_mul_interchange o.toSourceArithmetic]
  rw [he]
  have h := o.mulLeLeft (o.mulNonneg hr hc) ho
  rw [k_mul_one o] at h
  exact h

end Fefferman
