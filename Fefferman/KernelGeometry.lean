import Fefferman.KernelCapacity

set_option autoImplicit false

namespace Fefferman

theorem k_one_positive {a : Analysis} (o : KernelArithmetic a) : a.lt a.zero a.one := by
  simpa only [o.natOne] using o.natPositive 1 (by decide)

theorem k_nat_two {a : Analysis} (o : KernelArithmetic a) :
    o.nat 2 = a.add a.one a.one := by
  simpa only [o.natOne] using o.natAdd 1 1

theorem k_nat_three {a : Analysis} (o : KernelArithmetic a) :
    o.nat 3 = a.add (a.add a.one a.one) a.one := by
  simpa only [k_nat_two o, o.natOne] using o.natAdd 2 1

theorem k_nat_four {a : Analysis} (o : KernelArithmetic a) :
    o.nat 4 = a.add (a.add a.one a.one) (a.add a.one a.one) := by
  simpa only [k_nat_two o] using o.natAdd 2 2

theorem k_nat_five {a : Analysis} (o : KernelArithmetic a) :
    o.nat 5 = a.add (o.nat 4) a.one := by
  simpa only [o.natOne] using o.natAdd 4 1

def KernelEnvelopeDen {a : Analysis} (o : KernelArithmetic a) (g : a.Scalar) : a.Scalar :=
  a.add (KScale o 2 g) a.one

def KernelEnvelopeNum {a : Analysis} (o : KernelArithmetic a) (g : a.Scalar) : a.Scalar :=
  a.add g (o.nat 2)

theorem kernel_gain_product {a : Analysis} (o : KernelArithmetic a) {g q : a.Scalar}
    (hg : a.le a.one g) (hq : a.le a.one q) : a.le a.one (a.mul g q) := by
  have h := o.mulLeLeft (o.leTrans (k_one_nonneg o) hg) hq
  rw [k_mul_one o] at h
  exact o.leTrans hg h

theorem kernel_envelope_den_positive {a : Analysis} (o : KernelArithmetic a)
    {g : a.Scalar} (hg : a.le a.zero g) : a.lt a.zero (KernelEnvelopeDen o g) :=
  o.ltLeTrans (k_one_positive o)
    (ledger_drop_left o.toLedgerArithmetic a.one (o.mulNonneg (o.natNonneg 2) hg))

/- NSHP00's polynomial remainder is expanded using only the scalar laws.
   This is the positive-variable form of 2(G-1)(q-1)(Gq-1). -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
theorem kernel_envelope_shape_identity {a : Analysis} (o : KernelArithmetic a)
    (x y : a.Scalar) :
    a.mul (KernelEnvelopeNum o (a.mul (a.add x a.one) (a.add y a.one)))
      (a.mul (KernelEnvelopeDen o (a.add x a.one)) (KernelEnvelopeDen o (a.add y a.one))) =
    a.add
      (a.mul (a.mul (KernelEnvelopeNum o (a.add x a.one)) (KernelEnvelopeNum o (a.add y a.one)))
        (KernelEnvelopeDen o (a.mul (a.add x a.one) (a.add y a.one))))
      (KScale o 2 (a.mul (a.mul x y) (a.add (a.add (a.mul x y) x) y))) := by
  -- Keep natural coefficients grouped; cancel a common product at the end.
  have h12 : a.add a.one (o.nat 2) = o.nat 3 := by
    simpa only [o.natOne] using (o.natAdd 1 2).symm
  have h21 : a.add (o.nat 2) a.one = o.nat 3 :=
    (o.addComm (o.nat 2) a.one).trans h12
  have scaleNat (m n : Nat) : KScale o m (o.nat n) = o.nat (m * n) :=
    (o.natMul m n).symm
  have scaleOne : KScale o 2 a.one = o.nat 2 := k_mul_one o (o.nat 2)
  have merge (v : a.Scalar) : a.add v (KScale o 2 v) = KScale o 3 v := by
    simpa only [k_scale_one o] using (k_scale_nat_add o 1 2 v).symm
  have affine (c d u v : a.Scalar) :
      a.mul (a.add (a.mul c u) d) (a.add (a.mul c v) d) =
        a.add (a.mul (a.mul c c) (a.mul u v))
          (a.add (a.mul (a.mul c d) (a.add u v)) (a.mul d d)) := by
    simp only [o.mulAdd, o.addMul, o.mulAssoc, o.mulComm,
      source_mul_interchange o.toSourceArithmetic,
      o.addAssoc, o.addComm, k_add_left_comm o]
  have numShift (v : a.Scalar) :
      KernelEnvelopeNum o (a.add v a.one) = a.add v (o.nat 3) := by
    rw [KernelEnvelopeNum, o.addAssoc, h12]
  have denShift (v : a.Scalar) :
      KernelEnvelopeDen o (a.add v a.one) = a.add (KScale o 2 v) (o.nat 3) := by
    rw [KernelEnvelopeDen, k_scale_add o 2 v a.one, scaleOne, o.addAssoc, h21]
  let t := a.mul x y
  let s := a.add x y
  have product : a.mul (a.add x a.one) (a.add y a.one) =
      a.add (a.add t s) a.one := by
    simp only [t, s, o.mulAdd, o.addMul, o.oneMul, k_mul_one o, o.addAssoc]
    exact congrArg (a.add (a.mul x y)) (k_add_left_comm o y x a.one)
  have numProduct :
      a.mul (KernelEnvelopeNum o (a.add x a.one)) (KernelEnvelopeNum o (a.add y a.one)) =
        a.add t (a.add (KScale o 3 s) (o.nat 9)) := by
    rw [numShift x, numShift y]
    change a.mul (a.add x (o.nat 3)) (a.add y (o.nat 3)) =
      a.add (a.mul x y) (a.add (a.mul (o.nat 3) (a.add x y)) (o.nat 9))
    simpa only [o.oneMul, ← o.natMul 3 3] using affine a.one (o.nat 3) x y
  have denProduct :
      a.mul (KernelEnvelopeDen o (a.add x a.one)) (KernelEnvelopeDen o (a.add y a.one)) =
        a.add (KScale o 4 t) (a.add (KScale o 6 s) (o.nat 9)) := by
    rw [denShift x, denShift y]
    change a.mul (a.add (a.mul (o.nat 2) x) (o.nat 3))
        (a.add (a.mul (o.nat 2) y) (o.nat 3)) =
      a.add (a.mul (o.nat 4) (a.mul x y))
        (a.add (a.mul (o.nat 6) (a.add x y)) (o.nat 9))
    rw [affine, ← o.natMul 2 2, ← o.natMul 2 3, ← o.natMul 3 3]
  have numComposite :
      KernelEnvelopeNum o (a.mul (a.add x a.one) (a.add y a.one)) =
        a.add (a.add t s) (o.nat 3) := by
    rw [product, numShift]
  have denComposite :
      KernelEnvelopeDen o (a.mul (a.add x a.one) (a.add y a.one)) =
        a.add (KScale o 2 (a.add t s)) (o.nat 3) := by
    rw [product, denShift]
  have denBalance :
      a.add
        (a.mul (KernelEnvelopeDen o (a.add x a.one)) (KernelEnvelopeDen o (a.add y a.one)))
        (KScale o 2 t) =
      KScale o 3 (KernelEnvelopeDen o (a.mul (a.add x a.one) (a.add y a.one))) := by
    rw [denProduct, denComposite, k_scale_add o 3 (KScale o 2 (a.add t s)) (o.nat 3),
      k_scale_comp o 3 2 (a.add t s), scaleNat 3 3, k_scale_add o 6 t s]
    rw [ledger_add_rotate o.toLedgerArithmetic (KScale o 4 t)
      (a.add (KScale o 6 s) (o.nat 9)) (KScale o 2 t),
      ← k_scale_nat_add o 4 2 t]
    exact (o.addAssoc (KScale o 6 t) (KScale o 6 s) (o.nat 9)).symm
  have numBalance :
      a.add
        (a.mul (KernelEnvelopeNum o (a.add x a.one)) (KernelEnvelopeNum o (a.add y a.one)))
        (KScale o 2 t) =
      KScale o 3 (KernelEnvelopeNum o (a.mul (a.add x a.one) (a.add y a.one))) := by
    rw [numProduct, numComposite, k_scale_add o 3 (a.add t s) (o.nat 3),
      k_scale_add o 3 t s, scaleNat 3 3]
    rw [ledger_add_rotate o.toLedgerArithmetic t
      (a.add (KScale o 3 s) (o.nat 9)) (KScale o 2 t), merge t]
    exact (o.addAssoc (KScale o 3 t) (KScale o 3 s) (o.nat 9)).symm
  have gap :
      KernelEnvelopeDen o (a.mul (a.add x a.one) (a.add y a.one)) =
        a.add (KernelEnvelopeNum o (a.mul (a.add x a.one) (a.add y a.one))) (a.add t s) := by
    rw [denComposite, numComposite, k_scale_two o]
    exact ledger_add_rotate o.toLedgerArithmetic (a.add t s) (a.add t s) (o.nat 3)
  have cancelProduct (A B N D U Z c : a.Scalar)
      (hA : a.add A U = a.mul c D) (hB : a.add B U = a.mul c N)
      (hD : D = a.add N Z) :
      a.mul N A = a.add (a.mul B D) (a.mul U Z) := by
    have he : a.add (a.mul N A) (a.mul N U) =
        a.add (a.add (a.mul B D) (a.mul U Z)) (a.mul N U) := by
      calc
        a.add (a.mul N A) (a.mul N U) = a.mul N (a.add A U) := (o.mulAdd N A U).symm
        _ = a.mul N (a.mul c D) := congrArg (a.mul N) hA
        _ = a.mul (a.mul c N) D :=
          (source_mul_interchange o.toSourceArithmetic N c D).trans (o.mulAssoc c N D).symm
        _ = a.mul (a.add B U) D := congrArg (fun v => a.mul v D) hB.symm
        _ = a.add (a.mul B D) (a.mul U D) := o.addMul B U D
        _ = a.add (a.mul B D) (a.mul U (a.add N Z)) :=
          congrArg (fun v => a.add (a.mul B D) (a.mul U v)) hD
        _ = a.add (a.mul B D) (a.add (a.mul U N) (a.mul U Z)) :=
          congrArg (a.add (a.mul B D)) (o.mulAdd U N Z)
        _ = a.add (a.add (a.mul B D) (a.mul U Z)) (a.mul N U) := by
          rw [o.mulComm U N, ← o.addAssoc,
            ledger_add_rotate o.toLedgerArithmetic (a.mul B D) (a.mul N U) (a.mul U Z)]
    have hc := congrArg (fun v => a.add v (a.neg (a.mul N U))) he
    simpa only [o.addAssoc, o.addNeg, o.addZero] using hc
  have remainder : a.mul (KScale o 2 t) (a.add t s) =
      KScale o 2 (a.mul (a.mul x y) (a.add (a.add (a.mul x y) x) y)) := by
    change a.mul (a.mul (o.nat 2) (a.mul x y)) (a.add (a.mul x y) (a.add x y)) =
      a.mul (o.nat 2) (a.mul (a.mul x y) (a.add (a.add (a.mul x y) x) y))
    rw [o.mulAssoc, o.addAssoc (a.mul x y) x y]
  have result := cancelProduct
    (a.mul (KernelEnvelopeDen o (a.add x a.one)) (KernelEnvelopeDen o (a.add y a.one)))
    (a.mul (KernelEnvelopeNum o (a.add x a.one)) (KernelEnvelopeNum o (a.add y a.one)))
    (KernelEnvelopeNum o (a.mul (a.add x a.one) (a.add y a.one)))
    (KernelEnvelopeDen o (a.mul (a.add x a.one) (a.add y a.one)))
    (KScale o 2 t) (a.add t s) (o.nat 3) denBalance numBalance gap
  rw [remainder] at result
  exact result

theorem kernel_envelope_shape {a : Analysis} (o : KernelArithmetic a)
    (g q : a.Scalar) (hg : a.le a.one g) (hq : a.le a.one q) :
    a.le (a.mul (a.mul (KernelEnvelopeNum o g) (KernelEnvelopeNum o q))
      (KernelEnvelopeDen o (a.mul g q)))
      (a.mul (KernelEnvelopeNum o (a.mul g q))
        (a.mul (KernelEnvelopeDen o g) (KernelEnvelopeDen o q))) := by
  let x := KSub a g a.one
  let y := KSub a q a.one
  have hx : a.le a.zero x := k_sub_nonneg o hg
  have hy : a.le a.zero y := k_sub_nonneg o hq
  have hxy := o.mulNonneg hx hy
  have hrem : a.le a.zero
      (KScale o 2 (a.mul (a.mul x y) (a.add (a.add (a.mul x y) x) y))) :=
    o.mulNonneg (o.natNonneg 2)
      (o.mulNonneg hxy (k_add_nonneg o (k_add_nonneg o hxy hx) hy))
  have h := ledger_drop_right o.toLedgerArithmetic
    (a.mul (a.mul (KernelEnvelopeNum o (a.add x a.one)) (KernelEnvelopeNum o (a.add y a.one)))
      (KernelEnvelopeDen o (a.mul (a.add x a.one) (a.add y a.one)))) hrem
  rw [← kernel_envelope_shape_identity o, k_sub_add o, k_sub_add o] at h
  exact h

theorem kernel_envelope_compose {a : Analysis} (o : KernelArithmetic a)
    (g r q s : a.Scalar) (hg : a.le a.one g) (hq : a.le a.one q)
    (hr : a.le a.zero r) (hs : a.le a.zero s)
    (hgr : a.le (a.mul r (KernelEnvelopeDen o g)) (KernelEnvelopeNum o g))
    (hqs : a.le (a.mul s (KernelEnvelopeDen o q)) (KernelEnvelopeNum o q)) :
    a.le (a.mul (a.mul r s) (KernelEnvelopeDen o (a.mul g q)))
      (KernelEnvelopeNum o (a.mul g q)) := by
  have hg0 := o.leTrans (k_one_nonneg o) hg
  have hq0 := o.leTrans (k_one_nonneg o) hq
  have hgd := kernel_envelope_den_positive o hg0
  have hqd := kernel_envelope_den_positive o hq0
  have hqn := k_add_nonneg o hq0 (o.natNonneg 2)
  have hp := o.leTrans
    (o.mulLeLeft (o.mulNonneg hr (o.ltToLe hgd)) hqs)
    (k_mul_le_right o hqn hgr)
  have htail := kernel_envelope_den_positive o (o.mulNonneg hg0 hq0)
  have hbig := o.leTrans (k_mul_le_right o (o.ltToLe htail) hp)
    (kernel_envelope_shape o g q hg hq)
  apply o.mulLeCancelLeft (o.mulPositive hgd hqd)
  simpa only [o.mulAssoc, o.mulComm, source_mul_interchange o.toSourceArithmetic] using hbig

inductive KernelHeterochiralPath {a : Analysis} (o : KernelArithmetic a) :
    a.Scalar → a.Scalar → Prop
  | identity : KernelHeterochiralPath o a.one a.one
  | step {g r q s : a.Scalar} : KernelHeterochiralPath o g r →
      a.le a.one q → a.le a.zero s →
      a.le (a.mul s (KernelEnvelopeDen o q)) (KernelEnvelopeNum o q) →
      KernelHeterochiralPath o (a.mul g q) (a.mul r s)

theorem kernel_path_envelope {a : Analysis} (o : KernelArithmetic a)
    {g r : a.Scalar} (h : KernelHeterochiralPath o g r) :
    a.le a.one g ∧ a.le a.zero r ∧
      a.le (a.mul r (KernelEnvelopeDen o g)) (KernelEnvelopeNum o g) := by
  induction h with
  | identity =>
    refine ⟨o.leRefl _, k_one_nonneg o, ?_⟩
    have he : a.mul a.one (KernelEnvelopeDen o a.one) = KernelEnvelopeNum o a.one := by
      simp only [o.oneMul, KernelEnvelopeDen, KernelEnvelopeNum, k_scale_two o, k_nat_two o,
        o.addAssoc]
    rw [he]
    exact o.leRefl _
  | @step g r q s _ hq hs hstep ih =>
    exact ⟨kernel_gain_product o ih.1 hq, o.mulNonneg ih.2.1 hs,
      kernel_envelope_compose o g r q s ih.1 hq ih.2.1 hs ih.2.2 hstep⟩

theorem kernel_first_crossing_four_fifths {a : Analysis} (o : KernelArithmetic a)
    {g r : a.Scalar} (h : KernelHeterochiralPath o g r) (hg : a.le (o.nat 2) g) :
    a.le (KScale o 5 r) (o.nat 4) := by
  have hinv := kernel_path_envelope o h
  have hden := kernel_envelope_den_positive o (o.leTrans (o.natNonneg 2) hg)
  have h3 := k_scale_le o 3 hg
  have hright : a.le (KScale o 5 (KernelEnvelopeNum o g))
      (KScale o 4 (KernelEnvelopeDen o g)) := by
    have h := o.addLeAdd (o.leRefl (KScale o 5 g))
      (o.addLeAdd h3 (o.leRefl (o.nat 4)))
    have he1 : a.add (KScale o 5 g) (a.add (KScale o 3 (o.nat 2)) (o.nat 4)) =
        KScale o 5 (KernelEnvelopeNum o g) := by
      simp only [KernelEnvelopeNum, KScale, k_nat_five o, k_nat_four o, k_nat_three o,
        k_nat_two o, o.addMul, o.mulAdd, o.oneMul, k_mul_one o,
        o.addAssoc, o.addComm, k_add_left_comm o]
    have he2 : a.add (KScale o 5 g) (a.add (KScale o 3 g) (o.nat 4)) =
        KScale o 4 (KernelEnvelopeDen o g) := by
      simp only [KernelEnvelopeDen, KScale, k_nat_five o, k_nat_four o, k_nat_three o,
        k_nat_two o, o.addMul, o.mulAdd, o.oneMul, k_mul_one o,
        o.addAssoc, o.addComm, k_add_left_comm o]
    rw [he1, he2] at h
    exact h
  have hh := o.leTrans (k_scale_le o 5 hinv.2.2) hright
  apply o.mulLeCancelLeft hden
  simpa only [KScale, o.mulAssoc, o.mulComm, source_mul_interchange o.toSourceArithmetic] using hh

end Fefferman
