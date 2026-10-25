import Master_T3_derivation

set_option autoImplicit false

namespace Fefferman

noncomputable def T3Delta (F : T3FourierAlgebra) (one : F.Coefficient)
    (p k : T3Wave) : F.Coefficient := by
  classical
  exact if p = k then one else F.zero

noncomputable def T3Coefficient (F : T3FourierAlgebra) (k : T3Wave)
    (terms : List (T3FourierTerm F)) : F.Coefficient := by
  classical
  exact terms.foldr (fun term rest =>
    F.add (if term.1 = k then term.2 else F.zero) rest) F.zero

/- HasMean retains integrability certificates. No linearity of a totalized
   integral on arbitrary nonintegrable functions is assumed.
   The Coquelicot construction of these laws and character orthogonality is
   present in LH50_00--11 and remains a separate analytic Lean port. -/
structure T3IntegralCalculus (F : T3FourierAlgebra) where
  one : F.Coefficient
  conjugate : F.Coefficient → F.Coefficient
  addZero : ∀ x, F.add x F.zero = x
  mulOne : ∀ x, F.mul x one = x
  conjugateZero : conjugate F.zero = F.zero
  conjugateAdd : ∀ x y, conjugate (F.add x y) = F.add (conjugate x) (conjugate y)
  conjugateMul : ∀ x y, conjugate (F.mul x y) = F.mul (conjugate x) (conjugate y)
  mean : (F.Point → F.Coefficient) → F.Coefficient
  HasMean : (F.Point → F.Coefficient) → F.Coefficient → Prop
  value : ∀ {f b}, HasMean f b → mean f = b
  constant : ∀ b, HasMean (fun _ => b) b
  ext : ∀ {f g b}, (∀ x, f x = g x) → HasMean f b → HasMean g b
  add : ∀ {f g b c}, HasMean f b → HasMean g c →
    HasMean (fun x => F.add (f x) (g x)) (F.add b c)
  scaleLeft : ∀ c {f b}, HasMean f b →
    HasMean (fun x => F.mul c (f x)) (F.mul c b)
  scaleRight : ∀ c {f b}, HasMean f b →
    HasMean (fun x => F.mul (f x) c) (F.mul b c)
  atomOrthogonality : ∀ p k,
    HasMean (fun x => F.mul (F.character p x) (conjugate (F.character k x)))
      (T3Delta F one p k)

def T3IntegralCoefficient {F : T3FourierAlgebra} (C : T3IntegralCalculus F)
    (f : F.Point → F.Coefficient) (k : T3Wave) : F.Coefficient :=
  C.mean (fun x => F.mul (f x) (C.conjugate (F.character k x)))

theorem T3_term_coefficient_certificate (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (p k : T3Wave) (b : F.Coefficient) :
    C.HasMean (fun x => F.mul (F.mul b (F.character p x))
      (C.conjugate (F.character k x)))
      (T3Coefficient F k [(p, b)]) := by
  classical
  have h := C.ext
    (fun x => (F.mulAssoc b (F.character p x) (C.conjugate (F.character k x))).symm)
    (C.scaleLeft b (C.atomOrthogonality p k))
  have hvalue : F.mul b (T3Delta F C.one p k) = T3Coefficient F k [(p, b)] := by
    change F.mul b (if p = k then C.one else F.zero) =
      F.add (if p = k then b else F.zero) F.zero
    by_cases hp : p = k
    · calc
        F.mul b (if p = k then C.one else F.zero) = F.mul b C.one :=
          congrArg (F.mul b) (if_pos hp)
        _ = b := C.mulOne b
        _ = F.add (if p = k then b else F.zero) F.zero :=
          ((C.addZero (if p = k then b else F.zero)).trans (if_pos hp)).symm
    · calc
        F.mul b (if p = k then C.one else F.zero) = F.mul b F.zero :=
          congrArg (F.mul b) (if_neg hp)
        _ = F.zero := F.mulZero b
        _ = F.add (if p = k then b else F.zero) F.zero :=
          ((C.addZero (if p = k then b else F.zero)).trans (if_neg hp)).symm
  rw [hvalue] at h
  exact h

theorem T3_polynomial_coefficient_certificate (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (terms : List (T3FourierTerm F)) (k : T3Wave) :
    C.HasMean (fun x => F.mul (T3PolynomialEval F terms x)
      (C.conjugate (F.character k x))) (T3Coefficient F k terms) := by
  classical
  induction terms with
  | nil =>
    exact C.ext (fun x => (F.zeroMul (C.conjugate (F.character k x))).symm)
      (C.constant F.zero)
  | cons term rest ih =>
    rcases term with ⟨p, b⟩
    have ht := T3_term_coefficient_certificate F C p k b
    change C.HasMean _ (F.add (if p = k then b else F.zero) F.zero) at ht
    rw [C.addZero] at ht
    exact C.ext
      (fun x => (F.addMul (F.mul b (F.character p x))
        (T3PolynomialEval F rest x) (C.conjugate (F.character k x))).symm)
      (C.add ht ih)

theorem T3_integral_coefficient_equals_algebraic (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (terms : List (T3FourierTerm F)) (k : T3Wave) :
    T3IntegralCoefficient C (T3PolynomialEval F terms) k = T3Coefficient F k terms :=
  C.value (T3_polynomial_coefficient_certificate F C terms k)

theorem T3_integral_of_polynomial_product (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (left right : List (T3FourierTerm F)) (k : T3Wave) :
    T3IntegralCoefficient C
      (fun x => F.mul (T3PolynomialEval F left x) (T3PolynomialEval F right x)) k =
        T3Coefficient F k (T3ProductTerms F left right) := by
  have he : (fun x => F.mul (T3PolynomialEval F left x) (T3PolynomialEval F right x)) =
      T3PolynomialEval F (T3ProductTerms F left right) :=
    funext (fun x => (T3_finite_product_is_convolution F left right x).symm)
  rw [he]
  exact T3_integral_coefficient_equals_algebraic F C (T3ProductTerms F left right) k

noncomputable def T3GramCoefficient {F : T3FourierAlgebra} (C : T3IntegralCalculus F)
    (left : List (T3FourierTerm F)) : List (T3FourierTerm F) → F.Coefficient
  | [] => F.zero
  | term :: rest => F.add (F.mul (T3Coefficient F term.1 left) (C.conjugate term.2))
      (T3GramCoefficient C left rest)

theorem T3_polynomial_gram_certificate (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (left right : List (T3FourierTerm F)) :
    C.HasMean (fun x => F.mul (T3PolynomialEval F left x)
      (C.conjugate (T3PolynomialEval F right x))) (T3GramCoefficient C left right) := by
  induction right with
  | nil =>
    apply C.ext (f := fun _ => F.zero)
    · intro x
      change F.zero = F.mul (T3PolynomialEval F left x) (C.conjugate F.zero)
      rw [C.conjugateZero, F.mulZero]
    · exact C.constant F.zero
  | cons term rest ih =>
    rcases term with ⟨q, b⟩
    have ht := C.scaleRight (C.conjugate b)
      (T3_polynomial_coefficient_certificate F C left q)
    apply C.ext (f := fun x => F.add
      (F.mul (F.mul (T3PolynomialEval F left x) (C.conjugate (F.character q x)))
        (C.conjugate b))
      (F.mul (T3PolynomialEval F left x) (C.conjugate (T3PolynomialEval F rest x))))
    · intro x
      change _ = F.mul (T3PolynomialEval F left x)
        (C.conjugate (F.add (F.mul b (F.character q x)) (T3PolynomialEval F rest x)))
      rw [C.conjugateAdd, C.conjugateMul, F.mulAdd,
        F.mulAssoc (T3PolynomialEval F left x) (C.conjugate (F.character q x)) (C.conjugate b),
        F.mulComm (C.conjugate (F.character q x)) (C.conjugate b)]
    · exact C.add ht ih

theorem T3_finite_gram_with_repeated_modes (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (left right : List (T3FourierTerm F)) :
    C.mean (fun x => F.mul (T3PolynomialEval F left x)
      (C.conjugate (T3PolynomialEval F right x))) = T3GramCoefficient C left right :=
  C.value (T3_polynomial_gram_certificate F C left right)

def T3Terms (F : T3FourierAlgebra) (modes : List T3Wave)
    (coeff : T3Wave → F.Coefficient) : List (T3FourierTerm F) :=
  modes.map (fun p => (p, coeff p))

/- The structural NoDup predicate is kept explicit for the core-only port. -/
def T3NoRepeatedModes : List T3Wave → Prop
  | [] => True
  | p :: rest => p ∉ rest ∧ T3NoRepeatedModes rest

def T3CoefficientSum (F : T3FourierAlgebra) (modes : List T3Wave)
    (f : T3Wave → F.Coefficient) : F.Coefficient :=
  modes.foldr (fun p s => F.add (f p) s) F.zero

theorem T3_coefficient_absent (F : T3FourierAlgebra) (C : T3IntegralCalculus F)
    (modes : List T3Wave) (coeff : T3Wave → F.Coefficient) (k : T3Wave) :
    k ∉ modes → T3Coefficient F k (T3Terms F modes coeff) = F.zero := by
  classical
  induction modes with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro hk
    have hp : p ≠ k := by
      intro h
      apply hk
      exact List.mem_cons.mpr (Or.inl h.symm)
    have hr : k ∉ rest := fun h => hk (List.mem_cons.mpr (Or.inr h))
    change F.add (if p = k then coeff p else F.zero)
      (T3Coefficient F k (T3Terms F rest coeff)) = F.zero
    rw [if_neg hp, ih hr, F.zeroAdd]

theorem T3_coefficient_present (F : T3FourierAlgebra) (C : T3IntegralCalculus F)
    (modes : List T3Wave) (coeff : T3Wave → F.Coefficient) (k : T3Wave) :
    T3NoRepeatedModes modes → k ∈ modes →
      T3Coefficient F k (T3Terms F modes coeff) = coeff k := by
  classical
  induction modes with
  | nil => intro _ hk; cases hk
  | cons p rest ih =>
    intro hnd hk
    change (p ∉ rest ∧ T3NoRepeatedModes rest) at hnd
    rcases List.mem_cons.mp hk with h | h
    · subst k
      change F.add (if p = p then coeff p else F.zero)
        (T3Coefficient F p (T3Terms F rest coeff)) = coeff p
      rw [if_pos rfl, T3_coefficient_absent F C rest coeff p hnd.1, C.addZero]
    · have hp : p ≠ k := by
        intro he
        exact hnd.1 (he.symm ▸ h)
      change F.add (if p = k then coeff p else F.zero)
        (T3Coefficient F k (T3Terms F rest coeff)) = coeff k
      rw [if_neg hp, F.zeroAdd]
      exact ih hnd.2 h

theorem T3_coefficient_sum_congr (F : T3FourierAlgebra) (modes : List T3Wave)
    (f g : T3Wave → F.Coefficient) :
    (∀ p, p ∈ modes → f p = g p) →
      T3CoefficientSum F modes f = T3CoefficientSum F modes g := by
  induction modes with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    change F.add (f p) (T3CoefficientSum F rest f) =
      F.add (g p) (T3CoefficientSum F rest g)
    rw [h p (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq)))]

theorem T3_gram_terms_sum (F : T3FourierAlgebra) (C : T3IntegralCalculus F)
    (left : List (T3FourierTerm F)) (modes : List T3Wave)
    (coeff : T3Wave → F.Coefficient) :
    T3GramCoefficient C left (T3Terms F modes coeff) =
      T3CoefficientSum F modes
        (fun p => F.mul (T3Coefficient F p left) (C.conjugate (coeff p))) := by
  induction modes with
  | nil => rfl
  | cons p rest ih =>
    change F.add _ (T3GramCoefficient C left (T3Terms F rest coeff)) = F.add _ _
    rw [ih] <;> rfl

theorem T3_finite_parseval_pairing (F : T3FourierAlgebra) (C : T3IntegralCalculus F)
    (modes : List T3Wave) (coeff : T3Wave → F.Coefficient)
    (hnd : T3NoRepeatedModes modes) :
    C.mean (fun x => F.mul (T3PolynomialEval F (T3Terms F modes coeff) x)
      (C.conjugate (T3PolynomialEval F (T3Terms F modes coeff) x))) =
      T3CoefficientSum F modes (fun p => F.mul (coeff p) (C.conjugate (coeff p))) := by
  rw [T3_finite_gram_with_repeated_modes F C, T3_gram_terms_sum F C]
  apply T3_coefficient_sum_congr F modes
  intro p hp
  rw [T3_coefficient_present F C modes coeff p hnd hp]

structure T3RealReadout (a : Analysis) (F : T3FourierAlgebra) where
  realPart : F.Coefficient → a.Scalar
  zero : realPart F.zero = a.zero
  add : ∀ x y, realPart (F.add x y) = a.add (realPart x) (realPart y)

def T3ScalarSum (a : Analysis) (modes : List T3Wave)
    (f : T3Wave → a.Scalar) : a.Scalar := modes.foldr (fun p s => a.add (f p) s) a.zero

def T3NormSquared {a : Analysis} {F : T3FourierAlgebra} (C : T3IntegralCalculus F)
    (r : T3RealReadout a F) (z : F.Coefficient) : a.Scalar :=
  r.realPart (F.mul z (C.conjugate z))

def T3ScalarEnergy {a : Analysis} {F : T3FourierAlgebra} (C : T3IntegralCalculus F)
    (r : T3RealReadout a F) (f : F.Point → F.Coefficient) : a.Scalar :=
  r.realPart (C.mean (fun x => F.mul (f x) (C.conjugate (f x))))

theorem T3_real_part_sum {a : Analysis} (F : T3FourierAlgebra)
    (r : T3RealReadout a F) (modes : List T3Wave) (f : T3Wave → F.Coefficient) :
    r.realPart (T3CoefficientSum F modes f) =
      T3ScalarSum a modes (fun p => r.realPart (f p)) := by
  induction modes with
  | nil => exact r.zero
  | cons p rest ih =>
    change r.realPart (F.add (f p) (T3CoefficientSum F rest f)) = a.add _ _
    rw [r.add, ih] <;> rfl

theorem T3_finite_scalar_parseval {a : Analysis} (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (r : T3RealReadout a F) (modes : List T3Wave)
    (coeff : T3Wave → F.Coefficient) (hnd : T3NoRepeatedModes modes) :
    T3ScalarEnergy C r (T3PolynomialEval F (T3Terms F modes coeff)) =
      T3ScalarSum a modes (fun p => T3NormSquared C r (coeff p)) := by
  unfold T3ScalarEnergy
  rw [T3_finite_parseval_pairing F C modes coeff hnd, T3_real_part_sum F r] <;> rfl

abbrev T3ComplexVector (F : T3FourierAlgebra) := Fin 3 → F.Coefficient

def T3VectorPolynomial (F : T3FourierAlgebra) (modes : List T3Wave)
    (u : T3Wave → T3ComplexVector F) (x : F.Point) : T3ComplexVector F :=
  fun j => T3PolynomialEval F (T3Terms F modes (fun p => u p j)) x

def T3VectorEnergy {a : Analysis} {F : T3FourierAlgebra} (C : T3IntegralCalculus F)
    (r : T3RealReadout a F) (f : F.Point → T3ComplexVector F) : a.Scalar :=
  sum3 a (fun j => T3ScalarEnergy C r (fun x => f x j))

def T3SpectralMass {a : Analysis} {F : T3FourierAlgebra} (C : T3IntegralCalculus F)
    (r : T3RealReadout a F) (modes : List T3Wave)
    (u : T3Wave → T3ComplexVector F) : a.Scalar :=
  sum3 a (fun j => T3ScalarSum a modes (fun p => T3NormSquared C r (u p j)))

theorem T3_finite_vector_parseval {a : Analysis} (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (r : T3RealReadout a F) (modes : List T3Wave)
    (u : T3Wave → T3ComplexVector F) (hnd : T3NoRepeatedModes modes) :
    T3VectorEnergy C r (T3VectorPolynomial F modes u) = T3SpectralMass C r modes u :=
  congrArg (sum3 a) (funext (fun j => T3_finite_scalar_parseval F C r modes
    (fun p => u p j) hnd))

def T3SpectralL2Bound {a : Analysis} {F : T3FourierAlgebra} (C : T3IntegralCalculus F)
    (r : T3RealReadout a F) (u : T3Wave → T3ComplexVector F) (E : a.Scalar) : Prop :=
  a.le a.zero E ∧ ∀ modes, T3NoRepeatedModes modes → a.le (T3SpectralMass C r modes u) E

theorem T3_spectral_bound_controls_polynomial_energy {a : Analysis} (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (r : T3RealReadout a F)
    (u : T3Wave → T3ComplexVector F) (E : a.Scalar) (hE : T3SpectralL2Bound C r u E)
    (modes : List T3Wave) (hnd : T3NoRepeatedModes modes) :
    a.le (T3VectorEnergy C r (T3VectorPolynomial F modes u)) E := by
  rw [T3_finite_vector_parseval F C r modes u hnd]
  exact hE.2 modes hnd

/- For the source 2*pi chart these are the real coordinates of k and i.
   The unit-periodic Fefferman chart needs an explicit rescaling. -/
structure T3ModeSymbols (F : T3FourierAlgebra) where
  wave : T3Wave → T3ComplexVector F
  imaginary : F.Coefficient

def T3WaveDot (F : T3FourierAlgebra) (m : T3ModeSymbols F) (k : T3Wave)
    (z : T3ComplexVector F) : F.Coefficient :=
  F.add (F.add (F.mul (m.wave k 0) (z 0)) (F.mul (m.wave k 1) (z 1)))
    (F.mul (m.wave k 2) (z 2))

noncomputable def T3PolynomialMode (F : T3FourierAlgebra) (m : T3ModeSymbols F)
    (left right : List T3Wave) (k : T3Wave)
    (u v : T3Wave → T3ComplexVector F) : T3ComplexVector F := fun j =>
  F.mul m.imaginary (T3Coefficient F k (T3ProductTerms F
    (T3Terms F left (fun p => T3WaveDot F m k (u p)))
    (T3Terms F right (fun q => v q j))))

def T3IntegralMode {F : T3FourierAlgebra} (C : T3IntegralCalculus F) (m : T3ModeSymbols F)
    (left right : List T3Wave) (k : T3Wave)
    (u v : T3Wave → T3ComplexVector F) : T3ComplexVector F := fun j =>
  F.mul m.imaginary (T3IntegralCoefficient C (fun x => F.mul
    (T3PolynomialEval F (T3Terms F left (fun p => T3WaveDot F m k (u p))) x)
    (T3PolynomialEval F (T3Terms F right (fun q => v q j)) x)) k)

theorem T3_integral_mode_equals_polynomial (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (m : T3ModeSymbols F) (left right : List T3Wave)
    (k : T3Wave) (u v : T3Wave → T3ComplexVector F) :
    T3IntegralMode C m left right k u v = T3PolynomialMode F m left right k u v := by
  funext j
  exact congrArg (F.mul m.imaginary) (T3_integral_of_polynomial_product F C
    (T3Terms F left (fun p => T3WaveDot F m k (u p)))
    (T3Terms F right (fun q => v q j)) k)

def T3Contains (small large : List T3Wave) : Prop := ∀ k, k ∈ small → k ∈ large

def T3TwoCutoffLimit (a : Analysis) (F : T3FourierAlgebra)
    (near : a.Scalar → T3ComplexVector F → T3ComplexVector F → Prop)
    (value : List T3Wave → List T3Wave → T3ComplexVector F)
    (target : T3ComplexVector F) : Prop :=
  ∀ eps, a.lt a.zero eps → ∃ leftCore rightCore,
    T3NoRepeatedModes leftCore ∧ T3NoRepeatedModes rightCore ∧
    ∀ left right, T3NoRepeatedModes left → T3NoRepeatedModes right →
      T3Contains leftCore left → T3Contains rightCore right → near eps (value left right) target

/- LH49_33 and LH49_41 are already proved in the supplied Rocq dependency.
   Their spectral completion proofs remain Lean ports. The bound and limit
   below concern the algebraic polynomial mode, before integral identification. -/
structure T3CompletionPort (a : Analysis) (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (r : T3RealReadout a F) (m : T3ModeSymbols F) where
  u : T3Wave → T3ComplexVector F
  v : T3Wave → T3ComplexVector F
  energyU : a.Scalar
  energyV : a.Scalar
  spectralU : T3SpectralL2Bound C r u energyU
  spectralV : T3SpectralL2Bound C r v energyV
  lambda : T3Wave → a.Scalar
  normSquared : T3ComplexVector F → a.Scalar
  near : a.Scalar → T3ComplexVector F → T3ComplexVector F → Prop
  completed : T3Wave → T3ComplexVector F
  polynomialBound : ∀ left right k, T3NoRepeatedModes left → T3NoRepeatedModes right →
    a.le (normSquared (T3PolynomialMode F m left right k u v))
      (a.mul (a.mul (lambda k) energyU) energyV)
  polynomialLimit : ∀ k, T3TwoCutoffLimit a F near
    (fun left right => T3PolynomialMode F m left right k u v) (completed k)

theorem T3_integral_mode_bound {a : Analysis} (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (r : T3RealReadout a F) (m : T3ModeSymbols F)
    (p : T3CompletionPort a F C r m) (left right : List T3Wave) (k : T3Wave)
    (hl : T3NoRepeatedModes left) (hr : T3NoRepeatedModes right) :
    a.le (p.normSquared (T3IntegralMode C m left right k p.u p.v))
      (a.mul (a.mul (p.lambda k) p.energyU) p.energyV) := by
  rw [T3_integral_mode_equals_polynomial F C m]
  exact p.polynomialBound left right k hl hr

theorem T3_integral_two_cutoff_limit {a : Analysis} (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (r : T3RealReadout a F) (m : T3ModeSymbols F)
    (p : T3CompletionPort a F C r m) (k : T3Wave) :
    T3TwoCutoffLimit a F p.near
      (fun left right => T3IntegralMode C m left right k p.u p.v) (p.completed k) := by
  have he : (fun left right => T3IntegralMode C m left right k p.u p.v) =
      (fun left right => T3PolynomialMode F m left right k p.u p.v) :=
    funext (fun left => funext (fun right =>
      T3_integral_mode_equals_polynomial F C m left right k p.u p.v))
  rw [he]
  exact p.polynomialLimit k

structure T3IntegralResult {a : Analysis} (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (r : T3RealReadout a F) (m : T3ModeSymbols F)
    (p : T3CompletionPort a F C r m) : Prop where
  coefficient : ∀ terms k, T3IntegralCoefficient C (T3PolynomialEval F terms) k =
    T3Coefficient F k terms
  finiteParseval : ∀ modes, T3NoRepeatedModes modes →
    T3VectorEnergy C r (T3VectorPolynomial F modes p.u) = T3SpectralMass C r modes p.u
  productIdentification : ∀ left right k,
    T3IntegralMode C m left right k p.u p.v = T3PolynomialMode F m left right k p.u p.v
  completedLimit : ∀ k, T3TwoCutoffLimit a F p.near
    (fun left right => T3IntegralMode C m left right k p.u p.v) (p.completed k)
  modeBound : ∀ left right k, T3NoRepeatedModes left → T3NoRepeatedModes right →
    a.le (p.normSquared (T3IntegralMode C m left right k p.u p.v))
      (a.mul (a.mul (p.lambda k) p.energyU) p.energyV)

theorem T3_integral_result {a : Analysis} (F : T3FourierAlgebra)
    (C : T3IntegralCalculus F) (r : T3RealReadout a F) (m : T3ModeSymbols F)
    (p : T3CompletionPort a F C r m) : T3IntegralResult F C r m p :=
  ⟨T3_integral_coefficient_equals_algebraic F C,
    fun modes hnd => T3_finite_vector_parseval F C r modes p.u hnd,
    fun left right k => T3_integral_mode_equals_polynomial F C m left right k p.u p.v,
    T3_integral_two_cutoff_limit F C r m p,
    T3_integral_mode_bound F C r m p⟩

end Fefferman
