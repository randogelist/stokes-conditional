import Init

set_option autoImplicit false

namespace Fefferman

/- Core-only analytic signature. This is an interface, not a construction of
   the real numbers or a realization in real analysis. See SEMANTICS.txt.
   Coordinates, velocity components, and spatial derivatives have dimension 3.
   Space-time fields are represented on the ambient scalar line; all physical
   assertions are restricted to t >= 0. Smoothness includes the boundary t = 0.
   The time derivative is the derivative within the closed positive half-line. -/
structure Analysis where
  Scalar : Type
  zero : Scalar
  one : Scalar
  add : Scalar → Scalar → Scalar
  mul : Scalar → Scalar → Scalar
  neg : Scalar → Scalar
  le : Scalar → Scalar → Prop
  lt : Scalar → Scalar → Prop
  norm3 : (Fin 3 → Scalar) → Scalar
  dx : Fin 3 → ((Fin 3 → Scalar) → Scalar) → (Fin 3 → Scalar) → Scalar
  dt : (Scalar → Scalar) → Scalar → Scalar
  smoothSpatial : ((Fin 3 → Scalar) → Scalar) → Prop
  smoothClosedHalfSpace : ((Fin 3 → Scalar) → Scalar → Scalar) → Prop
  squareIntegrable : ((Fin 3 → Scalar) → (Fin 3 → Scalar)) → Prop
  integralNormSq : ((Fin 3 → Scalar) → (Fin 3 → Scalar)) → Scalar

abbrev Space (a : Analysis) := Fin 3 → a.Scalar
abbrev Vector (a : Analysis) := Fin 3 → a.Scalar
abbrev Initial (a : Analysis) := Space a → Vector a
abbrev Velocity (a : Analysis) := Space a → a.Scalar → Vector a
abbrev Force (a : Analysis) := Velocity a
abbrev Pressure (a : Analysis) := Space a → a.Scalar → a.Scalar
abbrev MultiIndex := Fin 3 → Nat
abbrev PositiveViscosity (a : Analysis) := {ν : a.Scalar // a.lt a.zero ν}

def sum3 (a : Analysis) (v : Fin 3 → a.Scalar) : a.Scalar :=
  a.add (a.add (v 0) (v 1)) (v 2)

def scalarPow (a : Analysis) (x : a.Scalar) : Nat → a.Scalar
  | 0 => a.one
  | n + 1 => a.mul x (scalarPow a x n)

def repeatOp {T : Type} (op : T → T) : Nat → T → T
  | 0, x => x
  | n + 1, x => op (repeatOp op n x)

def vectorDx (a : Analysis) (j : Fin 3) (v : Initial a) : Initial a :=
  fun x i => a.dx j (fun y => v y i) x

def spatialJet (a : Analysis) (α : MultiIndex) (v : Initial a) : Initial a :=
  repeatOp (vectorDx a 0) (α 0)
    (repeatOp (vectorDx a 1) (α 1) (repeatOp (vectorDx a 2) (α 2) v))

def vectorDt (a : Analysis) (v : Velocity a) : Velocity a :=
  fun x t i => a.dt (fun s => v x s i) t

def mixedJet (a : Analysis) (α : MultiIndex) (m : Nat)
    (f : Force a) (x : Space a) (t : a.Scalar) : Vector a :=
  spatialJet a α (fun y => repeatOp (vectorDt a) m f y t) x

def zeroForce (a : Analysis) : Force a := fun _ _ _ => a.zero

def unitShift (a : Analysis) (x : Space a) (j : Fin 3) : Space a :=
  fun i => if i = j then a.add (x i) a.one else x i

def initialSmooth (a : Analysis) (u₀ : Initial a) : Prop :=
  ∀ i, a.smoothSpatial (fun x => u₀ x i)

def vectorSmooth (a : Analysis) (u : Velocity a) : Prop :=
  ∀ i, a.smoothClosedHalfSpace (fun x t => u x t i)

def initialDivergenceFree (a : Analysis) (u₀ : Initial a) : Prop :=
  ∀ x, sum3 a (fun i => a.dx i (fun y => u₀ y i) x) = a.zero

/- (4), in weighted form: ||partial^alpha u0|| (1 + ||x||)^K <= C.
   This equals the decay formulation after the real-analysis realization. -/
def clause04 (a : Analysis) (u₀ : Initial a) : Prop :=
  ∀ (α : MultiIndex) (K : Nat), ∃ C : a.Scalar, a.lt a.zero C ∧
    ∀ x, a.le
      (a.mul (a.norm3 (spatialJet a α u₀ x))
        (scalarPow a (a.add a.one (a.norm3 x)) K)) C

/- (5): all mixed derivatives, with rapid joint space/time decay. -/
def clause05 (a : Analysis) (f : Force a) : Prop :=
  ∀ (α : MultiIndex) (m K : Nat), ∃ C : a.Scalar, a.lt a.zero C ∧
    ∀ x t, a.le a.zero t → a.le
      (a.mul (a.norm3 (mixedJet a α m f x t))
        (scalarPow a (a.add (a.add a.one (a.norm3 x)) t) K)) C

def initialPeriodic (a : Analysis) (u₀ : Initial a) : Prop :=
  ∀ x j, u₀ (unitShift a x j) = u₀ x

def vectorPeriodic (a : Analysis) (u : Velocity a) : Prop :=
  ∀ x t, a.le a.zero t → ∀ j, u (unitShift a x j) t = u x t

def pressurePeriodic (a : Analysis) (p : Pressure a) : Prop :=
  ∀ x t, a.le a.zero t → ∀ j, p (unitShift a x j) t = p x t

def clause08Data (a : Analysis) (u₀ : Initial a) (f : Force a) : Prop :=
  initialPeriodic a u₀ ∧ vectorPeriodic a f

/- (9): rapid time decay, uniformly in x; on t >= 0, |t| = t. -/
def clause09 (a : Analysis) (f : Force a) : Prop :=
  ∀ (α : MultiIndex) (m K : Nat), ∃ C : a.Scalar, a.lt a.zero C ∧
    ∀ x t, a.le a.zero t → a.le
      (a.mul (a.norm3 (mixedJet a α m f x t))
        (scalarPow a (a.add a.one t) K)) C

structure Solution (a : Analysis) where
  velocity : Velocity a
  pressure : Pressure a

def laplacian (a : Analysis) (g : Space a → a.Scalar) (x : Space a) : a.Scalar :=
  sum3 a (fun j => a.dx j (a.dx j g) x)

/- (1): dt u_i + sum_j u_j dx_j u_i = nu Delta u_i - dx_i p + f_i. -/
def clause01 (a : Analysis) (ν : PositiveViscosity a)
    (f : Force a) (s : Solution a) : Prop :=
  ∀ x t, a.le a.zero t → ∀ i,
    a.add (a.dt (fun r => s.velocity x r i) t)
      (sum3 a (fun j => a.mul (s.velocity x t j)
        (a.dx j (fun y => s.velocity y t i) x))) =
    a.add (a.add (a.mul ν.val (laplacian a (fun y => s.velocity y t i) x))
      (a.neg (a.dx i (fun y => s.pressure y t) x))) (f x t i)

def clause02 (a : Analysis) (s : Solution a) : Prop :=
  ∀ x t, a.le a.zero t →
    sum3 a (fun i => a.dx i (fun y => s.velocity y t i) x) = a.zero

def clause03 (a : Analysis) (u₀ : Initial a) (s : Solution a) : Prop :=
  ∀ x, s.velocity x a.zero = u₀ x

def clause06 (a : Analysis) (s : Solution a) : Prop :=
  vectorSmooth a s.velocity ∧ a.smoothClosedHalfSpace s.pressure

/- (7): one energy bound for ALL nonnegative times, not one bound per time.
   squareIntegrable prevents treating a totalized divergent integral as zero. -/
def clause07 (a : Analysis) (s : Solution a) : Prop :=
  ∃ C : a.Scalar, a.lt a.zero C ∧ ∀ t, a.le a.zero t →
    a.squareIntegrable (fun x => s.velocity x t) ∧
      a.lt (a.integralNormSq (fun x => s.velocity x t)) C

def clause10 (a : Analysis) (s : Solution a) : Prop :=
  vectorPeriodic a s.velocity

def clause11 (a : Analysis) (s : Solution a) : Prop := clause06 a s

/- The appended official erratum requires periodic pressure as well. -/
def periodicPressureErratum (a : Analysis) (s : Solution a) : Prop :=
  pressurePeriodic a s.pressure

end Fefferman
