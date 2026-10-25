import Fefferman.KernelGeometry

set_option autoImplicit false

namespace Fefferman

/- Actual finite arrays; neither common capacity nor the 509 estimate is
   stored here. Columns and actions are computed from these arrays. -/
structure KernelBirthFrame (a : Analysis) where
  internal : a.Scalar
  rows : Nat
  columns : Nat
  weight : Nat → a.Scalar
  rho : Nat → a.Scalar
  source : Nat → a.Scalar
  gain : Nat → a.Scalar
  retention : Nat → a.Scalar
  share : Nat → Nat → a.Scalar
  detector : Nat → Nat → a.Scalar
  child : Nat → Nat → a.Scalar
  settled : Nat → Nat → a.Scalar
  continuing : Nat → Nat → a.Scalar

def KernelBirthColumn {a : Analysis} (b : KernelBirthFrame a) : Nat → Nat → a.Scalar :=
  KernelOwnedColumn a b.retention b.rho b.share

def KernelBirthBoundary {a : Analysis} (b : KernelBirthFrame a) : a.Scalar :=
  KernelBoundaryBudget a b.rho b.source b.columns

noncomputable def KernelBirthUV {a : Analysis} (o : KernelArithmetic a) (b : KernelBirthFrame a) : a.Scalar :=
  KernelUVAction o b.weight (KernelBirthColumn b) b.source b.detector b.rows b.columns

structure KernelBirthWitness {a : Analysis} (o : KernelArithmetic a)
    (b : KernelBirthFrame a) (parent child paid : a.Scalar) : Prop where
  parentNonnegative : a.le a.zero parent
  paidNonnegative : a.le a.zero paid
  internalNonnegative : a.le a.zero b.internal
  weightNonnegative : ∀ j, j < b.rows → a.le a.zero (b.weight j)
  rhoNonnegative : ∀ i, i < b.columns → a.le a.zero (b.rho i)
  shareNonnegative : ∀ j i, j < b.rows → i < b.columns → a.le a.zero (b.share j i)
  continuingNonnegative : ∀ j i, j < b.rows → i < b.columns → a.le a.zero (b.continuing j i)
  partition : ∀ j i, j < b.rows → i < b.columns →
    a.add (a.add (b.child j i) (b.settled j i)) (b.continuing j i) = a.one
  route : ∀ j i, j < b.rows → i < b.columns →
    a.mul (b.weight j) (b.share j i) =
      a.mul (KernelSurvival a (fun k => a.mul (b.weight k) (b.share k i)) j)
        (a.add (b.child j i) (b.settled j i))
  path : ∀ i, i < b.columns → KernelHeterochiralPath o (b.gain i) (b.retention i)
  crossing : ∀ i, i < b.columns → a.le (o.nat 2) (b.gain i)
  parentSplit : parent = a.add b.internal (KernelBirthBoundary b)
  internalGap : a.le (KScale o 121 b.internal) (KScale o 25 parent)
  childAssembly : a.le child (a.add (a.add b.internal (KernelBirthUV o b)) paid)

def KernelCommonCapacity {a : Analysis} (b : KernelBirthFrame a) : Prop :=
  ∀ i, i < b.columns →
    a.le (ledgerPrefix a (fun j => a.mul (b.weight j) (KernelBirthColumn b j i)) b.rows)
      (a.mul (b.retention i) (b.rho i))

theorem kernel_birth_ownership {a : Analysis} (o : KernelArithmetic a)
    {b : KernelBirthFrame a} {parent child paid : a.Scalar}
    (h : KernelBirthWitness o b parent child paid) (i : Nat) (hi : i < b.columns) :
    a.le (ledgerPrefix a (fun j => a.mul (b.weight j) (b.share j i)) b.rows) a.one :=
  kernel_fraction_ownership o _ (fun j => b.child j i) (fun j => b.settled j i)
    (fun j => b.continuing j i) b.rows
    (fun j hj => h.continuingNonnegative j i hj hi)
    (fun j hj => h.partition j i hj hi) (fun j hj => h.route j i hj hi)

theorem kernel_birth_capacity {a : Analysis} (o : KernelArithmetic a)
    {b : KernelBirthFrame a} {parent child paid : a.Scalar}
    (h : KernelBirthWitness o b parent child paid) : KernelCommonCapacity b := by
  intro i hi
  exact kernel_capacity_no_reuse o b.weight b.share b.rho b.retention b.rows i
    (kernel_path_envelope o (h.path i hi)).2.1 (h.rhoNonnegative i hi)
    (kernel_birth_ownership o h i hi)

theorem kernel_birth_column_nonnegative {a : Analysis} (o : KernelArithmetic a)
    {b : KernelBirthFrame a} {parent child paid : a.Scalar}
    (h : KernelBirthWitness o b parent child paid) (j i : Nat)
    (hj : j < b.rows) (hi : i < b.columns) : a.le a.zero (KernelBirthColumn b j i) :=
  o.mulNonneg
    (o.mulNonneg (kernel_path_envelope o (h.path i hi)).2.1 (h.shareNonnegative j i hj hi))
    (h.rhoNonnegative i hi)

theorem kernel_birth_column_bound {a : Analysis} (o : KernelArithmetic a)
    {b : KernelBirthFrame a} {parent child paid : a.Scalar}
    (h : KernelBirthWitness o b parent child paid) (i : Nat) (hi : i < b.columns) :
    a.le (KScale o 5
      (ledgerPrefix a (fun j => a.mul (b.weight j) (KernelBirthColumn b j i)) b.rows))
      (KScale o 4 (b.rho i)) := by
  have hret := kernel_first_crossing_four_fifths o (h.path i hi) (h.crossing i hi)
  have hp := k_mul_le_right o (h.rhoNonnegative i hi) hret
  have hc := k_scale_le o 5 (kernel_birth_capacity o h i hi)
  exact o.leTrans hc (by simpa only [KScale, o.mulAssoc] using hp)

theorem kernel_birth_uv_bound {a : Analysis} (o : KernelArithmetic a)
    {b : KernelBirthFrame a} {parent child paid : a.Scalar}
    (h : KernelBirthWitness o b parent child paid) :
    a.le (KScale o 5 (KernelBirthUV o b)) (KScale o 4 (KernelBirthBoundary b)) :=
  kernel_column_action_bound o b.weight (KernelBirthColumn b) b.source b.detector b.rho
    b.rows b.columns h.weightNonnegative (kernel_birth_column_nonnegative o h)
    (kernel_birth_column_bound o h)

theorem kernel_birth_step {a : Analysis} (o : KernelArithmetic a)
    {b : KernelBirthFrame a} {parent child paid : a.Scalar}
    (h : KernelBirthWitness o b parent child paid) :
    a.le (KScale o 605 child) (a.add (KScale o 509 parent) (KScale o 605 paid)) :=
  kernel_firewall_509 o parent b.internal (KernelBirthBoundary b) (KernelBirthUV o b) child paid
    h.parentSplit h.internalGap (kernel_birth_uv_bound o h) h.childAssembly

theorem kernel_birth_gp509 {a : Analysis} (o : KernelArithmetic a)
    (frames : Nat → KernelBirthFrame a) (mass paid : Nat → a.Scalar)
    (h : ∀ n, KernelBirthWitness o (frames n) (mass n) (mass (n+1)) (paid n)) :
    GP509Certificate o mass paid :=
  ⟨fun n => (h n).parentNonnegative, fun n => (h n).paidNonnegative,
    fun n => kernel_birth_step o (h n)⟩

end Fefferman
