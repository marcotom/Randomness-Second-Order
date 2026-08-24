import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic

/-!
# Finite probability laws

The paper works throughout with finite alphabets.  This file provides a
real-valued finite probability-vector interface.  Keeping probabilities in
`ℝ` makes the finite-sum identities in the one-shot arguments transparent;
measure-theoretic probability is used later only for weak convergence and
Gaussian limits.
-/

open scoped BigOperators Classical

namespace RandomnessExtraction

/-- A probability law on a finite type, represented by its real-valued mass
function. -/
structure FinProb (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  sum_prob : ∑ x, prob x = 1

namespace FinProb

variable {α β γ : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]

instance : CoeFun (FinProb α) (fun _ ↦ α → ℝ) := ⟨FinProb.prob⟩

@[simp]
theorem sum_apply (p : FinProb α) : ∑ x, p x = 1 := p.sum_prob

theorem apply_nonneg (p : FinProb α) (x : α) : 0 ≤ p x := p.nonneg x

theorem apply_le_one (p : FinProb α) (x : α) : p x ≤ 1 := by
  classical
  calc
    p x ≤ ∑ y, p y := Finset.single_le_sum (fun y _ ↦ p.nonneg y) (Finset.mem_univ x)
    _ = 1 := p.sum_prob

theorem exists_pos (p : FinProb α) : ∃ x, 0 < p x := by
  by_contra h
  have hnonpos : ∀ x, p x ≤ 0 := fun x ↦ le_of_not_gt (fun hx ↦ h ⟨x, hx⟩)
  have hz : ∀ x, p x = 0 := fun x ↦ le_antisymm (hnonpos x) (p.nonneg x)
  have : (∑ x, p x) = 0 := by simp [hz]
  rw [p.sum_prob] at this
  exact one_ne_zero this

/-- The uniform probability law on a nonempty finite type `Fin n`. -/
noncomputable def uniformFin (n : ℕ) (hn : 0 < n) : FinProb (Fin n) where
  prob _ := (n : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg n)
  sum_prob := by
    simp [Nat.cast_ne_zero.mpr hn.ne']

@[simp]
theorem uniformFin_apply (n : ℕ) (hn : 0 < n) (i : Fin n) :
    uniformFin n hn i = (n : ℝ)⁻¹ := rfl

/-- Expectation of a real-valued function under a finite probability law. -/
def expect (p : FinProb α) (u : α → ℝ) : ℝ := ∑ x, p x * u x

@[simp]
theorem expect_const (p : FinProb α) (c : ℝ) : p.expect (fun _ ↦ c) = c := by
  simp [expect, ← Finset.sum_mul, p.sum_prob]

theorem expect_nonneg (p : FinProb α) {u : α → ℝ} (hu : ∀ x, 0 ≤ u x) :
    0 ≤ p.expect u := by
  classical
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (p.nonneg x) (hu x)

theorem expect_mono (p : FinProb α) {u v : α → ℝ} (huv : ∀ x, u x ≤ v x) :
    p.expect u ≤ p.expect v := by
  classical
  exact Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (huv x) (p.nonneg x)

/-- The product of two finite probability laws. -/
def prod (p : FinProb α) (q : FinProb β) : FinProb (α × β) where
  prob xy := p xy.1 * q xy.2
  nonneg xy := mul_nonneg (p.nonneg xy.1) (q.nonneg xy.2)
  sum_prob := by
    classical
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, q.sum_prob, mul_one]
    exact p.sum_prob

@[simp]
theorem prod_apply (p : FinProb α) (q : FinProb β) (x : α) (y : β) :
    p.prod q (x, y) = p x * q y := rfl

/-- The `n`-fold i.i.d. product law. -/
def iid (p : FinProb α) (n : ℕ) : FinProb (Fin n → α) where
  prob x := ∏ i, p (x i)
  nonneg x := Finset.prod_nonneg fun i _ ↦ p.nonneg (x i)
  sum_prob := by
    classical
    rw [← Fintype.prod_sum]
    simp [p.sum_prob]

@[simp]
theorem iid_apply (p : FinProb α) (n : ℕ) (x : Fin n → α) :
    p.iid n x = ∏ i, p (x i) := rfl

/-- A probability law pushed forward by a function. -/
noncomputable def map (p : FinProb α) (g : α → β) : FinProb β where
  prob y := ∑ x with g x = y, p x
  nonneg y := Finset.sum_nonneg fun x _ ↦ p.nonneg x
  sum_prob := by
    classical
    simpa [Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ g p] using p.sum_prob

@[simp]
theorem map_apply (p : FinProb α) (g : α → β) (y : β) :
    p.map g y = ∑ x with g x = y, p x := rfl

/-- Probability of a decidable event. -/
noncomputable def event (p : FinProb α) (A : Set α) : ℝ := ∑ x with x ∈ A, p x

theorem event_nonneg (p : FinProb α) (A : Set α) : 0 ≤ p.event A := by
  classical
  exact Finset.sum_nonneg fun x _ ↦ p.nonneg x

theorem event_le_one (p : FinProb α) (A : Set α) : p.event A ≤ 1 := by
  classical
  calc
    p.event A ≤ ∑ x, p x := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun x _ _ ↦ p.nonneg x)
    _ = 1 := p.sum_prob

end FinProb

/-- A finite joint law, presented as a marginal on `Y` and a conditional law
on `X` for each `y`.  Conditional laws at marginal-zero points are harmless. -/
structure FiniteSource (X Y : Type*) [Fintype X] [Fintype Y] where
  marginal : FinProb Y
  conditional : Y → FinProb X

namespace FiniteSource

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The induced joint law. -/
def joint (P : FiniteSource X Y) : FinProb (X × Y) where
  prob xy := P.marginal xy.2 * P.conditional xy.2 xy.1
  nonneg xy := mul_nonneg (P.marginal.nonneg xy.2) ((P.conditional xy.2).nonneg xy.1)
  sum_prob := by
    classical
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (P.conditional _).sum_prob, mul_one]
    exact P.marginal.sum_prob

@[simp]
theorem joint_apply (P : FiniteSource X Y) (x : X) (y : Y) :
    P.joint (x, y) = P.marginal y * P.conditional y x := rfl

end FiniteSource

end RandomnessExtraction
