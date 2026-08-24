import RandomnessExtraction.Generator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Seeded hashing

This file contains the paper's Definition 6 and Lemma 7.  The output
alphabet is `Fin M`, so its cardinality is definitionally the scalar `M`
appearing in the paper.
-/

open scoped BigOperators Classical

namespace RandomnessExtraction

/-- A finite seeded family of maps from `X` to an `M`-point output alphabet. -/
structure SeededHash (X S : Type*) [Fintype X] [Fintype S] (M : ℕ) where
  seed : FinProb S
  hash : S → X → Fin M

namespace SeededHash

variable {X S : Type*} [Fintype X] [Fintype S] {M : ℕ}

/-- Collision probability of two inputs under the seed law. -/
def collisionProbability (H : SeededHash X S M) (x x' : X) : ℝ :=
  H.seed.expect fun s ↦ if H.hash s x = H.hash s x' then 1 else 0

/-- **Definition 6 (two-universality).**  This is the exact condition in the
paper, with `Fin M` as output alphabet. -/
def paperDefinition6 (H : SeededHash X S M) : Prop :=
  ∀ ⦃x x' : X⦄, x ≠ x' → H.collisionProbability x x' ≤ (M : ℝ)⁻¹

/-- The mass in output bin `z` for a fixed seed. -/
noncomputable def binMass (H : SeededHash X S M) (ell : X → ℝ) (s : S) (z : Fin M) : ℝ :=
  ∑ x with H.hash s x = z, ell x

/-- Total input mass. -/
def totalMass (ell : X → ℝ) : ℝ := ∑ x, ell x

theorem binMass_eq_indicator (H : SeededHash X S M) (ell : X → ℝ) (s : S) (z : Fin M) :
    H.binMass ell s z = ∑ x, ell x * if H.hash s x = z then 1 else 0 := by
  classical
  simp [binMass, Finset.sum_filter]

theorem sum_binMass (H : SeededHash X S M) (ell : X → ℝ) (s : S) :
    ∑ z, H.binMass ell s z = totalMass ell := by
  classical
  simp_rw [binMass_eq_indicator]
  rw [Finset.sum_comm]
  simp [totalMass]

theorem collisionProbability_self (H : SeededHash X S M) (x : X) :
    H.collisionProbability x x = 1 := by
  simp [collisionProbability, FinProb.expect, H.seed.sum_prob]

private theorem sum_indicator_products (H : SeededHash X S M) (ell : X → ℝ)
    (s : S) (x x' : X) :
    ∑ z, (ell x * if H.hash s x = z then 1 else 0) *
        (ell x' * if H.hash s x' = z then 1 else 0) =
      ell x * ell x' * if H.hash s x = H.hash s x' then 1 else 0 := by
  classical
  by_cases h : H.hash s x = H.hash s x'
  · rw [h]
    simp
  · simp [h]

theorem sum_sq_binMass (H : SeededHash X S M) (ell : X → ℝ) (s : S) :
    ∑ z, (H.binMass ell s z) ^ 2 =
      ∑ x, ∑ x', ell x * ell x' * if H.hash s x = H.hash s x' then 1 else 0 := by
  classical
  simp_rw [binMass_eq_indicator, pow_two, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x' _
  exact sum_indicator_products H ell s x x'

private theorem centered_bin_identity (H : SeededHash X S M) (ell : X → ℝ)
    (hM : 0 < M) (s : S) :
    ∑ z, (H.binMass ell s z - totalMass ell / (M : ℝ)) ^ 2 =
      (∑ z, (H.binMass ell s z) ^ 2) - (totalMass ell) ^ 2 / (M : ℝ) := by
  classical
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hpoint (z : Fin M) :
      (H.binMass ell s z - totalMass ell / (M : ℝ)) ^ 2 =
        (H.binMass ell s z) ^ 2 -
          (2 * (totalMass ell / (M : ℝ))) * H.binMass ell s z +
          (totalMass ell / (M : ℝ)) ^ 2 := by ring
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, sum_binMass]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private theorem expected_sum_sq (H : SeededHash X S M) (ell : X → ℝ) :
    H.seed.expect (fun s ↦ ∑ z, (H.binMass ell s z) ^ 2) =
      ∑ x, ∑ x', ell x * ell x' * H.collisionProbability x x' := by
  classical
  rw [FinProb.expect]
  simp_rw [sum_sq_binMass]
  calc
    (∑ s, H.seed s * ∑ x, ∑ x',
        ell x * ell x' * if H.hash s x = H.hash s x' then 1 else 0) =
      ∑ s, ∑ x, ∑ x', H.seed s *
        (ell x * ell x' * if H.hash s x = H.hash s x' then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
    _ = ∑ x, ∑ x', ∑ s, H.seed s *
        (ell x * ell x' * if H.hash s x = H.hash s x' then 1 else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ x', ell x * ell x' * H.collisionProbability x x' := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro x' _
          rw [collisionProbability, FinProb.expect]
          calc
            (∑ s, H.seed s *
                (ell x * ell x' * if H.hash s x = H.hash s x' then 1 else 0)) =
              ∑ s, (ell x * ell x') *
                (H.seed s * if H.hash s x = H.hash s x' then 1 else 0) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  ring
            _ = ell x * ell x' *
                ∑ s, H.seed s * if H.hash s x = H.hash s x' then 1 else 0 := by
                  rw [Finset.mul_sum]

private theorem pair_collision_bound (H : SeededHash X S M) (ell : X → ℝ)
    (hell : ∀ x, 0 ≤ ell x) (hM : 0 < M) (h2 : paperDefinition6 H) (x x' : X) :
    ell x * ell x' * H.collisionProbability x x' ≤
      if x = x' then ell x ^ 2 else (M : ℝ)⁻¹ * (ell x * ell x') := by
  classical
  by_cases hxx : x = x'
  · subst x'
    simp [collisionProbability_self, pow_two]
  · rw [if_neg hxx]
    have hprod : 0 ≤ ell x * ell x' := mul_nonneg (hell x) (hell x')
    calc
      ell x * ell x' * H.collisionProbability x x' ≤
          ell x * ell x' * (M : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (h2 hxx) hprod
      _ = (M : ℝ)⁻¹ * (ell x * ell x') := by ring

private theorem sum_pair_bound (ell : X → ℝ) (M : ℕ) :
    (∑ x, ∑ x', if x = x' then ell x ^ 2 else (M : ℝ)⁻¹ * (ell x * ell x')) =
      (1 - (M : ℝ)⁻¹) * ∑ x, ell x ^ 2 +
        (M : ℝ)⁻¹ * (totalMass ell) ^ 2 := by
  classical
  have hpoint : ∀ x x' : X,
      (if x = x' then ell x ^ 2 else (M : ℝ)⁻¹ * (ell x * ell x')) =
        (M : ℝ)⁻¹ * (ell x * ell x') +
          (if x = x' then (1 - (M : ℝ)⁻¹) * ell x ^ 2 else 0) := by
    intro x x'
    by_cases h : x = x'
    · subst x'
      simp
      ring
    · simp [h]
  simp_rw [hpoint, Finset.sum_add_distrib]
  have hdouble :
      (∑ x, ∑ x', (M : ℝ)⁻¹ * (ell x * ell x')) =
        (M : ℝ)⁻¹ * (totalMass ell) ^ 2 := by
    calc
      (∑ x, ∑ x', (M : ℝ)⁻¹ * (ell x * ell x')) =
          ∑ x, (M : ℝ)⁻¹ * ∑ x', ell x * ell x' := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
      _ = (M : ℝ)⁻¹ * ∑ x, ∑ x', ell x * ell x' := by
            rw [Finset.mul_sum]
      _ = (M : ℝ)⁻¹ * ((∑ x, ell x) * ∑ x', ell x') := by
            rw [Fintype.sum_mul_sum]
      _ = (M : ℝ)⁻¹ * (totalMass ell) ^ 2 := by
            simp [totalMass, pow_two]
  have hdiag :
      (∑ x, ∑ x', if x = x' then (1 - (M : ℝ)⁻¹) * ell x ^ 2 else 0) =
        (1 - (M : ℝ)⁻¹) * ∑ x, ell x ^ 2 := by
    calc
      (∑ x, ∑ x', if x = x' then (1 - (M : ℝ)⁻¹) * ell x ^ 2 else 0) =
          ∑ x, (1 - (M : ℝ)⁻¹) * ell x ^ 2 := by
            apply Finset.sum_congr rfl
            intro x _
            simp
      _ = (1 - (M : ℝ)⁻¹) * ∑ x, ell x ^ 2 := by
            rw [Finset.mul_sum]
  rw [hdouble]
  rw [hdiag]
  ring

/-- **Lemma 7 (two-universal second moment).** -/
theorem paperLemma7 (H : SeededHash X S M) (ell : X → ℝ)
    (hell : ∀ x, 0 ≤ ell x) (hM : 0 < M) (h2 : paperDefinition6 H) :
    H.seed.expect (fun s ↦
      ∑ z, (H.binMass ell s z - totalMass ell / (M : ℝ)) ^ 2) ≤
      (1 - (M : ℝ)⁻¹) * ∑ x, ell x ^ 2 := by
  classical
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp_rw [centered_bin_identity H ell hM]
  rw [show H.seed.expect (fun s ↦
      (∑ z, (H.binMass ell s z) ^ 2) - (totalMass ell) ^ 2 / (M : ℝ)) =
      H.seed.expect (fun s ↦ ∑ z, (H.binMass ell s z) ^ 2) -
        (totalMass ell) ^ 2 / (M : ℝ) by
    simp only [FinProb.expect]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, H.seed.sum_prob, one_mul]]
  rw [expected_sum_sq]
  calc
    (∑ x, ∑ x', ell x * ell x' * H.collisionProbability x x') -
        (totalMass ell) ^ 2 / (M : ℝ) ≤
      (∑ x, ∑ x', if x = x' then ell x ^ 2
        else (M : ℝ)⁻¹ * (ell x * ell x')) - (totalMass ell) ^ 2 / (M : ℝ) := by
          gcongr with x hx x' hx'
          exact pair_collision_bound H ell hell hM h2 x x'
    _ = (1 - (M : ℝ)⁻¹) * ∑ x, ell x ^ 2 := by
      rw [sum_pair_bound]
      field_simp
      ring

end SeededHash

end RandomnessExtraction
