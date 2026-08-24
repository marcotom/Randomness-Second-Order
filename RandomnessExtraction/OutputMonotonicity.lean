import RandomnessExtraction.OperationalAsymptotics
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Monotonicity under discarding one output bit

This file proves the data-processing step used in the fixed-leakage
corollaries.  A hash with `2M` outputs is reindexed as `Fin M × Fin 2` and
the second coordinate is discarded.  The proof is the finite perspective
inequality, so it applies to both choices of reference marginal.
-/

open scoped BigOperators Classical

namespace RandomnessExtraction

open OneShot

set_option maxHeartbeats 800000

variable {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S]

noncomputable def discardOutputBit {M : ℕ}
    (H : SeededHash X S (M * 2)) : SeededHash X S M where
  seed := H.seed
  hash s x := (finProdFinEquiv.symm (H.hash s x)).1

theorem outputMass_discardOutputBit {M : ℕ}
    (H : SeededHash X S (M * 2)) (p : FinProb X) (s : S) (z : Fin M) :
    outputMass (discardOutputBit H) p s z =
      ∑ b : Fin 2, outputMass H p s (finProdFinEquiv (z, b)) := by
  classical
  unfold outputMass
  simp_rw [SeededHash.binMass_eq_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  let w := finProdFinEquiv.symm (H.hash s x)
  rcases hwval : w with ⟨w₁, w₂⟩
  have hw : finProdFinEquiv w = H.hash s x :=
    finProdFinEquiv.apply_symm_apply _
  simp only [discardOutputBit, ← hw, Equiv.symm_apply_apply,
    Equiv.apply_eq_iff_eq]
  rw [hwval]
  by_cases hz : w₁ = z
  · subst z
    fin_cases w₂ <;> simp
  · simp [hz]

private theorem perspective_uniform {M : ℕ} (hM : 0 < M)
    (f : AdmissibleGenerator) (p : ℝ) :
    perspective f p (M : ℝ)⁻¹ = (M : ℝ)⁻¹ * f ((M : ℝ) * p) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  rw [perspective_of_pos f (inv_pos.mpr hMr)]
  congr 1
  field_simp [hMr.ne']

private theorem two_uniform_sum {M : ℕ} (hM : 0 < M) :
    (∑ _b : Fin 2, ((M * 2 : ℕ) : ℝ)⁻¹) = (M : ℝ)⁻¹ := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp [Nat.cast_mul, hMr]

private theorem sum_prod_fin_two {M : ℕ} (u : Fin (M * 2) → ℝ) :
    (∑ z : Fin M, ∑ b : Fin 2, u (finProdFinEquiv (z, b))) = ∑ w, u w := by
  calc
    (∑ z : Fin M, ∑ b : Fin 2, u (finProdFinEquiv (z, b))) =
        ∑ p : Fin M × Fin 2, u (finProdFinEquiv p) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ w, u w := Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)

theorem fixedLeakage_discardOutputBit_le {M : ℕ} (hM : 0 < M)
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (H : SeededHash X S (M * 2)) :
    fixedLeakage f P (discardOutputBit H) ≤ fixedLeakage f P H := by
  unfold fixedLeakage
  apply H.seed.expect_mono
  intro s
  apply P.marginal.expect_mono
  intro y
  have h2M : 0 < M * 2 := Nat.mul_pos hM (by omega)
  calc
    (∑ z : Fin M, (M : ℝ)⁻¹ *
        f ((M : ℝ) * outputMass (discardOutputBit H) (P.conditional y) s z)) =
        ∑ z : Fin M, perspective f
          (outputMass (discardOutputBit H) (P.conditional y) s z) (M : ℝ)⁻¹ := by
            apply Finset.sum_congr rfl
            intro z _
            rw [perspective_uniform hM]
    _ ≤ ∑ z : Fin M, ∑ b : Fin 2, perspective f
        (outputMass H (P.conditional y) s (finProdFinEquiv (z, b)))
        (((M * 2 : ℕ) : ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro z _
          rw [outputMass_discardOutputBit, ← two_uniform_sum hM]
          exact perspective_sum_le f _ _
            (fun b => Finset.sum_nonneg fun _ _ => (P.conditional y).nonneg _)
            (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = ∑ w : Fin (M * 2), perspective f
        (outputMass H (P.conditional y) s w) (((M * 2 : ℕ) : ℝ)⁻¹) :=
          sum_prod_fin_two (M := M) (fun w => perspective f
            (outputMass H (P.conditional y) s w) (((M * 2 : ℕ) : ℝ)⁻¹))
    _ = ∑ w : Fin (M * 2), (((M * 2 : ℕ) : ℝ)⁻¹) *
        f (((M * 2 : ℕ) : ℝ) * outputMass H (P.conditional y) s w) := by
          apply Finset.sum_congr rfl
          intro w _
          rw [perspective_uniform h2M]

theorem referenceLeakage_discardOutputBit_le {M : ℕ} (hM : 0 < M)
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (H : SeededHash X S (M * 2)) (R : FinProb (Y × S)) :
    referenceLeakage f P (discardOutputBit H) R ≤ referenceLeakage f P H R := by
  unfold referenceLeakage
  apply Finset.sum_le_sum
  intro y _
  apply Finset.sum_le_sum
  intro s _
  have h2M : 0 < M * 2 := Nat.mul_pos hM (by omega)
  calc
    (∑ z : Fin M, perspective f
      (P.marginal y * H.seed s *
        outputMass (discardOutputBit H) (P.conditional y) s z)
      ((M : ℝ)⁻¹ * R (y, s))) =
        ∑ z : Fin M, perspective f
          (∑ b : Fin 2, P.marginal y * H.seed s *
            outputMass H (P.conditional y) s (finProdFinEquiv (z, b)))
          (∑ _b : Fin 2, (((M * 2 : ℕ) : ℝ)⁻¹ * R (y, s))) := by
            apply Finset.sum_congr rfl
            intro z _
            congr 1
            · rw [outputMass_discardOutputBit, Finset.mul_sum]
            · rw [← Finset.sum_mul, two_uniform_sum hM]
    _ ≤ ∑ z : Fin M, ∑ b : Fin 2, perspective f
        (P.marginal y * H.seed s *
          outputMass H (P.conditional y) s (finProdFinEquiv (z, b)))
        ((((M * 2 : ℕ) : ℝ)⁻¹) * R (y, s)) := by
          apply Finset.sum_le_sum
          intro z _
          exact perspective_sum_le f _ _
            (fun b => mul_nonneg
              (mul_nonneg (P.marginal.nonneg _) (H.seed.nonneg _))
              (Finset.sum_nonneg fun _ _ => (P.conditional _).nonneg _))
            (fun _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
              (R.nonneg _))
    _ = ∑ w : Fin (M * 2), perspective f
        (P.marginal y * H.seed s * outputMass H (P.conditional y) s w)
        ((((M * 2 : ℕ) : ℝ)⁻¹) * R (y, s)) := by
          exact sum_prod_fin_two (M := M) (fun w => perspective f
            (P.marginal y * H.seed s * outputMass H (P.conditional y) s w)
            ((((M * 2 : ℕ) : ℝ)⁻¹) * R (y, s)))

theorem optimizedLeakage_discardOutputBit_le {M : ℕ} (hM : 0 < M)
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (H : SeededHash X S (M * 2)) :
    optimizedLeakage f P (discardOutputBit H) ≤ optimizedLeakage f P H := by
  unfold optimizedLeakage
  apply le_csInf
  · let R₀ := P.marginal.prod H.seed
    exact ⟨referenceLeakage f P H R₀, R₀, rfl⟩
  · rintro v ⟨R, rfl⟩
    calc
      sInf {u : ℝ | ∃ Q, u = referenceLeakage f P (discardOutputBit H) Q} ≤
          referenceLeakage f P (discardOutputBit H) R := by
            apply csInf_le
            · exact ⟨0, by
                rintro u ⟨Q, rfl⟩
                exact referenceLeakage_nonneg f P (discardOutputBit H) hM Q⟩
            · exact ⟨R, rfl⟩
      _ ≤ referenceLeakage f P H R :=
        referenceLeakage_discardOutputBit_le hM f P H R

theorem optimalFixedLeakage_pow_two_monotone
    (f : AdmissibleGenerator) (P : FiniteSource X Y) (ell : ℕ) :
    optimalFixedLeakage f P (2 ^ ell) ≤
      optimalFixedLeakage f P (2 ^ (ell + 1)) := by
  rw [pow_succ]
  unfold optimalFixedLeakage
  apply le_csInf
  · let H₀ : SeededHash X (Fin 1) (2 ^ ell * 2) :=
      { seed := FinProb.uniformFin 1 (by omega)
        hash := fun _ _ => ⟨0, Nat.mul_pos (pow_pos (by omega) _) (by omega)⟩ }
    exact ⟨fixedLeakage f P H₀, 1, H₀, rfl⟩
  · rintro v ⟨N, H, rfl⟩
    calc
      sInf {u : ℝ | ∃ K, ∃ G : SeededHash X (Fin K) (2 ^ ell),
          u = fixedLeakage f P G} ≤
          fixedLeakage f P (discardOutputBit H) := by
            apply csInf_le
            · exact ⟨0, by
                rintro u ⟨K, G, rfl⟩
                exact fixedLeakage_nonneg f P G (pow_pos (by omega) _)⟩
            · exact ⟨N, discardOutputBit H, rfl⟩
      _ ≤ fixedLeakage f P H :=
        fixedLeakage_discardOutputBit_le (pow_pos (by omega) ell) f P H

theorem optimalOptimizedLeakage_pow_two_monotone
    (f : AdmissibleGenerator) (P : FiniteSource X Y) (ell : ℕ) :
    optimalOptimizedLeakage f P (2 ^ ell) ≤
      optimalOptimizedLeakage f P (2 ^ (ell + 1)) := by
  rw [pow_succ]
  unfold optimalOptimizedLeakage
  apply le_csInf
  · let H₀ : SeededHash X (Fin 1) (2 ^ ell * 2) :=
      { seed := FinProb.uniformFin 1 (by omega)
        hash := fun _ _ => ⟨0, Nat.mul_pos (pow_pos (by omega) _) (by omega)⟩ }
    exact ⟨optimizedLeakage f P H₀, 1, H₀, rfl⟩
  · rintro v ⟨N, H, rfl⟩
    calc
      sInf {u : ℝ | ∃ K, ∃ G : SeededHash X (Fin K) (2 ^ ell),
          u = optimizedLeakage f P G} ≤
          optimizedLeakage f P (discardOutputBit H) := by
            apply csInf_le
            · exact ⟨0, by
                rintro u ⟨K, G, rfl⟩
                exact optimizedLeakage_nonneg f P G (pow_pos (by omega) _)⟩
            · exact ⟨N, discardOutputBit H, rfl⟩
      _ ≤ optimizedLeakage f P H :=
        optimizedLeakage_discardOutputBit_le (pow_pos (by omega) ell) f P H

end RandomnessExtraction
