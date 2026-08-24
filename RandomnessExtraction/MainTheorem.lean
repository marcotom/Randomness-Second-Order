import RandomnessExtraction.FixedMain
import RandomnessExtraction.OptimizedMain

/-!
# Exact second-order operational theorem
-/

open Filter
open scoped Topology

namespace RandomnessExtraction

open ConditionalLimit OneShot

/-- **Theorem 1 (exact second-order `f`-leakage, fixed and optimized
marginals).**  The first two conjuncts are the two operational limits.  The
third says that every sequence of two-universal families attains both limits;
the fourth states the two converse lower bounds for arbitrary seeded-family
sequences. -/
theorem paperTheorem1
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L : ℝ)
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ optimalFixedLeakage f (blockSource P n) (M n)) atTop
        (nhds (gaussianProfile f (variance₁ P / totalVariance P)
          (-L / Real.sqrt (totalVariance P)))) ∧
      Tendsto (fun n ↦ optimalOptimizedLeakage f (blockSource P n) (M n)) atTop
        (nhds (f (gaussianCDF (-L / Real.sqrt (totalVariance P))))) ∧
      (∀ (N : ℕ → ℕ)
        (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n)),
        (∀ n, SeededHash.paperDefinition6 (H n)) →
        Tendsto (fun n ↦ fixedLeakage f (blockSource P n) (H n)) atTop
          (nhds (gaussianProfile f (variance₁ P / totalVariance P)
            (-L / Real.sqrt (totalVariance P)))) ∧
        Tendsto (fun n ↦ optimizedLeakage f (blockSource P n) (H n)) atTop
          (nhds (f (gaussianCDF (-L / Real.sqrt (totalVariance P)))))) ∧
      (∀ (N : ℕ → ℕ)
        (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n)),
        (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          gaussianProfile f (variance₁ P / totalVariance P)
              (-L / Real.sqrt (totalVariance P)) - ε ≤
            fixedLeakage f (blockSource P n) (H n)) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          f (gaussianCDF (-L / Real.sqrt (totalVariance P))) - ε ≤
            optimizedLeakage f (blockSource P n) (H n))) := by
  have hf := fixedOperationalLimits hBE f P hpY M hM L hV hRate
  have ho := optimizedOperationalLimits hBE f P hpY M hM L hV hRate
  refine ⟨hf.2, ho.2, ?_, ?_⟩
  · intro N H htwo
    exact ⟨(fixedFamilyOperationalLimits hBE f P hpY M hM L N H htwo
      hV hRate).1,
      (optimizedFamilyOperationalLimits hBE f P hpY M hM L N H htwo
        hV hRate).1⟩
  · intro N H
    constructor
    · intro ε hε
      have hgamma := fixedGamma_rate_tendsto hBE f P hpY M hM L hV hRate
      exact (hgamma.eventually (Ioi_mem_nhds (sub_lt_self _ hε))).mono
        (fun n hn ↦ hn.le.trans
          (fixed_family_converse f (blockSource P n) (H n) (hM n)))
    · intro ε hε
      have hgamma := optimizedGamma_rate_tendsto hBE f P hpY M hM L hV hRate
      exact (hgamma.eventually (Ioi_mem_nhds (sub_lt_self _ hε))).mono
        (fun n hn ↦ hn.le.trans
          (optimized_family_converse f (blockSource P n) (H n) (hM n)))

end RandomnessExtraction
