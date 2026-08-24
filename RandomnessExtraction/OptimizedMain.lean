import RandomnessExtraction.HashSequence

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

open ConditionalLimit ConditionalCapped UniformEndpoint
open OneShot LightAchievability

set_option maxHeartbeats 800000

/-- Optimized-reference half of Theorem 1 for an arbitrary sequence of
two-universal seeded families, together with the operational infimum. -/
theorem optimizedFamilyOperationalLimits
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L : ℝ)
    (N : ℕ → ℕ) (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n))
    (htwo : ∀ n, SeededHash.paperDefinition6 (H n))
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ optimizedLeakage f (blockSource P n) (H n)) atTop
      (nhds (f (gaussianCDF (-L / Real.sqrt (totalVariance P))))) ∧
    Tendsto (fun n ↦ optimalOptimizedLeakage f (blockSource P n) (M n)) atTop
      (nhds (f (gaussianCDF (-L / Real.sqrt (totalVariance P))))) := by
  let target := f (gaussianCDF (-L / Real.sqrt (totalVariance P)))
  let err : ℕ → ℝ := fun n ↦
    modulus f ((2 : ℝ) ^ (-canonicalShift n / 4)) +
      f 0 * (2 : ℝ) ^ (-canonicalShift n / 4)
  let upper : ℕ → ℝ := fun n ↦
    f (unconditionalTail P n (rateParameter P M n) (canonicalShift n)) + err n
  have herr : Tendsto err atTop (nhds 0) := by
    simpa [err] using extractionError_tendsto_zero f
  have hupper : Tendsto upper atTop (nhds target) := by
    simpa [upper, target] using
      (fUnconditionalTail_rate_tendsto hBE f P hpY M L hV hRate).add herr
  have htail := unconditionalTail_rate_tendsto hBE f P hpY M L hV hRate
  have htailPos : ∀ᶠ n in atTop,
      0 < unconditionalTail P n (rateParameter P M n) (canonicalShift n) :=
    htail.eventually (Ioi_mem_nhds (gaussianCDF_pos _))
  have hdirect : ∀ᶠ n in atTop,
      optimizedLeakage f (blockSource P n) (H n) ≤ upper n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      canonicalShift_eventually_pos, htailPos] with n hn hshift hbarTail
    have hcap := rateParameter_cap P M hV hM hn
    have havg : averageLightMass (blockSource P n) (M n) (canonicalShift n) =
        unconditionalTail P n (rateParameter P M n) (canonicalShift n) :=
      averageLightMass_eq_unconditionalTail P n (M n)
        (rateParameter P M n) (canonicalShift n) hcap
    have hbar : 0 < averageLightMass (blockSource P n) (M n)
        (canonicalShift n) := by rwa [havg]
    let R := tiltedReference (blockSource P n) (H n) (canonicalShift n) hbar
    have h8 := (paperLemma8 f (blockSource P n) (H n) (hM n)
      (htwo n) (canonicalShift n) hshift).2 hbar
    calc
      optimizedLeakage f (blockSource P n) (H n) ≤
          referenceLeakage f (blockSource P n) (H n) R :=
        optimizedLeakage_le_reference f (blockSource P n) (H n) (hM n) R
      _ ≤ f (averageLightMass (blockSource P n) (M n) (canonicalShift n)) +
          modulus f ((2 : ℝ) ^ (-canonicalShift n / 4)) +
            f 0 * (2 : ℝ) ^ (-canonicalShift n / 4) := h8
      _ = upper n := by
        rw [havg]
        simp [upper, err, add_assoc]
  have hgamma := optimizedGamma_rate_tendsto hBE f P hpY M hM L hV hRate
  have hhash : Tendsto
      (fun n ↦ optimizedLeakage f (blockSource P n) (H n)) atTop
      (nhds target) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hgamma hupper
    · exact Eventually.of_forall fun n ↦
        optimized_family_converse f (blockSource P n) (H n) (hM n)
    · exact hdirect
  have hoptimal : Tendsto
      (fun n ↦ optimalOptimizedLeakage f (blockSource P n) (M n))
      atTop (nhds target) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hgamma hhash
    · exact Eventually.of_forall fun n ↦
        optimal_optimized_converse f (blockSource P n) (M n) (hM n)
    · exact Eventually.of_forall fun n ↦
        optimalOptimizedLeakage_le_family f (blockSource P n) (H n) (hM n)
  constructor
  · simpa [target] using hhash
  · simpa [target] using hoptimal

/-- Optimized-reference operational limits for the canonical all-functions
two-universal family. -/
theorem optimizedOperationalLimits
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L : ℝ)
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ optimizedLeakage f (blockSource P n)
        (sourceBlockUniversalHash P M hM n)) atTop
      (nhds (f (gaussianCDF (-L / Real.sqrt (totalVariance P))))) ∧
    Tendsto (fun n ↦ optimalOptimizedLeakage f (blockSource P n) (M n)) atTop
      (nhds (f (gaussianCDF (-L / Real.sqrt (totalVariance P))))) := by
  exact optimizedFamilyOperationalLimits hBE f P hpY M hM L
    (sourceUniversalSeedCount P M hM)
    (fun n ↦ sourceBlockUniversalHash P M hM n)
    (fun n ↦ sourceBlockUniversalHash_twoUniversal P M hM n) hV hRate

end RandomnessExtraction
