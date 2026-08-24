import RandomnessExtraction.HashSequence

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

open ConditionalLimit ConditionalCapped UniformEndpoint
open OneShot LightAchievability

set_option maxHeartbeats 800000

/-- Fixed-reference half of Theorem 1 for an arbitrary sequence of
two-universal seeded families, together with the operational infimum. -/
theorem fixedFamilyOperationalLimits
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L : ℝ)
    (N : ℕ → ℕ) (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n))
    (htwo : ∀ n, SeededHash.paperDefinition6 (H n))
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ fixedLeakage f (blockSource P n) (H n)) atTop
      (nhds (gaussianProfile f (variance₁ P / totalVariance P)
        (-L / Real.sqrt (totalVariance P)))) ∧
    Tendsto (fun n ↦ optimalFixedLeakage f (blockSource P n) (M n)) atTop
      (nhds (gaussianProfile f (variance₁ P / totalVariance P)
        (-L / Real.sqrt (totalVariance P)))) := by
  let target := gaussianProfile f (variance₁ P / totalVariance P)
    (-L / Real.sqrt (totalVariance P))
  let err : ℕ → ℝ := fun n ↦
    modulus f ((2 : ℝ) ^ (-canonicalShift n / 4)) +
      f 0 * (2 : ℝ) ^ (-canonicalShift n / 4)
  let upper : ℕ → ℝ := fun n ↦
    endpointShiftedTailAverage f P n (rateParameter P M n) (canonicalShift n) +
      err n
  have herr : Tendsto err atTop (nhds 0) := by
    simpa [err] using extractionError_tendsto_zero f
  have hupper : Tendsto upper atTop (nhds target) := by
    simpa [upper, target] using
      (shiftedTailAverage_rate_tendsto hBE f P hpY M L hV hRate).add herr
  have hdirect : ∀ᶠ n in atTop,
      fixedLeakage f (blockSource P n) (H n) ≤ upper n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      canonicalShift_eventually_pos] with n hn hshift
    have hcap := rateParameter_cap P M hV hM hn
    have h8 := (paperLemma8 f (blockSource P n) (H n) (hM n)
      (htwo n) (canonicalShift n) hshift).1
    have hid :
        (blockSource P n).marginal.expect (fun y ↦
          f (lightMass ((blockSource P n).conditional y) (M n)
            (canonicalShift n))) =
          endpointShiftedTailAverage f P n (rateParameter P M n)
            (canonicalShift n) := by
      unfold endpointShiftedTailAverage
      apply congrArg (P.marginal.iid n).expect
      funext y
      simp only [blockSource_conditional]
      rw [lightMass_eq_shiftedConditionalTail P y (M n)
        (rateParameter P M n) (canonicalShift n) hcap]
    rw [hid] at h8
    simpa [upper, err, add_assoc] using h8
  have hgamma := fixedGamma_rate_tendsto hBE f P hpY M hM L hV hRate
  have hhash : Tendsto (fun n ↦ fixedLeakage f (blockSource P n) (H n))
      atTop (nhds target) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hgamma hupper
    · exact Eventually.of_forall fun n ↦
        fixed_family_converse f (blockSource P n) (H n) (hM n)
    · exact hdirect
  have hoptimal : Tendsto
      (fun n ↦ optimalFixedLeakage f (blockSource P n) (M n))
      atTop (nhds target) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hgamma hhash
    · exact Eventually.of_forall fun n ↦
        optimal_fixed_converse f (blockSource P n) (M n) (hM n)
    · exact Eventually.of_forall fun n ↦
        optimalFixedLeakage_le_family f (blockSource P n) (H n) (hM n)
  constructor
  · simpa [target] using hhash
  · simpa [target] using hoptimal

/-- Fixed-reference operational limits for the canonical all-functions
two-universal family. -/
theorem fixedOperationalLimits
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L : ℝ)
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ fixedLeakage f (blockSource P n)
        (sourceBlockUniversalHash P M hM n)) atTop
      (nhds (gaussianProfile f (variance₁ P / totalVariance P)
        (-L / Real.sqrt (totalVariance P)))) ∧
    Tendsto (fun n ↦ optimalFixedLeakage f (blockSource P n) (M n)) atTop
      (nhds (gaussianProfile f (variance₁ P / totalVariance P)
        (-L / Real.sqrt (totalVariance P)))) := by
  exact fixedFamilyOperationalLimits hBE f P hpY M hM L
    (sourceUniversalSeedCount P M hM)
    (fun n ↦ sourceBlockUniversalHash P M hM n)
    (fun n ↦ sourceBlockUniversalHash_twoUniversal P M hM n) hV hRate

end RandomnessExtraction
