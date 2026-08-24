import RandomnessExtraction.OperationalAsymptotics
import RandomnessExtraction.UniversalHash
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp

/-!
# Rate and moving-threshold asymptotics

This file contains the rate normalization, moving-threshold sandwiches,
continuity error, and Gaussian-limit bridges used by the operational theorem.
-/

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

open ConditionalLimit ConditionalCapped UniformEndpoint
open OneShot LightAchievability PerspectiveAggregation

set_option maxHeartbeats 800000

/-- Equation (5), the second-order output-rate condition. -/
def SecondOrderRate {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (M : ℕ → ℕ) (L : ℝ) : Prop :=
  Tendsto (fun n ↦
    (Real.logb 2 (M n : ℝ) - n * entropy P) / Real.sqrt (n : ℝ))
    atTop (nhds L)

/-- The moving threshold parameter corresponding exactly to `M n`. -/
noncomputable def rateParameter {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (M : ℕ → ℕ) (n : ℕ) : ℝ :=
  (n * entropy P - Real.logb 2 (M n : ℝ)) /
    Real.sqrt (n * totalVariance P)

theorem rateParameter_tendsto
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (M : ℕ → ℕ) (L : ℝ)
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (rateParameter P M) atTop
      (nhds (-L / Real.sqrt (totalVariance P))) := by
  have hsqrtV : Real.sqrt (totalVariance P) ≠ 0 := (Real.sqrt_pos.2 hV).ne'
  have hlim := hRate.neg.div_const (Real.sqrt (totalVariance P))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [rateParameter, Real.sqrt_mul hnR.le]
  field_simp
  ring

theorem threshold_rateParameter
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (M : ℕ → ℕ)
    (hV : 0 < totalVariance P) {n : ℕ} (hn : 0 < n) :
    threshold P n (rateParameter P M n) = Real.logb 2 (M n : ℝ) := by
  have hnV : 0 < (n : ℝ) * totalVariance P :=
    mul_pos (by exact_mod_cast hn) hV
  have hs : Real.sqrt ((n : ℝ) * totalVariance P) ≠ 0 :=
    (Real.sqrt_pos.2 hnV).ne'
  unfold threshold rateParameter
  field_simp
  ring

theorem rateParameter_cap
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (M : ℕ → ℕ)
    (hV : 0 < totalVariance P) (hM : ∀ n, 0 < M n)
    {n : ℕ} (hn : 0 < n) :
    (M n : ℝ)⁻¹ = (2 : ℝ) ^ (-threshold P n (rateParameter P M n)) := by
  rw [threshold_rateParameter P M hV hn]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) (by exact_mod_cast hM n)]

/-- The paper's choice `τₙ=n^{1/4}`, represented as an iterated square root. -/
noncomputable def canonicalShift (n : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (n : ℝ))

theorem canonicalShift_admissible : AdmissibleShift canonicalShift := by
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hfourth : Tendsto canonicalShift atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp hsqrt
  constructor
  · exact hfourth
  · have hinv : Tendsto (fun n : ℕ ↦ (canonicalShift n)⁻¹)
        atTop (nhds 0) := tendsto_inv_atTop_zero.comp hfourth
    apply hinv.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hsqrtPos : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hfourthPos : 0 < canonicalShift n :=
      Real.sqrt_pos.2 hsqrtPos
    unfold canonicalShift
    have hsquare : Real.sqrt (Real.sqrt (n : ℝ)) *
        Real.sqrt (Real.sqrt (n : ℝ)) = Real.sqrt (n : ℝ) :=
      Real.mul_self_sqrt hsqrtPos.le
    field_simp
    nlinarith

theorem canonicalShift_eventually_pos :
    ∀ᶠ n in atTop, 0 < canonicalShift n := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hn))

/-- Uniform continuity makes the explicit modulus in Lemma 8 vanish. -/
theorem modulus_tendsto_zero (f : AdmissibleGenerator) :
    Tendsto (modulus f) (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hUC : UniformContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ, hδ, hclose⟩ := (Metric.uniformContinuousOn_iff.1 hUC)
    (ε / 2) (by linarith)
  have hball : Metric.ball (0 : ℝ) δ ∈ nhdsWithin 0 (Set.Ici 0) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ)
  filter_upwards [self_mem_nhdsWithin, hball] with η hη0 hηball
  have hη0' : 0 ≤ η := hη0
  have hηδ : η < δ := by
    rw [Metric.mem_ball, Real.dist_eq] at hηball
    simpa [abs_of_nonneg hη0'] using hηball
  have hupper : modulus f η ≤ ε / 2 := by
    apply csSup_le
    · exact ⟨0, 0, ⟨le_rfl, zero_le_one⟩, 0,
        ⟨le_rfl, zero_le_one⟩, by simpa using hη0', by simp⟩
    · rintro r ⟨a, ha, b, hb, hab, rfl⟩
      have hd : dist a b < δ := by
        rw [Real.dist_eq]
        linarith
      exact (hclose a ha b hb hd).le
  have hlower := modulus_nonneg f hη0'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlower]
  linarith

theorem extractionError_tendsto_zero (f : AdmissibleGenerator) :
    Tendsto (fun n ↦
      modulus f ((2 : ℝ) ^ (-canonicalShift n / 4)) +
        f 0 * (2 : ℝ) ^ (-canonicalShift n / 4))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun n ↦ (2 : ℝ) ^ (-canonicalShift n / 4))
      atTop (nhds 0) := by
    have hneg : Tendsto (fun n ↦ -canonicalShift n / 4) atTop atBot := by
      exact (tendsto_neg_atTop_atBot.comp canonicalShift_admissible.1).atBot_div_const
        (by norm_num : (0 : ℝ) < 4)
    exact (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp hneg
  have hnonneg : ∀ n, 0 ≤ (2 : ℝ) ^ (-canonicalShift n / 4) :=
    fun n ↦ Real.rpow_nonneg (by norm_num) _
  have hmod := (modulus_tendsto_zero f).comp
    (tendsto_nhdsWithin_iff.2 ⟨hpow, Eventually.of_forall hnonneg⟩)
  simpa using hmod.add (tendsto_const_nhds.mul hpow)

theorem finiteSource_nonempty_left
    {X Y : Type} [Fintype X] [Fintype Y] (P : FiniteSource X Y) :
    Nonempty X := by
  let y := Classical.choice (support_nonempty P.marginal)
  let x := Classical.choice (support_nonempty (P.conditional y.1))
  exact ⟨x.1⟩

theorem varianceRatio_mem_unit
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (hV : 0 < totalVariance P) :
    variance₁ P / totalVariance P ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (variance₁_nonneg P) hV.le
  · rw [div_le_one hV]
    unfold totalVariance
    linarith [variance₂_nonneg P]

theorem endpointShiftedTailAverage_antitone
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (n : ℕ) (shift : ℝ) :
    Antitone (fun x ↦ endpointShiftedTailAverage f P n x shift) := by
  intro x₁ x₂ hx
  unfold endpointShiftedTailAverage
  apply (P.marginal.iid n).expect_mono
  intro y
  apply f.antitoneOn_nonneg
  · exact (FinProb.event_nonneg _ _)
  · exact (FinProb.event_nonneg _ _)
  · apply ConditionalLimit.finProb_event_mono
    intro z hz
    change threshold P n x₁ + shift ≤ blockInformation P z y at hz
    change threshold P n x₂ + shift ≤ blockInformation P z y
    apply le_trans _ hz
    unfold threshold
    gcongr

theorem fUnconditionalTail_antitone
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (n : ℕ) (shift : ℝ) :
    Antitone (fun x ↦ f (unconditionalTail P n x shift)) := by
  intro x₁ x₂ hx
  apply f.antitoneOn_nonneg
  · unfold unconditionalTail
    exact (P.marginal.iid n).expect_nonneg fun y ↦
      FinProb.event_nonneg _ _
  · unfold unconditionalTail
    exact (P.marginal.iid n).expect_nonneg fun y ↦
      FinProb.event_nonneg _ _
  · unfold unconditionalTail
    apply (P.marginal.iid n).expect_mono
    intro y
    apply ConditionalLimit.finProb_event_mono
    intro z hz
    change threshold P n x₁ + shift ≤ blockInformation P z y at hz
    change threshold P n x₂ + shift ≤ blockInformation P z y
    apply le_trans _ hz
    unfold threshold
    gcongr

theorem fixedGamma_rate_tendsto
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L : ℝ)
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ fixedGamma f (blockSource P n) (M n)) atTop
      (nhds (gaussianProfile f (variance₁ P / totalVariance P)
        (-L / Real.sqrt (totalVariance P)))) := by
  let u := rateParameter P M
  let g := gaussianProfile f (variance₁ P / totalVariance P)
  have hu := rateParameter_tendsto P M L hV hRate
  have hr := varianceRatio_mem_unit P hV
  have hmove : Tendsto (fun n ↦ endpointCappedAverage f P n (u n)) atTop
      (nhds (g (-L / Real.sqrt (totalVariance P)))) := by
    apply tendsto_moving_of_antitone _ g u _
    · exact fun n ↦ endpointCappedAverage_antitone f P n
    · intro z
      exact (paperProposition17 hBE f P hpY hV z).1
    · exact (continuous_gaussianProfile f hr.1 hr.2).continuousAt
    · exact hu
  apply hmove.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (fixedGamma_eq_endpointCappedAverage f P n (M n) (u n)
    (hM n) (rateParameter_cap P M hV hM hn)).symm

theorem optimizedGamma_rate_tendsto
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L : ℝ)
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ optimizedGamma f (blockSource P n) (M n)) atTop
      (nhds (f (gaussianCDF (-L / Real.sqrt (totalVariance P))))) := by
  let u := rateParameter P M
  let g : ℝ → ℝ := fun x ↦ f (gaussianCDF x)
  have hu := rateParameter_tendsto P M L hV hRate
  have hmove : Tendsto (fun n ↦ optimizedCappedProfileValue f P n (u n)) atTop
      (nhds (g (-L / Real.sqrt (totalVariance P)))) := by
    apply tendsto_moving_of_antitone _ g u _
    · exact fun n ↦ optimizedCappedProfileValue_antitone f P n
    · intro z
      exact (paperProposition18 hBE f P hpY hV z).1
    · exact f.continuous.continuousAt.comp
        continuous_gaussianCDF.continuousAt
    · exact hu
  apply hmove.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (optimizedGamma_eq_optimizedCappedProfileValue f P n (M n) (u n)
    (hM n) (rateParameter_cap P M hV hM hn)).symm

theorem shiftedTailAverage_rate_tendsto
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (L : ℝ)
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ endpointShiftedTailAverage f P n
      (rateParameter P M n) (canonicalShift n)) atTop
      (nhds (gaussianProfile f (variance₁ P / totalVariance P)
        (-L / Real.sqrt (totalVariance P)))) := by
  let u := rateParameter P M
  let g := gaussianProfile f (variance₁ P / totalVariance P)
  have hr := varianceRatio_mem_unit P hV
  have hm := tendsto_moving_of_antitone
    (fun n x ↦ endpointShiftedTailAverage f P n x (canonicalShift n))
    g u (-L / Real.sqrt (totalVariance P))
    (fun n ↦ endpointShiftedTailAverage_antitone f P n (canonicalShift n))
    (fun z ↦ (paperProposition17 hBE f P hpY hV z).2
      canonicalShift canonicalShift_admissible)
    (continuous_gaussianProfile f hr.1 hr.2).continuousAt
    (rateParameter_tendsto P M L hV hRate)
  simpa [u, g] using hm

theorem fUnconditionalTail_rate_tendsto
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (L : ℝ)
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ f (unconditionalTail P n
      (rateParameter P M n) (canonicalShift n))) atTop
      (nhds (f (gaussianCDF (-L / Real.sqrt (totalVariance P))))) := by
  let u := rateParameter P M
  let g : ℝ → ℝ := fun x ↦ f (gaussianCDF x)
  have hm := tendsto_moving_of_antitone
    (fun n x ↦ f (unconditionalTail P n x (canonicalShift n)))
    g u (-L / Real.sqrt (totalVariance P))
    (fun n ↦ fUnconditionalTail_antitone f P n (canonicalShift n))
    (fun z ↦ f.continuous.continuousAt.tendsto.comp
      ((paperProposition18 hBE f P hpY hV z).2
        canonicalShift canonicalShift_admissible))
    (f.continuous.continuousAt.comp continuous_gaussianCDF.continuousAt)
    (rateParameter_tendsto P M L hV hRate)
  simpa [u, g] using hm

theorem unconditionalTail_rate_tendsto
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (L : ℝ)
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ unconditionalTail P n
      (rateParameter P M n) (canonicalShift n)) atTop
      (nhds (gaussianCDF (-L / Real.sqrt (totalVariance P)))) := by
  let u := rateParameter P M
  have hm := tendsto_moving_of_antitone
    (fun n x ↦ -(unconditionalTail P n x (canonicalShift n)))
    (fun x ↦ -(gaussianCDF x)) u
    (-L / Real.sqrt (totalVariance P)) (by
      intro n x₁ x₂ hx
      simp only [neg_le_neg_iff]
      unfold unconditionalTail
      apply (P.marginal.iid n).expect_mono
      intro y
      apply ConditionalLimit.finProb_event_mono
      intro z hz
      change threshold P n x₁ + canonicalShift n ≤ blockInformation P z y at hz
      change threshold P n x₂ + canonicalShift n ≤ blockInformation P z y
      apply le_trans _ hz
      unfold threshold
      gcongr)
    (fun z ↦ by
      simpa using ((paperProposition18 hBE f P hpY hV z).2
        canonicalShift canonicalShift_admissible).neg)
    continuous_gaussianCDF.continuousAt.neg
    (rateParameter_tendsto P M L hV hRate)
  have := hm.neg
  simpa [u] using this

end RandomnessExtraction
