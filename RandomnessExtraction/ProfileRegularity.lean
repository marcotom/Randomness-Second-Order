import RandomnessExtraction.GaussianProfile
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Regularity of the Gaussian profile

This file formalizes Lemma 19 of the paper.  In particular, the endpoint
`r = 1` is proved to be the dominated-convergence limit from below.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace RandomnessExtraction

private noncomputable def standardGaussian : Measure ℝ := gaussianReal 0 1

private instance : IsProbabilityMeasure standardGaussian := by
  dsimp [standardGaussian]
  infer_instance

private theorem profileIntegrand_bounds (f : AdmissibleGenerator)
    (r x G : ℝ) :
    0 ≤ f (gaussianTransition r x G) ∧
      f (gaussianTransition r x G) ≤ f 0 := by
  exact ⟨f.nonneg_of_mem_unit (gaussianCDF_mem_unit _).1
      (gaussianCDF_mem_unit _).2,
    f.antitoneOn_nonneg (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr (gaussianCDF_mem_unit _).1)
      (gaussianCDF_mem_unit _).1⟩

private theorem profileIntegrand_integrable (f : AdmissibleGenerator)
    (r x : ℝ) : Integrable (fun G ↦ f (gaussianTransition r x G))
      standardGaussian := by
  refine Integrable.of_bound ?_ (f 0) ?_
  · exact (f.continuous.comp (continuous_gaussianCDF.comp
      (((continuous_const.add (continuous_const.mul continuous_id))).div_const
        (Real.sqrt (1 - r))))).aestronglyMeasurable
  · exact Eventually.of_forall fun G ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (profileIntegrand_bounds f r x G).1]
      exact (profileIntegrand_bounds f r x G).2

theorem gaussianProfile_zero (f : AdmissibleGenerator) (x : ℝ) :
    gaussianProfile f 0 x = f (gaussianCDF x) := by
  rw [gaussianProfile, if_neg (by norm_num : (0 : ℝ) ≠ 1)]
  have hpoint : (fun G ↦ f (gaussianTransition 0 x G)) =
      fun _ ↦ f (gaussianCDF x) := by
    funext G
    simp [gaussianTransition]
  rw [hpoint]
  simp

@[simp]
theorem gaussianProfile_one (f : AdmissibleGenerator) (x : ℝ) :
    gaussianProfile f 1 x = f 0 * (1 - gaussianCDF x) := by
  simp [gaussianProfile]

theorem continuous_gaussianProfile (f : AdmissibleGenerator) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Continuous (gaussianProfile f r) := by
  rcases hr1.eq_or_lt with rfl | hr1
  · rw [show gaussianProfile f 1 =
        fun x ↦ f 0 * (1 - gaussianCDF x) by funext x; simp]
    exact continuous_const.mul (continuous_const.sub continuous_gaussianCDF)
  · have hV₂ : 0 < 1 - r := sub_pos.mpr hr1
    have heq : varianceGaussianProfile f r (1 - r) = gaussianProfile f r := by
      funext x
      have h := varianceGaussianProfile_eq_gaussianProfile f hr0 hV₂ x
      simpa [add_sub_cancel_left, hr1.ne] using h
    rw [← heq]
    exact continuous_varianceGaussianProfile f r hV₂

theorem antitone_gaussianProfile (f : AdmissibleGenerator) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Antitone (gaussianProfile f r) := by
  intro x₁ x₂ hx
  rcases hr1.eq_or_lt with rfl | hr1
  · simp only [gaussianProfile_one]
    have hcdf := (monotone_cdf (gaussianReal 0 1)) hx
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hcdf 1)
      f.map_zero_nonneg
  · rw [gaussianProfile, if_neg hr1.ne, gaussianProfile, if_neg hr1.ne]
    apply integral_mono (profileIntegrand_integrable f r x₂)
      (profileIntegrand_integrable f r x₁)
    intro G
    apply f.antitoneOn_nonneg (gaussianCDF_mem_unit _).1
      (gaussianCDF_mem_unit _).1
    apply (monotone_cdf (gaussianReal 0 1))
    have hs : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.2 (sub_pos.mpr hr1)
    exact (div_le_div_iff_of_pos_right hs).2 (by gcongr)

private theorem generator_zero_pos_of_strict
    (f : AdmissibleGenerator) (hf : StrictAntiOn f (Set.Ioo 0 1)) :
    0 < f 0 := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hthree : (3 / 4 : ℝ) < 1 := by norm_num
  have hstrict : f (3 / 4 : ℝ) < f (1 / 2 : ℝ) :=
    hf (by norm_num) (by norm_num) (by norm_num)
  have hnonneg : 0 ≤ f (3 / 4 : ℝ) :=
    f.nonneg_of_mem_unit (by norm_num) (by norm_num)
  have hzeroHalf : f (1 / 2 : ℝ) ≤ f 0 :=
    f.antitoneOn_nonneg (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr hhalf.le) hhalf.le
  linarith

theorem strictAnti_gaussianProfile (f : AdmissibleGenerator) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hf : StrictAntiOn f (Set.Ioo 0 1)) :
    StrictAnti (gaussianProfile f r) := by
  intro x₁ x₂ hx
  rcases hr1.eq_or_lt with rfl | hr1
  · simp only [gaussianProfile_one]
    have hcdf : gaussianCDF x₁ < gaussianCDF x₂ := strictMono_gaussianCDF hx
    exact mul_lt_mul_of_pos_left (sub_lt_sub_left hcdf 1)
      (generator_zero_pos_of_strict f hf)
  · rw [gaussianProfile, if_neg hr1.ne, gaussianProfile, if_neg hr1.ne]
    let u : ℝ → ℝ := fun G ↦ f (gaussianTransition r x₂ G)
    let v : ℝ → ℝ := fun G ↦ f (gaussianTransition r x₁ G)
    have huv : ∀ G, u G < v G := by
      intro G
      apply hf
      · exact ⟨gaussianCDF_pos _, gaussianCDF_lt_one _⟩
      · exact ⟨gaussianCDF_pos _, gaussianCDF_lt_one _⟩
      · apply strictMono_gaussianCDF
        have hs : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.2 (sub_pos.mpr hr1)
        exact (div_lt_div_iff_of_pos_right hs).2 (by gcongr)
    have hu : Integrable u standardGaussian := profileIntegrand_integrable f r x₂
    have hv : Integrable v standardGaussian := profileIntegrand_integrable f r x₁
    have hpos : 0 < ∫ G, (v G - u G) ∂standardGaussian := by
      rw [integral_pos_iff_support_of_nonneg]
      · have hsupp : Function.support (fun G ↦ v G - u G) = Set.univ := by
          ext G
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          exact sub_ne_zero.mpr (huv G).ne'
        rw [hsupp, measure_univ]
        norm_num
      · intro G
        exact sub_nonneg.mpr (huv G).le
      · exact hv.sub hu
    rw [integral_sub hv hu] at hpos
    exact sub_pos.mp hpos

private theorem gaussianProfile_tendsto_atBot_of_lt_one
    (f : AdmissibleGenerator) {r : ℝ} (hr : r < 1) :
    Tendsto (gaussianProfile f r) atBot (nhds (f 0)) := by
  let μ := standardGaussian
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, standardGaussian]
    infer_instance
  have hs : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.2 (sub_pos.mpr hr)
  have hDCT : Tendsto (fun x ↦ ∫ G, f (gaussianTransition r x G) ∂μ)
      atBot (nhds (∫ _ : ℝ, f 0 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := fun _ ↦ f 0)
    · exact Eventually.of_forall fun x ↦
        (f.continuous.comp (continuous_gaussianCDF.comp
          ((continuous_const.add (continuous_const.mul continuous_id)).div_const
            (Real.sqrt (1 - r))))).aestronglyMeasurable
    · exact Eventually.of_forall fun x ↦ Eventually.of_forall fun G ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (profileIntegrand_bounds f r x G).1]
        exact (profileIntegrand_bounds f r x G).2
    · exact integrable_const (f 0)
    · exact Eventually.of_forall fun G ↦ by
        have harg : Tendsto (fun x ↦
            (x + Real.sqrt r * G) / Real.sqrt (1 - r)) atBot atBot :=
          Filter.Tendsto.atBot_div_const hs
            (tendsto_atBot_add_const_right atBot (Real.sqrt r * G) tendsto_id)
        have hcdf : Tendsto (fun x ↦ gaussianCDF
            ((x + Real.sqrt r * G) / Real.sqrt (1 - r))) atBot (nhds 0) := by
          exact (tendsto_cdf_atBot (gaussianReal 0 1)).comp harg
        simpa [gaussianTransition, Function.comp_def] using
          (f.continuousAt 0).tendsto.comp hcdf
  have hconst : (∫ _ : ℝ, f 0 ∂μ) = f 0 := by simp
  rw [hconst] at hDCT
  apply hDCT.congr'
  filter_upwards [] with x
  simp [gaussianProfile, hr.ne, μ, standardGaussian]

private theorem gaussianProfile_tendsto_atTop_of_lt_one
    (f : AdmissibleGenerator) {r : ℝ} (hr : r < 1) :
    Tendsto (gaussianProfile f r) atTop (nhds 0) := by
  let μ := standardGaussian
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, standardGaussian]
    infer_instance
  have hs : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.2 (sub_pos.mpr hr)
  have hDCT : Tendsto (fun x ↦ ∫ G, f (gaussianTransition r x G) ∂μ)
      atTop (nhds (∫ _ : ℝ, 0 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := fun _ ↦ f 0)
    · exact Eventually.of_forall fun x ↦
        (f.continuous.comp (continuous_gaussianCDF.comp
          ((continuous_const.add (continuous_const.mul continuous_id)).div_const
            (Real.sqrt (1 - r))))).aestronglyMeasurable
    · exact Eventually.of_forall fun x ↦ Eventually.of_forall fun G ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (profileIntegrand_bounds f r x G).1]
        exact (profileIntegrand_bounds f r x G).2
    · exact integrable_const (f 0)
    · exact Eventually.of_forall fun G ↦ by
        have harg : Tendsto (fun x ↦
            (x + Real.sqrt r * G) / Real.sqrt (1 - r)) atTop atTop :=
          Filter.Tendsto.atTop_div_const hs
            (tendsto_atTop_add_const_right atTop (Real.sqrt r * G) tendsto_id)
        have hcdf : Tendsto (fun x ↦ gaussianCDF
            ((x + Real.sqrt r * G) / Real.sqrt (1 - r))) atTop (nhds 1) := by
          exact (tendsto_cdf_atTop (gaussianReal 0 1)).comp harg
        simpa [gaussianTransition, f.map_one, Function.comp_def] using
          (f.continuousAt 1).tendsto.comp hcdf
  simp only [integral_zero] at hDCT
  apply hDCT.congr'
  filter_upwards [] with x
  simp [gaussianProfile, hr.ne, μ, standardGaussian]

theorem gaussianProfile_tendsto_atBot (f : AdmissibleGenerator) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Tendsto (gaussianProfile f r) atBot (nhds (f 0)) := by
  rcases hr1.eq_or_lt with rfl | hr
  · rw [show gaussianProfile f 1 =
        fun x ↦ f 0 * (1 - gaussianCDF x) by funext x; simp]
    have hcdf : Tendsto (fun x ↦ gaussianCDF x) atBot (nhds 0) :=
      tendsto_cdf_atBot (gaussianReal 0 1)
    have hf0 : Tendsto (fun _ : ℝ ↦ f 0) atBot (nhds (f 0)) :=
      tendsto_const_nhds
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atBot (nhds 1) :=
      tendsto_const_nhds
    simpa using hf0.mul (hone.sub hcdf)
  · exact gaussianProfile_tendsto_atBot_of_lt_one f hr

theorem gaussianProfile_tendsto_atTop (f : AdmissibleGenerator) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Tendsto (gaussianProfile f r) atTop (nhds 0) := by
  rcases hr1.eq_or_lt with rfl | hr
  · rw [show gaussianProfile f 1 =
        fun x ↦ f 0 * (1 - gaussianCDF x) by funext x; simp]
    have hcdf : Tendsto (fun x ↦ gaussianCDF x) atTop (nhds 1) :=
      tendsto_cdf_atTop (gaussianReal 0 1)
    have hf0 : Tendsto (fun _ : ℝ ↦ f 0) atTop (nhds (f 0)) :=
      tendsto_const_nhds
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hf0.mul (hone.sub hcdf)
  · exact gaussianProfile_tendsto_atTop_of_lt_one f hr

private theorem transition_tendsto_zero_from_below {x G : ℝ}
    (hG : G < -x) :
    Tendsto (fun r ↦ gaussianTransition r x G) (nhdsWithin 1 (Set.Iio 1))
      (nhds 0) := by
  let l : Filter ℝ := nhdsWithin 1 (Set.Iio 1)
  have hr : Tendsto (fun r : ℝ ↦ r) l (nhds 1) :=
    tendsto_id.mono_left inf_le_left
  have hnum : Tendsto (fun r : ℝ ↦ x + Real.sqrt r * G) l
      (nhds (x + G)) := by
    simpa using tendsto_const_nhds.add (hr.sqrt.mul_const G)
  have hden : Tendsto (fun r : ℝ ↦ Real.sqrt (1 - r)) l
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) l (nhds 1) :=
        tendsto_const_nhds
      simpa using (hone.sub hr).sqrt
    · filter_upwards [self_mem_nhdsWithin] with r hrlt
      exact Real.sqrt_pos.2 (sub_pos.mpr hrlt)
  have hinv : Tendsto (fun r : ℝ ↦ (Real.sqrt (1 - r))⁻¹) l atTop :=
    hden.inv_tendsto_nhdsGT_zero
  have harg : Tendsto (fun r : ℝ ↦
      (x + Real.sqrt r * G) / Real.sqrt (1 - r)) l atBot := by
    have hneg : x + G < 0 := by linarith
    simpa only [div_eq_mul_inv] using hnum.neg_mul_atTop hneg hinv
  exact (tendsto_cdf_atBot (gaussianReal 0 1)).comp harg

private theorem transition_tendsto_one_from_below {x G : ℝ}
    (hG : -x < G) :
    Tendsto (fun r ↦ gaussianTransition r x G) (nhdsWithin 1 (Set.Iio 1))
      (nhds 1) := by
  let l : Filter ℝ := nhdsWithin 1 (Set.Iio 1)
  have hr : Tendsto (fun r : ℝ ↦ r) l (nhds 1) :=
    tendsto_id.mono_left inf_le_left
  have hnum : Tendsto (fun r : ℝ ↦ x + Real.sqrt r * G) l
      (nhds (x + G)) := by
    simpa using tendsto_const_nhds.add (hr.sqrt.mul_const G)
  have hden : Tendsto (fun r : ℝ ↦ Real.sqrt (1 - r)) l
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) l (nhds 1) :=
        tendsto_const_nhds
      simpa using (hone.sub hr).sqrt
    · filter_upwards [self_mem_nhdsWithin] with r hrlt
      exact Real.sqrt_pos.2 (sub_pos.mpr hrlt)
  have hinv : Tendsto (fun r : ℝ ↦ (Real.sqrt (1 - r))⁻¹) l atTop :=
    hden.inv_tendsto_nhdsGT_zero
  have harg : Tendsto (fun r : ℝ ↦
      (x + Real.sqrt r * G) / Real.sqrt (1 - r)) l atTop := by
    have hpos : 0 < x + G := by linarith
    simpa only [div_eq_mul_inv] using hnum.pos_mul_atTop hpos hinv
  exact (tendsto_cdf_atTop (gaussianReal 0 1)).comp harg

/-- The formula used at `r=1` is the continuous extension of the integral
profile as the variance ratio approaches one from below. -/
theorem gaussianProfile_tendsto_ratio_one (f : AdmissibleGenerator) (x : ℝ) :
    Tendsto (fun r ↦ gaussianProfile f r x)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (gaussianProfile f 1 x)) := by
  let μ : Measure ℝ := standardGaussian
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, standardGaussian]
    infer_instance
  let l : Filter ℝ := nhdsWithin 1 (Set.Iio 1)
  let endpoint : ℝ → ℝ := (Set.Iic (-x)).indicator (fun _ ↦ f 0)
  have hDCT : Tendsto (fun r ↦ ∫ G, f (gaussianTransition r x G) ∂μ) l
      (nhds (∫ G, endpoint G ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := fun _ ↦ f 0)
    · exact Eventually.of_forall fun r ↦
        (f.continuous.comp (continuous_gaussianCDF.comp
          ((continuous_const.add (continuous_const.mul continuous_id)).div_const
            (Real.sqrt (1 - r))))).aestronglyMeasurable
    · exact Eventually.of_forall fun r ↦ Eventually.of_forall fun G ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (profileIntegrand_bounds f r x G).1]
        exact (profileIntegrand_bounds f r x G).2
    · exact integrable_const (f 0)
    · letI : NullSingletonClass μ :=
        nullSingletonClass_gaussianReal (by norm_num)
      filter_upwards [μ.ae_ne (-x)] with G hG
      rcases lt_or_gt_of_ne hG with hlt | hgt
      · have ht := transition_tendsto_zero_from_below hlt
        have hf := (f.continuousAt 0).tendsto.comp ht
        have hend : endpoint G = f 0 := by
          simp [endpoint, hlt.le]
        rw [hend]
        simpa [l, Function.comp_def] using hf
      · have ht := transition_tendsto_one_from_below hgt
        have hf := (f.continuousAt 1).tendsto.comp ht
        have hend : endpoint G = 0 := by
          simp [endpoint, not_le.mpr hgt]
        rw [hend]
        simpa [l, f.map_one, Function.comp_def] using hf
  have hendpoint : (∫ G, endpoint G ∂μ) =
      f 0 * (1 - gaussianCDF x) := by
    rw [show endpoint = (Set.Iic (-x)).indicator (fun _ ↦ f 0) by rfl,
      integral_indicator_const (f 0) measurableSet_Iic, smul_eq_mul]
    have hcdf : μ.real (Set.Iic (-x)) = gaussianCDF (-x) := by
      symm
      exact cdf_eq_real μ (-x)
    rw [hcdf, gaussianCDF_neg]
    ring
  rw [hendpoint] at hDCT
  rw [gaussianProfile_one]
  apply hDCT.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrne : r ≠ 1 := ne_of_lt hr
  simp [gaussianProfile, hrne, μ, standardGaussian]

/-- **Lemma 19 (profile regularity).**  This single declaration records all
assertions of the paper lemma, including strictness under its additional
hypothesis and the continuous `r=1` extension. -/
theorem paperLemma19 (f : AdmissibleGenerator) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Continuous (gaussianProfile f r) ∧
      Antitone (gaussianProfile f r) ∧
      Tendsto (gaussianProfile f r) atBot (nhds (f 0)) ∧
      Tendsto (gaussianProfile f r) atTop (nhds 0) ∧
      (StrictAntiOn f (Set.Ioo 0 1) → StrictAnti (gaussianProfile f r)) ∧
      ∀ x, Tendsto (fun s ↦ gaussianProfile f s x)
        (nhdsWithin 1 (Set.Iio 1)) (nhds (gaussianProfile f 1 x)) := by
  exact ⟨continuous_gaussianProfile f hr.1 hr.2,
    antitone_gaussianProfile f hr.1 hr.2,
    gaussianProfile_tendsto_atBot f hr.1 hr.2,
    gaussianProfile_tendsto_atTop f hr.1 hr.2,
    fun hf ↦ strictAnti_gaussianProfile f hr.1 hr.2 hf,
    gaussianProfile_tendsto_ratio_one f⟩

end RandomnessExtraction
