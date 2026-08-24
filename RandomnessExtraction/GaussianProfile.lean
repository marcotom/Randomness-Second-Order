import RandomnessExtraction.ConditionalCapped
import RandomnessExtraction.UniformEndpoint
import RandomnessExtraction.WeakConvergence
import Mathlib.Topology.UnitInterval

/-!
# Gaussian profiles

This file defines the nonlinear Gaussian profile from the paper and proves
the bounded-continuous-mapping and uniform-integrability steps used in
Proposition 17.
-/

open Filter MeasureTheory Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

open ConditionalCapped ConditionalLimit UniformEndpoint

/-- The Gaussian transition `Q_r(G;x)` from the paper. -/
noncomputable def gaussianTransition (r x G : ℝ) : ℝ :=
  gaussianCDF ((x + Real.sqrt r * G) / Real.sqrt (1 - r))

/-- The Gaussian `f`-profile, including its `r=1` endpoint. -/
noncomputable def gaussianProfile (f : AdmissibleGenerator) (r x : ℝ) : ℝ :=
  if r = 1 then f 0 * (1 - gaussianCDF x)
  else ∫ G, f (gaussianTransition r x G)
    ∂(ProbabilityTheory.gaussianReal 0 1)

/-- The same profile before the variance-ratio change of variables. -/
noncomputable def varianceGaussianProfile (f : AdmissibleGenerator)
    (V₁ V₂ x : ℝ) : ℝ :=
  ∫ G, f (gaussianCDF
      ((x * Real.sqrt (V₁ + V₂) + Real.sqrt V₁ * G) /
        Real.sqrt V₂))
    ∂(ProbabilityTheory.gaussianReal 0 1)

/-- Projection of a real number to the unit interval. -/
noncomputable def unitProjection (t : ℝ) : ℝ :=
  Set.projIcc (0 : ℝ) 1 zero_le_one t

/-- A globally uniformly continuous extension of `f|_[0,1]`. -/
noncomputable def clampedGenerator (f : AdmissibleGenerator) (t : ℝ) : ℝ :=
  f (unitProjection t)

theorem unitProjection_mem (t : ℝ) : unitProjection t ∈ Set.Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one t).2

theorem unitProjection_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    unitProjection t = t := by
  simpa [unitProjection] using congrArg Subtype.val
    (Set.projIcc_of_mem zero_le_one ht)

theorem clampedGenerator_of_mem (f : AdmissibleGenerator) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : clampedGenerator f t = f t := by
  rw [clampedGenerator, unitProjection_of_mem ht]

theorem clampedGenerator_bounds (f : AdmissibleGenerator) (t : ℝ) :
    0 ≤ clampedGenerator f t ∧ clampedGenerator f t ≤ f 0 := by
  have ht := unitProjection_mem t
  constructor
  · exact f.nonneg_of_mem_unit ht.1 ht.2
  · exact f.antitoneOn_nonneg (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr ht.1) ht.1

theorem clampedGenerator_dist_le (f : AdmissibleGenerator) (s t : ℝ) :
    dist (clampedGenerator f s) (clampedGenerator f t) ≤ f 0 := by
  rw [Real.dist_eq, abs_le]
  rcases clampedGenerator_bounds f s with ⟨hs0, hs1⟩
  rcases clampedGenerator_bounds f t with ⟨ht0, ht1⟩
  constructor <;> linarith

theorem uniformContinuous_clampedGenerator (f : AdmissibleGenerator) :
    UniformContinuous (clampedGenerator f) := by
  let F : Set.Icc (0 : ℝ) 1 → ℝ := fun t ↦ f t.1
  have hF : Continuous F := f.continuous.comp continuous_subtype_val
  have hFuc : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous hF
  have hproj : UniformContinuous (Set.projIcc (0 : ℝ) 1 zero_le_one) :=
    (LipschitzWith.projIcc zero_le_one).uniformContinuous
  change UniformContinuous (fun t ↦ F (Set.projIcc (0 : ℝ) 1 zero_le_one t))
  exact hFuc.comp hproj

theorem finProb_expect_sub {A : Type*} [Fintype A]
    (p : FinProb A) (u v : A → ℝ) :
    p.expect (fun a ↦ u a - v a) = p.expect u - p.expect v := by
  rw [FinProb.expect, FinProb.expect, FinProb.expect]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

/-- Convergence in probability to zero plus a deterministic uniform bound
implies convergence of the finite expectations to zero. -/
theorem expect_tendsto_zero_of_inProbability_bounded
    {A : ℕ → Type} [∀ n, Fintype (A n)]
    (law : ∀ n, FinProb (A n)) (Z : ∀ n, A n → ℝ)
    (hZ : TendstoInProbabilityZero A law Z) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n a, |Z n a| ≤ C) :
    Tendsto (fun n ↦ (law n).expect (Z n)) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_cases hC0 : C = 0
  · have hzero : ∀ n a, Z n a = 0 := by
      intro n a
      exact abs_eq_zero.mp (le_antisymm (by simpa [hC0] using hbound n a) (abs_nonneg _))
    filter_upwards [] with n
    simp [FinProb.expect, hzero, hε]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    let δ := ε / 2
    have hδ : 0 < δ := div_pos hε (by norm_num)
    have hprob := hZ δ hδ
    have hsmall : ∀ᶠ n in atTop,
        (law n).event {a | δ ≤ |Z n a|} < ε / (2 * C) :=
      (tendsto_order.1 hprob).2 _ (div_pos hε (mul_pos (by norm_num) hCpos))
    filter_upwards [hsmall] with n hn
    have habsExpect : |(law n).expect (Z n)| ≤
        (law n).expect (fun a ↦ |Z n a|) := by
      rw [FinProb.expect, FinProb.expect]
      calc
        |∑ a, law n a * Z n a| ≤ ∑ a, |law n a * Z n a| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ a, law n a * |Z n a| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [abs_mul, abs_of_nonneg ((law n).nonneg a)]
    have hlocal := ConditionalCapped.expect_le_local_add_bad (X := A n) (law n)
      (fun a : A n ↦ |Z n a|) {a : A n | |Z n a| < δ} δ C
      (fun _ ↦ abs_nonneg _) (fun _ ha ↦ ha.le) (hbound n) hδ.le hC
    have hcomp : (law n).event {a | |Z n a| < δ}ᶜ =
        (law n).event {a | δ ≤ |Z n a|} := by
      apply congrArg (law n).event
      ext a
      simp
    rw [hcomp] at hlocal
    rw [Real.dist_eq, sub_zero]
    exact habsExpect.trans_lt (hlocal.trans_lt (by
      have hmul := mul_lt_mul_of_pos_left hn hCpos
      have hcalc : C * (ε / (2 * C)) = ε / 2 := by field_simp [hC0]
      rw [hcalc] at hmul
      dsimp [δ]
      linarith))

theorem expect_difference_tendsto_zero_of_inProbability
    {A : ℕ → Type} [∀ n, Fintype (A n)]
    (law : ∀ n, FinProb (A n)) (U V : ∀ n, A n → ℝ)
    (hUV : TendstoInProbabilityZero A law
      (fun n a ↦ clampedGenerator f (U n a) - clampedGenerator f (V n a))) :
    Tendsto (fun n ↦ (law n).expect
      (fun a ↦ clampedGenerator f (U n a) - clampedGenerator f (V n a)))
      atTop (nhds 0) := by
  apply expect_tendsto_zero_of_inProbability_bounded law _ hUV f.map_zero_nonneg
  intro n a
  rw [abs_le]
  rcases clampedGenerator_bounds f (U n a) with ⟨hU0, hU1⟩
  rcases clampedGenerator_bounds f (V n a) with ⟨hV0, hV1⟩
  constructor <;> linarith

theorem gaussianCDF_mem_unit (t : ℝ) : gaussianCDF t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ProbabilityTheory.cdf_nonneg _ _, ProbabilityTheory.cdf_le_one _ _⟩

theorem conditionalTail_mem_unit {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) (x : ℝ) :
    conditionalTail P y x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(conditionalProduct P y).event_nonneg _, (conditionalProduct P y).event_le_one _⟩

theorem gaussianProfileIntegrand_continuous (f : AdmissibleGenerator)
    (V₁ V₂ x : ℝ) (hV₂ : 0 < V₂) :
    Continuous (fun z ↦ f (gaussianCDF
      ((x * Real.sqrt (V₁ + V₂) + z) / Real.sqrt V₂))) := by
  exact f.continuous.comp (continuous_gaussianCDF.comp
    ((continuous_const.add continuous_id).div_const (Real.sqrt V₂)))

theorem gaussianProfileIntegrand_bounded (f : AdmissibleGenerator)
    (V₁ V₂ x : ℝ) :
    ∃ C : ℝ, ∀ s t, dist
      (f (gaussianCDF ((x * Real.sqrt (V₁ + V₂) + s) / Real.sqrt V₂)))
      (f (gaussianCDF ((x * Real.sqrt (V₁ + V₂) + t) / Real.sqrt V₂))) ≤ C := by
  refine ⟨f 0, ?_⟩
  intro s t
  rw [Real.dist_eq, abs_le]
  have hs := gaussianCDF_mem_unit
    ((x * Real.sqrt (V₁ + V₂) + s) / Real.sqrt V₂)
  have ht := gaussianCDF_mem_unit
    ((x * Real.sqrt (V₁ + V₂) + t) / Real.sqrt V₂)
  have hfs0 := f.nonneg_of_mem_unit hs.1 hs.2
  have hft0 := f.nonneg_of_mem_unit ht.1 ht.2
  have hfs1 := f.antitoneOn_nonneg (Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr hs.1) hs.1
  have hft1 := f.antitoneOn_nonneg (Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr ht.1) ht.1
  constructor <;> linarith

/-- The central nonlinear expectation limit in the `V₂>0` proof of
Proposition 17. -/
theorem conditionalTailExpectation_tendsto_varianceProfile
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV₂ : 0 < variance₂ P) (x : ℝ) :
    Tendsto (fun n ↦ (P.marginal.iid n).expect
      (fun y ↦ f (conditionalTail P y x))) atTop
      (nhds (varianceGaussianProfile f (variance₁ P) (variance₂ P) x)) := by
  let law : ∀ n, FinProb (Fin n → Y) := fun n ↦ P.marginal.iid n
  let U : ∀ n, (Fin n → Y) → ℝ := fun _ y ↦ conditionalTail P y x
  let W : ∀ n, (Fin n → Y) → ℝ := fun _ y ↦
    gaussianCDF (limitingGaussianArgument P y x)
  have hlemma := paperLemma13 hBE P hpY hV₂ x
  have hclamp := tendstoInProbabilityZero_uniformContinuous_sub law U W
    (clampedGenerator f) hlemma.1 (uniformContinuous_clampedGenerator f)
  have hdiff := expect_difference_tendsto_zero_of_inProbability
    (f := f) law U W hclamp
  have hdiff' : Tendsto (fun n ↦
      (P.marginal.iid n).expect (fun y ↦ f (conditionalTail P y x)) -
      (P.marginal.iid n).expect (fun y ↦
        f (gaussianCDF (limitingGaussianArgument P y x)))) atTop (nhds 0) := by
    apply hdiff.congr'
    exact Eventually.of_forall fun n ↦ by
      change (law n).expect
        (fun y ↦ clampedGenerator f (U n y) - clampedGenerator f (W n y)) = _
      rw [finProb_expect_sub]
      dsimp only [law, U, W]
      apply congrArg₂ (fun a b : ℝ ↦ a - b)
      · apply congrArg (P.marginal.iid n).expect
        funext y
        rw [clampedGenerator_of_mem f (conditionalTail_mem_unit P y x)]
      · apply congrArg (P.marginal.iid n).expect
        funext y
        rw [clampedGenerator_of_mem f (gaussianCDF_mem_unit _)]
  let g : ℝ → ℝ := fun z ↦ f (gaussianCDF
    ((x * Real.sqrt (totalVariance P) + z) / Real.sqrt (variance₂ P)))
  have hg : Continuous g := by
    dsimp [g]
    rw [totalVariance]
    exact gaussianProfileIntegrand_continuous f
      (variance₁ P) (variance₂ P) x hV₂
  have hgb : ∃ C : ℝ, ∀ s t, dist (g s) (g t) ≤ C := by
    dsimp [g]
    rw [totalVariance]
    exact gaussianProfileIntegrand_bounded f
      (variance₁ P) (variance₂ P) x
  by_cases hV₁zero : variance₁ P = 0
  · have hpoint : ∀ y, centered P.marginal (fiberEntropy P) y = 0 :=
      centered_eq_zero_of_finiteVariance_eq_zero P.marginal hpY (fiberEntropy P)
        (by simpa only [finiteVariance_fiberEntropy] using hV₁zero)
    have hcenter : ∀ (n : ℕ) (y : Fin n → Y), center P y = 0 := by
      intro n y
      rw [center_eq_centered_sum]
      simp [hpoint]
    have hWexpect : ∀ n,
        (P.marginal.iid n).expect (fun y ↦
          f (gaussianCDF (limitingGaussianArgument P y x))) = g 0 := by
      intro n
      rw [show (fun y ↦ f (gaussianCDF (limitingGaussianArgument P y x))) =
          (fun _ ↦ g 0) by
        funext y
        simp only [limitingGaussianArgument, g, hcenter, add_zero]]
      exact (P.marginal.iid n).expect_const (g 0)
    have hprof : varianceGaussianProfile f (variance₁ P) (variance₂ P) x = g 0 := by
      have hVeq : totalVariance P = variance₂ P := by
        rw [totalVariance, hV₁zero, zero_add]
      rw [varianceGaussianProfile, hV₁zero, Real.sqrt_zero]
      simp only [zero_mul, add_zero]
      have hfun : (fun _G : ℝ ↦
          f (gaussianCDF (x * Real.sqrt (0 + variance₂ P) /
            Real.sqrt (variance₂ P)))) = (fun _ ↦ g 0) := by
        funext G
        simp [g, hVeq]
      rw [hfun]
      simp
    have hWlim : Tendsto (fun n ↦
        (P.marginal.iid n).expect (fun y ↦
          f (gaussianCDF (limitingGaussianArgument P y x)))) atTop
        (nhds (varianceGaussianProfile f (variance₁ P) (variance₂ P) x)) := by
      simp_rw [hWexpect, hprof]
      exact tendsto_const_nhds
    have := hdiff'.add hWlim
    simpa only [sub_add_cancel, zero_add] using this
  · have hV₁ : 0 < variance₁ P :=
      lt_of_le_of_ne (variance₁_nonneg P) (Ne.symm hV₁zero)
    have hWlim := WeakConvergence.expect_tendsto_of_gaussianCDF law
      (fun _ y ↦ center P y) hV₁ hlemma.2 g hg hgb
    have hWlim' : Tendsto (fun n ↦
        (P.marginal.iid n).expect (fun y ↦
          f (gaussianCDF (limitingGaussianArgument P y x)))) atTop
        (nhds (varianceGaussianProfile f (variance₁ P) (variance₂ P) x)) := by
      simpa only [law, g, limitingGaussianArgument, varianceGaussianProfile,
        totalVariance] using hWlim
    have := hdiff'.add hWlim'
    simpa only [sub_add_cancel, zero_add] using this

/-- Change of variables from the two variance components to the ratio
`r=V₁/(V₁+V₂)`. -/
theorem varianceGaussianProfile_eq_gaussianProfile
    (f : AdmissibleGenerator) {V₁ V₂ : ℝ} (hV₁ : 0 ≤ V₁) (hV₂ : 0 < V₂)
    (x : ℝ) :
    varianceGaussianProfile f V₁ V₂ x =
      gaussianProfile f (V₁ / (V₁ + V₂)) x := by
  let V := V₁ + V₂
  have hV : 0 < V := by dsimp [V]; linarith
  have hrne : V₁ / V ≠ 1 := by
    intro h
    have := (div_eq_one_iff_eq hV.ne').mp h
    dsimp [V] at this
    linarith
  rw [gaussianProfile, if_neg hrne, varianceGaussianProfile]
  apply integral_congr_ae
  filter_upwards [] with G
  unfold gaussianTransition
  congr 2
  have hsqrtV : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hsqrtV₂ : 0 < Real.sqrt V₂ := Real.sqrt_pos.2 hV₂
  have hone : 1 - V₁ / V = V₂ / V := by
    field_simp [hV.ne']
    dsimp [V]
    ring
  rw [Real.sqrt_div hV₁ V, hone, Real.sqrt_div hV₂.le V]
  dsimp [V]
  field_simp [hsqrtV.ne', hsqrtV₂.ne']

theorem abs_expect_le_expect_abs {A : Type*} [Fintype A]
    (p : FinProb A) (u : A → ℝ) :
    |p.expect u| ≤ p.expect (fun a ↦ |u a|) := by
  rw [FinProb.expect, FinProb.expect]
  calc
    |∑ a, p a * u a| ≤ ∑ a, |p a * u a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, p a * |u a| := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (p.nonneg a)]

/-- The fixed-reference capped quantity has the same `V₂>0` limit as
the nonlinear conditional-tail expectation. -/
theorem fixedCappedAverage_tendsto_varianceProfile
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV₂ : 0 < variance₂ P) (x : ℝ) :
    Tendsto (fun n ↦ endpointCappedAverage f P n x) atTop
      (nhds (varianceGaussianProfile f (variance₁ P) (variance₂ P) x)) := by
  have htail := conditionalTailExpectation_tendsto_varianceProfile
    hBE f P hpY hV₂ x
  have herr := (paperLemma14 hBE f P hpY hV₂ x
    (K := 1) zero_lt_one).2
  have hbound : ∀ n,
      |endpointCappedAverage f P n x -
        (P.marginal.iid n).expect (fun y ↦ f (conditionalTail P y x))| ≤
          conditionalCappedError f P n x := by
    intro n
    rw [endpointCappedAverage, ← finProb_expect_sub]
    refine (abs_expect_le_expect_abs (P.marginal.iid n) _).trans_eq ?_
    rw [conditionalCappedError]
    apply congrArg (P.marginal.iid n).expect
    funext y
    rw [supportTail_eq_conditionalTail]
  have habs : Tendsto (fun n ↦
      |endpointCappedAverage f P n x -
        (P.marginal.iid n).expect (fun y ↦ f (conditionalTail P y x))|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · exact Eventually.of_forall hbound
    · exact herr
  have hsub : Tendsto (fun n ↦ endpointCappedAverage f P n x -
      (P.marginal.iid n).expect (fun y ↦ f (conditionalTail P y x)))
      atTop (nhds 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simpa only [sub_zero, Real.norm_eq_abs] using habs
  have := hsub.add htail
  simpa only [sub_add_cancel, zero_add] using this

theorem fixedCappedAverage_tendsto_gaussianProfile
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV₂ : 0 < variance₂ P) (x : ℝ) :
    Tendsto (fun n ↦ endpointCappedAverage f P n x) atTop
      (nhds (gaussianProfile f (variance₁ P / totalVariance P) x)) := by
  have h := fixedCappedAverage_tendsto_varianceProfile hBE f P hpY hV₂ x
  have heq := varianceGaussianProfile_eq_gaussianProfile f
    (variance₁_nonneg P) hV₂ x
  rw [← totalVariance] at heq
  rwa [heq] at h

theorem continuous_varianceGaussianProfile (f : AdmissibleGenerator)
    (V₁ : ℝ) {V₂ : ℝ} (hV₂ : 0 < V₂) :
    Continuous (varianceGaussianProfile f V₁ V₂) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  unfold varianceGaussianProfile
  let μ := ProbabilityTheory.gaussianReal 0 1
  let F : ℝ → ℝ → ℝ := fun x G ↦ f (gaussianCDF
    ((x * Real.sqrt (V₁ + V₂) + Real.sqrt V₁ * G) / Real.sqrt V₂))
  apply tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (bound := fun _ ↦ f 0)
  · exact Eventually.of_forall fun x ↦ by
      exact (f.continuous.comp (continuous_gaussianCDF.comp
        ((continuous_const.add (continuous_const.mul continuous_id)).div_const
          (Real.sqrt V₂)))).aestronglyMeasurable
  · exact Eventually.of_forall fun x ↦ Filter.Eventually.of_forall fun G ↦ by
      have hq := gaussianCDF_mem_unit
        ((x * Real.sqrt (V₁ + V₂) + Real.sqrt V₁ * G) / Real.sqrt V₂)
      have hf0 := f.nonneg_of_mem_unit hq.1 hq.2
      have hf1 := f.antitoneOn_nonneg (Set.mem_Ici.mpr le_rfl)
        (Set.mem_Ici.mpr hq.1) hq.1
      rw [Real.norm_eq_abs, abs_of_nonneg hf0]
      exact hf1
  · exact integrable_const (f 0)
  · exact Filter.Eventually.of_forall fun G ↦ by
      exact f.continuous.continuousAt.comp'
        (continuous_gaussianCDF.continuousAt.comp'
          (((continuous_id.mul continuous_const).add continuous_const).div_const
            (Real.sqrt V₂)).continuousAt)

theorem conditionalTail_mono_parameter
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) {n : ℕ} {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂)
    (y : Fin n → Y) : conditionalTail P y x₁ ≤ conditionalTail P y x₂ := by
  apply ConditionalLimit.finProb_event_mono (conditionalProduct P y)
  intro z hz
  change threshold P n x₁ ≤ blockInformation P z y at hz
  change threshold P n x₂ ≤ blockInformation P z y
  apply le_trans _ hz
  unfold threshold
  gcongr

theorem shiftedParameter_tendsto
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (hV : 0 < totalVariance P)
    (x : ℝ) (tau : ℕ → ℝ) (htau : AdmissibleShift tau) :
    Tendsto (fun n ↦ shiftedThresholdParameter P n x (tau n)) atTop (nhds x) := by
  have hsqrtV : 0 < Real.sqrt (totalVariance P) := Real.sqrt_pos.2 hV
  have hratio : Tendsto
      (fun n ↦ (tau n / Real.sqrt (n : ℝ)) / Real.sqrt (totalVariance P))
      atTop (nhds 0) := by
    simpa using htau.2.div_const (Real.sqrt (totalVariance P))
  have heq : (fun n ↦ tau n / Real.sqrt ((n : ℝ) * totalVariance P)) =
      (fun n ↦ (tau n / Real.sqrt (n : ℝ)) /
        Real.sqrt (totalVariance P)) := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [Real.sqrt_mul hnR (totalVariance P)]
      ring
  have hsmall : Tendsto
      (fun n ↦ tau n / Real.sqrt ((n : ℝ) * totalVariance P))
      atTop (nhds 0) := by rwa [heq]
  simpa [shiftedThresholdParameter] using tendsto_const_nhds.sub hsmall

theorem shiftedTailExpectation_tendsto_varianceProfile
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV₂ : 0 < variance₂ P) (x : ℝ) (tau : ℕ → ℝ)
    (htau : AdmissibleShift tau) :
    Tendsto (fun n ↦ endpointShiftedTailAverage f P n x (tau n)) atTop
      (nhds (varianceGaussianProfile f (variance₁ P) (variance₂ P) x)) := by
  have hV : 0 < totalVariance P := by
    unfold totalVariance
    linarith [variance₁_nonneg P]
  have hparam := shiftedParameter_tendsto P hV x tau htau
  have hcont : ContinuousAt
      (varianceGaussianProfile f (variance₁ P) (variance₂ P)) x :=
    (continuous_varianceGaussianProfile f (variance₁ P) hV₂).continuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hprof⟩ := (Metric.continuousAt_iff.1 hcont) (ε / 3) (by linarith)
  let δ := min (η / 2) 1
  have hδ : 0 < δ := lt_min (div_pos hη (by norm_num)) zero_lt_one
  have hδη : δ < η := (min_le_left (η / 2) 1).trans_lt (by linarith)
  have hprofL : dist
      (varianceGaussianProfile f (variance₁ P) (variance₂ P) (x - δ))
      (varianceGaussianProfile f (variance₁ P) (variance₂ P) x) < ε / 3 := by
    apply hprof
    rw [Real.dist_eq]
    simpa [abs_of_nonneg hδ.le] using hδη
  have hprofR : dist
      (varianceGaussianProfile f (variance₁ P) (variance₂ P) (x + δ))
      (varianceGaussianProfile f (variance₁ P) (variance₂ P) x) < ε / 3 := by
    apply hprof
    rw [Real.dist_eq]
    simpa [abs_of_nonneg hδ.le] using hδη
  have hleft := conditionalTailExpectation_tendsto_varianceProfile
    hBE f P hpY hV₂ (x - δ)
  have hright := conditionalTailExpectation_tendsto_varianceProfile
    hBE f P hpY hV₂ (x + δ)
  have hparamEv : ∀ᶠ n in atTop,
      shiftedThresholdParameter P n x (tau n) ∈ Set.Icc (x - δ) (x + δ) := by
    have hnear := hparam.eventually (Metric.ball_mem_nhds x hδ)
    filter_upwards [hnear] with n hn
    rw [Real.dist_eq, abs_lt] at hn
    exact ⟨by linarith [hn.1], by linarith [hn.2]⟩
  have hleftEv := hleft.eventually
    (Metric.ball_mem_nhds _ (by linarith : 0 < ε / 3))
  have hrightEv := hright.eventually
    (Metric.ball_mem_nhds _ (by linarith : 0 < ε / 3))
  filter_upwards [hparamEv, hleftEv, hrightEv, eventually_gt_atTop (0 : ℕ)]
    with n hnpar hnleft hnright hn
  have hshiftEq (y : Fin n → Y) :
      shiftedConditionalTail P y x (tau n) =
        conditionalTail P y (shiftedThresholdParameter P n x (tau n)) := by
    exact (conditionalTail_shiftedParameter P hn hV₂ x (tau n) y).symm
  have hpointLower (y : Fin n → Y) :
      f (conditionalTail P y (x + δ)) ≤
        f (shiftedConditionalTail P y x (tau n)) := by
    rw [hshiftEq]
    exact f.antitoneOn_nonneg
      (conditionalTail_mem_unit P y _).1
      (conditionalTail_mem_unit P y (x + δ)).1
      (conditionalTail_mono_parameter P hnpar.2 y)
  have hpointUpper (y : Fin n → Y) :
      f (shiftedConditionalTail P y x (tau n)) ≤
        f (conditionalTail P y (x - δ)) := by
    rw [hshiftEq]
    exact f.antitoneOn_nonneg
      (conditionalTail_mem_unit P y (x - δ)).1
      (conditionalTail_mem_unit P y _).1
      (conditionalTail_mono_parameter P hnpar.1 y)
  have hlower := (P.marginal.iid n).expect_mono hpointLower
  have hupper := (P.marginal.iid n).expect_mono hpointUpper
  change dist (endpointShiftedTailAverage f P n x (tau n))
    (varianceGaussianProfile f (variance₁ P) (variance₂ P) x) < ε
  rw [Real.dist_eq, abs_lt]
  rw [Real.dist_eq, abs_lt] at hnleft hnright hprofL hprofR
  constructor <;> dsimp [endpointShiftedTailAverage] at hlower hupper ⊢ <;> linarith

/-- **Proposition 17 (Gaussian `f`-profile).**  Both the capped fixed-reference
quantity and every admissibly shifted conditional-tail expectation converge
to the same profile. -/
theorem paperProposition17
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV : 0 < totalVariance P) (x : ℝ) :
    Tendsto (fun n ↦ endpointCappedAverage f P n x) atTop
        (nhds (gaussianProfile f (variance₁ P / totalVariance P) x)) ∧
      ∀ tau : ℕ → ℝ, AdmissibleShift tau →
        Tendsto (fun n ↦ endpointShiftedTailAverage f P n x (tau n)) atTop
          (nhds (gaussianProfile f (variance₁ P / totalVariance P) x)) := by
  by_cases hV₂zero : variance₂ P = 0
  · have hV₁ : variance₁ P = totalVariance P := by
      rw [totalVariance, hV₂zero, add_zero]
    have hratio : variance₁ P / totalVariance P = 1 := by
      rw [hV₁]
      exact div_self hV.ne'
    have hend : gaussianProfile f (variance₁ P / totalVariance P) x =
        f 0 * (1 - gaussianCDF x) := by simp [gaussianProfile, hratio]
    have h16 := paperLemma16 hBE f P hpY hV₂zero hV x
    rw [hend]
    exact ⟨h16.2.1, h16.2.2⟩
  · have hV₂ : 0 < variance₂ P :=
      lt_of_le_of_ne (variance₂_nonneg P) (Ne.symm hV₂zero)
    constructor
    · exact fixedCappedAverage_tendsto_gaussianProfile hBE f P hpY hV₂ x
    · intro tau htau
      have hlim := shiftedTailExpectation_tendsto_varianceProfile
        hBE f P hpY hV₂ x tau htau
      have heq := varianceGaussianProfile_eq_gaussianProfile f
        (variance₁_nonneg P) hV₂ x
      rw [← totalVariance] at heq
      rwa [heq] at hlim

end RandomnessExtraction
