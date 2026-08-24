import RandomnessExtraction.ConditionalLimit
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite laws and weak convergence

This file connects the finite-sum probability interface used in the paper to
Mathlib's probability measures.  It also records the precise portmanteau
argument needed below: convergence of all real distribution functions to the
continuous standard-Gaussian distribution implies convergence of expectations
of bounded continuous functions.
-/

open Filter MeasureTheory Set
open scoped BigOperators Classical ENNReal NNReal Topology

namespace RandomnessExtraction

namespace FinProb

variable {A : Type*} [Fintype A]

/-- The probability mass function associated with a finite real-valued law. -/
noncomputable def toPMF (p : FinProb A) : PMF A :=
  PMF.ofFintype (fun a ↦ ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun a _ ↦ p.nonneg a), p.sum_prob]
    norm_num)

@[simp]
theorem toPMF_apply (p : FinProb A) (a : A) :
    p.toPMF a = ENNReal.ofReal (p a) := rfl

@[simp]
theorem toPMF_apply_toReal (p : FinProb A) (a : A) :
    (p.toPMF a).toReal = p a := by
  simp [toPMF, p.nonneg a]

/-- The probability measure associated with a finite law. -/
noncomputable def toProbabilityMeasure (p : FinProb A)
    [MeasurableSpace A] : ProbabilityMeasure A :=
  ⟨p.toPMF.toMeasure, inferInstance⟩

theorem toProbabilityMeasure_apply_real (p : FinProb A)
    [MeasurableSpace A] [MeasurableSingletonClass A] (s : Set A) :
    ((p.toProbabilityMeasure s : ℝ≥0) : ℝ) = p.event s := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  change (p.toPMF.toMeasure s).toReal = _
  rw [PMF.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum (fun a _ ↦ by
    simp only [Set.indicator]
    split_ifs <;> simp)]
  simp only [Set.indicator, ENNReal.toReal_zero, FinProb.event]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp [p.nonneg a]

theorem integral_toProbabilityMeasure (p : FinProb A)
    [MeasurableSpace A] [MeasurableSingletonClass A] (g : A → ℝ) :
    ∫ a, g a ∂(p.toProbabilityMeasure : Measure A) = p.expect g := by
  change ∫ a, g a ∂p.toPMF.toMeasure = _
  rw [PMF.integral_eq_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by
    rw [toPMF_apply, ENNReal.toReal_ofReal (p.nonneg a)]
    rfl

end FinProb

/-- The standard Gaussian as a bundled probability measure. -/
noncomputable def standardGaussianProbability : ProbabilityMeasure ℝ :=
  ⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩

@[simp]
theorem standardGaussianProbability_apply_Iic_real (t : ℝ) :
    (((standardGaussianProbability (Set.Iic t) : ℝ≥0) : ℝ)) = gaussianCDF t := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  exact ProbabilityTheory.cdf_eq_real _ _ |>.symm

namespace WeakConvergence

variable {A : ℕ → Type*} [∀ n, Fintype (A n)]

/-- The law on `ℝ` obtained by pushing a changing finite law forward by a
real random variable. -/
noncomputable def realLaw (law : ∀ n, FinProb (A n))
    (Z : ∀ n, A n → ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨((law n).toPMF.map (Z n)).toMeasure, inferInstance⟩

theorem realLaw_apply_Iic_real (law : ∀ n, FinProb (A n))
    (Z : ∀ n, A n → ℝ) (n : ℕ) (t : ℝ) :
    (((realLaw law Z n (Set.Iic t) : ℝ≥0) : ℝ)) =
      (law n).event {a | Z n a ≤ t} := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  change (((law n).toPMF.map (Z n)).toMeasure (Set.Iic t)).toReal = _
  letI : MeasurableSpace (A n) := ⊤
  rw [PMF.toMeasure_map_apply (p := (law n).toPMF) (f := Z n)
    (Set.Iic t) (by fun_prop) measurableSet_Iic]
  change ((law n).toPMF.toMeasure {a | Z n a ≤ t}).toReal = _
  have h := (law n).toProbabilityMeasure_apply_real {a | Z n a ≤ t}
  change ((law n).toPMF.toMeasure {a | Z n a ≤ t}).toReal = _ at h
  exact h

theorem realLaw_apply_Ioc_real (law : ∀ n, FinProb (A n))
    (Z : ∀ n, A n → ℝ) (n : ℕ) {a b : ℝ} (hab : a < b) :
    (((realLaw law Z n (Set.Ioc a b) : ℝ≥0) : ℝ)) =
      (law n).event {z | Z n z ≤ b} - (law n).event {z | Z n z ≤ a} := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  let μ : Measure ℝ := realLaw law Z n
  change μ.real (Set.Ioc a b) = _
  have hsub := measureReal_inter_add_sdiff
    (μ := μ) (s := Set.Iic b) (t := Set.Iic a) measurableSet_Iic
  have hset : Set.Iic b \ Set.Iic a = Set.Ioc a b := by ext z; simp
  have hinter : Set.Iic b ∩ Set.Iic a = Set.Iic a := by ext z; simp [hab.le]
  rw [hset, hinter] at hsub
  have ha : μ.real (Set.Iic a) = (law n).event {z | Z n z ≤ a} := by
    change (((realLaw law Z n (Set.Iic a) : ℝ≥0) : ℝ)) = _
    exact realLaw_apply_Iic_real law Z n a
  have hb : μ.real (Set.Iic b) = (law n).event {z | Z n z ≤ b} := by
    change (((realLaw law Z n (Set.Iic b) : ℝ≥0) : ℝ)) = _
    exact realLaw_apply_Iic_real law Z n b
  linarith

theorem standardGaussianProbability_apply_Ioc_real {a b : ℝ} (hab : a < b) :
    (((standardGaussianProbability (Set.Ioc a b) : ℝ≥0) : ℝ)) =
      gaussianCDF b - gaussianCDF a := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  let μ : Measure ℝ := standardGaussianProbability
  change μ.real (Set.Ioc a b) = _
  have hsub := measureReal_inter_add_sdiff
    (μ := μ) (s := Set.Iic b) (t := Set.Iic a) measurableSet_Iic
  have hset : Set.Iic b \ Set.Iic a = Set.Ioc a b := by ext z; simp
  have hinter : Set.Iic b ∩ Set.Iic a = Set.Iic a := by ext z; simp [hab.le]
  rw [hset, hinter] at hsub
  have ha : μ.real (Set.Iic a) = gaussianCDF a := by
    change (((standardGaussianProbability (Set.Iic a) : ℝ≥0) : ℝ)) = _
    exact standardGaussianProbability_apply_Iic_real a
  have hb : μ.real (Set.Iic b) = gaussianCDF b := by
    change (((standardGaussianProbability (Set.Iic b) : ℝ≥0) : ℝ)) = _
    exact standardGaussianProbability_apply_Iic_real b
  linarith

/-- CDF convergence to the continuous standard Gaussian entails weak
convergence of the corresponding probability measures. -/
theorem tendsto_realLaw_of_cdf
    (law : ∀ n, FinProb (A n)) (Z : ∀ n, A n → ℝ)
    (hCDF : ∀ t : ℝ, Tendsto
      (fun n ↦ (law n).event {a | Z n a ≤ t}) atTop (nhds (gaussianCDF t))) :
    Tendsto (realLaw law Z) atTop (nhds standardGaussianProbability) := by
  let S : Set (Set ℝ) := {s | ∃ a b : ℝ, a < b ∧ Set.Ioc a b = s}
  apply IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
    (S := S) (isPiSystem_Ioc (fun x : ℝ ↦ x) (fun x : ℝ ↦ x))
  · rintro s ⟨a, b, hab, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨ε, hε, hxε⟩ := Metric.isOpen_iff.1 hu x hx
    refine ⟨Set.Ioc (x - ε / 2) (x + ε / 2), ⟨x - ε / 2, x + ε / 2, by linarith,
      rfl⟩, ?_, ?_⟩
    · exact Ioc_mem_nhds (by linarith) (by linarith)
    · intro z hz
      apply hxε
      rw [Metric.mem_ball, Real.dist_eq]
      rcases hz with ⟨hz1, hz2⟩
      rw [abs_lt]
      constructor <;> linarith
  · rintro s ⟨a, b, hab, rfl⟩
    rw [← NNReal.tendsto_coe]
    simp only [realLaw_apply_Ioc_real law Z _ hab,
      standardGaussianProbability_apply_Ioc_real hab]
    exact (hCDF b).sub (hCDF a)

/-- Weak convergence gives convergence of expectations of every bounded
continuous real function, written back in the finite-sum interface. -/
theorem expect_tendsto_of_cdf
    (law : ∀ n, FinProb (A n)) (Z : ∀ n, A n → ℝ)
    (hCDF : ∀ t : ℝ, Tendsto
      (fun n ↦ (law n).event {a | Z n a ≤ t}) atTop (nhds (gaussianCDF t)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∃ C : ℝ, ∀ x y, dist (g x) (g y) ≤ C) :
    Tendsto (fun n ↦ (law n).expect (fun a ↦ g (Z n a))) atTop
      (nhds (∫ z, g z ∂(ProbabilityTheory.gaussianReal 0 1))) := by
  let G : BoundedContinuousFunction ℝ ℝ :=
    { toFun := g
      continuous_toFun := hg
      map_bounded' := hgb }
  have hweak := tendsto_realLaw_of_cdf law Z hCDF
  have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) G
  have hfinite : ∀ n, ∫ z, G z ∂(realLaw law Z n : Measure ℝ) =
      (law n).expect (fun a ↦ g (Z n a)) := by
    intro n
    change ∫ z, g z ∂((law n).toPMF.map (Z n)).toMeasure = _
    letI : MeasurableSpace (A n) := ⊤
    rw [← PMF.toMeasure_map (p := (law n).toPMF) (f := Z n) (by fun_prop)]
    rw [MeasureTheory.integral_map (by fun_prop) hg.aestronglyMeasurable]
    exact (law n).integral_toProbabilityMeasure (fun a ↦ g (Z n a))
  have hfun : (fun n ↦ ∫ z, G z ∂(realLaw law Z n : Measure ℝ)) =
      (fun n ↦ (law n).expect (fun a ↦ g (Z n a))) := funext hfinite
  rw [hfun] at hint
  simpa only [G, standardGaussianProbability, ProbabilityMeasure.coe_mk,
    BoundedContinuousFunction.coe_mk] using hint

/-- Bounded continuous mapping for the nondegenerate Gaussian CDF
convergence convention used in `ConditionalLimit.TendstoGaussianCDF`. -/
theorem expect_tendsto_of_gaussianCDF
    (law : ∀ n, FinProb (A n)) (Z : ∀ n, A n → ℝ) {v : ℝ} (hv : 0 < v)
    (hCDF : ConditionalLimit.TendstoGaussianCDF A law Z v)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∃ C : ℝ, ∀ x y, dist (g x) (g y) ≤ C) :
    Tendsto (fun n ↦ (law n).expect (fun a ↦ g (Z n a))) atTop
      (nhds (∫ z, g (Real.sqrt v * z)
        ∂(ProbabilityTheory.gaussianReal 0 1))) := by
  let s := Real.sqrt v
  have hs : 0 < s := Real.sqrt_pos.2 hv
  let W : ∀ n, A n → ℝ := fun n a ↦ Z n a / s
  have hWcdf : ∀ t : ℝ, Tendsto
      (fun n ↦ (law n).event {a | W n a ≤ t}) atTop
        (nhds (gaussianCDF t)) := by
    intro t
    have hraw := hCDF (t * s) (Or.inr hv.ne')
    simp only [if_neg hv.ne'] at hraw
    have harg : t * s / Real.sqrt v = t := by
      dsimp [s]
      field_simp [hs.ne']
    rw [harg] at hraw
    apply hraw.congr'
    exact Eventually.of_forall fun n ↦ by
      apply congrArg (law n).event
      ext a
      simp only [Set.mem_setOf_eq]
      dsimp [W]
      exact (div_le_iff₀ hs).symm
  let gs : ℝ → ℝ := fun z ↦ g (s * z)
  have hgs : Continuous gs := hg.comp (continuous_const.mul continuous_id)
  have hgsb : ∃ C : ℝ, ∀ x y, dist (gs x) (gs y) ≤ C := by
    obtain ⟨C, hC⟩ := hgb
    exact ⟨C, fun x y ↦ hC (s * x) (s * y)⟩
  have hlim := expect_tendsto_of_cdf law W hWcdf gs hgs hgsb
  apply hlim.congr'
  exact Eventually.of_forall fun n ↦ by
    apply congrArg (law n).expect
    funext a
    dsimp [gs, W]
    field_simp [hs.ne']

end WeakConvergence

end RandomnessExtraction
