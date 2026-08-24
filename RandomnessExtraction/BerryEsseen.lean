import RandomnessExtraction.FiniteProbability
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Berry--Esseen input

Mathlib does not currently contain the independent, non-identically
distributed Berry--Esseen inequality used by the paper.  Since every random
variable to which the paper applies it has finite support, Fact 12 is stated
below in its exact finite-product specialization.  Downstream declarations
take a proof of this proposition as an explicit argument; no axiom is added.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology Classical

namespace RandomnessExtraction

universe u

/-- Standard Gaussian cumulative distribution function `Φ`. -/
noncomputable def gaussianCDF (t : ℝ) : ℝ :=
  ProbabilityTheory.cdf (gaussianReal 0 1) t

/-- The standard Gaussian CDF is continuous.  Mathlib's general CDF is only
right-continuous; the missing left-continuity here follows from the fact that
the nondegenerate Gaussian law has no atoms. -/
theorem continuous_gaussianCDF : Continuous gaussianCDF := by
  letI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  rw [continuous_iff_continuousAt]
  intro x
  apply (monotone_cdf (gaussianReal 0 1)).continuousAt_iff_leftLim_eq_rightLim.2
  rw [(cdf (gaussianReal 0 1)).rightLim_eq]
  have hm : (cdf (gaussianReal 0 1)).measure {x} = 0 := by
    rw [measure_cdf]
    exact measure_singleton x
  rw [StieltjesFunction.measure_singleton] at hm
  have hnonneg : 0 ≤ cdf (gaussianReal 0 1) x -
      Function.leftLim (cdf (gaussianReal 0 1)) x := sub_nonneg.mpr
        ((monotone_cdf (gaussianReal 0 1)).leftLim_le le_rfl)
  have hle : cdf (gaussianReal 0 1) x -
      Function.leftLim (cdf (gaussianReal 0 1)) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hm
  linarith

theorem gaussianCDF_pos (t : ℝ) : 0 < gaussianCDF t := by
  rw [gaussianCDF, cdf_eq_real]
  apply ENNReal.toReal_pos
  · intro hzero
    have hac := gaussianReal_absolutelyContinuous' (0 : ℝ)
      (show (1 : ℝ≥0) ≠ 0 by norm_num)
    have hvol : volume (Set.Iic t) = 0 := hac hzero
    rw [Real.volume_Iic] at hvol
    exact ENNReal.top_ne_zero hvol
  · exact measure_ne_top (gaussianReal 0 1) _

theorem gaussianCDF_lt_one (t : ℝ) : gaussianCDF t < 1 := by
  let μ := gaussianReal 0 1
  have hac := gaussianReal_absolutelyContinuous' (0 : ℝ)
    (show (1 : ℝ≥0) ≠ 0 by norm_num)
  have hIoi : μ (Set.Ioi t) ≠ 0 := by
    intro hzero
    have hvol : volume (Set.Ioi t) = 0 := hac hzero
    rw [Real.volume_Ioi] at hvol
    exact ENNReal.top_ne_zero hvol
  have hlt : μ (Set.Iic t) < 1 := by
    have hle : μ (Set.Iic t) ≤ 1 := by
      calc
        μ (Set.Iic t) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    apply lt_of_le_of_ne hle
    intro heq
    have hadd := measure_add_measure_compl (μ := μ) (s := Set.Iic t) measurableSet_Iic
    rw [measure_univ, heq] at hadd
    have hcomp : μ (Set.Iic t)ᶜ = 0 := by
      have hadd' : (1 : ℝ≥0∞) + μ (Set.Iic t)ᶜ = 1 + 0 := by
        simpa using hadd
      exact (ENNReal.add_right_inj ENNReal.one_ne_top).mp hadd'
    have : μ (Set.Ioi t) = 0 := by simpa only [compl_Iic] using hcomp
    exact hIoi this
  rw [gaussianCDF, cdf_eq_real]
  change (μ (Set.Iic t)).toReal < 1
  have hreal := (ENNReal.toReal_lt_toReal
    (measure_ne_top μ (Set.Iic t)) (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).2 hlt
  simpa using hreal

/-- The nondegenerate Gaussian law assigns positive mass to every nonempty
interval, so its cumulative distribution function is strictly increasing. -/
theorem strictMono_gaussianCDF : StrictMono gaussianCDF := by
  intro x y hxy
  let μ := gaussianReal 0 1
  have hac : volume ≪ μ := gaussianReal_absolutelyContinuous' (0 : ℝ)
    (show (1 : ℝ≥0) ≠ 0 by norm_num)
  have hmass : μ (Set.Ioc x y) ≠ 0 := by
    intro hzero
    have hvol : volume (Set.Ioc x y) = 0 := hac hzero
    rw [Real.volume_Ioc] at hvol
    have hpos : 0 < y - x := sub_pos.mpr hxy
    have hyx : y ≤ x := by simpa [ENNReal.ofReal_eq_zero] using hvol
    exact (not_le_of_gt hxy) hyx
  have hmeasure : ENNReal.ofReal (gaussianCDF y - gaussianCDF x) =
      μ (Set.Ioc x y) := by
    change ENNReal.ofReal (cdf μ y - cdf μ x) = μ (Set.Ioc x y)
    calc
      ENNReal.ofReal (cdf μ y - cdf μ x) =
          (cdf μ).measure (Set.Ioc x y) :=
        (StieltjesFunction.measure_Ioc (cdf μ) x y).symm
      _ = μ (Set.Ioc x y) := by rw [measure_cdf μ]
  have hdiffNe : gaussianCDF y - gaussianCDF x ≠ 0 := by
    intro hzero
    rw [hzero, ENNReal.ofReal_zero] at hmeasure
    exact hmass hmeasure.symm
  have hdiffNonneg : 0 ≤ gaussianCDF y - gaussianCDF x :=
    sub_nonneg.mpr ((monotone_cdf μ) hxy.le)
  exact sub_pos.mp (lt_of_le_of_ne hdiffNonneg (Ne.symm hdiffNe))

/-- Symmetry of the standard Gaussian CDF. -/
theorem gaussianCDF_neg (t : ℝ) : gaussianCDF (-t) = 1 - gaussianCDF t := by
  let μ := gaussianReal 0 1
  have hsymm : μ.map (fun z : ℝ ↦ -z) = μ := by
    simpa [μ] using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
  have hneg : μ (Set.Iic (-t)) = μ (Set.Ici t) := by
    calc
      μ (Set.Iic (-t)) = (μ.map (fun z : ℝ ↦ -z)) (Set.Iic (-t)) := by
        rw [hsymm]
      _ = μ ((fun z : ℝ ↦ -z) ⁻¹' Set.Iic (-t)) := by
        rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
      _ = μ (Set.Ici t) := by
        congr 1
        ext z
        simp
  have hsingle : μ {t} = 0 := by
    letI : NullSingletonClass μ := nullSingletonClass_gaussianReal (by norm_num)
    exact measure_singleton t
  have hIoi : μ (Set.Ioi t) = μ (Set.Ici t) := by
    rw [← Set.Ici_sdiff_left, measure_sdiff_null hsingle]
  have hcompl := probReal_add_probReal_compl (μ := μ) (s := Set.Iic t) measurableSet_Iic
  rw [Set.compl_Iic] at hcompl
  unfold gaussianCDF
  rw [cdf_eq_real, cdf_eq_real]
  change μ.real (Set.Iic (-t)) = 1 - μ.real (Set.Iic t)
  have hnegReal : μ.real (Set.Iic (-t)) = μ.real (Set.Ici t) :=
    congrArg ENNReal.toReal hneg
  have hIoiReal : μ.real (Set.Ioi t) = μ.real (Set.Ici t) :=
    congrArg ENNReal.toReal hIoi
  rw [hnegReal, ← hIoiReal]
  linarith

/-- The Gaussian CDF is uniformly continuous on the whole real line.  The
proof combines its limits at both infinities with Heine--Cantor on one compact
interval. -/
theorem uniformContinuous_gaussianCDF : UniformContinuous gaussianCDF := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hbot : Tendsto gaussianCDF atBot (nhds 0) :=
    tendsto_cdf_atBot (gaussianReal 0 1)
  have htop : Tendsto gaussianCDF atTop (nhds 1) :=
    tendsto_cdf_atTop (gaussianReal 0 1)
  have hsmall : ∀ᶠ z in atBot, gaussianCDF z < ε / 4 :=
    (tendsto_order.1 hbot).2 _ (by linarith)
  have hlarge : ∀ᶠ z in atTop, 1 - ε / 4 < gaussianCDF z :=
    (tendsto_order.1 htop).1 _ (by linarith)
  obtain ⟨A₀, hA₀⟩ := eventually_atBot.1 hsmall
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.1 hlarge
  let A : ℝ := min A₀ (-1)
  let B : ℝ := max B₀ 1
  have hA : gaussianCDF A < ε / 4 := hA₀ A (min_le_left _ _)
  have hB : 1 - ε / 4 < gaussianCDF B := hB₀ B (le_max_left _ _)
  have hAB : A < B := by
    have hAneg : A ≤ -1 := min_le_right _ _
    have hBpos : 1 ≤ B := le_max_right _ _
    linarith
  have huc : UniformContinuousOn gaussianCDF (Set.Icc (A - 1) (B + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous continuous_gaussianCDF.continuousOn
  obtain ⟨δ₀, hδ₀, hlocal⟩ := (Metric.uniformContinuousOn_iff.1 huc) ε hε
  let δ : ℝ := min δ₀ 1
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  intro a b hab
  have hmono : Monotone gaussianCDF := monotone_cdf (gaussianReal 0 1)
  have hordered : ∀ {a b : ℝ}, a ≤ b → dist a b < δ →
      dist (gaussianCDF a) (gaussianCDF b) < ε := by
    intro a b habOrder habDist
    by_cases hbA : b ≤ A
    · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hmono habOrder))]
      rw [neg_sub]
      calc
        gaussianCDF b - gaussianCDF a ≤ gaussianCDF b :=
          sub_le_self _ (cdf_nonneg (gaussianReal 0 1) a)
        _ ≤ gaussianCDF A := hmono hbA
        _ < ε / 4 := hA
        _ < ε := by linarith
    · by_cases hBa : B ≤ a
      · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hmono habOrder))]
        rw [neg_sub]
        calc
          gaussianCDF b - gaussianCDF a ≤ 1 - gaussianCDF a := by
            exact sub_le_sub_right (cdf_le_one (gaussianReal 0 1) b) _
          _ ≤ 1 - gaussianCDF B := by gcongr; exact hmono hBa
          _ < ε / 4 := by linarith
          _ < ε := by linarith
      · have hgap : b - a < 1 := by
          have habs : |a - b| < δ := by simpa [Real.dist_eq] using habDist
          rw [abs_of_nonpos (sub_nonpos.mpr habOrder)] at habs
          have hδone : δ ≤ 1 := min_le_right _ _
          linarith
        have haMem : a ∈ Set.Icc (A - 1) (B + 1) := by
          constructor
          · have : A < b := lt_of_not_ge hbA
            linarith
          · have : a < B := lt_of_not_ge hBa
            linarith
        have hbMem : b ∈ Set.Icc (A - 1) (B + 1) := by
          constructor
          · have : A < b := lt_of_not_ge hbA
            linarith
          · have : a < B := lt_of_not_ge hBa
            linarith
        exact hlocal a haMem b hbMem (habDist.trans_le (min_le_left _ _))
  rcases le_total a b with habOrder | hbaOrder
  · exact hordered habOrder hab
  · simpa [dist_comm] using hordered hbaOrder (by simpa [dist_comm] using hab)

/-- Probability of an event under a heterogeneous finite product law. -/
noncomputable def finiteProductEventProbability
    {n : ℕ} (A : Fin n → Type*) [∀ i, Fintype (A i)]
    (p : ∀ i, FinProb (A i)) (E : Set (∀ i, A i)) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω ↦ ω ∈ E), ∏ i, p i (ω i)

/-- **Fact 12 (Berry--Esseen).**  This is the equivalent upper-tail form of
equation (67) for independent finite-valued summands.  Independence is
represented by the product mass in `finiteProductEventProbability`; the
summands need not be identically distributed. -/
def paperFact12 : Prop :=
  ∃ CBE : ℝ, 0 ≤ CBE ∧
    ∀ (n : ℕ) (A : Fin n → Type u) [∀ i, Fintype (A i)]
      (p : ∀ i, FinProb (A i)) (W : ∀ i, A i → ℝ),
      (∀ i, (p i).expect (W i) = 0) →
      let B2 := ∑ i, (p i).expect (fun ω ↦ (W i ω) ^ 2)
      0 < B2 →
      ∀ t : ℝ,
        |finiteProductEventProbability A p
            {ω | -(t : ℝ) ≤ (∑ i, W i (ω i)) / Real.sqrt B2} -
              gaussianCDF t| ≤
          CBE * (∑ i, (p i).expect (fun ω ↦ |W i ω| ^ 3)) /
            (Real.sqrt B2) ^ 3

noncomputable def berryEsseenConstant (hBE : paperFact12.{u}) : ℝ :=
  Classical.choose hBE

theorem berryEsseenConstant_nonneg (hBE : paperFact12.{u}) :
    0 ≤ berryEsseenConstant hBE := (Classical.choose_spec hBE).1

theorem iid_event_eq_finiteProductEventProbability
    {A : Type*} [Fintype A] (p : FinProb A) (n : ℕ)
    (E : Set (Fin n → A)) :
    (p.iid n).event E = finiteProductEventProbability (fun _ : Fin n ↦ A)
      (fun _ ↦ p) E := by
  unfold FinProb.event finiteProductEventProbability
  rfl

/-- The finite i.i.d. specialization of Fact 12. -/
theorem iid_berryEsseen
    (hBE : paperFact12.{u}) {A : Type u} [Fintype A]
    (p : FinProb A) (W : A → ℝ) (hW : p.expect W = 0)
    (n : ℕ) (hn : 0 < n)
    (hvar : 0 < p.expect (fun a ↦ (W a) ^ 2)) (t : ℝ) :
    |(p.iid n).event
        {ω | -(t : ℝ) ≤ (∑ i, W (ω i)) /
          Real.sqrt ((n : ℝ) * p.expect (fun a ↦ (W a) ^ 2))} - gaussianCDF t| ≤
      berryEsseenConstant hBE *
        ((n : ℝ) * p.expect (fun a ↦ |W a| ^ 3)) /
          (Real.sqrt ((n : ℝ) * p.expect (fun a ↦ (W a) ^ 2))) ^ 3 := by
  have hB2 : 0 < (n : ℝ) * p.expect (fun a ↦ (W a) ^ 2) :=
    mul_pos (by exact_mod_cast hn) hvar
  have hraw := (Classical.choose_spec hBE).2 n (fun _ : Fin n ↦ A)
    (fun _ ↦ p) (fun _ ↦ W) (fun _ ↦ hW)
  dsimp only at hraw
  have hineq := hraw (by simpa using hB2) t
  simp only [Finset.sum_const, nsmul_eq_mul] at hineq
  rw [← iid_event_eq_finiteProductEventProbability p n] at hineq
  simpa [berryEsseenConstant, mul_comm] using hineq

/-- The `O(n⁻¹/²)` expression occurring in finite i.i.d. applications of
Fact 12 tends to zero. -/
theorem berryEsseen_iid_rate_tendsto_zero
    (hBE : paperFact12.{u}) (ρ v : ℝ) (hv : 0 < v) :
    Tendsto (fun n : ℕ ↦ berryEsseenConstant hBE * ((n : ℝ) * ρ) /
      (Real.sqrt ((n : ℝ) * v)) ^ 3) atTop (𝓝 0) := by
  let K := berryEsseenConstant hBE * ρ / (Real.sqrt v) ^ 3
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hsimple : Tendsto (fun n : ℕ ↦ K * (Real.sqrt (n : ℝ))⁻¹)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hinv
  apply hsimple.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsqrtn : (Real.sqrt (n : ℝ)) ^ 2 = n := by
    simpa using Real.sq_sqrt hnpos.le
  have hsqrtv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hsqrtmul : Real.sqrt ((n : ℝ) * v) =
      Real.sqrt (n : ℝ) * Real.sqrt v := Real.sqrt_mul hnpos.le v
  dsimp [K]
  rw [hsqrtmul]
  field_simp [Real.sqrt_ne_zero'.2 hnpos, hsqrtv.ne']
  rw [hsqrtn]

end RandomnessExtraction
