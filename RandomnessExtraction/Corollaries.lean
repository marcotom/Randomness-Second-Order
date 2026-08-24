import RandomnessExtraction.FixedLeakage

/-!
# Rényi and total-variation corollaries
-/

open Filter Set
open scoped Classical Topology

namespace RandomnessExtraction

open ConditionalLimit OneShot

set_option maxHeartbeats 800000

/-- The inverse of the Gaussian Rényi overlap profile from equation (19). -/
noncomputable def gaussianRenyiOverlapInverse
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (r u : ℝ) : ℝ :=
  gaussianProfileInverse (powerGenerator α hα0 hα1) r
    ((1 - u) / (1 - α))

theorem gaussianRenyiOverlapInverse_spec
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {r u : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hu0 : 0 < u) (hu1 : u < 1) :
    gaussianRenyiOverlap α hα0 hα1 r
      (gaussianRenyiOverlapInverse α hα0 hα1 r u) = u := by
  let f := powerGenerator α hα0 hα1
  let d := (1 - u) / (1 - α)
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  have hd0 : 0 < d := div_pos (sub_pos.mpr hu1) hden
  have hdf : d < f 0 := by
    rw [show f 0 = (1 - α)⁻¹ by exact powerGenerator_zero α hα0 hα1]
    dsimp [d]
    rw [div_eq_mul_inv]
    apply mul_lt_of_lt_one_left (inv_pos.mpr hden)
    linarith
  have hlevel := gaussianProfileInverse_spec f hr
    (powerGenerator_strictAntiOn α hα0 hα1) hd0 hdf
  change 1 - (1 - α) * gaussianProfile f r
    (gaussianProfileInverse f r d) = u
  rw [hlevel]
  dsimp [d]
  field_simp [hden.ne']
  ring

/-- The `f_α`-budget corresponding exactly to a Rényi-divergence budget. -/
noncomputable def renyiFBudget (α δ : ℝ) : ℝ :=
  (1 - (2 : ℝ) ^ (-(1 - α) * δ)) / (1 - α)

theorem renyiTransform_fBudget
    (α : ℝ) (hα1 : α < 1) (δ : ℝ) :
    renyiTransform α (renyiFBudget α δ) = δ := by
  have hden : 1 - α ≠ 0 := (sub_pos.mpr hα1).ne'
  have hu : 0 < (2 : ℝ) ^ (-(1 - α) * δ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have harg : 1 - (1 - α) * renyiFBudget α δ =
      (2 : ℝ) ^ (-(1 - α) * δ) := by
    unfold renyiFBudget
    field_simp [hden]
    ring
  rw [renyiTransform, harg,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
  field_simp [hden]

theorem renyiFBudget_lt_endpoint
    (α : ℝ) (hα1 : α < 1) (δ : ℝ) (hδ : 0 < δ) :
    renyiFBudget α δ < (1 - α)⁻¹ := by
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  have hu : 0 < (2 : ℝ) ^ (-(1 - α) * δ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  unfold renyiFBudget
  rw [div_lt_iff₀ hden, inv_mul_cancel₀ hden.ne']
  linarith

/-- Fixed-reference Rényi output length, defined directly by the native
Rényi leakage criterion and valued in `ℕ ∪ {+∞}`. -/
noncomputable def fixedRenyiLeakageLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (δ : ℝ) (P : FiniteSource X Y) : WithTop ℕ :=
  extendedNatSup {ell : ℕ | optimalFixedRenyiLeakage α hα0 hα1 P (2 ^ ell)
    (pow_pos (by omega) ell) ≤ δ}

/-- Optimized-reference Rényi output length under the native criterion. -/
noncomputable def optimizedRenyiLeakageLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (δ : ℝ) (P : FiniteSource X Y) : WithTop ℕ :=
  extendedNatSup {ell : ℕ | optimalOptimizedRenyiLeakage α hα0 hα1 P (2 ^ ell)
    (pow_pos (by omega) ell) ≤ δ}

theorem fixedRenyiLeakageLength_eq_fLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (δ : ℝ) (hδ : 0 < δ) (P : FiniteSource X Y) :
    fixedRenyiLeakageLength α hα0 hα1 δ P =
      fixedLeakageLength (powerGenerator α hα0 hα1)
        (renyiFBudget α δ) P := by
  unfold fixedRenyiLeakageLength fixedLeakageLength
  congr 1
  ext ell
  simp only [Set.mem_setOf_eq]
  rw [optimalFixedRenyiLeakage_eq_transform]
  let d := optimalFixedLeakage (powerGenerator α hα0 hα1) P (2 ^ ell)
  have hiff := renyiTransform_le_renyiTransform_iff α hα1
    (optimalFixedPowerLeakage_lt_endpoint α hα0 hα1 P (2 ^ ell)
      (pow_pos (by omega) ell))
    (renyiFBudget_lt_endpoint α hα1 δ hδ)
  constructor
  · intro h
    apply hiff.mp
    simpa only [renyiTransform_fBudget α hα1 δ] using h
  · intro h
    have := hiff.mpr h
    simpa only [renyiTransform_fBudget α hα1 δ] using this

theorem optimizedRenyiLeakageLength_eq_fLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (δ : ℝ) (hδ : 0 < δ) (P : FiniteSource X Y) :
    optimizedRenyiLeakageLength α hα0 hα1 δ P =
      optimizedLeakageLength (powerGenerator α hα0 hα1)
        (renyiFBudget α δ) P := by
  unfold optimizedRenyiLeakageLength optimizedLeakageLength
  congr 1
  ext ell
  simp only [Set.mem_setOf_eq]
  rw [optimalOptimizedRenyiLeakage_eq_transform]
  have hiff := renyiTransform_le_renyiTransform_iff α hα1
    (optimalOptimizedPowerLeakage_lt_endpoint α hα0 hα1 P (2 ^ ell)
      (pow_pos (by omega) ell))
    (renyiFBudget_lt_endpoint α hα1 δ hδ)
  constructor
  · intro h
    apply hiff.mp
    simpa only [renyiTransform_fBudget α hα1 δ] using h
  · intro h
    have := hiff.mpr h
    simpa only [renyiTransform_fBudget α hα1 δ] using this

/-- **Corollary 3 (Rényi specialization, fixed and optimized marginals).**
The first four conjuncts are the two constant-leakage limits and the two
fixed-error output-length expansions.  The last two state achievability by
every two-universal family and the converse for every seeded family. -/
theorem paperCorollary3
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L δ : ℝ)
    (hδ : 0 < δ) (hV : 0 < totalVariance P)
    (hRate : SecondOrderRate P M L) :
    Tendsto (fun n => optimalFixedRenyiLeakage α hα0 hα1
        (blockSource P n) (M n) (hM n)) atTop
      (nhds (-(1 / (1 - α)) * Real.logb 2
        (gaussianRenyiOverlap α hα0 hα1
          (variance₁ P / totalVariance P) (-L / Real.sqrt (totalVariance P))))) ∧
    Tendsto (fun n => optimalOptimizedRenyiLeakage α hα0 hα1
        (blockSource P n) (M n) (hM n)) atTop
      (nhds (-(α / (1 - α)) * Real.logb 2
        (gaussianCDF (-L / Real.sqrt (totalVariance P))))) ∧
    Tendsto (fun n =>
      ((((fixedRenyiLeakageLength α hα0 hα1 δ
          (blockSource P n)).untopD 0 : ℕ) : ℝ) -
        n * entropy P) / Real.sqrt n) atTop
      (nhds (-Real.sqrt (totalVariance P) *
        gaussianRenyiOverlapInverse α hα0 hα1
          (variance₁ P / totalVariance P)
          ((2 : ℝ) ^ (-(1 - α) * δ)))) ∧
    Tendsto (fun n =>
      ((((optimizedRenyiLeakageLength α hα0 hα1 δ
          (blockSource P n)).untopD 0 : ℕ) : ℝ) -
        n * entropy P) / Real.sqrt n) atTop
      (nhds (-Real.sqrt (totalVariance P) *
        gaussianRenyiOverlapInverse α hα0 hα1 0
          ((2 : ℝ) ^ (-(1 - α) * δ)))) ∧
    (∀ (N : ℕ → ℕ)
      (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n)),
      (∀ n, SeededHash.paperDefinition6 (H n)) →
      Tendsto (fun n ↦ fixedRenyiLeakage α
          (blockSource P n) (H n) (hM n)) atTop
        (nhds (-(1 / (1 - α)) * Real.logb 2
          (gaussianRenyiOverlap α hα0 hα1
            (variance₁ P / totalVariance P)
            (-L / Real.sqrt (totalVariance P))))) ∧
      Tendsto (fun n ↦ optimizedRenyiLeakage α
          (blockSource P n) (H n) (hM n)) atTop
        (nhds (-(α / (1 - α)) * Real.logb 2
          (gaussianCDF (-L / Real.sqrt (totalVariance P)))))) ∧
    (∀ (N : ℕ → ℕ)
      (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n)),
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        -(1 / (1 - α)) * Real.logb 2
            (gaussianRenyiOverlap α hα0 hα1
              (variance₁ P / totalVariance P)
              (-L / Real.sqrt (totalVariance P))) - ε ≤
          fixedRenyiLeakage α (blockSource P n) (H n) (hM n)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        -(α / (1 - α)) * Real.logb 2
            (gaussianCDF (-L / Real.sqrt (totalVariance P))) - ε ≤
          optimizedRenyiLeakage α (blockSource P n) (H n) (hM n))) := by
  have hleak := paperCorollary3_leakage hBE P hpY α hα0 hα1 M hM L hV hRate
  let u := (2 : ℝ) ^ (-(1 - α) * δ)
  have hu0 : 0 < u := Real.rpow_pos_of_pos (by norm_num) _
  have hexp : -(1 - α) * δ < 0 := mul_neg_of_neg_of_pos
    (neg_neg_of_pos (sub_pos.mpr hα1)) hδ
  have hu1 : u < 1 := by
    simpa [u] using Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : ℝ) < 2) hexp
  let d := renyiFBudget α δ
  have hd0 : 0 < d := div_pos (sub_pos.mpr hu1) (sub_pos.mpr hα1)
  have hdf : d < (powerGenerator α hα0 hα1) 0 := by
    rw [powerGenerator_zero]
    dsimp [d, renyiFBudget]
    rw [div_eq_mul_inv]
    apply mul_lt_of_lt_one_left (inv_pos.mpr (sub_pos.mpr hα1))
    change 1 - u < 1
    linarith
  have hlen := paperCorollary2 hBE (powerGenerator α hα0 hα1)
    (powerGenerator_strictAntiOn α hα0 hα1) P hpY d hd0 hdf hV
  refine ⟨hleak.1, hleak.2.1, ?_, ?_, hleak.2.2.1, hleak.2.2.2⟩
  · simpa [fixedRenyiLeakageLength_eq_fLength α hα0 hα1 δ hδ,
      gaussianRenyiOverlapInverse,
      d, u, renyiFBudget] using hlen.1
  · simpa [optimizedRenyiLeakageLength_eq_fLength α hα0 hα1 δ hδ,
      gaussianRenyiOverlapInverse,
      d, u, renyiFBudget] using hlen.2

/-- Standard Gaussian quantile, introduced globally through the unique
level-set point of the strictly increasing Gaussian CDF. -/
noncomputable def gaussianQuantile (u : ℝ) : ℝ :=
  gaussianProfileInverse totalVariationGenerator 0 (1 - u)

theorem gaussianQuantile_spec {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    gaussianCDF (gaussianQuantile u) = u := by
  have hlevel := gaussianProfileInverse_spec totalVariationGenerator
    (r := 0) (δ := 1 - u) (by constructor <;> norm_num)
    (by
      intro a ha b hb hab
      rw [totalVariationGenerator_of_mem_unit ⟨ha.1.le, ha.2.le⟩,
        totalVariationGenerator_of_mem_unit ⟨hb.1.le, hb.2.le⟩]
      linarith)
    (sub_pos.mpr hu1) (by
      rw [show totalVariationGenerator 0 = 1 by norm_num [totalVariationGenerator]]
      linarith)
  rw [gaussianProfile_zero, totalVariationGenerator_of_mem_unit
    (gaussianCDF_mem_unit _)] at hlevel
  unfold gaussianQuantile
  linarith

theorem gaussianQuantile_one_sub {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    gaussianQuantile (1 - u) = -gaussianQuantile u := by
  apply strictMono_gaussianCDF.injective
  rw [gaussianQuantile_spec (sub_pos.mpr hu1) (by linarith), gaussianCDF_neg,
    gaussianQuantile_spec hu0 hu1]

theorem totalVariation_profileInverse
    {r δ : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    gaussianProfileInverse totalVariationGenerator r δ =
      -gaussianQuantile δ := by
  apply (strictAnti_gaussianProfile totalVariationGenerator hr.1 hr.2 (by
    intro a ha b hb hab
    rw [totalVariationGenerator_of_mem_unit ⟨ha.1.le, ha.2.le⟩,
      totalVariationGenerator_of_mem_unit ⟨hb.1.le, hb.2.le⟩]
    linarith)).injective
  rw [gaussianProfileInverse_spec totalVariationGenerator hr (by
      intro a ha b hb hab
      rw [totalVariationGenerator_of_mem_unit ⟨ha.1.le, ha.2.le⟩,
        totalVariationGenerator_of_mem_unit ⟨hb.1.le, hb.2.le⟩]
      linarith) hδ0 (by
        rw [show totalVariationGenerator 0 = 1 by norm_num [totalVariationGenerator]]
        exact hδ1),
    gaussianProfile_totalVariation hr, gaussianCDF_neg,
    gaussianQuantile_spec hδ0 hδ1]
  ring

/-- Native total-variation output lengths (fixed and optimized reference). -/
noncomputable def fixedTotalVariationLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (δ : ℝ) (P : FiniteSource X Y) : WithTop ℕ :=
  extendedNatSup {ell : ℕ |
    optimalFixedTotalVariationLeakage P (2 ^ ell) (pow_pos (by omega) ell) ≤ δ}

noncomputable def optimizedTotalVariationLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (δ : ℝ) (P : FiniteSource X Y) : WithTop ℕ :=
  extendedNatSup {ell : ℕ |
    optimalOptimizedTotalVariationLeakage P (2 ^ ell) (pow_pos (by omega) ell) ≤ δ}

theorem fixedTotalVariationLength_eq_fLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (δ : ℝ) (P : FiniteSource X Y) :
    fixedTotalVariationLength δ P =
      fixedLeakageLength totalVariationGenerator δ P := by
  unfold fixedTotalVariationLength fixedLeakageLength
  congr 1
  ext ell
  simp only [Set.mem_setOf_eq]
  rw [optimalFixedTotalVariationLeakage_eq_fLeakage]

theorem optimizedTotalVariationLength_eq_fLength
    {X Y : Type} [Fintype X] [Fintype Y]
    (δ : ℝ) (P : FiniteSource X Y) :
    optimizedTotalVariationLength δ P =
      optimizedLeakageLength totalVariationGenerator δ P := by
  unfold optimizedTotalVariationLength optimizedLeakageLength
  congr 1
  ext ell
  simp only [Set.mem_setOf_eq]
  rw [optimalOptimizedTotalVariationLeakage_eq_fLeakage]

/-- **Corollary 4 (total variation).** -/
theorem paperCorollary4
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hV : 0 < totalVariance P) (hRate : SecondOrderRate P M L) :
    Tendsto (fun n => optimalFixedTotalVariationLeakage
        (blockSource P n) (M n) (hM n)) atTop
      (nhds (gaussianCDF (L / Real.sqrt (totalVariance P)))) ∧
    Tendsto (fun n => optimalOptimizedTotalVariationLeakage
        (blockSource P n) (M n) (hM n)) atTop
      (nhds (gaussianCDF (L / Real.sqrt (totalVariance P)))) ∧
    Tendsto (fun n =>
      ((((fixedTotalVariationLength δ
          (blockSource P n)).untopD 0 : ℕ) : ℝ) - n * entropy P) /
        Real.sqrt n) atTop
      (nhds (Real.sqrt (totalVariance P) * gaussianQuantile δ)) ∧
    Tendsto (fun n =>
      ((((optimizedTotalVariationLength δ
          (blockSource P n)).untopD 0 : ℕ) : ℝ) - n * entropy P) /
        Real.sqrt n) atTop
      (nhds (Real.sqrt (totalVariance P) * gaussianQuantile δ)) ∧
    (∀ (N : ℕ → ℕ)
      (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n)),
      (∀ n, SeededHash.paperDefinition6 (H n)) →
      Tendsto (fun n ↦ fixedTotalVariationLeakage
          (blockSource P n) (H n) (hM n)) atTop
        (nhds (gaussianCDF (L / Real.sqrt (totalVariance P)))) ∧
      Tendsto (fun n ↦ optimizedTotalVariationLeakage
          (blockSource P n) (H n) (hM n)) atTop
        (nhds (gaussianCDF (L / Real.sqrt (totalVariance P))))) ∧
    (∀ (N : ℕ → ℕ)
      (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n)),
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        gaussianCDF (L / Real.sqrt (totalVariance P)) - ε ≤
          fixedTotalVariationLeakage
            (blockSource P n) (H n) (hM n)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        gaussianCDF (L / Real.sqrt (totalVariance P)) - ε ≤
          optimizedTotalVariationLeakage
            (blockSource P n) (H n) (hM n))) := by
  have hleak := paperCorollary4_leakage hBE P hpY M hM L hV hRate
  have hstrict : StrictAntiOn totalVariationGenerator (Set.Ioo 0 1) := by
    intro a ha b hb hab
    rw [totalVariationGenerator_of_mem_unit ⟨ha.1.le, ha.2.le⟩,
      totalVariationGenerator_of_mem_unit ⟨hb.1.le, hb.2.le⟩]
    linarith
  have hlen := paperCorollary2 hBE totalVariationGenerator hstrict P hpY δ
    hδ0 (by
      rw [show totalVariationGenerator 0 = 1 by norm_num [totalVariationGenerator]]
      exact hδ1) hV
  have hr := varianceRatio_mem_unit P hV
  refine ⟨hleak.1, hleak.2.1, ?_, ?_, hleak.2.2.1, hleak.2.2.2⟩
  · have hfixed := hlen.1
    rw [totalVariation_profileInverse
      (r := variance₁ P / totalVariance P) (δ := δ) hr hδ0 hδ1] at hfixed
    convert hfixed using 1 <;> simp [fixedTotalVariationLength_eq_fLength]
  · have hopt := hlen.2
    rw [totalVariation_profileInverse (r := 0) (δ := δ)
      (by constructor <;> norm_num) hδ0 hδ1] at hopt
    convert hopt using 1 <;> simp [optimizedTotalVariationLength_eq_fLength]

end RandomnessExtraction
