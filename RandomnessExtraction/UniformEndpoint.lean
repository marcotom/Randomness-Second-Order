import RandomnessExtraction.PerspectiveAggregation
import RandomnessExtraction.WaterFilling
import Mathlib.Tactic.Linarith

/-!
# The uniform-fibre endpoint

This file formalizes Lemma 16.  The endpoint `V₂ = 0` is treated directly:
positive conditional fibres are uniform, so both the capped program and the
conditional tail reduce to scalar functions of the outer conditional-entropy
fluctuation.
-/

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

namespace UniformEndpoint

open ConditionalLimit ConditionalCapped

variable {X Y : Type} [Fintype X] [Fintype Y]

theorem fiberVariance_eq_zero_of_variance₂_eq_zero
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) (y : Y) : fiberVariance P y = 0 := by
  have hterm : P.marginal y * fiberVariance P y ≤ variance₂ P := by
    rw [variance₂, FinProb.expect]
    exact Finset.single_le_sum
      (fun z _ ↦ mul_nonneg (P.marginal.nonneg z) (fiberVariance_nonneg P z))
      (Finset.mem_univ y)
  have hprod : P.marginal y * fiberVariance P y = 0 := by
    apply le_antisymm
    · simpa [hV2] using hterm
    · exact mul_nonneg (P.marginal.nonneg y) (fiberVariance_nonneg P y)
  exact (mul_eq_zero.mp hprod).resolve_left (hpY y).ne'

/-- A zero-variance positive fibre is uniform on its positive support. -/
theorem conditional_uniform_on_support
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) (y : Y) (z : Support (P.conditional y)) :
    (Fintype.card (Support (P.conditional y)) : ℝ) *
      P.conditional y z.1 = 1 := by
  let p := P.conditional y
  have hv := fiberVariance_eq_zero_of_variance₂_eq_zero P hpY hV2 y
  have hinfo (w : Support p) : information P w.1 y = fiberEntropy P y := by
    have hzeroTerm : p w.1 * (information P w.1 y - fiberEntropy P y) ^ 2 = 0 := by
      have hterms : ∀ x ∈ (Finset.univ : Finset X),
          0 ≤ p x * (information P x y - fiberEntropy P y) ^ 2 :=
        fun x _ ↦ mul_nonneg (p.nonneg x) (sq_nonneg _)
      have hsum : ∑ x, p x * (information P x y - fiberEntropy P y) ^ 2 = 0 := by
        simpa [fiberVariance, FinProb.expect, p] using hv
      exact (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum w.1 (Finset.mem_univ _)
    have hsquare : (information P w.1 y - fiberEntropy P y) ^ 2 = 0 :=
      (mul_eq_zero.mp hzeroTerm).resolve_left w.2.ne'
    nlinarith [sq_nonneg (information P w.1 y - fiberEntropy P y)]
  have hprobEq (w : Support p) : p w.1 = p z.1 := by
    apply Real.logb_injOn_pos (by norm_num : (1 : ℝ) < 2) w.2 z.2
    have hw := hinfo w
    have hz := hinfo z
    dsimp [information] at hw hz
    linarith
  have hsum : ∑ w : Support p, p w.1 = 1 := (supportLaw p).sum_prob
  have hcard :
      (Fintype.card (Support p) : ℝ) * p z.1 = 1 := by
    calc
      (Fintype.card (Support p) : ℝ) * p z.1 =
          ∑ _w : Support p, p z.1 := by simp
      _ = ∑ w : Support p, p w.1 := by
        apply Finset.sum_congr rfl
        intro w _
        exact (hprobEq w).symm
      _ = 1 := hsum
  simpa [p] using hcard

theorem conditional_probability_eq_inv_card
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) (y : Y) (z : Support (P.conditional y)) :
    P.conditional y z.1 =
      (Fintype.card (Support (P.conditional y)) : ℝ)⁻¹ := by
  have hN : (Fintype.card (Support (P.conditional y)) : ℝ) ≠ 0 := by
    exact_mod_cast (support_card_pos (P.conditional y)).ne'
  have h := conditional_uniform_on_support P hpY hV2 y z
  field_simp [hN]
  simpa [mul_comm] using h

theorem information_eq_logb_card
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) (y : Y) (z : Support (P.conditional y)) :
    information P z.1 y =
      Real.logb 2 (Fintype.card (Support (P.conditional y))) := by
  rw [information, conditional_probability_eq_inv_card P hpY hV2 y z,
    Real.logb_inv]
  ring

theorem fiberEntropy_eq_logb_card
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) (y : Y) :
    fiberEntropy P y =
      Real.logb 2 (Fintype.card (Support (P.conditional y))) := by
  rw [fiberEntropy, expect_eq_support]
  simp_rw [information_eq_logb_card P hpY hV2]
  rw [← Finset.sum_mul]
  have hsum : ∑ z : Support (P.conditional y), P.conditional y z.1 = 1 :=
    (supportLaw (P.conditional y)).sum_prob
  rw [hsum, one_mul]

theorem fiberSupportLaw_uniform
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) {n : ℕ} (y : Fin n → Y)
    (z : FiberSupport P y) :
    fiberSupportLaw P y z =
      (Fintype.card (FiberSupport P y) : ℝ)⁻¹ := by
  rw [fiberSupportLaw_apply]
  simp_rw [conditional_probability_eq_inv_card P hpY hV2]
  rw [Finset.prod_inv_distrib]
  rw [← fiberSupport_card]

theorem fiberSurprisal_eq_conditionalMean
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) {n : ℕ} (y : Fin n → Y)
    (z : FiberSupport P y) :
    fiberSurprisal P y z = conditionalMean P y := by
  rw [fiberSurprisal, conditionalMean]
  apply Finset.sum_congr rfl
  intro i _
  rw [information_eq_logb_card P hpY hV2,
    fiberEntropy_eq_logb_card P hpY hV2]

section UniformCapped

variable {A : Type} [Fintype A]

/-- Equation (97): the capped program for a uniform positive law. -/
theorem cappedValue_uniform_exact (f : AdmissibleGenerator)
    (p : FinProb A) (hp : ∀ a, 0 < p a)
    (hunif : ∀ a, (Fintype.card A : ℝ) * p a = 1)
    (c : ℝ) (hc : 0 < c) :
    cappedValue f c p =
      if 1 ≤ c * Fintype.card A then 0
      else (c * Fintype.card A) * f (1 / (c * Fintype.card A)) +
        (1 - c * Fintype.card A) * f 0 := by
  let N : ℝ := Fintype.card A
  have hNnat : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨Classical.choice
    (show Nonempty A by
      by_contra hnone
      have : ∑ a : A, p a = 0 := by simp_all
      linarith [p.sum_prob])⟩
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hNnat
  have hpEq (a : A) : p a = N⁻¹ := by
    have h := hunif a
    dsimp [N]
    field_simp [hN.ne']
    simpa [mul_comm] using h
  by_cases hcard : 1 ≤ c * Fintype.card A
  · rw [if_pos hcard]
    let qstar : CappedVector A c :=
      { mass := p
        nonneg := p.nonneg
        le_cap := by
          intro a
          have hmul := hcard
          rw [show p a = N⁻¹ by exact hpEq a]
          apply (inv_le_iff_one_le_mul₀ hN).2
          dsimp [N] at hmul ⊢
          simpa [mul_comm] using hmul
        sum_le_one := p.sum_prob.le }
    have hlower : 0 ≤ cappedValue f c p := by
      simpa [cappedValue, f.map_one] using
        CappedCost.scaledCappedValue_lower f 1 c (by norm_num) hc.le p
    have hupper : cappedValue f c p ≤ 0 := by
      have hv := CappedCost.scaledCappedValue_le_cost f 1 c (by norm_num) p qstar
      have hcost : scaledCappedCost f 1 p qstar = 0 := by
        rw [scaledCappedCost]
        simp only [one_mul]
        have hsum : ∑ a, perspective f (p a) (p a) = 0 := by
          apply Finset.sum_eq_zero
          intro a _
          exact perspective_self f (p.nonneg a)
        change (∑ a, perspective f (p a) (p a)) +
          (1 - ∑ a, p a) * f 0 = 0
        rw [hsum, p.sum_prob]
        ring
      simpa [cappedValue, hcost] using hv
    exact le_antisymm hupper hlower
  · have hcardLt : c * Fintype.card A < 1 := lt_of_not_ge hcard
    rw [if_neg hcard]
    let qstar := WaterFilling.allCappedVector c hc.le hcardLt.le
    have hopt := (WaterFilling.paperLemma9 c hc p hp).2 hcardLt f 1 (by norm_num)
    have hvalue := CappedCost.scaledCappedValue_eq_cost_of_optimizer
      f 1 c (by norm_num) hc.le p qstar hopt
    rw [cappedValue, hvalue]
    have hsumq : ∑ a, qstar a = c * Fintype.card A := by
      simp [qstar, WaterFilling.allCappedVector, mul_comm]
    rw [scaledCappedCost, hsumq]
    have hpersp (a : A) : perspective f (1 * p a) (qstar a) =
        c * f (1 / (c * Fintype.card A)) := by
      have hden : c * (Fintype.card A : ℝ) ≠ 0 :=
        mul_ne_zero hc.ne' (by exact_mod_cast hNnat.ne')
      change perspective f (1 * p a) c =
        c * f (1 / (c * Fintype.card A))
      rw [perspective_of_pos f hc]
      simp only [one_mul]
      rw [hpEq]
      congr 1
      dsimp [N]
      field_simp [hc.ne', hden]
    simp_rw [hpersp]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring

/-- The scaled form of equation (97), used by the optimized-reference
endpoint argument. -/
theorem scaledCappedValue_uniform_exact (f : AdmissibleGenerator)
    (p : FinProb A) (hp : ∀ a, 0 < p a)
    (hunif : ∀ a, (Fintype.card A : ℝ) * p a = 1)
    (a c : ℝ) (ha : 0 ≤ a) (hc : 0 < c) :
    scaledCappedValue f a c p =
      if 1 ≤ c * Fintype.card A then f a
      else (c * Fintype.card A) * f (a / (c * Fintype.card A)) +
        (1 - c * Fintype.card A) * f 0 := by
  by_cases haZero : a = 0
  · subst a
    have hb := TailLimit.scaled_bounds f 0 c le_rfl hc.le p
    have hv : scaledCappedValue f 0 c p = f 0 := le_antisymm hb.2 hb.1
    rw [hv]
    by_cases hcard : 1 ≤ c * Fintype.card A
    · simp [hcard]
    · simp [hcard]
      ring
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm haZero)
  let N : ℝ := Fintype.card A
  have hNnat : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨Classical.choice
    (show Nonempty A by
      by_contra hnone
      have : ∑ z : A, p z = 0 := by simp_all
      linarith [p.sum_prob])⟩
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hNnat
  have hpEq (z : A) : p z = N⁻¹ := by
    have h := hunif z
    dsimp [N]
    field_simp [hN.ne']
    simpa [mul_comm] using h
  by_cases hcard : 1 ≤ c * Fintype.card A
  · rw [if_pos hcard]
    let qstar : CappedVector A c :=
      { mass := p
        nonneg := p.nonneg
        le_cap := by
          intro z
          rw [show p z = N⁻¹ by exact hpEq z]
          apply (inv_le_iff_one_le_mul₀ hN).2
          dsimp [N] at hcard ⊢
          simpa [mul_comm] using hcard
        sum_le_one := p.sum_prob.le }
    have hlower : f a ≤ scaledCappedValue f a c p :=
      CappedCost.scaledCappedValue_lower f a c ha hc.le p
    have hupper : scaledCappedValue f a c p ≤ f a := by
      have hv := CappedCost.scaledCappedValue_le_cost f a c ha p qstar
      have hcost : scaledCappedCost f a p qstar = f a := by
        rw [scaledCappedCost]
        have hsum : ∑ z, perspective f (a * p z) (p z) = f a := by
          calc
            (∑ z, perspective f (a * p z) (p z)) =
                ∑ z, p z * f a := by
                  apply Finset.sum_congr rfl
                  intro z _
                  rw [perspective_of_pos f (hp z)]
                  congr 1
                  field_simp [(hp z).ne']
            _ = f a := by rw [← Finset.sum_mul, p.sum_prob, one_mul]
        change (∑ z, perspective f (a * p z) (p z)) +
          (1 - ∑ z, p z) * f 0 = f a
        rw [hsum, p.sum_prob]
        ring
      simpa [hcost] using hv
    exact le_antisymm hupper hlower
  · have hcardLt : c * Fintype.card A < 1 := lt_of_not_ge hcard
    rw [if_neg hcard]
    let qstar := WaterFilling.allCappedVector c hc.le hcardLt.le
    have hopt := (WaterFilling.paperLemma9 c hc p hp).2 hcardLt f a haPos
    have hvalue := CappedCost.scaledCappedValue_eq_cost_of_optimizer
      f a c ha hc.le p qstar hopt
    rw [hvalue]
    have hsumq : ∑ z, qstar z = c * Fintype.card A := by
      simp [qstar, WaterFilling.allCappedVector, mul_comm]
    rw [scaledCappedCost, hsumq]
    have hpersp (z : A) : perspective f (a * p z) (qstar z) =
        c * f (a / (c * Fintype.card A)) := by
      have hden : c * (Fintype.card A : ℝ) ≠ 0 :=
        mul_ne_zero hc.ne' (by exact_mod_cast hNnat.ne')
      change perspective f (a * p z) c =
        c * f (a / (c * Fintype.card A))
      rw [perspective_of_pos f hc]
      rw [hpEq]
      congr 1
      dsimp [N]
      field_simp [hc.ne', hden]
    simp_rw [hpersp]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring

end UniformCapped

/-- Capped value of a conditional endpoint fibre, in scalar form. -/
theorem fiberCappedValue_uniform_exact (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) {n : ℕ} (y : Fin n → Y) (x : ℝ) :
    fiberScaledCappedValue f P y x 1 =
      if 1 ≤ (2 : ℝ) ^ (-threshold P n x) *
          Fintype.card (FiberSupport P y) then 0
      else ((2 : ℝ) ^ (-threshold P n x) *
          Fintype.card (FiberSupport P y)) *
            f (1 / ((2 : ℝ) ^ (-threshold P n x) *
              Fintype.card (FiberSupport P y))) +
          (1 - (2 : ℝ) ^ (-threshold P n x) *
            Fintype.card (FiberSupport P y)) * f 0 := by
  unfold fiberScaledCappedValue
  change cappedValue f ((2 : ℝ) ^ (-threshold P n x)) (fiberSupportLaw P y) = _
  simpa only [one_mul] using cappedValue_uniform_exact f (fiberSupportLaw P y)
    (fiberSupportLaw_pos P y) (fun z ↦ by
      have h := fiberSupportLaw_uniform P hpY hV2 y z
      have hcard : (Fintype.card (FiberSupport P y) : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_pos_iff.mpr ⟨z⟩).ne'
      rw [h]
      exact mul_inv_cancel₀ hcard)
    ((2 : ℝ) ^ (-threshold P n x)) (Real.rpow_pos_of_pos (by norm_num) _)

noncomputable def endpointScale (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ (conditionalMean P y - threshold P n x)

noncomputable def endpointProfile (f : AdmissibleGenerator) (t : ℝ) : ℝ :=
  if 0 ≤ t then 0
  else (2 : ℝ) ^ t * f ((2 : ℝ) ^ (-t)) +
    (1 - (2 : ℝ) ^ t) * f 0

theorem fiberSupport_card_eq_rpow_conditionalMean
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) {n : ℕ} (y : Fin n → Y) :
    (Fintype.card (FiberSupport P y) : ℝ) =
      (2 : ℝ) ^ (conditionalMean P y) := by
  have hcard : 0 < (Fintype.card (FiberSupport P y) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun i ↦ Classical.choice
      (support_nonempty (P.conditional (y i)))⟩)
  calc
    (Fintype.card (FiberSupport P y) : ℝ) =
        (2 : ℝ) ^ Real.logb 2 (Fintype.card (FiberSupport P y)) := by
      exact (Real.rpow_logb (by norm_num) (by norm_num) hcard).symm
    _ = (2 : ℝ) ^ (conditionalMean P y) := by
      congr 1
      rw [logb_fiberSupport_card, conditionalMean]
      apply Finset.sum_congr rfl
      intro i _
      exact (fiberEntropy_eq_logb_card P hpY hV2 (y i)).symm

theorem cappedScale_eq_endpointScale
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) {n : ℕ} (y : Fin n → Y) (x : ℝ) :
    (2 : ℝ) ^ (-threshold P n x) * Fintype.card (FiberSupport P y) =
      endpointScale P y x := by
  rw [fiberSupport_card_eq_rpow_conditionalMean P hpY hV2]
  rw [← Real.rpow_add (by norm_num)]
  unfold endpointScale
  congr 1
  ring

/-- General-scale version of the uniform-fibre identity. -/
theorem fiberScaledCappedValue_uniform_exact (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) {n : ℕ} (y : Fin n → Y) (x a : ℝ)
    (ha : 0 ≤ a) :
    fiberScaledCappedValue f P y x a =
      if 1 ≤ endpointScale P y x then f a
      else endpointScale P y x * f (a / endpointScale P y x) +
        (1 - endpointScale P y x) * f 0 := by
  unfold fiberScaledCappedValue
  rw [scaledCappedValue_uniform_exact f (fiberSupportLaw P y)
    (fiberSupportLaw_pos P y) (fun z ↦ by
      have h := fiberSupportLaw_uniform P hpY hV2 y z
      have hcard : (Fintype.card (FiberSupport P y) : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_pos_iff.mpr ⟨z⟩).ne'
      rw [h]
      exact mul_inv_cancel₀ hcard)
    a ((2 : ℝ) ^ (-threshold P n x)) ha
    (Real.rpow_pos_of_pos (by norm_num) _)]
  rw [cappedScale_eq_endpointScale P hpY hV2]

theorem fiberCappedValue_eq_endpointProfile (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) {n : ℕ} (y : Fin n → Y) (x : ℝ) :
    fiberScaledCappedValue f P y x 1 =
      endpointProfile f (conditionalMean P y - threshold P n x) := by
  rw [fiberCappedValue_uniform_exact f P hpY hV2 y x]
  rw [cappedScale_eq_endpointScale P hpY hV2]
  unfold endpointScale endpointProfile
  by_cases ht : 0 ≤ conditionalMean P y - threshold P n x
  · rw [if_pos ht]
    rw [if_pos]
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 ht
  · rw [if_neg ht]
    rw [if_neg]
    · congr 2
      rw [one_div, Real.rpow_neg (by norm_num)]
    · intro hone
      have := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1
        (show (2 : ℝ) ^ 0 ≤
          (2 : ℝ) ^ (conditionalMean P y - threshold P n x) by simpa using hone)
      exact ht this

theorem endpointProfile_tendsto_atBot (f : AdmissibleGenerator) :
    Tendsto (endpointProfile f) atBot (𝓝 (f 0)) := by
  have ha : Tendsto (fun t : ℝ ↦ (2 : ℝ) ^ t) atBot (𝓝 0) :=
    tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)
  have hu : Tendsto (fun t : ℝ ↦ (2 : ℝ) ^ (-t)) atBot atTop :=
    (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
      tendsto_neg_atBot_atTop
  have hfirst : Tendsto
      (fun t : ℝ ↦ f ((2 : ℝ) ^ (-t)) / (2 : ℝ) ^ (-t)) atBot (𝓝 0) :=
    f.sublinear_atTop.comp hu
  have hsecond : Tendsto
      (fun t : ℝ ↦ (1 - (2 : ℝ) ^ t) * f 0) atBot (𝓝 (f 0)) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atBot (𝓝 1) := tendsto_const_nhds
    simpa using (hone.sub ha).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ f 0) atBot (𝓝 (f 0)))
  have hsum : Tendsto
      (fun t : ℝ ↦ f ((2 : ℝ) ^ (-t)) / (2 : ℝ) ^ (-t) +
        (1 - (2 : ℝ) ^ t) * f 0) atBot (𝓝 (f 0)) := by
    simpa only [zero_add] using hfirst.add hsecond
  apply hsum.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  rw [endpointProfile, if_neg (not_le.mpr ht)]
  congr 1
  rw [Real.rpow_neg (by norm_num)]
  have hpow : (2 : ℝ) ^ t ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp [hpow]

theorem endpointProfile_of_nonneg (f : AdmissibleGenerator) {t : ℝ}
    (ht : 0 ≤ t) : endpointProfile f t = 0 := by
  simp [endpointProfile, ht]

theorem endpointExponent_eq (P : FiniteSource X Y) {n : ℕ} (hn : 0 < n)
    (y : Fin n → Y) (x : ℝ) :
    conditionalMean P y - threshold P n x =
      Real.sqrt n * (x * Real.sqrt (totalVariance P) + center P y) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrtNV : Real.sqrt ((n : ℝ) * totalVariance P) =
      Real.sqrt n * Real.sqrt (totalVariance P) :=
    Real.sqrt_mul hnR.le _
  rw [threshold, ConditionalLimit.center, hsqrtNV]
  field_simp [hsqrtn.ne']
  ring

noncomputable def endpointCappedAverage (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (n : ℕ) (x : ℝ) : ℝ :=
  (P.marginal.iid n).expect fun y ↦ fiberScaledCappedValue f P y x 1

noncomputable def shiftedConditionalTail (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x shift : ℝ) : ℝ :=
  (conditionalProduct P y).event
    {z | threshold P n x + shift ≤ blockInformation P z y}

noncomputable def endpointShiftedTailAverage (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (n : ℕ) (x shift : ℝ) : ℝ :=
  (P.marginal.iid n).expect fun y ↦ f (shiftedConditionalTail P y x shift)

theorem expect_indicator {A : Type} [Fintype A]
    (p : FinProb A) (S : Set A) (c : ℝ) :
    p.expect (fun a ↦ if a ∈ S then c else 0) = c * p.event S := by
  classical
  rw [FinProb.expect, FinProb.event]
  simp only [Finset.sum_filter]
  calc
    (∑ a, p a * if a ∈ S then c else 0) =
        ∑ a, if a ∈ S then p a * c else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ S <;> simp [ha]
    _ = c * ∑ a, if a ∈ S then p a else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ S <;> simp [ha, mul_comm]

theorem fiberCappedValue_nonneg (f : AdmissibleGenerator)
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) (x : ℝ) :
    0 ≤ fiberScaledCappedValue f P y x 1 := by
  simpa [fiberScaledCappedValue, f.map_one] using
    (TailLimit.scaled_bounds f 1 ((2 : ℝ) ^ (-threshold P n x))
      (by norm_num) (Real.rpow_nonneg (by norm_num) _) (fiberSupportLaw P y)).1

theorem fiberCappedValue_le_map_zero (f : AdmissibleGenerator)
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) (x : ℝ) :
    fiberScaledCappedValue f P y x 1 ≤ f 0 := by
  simpa [fiberScaledCappedValue] using
    (TailLimit.scaled_bounds f 1 ((2 : ℝ) ^ (-threshold P n x))
      (by norm_num) (Real.rpow_nonneg (by norm_num) _) (fiberSupportLaw P y)).2

theorem centerCDF_tendsto_standard
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV2 : variance₂ P = 0)
    (hV : 0 < totalVariance P) (u : ℝ) :
    Tendsto (fun n ↦ (P.marginal.iid n).event
      {y | center P y ≤ -u * Real.sqrt (totalVariance P)}) atTop
      (𝓝 (gaussianCDF (-u))) := by
  have hV1 : variance₁ P = totalVariance P := by
    rw [totalVariance, hV2, add_zero]
  have hV1pos : 0 < variance₁ P := by rwa [hV1]
  have hraw := center_tendstoGaussianCDF hBE P hpY
    (-u * Real.sqrt (totalVariance P)) (Or.inr hV1pos.ne')
  simp only [if_neg hV1pos.ne'] at hraw
  have hsqrt : Real.sqrt (variance₁ P) = Real.sqrt (totalVariance P) := by rw [hV1]
  have hsqrtV : 0 < Real.sqrt (totalVariance P) := Real.sqrt_pos.2 hV
  rw [hsqrt] at hraw
  convert hraw using 1
  field_simp [hsqrtV.ne']

theorem endpointCappedAverage_tendsto
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) (hV : 0 < totalVariance P) (x : ℝ) :
    Tendsto (fun n ↦ endpointCappedAverage f P n x) atTop
      (𝓝 (f 0 * gaussianCDF (-x))) := by
  by_cases hf0 : f 0 = 0
  · have hzero : ∀ n, endpointCappedAverage f P n x = 0 := by
      intro n
      apply le_antisymm
      · calc
          endpointCappedAverage f P n x ≤
              (P.marginal.iid n).expect (fun _ ↦ (0 : ℝ)) := by
            apply (P.marginal.iid n).expect_mono
            intro y
            simpa [hf0] using fiberCappedValue_le_map_zero f P y x
          _ = 0 := (P.marginal.iid n).expect_const 0
      · exact (P.marginal.iid n).expect_nonneg
          (fun y ↦ fiberCappedValue_nonneg f P y x)
    simp_rw [hzero, hf0, zero_mul]
    exact tendsto_const_nhds
  · have hf0pos : 0 < f 0 := lt_of_le_of_ne f.map_zero_nonneg (Ne.symm hf0)
    have hsqrtV : 0 < Real.sqrt (totalVariance P) := Real.sqrt_pos.2 hV
    rw [Metric.tendsto_nhds]
    intro ε hε
    let e := min (ε / 8) (f 0 / 2)
    have he : 0 < e := lt_min (div_pos hε (by norm_num))
      (div_pos hf0pos (by norm_num))
    have heε : e ≤ ε / 8 := min_le_left _ _
    have hef : e ≤ f 0 / 2 := min_le_right _ _
    have hfe0 : 0 ≤ f 0 - e := by linarith
    have hprof := (endpointProfile_tendsto_atBot f).eventually
      (Metric.ball_mem_nhds (f 0) he)
    have hprof' : ∀ᶠ t : ℝ in atBot, |endpointProfile f t - f 0| < e := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hprof
    obtain ⟨T, hT⟩ := eventually_atBot.1 hprof'
    let γ := ε / (16 * f 0)
    have hγ : 0 < γ := div_pos hε (mul_pos (by norm_num) hf0pos)
    obtain ⟨d, hd, hPhiCont⟩ :=
      (Metric.continuousAt_iff.mp continuous_gaussianCDF.continuousAt) γ hγ
    let s := min (d / 2) 1
    have hs : 0 < s := lt_min (div_pos hd (by norm_num)) zero_lt_one
    have hsd : s < d :=
      (min_le_left (d / 2) 1).trans_lt (by linarith)
    have hPhiClose : |gaussianCDF (-(x + s)) - gaussianCDF (-x)| < γ := by
      have hdist : dist (-(x + s)) (-x) < d := by
        rw [Real.dist_eq]
        have hsub : -(x + s) - -x = -s := by ring
        have : |-(x + s) - -x| = s := by rw [hsub, abs_neg, abs_of_nonneg hs.le]
        rw [this]
        exact hsd
      simpa [Real.dist_eq] using hPhiCont hdist
    have hCDFupper := centerCDF_tendsto_standard hBE P hpY hV2 hV x
    have hCDFlower := centerCDF_tendsto_standard hBE P hpY hV2 hV (x + s)
    have hprobUpper : ∀ᶠ n in atTop,
        (P.marginal.iid n).event
          {y | center P y ≤ -x * Real.sqrt (totalVariance P)} <
            gaussianCDF (-x) + γ :=
      (tendsto_order.1 hCDFupper).2 _ (by linarith)
    have hprobLower : ∀ᶠ n in atTop,
        gaussianCDF (-(x + s)) - γ <
          (P.marginal.iid n).event
            {y | center P y ≤ -(x + s) * Real.sqrt (totalVariance P)} :=
      (tendsto_order.1 hCDFlower).1 _ (by linarith)
    have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hsqrtEv : ∀ᶠ n : ℕ in atTop,
        -T / (s * Real.sqrt (totalVariance P)) ≤ Real.sqrt (n : ℝ) :=
      hsqrt.eventually (eventually_ge_atTop _)
    filter_upwards [hprobUpper, hprobLower, hsqrtEv, eventually_gt_atTop (0 : ℕ)]
      with n hpu hpl hsqrtn hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsqrtn0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
    have hsqrtBound : -T ≤ Real.sqrt (n : ℝ) *
        (s * Real.sqrt (totalVariance P)) := by
      have hmul := mul_le_mul_of_nonneg_right hsqrtn
        (mul_nonneg hs.le hsqrtV.le)
      have hden : s * Real.sqrt (totalVariance P) ≠ 0 :=
        mul_ne_zero hs.ne' hsqrtV.ne'
      field_simp [hden] at hmul
      nlinarith
    let Slow : Set (Fin n → Y) :=
      {y | center P y ≤ -(x + s) * Real.sqrt (totalVariance P)}
    let Sup : Set (Fin n → Y) :=
      {y | center P y ≤ -x * Real.sqrt (totalVariance P)}
    have hpointLower (y : Fin n → Y) :
        (if y ∈ Slow then f 0 - e else 0) ≤
          fiberScaledCappedValue f P y x 1 := by
      by_cases hy : y ∈ Slow
      · rw [if_pos hy, fiberCappedValue_eq_endpointProfile f P hpY hV2]
        have hinside : x * Real.sqrt (totalVariance P) + center P y ≤
            -(s * Real.sqrt (totalVariance P)) := by
          change center P y ≤ -(x + s) * Real.sqrt (totalVariance P) at hy
          nlinarith
        have hexp : conditionalMean P y - threshold P n x ≤ T := by
          rw [endpointExponent_eq P hn y x]
          have hmul := mul_le_mul_of_nonneg_left hinside hsqrtn0.le
          nlinarith
        have hnear := hT _ hexp
        linarith [abs_lt.mp hnear]
      · rw [if_neg hy]
        exact fiberCappedValue_nonneg f P y x
    have hpointUpper (y : Fin n → Y) :
        fiberScaledCappedValue f P y x 1 ≤ if y ∈ Sup then f 0 else 0 := by
      by_cases hy : y ∈ Sup
      · rw [if_pos hy]
        exact fiberCappedValue_le_map_zero f P y x
      · rw [if_neg hy, fiberCappedValue_eq_endpointProfile f P hpY hV2]
        apply le_of_eq
        apply endpointProfile_of_nonneg
        rw [endpointExponent_eq P hn y x]
        have hinside : 0 < x * Real.sqrt (totalVariance P) + center P y := by
          change ¬center P y ≤ -x * Real.sqrt (totalVariance P) at hy
          linarith
        exact mul_nonneg hsqrtn0.le hinside.le
    have havgLower : (f 0 - e) * (P.marginal.iid n).event Slow ≤
        endpointCappedAverage f P n x := by
      rw [endpointCappedAverage]
      calc
        (f 0 - e) * (P.marginal.iid n).event Slow =
            (P.marginal.iid n).expect
              (fun y ↦ if y ∈ Slow then f 0 - e else 0) :=
          (expect_indicator (P.marginal.iid n) Slow (f 0 - e)).symm
        _ ≤ _ := (P.marginal.iid n).expect_mono hpointLower
    have havgUpper : endpointCappedAverage f P n x ≤
        f 0 * (P.marginal.iid n).event Sup := by
      rw [endpointCappedAverage]
      calc
        (P.marginal.iid n).expect
            (fun y ↦ fiberScaledCappedValue f P y x 1) ≤
            (P.marginal.iid n).expect
              (fun y ↦ if y ∈ Sup then f 0 else 0) :=
          (P.marginal.iid n).expect_mono hpointUpper
        _ = _ := expect_indicator (P.marginal.iid n) Sup (f 0)
    have hpl' : gaussianCDF (-x) - 2 * γ <
        (P.marginal.iid n).event Slow := by
      have habs := abs_lt.mp hPhiClose
      change gaussianCDF (-(x + s)) - γ <
        (P.marginal.iid n).event Slow at hpl
      linarith
    have hmulLower := mul_lt_mul_of_pos_left hpl' hf0pos
    have hSlowLe : (P.marginal.iid n).event Slow ≤ 1 :=
      (P.marginal.iid n).event_le_one Slow
    have hevent : e * (P.marginal.iid n).event Slow ≤ e := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hSlowLe he.le
    have htargetLower : f 0 * gaussianCDF (-x) - ε <
        (f 0 - e) * (P.marginal.iid n).event Slow := by
      have hγeq : 2 * f 0 * γ = ε / 8 := by
        dsimp [γ]
        field_simp [hf0]
        ring
      rw [mul_sub] at hmulLower
      nlinarith
    have htargetUpper : f 0 * (P.marginal.iid n).event Sup <
        f 0 * gaussianCDF (-x) + ε := by
      change (P.marginal.iid n).event Sup < gaussianCDF (-x) + γ at hpu
      have hmul := mul_lt_mul_of_pos_left hpu hf0pos
      have hγeq : f 0 * γ = ε / 16 := by
        dsimp [γ]
        field_simp [hf0]
      nlinarith
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith
    · linarith

theorem blockInformation_eq_conditionalMean_of_pos
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) {n : ℕ} (y : Fin n → Y) (z : Fin n → X)
    (hz : 0 < conditionalProduct P y z) :
    blockInformation P z y = conditionalMean P y := by
  let w : FiberSupport P y := fun i ↦ ⟨z i, by
    have hprod : (∏ j, P.conditional (y j) (z j)) ≠ 0 := by
      simpa only [conditionalProduct_apply] using hz.ne'
    have hne := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
    exact lt_of_le_of_ne ((P.conditional (y i)).nonneg (z i)) (Ne.symm hne)⟩
  have h := fiberSurprisal_eq_conditionalMean P hpY hV2 y w
  simpa [fiberSurprisal, blockInformation, w] using h

theorem shiftedConditionalTail_eq_indicator
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) {n : ℕ} (y : Fin n → Y) (x shift : ℝ) :
    shiftedConditionalTail P y x shift =
      if threshold P n x + shift ≤ conditionalMean P y then 1 else 0 := by
  by_cases hmean : threshold P n x + shift ≤ conditionalMean P y
  · rw [if_pos hmean]
    unfold shiftedConditionalTail FinProb.event
    simp only [Finset.sum_filter]
    calc
      (∑ z, if threshold P n x + shift ≤ blockInformation P z y then
          conditionalProduct P y z else 0) =
          ∑ z, conditionalProduct P y z := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : 0 < conditionalProduct P y z
        · have hinfo := blockInformation_eq_conditionalMean_of_pos P hpY hV2 y z hz
          simp [hinfo, hmean]
        · have hz0 : conditionalProduct P y z = 0 :=
            le_antisymm (le_of_not_gt hz) ((conditionalProduct P y).nonneg z)
          have hprod : ∏ i, P.conditional (y i) (z i) = 0 := by
            simpa only [conditionalProduct_apply] using hz0
          simp [hprod]
      _ = 1 := (conditionalProduct P y).sum_prob
  · rw [if_neg hmean]
    unfold shiftedConditionalTail FinProb.event
    apply Finset.sum_eq_zero
    intro z hzmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hzmem
    have hznot : ¬0 < conditionalProduct P y z := by
      intro hz
      have hinfo := blockInformation_eq_conditionalMean_of_pos P hpY hV2 y z hz
      rw [hinfo] at hzmem
      exact hmean hzmem
    exact le_antisymm (le_of_not_gt hznot) ((conditionalProduct P y).nonneg z)

theorem endpointShiftedTailAverage_eq_event (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) (n : ℕ) (x shift : ℝ) :
    endpointShiftedTailAverage f P n x shift =
      f 0 * (P.marginal.iid n).event
        {y | conditionalMean P y < threshold P n x + shift} := by
  rw [endpointShiftedTailAverage]
  have hpoint (y : Fin n → Y) :
      f (shiftedConditionalTail P y x shift) =
        if y ∈ {y | conditionalMean P y < threshold P n x + shift} then f 0 else 0 := by
    rw [shiftedConditionalTail_eq_indicator P hpY hV2]
    by_cases h : threshold P n x + shift ≤ conditionalMean P y
    · have hnot : ¬conditionalMean P y < threshold P n x + shift := not_lt_of_ge h
      simp [h, hnot, f.map_one]
    · have hlt : conditionalMean P y < threshold P n x + shift := lt_of_not_ge h
      simp [h, hlt]
  simp_rw [hpoint]
  exact expect_indicator (P.marginal.iid n)
    {y | conditionalMean P y < threshold P n x + shift} (f 0)

def AdmissibleShift (τ : ℕ → ℝ) : Prop :=
  Tendsto τ atTop atTop ∧
    Tendsto (fun n ↦ τ n / Real.sqrt (n : ℝ)) atTop (𝓝 0)

theorem movingEntropyEvent_tendsto
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV2 : variance₂ P = 0)
    (hV : 0 < totalVariance P) (x : ℝ) (τ : ℕ → ℝ)
    (hτ : AdmissibleShift τ) :
    Tendsto (fun n ↦ (P.marginal.iid n).event
      {y | conditionalMean P y < threshold P n x + τ n}) atTop
      (𝓝 (gaussianCDF (-x))) := by
  have hsqrtV : 0 < Real.sqrt (totalVariance P) := Real.sqrt_pos.2 hV
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨d, hd, hPhiCont⟩ :=
    (Metric.continuousAt_iff.mp continuous_gaussianCDF.continuousAt) (ε / 4)
      (by linarith)
  let s := min (d / 2) 1
  have hs : 0 < s := lt_min (div_pos hd (by norm_num)) zero_lt_one
  have hsd : s < d := (min_le_left (d / 2) 1).trans_lt (by linarith)
  have hPhiLeft : |gaussianCDF (-(x + s)) - gaussianCDF (-x)| < ε / 4 := by
    apply hPhiCont
    rw [Real.dist_eq]
    have hsub : -(x + s) - -x = -s := by ring
    rw [hsub, abs_neg, abs_of_nonneg hs.le]
    exact hsd
  have hPhiRight : |gaussianCDF (-(x - s)) - gaussianCDF (-x)| < ε / 4 := by
    apply hPhiCont
    rw [Real.dist_eq]
    have hsub : -(x - s) - -x = s := by ring
    rw [hsub, abs_of_nonneg hs.le]
    exact hsd
  have hCDFleft := centerCDF_tendsto_standard hBE P hpY hV2 hV (x + s)
  have hCDFright := centerCDF_tendsto_standard hBE P hpY hV2 hV (x - s)
  have hleftEv : ∀ᶠ n in atTop,
      gaussianCDF (-(x + s)) - ε / 4 <
        (P.marginal.iid n).event
          {y | center P y ≤ -(x + s) * Real.sqrt (totalVariance P)} :=
    (tendsto_order.1 hCDFleft).1 _ (by linarith)
  have hrightEv : ∀ᶠ n in atTop,
      (P.marginal.iid n).event
          {y | center P y ≤ -(x - s) * Real.sqrt (totalVariance P)} <
        gaussianCDF (-(x - s)) + ε / 4 :=
    (tendsto_order.1 hCDFright).2 _ (by linarith)
  have hratioEv : ∀ᶠ n in atTop,
      |τ n / Real.sqrt (n : ℝ)| < s * Real.sqrt (totalVariance P) := by
    have hradius : 0 < s * Real.sqrt (totalVariance P) := mul_pos hs hsqrtV
    have hh := hτ.2.eventually (Metric.ball_mem_nhds 0 hradius)
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
  filter_upwards [hleftEv, hrightEv, hratioEv, eventually_gt_atTop (0 : ℕ)]
    with n hleft hright hratio hn
  let Aleft : Set (Fin n → Y) :=
    {y | center P y ≤ -(x + s) * Real.sqrt (totalVariance P)}
  let A : Set (Fin n → Y) :=
    {y | conditionalMean P y < threshold P n x + τ n}
  let Aright : Set (Fin n → Y) :=
    {y | center P y ≤ -(x - s) * Real.sqrt (totalVariance P)}
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hleftSubset : Aleft ⊆ A := by
    intro y hy
    change center P y ≤ -(x + s) * Real.sqrt (totalVariance P) at hy
    change conditionalMean P y < threshold P n x + τ n
    have hratioLower := (abs_lt.mp hratio).1
    have hmul := (lt_div_iff₀ hsqrtn).mp hratioLower
    have hexp := endpointExponent_eq P hn y x
    have hinside : x * Real.sqrt (totalVariance P) + center P y ≤
        -(s * Real.sqrt (totalVariance P)) := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hinside hsqrtn.le
    linarith [hexp]
  have hrightSubset : A ⊆ Aright := by
    intro y hy
    change conditionalMean P y < threshold P n x + τ n at hy
    change center P y ≤ -(x - s) * Real.sqrt (totalVariance P)
    have hratioUpper := (abs_lt.mp hratio).2
    have hmul := (div_lt_iff₀ hsqrtn).mp hratioUpper
    rw [mul_comm (s * Real.sqrt (totalVariance P)) (Real.sqrt (n : ℝ))] at hmul
    have hexp := endpointExponent_eq P hn y x
    have hinside : x * Real.sqrt (totalVariance P) + center P y <
        s * Real.sqrt (totalVariance P) := by
      by_contra hnot
      have hscaled := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) hsqrtn.le
      have hleftTau : Real.sqrt (n : ℝ) *
          (x * Real.sqrt (totalVariance P) + center P y) < τ n := by
        linarith [hexp]
      linarith
    linarith
  have hmonoLeft := finProb_event_mono (P.marginal.iid n) Aleft A hleftSubset
  have hmonoRight := finProb_event_mono (P.marginal.iid n) A Aright hrightSubset
  change gaussianCDF (-(x + s)) - ε / 4 <
    (P.marginal.iid n).event Aleft at hleft
  change (P.marginal.iid n).event Aright <
    gaussianCDF (-(x - s)) + ε / 4 at hright
  have hPhiL := abs_lt.mp hPhiLeft
  have hPhiR := abs_lt.mp hPhiRight
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem endpointShiftedTailAverage_tendsto
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) (hV : 0 < totalVariance P)
    (x : ℝ) (τ : ℕ → ℝ) (hτ : AdmissibleShift τ) :
    Tendsto (fun n ↦ endpointShiftedTailAverage f P n x (τ n)) atTop
      (𝓝 (f 0 * gaussianCDF (-x))) := by
  have hprob := movingEntropyEvent_tendsto hBE P hpY hV2 hV x τ hτ
  have hconst : Tendsto (fun _ : ℕ ↦ f 0) atTop (𝓝 (f 0)) := tendsto_const_nhds
  have hmul := hconst.mul hprob
  apply hmul.congr'
  exact Eventually.of_forall fun n ↦ by
    exact (endpointShiftedTailAverage_eq_event f P hpY hV2 n x (τ n)).symm

/-- **Lemma 16 (uniform endpoint).** -/
theorem paperLemma16
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : variance₂ P = 0) (hV : 0 < totalVariance P) (x : ℝ) :
    (∀ y (z : Support (P.conditional y)),
      (Fintype.card (Support (P.conditional y)) : ℝ) *
        P.conditional y z.1 = 1) ∧
    Tendsto (fun n ↦ endpointCappedAverage f P n x) atTop
      (𝓝 (f 0 * (1 - gaussianCDF x))) ∧
    ∀ τ : ℕ → ℝ, AdmissibleShift τ →
      Tendsto (fun n ↦ endpointShiftedTailAverage f P n x (τ n)) atTop
        (𝓝 (f 0 * (1 - gaussianCDF x))) := by
  refine ⟨conditional_uniform_on_support P hpY hV2, ?_, ?_⟩
  · simpa only [gaussianCDF_neg] using
      endpointCappedAverage_tendsto hBE f P hpY hV2 hV x
  · intro τ hτ
    simpa only [gaussianCDF_neg] using
      endpointShiftedTailAverage_tendsto hBE f P hpY hV2 hV x τ hτ

end UniformEndpoint

end RandomnessExtraction
