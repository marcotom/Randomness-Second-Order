import RandomnessExtraction.WaterFilling
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Probability representation of the water-filled value

This file formalizes Lemma 10 of the paper.  All logarithms used below have
base two, as in the manuscript.
-/

open scoped BigOperators Classical

namespace RandomnessExtraction

namespace ProbabilityRepresentation

/-- The base-two surprisal of a point under a positive finite law. -/
noncomputable def surprisal {α : Type*} [Fintype α]
    (p : FinProb α) (x : α) : ℝ := -Real.logb 2 (p x)

/-- `Pr{J_p > b}` written as a finite expectation. -/
noncomputable def upperTail {α : Type*} [Fintype α]
    (p : FinProb α) (b : ℝ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x ↦ b < surprisal p x), p x

/-- The truncated exponential moment in equation (57). -/
noncomputable def lowerMoment {α : Type*} [Fintype α]
    (p : FinProb α) (b : ℝ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x ↦ surprisal p x ≤ b),
    p x * (2 : ℝ) ^ (surprisal p x - b)

/-- The function `R_p` in equation (57). -/
noncomputable def tailFunctional {α : Type*} [Fintype α]
    (p : FinProb α) (b : ℝ) : ℝ := upperTail p b + lowerMoment p b

/-- The expectation term in equations (59) and (60). -/
noncomputable def cappedExpectation {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (a h b : ℝ) (p : FinProb α) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x ↦ surprisal p x ≤ b),
    p x * ((2 : ℝ) ^ (surprisal p x - h) *
      f (a * (2 : ℝ) ^ (h - surprisal p x)))

theorem two_rpow_surprisal {α : Type*} [Fintype α]
    (p : FinProb α) (hp : ∀ x, 0 < p x) (x : α) :
    (2 : ℝ) ^ surprisal p x = (p x)⁻¹ := by
  rw [surprisal, Real.rpow_neg (by norm_num)]
  rw [Real.rpow_logb (by norm_num) (by norm_num) (hp x)]

theorem two_rpow_waterLevel (h t : ℝ) (ht : 0 < t) :
    (2 : ℝ) ^ (h + Real.logb 2 t) = (2 : ℝ) ^ h * t := by
  rw [Real.rpow_add (by norm_num)]
  rw [Real.rpow_logb (by norm_num) (by norm_num) ht]

theorem capped_iff_surprisal_le {α : Type*} [Fintype α]
    (h t : ℝ) (ht : 0 < t) (p : FinProb α) (hp : ∀ x, 0 < p x) (x : α) :
    (2 : ℝ) ^ (-h) ≤ t * p x ↔
      surprisal p x ≤ h + Real.logb 2 t := by
  conv_rhs =>
    rw [← Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)]
  rw [two_rpow_surprisal p hp x, two_rpow_waterLevel h t ht]
  rw [Real.rpow_neg (by norm_num)]
  let A : ℝ := (2 : ℝ) ^ h
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) h
  change A⁻¹ ≤ t * p x ↔ (p x)⁻¹ ≤ A * t
  constructor
  · intro hcap
    rw [inv_le_iff_one_le_mul₀' (hp x)]
    rw [inv_le_iff_one_le_mul₀' hA] at hcap
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcap
  · intro hinv
    rw [inv_le_iff_one_le_mul₀' hA]
    rw [inv_le_iff_one_le_mul₀' (hp x)] at hinv
    simpa [mul_assoc, mul_left_comm, mul_comm] using hinv

theorem weighted_rpow_surprisal_sub {α : Type*} [Fintype α]
    (p : FinProb α) (hp : ∀ x, 0 < p x) (x : α) (b : ℝ) :
    p x * (2 : ℝ) ^ (surprisal p x - b) = (2 : ℝ) ^ (-b) := by
  rw [Real.rpow_sub (by norm_num), two_rpow_surprisal p hp x]
  rw [Real.rpow_neg (by norm_num)]
  rw [← mul_div_assoc, mul_inv_cancel₀ (hp x).ne', one_div]

theorem weighted_rpow_surprisal_sub_threshold {α : Type*} [Fintype α]
    (p : FinProb α) (hp : ∀ x, 0 < p x) (x : α) (h : ℝ) :
    p x * (2 : ℝ) ^ (surprisal p x - h) = (2 : ℝ) ^ (-h) :=
  weighted_rpow_surprisal_sub p hp x h

theorem rpow_threshold_sub_surprisal {α : Type*} [Fintype α]
    (p : FinProb α) (hp : ∀ x, 0 < p x) (x : α) (h : ℝ) :
    (2 : ℝ) ^ (h - surprisal p x) = (2 : ℝ) ^ h * p x := by
  rw [Real.rpow_sub (by norm_num), two_rpow_surprisal p hp x, div_inv_eq_mul]

theorem scaled_rpow_threshold_sub_surprisal {α : Type*} [Fintype α]
    (a h : ℝ) (p : FinProb α) (hp : ∀ x, 0 < p x) (x : α) :
    a * (2 : ℝ) ^ (h - surprisal p x) =
      a * p x / (2 : ℝ) ^ (-h) := by
  rw [rpow_threshold_sub_surprisal p hp x h, Real.rpow_neg (by norm_num),
    div_inv_eq_mul]
  ring

theorem rpow_waterLevel_sub_threshold (h t : ℝ) (ht : 0 < t) :
    (2 : ℝ) ^ ((h + Real.logb 2 t) - h) = t := by
  convert Real.rpow_logb (show (0 : ℝ) < 2 by norm_num)
    (show (2 : ℝ) ≠ 1 by norm_num) ht using 1 <;> ring

private theorem waterMass_eq_if {α : Type*} [Fintype α]
    (h t : ℝ) (ht : 0 < t) (p : FinProb α) (hp : ∀ x, 0 < p x) (x : α) :
    WaterFilling.mass ((2 : ℝ) ^ (-h)) t p x =
      if surprisal p x ≤ h + Real.logb 2 t then (2 : ℝ) ^ (-h) else t * p x := by
  rw [WaterFilling.mass]
  by_cases hx : surprisal p x ≤ h + Real.logb 2 t
  · rw [if_pos hx, min_eq_left]
    exact (capped_iff_surprisal_le h t ht p hp x).2 hx
  · rw [if_neg hx, min_eq_right]
    exact le_of_not_ge ((capped_iff_surprisal_le h t ht p hp x).not.mpr hx)

private theorem normalized_tail_identity {α : Type*} [Fintype α]
    (h t : ℝ) (ht : 0 < t) (p : FinProb α) (hp : ∀ x, 0 < p x)
    (hnorm : WaterFilling.normalization ((2 : ℝ) ^ (-h)) p t = 1) :
    1 = (2 : ℝ) ^ ((h + Real.logb 2 t) - h) *
      tailFunctional p (h + Real.logb 2 t) := by
  let b := h + Real.logb 2 t
  let P : α → Prop := fun x ↦ surprisal p x ≤ b
  have hpow : (2 : ℝ) ^ (b - h) = t := by
    simpa [b] using rpow_waterLevel_sub_threshold h t ht
  have hlower : lowerMoment p b =
      ∑ x ∈ Finset.univ.filter P, (2 : ℝ) ^ (-b) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact weighted_rpow_surprisal_sub p hp x b
  have hconst : t * (2 : ℝ) ^ (-b) = (2 : ℝ) ^ (-h) := by
    have hbpow : (2 : ℝ) ^ b = (2 : ℝ) ^ h * t := by
      simpa [b] using two_rpow_waterLevel h t ht
    rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num), hbpow]
    simp [ht.ne', mul_comm]
  have hmass : (∑ x, WaterFilling.mass ((2 : ℝ) ^ (-h)) t p x) =
      (∑ x ∈ Finset.univ.filter P, (2 : ℝ) ^ (-h)) +
      ∑ x ∈ Finset.univ.filter (fun x ↦ ¬ P x), t * p x := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P
      (fun x ↦ WaterFilling.mass ((2 : ℝ) ^ (-h)) t p x)]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      rw [waterMass_eq_if h t ht p hp x, if_pos (Finset.mem_filter.1 hx).2]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [waterMass_eq_if h t ht p hp x, if_neg (Finset.mem_filter.1 hx).2]
  have hnorm' : ∑ x, WaterFilling.mass ((2 : ℝ) ^ (-h)) t p x = 1 := by
    simpa [WaterFilling.normalization] using hnorm
  have hnotfilter : Finset.univ.filter (fun x ↦ ¬ P x) =
      Finset.univ.filter (fun x ↦ b < surprisal p x) := by
    ext x
    simp [P, not_le]
  rw [hnotfilter] at hmass
  rw [hpow, tailFunctional, upperTail, hlower]
  rw [← hnorm', hmass]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact hconst.symm

private theorem waterCost_eq_representation {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (a h t : ℝ) (_ha : 0 ≤ a) (ht : 1 ≤ t)
    (p : FinProb α) (hp : ∀ x, 0 < p x)
    (hnorm : WaterFilling.normalization ((2 : ℝ) ^ (-h)) p t = 1) :
    scaledCappedCost f a p
        (WaterFilling.normalizedVector ((2 : ℝ) ^ (-h)) t p
          (Real.rpow_nonneg (by norm_num) _) (zero_le_one.trans ht) hnorm) =
      t * upperTail p (h + Real.logb 2 t) * f (a / t) +
        cappedExpectation f a h (h + Real.logb 2 t) p := by
  let c : ℝ := (2 : ℝ) ^ (-h)
  let b : ℝ := h + Real.logb 2 t
  let P : α → Prop := fun x ↦ surprisal p x ≤ b
  let qstar := WaterFilling.normalizedVector c t p
    (Real.rpow_nonneg (by norm_num) _) (zero_le_one.trans ht) hnorm
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hqsum : ∑ x, qstar x = 1 :=
    WaterFilling.sum_normalizedVector c t p _ _ hnorm
  have hpoint (x : α) : perspective f (a * p x) (qstar x) =
      if P x then
        p x * ((2 : ℝ) ^ (surprisal p x - h) *
          f (a * (2 : ℝ) ^ (h - surprisal p x)))
      else t * p x * f (a / t) := by
    change perspective f (a * p x) (WaterFilling.mass c t p x) = _
    by_cases hx : P x
    · rw [if_pos hx, waterMass_eq_if h t htpos p hp x, if_pos]
      · rw [perspective_of_pos f hcpos]
        have hcoeff := weighted_rpow_surprisal_sub_threshold p hp x h
        have hratio := scaled_rpow_threshold_sub_surprisal a h p hp x
        change c * f (a * p x / c) = _
        rw [hratio]
        rw [← mul_assoc, hcoeff]
      · simpa [P, b] using hx
    · rw [if_neg hx, waterMass_eq_if h t htpos p hp x, if_neg]
      · rw [perspective_of_pos f (mul_pos htpos (hp x))]
        have hratio : a * p x / (t * p x) = a / t := by
          field_simp [htpos.ne', (hp x).ne']
        rw [hratio]
      · simpa [P, b] using hx
  change (∑ x, perspective f (a * p x) (qstar x)) +
      (1 - ∑ x, qstar x) * f 0 = _
  rw [hqsum, sub_self, zero_mul, add_zero]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P
    (fun x ↦ perspective f (a * p x) (qstar x))]
  have hPsum : (∑ x ∈ Finset.univ.filter P,
      perspective f (a * p x) (qstar x)) = cappedExpectation f a h b p := by
    rw [cappedExpectation]
    apply Finset.sum_congr
    · ext x
      simp [P, b]
    · intro x hx
      rw [hpoint x, if_pos (Finset.mem_filter.1 hx).2]
  have hnotPsum : (∑ x ∈ Finset.univ.filter (fun x ↦ ¬ P x),
      perspective f (a * p x) (qstar x)) =
      t * upperTail p b * f (a / t) := by
    rw [upperTail]
    have hfilter : Finset.univ.filter (fun x ↦ ¬ P x) =
        Finset.univ.filter (fun x ↦ b < surprisal p x) := by
      ext x
      simp [P, not_le]
    rw [hfilter]
    calc
      (∑ x ∈ Finset.univ.filter (fun x ↦ b < surprisal p x),
          perspective f (a * p x) (qstar x)) =
          ∑ x ∈ Finset.univ.filter (fun x ↦ b < surprisal p x),
            t * p x * f (a / t) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [hpoint x, if_neg]
              simpa [P] using (Finset.mem_filter.1 hx).2
      _ = t * (∑ x ∈ Finset.univ.filter (fun x ↦ b < surprisal p x), p x) *
          f (a / t) := by
            rw [Finset.mul_sum]
            rw [Finset.sum_mul]
  rw [hPsum, hnotPsum]
  ring

/-- **Lemma 10 (probability representation).**

The finite sums are exactly the probability and expectation notation in
equations (57)--(60).  The support hypothesis is `hp`; `hnorm` says that `t`
is the water-filling scalar supplied by Lemma 9. -/
theorem paperLemma10 {α : Type*} [Fintype α]
    (h t : ℝ) (ht : 1 ≤ t) (p : FinProb α) (hp : ∀ x, 0 < p x)
    (_hcard : 1 < (2 : ℝ) ^ (-h) * Fintype.card α)
    (hnorm : WaterFilling.normalization ((2 : ℝ) ^ (-h)) p t = 1) :
    let b := h + Real.logb 2 t
    1 = (2 : ℝ) ^ (b - h) * tailFunctional p b ∧
      ∀ f : AdmissibleGenerator,
        cappedValue f ((2 : ℝ) ^ (-h)) p =
            t * upperTail p b * f (1 / t) + cappedExpectation f 1 h b p ∧
        ∀ a : ℝ, 0 ≤ a →
          scaledCappedValue f a ((2 : ℝ) ^ (-h)) p =
            t * upperTail p b * f (a / t) + cappedExpectation f a h b p := by
  dsimp only
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  constructor
  · exact normalized_tail_identity h t htpos p hp hnorm
  · intro f
    have hc : 0 ≤ (2 : ℝ) ^ (-h) := Real.rpow_nonneg (by norm_num) _
    have hscaled (a : ℝ) (ha : 0 ≤ a) :
        scaledCappedValue f a ((2 : ℝ) ^ (-h)) p =
          t * upperTail p (h + Real.logb 2 t) * f (a / t) +
            cappedExpectation f a h (h + Real.logb 2 t) p := by
      let qstar := WaterFilling.normalizedVector ((2 : ℝ) ^ (-h)) t p hc
        (zero_le_one.trans ht) hnorm
      by_cases ha0 : a = 0
      · subst a
        have hqcost : scaledCappedCost f 0 p qstar = f 0 := by
          have hpoint (x : α) :
              perspective f (0 * p x) (qstar x) = qstar x * f 0 := by
            rw [zero_mul]
            by_cases hqx : qstar x = 0
            · simp [hqx, perspective]
            · rw [perspective_of_pos f
                (lt_of_le_of_ne (qstar.nonneg x) (Ne.symm hqx))]
              simp
          unfold scaledCappedCost
          simp_rw [hpoint]
          rw [← Finset.sum_mul]
          ring
        calc
          scaledCappedValue f 0 ((2 : ℝ) ^ (-h)) p =
              scaledCappedCost f 0 p qstar := by
            apply le_antisymm
            · exact CappedCost.scaledCappedValue_le_cost f 0
                ((2 : ℝ) ^ (-h)) (le_refl (0 : ℝ)) p qstar
            · rw [hqcost]
              exact CappedCost.scaledCappedValue_lower f 0
                ((2 : ℝ) ^ (-h)) (le_refl (0 : ℝ)) hc p
          _ = _ := waterCost_eq_representation f 0 h t
            (le_refl (0 : ℝ)) ht p hp hnorm
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hopt : WaterFilling.IsOptimizer f a p qstar :=
          WaterFilling.normalizedVector_isOptimizer f a ((2 : ℝ) ^ (-h)) t hapos
            (Real.rpow_pos_of_pos (by norm_num) _) ht p hp hnorm
        calc
          scaledCappedValue f a ((2 : ℝ) ^ (-h)) p =
              scaledCappedCost f a p qstar :=
            CappedCost.scaledCappedValue_eq_cost_of_optimizer f a
              ((2 : ℝ) ^ (-h)) ha hc p qstar hopt
          _ = _ := waterCost_eq_representation f a h t ha ht p hp hnorm
    constructor
    · simpa [cappedValue] using hscaled 1 zero_le_one
    · exact hscaled


end ProbabilityRepresentation

end RandomnessExtraction
