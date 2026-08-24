import RandomnessExtraction.Generator
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Capped reference vectors

These are the finite convex programs in equations (34)--(38) of the paper.
-/

open scoped BigOperators Classical

namespace RandomnessExtraction

/-- A nonnegative subprobability vector whose coordinates are capped by `c`. -/
structure CappedVector (α : Type*) [Fintype α] (c : ℝ) where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  le_cap : ∀ x, mass x ≤ c
  sum_le_one : ∑ x, mass x ≤ 1

namespace CappedVector

variable {α : Type*} [Fintype α] {c : ℝ}

instance : CoeFun (CappedVector α c) (fun _ ↦ α → ℝ) := ⟨CappedVector.mass⟩

/-- The all-zero capped vector. -/
def zero (hc : 0 ≤ c) : CappedVector α c where
  mass _ := 0
  nonneg _ := le_rfl
  le_cap _ := hc
  sum_le_one := by simp

end CappedVector

/-- The scaled capped objective in equation (37). -/
noncomputable def scaledCappedCost {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (a : ℝ) (p : FinProb α) {c : ℝ}
    (q : CappedVector α c) : ℝ :=
  (∑ x, perspective f (a * p x) (q x)) + (1 - ∑ x, q x) * f 0

/-- The unscaled capped objective in equation (35). -/
noncomputable def cappedCost {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (p : FinProb α) {c : ℝ} (q : CappedVector α c) : ℝ :=
  scaledCappedCost f 1 p q

/-- The scaled capped value `g_{f,c}^{(a)}` in equation (37). -/
noncomputable def scaledCappedValue {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (a c : ℝ) (p : FinProb α) : ℝ :=
  sInf {v : ℝ | ∃ q : CappedVector α c, v = scaledCappedCost f a p q}

/-- The capped value `g_{f,c}` in equation (36). -/
noncomputable def cappedValue {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (c : ℝ) (p : FinProb α) : ℝ :=
  scaledCappedValue f 1 c p

namespace CappedCost

variable {α : Type*} [Fintype α]

private noncomputable def weight {c : ℝ} (q : CappedVector α c) : Option α → ℝ
  | none => 1 - ∑ x, q x
  | some x => q x

private noncomputable def ratio (a : ℝ) (p : FinProb α) {c : ℝ}
    (q : CappedVector α c) : Option α → ℝ
  | none => 0
  | some x => if q x = 0 then 0 else a * p x / q x

private theorem sum_weight {c : ℝ} (q : CappedVector α c) : ∑ i, weight q i = 1 := by
  classical
  rw [Fintype.sum_option]
  simp [weight]

private theorem weight_nonneg {c : ℝ} (q : CappedVector α c) (i : Option α) :
    0 ≤ weight q i := by
  cases i with
  | none => simpa [weight] using sub_nonneg.mpr q.sum_le_one
  | some x => exact q.nonneg x

private theorem ratio_nonneg (a : ℝ) (ha : 0 ≤ a) (p : FinProb α) {c : ℝ}
    (q : CappedVector α c) (i : Option α) : 0 ≤ ratio a p q i := by
  cases i with
  | none => simp [ratio]
  | some x =>
      by_cases hqx : q x = 0
      · simp [ratio, hqx]
      · have hqpos : 0 < q x := lt_of_le_of_ne (q.nonneg x) (Ne.symm hqx)
        simpa [ratio, hqx] using
          (div_nonneg (mul_nonneg ha (p.nonneg x)) hqpos.le)

private theorem weighted_ratio_le (a : ℝ) (ha : 0 ≤ a) (p : FinProb α) {c : ℝ}
    (q : CappedVector α c) :
    (∑ i, weight q i * ratio a p q i) ≤ a := by
  classical
  rw [Fintype.sum_option]
  simp only [weight, ratio, mul_zero, zero_add]
  calc
    (∑ x, q x * if q x = 0 then 0 else a * p x / q x) =
        ∑ x, if q x = 0 then 0 else a * p x := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hqx : q x = 0
          · simp [hqx]
          · simp only [if_neg hqx]
            field_simp
    _ ≤ ∑ x, a * p x := by
          gcongr with x hx
          split_ifs
          · exact mul_nonneg ha (p.nonneg x)
          · exact le_rfl
    _ = a := by rw [← Finset.mul_sum, p.sum_prob, mul_one]

private theorem weighted_f_eq_cost (f : AdmissibleGenerator) (a : ℝ)
    (p : FinProb α) {c : ℝ} (q : CappedVector α c) :
    (∑ i, weight q i * f (ratio a p q i)) = scaledCappedCost f a p q := by
  classical
  rw [Fintype.sum_option]
  simp only [weight, ratio]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hqx : q x = 0
  · simp [hqx, perspective]
  · simp [hqx, perspective]

/-- Every scaled capped objective is bounded below by `f(a)`.  This supplies
the boundedness needed for the real infimum and is also the Jensen step used
in the optimized-reference converse. -/
theorem scaledCappedCost_lower (f : AdmissibleGenerator) (a : ℝ) (ha : 0 ≤ a)
    (p : FinProb α) {c : ℝ} (q : CappedVector α c) :
    f a ≤ scaledCappedCost f a p q := by
  let w : Option α → ℝ := weight q
  let u : Option α → ℝ := ratio a p q
  have hjensen := f.convexOn_nonneg.map_sum_le
    (t := Finset.univ) (w := w) (p := u)
    (fun i _ ↦ weight_nonneg q i) (by simpa [w] using sum_weight q)
    (fun i _ ↦ ratio_nonneg a ha p q i)
  have havg_nonneg : 0 ≤ ∑ i, w i * u i := by
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (weight_nonneg q i) (ratio_nonneg a ha p q i)
  have havg_le : (∑ i, w i * u i) ≤ a := by
    simpa [w, u] using weighted_ratio_le a ha p q
  calc
    f a ≤ f (∑ i, w i * u i) :=
      f.antitoneOn_nonneg havg_nonneg ha havg_le
    _ ≤ ∑ i, w i * f (u i) := by
      simpa only [smul_eq_mul] using hjensen
    _ = scaledCappedCost f a p q := by
      simpa [w, u] using weighted_f_eq_cost f a p q

theorem scaledCappedValue_le_cost (f : AdmissibleGenerator) (a c : ℝ)
    (ha : 0 ≤ a) (p : FinProb α) (q : CappedVector α c) :
    scaledCappedValue f a c p ≤ scaledCappedCost f a p q := by
  apply csInf_le
  · refine ⟨f a, ?_⟩
    rintro v ⟨q', rfl⟩
    exact scaledCappedCost_lower f a ha p q'
  · exact ⟨q, rfl⟩

theorem scaledCappedValue_lower (f : AdmissibleGenerator) (a c : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (p : FinProb α) :
    f a ≤ scaledCappedValue f a c p := by
  apply le_csInf
  · exact ⟨scaledCappedCost f a p (CappedVector.zero hc),
      CappedVector.zero hc, rfl⟩
  · rintro v ⟨q, rfl⟩
    exact scaledCappedCost_lower f a ha p q

theorem scaledCappedCost_antitone_scale (f : AdmissibleGenerator)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (p : FinProb α) {c : ℝ}
    (q : CappedVector α c) :
    scaledCappedCost f b p q ≤ scaledCappedCost f a p q := by
  dsimp [scaledCappedCost]
  gcongr with x hx
  by_cases hqx : q x = 0
  · simp [perspective, hqx]
  · have hqpos : 0 < q x := lt_of_le_of_ne (q.nonneg x) (Ne.symm hqx)
    rw [perspective_of_pos f hqpos, perspective_of_pos f hqpos]
    gcongr
    apply f.antitoneOn_nonneg
    · exact div_nonneg (mul_nonneg ha (p.nonneg x)) hqpos.le
    · exact div_nonneg (mul_nonneg (ha.trans hab) (p.nonneg x)) hqpos.le
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hab (p.nonneg x)) hqpos.le

theorem scaledCappedValue_antitone_scale (f : AdmissibleGenerator)
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c)
    (p : FinProb α) :
    scaledCappedValue f b c p ≤ scaledCappedValue f a c p := by
  apply le_csInf
  · exact ⟨scaledCappedCost f a p (CappedVector.zero hc),
      CappedVector.zero hc, rfl⟩
  · rintro v ⟨q, rfl⟩
    exact (scaledCappedValue_le_cost f b c (ha.trans hab) p q).trans
      (scaledCappedCost_antitone_scale f ha hab p q)

theorem scaledCappedValue_eq_cost_of_optimizer (f : AdmissibleGenerator)
    (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (p : FinProb α)
    (qstar : CappedVector α c)
    (hopt : ∀ q : CappedVector α c,
      scaledCappedCost f a p qstar ≤ scaledCappedCost f a p q) :
    scaledCappedValue f a c p = scaledCappedCost f a p qstar := by
  apply le_antisymm
  · exact scaledCappedValue_le_cost f a c ha p qstar
  · apply le_csInf
    · exact ⟨scaledCappedCost f a p (CappedVector.zero hc),
        CappedVector.zero hc, rfl⟩
    · rintro v ⟨q, rfl⟩
      exact hopt q

end CappedCost

end RandomnessExtraction
