import RandomnessExtraction.Capped
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional water filling

The public theorem at the end of this file is Lemma 9 of the paper.  The
supporting-line proof below spells out the KKT argument used in the text.
-/

open Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

namespace WaterFilling

/-- Right derivative used in the paper's proof of Lemma 9. -/
noncomputable def rightDeriv (f : AdmissibleGenerator) (u : ℝ) : ℝ :=
  derivWithin f (Set.Ioi u) u

/-- `γ(u) = f(u) - u f'_+(u)`. -/
noncomputable def gamma (f : AdmissibleGenerator) (u : ℝ) : ℝ :=
  f u - u * rightDeriv f u

private theorem mem_interior_nonneg {u : ℝ} (hu : 0 < u) :
    u ∈ interior (Set.Ici (0 : ℝ)) := by
  rw [interior_Ici]
  exact hu

theorem rightDeriv_nonpos (f : AdmissibleGenerator) {u : ℝ} (hu : 0 ≤ u) :
    rightDeriv f u ≤ 0 := by
  apply AntitoneOn.derivWithin_nonpos
  apply f.antitoneOn_nonneg.mono
  intro z hz
  exact hu.trans hz.le

/-- A right derivative of a convex function is a valid subgradient. -/
theorem rightDeriv_supporting (f : AdmissibleGenerator) {u v : ℝ}
    (hu : 0 < u) (hv : 0 ≤ v) :
    f u + rightDeriv f u * (v - u) ≤ f v := by
  rcases lt_trichotomy v u with hvu | rfl | huv
  · have hslope := f.convexOn_nonneg.slope_le_leftDeriv_of_mem_interior
      hv (mem_interior_nonneg hu) hvu
    have hleft := f.convexOn_nonneg.leftDeriv_le_rightDeriv_of_mem_interior
      (mem_interior_nonneg hu)
    have hsr : slope f v u ≤ rightDeriv f u := hslope.trans hleft
    rw [slope_def_field] at hsr
    have hneg : v - u < 0 := sub_neg.mpr hvu
    have := mul_le_mul_of_nonpos_right hsr hneg.le
    have heq : ((f u - f v) / (u - v)) * (v - u) = f v - f u := by
      field_simp [hvu.ne]
      ring
    rw [heq] at this
    linarith
  · simp
  · have hsr := f.convexOn_nonneg.rightDeriv_le_slope_of_mem_interior
      (mem_interior_nonneg hu) hv huv
    rw [slope_def_field] at hsr
    have hpos : 0 < v - u := sub_pos.mpr huv
    have := mul_le_mul_of_nonneg_right hsr hpos.le
    have heq : ((f v - f u) / (v - u)) * (v - u) = f v - f u := by
      field_simp [huv.ne]
    rw [heq] at this
    dsimp [rightDeriv] at this ⊢
    linarith

/-- The function `γ` is nonincreasing, as asserted in equation (55). -/
theorem gamma_antitoneOn (f : AdmissibleGenerator) :
    AntitoneOn (gamma f) (Set.Ioi 0) := by
  intro u hu v hv huv
  rcases huv.eq_or_lt with rfl | huv
  · exact le_rfl
  · have hduv : rightDeriv f u ≤ rightDeriv f v :=
      f.convexOn_nonneg.monotoneOn_rightDeriv
        (mem_interior_nonneg hu) (mem_interior_nonneg hv) huv.le
    have hsupport := rightDeriv_supporting f hv hu.le
    dsimp [gamma] at *
    nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hduv)]

theorem gamma_le_map_zero (f : AdmissibleGenerator) {u : ℝ} (hu : 0 < u) :
    gamma f u ≤ f 0 := by
  have h := rightDeriv_supporting f hu (le_refl 0)
  dsimp [gamma] at *
  linarith

/-- Supporting line for a single perspective coordinate. -/
theorem perspective_supporting (f : AdmissibleGenerator) {P q qstar u : ℝ}
    (hP : 0 < P) (hq : 0 ≤ q) (hqstar : 0 < qstar)
    (hu : 0 < u) (hPu : P = qstar * u) :
    perspective f P qstar + gamma f u * (q - qstar) ≤ perspective f P q := by
  rcases hq.eq_or_lt with rfl | hq
  · rw [perspective_zero_right, perspective_of_pos f hqstar]
    have hd := rightDeriv_nonpos f hu.le
    have hPnonneg := hP.le
    rw [hPu]
    dsimp [gamma]
    field_simp
    nlinarith [mul_nonneg hPnonneg (neg_nonneg.mpr hd)]
  · rw [perspective_of_pos f hqstar, perspective_of_pos f hq]
    have hv : 0 ≤ P / q := div_nonneg hP.le hq.le
    have hs := rightDeriv_supporting f hu hv
    rw [hPu] at hs ⊢
    dsimp [gamma] at *
    have hmul := mul_le_mul_of_nonneg_left hs hq.le
    have hcancel : q * (qstar * u / q - u) = qstar * u - q * u := by
      field_simp [hq.ne']
    have hrewrite :
        q * (f u + rightDeriv f u * (qstar * u / q - u)) =
          q * f u + rightDeriv f u * (qstar * u - q * u) := by
      calc
        q * (f u + rightDeriv f u * (qstar * u / q - u)) =
            q * f u + rightDeriv f u * (q * (qstar * u / q - u)) := by ring
        _ = q * f u + rightDeriv f u * (qstar * u - q * u) := by rw [hcancel]
    have hstar : qstar * u / qstar = u := by field_simp [hqstar.ne']
    rw [hrewrite] at hmul
    rw [hstar]
    nlinarith

/-- Coordinatewise water-filled mass. -/
noncomputable def mass {α : Type*} [Fintype α]
    (c t : ℝ) (p : FinProb α) (x : α) : ℝ := min c (t * p x)

/-- Normalization function `t ↦ ∑ₓ min(c,t pₓ)`. -/
noncomputable def normalization {α : Type*} [Fintype α]
    (c : ℝ) (p : FinProb α) (t : ℝ) : ℝ := ∑ x, mass c t p x

theorem continuous_normalization {α : Type*} [Fintype α] (c : ℝ) (p : FinProb α) :
    Continuous (normalization c p) := by
  apply continuous_finset_sum
  intro x _
  exact continuous_const.min (continuous_id.mul continuous_const)

theorem normalization_one_le {α : Type*} [Fintype α]
    (c : ℝ) (p : FinProb α) : normalization c p 1 ≤ 1 := by
  calc
    normalization c p 1 ≤ ∑ x, p x := by
      apply Finset.sum_le_sum
      intro x _
      simp [normalization, mass]
    _ = 1 := p.sum_prob

/-- An explicit parameter at which every coordinate is capped. -/
noncomputable def largeParameter {α : Type*} [Fintype α]
    (c : ℝ) (p : FinProb α) : ℝ := 1 + ∑ x, c / p x

private theorem one_le_largeParameter {α : Type*} [Fintype α]
    (c : ℝ) (hc : 0 ≤ c) (p : FinProb α) (hp : ∀ x, 0 < p x) :
    1 ≤ largeParameter c p := by
  dsimp [largeParameter]
  have : 0 ≤ ∑ x, c / p x := Finset.sum_nonneg fun x _ ↦ div_nonneg hc (hp x).le
  linarith

private theorem mass_largeParameter {α : Type*} [Fintype α]
    (c : ℝ) (hc : 0 ≤ c) (p : FinProb α) (hp : ∀ x, 0 < p x) (x : α) :
    mass c (largeParameter c p) p x = c := by
  rw [mass, min_eq_left]
  have hxterm : c / p x ≤ ∑ y, c / p y := by
    exact Finset.single_le_sum (fun y _ ↦ div_nonneg hc (hp y).le) (Finset.mem_univ x)
  have hT : c / p x ≤ largeParameter c p := by
    dsimp [largeParameter]
    linarith
  have := mul_le_mul_of_nonneg_right hT (hp x).le
  have hcancel : (c / p x) * p x = c := by field_simp [(hp x).ne']
  rw [hcancel] at this
  simpa [mul_comm] using this

theorem normalization_largeParameter {α : Type*} [Fintype α]
    (c : ℝ) (hc : 0 ≤ c) (p : FinProb α) (hp : ∀ x, 0 < p x) :
    normalization c p (largeParameter c p) = c * Fintype.card α := by
  simp [normalization, mass_largeParameter c hc p hp, mul_comm]

/-- Existence of the normalizing scalar in the first case of Lemma 9. -/
theorem exists_normalizing_parameter {α : Type*} [Fintype α]
    (c : ℝ) (hc : 0 ≤ c) (p : FinProb α) (hp : ∀ x, 0 < p x)
    (hcard : 1 ≤ c * Fintype.card α) :
    ∃ t : ℝ, 1 ≤ t ∧ normalization c p t = 1 := by
  let T := largeParameter c p
  have h1T : 1 ≤ T := one_le_largeParameter c hc p hp
  have hF1 : normalization c p 1 ≤ 1 := normalization_one_le c p
  have hFT : 1 ≤ normalization c p T := by
    rw [show T = largeParameter c p by rfl, normalization_largeParameter c hc p hp]
    exact hcard
  have himage : (1 : ℝ) ∈ normalization c p '' Set.Icc 1 T :=
    intermediate_value_Icc h1T (continuous_normalization c p).continuousOn ⟨hF1, hFT⟩
  rcases himage with ⟨t, ht, htnorm⟩
  exact ⟨t, ht.1, htnorm⟩

/-- The normalized water-filled vector. -/
noncomputable def normalizedVector {α : Type*} [Fintype α]
    (c t : ℝ) (p : FinProb α) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hnorm : normalization c p t = 1) : CappedVector α c where
  mass x := mass c t p x
  nonneg x := le_min hc (mul_nonneg ht (p.nonneg x))
  le_cap x := min_le_left _ _
  sum_le_one := hnorm.le

@[simp]
theorem normalizedVector_apply {α : Type*} [Fintype α]
    (c t : ℝ) (p : FinProb α) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hnorm : normalization c p t = 1) (x : α) :
    normalizedVector c t p hc ht hnorm x = mass c t p x := rfl

theorem sum_normalizedVector {α : Type*} [Fintype α]
    (c t : ℝ) (p : FinProb α) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hnorm : normalization c p t = 1) :
    ∑ x, normalizedVector c t p hc ht hnorm x = 1 := hnorm

/-- The all-capped vector used when the support cannot carry unit mass. -/
def allCappedVector {α : Type*} [Fintype α]
    (c : ℝ) (hc : 0 ≤ c) (hcard : c * Fintype.card α ≤ 1) : CappedVector α c where
  mass _ := c
  nonneg _ := hc
  le_cap _ := le_rfl
  sum_le_one := by simpa [mul_comm] using hcard

@[simp]
theorem allCappedVector_apply {α : Type*} [Fintype α]
    (c : ℝ) (hc : 0 ≤ c) (hcard : c * Fintype.card α ≤ 1) (x : α) :
    allCappedVector c hc hcard x = c := rfl

/-- A feasible vector minimizes the scaled capped problem. -/
def IsOptimizer {α : Type*} [Fintype α] (f : AdmissibleGenerator)
    (a : ℝ) (p : FinProb α) {c : ℝ} (qstar : CappedVector α c) : Prop :=
  ∀ q : CappedVector α c,
    scaledCappedCost f a p qstar ≤ scaledCappedCost f a p q

private theorem normalized_coordinate_support {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (a c t : ℝ) (ha : 0 < a) (hc : 0 < c)
    (ht : 1 ≤ t) (p : FinProb α) (hp : ∀ x, 0 < p x)
    (q : CappedVector α c) (x : α) :
    perspective f (a * p x) (mass c t p x) + gamma f (a / t) *
        (q x - mass c t p x) ≤ perspective f (a * p x) (q x) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hapos : 0 < a / t := div_pos ha htpos
  have hP : 0 < a * p x := mul_pos ha (hp x)
  have hqnonneg := q.nonneg x
  rcases le_total (t * p x) c with huncapped | hcapped
  · rw [mass, min_eq_right huncapped]
    apply perspective_supporting f hP hqnonneg (mul_pos htpos (hp x)) hapos
    field_simp [htpos.ne']
  · rw [mass, min_eq_left hcapped]
    let ux := a * p x / c
    have hux : 0 < ux := div_pos hP hc
    have hratio : a * p x = c * ux := by
      dsimp [ux]
      field_simp [hc.ne']
    have hsupp := perspective_supporting f hP hqnonneg hc hux hratio
    have huorder : a / t ≤ ux := by
      dsimp [ux]
      have hmul := mul_le_mul_of_nonneg_left hcapped ha.le
      apply (div_le_div_iff₀ htpos hc).2
      nlinarith
    have hgamma : gamma f ux ≤ gamma f (a / t) :=
      gamma_antitoneOn f hapos hux huorder
    have hdiff : q x - c ≤ 0 := sub_nonpos.mpr (q.le_cap x)
    have hmul := mul_le_mul_of_nonpos_right hgamma hdiff
    linarith

/-- Optimality of the normalized water-filled vector. -/
theorem normalizedVector_isOptimizer {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (a c t : ℝ) (ha : 0 < a) (hc : 0 < c)
    (ht : 1 ≤ t) (p : FinProb α) (hp : ∀ x, 0 < p x)
    (hnorm : normalization c p t = 1) :
    IsOptimizer f a p (normalizedVector c t p hc.le (zero_le_one.trans ht) hnorm) := by
  intro q
  let qstar := normalizedVector c t p hc.le (zero_le_one.trans ht) hnorm
  let lambda := gamma f (a / t)
  have hcoord : ∀ x,
      perspective f (a * p x) (qstar x) + lambda * (q x - qstar x) ≤
        perspective f (a * p x) (q x) := by
    intro x
    exact normalized_coordinate_support f a c t ha hc ht p hp q x
  have hsum :
      (∑ x, (perspective f (a * p x) (qstar x) + lambda * (q x - qstar x))) ≤
        ∑ x, perspective f (a * p x) (q x) := by
    exact Finset.sum_le_sum fun x _ ↦ hcoord x
  have hqsum : ∑ x, q x ≤ 1 := q.sum_le_one
  have hr : 0 ≤ 1 - ∑ x, q x := sub_nonneg.mpr hqsum
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hlambda : lambda ≤ f 0 := gamma_le_map_zero f (div_pos ha htpos)
  dsimp [scaledCappedCost]
  have hqstarsum : ∑ x, qstar x = 1 := sum_normalizedVector _ _ _ _ _ _
  simp_rw [Finset.sum_add_distrib] at hsum
  have hlinear : ∑ x, lambda * (q x - qstar x) =
      lambda * ((∑ x, q x) - 1) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hqstarsum]
  rw [hlinear] at hsum
  rw [show (∑ x, mass c t p x) = 1 by exact hnorm, sub_self, zero_mul, add_zero]
  calc
    (∑ x, perspective f (a * p x) (qstar x)) ≤
        (∑ x, perspective f (a * p x) (q x)) + lambda * (1 - ∑ x, q x) := by
          linarith
    _ ≤ (∑ x, perspective f (a * p x) (q x)) +
        (1 - ∑ x, q x) * f 0 := by
          have := mul_le_mul_of_nonneg_right hlambda hr
          nlinarith

private theorem allCapped_coordinate_support {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (p : FinProb α) (hp : ∀ x, 0 < p x) (q : CappedVector α c) (x : α) :
    perspective f (a * p x) c + f 0 * (q x - c) ≤
      perspective f (a * p x) (q x) := by
  let ux := a * p x / c
  have hP : 0 < a * p x := mul_pos ha (hp x)
  have hux : 0 < ux := div_pos hP hc
  have hratio : a * p x = c * ux := by
    dsimp [ux]
    field_simp [hc.ne']
  have hsupp := perspective_supporting f hP (q.nonneg x) hc hux hratio
  have hgamma := gamma_le_map_zero f hux
  have hdiff : q x - c ≤ 0 := sub_nonpos.mpr (q.le_cap x)
  have hmul := mul_le_mul_of_nonpos_right hgamma hdiff
  linarith

/-- Optimality of the all-capped vector when its total mass is below one. -/
theorem allCappedVector_isOptimizer {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (p : FinProb α) (hp : ∀ x, 0 < p x)
    (hcard : c * Fintype.card α ≤ 1) :
    IsOptimizer f a p (allCappedVector c hc.le hcard) := by
  intro q
  let qstar := allCappedVector c hc.le hcard
  have hcoord := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦
    allCapped_coordinate_support f a c ha hc p hp q x
  dsimp [scaledCappedCost]
  have hstar : ∑ x, qstar x = c * Fintype.card α := by
    simp [qstar, mul_comm]
  have hlinear : ∑ x, f 0 * (q x - c) =
      f 0 * ((∑ x, q x) - c * Fintype.card α) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp [mul_comm]
  simp_rw [Finset.sum_add_distrib] at hcoord
  rw [hlinear] at hcoord
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  nlinarith

/-- **Lemma 9 (water filling).**

The probability vector is indexed by its support, expressed by `hp`.  In the
first case the same normalized vector `min c (t pₓ)` minimizes every scaled
objective for every admissible generator and every positive scale.  In the
second case the all-capped vector does so.  Thus the optimizer is independent
of both `f` and `a`, exactly as stated in the paper. -/
theorem paperLemma9 {α : Type*} [Fintype α]
    (c : ℝ) (hc : 0 < c) (p : FinProb α) (hp : ∀ x, 0 < p x) :
    (1 ≤ c * Fintype.card α →
      ∃ t : ℝ, ∃ ht : 1 ≤ t, ∃ hnorm : normalization c p t = 1,
        ∀ (f : AdmissibleGenerator) (a : ℝ), 0 < a →
          IsOptimizer f a p (normalizedVector c t p hc.le (zero_le_one.trans ht) hnorm)) ∧
    (∀ hcard : c * Fintype.card α < 1,
      ∀ (f : AdmissibleGenerator) (a : ℝ), 0 < a →
        IsOptimizer f a p (allCappedVector c hc.le hcard.le)) := by
  constructor
  · intro hcard
    obtain ⟨t, ht, hnorm⟩ := exists_normalizing_parameter c hc.le p hp hcard
    exact ⟨t, ht, hnorm, fun f a ha ↦
      normalizedVector_isOptimizer f a c t ha hc ht p hp hnorm⟩
  · intro hcard f a ha
    exact allCappedVector_isOptimizer f a c ha hc p hp hcard.le

end WaterFilling

end RandomnessExtraction
