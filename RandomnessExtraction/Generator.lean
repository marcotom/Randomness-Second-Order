import RandomnessExtraction.FiniteProbability
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Admissible generators and finite f-divergence
-/

open Filter Set
open scoped BigOperators Topology

namespace RandomnessExtraction

/-- The paper's admissibility assumptions on an `f`-divergence generator.
Only the nonnegative half-line is semantically relevant. -/
structure AdmissibleGenerator where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  convexOn_nonneg : ConvexOn ℝ (Set.Ici 0) toFun
  map_one : toFun 1 = 0
  sublinear_atTop : Tendsto (fun t : ℝ ↦ toFun t / t) atTop (𝓝 0)

namespace AdmissibleGenerator

instance : CoeFun AdmissibleGenerator (fun _ ↦ ℝ → ℝ) :=
  ⟨AdmissibleGenerator.toFun⟩

variable (f : AdmissibleGenerator)

@[simp]
theorem apply_one : f 1 = 0 := f.map_one

theorem continuousAt (x : ℝ) : ContinuousAt f x := f.continuous.continuousAt

private theorem tendsto_secant_atTop (x : ℝ) :
    Tendsto (fun z : ℝ ↦ (f z - f x) / (z - x)) atTop (𝓝 0) := by
  have hconstdiv (c : ℝ) : Tendsto (fun z : ℝ ↦ c / z) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero :
        Tendsto (fun z : ℝ ↦ z⁻¹) atTop (𝓝 0)))
  have hxdiv := hconstdiv x
  have hfxdiv := hconstdiv (f x)
  have hden : Tendsto (fun z : ℝ ↦ 1 - x / z) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub hxdiv using 1 <;> simp
  have hquot : Tendsto
      (fun z : ℝ ↦ (f z / z - f x / z) / (1 - x / z)) atTop (𝓝 0) := by
    have ht := (f.sublinear_atTop.sub hfxdiv).div hden (by norm_num : (1 : ℝ) ≠ 0)
    have ht0 : Tendsto
        ((fun z : ℝ ↦ f z / z - f x / z) /
          (fun z : ℝ ↦ 1 - x / z)) atTop (𝓝 0) := by
      simpa using ht
    exact ht0.congr' (Eventually.of_forall fun _ ↦ rfl)
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop x] with z hz0 hzx
  have hz : z ≠ 0 := hz0.ne'
  have hzx0 : z - x ≠ 0 := sub_ne_zero.mpr hzx.ne'
  field_simp

/-- The paper's assumptions force every admissible generator to be
nonincreasing on the nonnegative half-line. -/
theorem antitoneOn_nonneg : AntitoneOn f (Set.Ici 0) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  · have hslope : (f y - f x) / (y - x) ≤ 0 := by
      apply ge_of_tendsto (f.tendsto_secant_atTop x)
      filter_upwards [eventually_gt_atTop y] with z hyz
      exact f.convexOn_nonneg.secant_mono hx hy (hy.trans hyz.le)
        hxy.ne' (hxy.trans hyz).ne' hyz.le
    rcases (div_nonpos_iff.mp hslope) with hbad | hgood
    · exact (not_lt_of_ge hbad.2 (sub_pos.mpr hxy)).elim
    · exact sub_nonpos.mp hgood.1

theorem nonneg_of_mem_unit {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ f x := by
  rw [← f.map_one]
  exact f.antitoneOn_nonneg hx0 (zero_le_one : (0 : ℝ) ≤ 1) hx1

theorem map_zero_nonneg : 0 ≤ f 0 := f.nonneg_of_mem_unit le_rfl zero_le_one

end AdmissibleGenerator

/-- The lower-semicontinuous perspective, specialized to the paper's
zero-recession case. -/
noncomputable def perspective (f : AdmissibleGenerator) (p q : ℝ) : ℝ :=
  if q = 0 then 0 else q * f (p / q)

@[simp]
theorem perspective_zero_right (f : AdmissibleGenerator) (p : ℝ) :
    perspective f p 0 = 0 := by simp [perspective]

@[simp]
theorem perspective_of_pos (f : AdmissibleGenerator) {p q : ℝ} (hq : 0 < q) :
    perspective f p q = q * f (p / q) := by simp [perspective, hq.ne']

@[simp]
theorem perspective_self (f : AdmissibleGenerator) {q : ℝ} (hq : 0 ≤ q) :
    perspective f q q = 0 := by
  rcases hq.eq_or_lt with rfl | hq
  · simp
  · simp [perspective, hq.ne', f.map_one]

/-- Positive homogeneity of the perspective. -/
theorem perspective_smul (f : AdmissibleGenerator) {r p q : ℝ}
    (hr : 0 ≤ r) :
    perspective f (r * p) (r * q) = r * perspective f p q := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [perspective]
  · by_cases hq : q = 0
    · simp [perspective, hq]
    · have hrq : r * q ≠ 0 := mul_ne_zero hr.ne' hq
      simp only [perspective, if_neg hq, if_neg hrq]
      have hratio : r * p / (r * q) = p / q := by
        field_simp [hr.ne', hq]
      rw [hratio]
      ring

/-- Finite `f`-divergence with the reference-zero value fixed by the
sublinear recession assumption. -/
noncomputable def fDivergence {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (P Q : FinProb α) : ℝ :=
  ∑ x, perspective f (P x) (Q x)

@[simp]
theorem fDivergence_self {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (P : FinProb α) : fDivergence f P P = 0 := by
  classical
  simp [fDivergence, perspective_self f (P.nonneg _)]

/-- A finite sum of perspectives dominates the perspective of the sums.
This is the finite joint-convexity inequality used to aggregate seed
coordinates in the optimized-reference converse. -/
theorem perspective_sum_le {ι : Type*} [Fintype ι]
    (f : AdmissibleGenerator) (P Q : ι → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i) :
    perspective f (∑ i, P i) (∑ i, Q i) ≤
      ∑ i, perspective f (P i) (Q i) := by
  classical
  by_cases hQsum : ∑ i, Q i = 0
  · have hQi : ∀ i, Q i = 0 := by
      intro i
      exact le_antisymm
        (by
          have := Finset.single_le_sum (fun j _ ↦ hQ j) (Finset.mem_univ i)
          simpa [hQsum] using this)
        (hQ i)
    simp [hQsum, hQi, perspective]
  · have hQsumpos : 0 < ∑ i, Q i :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ hQ i) (Ne.symm hQsum)
    let w : ι → ℝ := fun i ↦ Q i / ∑ j, Q j
    let u : ι → ℝ := fun i ↦ if Q i = 0 then 0 else P i / Q i
    have hw : ∀ i, 0 ≤ w i := fun i ↦ div_nonneg (hQ i) hQsumpos.le
    have hwsum : ∑ i, w i = 1 := by
      simp [w, div_eq_mul_inv, ← Finset.sum_mul, hQsum]
    have hu : ∀ i, 0 ≤ u i := by
      intro i
      simp only [u]
      split_ifs
      · exact le_rfl
      · exact div_nonneg (hP i) (hQ i)
    have havg_le : ∑ i, w i * u i ≤ (∑ i, P i) / ∑ i, Q i := by
      rw [div_eq_mul_inv]
      calc
        (∑ i, w i * u i) ≤ ∑ i, (P i) * (∑ j, Q j)⁻¹ := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hqi : Q i = 0
          · have hright : 0 ≤ P i * (∑ j, Q j)⁻¹ :=
              mul_nonneg (hP i) (inv_nonneg.mpr hQsumpos.le)
            simpa [w, u, hqi] using hright
          · have heq : w i * u i = P i * (∑ j, Q j)⁻¹ := by
              simp [w, u, hqi, div_eq_mul_inv]
              field_simp [hqi, hQsum]
            rw [heq]
        _ = (∑ i, P i) * (∑ j, Q j)⁻¹ := by rw [Finset.sum_mul]
    have hjensen := f.convexOn_nonneg.map_sum_le
      (t := Finset.univ) (w := w) (p := u)
      (fun i _ ↦ hw i) hwsum (fun i _ ↦ hu i)
    have havgnonneg : 0 ≤ ∑ i, w i * u i :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (hu i)
    have hratio_nonneg : 0 ≤ (∑ i, P i) / ∑ i, Q i :=
      div_nonneg (Finset.sum_nonneg fun i _ ↦ hP i) hQsumpos.le
    rw [perspective_of_pos f hQsumpos]
    calc
      (∑ i, Q i) * f ((∑ i, P i) / ∑ i, Q i) ≤
          (∑ i, Q i) * f (∑ i, w i * u i) := by
            gcongr
            exact f.antitoneOn_nonneg havgnonneg hratio_nonneg havg_le
      _ ≤ (∑ i, Q i) * ∑ i, w i * f (u i) := by
            gcongr
            simpa only [smul_eq_mul] using hjensen
      _ = ∑ i, perspective f (P i) (Q i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            by_cases hqi : Q i = 0
            · simp [w, u, hqi, perspective]
            · have hqipos : 0 < Q i := lt_of_le_of_ne (hQ i) (Ne.symm hqi)
              rw [perspective_of_pos f hqipos]
              simp [w, u, hqi]
              field_simp [hQsum]

/-- Nonnegativity of finite `f`-divergence under the paper's normalization. -/
theorem fDivergence_nonneg {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (P Q : FinProb α) :
    0 ≤ fDivergence f P Q := by
  calc
    0 = perspective f 1 1 := by simp [perspective, f.map_one]
    _ = perspective f (∑ x, P x) (∑ x, Q x) := by rw [P.sum_prob, Q.sum_prob]
    _ ≤ ∑ x, perspective f (P x) (Q x) :=
      perspective_sum_le f P Q P.nonneg Q.nonneg
    _ = fDivergence f P Q := rfl

end RandomnessExtraction
