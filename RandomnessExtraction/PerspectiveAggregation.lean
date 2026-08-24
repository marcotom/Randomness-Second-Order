import RandomnessExtraction.ConditionalCapped
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Perspective aggregation

This file formalizes Lemma 15.  Reference-zero summands are represented by
an explicit `if`; their value is zero, as prescribed by the paper's
zero-recession convention.
-/

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

namespace PerspectiveAggregation

variable {E : ℕ → Type} [∀ n, Fintype (E n)]

noncomputable def average (π : ∀ n, FinProb (E n))
    (q : ∀ n, E n → ℝ) (n : ℕ) : ℝ :=
  (π n).expect (q n)

noncomputable def scale (π R : FinProb (E n)) (e : E n) : ℝ :=
  if R e = 0 then 0 else π e / R e

noncomputable def objective (G : ∀ n, E n → ℝ → ℝ)
    (π : ∀ n, FinProb (E n)) (n : ℕ) (R : FinProb (E n)) : ℝ :=
  ∑ e, if R e = 0 then 0 else R e * G n e (π n e / R e)

noncomputable def value (G : ∀ n, E n → ℝ → ℝ)
    (π : ∀ n, FinProb (E n)) (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ R : FinProb (E n), v = objective G π n R}

def TightTypicalSets (π : ∀ n, FinProb (E n))
    (T : ∀ n, ℝ → Set (E n)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 < K ∧
    ∀ᶠ n in atTop, (π n).event (T n K)ᶜ < δ

def TypicalTailBounds (q : ∀ n, E n → ℝ)
    (T : ∀ n, ℝ → Set (E n)) : Prop :=
  ∀ K : ℝ, 0 < K → ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
    ∀ᶠ n in atTop, ∀ e, e ∈ T n K → η ≤ q n e ∧ q n e ≤ 1 - η

def TypicalLocalLimit (f : AdmissibleGenerator)
    (q : ∀ n, E n → ℝ) (G : ∀ n, E n → ℝ → ℝ)
    (T : ∀ n, ℝ → Set (E n)) : Prop :=
  ∀ K : ℝ, 0 < K → ∀ aMin aMax : ℝ, 0 < aMin → aMin < aMax →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ e, e ∈ T n K →
      ∀ a, a ∈ Set.Icc aMin aMax → |G n e a - f (a * q n e)| < ε

theorem scale_nonneg (π R : FinProb (E n)) (e : E n) :
    0 ≤ scale π R e := by
  unfold scale
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (π.nonneg e) (R.nonneg e)

theorem weighted_scale_le_one (π R : FinProb (E n)) :
    ∑ e, R e * scale π R e ≤ 1 := by
  calc
    (∑ e, R e * scale π R e) ≤ ∑ e, π e := by
      apply Finset.sum_le_sum
      intro e _
      by_cases hR : R e = 0
      · simp [scale, hR, π.nonneg e]
      · have hRpos : 0 < R e := lt_of_le_of_ne (R.nonneg e) (Ne.symm hR)
        simp [scale, hR]
        field_simp [hR]
        exact le_rfl
    _ = 1 := π.sum_prob

theorem objective_nonneg (f : AdmissibleGenerator)
    (π : ∀ n, FinProb (E n)) (q : ∀ n, E n → ℝ)
    (G : ∀ n, E n → ℝ → ℝ)
    (hG : ∀ n e a, 0 ≤ a → f a ≤ G n e a)
    (n : ℕ) (R : FinProb (E n)) : 0 ≤ objective G π n R := by
  let a : E n → ℝ := scale (π n) R
  have ha : ∀ e, 0 ≤ a e := scale_nonneg (π n) R
  have havg0 : 0 ≤ ∑ e, R e * a e :=
    Finset.sum_nonneg fun e _ ↦ mul_nonneg (R.nonneg e) (ha e)
  have havg1 : ∑ e, R e * a e ≤ 1 := weighted_scale_le_one (π n) R
  have hjensen := f.convexOn_nonneg.map_sum_le
    (t := Finset.univ) (w := R) (p := a)
    (fun e _ ↦ R.nonneg e) R.sum_prob (fun e _ ↦ ha e)
  have hzero : 0 ≤ ∑ e, R e * f (a e) := by
    calc
      0 = f 1 := f.map_one.symm
      _ ≤ f (∑ e, R e * a e) :=
        f.antitoneOn_nonneg havg0 (Set.mem_Ici.mpr zero_le_one) havg1
      _ ≤ ∑ e, R e * f (a e) := by simpa only [smul_eq_mul] using hjensen
  calc
    0 ≤ ∑ e, R e * f (a e) := hzero
    _ ≤ objective G π n R := by
      rw [objective]
      apply Finset.sum_le_sum
      intro e _
      by_cases hR0 : R e = 0
      · simp [a, scale, hR0]
      · have hRpos : 0 < R e := lt_of_le_of_ne (R.nonneg e) (Ne.symm hR0)
        simp only [if_neg hR0]
        rw [show a e = π n e / R e by simp [a, scale, hR0]]
        exact mul_le_mul_of_nonneg_left
          (hG n e _ (div_nonneg ((π n).nonneg e) hRpos.le))
          (R.nonneg e)

theorem value_nonneg (f : AdmissibleGenerator)
    (π : ∀ n, FinProb (E n)) (q : ∀ n, E n → ℝ)
    (G : ∀ n, E n → ℝ → ℝ)
    (hG : ∀ n e a, 0 ≤ a → f a ≤ G n e a) (n : ℕ) :
    0 ≤ value G π n := by
  apply le_csInf
  · exact ⟨objective G π n (π n), π n, rfl⟩
  · rintro v ⟨R, rfl⟩
    exact objective_nonneg f π q G hG n R

theorem value_le_objective (f : AdmissibleGenerator)
    (π : ∀ n, FinProb (E n)) (q : ∀ n, E n → ℝ)
    (G : ∀ n, E n → ℝ → ℝ)
    (hG : ∀ n e a, 0 ≤ a → f a ≤ G n e a)
    (n : ℕ) (R : FinProb (E n)) : value G π n ≤ objective G π n R := by
  apply csInf_le
  · exact ⟨0, by rintro v ⟨R', rfl⟩; exact objective_nonneg f π q G hG n R'⟩
  · exact ⟨R, rfl⟩

noncomputable def modifiedTail (q : ∀ n, E n → ℝ)
    (T : ∀ n, ℝ → Set (E n)) (n : ℕ) (K : ℝ) (e : E n) : ℝ :=
  if e ∈ T n K then q n e else 1

theorem modifiedTail_mem_unit (q : ∀ n, E n → ℝ)
    (T : ∀ n, ℝ → Set (E n))
    (hq0 : ∀ n e, 0 ≤ q n e) (hq1 : ∀ n e, q n e ≤ 1)
    (n : ℕ) (K : ℝ) (e : E n) :
    modifiedTail q T n K e ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases he : e ∈ T n K <;> simp [modifiedTail, he, hq0, hq1]

theorem modifiedAverage_error (π : ∀ n, FinProb (E n))
    (q : ∀ n, E n → ℝ) (T : ∀ n, ℝ → Set (E n))
    (hq0 : ∀ n e, 0 ≤ q n e) (hq1 : ∀ n e, q n e ≤ 1)
    (n : ℕ) (K : ℝ) :
    0 ≤ (π n).expect (modifiedTail q T n K) - average π q n ∧
      (π n).expect (modifiedTail q T n K) - average π q n ≤
        (π n).event (T n K)ᶜ := by
  constructor
  · unfold average
    apply sub_nonneg.mpr
    apply (π n).expect_mono
    intro e
    by_cases he : e ∈ T n K
    · simp [modifiedTail, he]
    · simp [modifiedTail, he, hq1 n e]
  · classical
    unfold average FinProb.expect FinProb.event
    rw [← Finset.sum_sub_distrib]
    simp only [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro e _
    by_cases he : e ∈ T n K
    · simp [modifiedTail, he]
    · have hec : e ∈ (T n K)ᶜ := he
      simp [modifiedTail, he, hec]
      exact mul_nonneg ((π n).nonneg e) (hq0 n e)

theorem average_nonneg (π : ∀ n, FinProb (E n))
    (q : ∀ n, E n → ℝ) (hq0 : ∀ n e, 0 ≤ q n e) (n : ℕ) :
    0 ≤ average π q n := by
  exact (π n).expect_nonneg (hq0 n)

theorem average_le_one (π : ∀ n, FinProb (E n))
    (q : ∀ n, E n → ℝ) (hq1 : ∀ n e, q n e ≤ 1) (n : ℕ) :
    average π q n ≤ 1 := by
  calc
    average π q n ≤ (π n).expect (fun _ ↦ (1 : ℝ)) :=
      (π n).expect_mono (hq1 n)
    _ = 1 := (π n).expect_const 1

/-- The tail-tilted reference in equation (94). -/
noncomputable def tiltedReference (π : ∀ n, FinProb (E n))
    (q : ∀ n, E n → ℝ) (hq0 : ∀ n e, 0 ≤ q n e)
    (n : ℕ) (hbar : 0 < average π q n) : FinProb (E n) where
  prob e := π n e * q n e / average π q n
  nonneg e := div_nonneg (mul_nonneg ((π n).nonneg e) (hq0 n e)) hbar.le
  sum_prob := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    change average π q n * (average π q n)⁻¹ = 1
    exact mul_inv_cancel₀ hbar.ne'

@[simp]
theorem tiltedReference_apply (π : ∀ n, FinProb (E n))
    (q : ∀ n, E n → ℝ) (hq0 : ∀ n e, 0 ≤ q n e)
    (n : ℕ) (hbar : 0 < average π q n) (e : E n) :
    tiltedReference π q hq0 n hbar e =
      π n e * q n e / average π q n := rfl

/-- Jensen step (88), including reference-zero coordinates. -/
theorem weighted_modifiedTail_jensen (f : AdmissibleGenerator)
    (π R : FinProb (E n)) (r : E n → ℝ) (hr : ∀ e, 0 ≤ r e) :
    f (π.expect r) ≤
      ∑ e, if R e = 0 then 0 else
        R e * f ((π e / R e) * r e) := by
  let a : E n → ℝ := scale π R
  let b : E n → ℝ := fun e ↦ a e * r e
  have ha : ∀ e, 0 ≤ a e := scale_nonneg π R
  have hb : ∀ e, 0 ≤ b e := fun e ↦ mul_nonneg (ha e) (hr e)
  have hjensen := f.convexOn_nonneg.map_sum_le
    (t := Finset.univ) (w := R) (p := b)
    (fun e _ ↦ R.nonneg e) R.sum_prob (fun e _ ↦ hb e)
  have hpartial : ∑ e, R e * b e ≤ π.expect r := by
    rw [FinProb.expect]
    apply Finset.sum_le_sum
    intro e _
    by_cases hR : R e = 0
    · rw [hR, zero_mul]
      exact mul_nonneg (π.nonneg e) (hr e)
    · have hRpos : 0 < R e := lt_of_le_of_ne (R.nonneg e) (Ne.symm hR)
      have heq : R e * b e = π e * r e := by
        dsimp [b, a, scale]
        simp only [if_neg hR]
        field_simp [hR]
      rw [heq]
  have hpartial0 : 0 ≤ ∑ e, R e * b e :=
    Finset.sum_nonneg fun e _ ↦ mul_nonneg (R.nonneg e) (hb e)
  have hfull0 : 0 ≤ π.expect r := π.expect_nonneg hr
  calc
    f (π.expect r) ≤ f (∑ e, R e * b e) :=
      f.antitoneOn_nonneg (Set.mem_Ici.mpr hpartial0)
        (Set.mem_Ici.mpr hfull0) hpartial
    _ ≤ ∑ e, R e * f (b e) := by simpa only [smul_eq_mul] using hjensen
    _ = ∑ e, if R e = 0 then 0 else R e * f ((π e / R e) * r e) := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases hR : R e = 0
      · simp [b, a, scale, hR]
      · simp [b, a, scale, hR]

/-- A pointwise four-region estimate used for the lower bound. -/
theorem objective_lower_of_regions (f : AdmissibleGenerator)
    (π : ∀ n, FinProb (E n)) (q : ∀ n, E n → ℝ)
    (G : ∀ n, E n → ℝ → ℝ) (T : ∀ n, ℝ → Set (E n))
    (hq0 : ∀ n e, 0 ≤ q n e) (hq1 : ∀ n e, q n e ≤ 1)
    (hG : ∀ n e a, 0 ≤ a → f a ≤ G n e a)
    (n : ℕ) (K η small A δ : ℝ)
    (hsmall : 0 < small) (hA : small < A) (hδ : 0 ≤ δ)
    (hTail : ∀ e, e ∈ T n K → η ≤ q n e)
    (hclose : ∀ u v, u ∈ Set.Icc (0 : ℝ) small →
      v ∈ Set.Icc (0 : ℝ) small → |f u - f v| ≤ δ)
    (hlocal : ∀ e, e ∈ T n K → ∀ a, a ∈ Set.Icc small A →
      |G n e a - f (a * q n e)| ≤ δ)
    (hlargeA : ∀ u, A < u → |f u / u| ≤ δ)
    (hlargeEta : ∀ u, A * η < u → |f u / u| ≤ δ)
    (hη0 : 0 < η) :
    ∀ R : FinProb (E n),
      f ((π n).expect (modifiedTail q T n K)) - 4 * δ ≤
        objective G π n R := by
  intro R
  let r := modifiedTail q T n K
  have hr : ∀ e, 0 ≤ r e := fun e ↦
    (modifiedTail_mem_unit q T hq0 hq1 n K e).1
  have hjensen := weighted_modifiedTail_jensen f (π n) R r hr
  have hpoint (e : E n) :
      (if R e = 0 then 0 else R e * f ((π n e / R e) * r e)) -
          (R e * δ + 2 * π n e * δ) ≤
        if R e = 0 then 0 else R e * G n e (π n e / R e) := by
    by_cases hR0 : R e = 0
    · rw [hR0]
      simp only [if_pos, zero_mul, zero_add]
      rw [zero_sub]
      exact neg_nonpos.mpr
        (mul_nonneg (mul_nonneg (by norm_num) ((π n).nonneg e)) hδ)
    · have hRpos : 0 < R e := lt_of_le_of_ne (R.nonneg e) (Ne.symm hR0)
      let a := π n e / R e
      have ha0 : 0 ≤ a := div_nonneg ((π n).nonneg e) hRpos.le
      have hRa : R e * a = π n e := by
        dsimp [a]
        field_simp [hR0]
      simp only [if_neg hR0]
      by_cases heT : e ∈ T n K
      · have hq0e := hq0 n e
        have hq1e := hq1 n e
        have hre : r e = q n e := by simp [r, modifiedTail, heT]
        rw [hre]
        by_cases hasmall : a < small
        · have haq0 : 0 ≤ a * q n e := mul_nonneg ha0 hq0e
          have haqle : a * q n e ≤ a := mul_le_of_le_one_right ha0 hq1e
          have hcont := hclose a (a * q n e)
            ⟨ha0, hasmall.le⟩ ⟨haq0, haqle.trans hasmall.le⟩
          have hGlow := hG n e a ha0
          have hdiff : f (a * q n e) - δ ≤ f a := by
            linarith [neg_le_abs (f a - f (a * q n e))]
          have hRδ : 0 ≤ R e * δ := mul_nonneg (R.nonneg e) hδ
          have hπδ : 0 ≤ 2 * π n e * δ :=
            mul_nonneg (mul_nonneg (by norm_num) ((π n).nonneg e)) hδ
          have hm := mul_le_mul_of_nonneg_left (hdiff.trans hGlow) (R.nonneg e)
          linarith
        · by_cases haA : a ≤ A
          · have hloc := hlocal e heT a ⟨le_of_not_gt hasmall, haA⟩
            have hlower : f (a * q n e) - δ ≤ G n e a := by
              linarith [neg_abs_le (G n e a - f (a * q n e))]
            have hπδ : 0 ≤ 2 * π n e * δ :=
              mul_nonneg (mul_nonneg (by norm_num) ((π n).nonneg e)) hδ
            nlinarith [mul_le_mul_of_nonneg_left hlower (R.nonneg e)]
          · have haLarge : A < a := lt_of_not_ge haA
            have haqLarge : A * η < a * q n e := by
              have hApos : 0 < A := hsmall.trans hA
              have haPos : 0 < a := hApos.trans haLarge
              have hfirst : A * η < a * η :=
                mul_lt_mul_of_pos_right haLarge hη0
              have hsecond : a * η ≤ a * q n e :=
                mul_le_mul_of_nonneg_left (hTail e heT) haPos.le
              exact hfirst.trans_le hsecond
            have hfa := hlargeA a haLarge
            have hfaq := hlargeEta (a * q n e) haqLarge
            have haPos : 0 < a := hsmall.trans_le (le_of_not_gt hasmall)
            have haqPos : 0 < a * q n e := mul_pos haPos (hη0.trans_le (hTail e heT))
            have hfaAbs : |f a| ≤ a * δ := by
              have hm := mul_le_mul_of_nonneg_right hfa haPos.le
              rw [abs_div, abs_of_pos haPos, div_mul_cancel₀ _ haPos.ne'] at hm
              simpa [mul_comm] using hm
            have hfaqAbs : |f (a * q n e)| ≤ a * δ := by
              have hm := mul_le_mul_of_nonneg_right hfaq haqPos.le
              rw [abs_div, abs_of_pos haqPos, div_mul_cancel₀ _ haqPos.ne'] at hm
              have hqmul : δ * (a * q n e) ≤ a * δ := by
                calc
                  δ * (a * q n e) = (a * q n e) * δ := by ring
                  _ ≤ a * δ := mul_le_mul_of_nonneg_right
                    (mul_le_of_le_one_right ha0 (hq1 n e)) hδ
              exact hm.trans hqmul
            have hdiff : f (a * q n e) - f a ≤ 2 * a * δ := by
              linarith [le_abs_self (f (a * q n e)), neg_le_abs (f a)]
            have hGlow := hG n e a ha0
            have hmul := mul_le_mul_of_nonneg_left
              (show f (a * q n e) - 2 * a * δ ≤ G n e a by linarith)
              (R.nonneg e)
            rw [mul_sub] at hmul
            have herror : R e * (2 * a * δ) = 2 * π n e * δ := by
              calc
                R e * (2 * a * δ) = 2 * (R e * a) * δ := by ring
                _ = 2 * π n e * δ := by rw [hRa]
            rw [herror] at hmul
            linarith [mul_nonneg (R.nonneg e) hδ]
      · have hre : r e = 1 := by simp [r, modifiedTail, heT]
        rw [hre, mul_one]
        have hGlow := hG n e a ha0
        have herr : 0 ≤ R e * δ + 2 * π n e * δ :=
          add_nonneg (mul_nonneg (R.nonneg e) hδ)
            (mul_nonneg (mul_nonneg (by norm_num) ((π n).nonneg e)) hδ)
        linarith [mul_le_mul_of_nonneg_left hGlow (R.nonneg e)]
  have hsumPoint := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) ↦ hpoint e
  have herrsum :
      ∑ e, (R e * δ + 2 * π n e * δ) = 3 * δ := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, R.sum_prob, one_mul]
    have hpisum : ∑ e, 2 * π n e = 2 := by
      rw [← Finset.mul_sum, (π n).sum_prob]
      norm_num
    rw [← Finset.sum_mul, hpisum]
    ring
  rw [Finset.sum_sub_distrib, herrsum] at hsumPoint
  change
    (∑ e, if R e = 0 then 0 else
      R e * f ((π n e / R e) * r e)) - 3 * δ ≤ objective G π n R at hsumPoint
  linarith

/-- The tilted-reference upper estimate used in the second half of Lemma 15. -/
theorem tilted_objective_upper (f : AdmissibleGenerator)
    (π : ∀ n, FinProb (E n)) (q : ∀ n, E n → ℝ)
    (G : ∀ n, E n → ℝ → ℝ) (T : ∀ n, ℝ → Set (E n))
    (hq0 : ∀ n e, 0 ≤ q n e) (hq1 : ∀ n e, q n e ≤ 1)
    (hGupper : ∀ n e a, 0 ≤ a → G n e a ≤ f 0)
    (n : ℕ) (K η aMin aMax δ : ℝ)
    (hη0 : 0 < η) (haMin : 0 < aMin) (hδ : 0 ≤ δ)
    (hbar : 0 < average π q n)
    (hbarMin : aMin ≤ average π q n)
    (hbarMax : average π q n ≤ aMax * η)
    (hTail : ∀ e, e ∈ T n K → η ≤ q n e)
    (hlocal : ∀ e, e ∈ T n K → ∀ a, a ∈ Set.Icc aMin aMax →
      |G n e a - f (a * q n e)| ≤ δ) :
    objective G π n (tiltedReference π q hq0 n hbar) ≤
      f (average π q n) + δ +
        f 0 / average π q n * (π n).event (T n K)ᶜ := by
  let R := tiltedReference π q hq0 n hbar
  let bar := average π q n
  have hbar0 : 0 ≤ bar := hbar.le
  have hbar1 : bar ≤ 1 := average_le_one π q hq1 n
  have hfbar0 : 0 ≤ f bar := f.nonneg_of_mem_unit hbar0 hbar1
  have hf00 : 0 ≤ f 0 := f.map_zero_nonneg
  have hpoint (e : E n) :
      (if R e = 0 then 0 else R e * G n e (π n e / R e)) ≤
        R e * (f bar + δ) +
          (if e ∈ (T n K)ᶜ then R e * f 0 else 0) := by
    by_cases hR0 : R e = 0
    · simp [hR0, hfbar0, hδ]
    · have hRpos : 0 < R e := lt_of_le_of_ne (R.nonneg e) (Ne.symm hR0)
      have hqPos : 0 < q n e := by
        by_contra hnot
        have hqZero : q n e = 0 := le_antisymm (le_of_not_gt hnot) (hq0 n e)
        apply hR0
        simp [R, tiltedReference_apply, hqZero]
      have hπPos : 0 < π n e := by
        by_contra hnot
        have hπZero : π n e = 0 :=
          le_antisymm (le_of_not_gt hnot) ((π n).nonneg e)
        apply hR0
        simp [R, tiltedReference_apply, hπZero]
      have hscale : π n e / R e = bar / q n e := by
        dsimp [R, bar, tiltedReference]
        field_simp [hbar.ne', hqPos.ne', hπPos.ne']
      by_cases heT : e ∈ T n K
      · have hqEta := hTail e heT
        have hscaleMin : aMin ≤ π n e / R e := by
          rw [hscale]
          apply (le_div_iff₀ hqPos).2
          calc
            aMin * q n e ≤ aMin := mul_le_of_le_one_right haMin.le (hq1 n e)
            _ ≤ bar := hbarMin
        have hscaleMax : π n e / R e ≤ aMax := by
          rw [hscale]
          apply (div_le_iff₀ hqPos).2
          exact hbarMax.trans (mul_le_mul_of_nonneg_left hqEta (by
            have : 0 ≤ aMax := by
              have := hbar.trans_le hbarMax
              nlinarith
            exact this))
        have hproduct : (π n e / R e) * q n e = bar := by
          rw [hscale]
          field_simp [hqPos.ne']
        have hloc := hlocal e heT (π n e / R e) ⟨hscaleMin, hscaleMax⟩
        have hGle : G n e (π n e / R e) ≤ f bar + δ := by
          rw [← hproduct]
          linarith [le_abs_self (G n e (π n e / R e) -
            f ((π n e / R e) * q n e))]
        simp only [if_neg hR0]
        have hec : e ∉ (T n K)ᶜ := by simpa using heT
        simp only [if_neg hec, add_zero]
        exact mul_le_mul_of_nonneg_left hGle (R.nonneg e)
      · have hec : e ∈ (T n K)ᶜ := heT
        simp only [if_neg hR0, if_pos hec]
        have ha0 : 0 ≤ π n e / R e :=
          div_nonneg ((π n).nonneg e) hRpos.le
        have hupper := mul_le_mul_of_nonneg_left
          (hGupper n e (π n e / R e) ha0) (R.nonneg e)
        have hfirst0 : 0 ≤ R e * (f bar + δ) :=
          mul_nonneg (R.nonneg e) (add_nonneg hfbar0 hδ)
        linarith
  have hsum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) ↦ hpoint e
  have hRsum : ∑ e, R e * (f bar + δ) = f bar + δ := by
    rw [← Finset.sum_mul, R.sum_prob, one_mul]
  have hout :
      (∑ e, if e ∈ (T n K)ᶜ then R e * f 0 else 0) ≤
        f 0 / bar * (π n).event (T n K)ᶜ := by
    have hcalc :
        (∑ e, if e ∈ (T n K)ᶜ then R e * f 0 else 0) ≤
          f 0 / bar * ∑ e with e ∈ (T n K)ᶜ, π n e := by
      calc
        (∑ e, if e ∈ (T n K)ᶜ then R e * f 0 else 0) =
          ∑ e with e ∈ (T n K)ᶜ, R e * f 0 := by
            rw [Finset.sum_filter]
        _ = ∑ e with e ∈ (T n K)ᶜ, (π n e * q n e / bar) * f 0 := by
            apply Finset.sum_congr rfl
            intro e _
            rfl
        _ ≤ ∑ e with e ∈ (T n K)ᶜ, (π n e / bar) * f 0 := by
            apply Finset.sum_le_sum
            intro e _
            have hpbar : 0 ≤ π n e / bar := div_nonneg ((π n).nonneg e) hbar.le
            have hqmul : π n e * q n e / bar ≤ π n e / bar := by
              calc
                π n e * q n e / bar = (π n e / bar) * q n e := by ring
                _ ≤ (π n e / bar) * 1 :=
                  mul_le_mul_of_nonneg_left (hq1 n e) hpbar
                _ = π n e / bar := mul_one _
            exact mul_le_mul_of_nonneg_right hqmul hf00
        _ = f 0 / bar * ∑ e with e ∈ (T n K)ᶜ, π n e := by
            simp_rw [div_eq_mul_inv]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _
            ring
    convert hcalc using 1 <;> simp only [FinProb.event] <;> congr 2 <;> ext e <;> simp
  rw [Finset.sum_add_distrib, hRsum] at hsum
  change objective G π n R ≤
    f bar + δ + (∑ e, if e ∈ (T n K)ᶜ then R e * f 0 else 0) at hsum
  have hfinal : objective G π n R ≤
      f bar + δ + f 0 / bar * (π n).event (T n K)ᶜ := by
    linarith
  simpa [R, bar] using hfinal

theorem value_eventually_lower (f : AdmissibleGenerator)
    (π : ∀ n, FinProb (E n)) (q : ∀ n, E n → ℝ)
    (G : ∀ n, E n → ℝ → ℝ) (T : ∀ n, ℝ → Set (E n))
    (q₀ : ℝ) (hq0 : ∀ n e, 0 ≤ q n e) (hq1 : ∀ n e, q n e ≤ 1)
    (hG : ∀ n e a, 0 ≤ a → f a ≤ G n e a)
    (haverage : Tendsto (average π q) atTop (𝓝 q₀))
    (htight : TightTypicalSets π T) (htail : TypicalTailBounds q T)
    (hlocal : TypicalLocalLimit f q G T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f q₀ - ε < value G π n := by
  intro ε hε
  let δ := ε / 16
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨ζ, hζ, hcontq⟩ :=
    (Metric.continuousAt_iff.mp (f.continuousAt q₀)) (ε / 4) (by linarith)
  let ξ := min (ζ / 4) 1
  have hξ : 0 < ξ := lt_min (div_pos hζ (by norm_num)) zero_lt_one
  have hξζ : ξ ≤ ζ / 4 := min_le_left _ _
  obtain ⟨K, hK, hbad⟩ := htight ξ hξ
  obtain ⟨η, hη, hηhalf, htailEv⟩ := htail K hK
  obtain ⟨κ, hκ, hcont0⟩ :=
    (Metric.continuousAt_iff.mp (f.continuousAt 0)) (δ / 2) (by linarith)
  let small := min (κ / 2) (1 / 2)
  have hsmall : 0 < small := lt_min (div_pos hκ (by norm_num)) (by norm_num)
  have hsmallκ : small < κ :=
    (min_le_left (κ / 2) (1 / 2)).trans_lt (by linarith)
  have hclose : ∀ u v : ℝ, u ∈ Set.Icc (0 : ℝ) small →
      v ∈ Set.Icc (0 : ℝ) small → |f u - f v| ≤ δ := by
    intro u v hu hv
    have hudist : dist u 0 < κ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
      exact hu.2.trans_lt hsmallκ
    have hvdist : dist v 0 < κ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hv.1]
      exact hv.2.trans_lt hsmallκ
    have hfu := hcont0 hudist
    have hfv := hcont0 hvdist
    rw [Real.dist_eq] at hfu hfv
    calc
      |f u - f v| = |(f u - f 0) + (f 0 - f v)| := by ring_nf
      _ ≤ |f u - f 0| + |f 0 - f v| := abs_add_le _ _
      _ = |f u - f 0| + |f v - f 0| := by rw [abs_sub_comm (f 0) (f v)]
      _ ≤ δ := by linarith
  have hfEvent : ∀ᶠ u : ℝ in atTop, |f u / u| < δ := by
    have hh := f.sublinear_atTop.eventually (Metric.ball_mem_nhds 0 hδ)
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
  obtain ⟨B, hB⟩ := eventually_atTop.1 hfEvent
  let C := max B 0 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right B 0]
  have hBC : B < C := by dsimp [C]; linarith [le_max_left B 0]
  let A := max (small + 1) (C / η + C)
  have hA : small < A :=
    (show small < small + 1 by linarith).trans_le (le_max_left _ _)
  have hCA : C < A := by
    have : C < C / η + C := by linarith [div_pos hC hη]
    exact this.trans_le (le_max_right _ _)
  have hCAη : C < A * η := by
    have hdiv : C / η * η = C := by field_simp [hη.ne']
    have hbase : C / η + C ≤ A := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_right hbase hη.le
    rw [add_mul, hdiv] at hmul
    nlinarith [mul_pos hC hη]
  have hlargeA : ∀ u : ℝ, A < u → |f u / u| ≤ δ := by
    intro u hu
    exact (hB u (hBC.trans (hCA.trans hu)).le).le
  have hlargeEta : ∀ u : ℝ, A * η < u → |f u / u| ≤ δ := by
    intro u hu
    exact (hB u (hBC.trans (hCAη.trans hu)).le).le
  have havgEv : ∀ᶠ n in atTop, |average π q n - q₀| < ξ := by
    have hh := haverage.eventually (Metric.ball_mem_nhds q₀ hξ)
    simpa only [Metric.mem_ball, Real.dist_eq] using hh
  have hlocalEv := hlocal K hK small A hsmall hA δ hδ
  filter_upwards [hbad, htailEv, havgEv, hlocalEv] with n hbadn htailn havgn hlocaln
  let ravg := (π n).expect (modifiedTail q T n K)
  have hrerr := modifiedAverage_error π q T hq0 hq1 n K
  have hrclose : |ravg - q₀| < ζ := by
    have havgBounds := abs_lt.mp havgn
    dsimp [ravg]
    have hdiff := hrerr.2
    have hdiff0 := hrerr.1
    rw [average] at hdiff hdiff0 havgBounds
    have hξζ' : 2 * ξ ≤ ζ := by linarith
    rw [abs_lt]
    constructor <;> linarith
  have hfclose : |f ravg - f q₀| < ε / 4 := by
    have := hcontq (show dist ravg q₀ < ζ by simpa [Real.dist_eq] using hrclose)
    simpa [Real.dist_eq] using this
  have hobj (R : FinProb (E n)) :
      f ravg - 4 * δ ≤ objective G π n R := by
    exact objective_lower_of_regions f π q G T hq0 hq1 hG n K η small A δ
      hsmall hA hδ.le (fun e he ↦ (htailn e he).1) hclose
      (fun e he a ha ↦ (hlocaln e he a ha).le) hlargeA hlargeEta hη R
  have hvalue : f ravg - 4 * δ ≤ value G π n := by
    apply le_csInf
    · exact ⟨objective G π n (π n), π n, rfl⟩
    · rintro v ⟨R, rfl⟩
      exact hobj R
  dsimp [δ] at hvalue
  linarith [abs_lt.mp hfclose]

theorem value_eventually_upper (f : AdmissibleGenerator)
    (π : ∀ n, FinProb (E n)) (q : ∀ n, E n → ℝ)
    (G : ∀ n, E n → ℝ → ℝ) (T : ∀ n, ℝ → Set (E n))
    (q₀ : ℝ) (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1)
    (hq0 : ∀ n e, 0 ≤ q n e) (hq1 : ∀ n e, q n e ≤ 1)
    (hGlower : ∀ n e a, 0 ≤ a → f a ≤ G n e a)
    (hGupper : ∀ n e a, 0 ≤ a → G n e a ≤ f 0)
    (haverage : Tendsto (average π q) atTop (𝓝 q₀))
    (htight : TightTypicalSets π T) (htail : TypicalTailBounds q T)
    (hlocal : TypicalLocalLimit f q G T) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, value G π n < f q₀ + ε := by
  intro ε hε
  have hf00 : 0 ≤ f 0 := f.map_zero_nonneg
  let C := 2 * f 0 / q₀
  have hC0 : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) hf00) hq₀.le
  have hC1 : 0 < C + 1 := by linarith
  let ξ := ε / (8 * (C + 1))
  have hξ : 0 < ξ := div_pos hε (mul_pos (by norm_num) hC1)
  have hCξ : C * ξ < ε / 8 := by
    have hratio : C / (C + 1) < 1 := (div_lt_one hC1).2 (by linarith)
    calc
      C * ξ = (ε / 8) * (C / (C + 1)) := by
        dsimp [ξ]
        field_simp [hC1.ne']
      _ < (ε / 8) * 1 :=
        mul_lt_mul_of_pos_left hratio (div_pos hε (by norm_num))
      _ = ε / 8 := mul_one _
  obtain ⟨ζ, hζ, hcontq⟩ :=
    (Metric.continuousAt_iff.mp (f.continuousAt q₀)) (ε / 4) (by linarith)
  let r := min (q₀ / 2) ζ
  have hr : 0 < r := lt_min (div_pos hq₀ (by norm_num)) hζ
  obtain ⟨K, hK, hbad⟩ := htight ξ hξ
  obtain ⟨η, hη, hηhalf, htailEv⟩ := htail K hK
  let aMin := q₀ / 2
  let aMax := 2 / η
  have haMin : 0 < aMin := div_pos hq₀ (by norm_num)
  have haMax : aMin < aMax := by
    have hetaLtOne : η < 1 := hηhalf.trans (by norm_num)
    have haMaxTwo : 2 < aMax := by
      dsimp [aMax]
      exact (lt_div_iff₀ hη).2 (by nlinarith)
    dsimp [aMin]
    linarith
  have havgEv : ∀ᶠ n in atTop, |average π q n - q₀| < r := by
    have hh := haverage.eventually (Metric.ball_mem_nhds q₀ hr)
    simpa only [Metric.mem_ball, Real.dist_eq] using hh
  have hlocalEv := hlocal K hK aMin aMax haMin haMax (ε / 4) (by linarith)
  filter_upwards [hbad, htailEv, havgEv, hlocalEv] with n hbadn htailn havgn hlocaln
  let bar := average π q n
  have havgBounds := abs_lt.mp havgn
  have hbarMin : aMin ≤ bar := by
    dsimp [aMin, bar]
    have hrq : r ≤ q₀ / 2 := min_le_left _ _
    linarith
  have hbar : 0 < bar := haMin.trans_le hbarMin
  have hbarMax : bar ≤ aMax * η := by
    have havg1 := average_le_one π q hq1 n
    have hproduct : aMax * η = 2 := by
      dsimp [aMax]
      field_simp [hη.ne']
    dsimp [bar]
    rw [hproduct]
    linarith
  have hfclose : |f bar - f q₀| < ε / 4 := by
    have hrζ : r ≤ ζ := min_le_right _ _
    have hdist : dist bar q₀ < ζ := by
      rw [Real.dist_eq]
      exact havgn.trans_le hrζ
    have := hcontq hdist
    simpa [Real.dist_eq] using this
  have hobj := tilted_objective_upper f π q G T hq0 hq1 hGupper
    n K η aMin aMax (ε / 4) hη haMin (by linarith) hbar hbarMin hbarMax
    (fun e he ↦ (htailn e he).1)
    (fun e he a ha ↦ (hlocaln e he a ha).le)
  have hcoef : f 0 / bar ≤ C := by
    apply (div_le_iff₀ hbar).2
    have hCbar := mul_le_mul_of_nonneg_left hbarMin hC0
    have hidentity : C * aMin = f 0 := by
      dsimp [C, aMin]
      field_simp [hq₀.ne']
    rw [hidentity] at hCbar
    exact hCbar
  have htailTerm : f 0 / bar * (π n).event (T n K)ᶜ < ε / 8 := by
    calc
      f 0 / bar * (π n).event (T n K)ᶜ ≤
          C * (π n).event (T n K)ᶜ :=
        mul_le_mul_of_nonneg_right hcoef ((π n).event_nonneg _)
      _ ≤ C * ξ := mul_le_mul_of_nonneg_left hbadn.le hC0
      _ < ε / 8 := hCξ
  have hvle := value_le_objective f π q G hGlower n
    (tiltedReference π q hq0 n hbar)
  dsimp [bar] at hobj hvle htailTerm hfclose
  linarith [hvle.trans hobj, abs_lt.mp hfclose]

/-- Lemma 15 (Perspective aggregation). -/
theorem paperLemma15 (f : AdmissibleGenerator)
    (π : ∀ n, FinProb (E n)) (q : ∀ n, E n → ℝ)
    (G : ∀ n, E n → ℝ → ℝ) (T : ∀ n, ℝ → Set (E n))
    (q₀ : ℝ) (hq₀0 : 0 < q₀) (hq₀1 : q₀ < 1)
    (hq0 : ∀ n e, 0 ≤ q n e) (hq1 : ∀ n e, q n e ≤ 1)
    (hGlower : ∀ n e a, 0 ≤ a → f a ≤ G n e a)
    (hGupper : ∀ n e a, 0 ≤ a → G n e a ≤ f 0)
    (haverage : Tendsto (average π q) atTop (𝓝 q₀))
    (htight : TightTypicalSets π T) (htail : TypicalTailBounds q T)
    (hlocal : TypicalLocalLimit f q G T) :
    Tendsto (value G π) atTop (𝓝 (f q₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlower := value_eventually_lower f π q G T q₀ hq0 hq1 hGlower
    haverage htight htail hlocal ε hε
  have hupper := value_eventually_upper f π q G T q₀ hq₀0 hq₀1 hq0 hq1 hGlower
    hGupper haverage htight htail hlocal ε hε
  filter_upwards [hlower, hupper] with n hlo hup
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith


end PerspectiveAggregation

end RandomnessExtraction
