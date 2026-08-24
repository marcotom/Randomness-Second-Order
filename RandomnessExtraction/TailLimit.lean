import RandomnessExtraction.ProbabilityRepresentation
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Locally uniform scaled tail limit

This file formalizes Lemma 11 of the paper.  The hypotheses below spell out
the two probabilistic limits in the statement using finite sums and the
eventually quantifier.  This avoids introducing a measure-space wrapper for a
finite probability vector and keeps the declaration directly reusable for
the conditional product fibres later in the proof.
-/

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

namespace TailLimit

/-- Probability of an event under a finite law. -/
noncomputable def eventProbability {α : Type*} [Fintype α]
    (p : FinProb α) (E : α → Prop) [DecidablePred E] : ℝ :=
  ∑ x ∈ Finset.univ.filter E, p x

theorem eventProbability_nonneg {α : Type*} [Fintype α]
    (p : FinProb α) (E : α → Prop) [DecidablePred E] :
    0 ≤ eventProbability p E :=
  Finset.sum_nonneg fun x _ ↦ p.nonneg x

theorem eventProbability_le_one {α : Type*} [Fintype α]
    (p : FinProb α) (E : α → Prop) [DecidablePred E] :
    eventProbability p E ≤ 1 := by
  rw [← p.sum_prob]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun x _ _ ↦ p.nonneg x)

theorem eventProbability_mono {α : Type*} [Fintype α]
    (p : FinProb α) (E F : α → Prop) [DecidablePred E] [DecidablePred F]
    (hEF : ∀ x, E x → F x) :
    eventProbability p E ≤ eventProbability p F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hEF x hx
  · exact fun x _ _ ↦ p.nonneg x

theorem eventProbability_le_add {α : Type*} [Fintype α]
    (p : FinProb α) (E F G : α → Prop)
    [DecidablePred E] [DecidablePred F] [DecidablePred G]
    (hEFG : ∀ x, E x → F x ∨ G x) :
    eventProbability p E ≤ eventProbability p F + eventProbability p G := by
  classical
  simp only [eventProbability, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hFnonneg : 0 ≤ if F x then p x else 0 := by
    split_ifs
    · exact p.nonneg x
    · exact le_rfl
  have hGnonneg : 0 ≤ if G x then p x else 0 := by
    split_ifs
    · exact p.nonneg x
    · exact le_rfl
  by_cases hE : E x
  · rcases hEFG x hE with hF | hG
    · simp only [hE, hF, if_pos]
      linarith
    · simp only [hE, hG, if_pos]
      linarith
  · simp only [hE, if_false]
    linarith

/-- `Pr{J_p ≥ h}`. -/
noncomputable def tailGE {α : Type*} [Fintype α]
    (p : FinProb α) (h : ℝ) : ℝ :=
  eventProbability p (fun x ↦ h ≤ ProbabilityRepresentation.surprisal p x)

/-- `Pr{|J_p-h-u| ≤ B}`. -/
noncomputable def windowProbability {α : Type*} [Fintype α]
    (p : FinProb α) (h u B : ℝ) : ℝ :=
  eventProbability p
    (fun x ↦ |ProbabilityRepresentation.surprisal p x - h - u| ≤ B)

/-- Equation (62), written without a supremum over the real interval. -/
def UniformAntiConcentration
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (p : ∀ n, FinProb (α n)) (h : ℕ → ℝ) : Prop :=
  ∀ K B : ℝ, 0 < K → 0 < B → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop, ∀ u : ℝ, |u| ≤ K → windowProbability (p n) (h n) u B < ε

/-- Local uniform convergence in equation (63), expressed by its epsilon
criterion. -/
def LocallyUniformScaledLimit
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (f : AdmissibleGenerator) (p : ∀ n, FinProb (α n))
    (h : ℕ → ℝ) (q : ℝ) : Prop :=
  ∀ aMin aMax : ℝ, 0 < aMin → aMin < aMax →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ a : ℝ, a ∈ Set.Icc aMin aMax →
        |scaledCappedValue f a ((2 : ℝ) ^ (-h n)) (p n) - f (a * q)| < ε

theorem tailGE_nonneg {α : Type*} [Fintype α] (p : FinProb α) (h : ℝ) :
    0 ≤ tailGE p h := eventProbability_nonneg p _

theorem tailGE_le_one {α : Type*} [Fintype α] (p : FinProb α) (h : ℝ) :
    tailGE p h ≤ 1 := eventProbability_le_one p _

theorem windowProbability_nonneg {α : Type*} [Fintype α]
    (p : FinProb α) (h u B : ℝ) : 0 ≤ windowProbability p h u B :=
  eventProbability_nonneg p _

theorem windowProbability_le_one {α : Type*} [Fintype α]
    (p : FinProb α) (h u B : ℝ) : windowProbability p h u B ≤ 1 :=
  eventProbability_le_one p _

theorem upperTail_le_tailGE {α : Type*} [Fintype α]
    (p : FinProb α) {h b : ℝ} (hhb : h ≤ b) :
    ProbabilityRepresentation.upperTail p b ≤ tailGE p h := by
  apply eventProbability_mono
  intro x hx
  exact hhb.trans hx.le

theorem upperTail_antitone {α : Type*} [Fintype α]
    (p : FinProb α) {b₁ b₂ : ℝ} (h : b₁ ≤ b₂) :
    ProbabilityRepresentation.upperTail p b₂ ≤
      ProbabilityRepresentation.upperTail p b₁ := by
  apply eventProbability_mono
  intro x hx
  exact h.trans_lt hx

/-- Moving the threshold a bounded distance changes the tail by at most one
fixed-width window probability. -/
theorem tailGE_le_upperTail_add_window {α : Type*} [Fintype α]
    (p : FinProb α) (h D : ℝ) (hD : 0 ≤ D) :
    tailGE p h ≤ ProbabilityRepresentation.upperTail p (h + D) +
      windowProbability p h (D / 2) (D / 2) := by
  apply eventProbability_le_add
  intro x hx
  by_cases hfar : h + D < ProbabilityRepresentation.surprisal p x
  · exact Or.inl hfar
  · right
    rw [abs_le]
    constructor <;> linarith [le_of_not_gt hfar]

theorem fixedWindow_tendsto_zero
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (p : ∀ n, FinProb (α n)) (h : ℕ → ℝ)
    (hAnti : UniformAntiConcentration α p h)
    {K B u : ℝ} (hK : 0 < K) (hB : 0 < B) (hu : |u| ≤ K) :
    Tendsto (fun n ↦ windowProbability (p n) (h n) u B) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le
      (windowProbability_nonneg (p n) (h n) u B)
  · intro a ha
    exact hAnti K B hK hB a ha |>.mono fun n hn ↦ hn u hu

/-- A bounded displacement of the tail threshold has the same limit.  This
is the uniform anti-concentration step used twice in Lemma 11. -/
theorem boundedShift_upperTail_tendsto
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (p : ∀ n, FinProb (α n)) (h b : ℕ → ℝ) (q D : ℝ)
    (hD : 0 < D)
    (hTail : Tendsto (fun n ↦ tailGE (p n) (h n)) atTop (𝓝 q))
    (hAnti : UniformAntiConcentration α p h)
    (hb : ∀ᶠ n in atTop, h n ≤ b n ∧ b n ≤ h n + D) :
    Tendsto (fun n ↦ ProbabilityRepresentation.upperTail (p n) (b n))
      atTop (𝓝 q) := by
  let W : ℕ → ℝ := fun n ↦ windowProbability (p n) (h n) (D / 2) (D / 2)
  have hW : Tendsto W atTop (𝓝 0) := by
    apply fixedWindow_tendsto_zero α p h hAnti (K := D) (B := D / 2) (u := D / 2)
    · exact hD
    · linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ D / 2)]
      linarith
  have hfar : Tendsto
      (fun n ↦ ProbabilityRepresentation.upperTail (p n) (h n + D))
      atTop (𝓝 q) := by
    have hlower : Tendsto (fun n ↦ tailGE (p n) (h n) - W n) atTop (𝓝 q) := by
      convert hTail.sub hW using 1 <;> simp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hTail
    · exact Eventually.of_forall fun n ↦ by
        have hle := tailGE_le_upperTail_add_window (p n) (h n) D hD.le
        dsimp [W]
        linarith
    · exact Eventually.of_forall fun n ↦
        upperTail_le_tailGE (p n) (show h n ≤ h n + D by linarith)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hfar hTail
  · filter_upwards [hb] with n hn
    exact upperTail_antitone (p n) hn.2
  · filter_upwards [hb] with n hn
    exact upperTail_le_tailGE (p n) hn.1

theorem normalization_mono {α : Type*} [Fintype α]
    (p : FinProb α) (c : ℝ) : Monotone (WaterFilling.normalization c p) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro x _
  dsimp [WaterFilling.normalization, WaterFilling.mass]
  exact min_le_min_left c (mul_le_mul_of_nonneg_right hst (p.nonneg x))

/-- At multiplier `2^D`, the normalization dominates `2^D` times the tail
above `h+D`. -/
theorem rpow_mul_upperTail_le_normalization {α : Type*} [Fintype α]
    (p : FinProb α) (hp : ∀ x, 0 < p x) (h D : ℝ) :
    (2 : ℝ) ^ D * ProbabilityRepresentation.upperTail p (h + D) ≤
      WaterFilling.normalization ((2 : ℝ) ^ (-h)) p ((2 : ℝ) ^ D) := by
  rw [ProbabilityRepresentation.upperTail, Finset.mul_sum]
  calc
    (∑ x ∈ Finset.univ.filter
        (fun x ↦ h + D < ProbabilityRepresentation.surprisal p x),
        (2 : ℝ) ^ D * p x) =
        ∑ x ∈ Finset.univ.filter
          (fun x ↦ h + D < ProbabilityRepresentation.surprisal p x),
          WaterFilling.mass ((2 : ℝ) ^ (-h)) ((2 : ℝ) ^ D) p x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [WaterFilling.mass, min_eq_right]
      have htail : h + D < ProbabilityRepresentation.surprisal p x :=
        (Finset.mem_filter.1 hx).2
      have hlog : Real.logb 2 ((2 : ℝ) ^ D) = D :=
        Real.logb_rpow (by norm_num) (by norm_num)
      have hncap : ¬(2 : ℝ) ^ (-h) ≤ (2 : ℝ) ^ D * p x := by
        rw [ProbabilityRepresentation.capped_iff_surprisal_le h ((2 : ℝ) ^ D)
          (Real.rpow_pos_of_pos (by norm_num) _) p hp x, hlog]
        exact not_le.mpr htail
      exact le_of_lt (lt_of_not_ge hncap)
    _ ≤ ∑ x, WaterFilling.mass ((2 : ℝ) ^ (-h)) ((2 : ℝ) ^ D) p x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro x _ _
      exact le_min (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (p.nonneg x))
    _ = WaterFilling.normalization ((2 : ℝ) ^ (-h)) p ((2 : ℝ) ^ D) := rfl

/-- The water multiplier, with an irrelevant default before the eventual
support condition becomes true. -/
noncomputable def waterMultiplier
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (p : ∀ n, FinProb (α n)) (hp : ∀ n x, 0 < p n x)
    (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  if hs : 1 ≤ (2 : ℝ) ^ (-h n) * Fintype.card (α n) then
    Classical.choose
      (WaterFilling.exists_normalizing_parameter ((2 : ℝ) ^ (-h n))
        (Real.rpow_nonneg (by norm_num) _) (p n) (hp n) hs)
  else 1

theorem waterMultiplier_spec
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (p : ∀ n, FinProb (α n)) (hp : ∀ n x, 0 < p n x)
    (h : ℕ → ℝ) (n : ℕ)
    (hs : 1 ≤ (2 : ℝ) ^ (-h n) * Fintype.card (α n)) :
    1 ≤ waterMultiplier α p hp h n ∧
      WaterFilling.normalization ((2 : ℝ) ^ (-h n)) (p n)
        (waterMultiplier α p hp h n) = 1 := by
  rw [waterMultiplier, dif_pos hs]
  exact ⟨Classical.choose_spec
      (WaterFilling.exists_normalizing_parameter ((2 : ℝ) ^ (-h n))
        (Real.rpow_nonneg (by norm_num) _) (p n) (hp n) hs) |>.1,
    Classical.choose_spec
      (WaterFilling.exists_normalizing_parameter ((2 : ℝ) ^ (-h n))
        (Real.rpow_nonneg (by norm_num) _) (p n) (hp n) hs) |>.2⟩

noncomputable def waterThreshold
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (p : ∀ n, FinProb (α n)) (hp : ∀ n x, 0 < p n x)
    (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  h n + Real.logb 2 (waterMultiplier α p hp h n)

/-- Equations (66) and the preceding water-level argument: the selected
water threshold stays in a fixed strip above `hₙ`. -/
theorem waterThreshold_eventually_bounded
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (p : ∀ n, FinProb (α n)) (hp : ∀ n x, 0 < p n x)
    (h : ℕ → ℝ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hTail : Tendsto (fun n ↦ tailGE (p n) (h n)) atTop (𝓝 q))
    (hAnti : UniformAntiConcentration α p h)
    (hSupport : ∀ᶠ n in atTop,
      1 < (2 : ℝ) ^ (-h n) * Fintype.card (α n)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n in atTop,
      h n ≤ waterThreshold α p hp h n ∧ waterThreshold α p hp h n ≤ h n + D := by
  let D : ℝ := 1 - Real.logb 2 q
  have hlogq : Real.logb 2 q < 0 := Real.logb_neg (by norm_num) hq0 hq1
  have hD : 0 < D := by dsimp [D]; linarith
  have hDtail : Tendsto
      (fun n ↦ ProbabilityRepresentation.upperTail (p n) (h n + D))
      atTop (𝓝 q) := by
    apply boundedShift_upperTail_tendsto α p h (fun n ↦ h n + D) q D hD hTail hAnti
    exact Eventually.of_forall fun n ↦ ⟨by linarith, le_rfl⟩
  have hDq : (2 : ℝ) ^ D * q = 2 := by
    dsimp [D]
    rw [Real.rpow_sub (by norm_num), Real.rpow_one,
      Real.rpow_logb (by norm_num) (by norm_num) hq0]
    field_simp [hq0.ne']
  have hscaled : Tendsto
      (fun n ↦ (2 : ℝ) ^ D *
        ProbabilityRepresentation.upperTail (p n) (h n + D))
      atTop (𝓝 2) := by
    have hh : Tendsto
        (fun n ↦ (2 : ℝ) ^ D *
          ProbabilityRepresentation.upperTail (p n) (h n + D))
        atTop (𝓝 ((2 : ℝ) ^ D * q)) := tendsto_const_nhds.mul hDtail
    rw [hDq] at hh
    exact hh
  have hgt : ∀ᶠ n in atTop,
      1 < (2 : ℝ) ^ D * ProbabilityRepresentation.upperTail (p n) (h n + D) :=
    (tendsto_order.1 hscaled).1 1 (by norm_num)
  refine ⟨D, hD, ?_⟩
  filter_upwards [hSupport, hgt] with n hs htail
  have hsweak : 1 ≤ (2 : ℝ) ^ (-h n) * Fintype.card (α n) := hs.le
  have hspec := waterMultiplier_spec α p hp h n hsweak
  let t := waterMultiplier α p hp h n
  have ht : 1 ≤ t := hspec.1
  have hnorm : WaterFilling.normalization ((2 : ℝ) ^ (-h n)) (p n) t = 1 := hspec.2
  have hnormD : 1 < WaterFilling.normalization ((2 : ℝ) ^ (-h n)) (p n)
      ((2 : ℝ) ^ D) :=
    htail.trans_le (rpow_mul_upperTail_le_normalization (p n) (hp n) (h n) D)
  have htD : t ≤ (2 : ℝ) ^ D := by
    by_contra hnot
    have hmono := normalization_mono (p n) ((2 : ℝ) ^ (-h n)) (le_of_not_ge hnot)
    rw [hnorm] at hmono
    linarith
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hlognonneg : 0 ≤ Real.logb 2 t := Real.logb_nonneg (by norm_num) ht
  have hlogle : Real.logb 2 t ≤ D := by
    calc
      Real.logb 2 t ≤ Real.logb 2 ((2 : ℝ) ^ D) :=
        Real.logb_le_logb_of_le (by norm_num) htpos htD
      _ = D := Real.logb_rpow (by norm_num) (by norm_num)
  change h n ≤ h n + Real.logb 2 t ∧ h n + Real.logb 2 t ≤ h n + D
  constructor <;> linarith

/-- Quantitative split of the truncated exponential moment into a far part
and a fixed-width strip. -/
theorem lowerMoment_le_rpow_add_window {α : Type*} [Fintype α]
    (p : FinProb α) (h b D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hb0 : h ≤ b) (hbD : b ≤ h + D) :
    ProbabilityRepresentation.lowerMoment p b ≤ (2 : ℝ) ^ (-B) +
      windowProbability p h (D / 2) (D / 2 + B) := by
  let J : α → ℝ := ProbabilityRepresentation.surprisal p
  let W : α → Prop := fun x ↦ |J x - h - D / 2| ≤ D / 2 + B
  calc
    ProbabilityRepresentation.lowerMoment p b =
        ∑ x, if J x ≤ b then p x * (2 : ℝ) ^ (J x - b) else 0 := by
      simp [ProbabilityRepresentation.lowerMoment, J, Finset.sum_filter]
    _ ≤ ∑ x, (p x * (2 : ℝ) ^ (-B) + if W x then p x else 0) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hxb : J x ≤ b
      · rw [if_pos hxb]
        by_cases hfar : J x ≤ b - B
        · have hrpow : (2 : ℝ) ^ (J x - b) ≤ (2 : ℝ) ^ (-B) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          have hmul := mul_le_mul_of_nonneg_left hrpow (p.nonneg x)
          have hWnonneg : 0 ≤ if W x then p x else 0 := by
            split_ifs
            · exact p.nonneg x
            · exact le_rfl
          linarith
        · have hnearLower : h - B < J x := by linarith [lt_of_not_ge hfar]
          have hW : W x := by
            dsimp [W]
            rw [abs_le]
            constructor <;> linarith
          rw [if_pos hW]
          have hrpow : (2 : ℝ) ^ (J x - b) ≤ 1 := by
            calc
              (2 : ℝ) ^ (J x - b) ≤ (2 : ℝ) ^ (0 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 1 := by simp
          have hmul := mul_le_mul_of_nonneg_left hrpow (p.nonneg x)
          have hpowNonneg : 0 ≤ (2 : ℝ) ^ (-B) := Real.rpow_nonneg (by norm_num) _
          nlinarith [mul_nonneg (p.nonneg x) hpowNonneg]
      · rw [if_neg hxb]
        have hfirst : 0 ≤ p x * (2 : ℝ) ^ (-B) :=
          mul_nonneg (p.nonneg x) (Real.rpow_nonneg (by norm_num) _)
        have hsecond : 0 ≤ if W x then p x else 0 := by
          split_ifs
          · exact p.nonneg x
          · exact le_rfl
        linarith
    _ = (2 : ℝ) ^ (-B) + windowProbability p h (D / 2) (D / 2 + B) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, p.sum_prob, one_mul]
      simp [windowProbability, eventProbability, W, J, Finset.sum_filter]

theorem lowerMoment_nonneg {α : Type*} [Fintype α]
    (p : FinProb α) (b : ℝ) :
    0 ≤ ProbabilityRepresentation.lowerMoment p b := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (p.nonneg x) (Real.rpow_nonneg (by norm_num) _)

theorem bounded_lowerMoment_tendsto_zero
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (p : ∀ n, FinProb (α n)) (h b : ℕ → ℝ) (D : ℝ) (hD : 0 < D)
    (hAnti : UniformAntiConcentration α p h)
    (hb : ∀ᶠ n in atTop, h n ≤ b n ∧ b n ≤ h n + D) :
    Tendsto (fun n ↦ ProbabilityRepresentation.lowerMoment (p n) (b n))
      atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (lowerMoment_nonneg (p n) (b n))
  · intro a ha
    let r : ℝ := min (a / 4) (1 / 2)
    have hr0 : 0 < r := by
      dsimp [r]
      exact lt_min (div_pos ha (by norm_num)) (by norm_num)
    have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
    let B : ℝ := -Real.logb 2 r
    have hlogr : Real.logb 2 r < 0 := Real.logb_neg (by norm_num) hr0 hr1
    have hB : 0 < B := by dsimp [B]; linarith
    have hpow : (2 : ℝ) ^ (-B) = r := by
      dsimp [B]
      rw [neg_neg]
      exact Real.rpow_logb (by norm_num) (by norm_num) hr0
    have hW : Tendsto
        (fun n ↦ windowProbability (p n) (h n) (D / 2) (D / 2 + B))
        atTop (𝓝 0) := by
      apply fixedWindow_tendsto_zero α p h hAnti
        (K := D) (B := D / 2 + B) (u := D / 2)
      · exact hD
      · linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ D / 2)]
        linarith
    have hWevent : ∀ᶠ n in atTop,
        windowProbability (p n) (h n) (D / 2) (D / 2 + B) < a / 2 :=
      (tendsto_order.1 hW).2 (a / 2) (by linarith)
    filter_upwards [hb, hWevent] with n hbn hWn
    have hbound := lowerMoment_le_rpow_add_window (p n) (h n) (b n) D B
      hD.le hB.le hbn.1 hbn.2
    rw [hpow] at hbound
    have hrle : r ≤ a / 4 := min_le_left _ _
    linarith

/-- Consequences of the water-level identity needed in the two terms of
equation (60). -/
theorem waterMultiplier_asymptotics
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (p : ∀ n, FinProb (α n)) (hp : ∀ n x, 0 < p n x)
    (h : ℕ → ℝ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hTail : Tendsto (fun n ↦ tailGE (p n) (h n)) atTop (𝓝 q))
    (hAnti : UniformAntiConcentration α p h)
    (hSupport : ∀ᶠ n in atTop,
      1 < (2 : ℝ) ^ (-h n) * Fintype.card (α n)) :
    Tendsto (fun n ↦ waterMultiplier α p hp h n) atTop (𝓝 (1 / q)) ∧
    Tendsto (fun n ↦ ProbabilityRepresentation.upperTail (p n)
      (waterThreshold α p hp h n)) atTop (𝓝 q) ∧
    Tendsto (fun n ↦ waterMultiplier α p hp h n *
      ProbabilityRepresentation.upperTail (p n) (waterThreshold α p hp h n))
      atTop (𝓝 1) ∧
    Tendsto (fun n ↦ ProbabilityRepresentation.lowerMoment (p n)
      (waterThreshold α p hp h n)) atTop (𝓝 0) := by
  obtain ⟨D, hD, hb⟩ := waterThreshold_eventually_bounded α p hp h q hq0 hq1
    hTail hAnti hSupport
  have hA : Tendsto (fun n ↦ ProbabilityRepresentation.upperTail (p n)
      (waterThreshold α p hp h n)) atTop (𝓝 q) :=
    boundedShift_upperTail_tendsto α p h (waterThreshold α p hp h) q D hD
      hTail hAnti hb
  have hC : Tendsto (fun n ↦ ProbabilityRepresentation.lowerMoment (p n)
      (waterThreshold α p hp h n)) atTop (𝓝 0) :=
    bounded_lowerMoment_tendsto_zero α p h (waterThreshold α p hp h) D hD hAnti hb
  have hR : Tendsto (fun n ↦ ProbabilityRepresentation.tailFunctional (p n)
      (waterThreshold α p hp h n)) atTop (𝓝 q) := by
    simpa [ProbabilityRepresentation.tailFunctional] using hA.add hC
  have hformula : ∀ᶠ n in atTop,
      waterMultiplier α p hp h n =
        1 / ProbabilityRepresentation.tailFunctional (p n)
          (waterThreshold α p hp h n) := by
    filter_upwards [hSupport] with n hs
    have hsweak : 1 ≤ (2 : ℝ) ^ (-h n) * Fintype.card (α n) := hs.le
    have hspec := waterMultiplier_spec α p hp h n hsweak
    let t := waterMultiplier α p hp h n
    have ht : 1 ≤ t := hspec.1
    have hnorm := hspec.2
    have hid := (ProbabilityRepresentation.paperLemma10 (h n) t ht (p n) (hp n) hs hnorm).1
    have hpow : (2 : ℝ) ^ (waterThreshold α p hp h n - h n) = t := by
      simpa [waterThreshold, t] using
        ProbabilityRepresentation.rpow_waterLevel_sub_threshold (h n) t
          (zero_lt_one.trans_le ht)
    have hid' : 1 = (2 : ℝ) ^ (waterThreshold α p hp h n - h n) *
        ProbabilityRepresentation.tailFunctional (p n)
          (waterThreshold α p hp h n) := by
      simpa [waterThreshold, t] using hid
    change t = 1 / ProbabilityRepresentation.tailFunctional (p n)
      (waterThreshold α p hp h n)
    rw [hpow] at hid'
    have hRne : ProbabilityRepresentation.tailFunctional (p n)
        (waterThreshold α p hp h n) ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hid'
      norm_num at hid'
    field_simp [hRne]
    linarith
  have htendInv : Tendsto (fun n ↦
      1 / ProbabilityRepresentation.tailFunctional (p n)
        (waterThreshold α p hp h n)) atTop (𝓝 (1 / q)) :=
    tendsto_const_nhds.div hR hq0.ne'
  have ht : Tendsto (fun n ↦ waterMultiplier α p hp h n)
      atTop (𝓝 (1 / q)) := htendInv.congr'
        (hformula.mono fun _ hn ↦ hn.symm)
  have htA : Tendsto (fun n ↦ waterMultiplier α p hp h n *
      ProbabilityRepresentation.upperTail (p n) (waterThreshold α p hp h n))
      atTop (𝓝 1) := by
    have hh := ht.mul hA
    have hlimit : (1 / q) * q = 1 := by field_simp [hq0.ne']
    rw [hlimit] at hh
    exact hh
  exact ⟨ht, hA, htA, hC⟩

theorem abs_generator_le_endpoints (f : AdmissibleGenerator)
    {L x U : ℝ} (hL : 0 ≤ L) (hLx : L ≤ x) (hxU : x ≤ U) :
    |f x| ≤ |f L| + |f U| := by
  have hx0 : 0 ≤ x := hL.trans hLx
  have hU0 : 0 ≤ U := hx0.trans hxU
  have hupper : f x ≤ f L := f.antitoneOn_nonneg hL hx0 hLx
  have hlower : f U ≤ f x := f.antitoneOn_nonneg hx0 hU0 hxU
  rw [abs_le]
  constructor
  · have hneg : -|f U| ≤ f U := neg_abs_le (f U)
    have habsL : 0 ≤ |f L| := abs_nonneg _
    linarith
  · have habsU : 0 ≤ |f U| := abs_nonneg _
    exact hupper.trans (by linarith [le_abs_self (f L)])

/-- Uniform convergence of the uncapped term in equation (60). -/
theorem uncappedTerm_locallyUniform
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (f : AdmissibleGenerator) (p : ∀ n, FinProb (α n))
    (hp : ∀ n x, 0 < p n x) (h : ℕ → ℝ)
    (q aMin aMax : ℝ) (hq : 0 < q) (haMin : 0 < aMin) (haMM : aMin < aMax)
    (ht : Tendsto (fun n ↦ waterMultiplier α p hp h n) atTop (𝓝 (1 / q)))
    (htA : Tendsto (fun n ↦ waterMultiplier α p hp h n *
      ProbabilityRepresentation.upperTail (p n) (waterThreshold α p hp h n))
      atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ a : ℝ, a ∈ Set.Icc aMin aMax →
      |waterMultiplier α p hp h n *
          ProbabilityRepresentation.upperTail (p n) (waterThreshold α p hp h n) *
          f (a / waterMultiplier α p hp h n) - f (a * q)| < ε := by
  intro ε hε
  let L := aMin * q / 2
  let U := 2 * aMax * q
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLU : L ≤ U := by
    dsimp [L, U]
    nlinarith [mul_pos haMin hq, mul_pos (haMin.trans haMM) hq]
  have huc : UniformContinuousOn f (Set.Icc L U) :=
    isCompact_Icc.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ, hδ, hδf⟩ := (Metric.uniformContinuousOn_iff.1 huc) (ε / 2) (by linarith)
  let C := |f L| + |f U| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hqinv : (1 / q)⁻¹ = q := by field_simp [hq.ne']
  have hinv : Tendsto (fun n ↦ (waterMultiplier α p hp h n)⁻¹) atTop (𝓝 q) := by
    have hh := ht.inv₀ (by positivity : (1 / q) ≠ 0)
    rw [hqinv] at hh
    exact hh
  have htlower : 1 / (2 * q) < 1 / q := by
    rw [div_lt_div_iff₀ (by positivity : 0 < 2 * q) hq]
    nlinarith
  have htupper : 1 / q < 2 / q := by
    rw [div_lt_div_iff₀ hq hq]
    nlinarith
  have htBounds : ∀ᶠ n in atTop,
      1 / (2 * q) < waterMultiplier α p hp h n ∧
        waterMultiplier α p hp h n < 2 / q :=
    ((tendsto_order.1 ht).1 _ htlower).and ((tendsto_order.1 ht).2 _ htupper)
  have hInvClose : ∀ᶠ n in atTop,
      |(waterMultiplier α p hp h n)⁻¹ - q| < δ / aMax := by
    have hδa : 0 < δ / aMax := div_pos hδ (haMin.trans haMM)
    have hh := hinv.eventually (Metric.ball_mem_nhds q hδa)
    simpa [Metric.mem_ball, Real.dist_eq] using hh
  have hCoeffClose : ∀ᶠ n in atTop,
      |waterMultiplier α p hp h n *
        ProbabilityRepresentation.upperTail (p n) (waterThreshold α p hp h n) - 1| <
          ε / (2 * C) := by
    have heC : 0 < ε / (2 * C) := div_pos hε (mul_pos two_pos hC)
    have hh := htA.eventually (Metric.ball_mem_nhds 1 heC)
    simpa [Metric.mem_ball, Real.dist_eq] using hh
  filter_upwards [htBounds, hInvClose, hCoeffClose] with n htn hinvN hcoefN
  intro a ha
  have ha0 : 0 ≤ a := haMin.le.trans ha.1
  let t := waterMultiplier α p hp h n
  let A := ProbabilityRepresentation.upperTail (p n) (waterThreshold α p hp h n)
  have htpos : 0 < t := by
    have hbase : 0 < 1 / (2 * q) := one_div_pos.mpr (mul_pos two_pos hq)
    dsimp [t]
    exact hbase.trans htn.1
  have hxLower : L ≤ a / t := by
    rw [le_div_iff₀ htpos]
    have htU : t < 2 / q := htn.2
    have hcalc : L * (2 / q) = aMin := by
      dsimp [L]
      field_simp [hq.ne']
    have hLt : L * t ≤ aMin := by
      have := mul_le_mul_of_nonneg_left htU.le hL
      rwa [hcalc] at this
    exact hLt.trans ha.1
  have hxUpper : a / t ≤ U := by
    rw [div_le_iff₀ htpos]
    have htL : 1 / (2 * q) < t := htn.1
    have hcalc : U * (1 / (2 * q)) = aMax := by
      dsimp [U]
      field_simp [hq.ne']
    have haU : aMax ≤ U * t := by
      have hU0 : 0 ≤ U := by
        dsimp [U]
        exact mul_nonneg (mul_nonneg (by norm_num) (haMin.trans haMM).le) hq.le
      have := mul_le_mul_of_nonneg_left htL.le hU0
      rwa [hcalc] at this
    exact ha.2.trans haU
  have hyLower : L ≤ a * q := by
    dsimp [L]
    nlinarith [mul_le_mul_of_nonneg_right ha.1 hq.le]
  have hyUpper : a * q ≤ U := by
    dsimp [U]
    nlinarith [mul_le_mul_of_nonneg_right ha.2 hq.le]
  have hdist : dist (a / t) (a * q) < δ := by
    rw [Real.dist_eq]
    have heq : a / t - a * q = a * (t⁻¹ - q) := by
      rw [div_eq_mul_inv]
      ring
    rw [heq, abs_mul, abs_of_nonneg ha0]
    have haPos : 0 < a := haMin.trans_le ha.1
    have hmul := mul_lt_mul_of_pos_left hinvN haPos
    have haa : a * (δ / aMax) ≤ δ := by
      calc
        a * (δ / aMax) ≤ aMax * (δ / aMax) :=
          mul_le_mul_of_nonneg_right ha.2 (div_nonneg hδ.le (haMin.trans haMM).le)
        _ = δ := by field_simp [(haMin.trans haMM).ne']
    exact hmul.trans_le haa
  have hfclose : |f (a / t) - f (a * q)| < ε / 2 := by
    simpa [Real.dist_eq] using hδf (a / t) ⟨hxLower, hxUpper⟩
      (a * q) ⟨hyLower, hyUpper⟩ hdist
  have hfbound : |f (a / t)| < C := by
    have := abs_generator_le_endpoints f hL hxLower hxUpper
    dsimp [C]
    linarith
  have hfirst : |(t * A - 1) * f (a / t)| < ε / 2 := by
    rw [abs_mul]
    have hcancel : (ε / (2 * C)) * C = ε / 2 := by field_simp [hC.ne']
    have hstep1 : |t * A - 1| * |f (a / t)| ≤ |t * A - 1| * C :=
      mul_le_mul_of_nonneg_left hfbound.le (abs_nonneg _)
    have hstep2 : |t * A - 1| * C < (ε / (2 * C)) * C :=
      mul_lt_mul_of_pos_right hcoefN hC
    rw [hcancel] at hstep2
    exact hstep1.trans_lt hstep2
  calc
    |t * A * f (a / t) - f (a * q)| =
        |(t * A - 1) * f (a / t) + (f (a / t) - f (a * q))| := by ring_nf
    _ ≤ |(t * A - 1) * f (a / t)| + |f (a / t) - f (a * q)| := abs_add_le _ _
    _ < ε := by linarith

/-- The far/near estimate for the capped term in equation (60). -/
theorem abs_cappedExpectation_le
    {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (p : FinProb α)
    (aMin aMax a h b D B κ : ℝ)
    (haMin : 0 < aMin) (haMM : aMin < aMax) (ha : a ∈ Set.Icc aMin aMax)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hb0 : h ≤ b) (hbD : b ≤ h + D)
    (hRatio : ∀ u : ℝ, aMin * (2 : ℝ) ^ (B - D) ≤ u → |f u / u| ≤ κ) :
    |ProbabilityRepresentation.cappedExpectation f a h b p| ≤
      aMax * κ + (2 : ℝ) ^ D *
        (|f (aMin * (2 : ℝ) ^ (-D))| + |f (aMax * (2 : ℝ) ^ B)|) *
        windowProbability p h (D / 2) (D / 2 + B) := by
  let J : α → ℝ := ProbabilityRepresentation.surprisal p
  let u : α → ℝ := fun x ↦ a * (2 : ℝ) ^ (h - J x)
  let W : α → Prop := fun x ↦ |J x - h - D / 2| ≤ D / 2 + B
  let L := aMin * (2 : ℝ) ^ (-D)
  let U := aMax * (2 : ℝ) ^ B
  let C := |f L| + |f U|
  have ha0 : 0 ≤ a := haMin.le.trans ha.1
  have haPos : 0 < a := haMin.trans_le ha.1
  have hL0 : 0 ≤ L := mul_nonneg haMin.le (Real.rpow_nonneg (by norm_num) _)
  have hU0 : 0 ≤ U := mul_nonneg (haMin.trans haMM).le (Real.rpow_nonneg (by norm_num) _)
  have hC0 : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hK0 : 0 ≤ (2 : ℝ) ^ D * C :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hC0
  calc
    |ProbabilityRepresentation.cappedExpectation f a h b p| =
        |∑ x, if J x ≤ b then
          p x * ((2 : ℝ) ^ (J x - h) * f (u x)) else 0| := by
      congr 1
      simp [ProbabilityRepresentation.cappedExpectation, J, u, Finset.sum_filter]
    _ ≤ ∑ x, |if J x ≤ b then
          p x * ((2 : ℝ) ^ (J x - h) * f (u x)) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, (p x * aMax * κ +
        (2 : ℝ) ^ D * C * (if W x then p x else 0)) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hxb : J x ≤ b
      · rw [if_pos hxb]
        by_cases hfar : J x ≤ b - B
        · have huLower : aMin * (2 : ℝ) ^ (B - D) ≤ u x := by
            have hexp : B - D ≤ h - J x := by linarith
            have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
            have hmul1 := mul_le_mul_of_nonneg_left hpow haMin.le
            have hmul2 : aMin * (2 : ℝ) ^ (h - J x) ≤
                a * (2 : ℝ) ^ (h - J x) :=
              mul_le_mul_of_nonneg_right ha.1 (Real.rpow_nonneg (by norm_num) _)
            simpa [u] using hmul1.trans hmul2
          have huPos : 0 < u x := mul_pos haPos (Real.rpow_pos_of_pos (by norm_num) _)
          have hfuDiv := hRatio (u x) huLower
          have hfu : |f (u x)| ≤ κ * u x := by
            have hh := mul_le_mul_of_nonneg_right hfuDiv huPos.le
            rw [abs_div, abs_of_pos huPos, div_mul_cancel₀ _ huPos.ne'] at hh
            exact hh
          have hpows : (2 : ℝ) ^ (J x - h) * (2 : ℝ) ^ (h - J x) = 1 := by
            rw [← Real.rpow_add (by norm_num)]
            ring_nf
            simp
          have hterm :
              |p x * ((2 : ℝ) ^ (J x - h) * f (u x))| ≤ p x * aMax * κ := by
            rw [abs_mul, abs_mul, abs_of_nonneg (p.nonneg x),
              abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
            calc
              p x * ((2 : ℝ) ^ (J x - h) * |f (u x)|) ≤
                  p x * ((2 : ℝ) ^ (J x - h) * (κ * u x)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hfu (Real.rpow_nonneg (by norm_num) _))
                  (p.nonneg x)
              _ = p x * a * κ := by
                dsimp [u]
                calc
                  p x * ((2 : ℝ) ^ (J x - h) *
                      (κ * (a * (2 : ℝ) ^ (h - J x)))) =
                      p x * a * κ *
                        ((2 : ℝ) ^ (J x - h) * (2 : ℝ) ^ (h - J x)) := by ring
                  _ = p x * a * κ := by rw [hpows, mul_one]
              _ ≤ p x * aMax * κ := by
                have := mul_le_mul_of_nonneg_left ha.2 (p.nonneg x)
                exact mul_le_mul_of_nonneg_right this hκ
          have hWterm : 0 ≤ (2 : ℝ) ^ D * C * (if W x then p x else 0) := by
            apply mul_nonneg hK0
            split_ifs
            · exact p.nonneg x
            · exact le_rfl
          exact hterm.trans (by linarith)
        · have hW : W x := by
            dsimp [W]
            rw [abs_le]
            constructor <;> linarith [lt_of_not_ge hfar]
          rw [if_pos hW]
          have huLower : L ≤ u x := by
            have hexp : -D ≤ h - J x := by linarith
            have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
            have hmul1 := mul_le_mul_of_nonneg_left hpow haMin.le
            have hmul2 : aMin * (2 : ℝ) ^ (h - J x) ≤
                a * (2 : ℝ) ^ (h - J x) :=
              mul_le_mul_of_nonneg_right ha.1 (Real.rpow_nonneg (by norm_num) _)
            simpa [L, u] using hmul1.trans hmul2
          have huUpper : u x ≤ U := by
            have hexp : h - J x ≤ B := by linarith [lt_of_not_ge hfar]
            have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
            have hmul1 := mul_le_mul_of_nonneg_left hpow ha0
            have hmul2 : a * (2 : ℝ) ^ B ≤ aMax * (2 : ℝ) ^ B :=
              mul_le_mul_of_nonneg_right ha.2 (Real.rpow_nonneg (by norm_num) _)
            simpa [U, u] using hmul1.trans hmul2
          have hf := abs_generator_le_endpoints f hL0 huLower huUpper
          have hpowD : (2 : ℝ) ^ (J x - h) ≤ (2 : ℝ) ^ D :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          have hterm :
              |p x * ((2 : ℝ) ^ (J x - h) * f (u x))| ≤
                (2 : ℝ) ^ D * C * p x := by
            rw [abs_mul, abs_mul, abs_of_nonneg (p.nonneg x),
              abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
            have hinner1 : (2 : ℝ) ^ (J x - h) * |f (u x)| ≤
                (2 : ℝ) ^ D * |f (u x)| :=
              mul_le_mul_of_nonneg_right hpowD (abs_nonneg _)
            have hinner2 : (2 : ℝ) ^ D * |f (u x)| ≤ (2 : ℝ) ^ D * C :=
              mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg (by norm_num) _)
            calc
              p x * ((2 : ℝ) ^ (J x - h) * |f (u x)|) ≤
                  p x * ((2 : ℝ) ^ D * C) :=
                mul_le_mul_of_nonneg_left (hinner1.trans hinner2) (p.nonneg x)
              _ = (2 : ℝ) ^ D * C * p x := by ring
          have hfarNonneg : 0 ≤ p x * aMax * κ :=
            mul_nonneg (mul_nonneg (p.nonneg x) (haMin.trans haMM).le) hκ
          exact hterm.trans (by linarith)
      · rw [if_neg hxb, abs_zero]
        have hfarNonneg : 0 ≤ p x * aMax * κ :=
          mul_nonneg (mul_nonneg (p.nonneg x) (haMin.trans haMM).le) hκ
        have hnearNonneg : 0 ≤ (2 : ℝ) ^ D * C * (if W x then p x else 0) := by
          apply mul_nonneg hK0
          split_ifs
          · exact p.nonneg x
          · exact le_rfl
        linarith
    _ = aMax * κ + (2 : ℝ) ^ D * C * windowProbability p h (D / 2) (D / 2 + B) := by
      rw [Finset.sum_add_distrib]
      have hfirst : (∑ x, p x * aMax * κ) = aMax * κ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, p.sum_prob, one_mul]
      rw [hfirst, ← Finset.mul_sum]
      congr 1
      simp [windowProbability, eventProbability, W, J, Finset.sum_filter]
    _ = _ := by rfl

/-- Uniform disappearance of the capped expectation in equation (60). -/
theorem cappedTerm_locallyUniform_zero
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (f : AdmissibleGenerator) (p : ∀ n, FinProb (α n))
    (h b : ℕ → ℝ) (D : ℝ) (hD : 0 < D)
    (hAnti : UniformAntiConcentration α p h)
    (hb : ∀ᶠ n in atTop, h n ≤ b n ∧ b n ≤ h n + D)
    (aMin aMax : ℝ) (haMin : 0 < aMin) (haMM : aMin < aMax) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ a : ℝ, a ∈ Set.Icc aMin aMax →
      |ProbabilityRepresentation.cappedExpectation f a (h n) (b n) (p n)| < ε := by
  intro ε hε
  let κ := ε / (2 * aMax)
  have haMax : 0 < aMax := haMin.trans haMM
  have hκ : 0 < κ := div_pos hε (mul_pos two_pos haMax)
  have hfEvent : ∀ᶠ u : ℝ in atTop, |f u / u| < κ := by
    have hh := f.sublinear_atTop.eventually (Metric.ball_mem_nhds 0 hκ)
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
  obtain ⟨T0, hT0⟩ := (eventually_atTop.1 hfEvent)
  let T := max T0 (aMin + 1)
  have hT0T : T0 ≤ T := le_max_left _ _
  have hTamin : aMin < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hTpos : 0 < T := haMin.trans hTamin
  have hratioPos : 0 < T / aMin := div_pos hTpos haMin
  have hratioOne : 1 < T / aMin := (lt_div_iff₀ haMin).2 (by simpa using hTamin)
  let B := D + Real.logb 2 (T / aMin)
  have hlogPos : 0 < Real.logb 2 (T / aMin) := Real.logb_pos (by norm_num) hratioOne
  have hB : 0 < B := by dsimp [B]; linarith
  have hthreshold : aMin * (2 : ℝ) ^ (B - D) = T := by
    have hpow : (2 : ℝ) ^ (B - D) = T / aMin := by
      have hBD : B - D = Real.logb 2 (T / aMin) := by dsimp [B]; ring
      rw [hBD]
      exact Real.rpow_logb (by norm_num) (by norm_num) hratioPos
    rw [hpow]
    field_simp [haMin.ne']
  let C := |f (aMin * (2 : ℝ) ^ (-D))| + |f (aMax * (2 : ℝ) ^ B)|
  let Kc := (2 : ℝ) ^ D * C
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hKc0 : 0 ≤ Kc := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hC0
  have hsmall : 0 < ε / (2 * (Kc + 1)) := by
    exact div_pos hε (mul_pos two_pos (by linarith))
  have hW : Tendsto
      (fun n ↦ windowProbability (p n) (h n) (D / 2) (D / 2 + B))
      atTop (𝓝 0) := by
    apply fixedWindow_tendsto_zero α p h hAnti
      (K := D) (B := D / 2 + B) (u := D / 2)
    · exact hD
    · linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ D / 2)]
      linarith
  have hWevent : ∀ᶠ n in atTop,
      windowProbability (p n) (h n) (D / 2) (D / 2 + B) <
        ε / (2 * (Kc + 1)) :=
    (tendsto_order.1 hW).2 _ hsmall
  filter_upwards [hb, hWevent] with n hbn hWn
  intro a ha
  have hRatio : ∀ u : ℝ, aMin * (2 : ℝ) ^ (B - D) ≤ u → |f u / u| ≤ κ := by
    intro u hu
    have hTu : T ≤ u := by rwa [← hthreshold]
    exact (hT0 u (hT0T.trans hTu)).le
  have hbound := abs_cappedExpectation_le f (p n) aMin aMax a (h n) (b n)
    D B κ haMin haMM ha hD.le hB.le hκ.le hbn.1 hbn.2 hRatio
  change |ProbabilityRepresentation.cappedExpectation f a (h n) (b n) (p n)| < ε
  have hfar : aMax * κ = ε / 2 := by
    dsimp [κ]
    field_simp [haMax.ne']
  have hnear : Kc * windowProbability (p n) (h n) (D / 2) (D / 2 + B) < ε / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hWn.le hKc0
    have hfrac : Kc * (ε / (2 * (Kc + 1))) < ε / 2 := by
      have hratio : Kc / (Kc + 1) < 1 := by
        rw [div_lt_one (by linarith : 0 < Kc + 1)]
        linarith
      have hmulRatio := mul_lt_mul_of_pos_right hratio (half_pos hε)
      calc
        Kc * (ε / (2 * (Kc + 1))) = (Kc / (Kc + 1)) * (ε / 2) := by
          field_simp [show Kc + 1 ≠ 0 by linarith]
        _ < 1 * (ε / 2) := hmulRatio
        _ = ε / 2 := one_mul _
    exact hmul.trans_lt hfrac
  dsimp [Kc, C] at hbound hnear
  rw [hfar] at hbound
  linarith

/-- The pointwise bounds in equation (65). -/
theorem scaled_bounds {α : Type*} [Fintype α]
    (f : AdmissibleGenerator) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (p : FinProb α) :
    f a ≤ scaledCappedValue f a c p ∧ scaledCappedValue f a c p ≤ f 0 := by
  constructor
  · exact CappedCost.scaledCappedValue_lower f a c ha hc p
  · let qzero : CappedVector α c := CappedVector.zero hc
    calc
      scaledCappedValue f a c p ≤ scaledCappedCost f a p qzero :=
        CappedCost.scaledCappedValue_le_cost f a c ha p qzero
      _ = f 0 := by simp [scaledCappedCost, qzero, CappedVector.zero, perspective]

/-- **Lemma 11 (locally uniform scaled tail limit).**

The tail, anti-concentration, and eventual support assumptions are equations
(61), (62), and the support condition in the paper.  The first conclusion is
equation (63), the second is (64), and the final universally quantified pair
of inequalities is (65). -/
theorem paperLemma11
    (α : ℕ → Type*) [∀ n, Fintype (α n)]
    (f : AdmissibleGenerator) (p : ∀ n, FinProb (α n))
    (hp : ∀ n x, 0 < p n x) (h : ℕ → ℝ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hTail : Tendsto (fun n ↦ tailGE (p n) (h n)) atTop (𝓝 q))
    (hAnti : UniformAntiConcentration α p h)
    (hSupport : ∀ᶠ n in atTop,
      1 < (2 : ℝ) ^ (-h n) * Fintype.card (α n)) :
    LocallyUniformScaledLimit α f p h q ∧
      Tendsto (fun n ↦ cappedValue f ((2 : ℝ) ^ (-h n)) (p n))
        atTop (𝓝 (f q)) ∧
      (∀ (β : Type*) [Fintype β] (a c : ℝ), 0 ≤ a → 0 ≤ c →
        ∀ r : FinProb β,
          f a ≤ scaledCappedValue f a c r ∧ scaledCappedValue f a c r ≤ f 0) := by
  obtain ⟨D, hD, hb⟩ := waterThreshold_eventually_bounded α p hp h q hq0 hq1
    hTail hAnti hSupport
  obtain ⟨ht, _hA, htA, _hC⟩ := waterMultiplier_asymptotics α p hp h q hq0 hq1
    hTail hAnti hSupport
  have hLocal : LocallyUniformScaledLimit α f p h q := by
    intro aMin aMax haMin haMM ε hε
    have hUncapped := uncappedTerm_locallyUniform α f p hp h q aMin aMax hq0
      haMin haMM ht htA (ε / 2) (by linarith)
    have hCapped := cappedTerm_locallyUniform_zero α f p h
      (waterThreshold α p hp h) D hD hAnti hb aMin aMax haMin haMM
      (ε / 2) (by linarith)
    have hRepresentation : ∀ᶠ n in atTop, ∀ a : ℝ, 0 < a →
        scaledCappedValue f a ((2 : ℝ) ^ (-h n)) (p n) =
          waterMultiplier α p hp h n *
              ProbabilityRepresentation.upperTail (p n)
                (waterThreshold α p hp h n) *
              f (a / waterMultiplier α p hp h n) +
            ProbabilityRepresentation.cappedExpectation f a (h n)
              (waterThreshold α p hp h n) (p n) := by
      filter_upwards [hSupport] with n hs
      intro a ha
      have hsweak : 1 ≤ (2 : ℝ) ^ (-h n) * Fintype.card (α n) := hs.le
      have hspec := waterMultiplier_spec α p hp h n hsweak
      let t := waterMultiplier α p hp h n
      have hrepr := ((ProbabilityRepresentation.paperLemma10 (h n) t hspec.1
        (p n) (hp n) hs hspec.2).2 f).2 a ha.le
      simpa [waterThreshold, t] using hrepr
    filter_upwards [hUncapped, hCapped, hRepresentation] with n hU hC hR
    intro a ha
    have haPos : 0 < a := haMin.trans_le ha.1
    rw [hR a haPos]
    let U := waterMultiplier α p hp h n *
      ProbabilityRepresentation.upperTail (p n) (waterThreshold α p hp h n) *
        f (a / waterMultiplier α p hp h n)
    let C := ProbabilityRepresentation.cappedExpectation f a (h n)
      (waterThreshold α p hp h n) (p n)
    have hU' : |U - f (a * q)| < ε / 2 := hU a ha
    have hC' : |C| < ε / 2 := hC a ha
    calc
      |U + C - f (a * q)| = |(U - f (a * q)) + C| := by ring_nf
      _ ≤ |U - f (a * q)| + |C| := abs_add_le _ _
      _ < ε := by linarith
  have hUnscaled : Tendsto
      (fun n ↦ cappedValue f ((2 : ℝ) ^ (-h n)) (p n)) atTop (𝓝 (f q)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hev := hLocal (1 / 2) 2 (by norm_num) (by norm_num) ε hε
    have hevOne : ∀ᶠ n in atTop,
        |cappedValue f ((2 : ℝ) ^ (-h n)) (p n) - f q| < ε := by
      filter_upwards [hev] with n hn
      simpa [cappedValue] using hn 1 (by norm_num : (1 : ℝ) ∈ Set.Icc (1 / 2) 2)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevOne
    refine ⟨N, fun n hn ↦ ?_⟩
    simpa [Real.dist_eq] using hN n hn
  exact ⟨hLocal, hUnscaled, fun β _ a c ha hc r ↦ scaled_bounds f a c ha hc r⟩

end TailLimit

end RandomnessExtraction
