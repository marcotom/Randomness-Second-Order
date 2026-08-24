import RandomnessExtraction.OneShot
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Light-part achievability

This file formalizes Lemma 8.  The proof keeps the second-moment, `L¹`, and
uniform-continuity steps separate so each estimate can be audited.
-/

open Set
open scoped BigOperators Classical

namespace RandomnessExtraction

namespace LightAchievability

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y] {M : ℕ}

/-- The light part in equation (49). -/
noncomputable def lightPart (p : FinProb X) (M : ℕ) (τ : ℝ) (x : X) : ℝ :=
  if p x ≤ (2 : ℝ) ^ (-τ) / (M : ℝ) then p x else 0

/-- The light mass `Q_τ`. -/
noncomputable def lightMass (p : FinProb X) (M : ℕ) (τ : ℝ) : ℝ :=
  ∑ x, lightPart p M τ x

theorem lightPart_nonneg (p : FinProb X) (M : ℕ) (τ : ℝ) (x : X) :
    0 ≤ lightPart p M τ x := by
  by_cases hx : p x ≤ (2 : ℝ) ^ (-τ) / (M : ℝ)
  · simp [lightPart, hx, p.nonneg x]
  · simp [lightPart, hx]

theorem lightPart_le (p : FinProb X) (M : ℕ) (τ : ℝ) (x : X) :
    lightPart p M τ x ≤ p x := by
  by_cases hx : p x ≤ (2 : ℝ) ^ (-τ) / (M : ℝ) <;>
    simp [lightPart, hx, p.nonneg x]

theorem lightMass_mem_unit (p : FinProb X) (M : ℕ) (τ : ℝ) :
    lightMass p M τ ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun x _ ↦ lightPart_nonneg p M τ x
  · calc
      lightMass p M τ ≤ ∑ x, p x :=
        Finset.sum_le_sum fun x _ ↦ lightPart_le p M τ x
      _ = 1 := p.sum_prob

/-- Modulus of continuity of `f` on `[0,1]`, equation (51). -/
noncomputable def modulus (f : AdmissibleGenerator) (η : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
    |a - b| ≤ η ∧ r = |f a - f b|}

private theorem modulus_set_bdd (f : AdmissibleGenerator) (η : ℝ) :
    BddAbove {r : ℝ | ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ b ∈ Set.Icc (0 : ℝ) 1,
      |a - b| ≤ η ∧ r = |f a - f b|} := by
  refine ⟨f 0, ?_⟩
  rintro r ⟨a, ha, b, hb, _hab, rfl⟩
  have hfa0 : 0 ≤ f a := f.nonneg_of_mem_unit ha.1 ha.2
  have hfb0 : 0 ≤ f b := f.nonneg_of_mem_unit hb.1 hb.2
  have hfa : f a ≤ f 0 := f.antitoneOn_nonneg
    (show (0 : ℝ) ∈ Set.Ici 0 by simp) ha.1 ha.1
  have hfb : f b ≤ f 0 := f.antitoneOn_nonneg
    (show (0 : ℝ) ∈ Set.Ici 0 by simp) hb.1 hb.1
  rw [abs_le]
  constructor <;> linarith

theorem abs_sub_le_modulus (f : AdmissibleGenerator) {η a b : ℝ}
    (hη : 0 ≤ η) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : |a - b| ≤ η) :
    |f a - f b| ≤ modulus f η := by
  apply le_csSup (modulus_set_bdd f η)
  exact ⟨a, ha, b, hb, hab, rfl⟩

theorem modulus_nonneg (f : AdmissibleGenerator) {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ modulus f η := by
  have hmem : (0 : ℝ) ∈ {r : ℝ | ∃ a ∈ Set.Icc (0 : ℝ) 1,
      ∃ b ∈ Set.Icc (0 : ℝ) 1, |a - b| ≤ η ∧ r = |f a - f b|} := by
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, 0, ⟨le_rfl, zero_le_one⟩,
      by simpa using hη, by simp⟩
  exact le_csSup (modulus_set_bdd f η) hmem

/-- The finite Markov/modulus estimate used twice in Lemma 8. -/
theorem weighted_stability {Ω : Type*} [Fintype Ω]
    (f : AdmissibleGenerator) (w u : Ω → ℝ) (v ε η : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hu : ∀ i, 0 ≤ u i) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hη : 0 < η) (hL1 : ∑ i, w i * |u i - v| ≤ ε) :
    ∑ i, w i * f (u i) ≤
      f v + modulus f η + f 0 * ε / η := by
  have hpoint (i : Ω) :
      f (u i) ≤ f v + modulus f η + (f 0 / η) * |u i - v| := by
    rcases le_total v (u i) with hvu | huv
    · have hfu : f (u i) ≤ f v :=
        f.antitoneOn_nonneg hv0 (hu i) hvu
      have homega := modulus_nonneg f hη.le
      have hlast : 0 ≤ (f 0 / η) * |u i - v| :=
        mul_nonneg (div_nonneg f.map_zero_nonneg hη.le) (abs_nonneg _)
      linarith
    · have hui1 : u i ≤ 1 := huv.trans hv1
      by_cases hclose : |u i - v| ≤ η
      · have hmod := abs_sub_le_modulus f hη.le ⟨hu i, hui1⟩
          ⟨hv0, hv1⟩ hclose
        have hdiff : f (u i) - f v ≤ modulus f η :=
          (le_abs_self _).trans hmod
        have hlast : 0 ≤ (f 0 / η) * |u i - v| :=
          mul_nonneg (div_nonneg f.map_zero_nonneg hη.le) (abs_nonneg _)
        linarith
      · have hfar : η < |u i - v| := lt_of_not_ge hclose
        have hfu : f (u i) ≤ f 0 :=
          f.antitoneOn_nonneg (show (0 : ℝ) ∈ Set.Ici 0 by simp) (hu i) (hu i)
        have hmarkov : f 0 ≤ (f 0 / η) * |u i - v| := by
          have hratio : 1 ≤ |u i - v| / η := (le_div_iff₀ hη).2 (by
            simpa using hfar.le)
          calc
            f 0 = f 0 * 1 := by ring
            _ ≤ f 0 * (|u i - v| / η) :=
              mul_le_mul_of_nonneg_left hratio f.map_zero_nonneg
            _ = (f 0 / η) * |u i - v| := by ring
        have homega := modulus_nonneg f hη.le
        have hfv0 : 0 ≤ f v := f.nonneg_of_mem_unit hv0 hv1
        linarith
  calc
    (∑ i, w i * f (u i)) ≤
        ∑ i, w i * (f v + modulus f η + (f 0 / η) * |u i - v|) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hpoint i) (hw i)
    _ = f v + modulus f η + (f 0 / η) * ∑ i, w i * |u i - v| := by
      calc
        (∑ i, w i * (f v + modulus f η + (f 0 / η) * |u i - v|)) =
            ∑ i, (w i * f v + w i * modulus f η +
              (f 0 / η) * (w i * |u i - v|)) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [← Finset.sum_mul, ← Finset.sum_mul, hwsum]
          rw [← Finset.mul_sum]
          ring
    _ ≤ f v + modulus f η + f 0 * ε / η := by
      have hcoef : 0 ≤ f 0 / η := div_nonneg f.map_zero_nonneg hη.le
      have := mul_le_mul_of_nonneg_left hL1 hcoef
      calc
        f v + modulus f η + (f 0 / η) * ∑ i, w i * |u i - v| ≤
            f v + modulus f η + (f 0 / η) * ε := by linarith
        _ = f v + modulus f η + f 0 * ε / η := by ring

/-- Output mass produced by hashing the light part. -/
noncomputable def lightBinMass (H : SeededHash X S M) (p : FinProb X)
    (τ : ℝ) (s : S) (z : Fin M) : ℝ := H.binMass (lightPart p M τ) s z

theorem lightBinMass_le_outputMass (H : SeededHash X S M) (p : FinProb X)
    (τ : ℝ) (s : S) (z : Fin M) :
    lightBinMass H p τ s z ≤ OneShot.outputMass H p s z := by
  apply Finset.sum_le_sum
  intro x hx
  exact lightPart_le p M τ x

/-- Squared output deviation of the hashed light part. -/
noncomputable def squareDeviation (H : SeededHash X S M) (p : FinProb X)
    (τ : ℝ) (s : S) : ℝ :=
  ∑ z, (lightBinMass H p τ s z - lightMass p M τ / (M : ℝ)) ^ 2

/-- `L¹` output deviation of the hashed light part. -/
noncomputable def l1Deviation (H : SeededHash X S M) (p : FinProb X)
    (τ : ℝ) (s : S) : ℝ :=
  ∑ z, |lightBinMass H p τ s z - lightMass p M τ / (M : ℝ)|

private theorem sum_sq_lightPart_le (p : FinProb X) (M : ℕ) (hM : 0 < M)
    (τ : ℝ) :
    ∑ x, (lightPart p M τ x) ^ 2 ≤
      ((2 : ℝ) ^ (-τ) / (M : ℝ)) * lightMass p M τ := by
  rw [lightMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p x ≤ (2 : ℝ) ^ (-τ) / (M : ℝ)
  · rw [lightPart, if_pos hx]
    simpa [pow_two, mul_comm] using
      (mul_le_mul_of_nonneg_right hx (p.nonneg x))
  · simp [lightPart, hx]

private theorem l1Deviation_sq_le (H : SeededHash X S M) (p : FinProb X)
    (τ : ℝ) (s : S) :
    (l1Deviation H p τ s) ^ 2 ≤ (M : ℝ) * squareDeviation H p τ s := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin M)))
    (f := fun z ↦ |lightBinMass H p τ s z - lightMass p M τ / (M : ℝ)|)
  simpa [l1Deviation, squareDeviation, sq_abs] using h

/-- Equations (52)--(53): two-universality turns the light cap into a
uniform `L¹` estimate. -/
theorem expected_l1Deviation_le (H : SeededHash X S M) (p : FinProb X)
    (hM : 0 < M) (h2 : SeededHash.paperDefinition6 H) (τ : ℝ) :
    H.seed.expect (l1Deviation H p τ) ≤ (2 : ℝ) ^ (-τ / 2) := by
  let Q := lightMass p M τ
  let e := (2 : ℝ) ^ (-τ / 2)
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hQ := lightMass_mem_unit p M τ
  have hell : ∀ x, 0 ≤ lightPart p M τ x := lightPart_nonneg p M τ
  have hsecond := SeededHash.paperLemma7 H (lightPart p M τ) hell hM h2
  change H.seed.expect (squareDeviation H p τ) ≤
      (1 - (M : ℝ)⁻¹) * ∑ x, (lightPart p M τ x) ^ 2 at hsecond
  have hinvle : (M : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hMr]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hM.ne')
  have hfactor : 0 ≤ 1 - (M : ℝ)⁻¹ := sub_nonneg.mpr hinvle
  have hsqLight := sum_sq_lightPart_le p M hM τ
  have hsquare : H.seed.expect (squareDeviation H p τ) ≤
      ((2 : ℝ) ^ (-τ) / (M : ℝ)) * Q := by
    calc
      H.seed.expect (squareDeviation H p τ) ≤
          (1 - (M : ℝ)⁻¹) * ∑ x, (lightPart p M τ x) ^ 2 := hsecond
      _ ≤ 1 * ∑ x, (lightPart p M τ x) ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (by linarith [inv_nonneg.mpr hMr.le])
            (Finset.sum_nonneg fun x _ ↦ sq_nonneg _)
      _ ≤ ((2 : ℝ) ^ (-τ) / (M : ℝ)) * Q := by simpa [Q] using hsqLight
  have hl1nonneg : ∀ s, 0 ≤ l1Deviation H p τ s := fun s ↦
    Finset.sum_nonneg fun z _ ↦ abs_nonneg _
  have hweightedCS :
      (H.seed.expect (l1Deviation H p τ)) ^ 2 ≤
        H.seed.expect (fun s ↦ (l1Deviation H p τ s) ^ 2) := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := (Finset.univ : Finset S))
      (r := fun s ↦ H.seed s * l1Deviation H p τ s)
      (f := fun s ↦ H.seed s)
      (g := fun s ↦ H.seed s * (l1Deviation H p τ s) ^ 2)
      (fun s _ ↦ H.seed.nonneg s)
      (fun s _ ↦ mul_nonneg (H.seed.nonneg s) (sq_nonneg _))
      (fun s _ ↦ by ring_nf; exact le_rfl)
    simpa [FinProb.expect, H.seed.sum_prob] using hcs
  have hl1sq : H.seed.expect (fun s ↦ (l1Deviation H p τ s) ^ 2) ≤
      (M : ℝ) * H.seed.expect (squareDeviation H p τ) := by
    calc
      H.seed.expect (fun s ↦ (l1Deviation H p τ s) ^ 2) ≤
          H.seed.expect (fun s ↦ (M : ℝ) * squareDeviation H p τ s) :=
        H.seed.expect_mono fun s ↦ l1Deviation_sq_le H p τ s
      _ = (M : ℝ) * H.seed.expect (squareDeviation H p τ) := by
        simp [FinProb.expect, ← Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  have htotalSq : (H.seed.expect (l1Deviation H p τ)) ^ 2 ≤ (2 : ℝ) ^ (-τ) := by
    calc
      (H.seed.expect (l1Deviation H p τ)) ^ 2 ≤
          H.seed.expect (fun s ↦ (l1Deviation H p τ s) ^ 2) := hweightedCS
      _ ≤ (M : ℝ) * H.seed.expect (squareDeviation H p τ) := hl1sq
      _ ≤ (M : ℝ) * (((2 : ℝ) ^ (-τ) / (M : ℝ)) * Q) := by
        exact mul_le_mul_of_nonneg_left hsquare hMr.le
      _ = (2 : ℝ) ^ (-τ) * Q := by field_simp [hMr.ne']
      _ ≤ (2 : ℝ) ^ (-τ) := by
        exact mul_le_of_le_one_right (Real.rpow_nonneg (by norm_num) _) hQ.2
  have hepos : 0 ≤ e := Real.rpow_nonneg (by norm_num) _
  have heSq : e ^ 2 = (2 : ℝ) ^ (-τ) := by
    dsimp [e]
    rw [pow_two, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hexpectnonneg : 0 ≤ H.seed.expect (l1Deviation H p τ) :=
    H.seed.expect_nonneg hl1nonneg
  rw [← heSq] at htotalSq
  nlinarith

private theorem rpow_error_ratio (τ : ℝ) :
    (2 : ℝ) ^ (-τ / 2) / (2 : ℝ) ^ (-τ / 4) = (2 : ℝ) ^ (-τ / 4) := by
  rw [← Real.rpow_sub (by norm_num)]
  congr 1
  ring

private theorem fixed_fiber_light_bound (f : AdmissibleGenerator)
    (H : SeededHash X S M) (p : FinProb X) (hM : 0 < M)
    (h2 : SeededHash.paperDefinition6 H) (τ : ℝ) (hτ : 0 < τ) :
    H.seed.expect (fun s ↦ ∑ z : Fin M, (M : ℝ)⁻¹ *
        f ((M : ℝ) * OneShot.outputMass H p s z)) ≤
      f (lightMass p M τ) + modulus f ((2 : ℝ) ^ (-τ / 4)) +
        f 0 * (2 : ℝ) ^ (-τ / 4) := by
  let η : ℝ := (2 : ℝ) ^ (-τ / 4)
  let ε : ℝ := (2 : ℝ) ^ (-τ / 2)
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hη : 0 < η := Real.rpow_pos_of_pos (by norm_num) _
  have hεL1 := expected_l1Deviation_le H p hM h2 τ
  have hactual : H.seed.expect (fun s ↦ ∑ z : Fin M, (M : ℝ)⁻¹ *
      f ((M : ℝ) * OneShot.outputMass H p s z)) ≤
      H.seed.expect (fun s ↦ ∑ z : Fin M, (M : ℝ)⁻¹ *
        f ((M : ℝ) * lightBinMass H p τ s z)) := by
    apply H.seed.expect_mono
    intro s
    apply Finset.sum_le_sum
    intro z _
    gcongr
    apply f.antitoneOn_nonneg
    · exact mul_nonneg hMr.le (Finset.sum_nonneg fun x _ ↦ lightPart_nonneg p M τ x)
    · exact mul_nonneg hMr.le (Finset.sum_nonneg fun x _ ↦ p.nonneg x)
    · exact mul_le_mul_of_nonneg_left (lightBinMass_le_outputMass H p τ s z) hMr.le
  let w : S × Fin M → ℝ := fun sz ↦ H.seed sz.1 * (M : ℝ)⁻¹
  let u : S × Fin M → ℝ := fun sz ↦
    (M : ℝ) * lightBinMass H p τ sz.1 sz.2
  have hwsum : ∑ sz, w sz = 1 := by
    rw [Fintype.sum_prod_type]
    dsimp [w]
    calc
      (∑ s, ∑ _z : Fin M, H.seed s * (M : ℝ)⁻¹) =
          ∑ s, H.seed s * 1 := by
            apply Finset.sum_congr rfl
            intro s _
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            field_simp [hMr.ne']
      _ = 1 := by simp [H.seed.sum_prob]
  have hw : ∀ sz, 0 ≤ w sz := fun sz ↦
    mul_nonneg (H.seed.nonneg sz.1) (inv_nonneg.mpr hMr.le)
  have hu : ∀ sz, 0 ≤ u sz := fun sz ↦
    mul_nonneg hMr.le (Finset.sum_nonneg fun x _ ↦ lightPart_nonneg p M τ x)
  have hL1 : ∑ sz, w sz * |u sz - lightMass p M τ| ≤ ε := by
    have heq : (∑ sz, w sz * |u sz - lightMass p M τ|) =
        H.seed.expect (l1Deviation H p τ) := by
      rw [Fintype.sum_prod_type]
      rw [FinProb.expect]
      dsimp [w, u]
      apply Finset.sum_congr rfl
      intro s _
      rw [l1Deviation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      have halg : (M : ℝ) * lightBinMass H p τ s z - lightMass p M τ =
          (M : ℝ) *
            (lightBinMass H p τ s z - lightMass p M τ / (M : ℝ)) := by
        field_simp [hMr.ne']
      rw [halg, abs_mul, abs_of_pos hMr]
      field_simp [hMr.ne']
    rw [heq]
    simpa [ε] using hεL1
  have hstable := weighted_stability f w u (lightMass p M τ) ε η hw hwsum hu
    (lightMass_mem_unit p M τ).1 (lightMass_mem_unit p M τ).2 hη hL1
  have hlight : H.seed.expect (fun s ↦ ∑ z : Fin M, (M : ℝ)⁻¹ *
      f ((M : ℝ) * lightBinMass H p τ s z)) ≤
      f (lightMass p M τ) + modulus f η + f 0 * ε / η := by
    convert hstable using 1
    rw [Fintype.sum_prod_type, FinProb.expect]
    dsimp [w, u]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  calc
    H.seed.expect (fun s ↦ ∑ z : Fin M, (M : ℝ)⁻¹ *
        f ((M : ℝ) * OneShot.outputMass H p s z)) ≤
      H.seed.expect (fun s ↦ ∑ z : Fin M, (M : ℝ)⁻¹ *
        f ((M : ℝ) * lightBinMass H p τ s z)) := hactual
    _ ≤ f (lightMass p M τ) + modulus f η + f 0 * ε / η := hlight
    _ = f (lightMass p M τ) + modulus f ((2 : ℝ) ^ (-τ / 4)) +
        f 0 * (2 : ℝ) ^ (-τ / 4) := by
      dsimp [ε, η]
      have herr : f 0 * (2 : ℝ) ^ (-τ / 2) / (2 : ℝ) ^ (-τ / 4) =
          f 0 * (2 : ℝ) ^ (-τ / 4) := by
        calc
          f 0 * (2 : ℝ) ^ (-τ / 2) / (2 : ℝ) ^ (-τ / 4) =
              f 0 * ((2 : ℝ) ^ (-τ / 2) / (2 : ℝ) ^ (-τ / 4)) := by ring
          _ = _ := by rw [rpow_error_ratio]
      rw [herr]

/-- The fixed-reference inequality in Lemma 8. -/
theorem fixed_light_achievability (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M)
    (h2 : SeededHash.paperDefinition6 H) (τ : ℝ) (hτ : 0 < τ) :
    OneShot.fixedLeakage f P H ≤
      P.marginal.expect (fun y ↦ f (lightMass (P.conditional y) M τ)) +
        modulus f ((2 : ℝ) ^ (-τ / 4)) + f 0 * (2 : ℝ) ^ (-τ / 4) := by
  rw [OneShot.fixedLeakage]
  rw [FinProb.expect]
  calc
    (∑ s, H.seed s * P.marginal.expect (fun y ↦
        ∑ z : Fin M, (M : ℝ)⁻¹ *
          f ((M : ℝ) * OneShot.outputMass H (P.conditional y) s z))) =
      P.marginal.expect (fun y ↦ H.seed.expect (fun s ↦
        ∑ z : Fin M, (M : ℝ)⁻¹ *
          f ((M : ℝ) * OneShot.outputMass H (P.conditional y) s z))) := by
        simp only [FinProb.expect]
        calc
          (∑ s, H.seed s * ∑ y, P.marginal y *
              ∑ z : Fin M, (M : ℝ)⁻¹ *
                f ((M : ℝ) * OneShot.outputMass H (P.conditional y) s z)) =
            ∑ s, ∑ y, H.seed s * (P.marginal y *
              ∑ z : Fin M, (M : ℝ)⁻¹ *
                f ((M : ℝ) * OneShot.outputMass H (P.conditional y) s z)) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  rw [Finset.mul_sum]
          _ = ∑ y, ∑ s, H.seed s * (P.marginal y *
              ∑ z : Fin M, (M : ℝ)⁻¹ *
                f ((M : ℝ) * OneShot.outputMass H (P.conditional y) s z)) := by
                  rw [Finset.sum_comm]
          _ = ∑ y, P.marginal y * ∑ s, H.seed s *
              ∑ z : Fin M, (M : ℝ)⁻¹ *
                f ((M : ℝ) * OneShot.outputMass H (P.conditional y) s z) := by
                  apply Finset.sum_congr rfl
                  intro y _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro s _
                  ring
    _ ≤ P.marginal.expect (fun y ↦
        f (lightMass (P.conditional y) M τ) +
          modulus f ((2 : ℝ) ^ (-τ / 4)) + f 0 * (2 : ℝ) ^ (-τ / 4)) := by
        apply P.marginal.expect_mono
        intro y
        exact fixed_fiber_light_bound f H (P.conditional y) hM h2 τ hτ
    _ = _ := by
      simp only [FinProb.expect]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, ← Finset.sum_mul, P.marginal.sum_prob]
      ring

/-- Average conditional light mass. -/
noncomputable def averageLightMass (P : FiniteSource X Y) (M : ℕ) (τ : ℝ) : ℝ :=
  P.marginal.expect fun y ↦ lightMass (P.conditional y) M τ

theorem averageLightMass_mem_unit (P : FiniteSource X Y) (M : ℕ) (τ : ℝ) :
    averageLightMass P M τ ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact P.marginal.expect_nonneg fun y ↦ (lightMass_mem_unit (P.conditional y) M τ).1
  · calc
      averageLightMass P M τ ≤ P.marginal.expect (fun _ ↦ (1 : ℝ)) :=
        P.marginal.expect_mono fun y ↦ (lightMass_mem_unit (P.conditional y) M τ).2
      _ = 1 := P.marginal.expect_const 1

/-- The tilted reference in equation (54). -/
noncomputable def tiltedReference (P : FiniteSource X Y) (H : SeededHash X S M)
    (τ : ℝ) (hbar : 0 < averageLightMass P M τ) : FinProb (Y × S) where
  prob ys := P.marginal ys.1 * H.seed ys.2 *
    lightMass (P.conditional ys.1) M τ / averageLightMass P M τ
  nonneg ys := div_nonneg
    (mul_nonneg (mul_nonneg (P.marginal.nonneg ys.1) (H.seed.nonneg ys.2))
      (lightMass_mem_unit (P.conditional ys.1) M τ).1) hbar.le
  sum_prob := by
    rw [Fintype.sum_prod_type]
    have hinner (y : Y) :
        (∑ s, P.marginal y * H.seed s * lightMass (P.conditional y) M τ /
            averageLightMass P M τ) =
          (P.marginal y * lightMass (P.conditional y) M τ) /
            averageLightMass P M τ := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      congr 1
      calc
        (∑ s, P.marginal y * H.seed s * lightMass (P.conditional y) M τ) =
            P.marginal y * lightMass (P.conditional y) M τ * ∑ s, H.seed s := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              ring
        _ = P.marginal y * lightMass (P.conditional y) M τ := by
          rw [H.seed.sum_prob, mul_one]
    simp_rw [hinner]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    change averageLightMass P M τ * (averageLightMass P M τ)⁻¹ = 1
    exact mul_inv_cancel₀ hbar.ne'

@[simp]
theorem tiltedReference_apply (P : FiniteSource X Y) (H : SeededHash X S M)
    (τ : ℝ) (hbar : 0 < averageLightMass P M τ) (y : Y) (s : S) :
    tiltedReference P H τ hbar (y, s) =
      P.marginal y * H.seed s * lightMass (P.conditional y) M τ /
        averageLightMass P M τ := rfl

private theorem zero_lightMass_bin (H : SeededHash X S M) (p : FinProb X)
    (τ : ℝ) {s : S} (hQ : lightMass p M τ = 0) (z : Fin M) :
    lightBinMass H p τ s z = 0 := by
  apply le_antisymm
  · calc
      lightBinMass H p τ s z ≤ ∑ x, lightPart p M τ x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x _ _ ↦ lightPart_nonneg p M τ x)
      _ = 0 := hQ
  · exact Finset.sum_nonneg fun x _ ↦ lightPart_nonneg p M τ x

/-- The optimized-reference inequality in Lemma 8. -/
theorem optimized_light_achievability (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M)
    (h2 : SeededHash.paperDefinition6 H) (τ : ℝ) (hτ : 0 < τ)
    (hbar : 0 < averageLightMass P M τ) :
    OneShot.referenceLeakage f P H (tiltedReference P H τ hbar) ≤
      f (averageLightMass P M τ) + modulus f ((2 : ℝ) ^ (-τ / 4)) +
        f 0 * (2 : ℝ) ^ (-τ / 4) := by
  let qbar := averageLightMass P M τ
  let η : ℝ := (2 : ℝ) ^ (-τ / 4)
  let ε : ℝ := (2 : ℝ) ^ (-τ / 2)
  let R := tiltedReference P H τ hbar
  let w : (Y × S) × Fin M → ℝ := fun o ↦ (M : ℝ)⁻¹ * R o.1
  let u : (Y × S) × Fin M → ℝ := fun o ↦
    let Qy := lightMass (P.conditional o.1.1) M τ
    if Qy = 0 then 0 else
      qbar * (M : ℝ) * lightBinMass H (P.conditional o.1.1) τ o.1.2 o.2 / Qy
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hη : 0 < η := Real.rpow_pos_of_pos (by norm_num) _
  have hqbarUnit := averageLightMass_mem_unit P M τ
  have hw : ∀ o, 0 ≤ w o := fun o ↦
    mul_nonneg (inv_nonneg.mpr hMr.le) (R.nonneg o.1)
  have hwsum : ∑ o, w o = 1 := by
    rw [Fintype.sum_prod_type]
    dsimp [w]
    calc
      (∑ ys, ∑ _z : Fin M, (M : ℝ)⁻¹ * R ys) = ∑ ys, R ys := by
        apply Finset.sum_congr rfl
        intro ys _
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp [hMr.ne']
      _ = 1 := R.sum_prob
  have hu : ∀ o, 0 ≤ u o := by
    intro o
    dsimp [u]
    split_ifs with hQ
    · exact le_rfl
    · exact div_nonneg
        (mul_nonneg (mul_nonneg hbar.le hMr.le)
          (Finset.sum_nonneg fun x _ ↦ lightPart_nonneg (P.conditional o.1.1) M τ x))
        (lightMass_mem_unit (P.conditional o.1.1) M τ).1
  have hL1 : ∑ o, w o * |u o - qbar| ≤ ε := by
    have hperY (y : Y) :
        (∑ s, ∑ z : Fin M, w ((y, s), z) * |u ((y, s), z) - qbar|) =
          P.marginal y * H.seed.expect (l1Deviation H (P.conditional y) τ) := by
      let Qy := lightMass (P.conditional y) M τ
      by_cases hQ : Qy = 0
      · have hRzero : ∀ s, R (y, s) = 0 := by
          intro s
          simp [R, tiltedReference, Qy, hQ]
        have hdevzero : ∀ s, l1Deviation H (P.conditional y) τ s = 0 := by
          intro s
          apply Finset.sum_eq_zero
          intro z _
          have hQ' : lightMass (P.conditional y) M τ = 0 := hQ
          rw [zero_lightMass_bin H (P.conditional y) τ hQ z, hQ']
          simp
        simp [w, u, Qy, hQ, hRzero, hdevzero, FinProb.expect]
      · have hQpos : 0 < Qy := lt_of_le_of_ne
          (lightMass_mem_unit (P.conditional y) M τ).1 (Ne.symm hQ)
        rw [FinProb.expect]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [l1Deviation, Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        dsimp [w, u]
        rw [if_neg hQ]
        change (M : ℝ)⁻¹ *
            (P.marginal y * H.seed s * Qy / qbar) *
              |qbar * (M : ℝ) * lightBinMass H (P.conditional y) τ s z / Qy - qbar| =
          P.marginal y * (H.seed s *
            |lightBinMass H (P.conditional y) τ s z - Qy / (M : ℝ)|)
        have hdiff : qbar * (M : ℝ) * lightBinMass H (P.conditional y) τ s z / Qy - qbar =
            (qbar * (M : ℝ) / Qy) *
              (lightBinMass H (P.conditional y) τ s z - Qy / (M : ℝ)) := by
          field_simp [hMr.ne', hQpos.ne']
        rw [hdiff, abs_mul, abs_of_pos (div_pos (mul_pos hbar hMr) hQpos)]
        field_simp [hMr.ne', hQpos.ne', hbar.ne', qbar]
        simp only [qbar]
    calc
      (∑ o, w o * |u o - qbar|) =
          ∑ y, P.marginal y * H.seed.expect (l1Deviation H (P.conditional y) τ) := by
            rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro y _
            exact hperY y
      _ ≤ ∑ y, P.marginal y * ε := by
            apply Finset.sum_le_sum
            intro y _
            exact mul_le_mul_of_nonneg_left
              (by simpa [ε] using expected_l1Deviation_le H (P.conditional y) hM h2 τ)
              (P.marginal.nonneg y)
      _ = ε := by rw [← Finset.sum_mul, P.marginal.sum_prob, one_mul]
  have hlight : OneShot.referenceLeakage f P H R ≤ ∑ o, w o * f (u o) := by
    rw [OneShot.referenceLeakage]
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro y _
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro z _
    let Qy := lightMass (P.conditional y) M τ
    by_cases hQ : Qy = 0
    · have hRzero : R (y, s) = 0 := by simp [R, tiltedReference, Qy, hQ]
      simp [w, u, Qy, hQ, hRzero, perspective]
    · have hQpos : 0 < Qy := lt_of_le_of_ne
        (lightMass_mem_unit (P.conditional y) M τ).1 (Ne.symm hQ)
      have hRformula : R (y, s) = P.marginal y * H.seed s * Qy / qbar := rfl
      by_cases hR0 : R (y, s) = 0
      · simp [w, u, Qy, hQ, hR0, perspective]
      · have hrefpos : 0 < (M : ℝ)⁻¹ * R (y, s) :=
          mul_pos (inv_pos.mpr hMr) (lt_of_le_of_ne (R.nonneg _) (Ne.symm hR0))
        have hpys : P.marginal y * H.seed s ≠ 0 := by
          intro hpys0
          apply hR0
          rw [hRformula, hpys0, zero_mul, zero_div]
        have hpy0 : P.marginal y ≠ 0 := (mul_ne_zero_iff.mp hpys).1
        have hps0 : H.seed s ≠ 0 := (mul_ne_zero_iff.mp hpys).2
        rw [perspective_of_pos f hrefpos]
        have hlightle := lightBinMass_le_outputMass H (P.conditional y) τ s z
        have hratio :
            (P.marginal y * H.seed s * lightBinMass H (P.conditional y) τ s z) /
                ((M : ℝ)⁻¹ * R (y, s)) =
              qbar * (M : ℝ) * lightBinMass H (P.conditional y) τ s z / Qy := by
          rw [hRformula]
          field_simp [hMr.ne', hQpos.ne', hbar.ne', hR0, hpy0, hps0]
        have hactualRatioNonneg : 0 ≤
            (P.marginal y * H.seed s * OneShot.outputMass H (P.conditional y) s z) /
              ((M : ℝ)⁻¹ * R (y, s)) := by
          exact div_nonneg
            (mul_nonneg (mul_nonneg (P.marginal.nonneg y) (H.seed.nonneg s))
              (Finset.sum_nonneg fun x _ ↦ (P.conditional y).nonneg x))
            hrefpos.le
        have hlightRatioNonneg : 0 ≤
            (P.marginal y * H.seed s * lightBinMass H (P.conditional y) τ s z) /
              ((M : ℝ)⁻¹ * R (y, s)) := by
          exact div_nonneg
            (mul_nonneg (mul_nonneg (P.marginal.nonneg y) (H.seed.nonneg s))
              (Finset.sum_nonneg fun x _ ↦ lightPart_nonneg (P.conditional y) M τ x))
            hrefpos.le
        have hratiole :
            (P.marginal y * H.seed s * lightBinMass H (P.conditional y) τ s z) /
                ((M : ℝ)⁻¹ * R (y, s)) ≤
              (P.marginal y * H.seed s * OneShot.outputMass H (P.conditional y) s z) /
                ((M : ℝ)⁻¹ * R (y, s)) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlightle
              (mul_nonneg (P.marginal.nonneg y) (H.seed.nonneg s))) hrefpos.le
        have hfmono := f.antitoneOn_nonneg hlightRatioNonneg hactualRatioNonneg hratiole
        change ((M : ℝ)⁻¹ * R (y, s)) * f _ ≤ w ((y, s), z) * f (u ((y, s), z))
        rw [show u ((y, s), z) =
          qbar * (M : ℝ) * lightBinMass H (P.conditional y) τ s z / Qy by
            simp [u, Qy, hQ]]
        rw [← hratio]
        exact mul_le_mul_of_nonneg_left hfmono hrefpos.le
  have hstable := weighted_stability f w u qbar ε η hw hwsum hu
    hqbarUnit.1 hqbarUnit.2 hη hL1
  calc
    OneShot.referenceLeakage f P H R ≤ ∑ o, w o * f (u o) := hlight
    _ ≤ f qbar + modulus f η + f 0 * ε / η := hstable
    _ = f (averageLightMass P M τ) + modulus f ((2 : ℝ) ^ (-τ / 4)) +
        f 0 * (2 : ℝ) ^ (-τ / 4) := by
      dsimp [qbar, ε, η]
      have herr : f 0 * (2 : ℝ) ^ (-τ / 2) / (2 : ℝ) ^ (-τ / 4) =
          f 0 * (2 : ℝ) ^ (-τ / 4) := by
        calc
          f 0 * (2 : ℝ) ^ (-τ / 2) / (2 : ℝ) ^ (-τ / 4) =
              f 0 * ((2 : ℝ) ^ (-τ / 2) / (2 : ℝ) ^ (-τ / 4)) := by ring
          _ = _ := by rw [rpow_error_ratio]
      rw [herr]

/-- **Lemma 8 (light-part achievability), fixed and optimized references.** -/
theorem paperLemma8 (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M)
    (h2 : SeededHash.paperDefinition6 H) (τ : ℝ) (hτ : 0 < τ) :
    OneShot.fixedLeakage f P H ≤
        P.marginal.expect (fun y ↦ f (lightMass (P.conditional y) M τ)) +
          modulus f ((2 : ℝ) ^ (-τ / 4)) + f 0 * (2 : ℝ) ^ (-τ / 4) ∧
      ∀ hbar : 0 < averageLightMass P M τ,
        OneShot.referenceLeakage f P H (tiltedReference P H τ hbar) ≤
          f (averageLightMass P M τ) + modulus f ((2 : ℝ) ^ (-τ / 4)) +
            f 0 * (2 : ℝ) ^ (-τ / 4) := by
  exact ⟨fixed_light_achievability f P H hM h2 τ hτ,
    fun hbar ↦ optimized_light_achievability f P H hM h2 τ hτ hbar⟩

end LightAchievability

end RandomnessExtraction
