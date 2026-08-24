import RandomnessExtraction.Capped
import RandomnessExtraction.Hashing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# One-shot converse

This file formalizes the bin construction in Lemma 5, including empty bins.
-/

open scoped BigOperators Classical

namespace RandomnessExtraction

namespace OneShot

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y] {M : ℕ}

/-- The output-bin probability of `p` under a fixed hash seed. -/
noncomputable def outputMass (H : SeededHash X S M) (p : FinProb X)
    (s : S) (z : Fin M) : ℝ := H.binMass p s z

/-- The joint law of the hash output and the public view `(Y,S)`.  Introducing
this law explicitly lets specializations be stated using their native
divergences rather than by definitional abbreviation through `f`-leakage. -/
noncomputable def hashedLaw (P : FiniteSource X Y) (H : SeededHash X S M) :
    FinProb (Fin M × (Y × S)) where
  prob o := P.marginal o.2.1 * H.seed o.2.2 *
    outputMass H (P.conditional o.2.1) o.2.2 o.1
  nonneg o := mul_nonneg
    (mul_nonneg (P.marginal.nonneg _) (H.seed.nonneg _))
    (Finset.sum_nonneg fun _ _ ↦ (P.conditional _).nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [show (∑ ys : Y × S, ∑ z : Fin M,
        P.marginal ys.1 * H.seed ys.2 *
          outputMass H (P.conditional ys.1) ys.2 z) =
        ∑ ys : Y × S, P.marginal ys.1 * H.seed ys.2 by
      apply Finset.sum_congr rfl
      intro ys _
      rw [← Finset.mul_sum]
      have hout : ∑ z : Fin M, outputMass H (P.conditional ys.1) ys.2 z = 1 := by
        exact (H.sum_binMass (P.conditional ys.1) ys.2).trans
          (P.conditional ys.1).sum_prob
      rw [hout, mul_one]]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, H.seed.sum_prob, mul_one]
    exact P.marginal.sum_prob

/-- The law `U_Z × R_{YS}` on the same alphabet as `hashedLaw`. -/
noncomputable def uniformViewLaw (M : ℕ) (hM : 0 < M)
    (R : FinProb (Y × S)) : FinProb (Fin M × (Y × S)) where
  prob o := (M : ℝ)⁻¹ * R o.2
  nonneg o := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg M)) (R.nonneg _)
  sum_prob := by
    have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [Fintype.sum_prod_type]
    have hinner (z : Fin M) :
        ∑ ys : Y × S, (M : ℝ)⁻¹ * R ys = (M : ℝ)⁻¹ := by
      rw [← Finset.mul_sum, R.sum_prob, mul_one]
    calc
      (∑ z : Fin M, ∑ ys : Y × S, (M : ℝ)⁻¹ * R ys) =
          ∑ _z : Fin M, (M : ℝ)⁻¹ := by
            apply Finset.sum_congr rfl
            intro z _
            exact hinner z
      _ = 1 := by simp [hMr]

@[simp]
theorem hashedLaw_apply (P : FiniteSource X Y) (H : SeededHash X S M)
    (z : Fin M) (y : Y) (s : S) :
    hashedLaw P H (z, (y, s)) = P.marginal y * H.seed s *
      outputMass H (P.conditional y) s z := rfl

@[simp]
theorem uniformViewLaw_apply (hM : 0 < M) (R : FinProb (Y × S))
    (z : Fin M) (y : Y) (s : S) :
    uniformViewLaw M hM R (z, (y, s)) = (M : ℝ)⁻¹ * R (y, s) := rfl

/-- The capped input vector induced by the occupied output bins. -/
noncomputable def vectorFromBins (H : SeededHash X S M) (p : FinProb X)
    (hM : 0 < M) (s : S) : CappedVector X (M : ℝ)⁻¹ where
  mass x := if outputMass H p s (H.hash s x) = 0 then 0
    else p x / ((M : ℝ) * outputMass H p s (H.hash s x))
  nonneg x := by
    split_ifs with hr
    · exact le_rfl
    · have hrnonneg : 0 ≤ outputMass H p s (H.hash s x) :=
        Finset.sum_nonneg fun u _ ↦ p.nonneg u
      exact div_nonneg (p.nonneg x) (mul_nonneg (by positivity) hrnonneg)
  le_cap x := by
    by_cases hr : outputMass H p s (H.hash s x) = 0
    · simp [hr]
    · rw [if_neg hr]
      have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
      have hrpos : 0 < outputMass H p s (H.hash s x) :=
        lt_of_le_of_ne (Finset.sum_nonneg fun u _ ↦ p.nonneg u) (Ne.symm hr)
      have hpr : p x ≤ outputMass H p s (H.hash s x) := by
        exact Finset.single_le_sum (fun u _ ↦ p.nonneg u)
          (Finset.mem_filter.2 ⟨Finset.mem_univ x, rfl⟩)
      rw [div_le_iff₀ (mul_pos hMr hrpos)]
      simpa [mul_assoc, mul_left_comm, mul_comm, hMr.ne'] using hpr
  sum_le_one := by
    have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
    have hfiber : (∑ x, if outputMass H p s (H.hash s x) = 0 then 0
          else p x / ((M : ℝ) * outputMass H p s (H.hash s x))) =
        ∑ z, ∑ x with H.hash s x = z,
          if outputMass H p s (H.hash s x) = 0 then 0
          else p x / ((M : ℝ) * outputMass H p s (H.hash s x)) := by
      symm
      simpa using (Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ
        (H.hash s) _)
    rw [hfiber]
    calc
      (∑ z, ∑ x with H.hash s x = z,
          if outputMass H p s (H.hash s x) = 0 then 0
          else p x / ((M : ℝ) * outputMass H p s (H.hash s x))) ≤
          ∑ _z : Fin M, (M : ℝ)⁻¹ := by
            apply Finset.sum_le_sum
            intro z _
            by_cases hr : outputMass H p s z = 0
            · have hzero : ∑ x with H.hash s x = z,
                    (if outputMass H p s (H.hash s x) = 0 then 0
                    else p x / ((M : ℝ) * outputMass H p s (H.hash s x))) = 0 := by
                  apply Finset.sum_eq_zero
                  intro x hx
                  rw [(Finset.mem_filter.1 hx).2, if_pos hr]
              rw [hzero]
              exact inv_nonneg.mpr hMr.le
            · have hrpos : 0 < outputMass H p s z :=
                lt_of_le_of_ne (Finset.sum_nonneg fun u _ ↦ p.nonneg u) (Ne.symm hr)
              calc
                (∑ x with H.hash s x = z,
                    if outputMass H p s (H.hash s x) = 0 then 0
                    else p x / ((M : ℝ) * outputMass H p s (H.hash s x))) =
                    ∑ x with H.hash s x = z,
                      p x / ((M : ℝ) * outputMass H p s z) := by
                        apply Finset.sum_congr rfl
                        intro x hx
                        rw [(Finset.mem_filter.1 hx).2, if_neg hr]
                _ = (∑ x with H.hash s x = z, p x) /
                    ((M : ℝ) * outputMass H p s z) := by
                      simp_rw [div_eq_mul_inv]
                      rw [← Finset.sum_mul]
                _ = (M : ℝ)⁻¹ := by
                      change outputMass H p s z /
                        ((M : ℝ) * outputMass H p s z) = (M : ℝ)⁻¹
                      field_simp [hMr.ne', hrpos.ne']
                _ ≤ (M : ℝ)⁻¹ := le_rfl
      _ = 1 := by
        simp [hMr.ne']

@[simp]
theorem vectorFromBins_apply (H : SeededHash X S M) (p : FinProb X)
    (hM : 0 < M) (s : S) (x : X) :
    vectorFromBins H p hM s x =
      if outputMass H p s (H.hash s x) = 0 then 0
      else p x / ((M : ℝ) * outputMass H p s (H.hash s x)) := rfl

/-- Exact bin identity, including the dummy mass corresponding to empty
output bins.  This is equation (44), in its scaled form. -/
theorem scaled_bin_identity (f : AdmissibleGenerator) (a : ℝ)
    (H : SeededHash X S M) (p : FinProb X) (hM : 0 < M) (s : S) :
    scaledCappedCost f a p (vectorFromBins H p hM s) =
      ∑ z : Fin M, (M : ℝ)⁻¹ * f (a * (M : ℝ) * outputMass H p s z) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  let q := vectorFromBins H p hM s
  have hfiber : (∑ x, perspective f (a * p x) (q x)) =
      ∑ z, ∑ x with H.hash s x = z,
        perspective f (a * p x) (q x) := by
    symm
    simpa using (Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ
      (H.hash s) _)
  have hoccupied (z : Fin M) (hr : outputMass H p s z ≠ 0) :
      (∑ x with H.hash s x = z, perspective f (a * p x) (q x)) =
        (M : ℝ)⁻¹ * f (a * (M : ℝ) * outputMass H p s z) := by
    have hrpos : 0 < outputMass H p s z :=
      lt_of_le_of_ne (Finset.sum_nonneg fun u _ ↦ p.nonneg u) (Ne.symm hr)
    calc
      (∑ x with H.hash s x = z, perspective f (a * p x) (q x)) =
          ∑ x with H.hash s x = z,
            (p x / ((M : ℝ) * outputMass H p s z)) *
              f (a * (M : ℝ) * outputMass H p s z) := by
                apply Finset.sum_congr rfl
                intro x hx
                have hxhash := (Finset.mem_filter.1 hx).2
                by_cases hpx : p x = 0
                · simp [q, vectorFromBins, hxhash, hpx, perspective]
                · have hqpos : 0 < p x / ((M : ℝ) * outputMass H p s z) :=
                    div_pos (lt_of_le_of_ne (p.nonneg x) (Ne.symm hpx))
                      (mul_pos hMr hrpos)
                  rw [show q x = p x / ((M : ℝ) * outputMass H p s z) by
                    simp [q, vectorFromBins, hxhash, hr]]
                  rw [perspective_of_pos f hqpos]
                  change (p x / ((M : ℝ) * outputMass H p s z)) *
                      f ((a * p x) /
                        (p x / ((M : ℝ) * outputMass H p s z))) = _
                  have hratio : (a * p x) /
                      (p x / ((M : ℝ) * outputMass H p s z)) =
                        a * (M : ℝ) * outputMass H p s z := by
                    field_simp [hpx, hMr.ne', hrpos.ne']
                  rw [hratio]
      _ = ((∑ x with H.hash s x = z, p x) /
            ((M : ℝ) * outputMass H p s z)) *
          f (a * (M : ℝ) * outputMass H p s z) := by
            simp_rw [div_eq_mul_inv, mul_assoc]
            rw [← Finset.sum_mul]
      _ = (M : ℝ)⁻¹ * f (a * (M : ℝ) * outputMass H p s z) := by
            change (outputMass H p s z /
                ((M : ℝ) * outputMass H p s z)) * _ = _
            field_simp [hMr.ne', hrpos.ne']
  have hempty (z : Fin M) (hr : outputMass H p s z = 0) :
      ∑ x with H.hash s x = z, perspective f (a * p x) (q x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxhash := (Finset.mem_filter.1 hx).2
    have hpx : p x = 0 := by
      have hle : p x ≤ outputMass H p s z := by
        exact Finset.single_le_sum (fun u _ ↦ p.nonneg u) hx
      exact le_antisymm (by simpa [hr] using hle) (p.nonneg x)
    simp [q, vectorFromBins, hxhash, hr, hpx, perspective]
  rw [scaledCappedCost, hfiber]
  let E : Finset (Fin M) := Finset.univ.filter fun z ↦ outputMass H p s z = 0
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun z ↦ outputMass H p s z = 0)
    (fun z ↦ ∑ x with H.hash s x = z, perspective f (a * p x) (q x))]
  have hsumq : ∑ x, q x =
      ∑ z, if outputMass H p s z = 0 then 0 else (M : ℝ)⁻¹ := by
    rw [show (∑ x, q x) = ∑ z, ∑ x with H.hash s x = z, q x by
      symm
      simpa using (Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ
        (H.hash s) _)]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hr : outputMass H p s z = 0
    · rw [if_pos hr]
      apply Finset.sum_eq_zero
      intro x hx
      simp [q, vectorFromBins, (Finset.mem_filter.1 hx).2, hr]
    · rw [if_neg hr]
      have hrpos : 0 < outputMass H p s z :=
        lt_of_le_of_ne (Finset.sum_nonneg fun u _ ↦ p.nonneg u) (Ne.symm hr)
      calc
        (∑ x with H.hash s x = z, q x) =
            (∑ x with H.hash s x = z, p x) /
              ((M : ℝ) * outputMass H p s z) := by
                calc
                  (∑ x with H.hash s x = z, q x) =
                      ∑ x with H.hash s x = z,
                        p x / ((M : ℝ) * outputMass H p s z) := by
                          apply Finset.sum_congr rfl
                          intro x hx
                          simp [q, vectorFromBins, (Finset.mem_filter.1 hx).2, hr]
                  _ = _ := by
                    simp_rw [div_eq_mul_inv]
                    rw [← Finset.sum_mul]
        _ = (M : ℝ)⁻¹ := by
          change outputMass H p s z /
            ((M : ℝ) * outputMass H p s z) = (M : ℝ)⁻¹
          field_simp [hMr.ne', hrpos.ne']
  rw [hsumq]
  -- Empty bins contribute through the unused-mass term.
  have hunused : 1 - ∑ z, (if outputMass H p s z = 0 then 0 else (M : ℝ)⁻¹) =
      ∑ z ∈ E, (M : ℝ)⁻¹ := by
    have hall : ∑ _z : Fin M, (M : ℝ)⁻¹ = 1 := by simp [hMr.ne']
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun z ↦ outputMass H p s z = 0) (fun _z ↦ (M : ℝ)⁻¹)
    have hif : (∑ z, if outputMass H p s z = 0 then 0 else (M : ℝ)⁻¹) =
        ∑ z ∈ Finset.univ.filter (fun z ↦ ¬ outputMass H p s z = 0),
          (M : ℝ)⁻¹ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : outputMass H p s z = 0 <;> simp [hz]
    rw [← hall, hif, ← hsplit]
    simp [E]
  rw [hunused]
  have hemptysum : (∑ z ∈ E,
      ∑ x with H.hash s x = z, perspective f (a * p x) (q x)) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    exact hempty z (Finset.mem_filter.1 hz).2
  rw [hemptysum, zero_add]
  have hoccupiedSum : (∑ z ∈ Finset.univ.filter
      (fun z ↦ ¬ outputMass H p s z = 0),
      ∑ x with H.hash s x = z, perspective f (a * p x) (q x)) =
      ∑ z ∈ Finset.univ.filter (fun z ↦ ¬ outputMass H p s z = 0),
        (M : ℝ)⁻¹ * f (a * (M : ℝ) * outputMass H p s z) := by
    apply Finset.sum_congr rfl
    intro z hz
    exact hoccupied z (Finset.mem_filter.1 hz).2
  rw [hoccupiedSum]
  let rhs : Fin M → ℝ := fun z ↦
    (M : ℝ)⁻¹ * f (a * (M : ℝ) * outputMass H p s z)
  have hemptyRhs : (∑ z ∈ E, (M : ℝ)⁻¹ * f 0) = ∑ z ∈ E, rhs z := by
    apply Finset.sum_congr rfl
    intro z hz
    simp [rhs, (Finset.mem_filter.1 hz).2]
  have hsplitRhs := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun z ↦ outputMass H p s z = 0) rhs
  calc
    (∑ z ∈ Finset.univ.filter (fun z ↦ ¬ outputMass H p s z = 0),
        (M : ℝ)⁻¹ * f (a * (M : ℝ) * outputMass H p s z)) +
        (∑ z ∈ E, (M : ℝ)⁻¹) * f 0 =
      (∑ z ∈ Finset.univ.filter (fun z ↦ ¬ outputMass H p s z = 0), rhs z) +
        ∑ z ∈ E, (M : ℝ)⁻¹ * f 0 := by
          rw [Finset.sum_mul]
    _ = (∑ z ∈ Finset.univ.filter (fun z ↦ ¬ outputMass H p s z = 0), rhs z) +
        ∑ z ∈ E, rhs z := by rw [hemptyRhs]
    _ = (∑ z ∈ E, rhs z) +
        ∑ z ∈ Finset.univ.filter (fun z ↦ ¬ outputMass H p s z = 0), rhs z := by
          rw [add_comm]
    _ = ∑ z, rhs z := by
          simpa [E] using hsplitRhs

/-- The fixed-reference leakage of a seeded family.  This is the finite-sum
form of `D_f(P_{\varphi_S(X)YS} ‖ U_Z × P_Y × P_S)`. -/
noncomputable def fixedLeakage (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) : ℝ :=
  H.seed.expect fun s ↦ P.marginal.expect fun y ↦
    ∑ z : Fin M, (M : ℝ)⁻¹ *
      f ((M : ℝ) * outputMass H (P.conditional y) s z)

/-- The fixed-reference capped converse quantity `Γ_{f,P}` at cap `1/M`. -/
noncomputable def fixedGamma (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (M : ℕ) : ℝ :=
  P.marginal.expect fun y ↦ cappedValue f (M : ℝ)⁻¹ (P.conditional y)

/-- Optimal fixed-reference leakage, with an arbitrary finite seed encoded as
`Fin N`. -/
noncomputable def optimalFixedLeakage (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (M : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M,
    v = fixedLeakage f P H}

theorem fixed_family_converse (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    fixedGamma f P M ≤ fixedLeakage f P H := by
  rw [fixedGamma, fixedLeakage]
  rw [← H.seed.expect_const
    (P.marginal.expect fun y ↦ cappedValue f (M : ℝ)⁻¹ (P.conditional y))]
  apply H.seed.expect_mono
  intro s
  apply P.marginal.expect_mono
  intro y
  have hcost := CappedCost.scaledCappedValue_le_cost f 1 (M : ℝ)⁻¹
    zero_le_one (P.conditional y) (vectorFromBins H (P.conditional y) hM s)
  rw [scaled_bin_identity f 1 H (P.conditional y) hM s] at hcost
  simpa [cappedValue] using hcost

theorem optimal_fixed_converse (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) :
    fixedGamma f P M ≤ optimalFixedLeakage f P M := by
  rw [optimalFixedLeakage]
  apply le_csInf
  · let H₀ : SeededHash X (Fin 1) M :=
      { seed := FinProb.uniformFin 1 (by omega)
        hash := fun _ _ ↦ ⟨0, hM⟩ }
    exact ⟨fixedLeakage f P H₀, 1, H₀, rfl⟩
  · rintro v ⟨N, H, rfl⟩
    exact fixed_family_converse f P H hM

/-- Weighted average of capped vectors. -/
noncomputable def averagedVector {ι α : Type*} [Fintype ι] [Fintype α]
    {c : ℝ} (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) (hRsum : 0 < ∑ i, R i)
    (q : ι → CappedVector α c) : CappedVector α c where
  mass x := ∑ i, (R i / ∑ j, R j) * q i x
  nonneg x := Finset.sum_nonneg fun i _ ↦
    mul_nonneg (div_nonneg (hR i) hRsum.le) ((q i).nonneg x)
  le_cap x := by
    calc
      (∑ i, (R i / ∑ j, R j) * q i x) ≤
          ∑ i, (R i / ∑ j, R j) * c := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left ((q i).le_cap x)
              (div_nonneg (hR i) hRsum.le)
      _ = c := by
        rw [← Finset.sum_mul]
        have : ∑ i, R i / ∑ j, R j = 1 := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
          simp [hRsum.ne']
        rw [this, one_mul]
  sum_le_one := by
    calc
      (∑ x, ∑ i, (R i / ∑ j, R j) * q i x) =
          ∑ i, (R i / ∑ j, R j) * ∑ x, q i x := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ ≤ ∑ i, (R i / ∑ j, R j) * 1 := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left (q i).sum_le_one
              (div_nonneg (hR i) hRsum.le)
      _ = 1 := by
            simp_rw [mul_one, div_eq_mul_inv]
            rw [← Finset.sum_mul]
            simp [hRsum.ne']

@[simp]
theorem averagedVector_apply {ι α : Type*} [Fintype ι] [Fintype α]
    {c : ℝ} (R : ι → ℝ) (hR : ∀ i, 0 ≤ R i) (hRsum : 0 < ∑ i, R i)
    (q : ι → CappedVector α c) (x : α) :
    averagedVector R hR hRsum q x =
      ∑ i, (R i / ∑ j, R j) * q i x := rfl

/-- Joint convexity after aggregating scaled capped costs. -/
theorem aggregate_scaled_cost {ι α : Type*} [Fintype ι] [Fintype α]
    (f : AdmissibleGenerator) (p : FinProb α) {c : ℝ}
    (R a : ι → ℝ) (hR : ∀ i, 0 ≤ R i) (ha : ∀ i, 0 ≤ a i)
    (hRsum : 0 < ∑ i, R i) (q : ι → CappedVector α c) :
    (∑ i, R i) * scaledCappedCost f
        ((∑ i, R i * a i) / ∑ i, R i) p
        (averagedVector R hR hRsum q) ≤
      ∑ i, R i * scaledCappedCost f (a i) p (q i) := by
  let Q : ℝ := ∑ i, R i
  let A : ℝ := ∑ i, R i * a i
  let qbar := averagedVector R hR hRsum q
  have hQ : 0 < Q := hRsum
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ ↦ mul_nonneg (hR i) (ha i)
  have hqmass (x : α) : Q * qbar x = ∑ i, R i * q i x := by
    dsimp [Q, qbar, averagedVector]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hRsum.ne']
  have hcoord (x : α) :
      Q * perspective f ((A / Q) * p x) (qbar x) ≤
        ∑ i, R i * perspective f (a i * p x) (q i x) := by
    calc
      Q * perspective f ((A / Q) * p x) (qbar x) =
          perspective f (A * p x) (∑ i, R i * q i x) := by
            have hPscale : Q * ((A / Q) * p x) = A * p x := by
              field_simp [hQ.ne']
            rw [← perspective_smul f hQ.le, hPscale, hqmass]
      _ ≤ ∑ i, perspective f ((R i * a i) * p x) (R i * q i x) := by
            have hs := perspective_sum_le f
              (fun i ↦ (R i * a i) * p x) (fun i ↦ R i * q i x)
              (fun i ↦ mul_nonneg (mul_nonneg (hR i) (ha i)) (p.nonneg x))
              (fun i ↦ mul_nonneg (hR i) ((q i).nonneg x))
            have hPsum : ∑ i, (R i * a i) * p x = A * p x := by
              rw [← Finset.sum_mul]
            rw [hPsum] at hs
            exact hs
      _ = ∑ i, R i * perspective f (a i * p x) (q i x) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [show (R i * a i) * p x = R i * (a i * p x) by ring]
            rw [perspective_smul f (hR i)]
  have hperspective :
      Q * (∑ x, perspective f ((A / Q) * p x) (qbar x)) ≤
        ∑ i, R i * ∑ x, perspective f (a i * p x) (q i x) := by
    rw [Finset.mul_sum]
    calc
      (∑ x, Q * perspective f ((A / Q) * p x) (qbar x)) ≤
          ∑ x, ∑ i, R i * perspective f (a i * p x) (q i x) :=
            Finset.sum_le_sum fun x _ ↦ hcoord x
      _ = ∑ i, R i * ∑ x, perspective f (a i * p x) (q i x) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
  have hqsum : Q * (∑ x, qbar x) = ∑ i, R i * ∑ x, q i x := by
    rw [Finset.mul_sum]
    calc
      (∑ x, Q * qbar x) = ∑ x, ∑ i, R i * q i x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hqmass]
      _ = ∑ i, R i * ∑ x, q i x := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
  have hdummy : Q * (1 - ∑ x, qbar x) * f 0 =
      ∑ i, R i * ((1 - ∑ x, q i x) * f 0) := by
    have hbase : Q * (1 - ∑ x, qbar x) =
        ∑ i, R i * (1 - ∑ x, q i x) := by
      calc
        Q * (1 - ∑ x, qbar x) = Q - Q * ∑ x, qbar x := by ring
        _ = (∑ i, R i) - ∑ i, R i * ∑ x, q i x := by rw [hqsum]
        _ = ∑ i, R i * (1 - ∑ x, q i x) := by
          simp_rw [mul_sub, mul_one]
          rw [Finset.sum_sub_distrib]
    calc
      Q * (1 - ∑ x, qbar x) * f 0 =
          (∑ i, R i * (1 - ∑ x, q i x)) * f 0 := by rw [hbase]
      _ = ∑ i, R i * ((1 - ∑ x, q i x) * f 0) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
  change Q * scaledCappedCost f (A / Q) p qbar ≤
    ∑ i, R i * scaledCappedCost f (a i) p (q i)
  simp only [scaledCappedCost]
  rw [mul_add]
  calc
    Q * (∑ x, perspective f ((A / Q) * p x) (qbar x)) +
        Q * ((1 - ∑ x, qbar x) * f 0) ≤
      (∑ i, R i * ∑ x, perspective f (a i * p x) (q i x)) +
        ∑ i, R i * ((1 - ∑ x, q i x) * f 0) := by
          exact add_le_add hperspective (by simpa [mul_assoc] using hdummy.le)
    _ = ∑ i, R i *
        ((∑ x, perspective f (a i * p x) (q i x)) +
          (1 - ∑ x, q i x) * f 0) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- The first marginal of a finite joint law. -/
noncomputable def firstMarginal (R : FinProb (Y × S)) : FinProb Y where
  prob y := ∑ s, R (y, s)
  nonneg y := Finset.sum_nonneg fun s _ ↦ R.nonneg (y, s)
  sum_prob := by
    rw [← Fintype.sum_prod_type]
    exact R.sum_prob

@[simp]
theorem firstMarginal_apply (R : FinProb (Y × S)) (y : Y) :
    firstMarginal R y = ∑ s, R (y, s) := rfl

/-- Leakage to a specified optimized reference on `(Y,S)`.  Written with
perspectives, this includes the paper's reference-zero convention. -/
noncomputable def referenceLeakage (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (R : FinProb (Y × S)) : ℝ :=
  ∑ y, ∑ s, ∑ z : Fin M,
    perspective f
      (P.marginal y * H.seed s * outputMass H (P.conditional y) s z)
      ((M : ℝ)⁻¹ * R (y, s))

/-- The perspective sum called `referenceLeakage` is literally the finite
`f`-divergence between the distribution induced by the hash and
`U_Z × R_{YS}`. -/
theorem referenceLeakage_eq_fDivergence (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M)
    (R : FinProb (Y × S)) :
    referenceLeakage f P H R =
      fDivergence f (hashedLaw P H) (uniformViewLaw M hM R) := by
  unfold referenceLeakage fDivergence
  simp only [Fintype.sum_prod_type]
  change (∑ y, ∑ s, ∑ z, perspective f
      (P.marginal y * H.seed s * outputMass H (P.conditional y) s z)
      ((M : ℝ)⁻¹ * R (y, s))) =
    ∑ z, ∑ y, ∑ s, perspective f
      (P.marginal y * H.seed s * outputMass H (P.conditional y) s z)
      ((M : ℝ)⁻¹ * R (y, s))
  calc
    (∑ y, ∑ s, ∑ z, perspective f
        (P.marginal y * H.seed s * outputMass H (P.conditional y) s z)
        ((M : ℝ)⁻¹ * R (y, s))) =
        ∑ y, ∑ z, ∑ s, perspective f
          (P.marginal y * H.seed s * outputMass H (P.conditional y) s z)
          ((M : ℝ)⁻¹ * R (y, s)) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.sum_comm]
    _ = ∑ z, ∑ y, ∑ s, perspective f
          (P.marginal y * H.seed s * outputMass H (P.conditional y) s z)
          ((M : ℝ)⁻¹ * R (y, s)) := by rw [Finset.sum_comm]

/-- The fixed-reference leakage is the native `f`-divergence to
`U_Z × P_Y × P_S`. -/
theorem fixedLeakage_eq_fDivergence (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    fixedLeakage f P H = fDivergence f (hashedLaw P H)
      (uniformViewLaw M hM (P.marginal.prod H.seed)) := by
  rw [← referenceLeakage_eq_fDivergence]
  unfold fixedLeakage referenceLeakage FinProb.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro z _
  by_cases hpy : P.marginal y = 0
  · simp [hpy, perspective]
  by_cases hps : H.seed s = 0
  · simp [hps, perspective]
  have hpypos : 0 < P.marginal y :=
    lt_of_le_of_ne (P.marginal.nonneg y) (Ne.symm hpy)
  have hpspos : 0 < H.seed s := lt_of_le_of_ne (H.seed.nonneg s) (Ne.symm hps)
  simp only [FinProb.prod_apply]
  rw [perspective_of_pos f (mul_pos (inv_pos.mpr (by exact_mod_cast hM))
    (mul_pos hpypos hpspos))]
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hratio :
      (P.marginal y * H.seed s * outputMass H (P.conditional y) s z) /
          ((M : ℝ)⁻¹ * (P.marginal y * H.seed s)) =
        (M : ℝ) * outputMass H (P.conditional y) s z := by
    field_simp [hMr, hpy, hps]
  rw [hratio]
  field_simp [hMr]

/-- Optimized-reference leakage of a fixed seeded family. -/
noncomputable def optimizedLeakage (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) : ℝ :=
  sInf {v : ℝ | ∃ R : FinProb (Y × S), v = referenceLeakage f P H R}

/-- A single `Y`-coordinate of `Γ↓`. -/
noncomputable def gammaTerm (f : AdmissibleGenerator) (c : ℝ)
    (p : FinProb X) (py qy : ℝ) : ℝ :=
  if qy = 0 then 0 else qy * scaledCappedValue f (py / qy) c p

/-- The optimized-reference capped converse quantity `Γ↓_{f,P}`. -/
noncomputable def optimizedGammaObjective (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (M : ℕ) (Q : FinProb Y) : ℝ :=
  ∑ y, gammaTerm f (M : ℝ)⁻¹ (P.conditional y) (P.marginal y) (Q y)

noncomputable def optimizedGamma (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (M : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ Q : FinProb Y, v = optimizedGammaObjective f P M Q}

noncomputable def optimalOptimizedLeakage (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (M : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M,
    v = optimizedLeakage f P H}

theorem gammaTerm_ge_perspective (f : AdmissibleGenerator) (c : ℝ)
    (hc : 0 ≤ c) (p : FinProb X) (py qy : ℝ) (hpy : 0 ≤ py) (hqy : 0 ≤ qy) :
    perspective f py qy ≤ gammaTerm f c p py qy := by
  by_cases hq0 : qy = 0
  · simp [gammaTerm, hq0, perspective]
  · have hqpos : 0 < qy := lt_of_le_of_ne hqy (Ne.symm hq0)
    rw [gammaTerm, if_neg hq0, perspective_of_pos f hqpos]
    gcongr
    exact CappedCost.scaledCappedValue_lower f (py / qy) c
      (div_nonneg hpy hqpos.le) hc p

theorem optimizedGammaObjective_nonneg (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) (Q : FinProb Y) :
    0 ≤ optimizedGammaObjective f P M Q := by
  have hc : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
  calc
    0 ≤ fDivergence f P.marginal Q := fDivergence_nonneg f P.marginal Q
    _ = ∑ y, perspective f (P.marginal y) (Q y) := rfl
    _ ≤ ∑ y, gammaTerm f (M : ℝ)⁻¹ (P.conditional y)
        (P.marginal y) (Q y) := Finset.sum_le_sum fun y _ ↦
          gammaTerm_ge_perspective f (M : ℝ)⁻¹ hc (P.conditional y)
            (P.marginal y) (Q y) (P.marginal.nonneg y) (Q.nonneg y)
    _ = optimizedGammaObjective f P M Q := rfl

theorem optimizedGamma_le_objective (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) (Q : FinProb Y) :
    optimizedGamma f P M ≤ optimizedGammaObjective f P M Q := by
  rw [optimizedGamma]
  apply csInf_le
  · exact ⟨0, by
      rintro v ⟨Q', rfl⟩
      exact optimizedGammaObjective_nonneg f P M hM Q'⟩
  · exact ⟨Q, rfl⟩

private theorem optimized_fiber_converse (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M)
    (R : FinProb (Y × S)) (y : Y) :
    gammaTerm f (M : ℝ)⁻¹ (P.conditional y) (P.marginal y)
        (firstMarginal R y) ≤
      ∑ s, ∑ z : Fin M,
        perspective f
          (P.marginal y * H.seed s * outputMass H (P.conditional y) s z)
          ((M : ℝ)⁻¹ * R (y, s)) := by
  let Ry : S → ℝ := fun s ↦ R (y, s)
  let Qy : ℝ := ∑ s, Ry s
  have hRy : ∀ s, 0 ≤ Ry s := fun s ↦ R.nonneg (y, s)
  change gammaTerm f (M : ℝ)⁻¹ (P.conditional y) (P.marginal y) Qy ≤ _
  by_cases hQ0 : Qy = 0
  · have hRzero : ∀ s, Ry s = 0 := by
      intro s
      have hs := Finset.single_le_sum (fun i _ ↦ hRy i) (Finset.mem_univ s)
      have hsumzero : ∑ i, Ry i = 0 := hQ0
      rw [hsumzero] at hs
      exact le_antisymm hs (hRy s)
    rw [gammaTerm, if_pos hQ0]
    have hright : (∑ s, ∑ z : Fin M,
        perspective f
          (P.marginal y * H.seed s * outputMass H (P.conditional y) s z)
          ((M : ℝ)⁻¹ * R (y, s))) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      apply Finset.sum_eq_zero
      intro z _
      have hrs : R (y, s) = 0 := by simpa [Ry] using hRzero s
      simp [hrs, perspective]
    rw [hright]
  · have hQpos : 0 < Qy :=
      lt_of_le_of_ne (Finset.sum_nonneg fun s _ ↦ hRy s) (Ne.symm hQ0)
    let scale : S → ℝ := fun s ↦
      if Ry s = 0 then 0 else P.marginal y * H.seed s / Ry s
    let q : S → CappedVector X (M : ℝ)⁻¹ := fun s ↦
      vectorFromBins H (P.conditional y) hM s
    have hscale : ∀ s, 0 ≤ scale s := by
      intro s
      by_cases hrs : Ry s = 0
      · simp [scale, hrs]
      · simpa [scale, hrs] using
          (div_nonneg (mul_nonneg (P.marginal.nonneg y) (H.seed.nonneg s))
            (hRy s))
    have href : (∑ s, Ry s *
        scaledCappedCost f (scale s) (P.conditional y) (q s)) =
        ∑ s, ∑ z : Fin M,
          perspective f
            (P.marginal y * H.seed s * outputMass H (P.conditional y) s z)
            ((M : ℝ)⁻¹ * R (y, s)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [scaled_bin_identity f (scale s) H (P.conditional y) hM s]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hrs : Ry s = 0
      · have hrs' : R (y, s) = 0 := by simpa [Ry] using hrs
        simp [hrs, hrs', perspective]
      · have hrspos : 0 < Ry s := lt_of_le_of_ne (hRy s) (Ne.symm hrs)
        have hrefpos : 0 < (M : ℝ)⁻¹ * R (y, s) := by
          have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
          exact mul_pos (inv_pos.mpr hMr) hrspos
        rw [perspective_of_pos f hrefpos]
        have hratio :
            (P.marginal y * H.seed s * outputMass H (P.conditional y) s z) /
                ((M : ℝ)⁻¹ * R (y, s)) =
              scale s * (M : ℝ) * outputMass H (P.conditional y) s z := by
          simp [scale, Ry, hrs]
          have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
          field_simp [hrs, hMr]
        rw [hratio]
        change Ry s * ((M : ℝ)⁻¹ * f _) =
          ((M : ℝ)⁻¹ * Ry s) * f _
        ring
    let A : ℝ := ∑ s, Ry s * scale s
    let qbar := averagedVector Ry hRy hQpos q
    have hA0 : 0 ≤ A :=
      Finset.sum_nonneg fun s _ ↦ mul_nonneg (hRy s) (hscale s)
    have hAle : A ≤ P.marginal y := by
      calc
        A ≤ ∑ s, P.marginal y * H.seed s := by
          apply Finset.sum_le_sum
          intro s _
          by_cases hrs : Ry s = 0
          · rw [hrs, zero_mul]
            exact mul_nonneg (P.marginal.nonneg y) (H.seed.nonneg s)
          · have heq : Ry s * scale s = P.marginal y * H.seed s := by
              simp [scale, hrs]
              field_simp [hrs]
            exact heq.le
        _ = P.marginal y := by
          rw [← Finset.mul_sum, H.seed.sum_prob, mul_one]
    have hscaleOrder : A / Qy ≤ P.marginal y / Qy :=
      div_le_div_of_nonneg_right hAle hQpos.le
    have haggregate := aggregate_scaled_cost f (P.conditional y) Ry scale
      hRy hscale hQpos q
    have hc : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
    rw [gammaTerm, if_neg hQ0]
    calc
      Qy * scaledCappedValue f (P.marginal y / Qy) (M : ℝ)⁻¹
          (P.conditional y) ≤
        Qy * scaledCappedCost f (P.marginal y / Qy)
          (P.conditional y) qbar := by
            gcongr
            exact CappedCost.scaledCappedValue_le_cost f
              (P.marginal y / Qy) (M : ℝ)⁻¹
              (div_nonneg (P.marginal.nonneg y) hQpos.le)
              (P.conditional y) qbar
      _ ≤ Qy * scaledCappedCost f (A / Qy) (P.conditional y) qbar := by
            gcongr
            exact CappedCost.scaledCappedCost_antitone_scale f
              (div_nonneg hA0 hQpos.le) hscaleOrder (P.conditional y) qbar
      _ ≤ ∑ s, Ry s * scaledCappedCost f (scale s) (P.conditional y) (q s) := by
            simpa [Qy, A, qbar] using haggregate
      _ = _ := href

theorem optimized_reference_converse (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M)
    (R : FinProb (Y × S)) :
    optimizedGammaObjective f P M (firstMarginal R) ≤
      referenceLeakage f P H R := by
  rw [optimizedGammaObjective, referenceLeakage]
  exact Finset.sum_le_sum fun y _ ↦ optimized_fiber_converse f P H hM R y

theorem optimized_family_converse (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    optimizedGamma f P M ≤ optimizedLeakage f P H := by
  rw [optimizedLeakage]
  apply le_csInf
  · let R₀ := P.marginal.prod H.seed
    exact ⟨referenceLeakage f P H R₀, R₀, rfl⟩
  · rintro v ⟨R, rfl⟩
    exact (optimizedGamma_le_objective f P M hM (firstMarginal R)).trans
      (optimized_reference_converse f P H hM R)

theorem optimal_optimized_converse (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) :
    optimizedGamma f P M ≤ optimalOptimizedLeakage f P M := by
  rw [optimalOptimizedLeakage]
  apply le_csInf
  · let H₀ : SeededHash X (Fin 1) M :=
      { seed := FinProb.uniformFin 1 (by omega)
        hash := fun _ _ ↦ ⟨0, hM⟩ }
    exact ⟨optimizedLeakage f P H₀, 1, H₀, rfl⟩
  · rintro v ⟨N, H, rfl⟩
    exact optimized_family_converse f P H hM

/-- **Lemma 5 (fixed- and optimized-reference converses).** -/
theorem paperLemma5 (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    fixedGamma f P M ≤ fixedLeakage f P H ∧
    fixedGamma f P M ≤ optimalFixedLeakage f P M ∧
    optimizedGamma f P M ≤ optimizedLeakage f P H ∧
    optimizedGamma f P M ≤ optimalOptimizedLeakage f P M := by
  exact ⟨fixed_family_converse f P H hM,
    optimal_fixed_converse f P M hM,
    optimized_family_converse f P H hM,
    optimal_optimized_converse f P M hM⟩

end OneShot

end RandomnessExtraction
