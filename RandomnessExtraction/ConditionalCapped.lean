import RandomnessExtraction.ConditionalLimit
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Uniform conditional capped approximation

This file formalizes Lemma 14.  Conditional probability vectors are indexed
by their actual supports, exactly as in the water-filling lemmas.
-/

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

namespace ConditionalCapped

open ConditionalLimit

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- The positive support of a finite probability vector. -/
abbrev Support (p : FinProb X) := {x : X // 0 < p x}

noncomputable instance (p : FinProb X) : Fintype (Support p) := inferInstance

/-- Restriction of a probability vector to its positive support. -/
def supportLaw (p : FinProb X) : FinProb (Support p) where
  prob x := p x.1
  nonneg x := p.nonneg x.1
  sum_prob := by
    classical
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x ↦ 0 < p x) p
    have hzero : (∑ x : {x : X // ¬ 0 < p x}, p x.1) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      exact le_antisymm (le_of_not_gt x.2) (p.nonneg x.1)
    rw [hzero, add_zero, p.sum_prob] at hsplit
    exact hsplit

@[simp]
theorem supportLaw_apply (p : FinProb X) (x : Support p) :
    supportLaw p x = p x.1 := rfl

theorem supportLaw_pos (p : FinProb X) (x : Support p) :
    0 < supportLaw p x := x.2

theorem support_nonempty (p : FinProb X) : Nonempty (Support p) := by
  by_contra hempty
  have hnonpos : ∀ x, ¬0 < p x := by
    intro x hx
    exact hempty ⟨⟨x, hx⟩⟩
  have hzero : ∀ x, p x = 0 := fun x ↦
    le_antisymm (le_of_not_gt (hnonpos x)) (p.nonneg x)
  have := p.sum_prob
  simp [hzero] at this

theorem support_card_pos (p : FinProb X) :
    0 < Fintype.card (Support p) :=
  Fintype.card_pos_iff.mpr (support_nonempty p)

/-- Zero-mass points may be discarded from a finite expectation. -/
theorem expect_eq_support (p : FinProb X) (g : X → ℝ) :
    p.expect g = ∑ z : Support p, p z.1 * g z.1 := by
  rw [FinProb.expect]
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x ↦ 0 < p x)
    (fun x ↦ p x * g x)
  have hzero : (∑ z : {x : X // ¬0 < p x}, p z.1 * g z.1) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    have hpz : p z.1 = 0 := le_antisymm (le_of_not_gt z.2) (p.nonneg z.1)
    simp [hpz]
  linarith

theorem supportLaw_event (p : FinProb X) (A : Set X) :
    (supportLaw p).event {z | z.1 ∈ A} = p.event A := by
  classical
  have h := expect_eq_support p (fun x ↦ if x ∈ A then 1 else 0)
  simpa [FinProb.expect, FinProb.event, Finset.sum_filter] using h.symm

/-- The dependent support of a conditional product fibre. -/
abbrev FiberSupport (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) :=
  ∀ i, Support (P.conditional (y i))

/-- Product law on the dependent conditional support. -/
def fiberSupportLaw (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) :
    FinProb (FiberSupport P y) where
  prob z := ∏ i, P.conditional (y i) (z i).1
  nonneg z := Finset.prod_nonneg fun i _ ↦ (P.conditional (y i)).nonneg (z i).1
  sum_prob := by
    classical
    calc
      (∑ z : FiberSupport P y, ∏ i, P.conditional (y i) (z i).1) =
          ∏ i, ∑ xi : Support (P.conditional (y i)),
            P.conditional (y i) xi.1 :=
        (Fintype.prod_sum
          (fun i (xi : Support (P.conditional (y i))) ↦
            P.conditional (y i) xi.1)).symm
      _ = ∏ _i : Fin n, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i _
        exact (supportLaw (P.conditional (y i))).sum_prob
      _ = 1 := by simp

@[simp]
theorem fiberSupportLaw_apply (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (z : FiberSupport P y) :
    fiberSupportLaw P y z = ∏ i, P.conditional (y i) (z i).1 := rfl

theorem fiberSupportLaw_pos (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (z : FiberSupport P y) : 0 < fiberSupportLaw P y z := by
  rw [fiberSupportLaw_apply]
  exact Finset.prod_pos fun i _ ↦ (z i).2

/-- A pointwise-positive conditional word is exactly a positive-support
point of the ordinary conditional product law. -/
noncomputable def fiberSupportEquiv (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) : FiberSupport P y ≃ Support (conditionalProduct P y) where
  toFun z := ⟨fun i ↦ (z i).1, by
    rw [conditionalProduct_apply]
    exact Finset.prod_pos fun i _ ↦ (z i).2⟩
  invFun z := fun i ↦ ⟨z.1 i, by
    have hprod : (∏ j, P.conditional (y j) (z.1 j)) ≠ 0 := by
      simpa only [conditionalProduct_apply] using z.2.ne'
    have hne : P.conditional (y i) (z.1 i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
    exact lt_of_le_of_ne ((P.conditional (y i)).nonneg (z.1 i)) (Ne.symm hne)⟩
  left_inv z := rfl
  right_inv z := rfl

@[simp]
theorem fiberSupportEquiv_val (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (z : FiberSupport P y) :
    (fiberSupportEquiv P y z).1 = fun i ↦ (z i).1 := rfl

theorem fiberSupportLaw_eq_supportLaw_under_equiv
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y)
    (z : FiberSupport P y) :
    fiberSupportLaw P y z =
      supportLaw (conditionalProduct P y) (fiberSupportEquiv P y z) := by
  rfl

/-- Surprisal on the positive conditional support. -/
noncomputable def fiberSurprisal (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (z : FiberSupport P y) : ℝ :=
  ∑ i, information P (z i).1 (y i)

theorem fiberSupport_surprisal_eq (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (z : FiberSupport P y) :
    ProbabilityRepresentation.surprisal (fiberSupportLaw P y) z =
      fiberSurprisal P y z := by
  rw [ProbabilityRepresentation.surprisal, fiberSupportLaw_apply,
    Real.logb_prod Finset.univ (fun i ↦ P.conditional (y i) (z i).1)
      (fun i _ ↦ ne_of_gt (z i).2)]
  simp only [fiberSurprisal, information]
  simp

/-- Conditional support entropy defect `d(y)`. -/
noncomputable def entropyDefect (P : FiniteSource X Y) (y : Y) : ℝ :=
  Real.logb 2 (Fintype.card (Support (P.conditional y))) - fiberEntropy P y

noncomputable def meanEntropyDefect (P : FiniteSource X Y) : ℝ :=
  P.marginal.expect (entropyDefect P)

/-- The entropy defect is the relative entropy from the conditional law to
the uniform law on its positive support, written with natural logarithms. -/
theorem entropyDefect_mul_log_two (P : FiniteSource X Y) (y : Y) :
    entropyDefect P y * Real.log 2 =
      ∑ z : Support (P.conditional y),
        P.conditional y z.1 *
          Real.log ((Fintype.card (Support (P.conditional y)) : ℝ) *
            P.conditional y z.1) := by
  let p := P.conditional y
  let N : ℝ := Fintype.card (Support p)
  have hNnat : 0 < Fintype.card (Support p) := support_card_pos p
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hNnat
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hsum : ∑ z : Support p, p z.1 = 1 := (supportLaw p).sum_prob
  change (Real.logb 2 N - p.expect (fun x ↦ -Real.logb 2 (p x))) *
      Real.log 2 = ∑ z : Support p, p z.1 * Real.log (N * p z.1)
  rw [FinProb.expect]
  have hrestrict : (∑ x, p x * -Real.logb 2 (p x)) =
      ∑ z : Support p, p z.1 * -Real.logb 2 (p z.1) := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x ↦ 0 < p x)
      (fun x ↦ p x * -Real.logb 2 (p x))
    have hzero :
        (∑ z : {x : X // ¬0 < p x},
          p z.1 * -Real.logb 2 (p z.1)) = 0 := by
      apply Finset.sum_eq_zero
      intro z _
      have hpz : p z.1 = 0 := le_antisymm (le_of_not_gt z.2) (p.nonneg z.1)
      simp [hpz]
    linarith
  rw [hrestrict]
  simp only [Real.logb]
  rw [sub_mul, div_mul_cancel₀ _ hlog2]
  have hlogmul : ∀ z : Support p,
      Real.log (N * p z.1) = Real.log N + Real.log (p z.1) :=
    fun z ↦ Real.log_mul hN.ne' z.2.ne'
  simp_rw [hlogmul]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hsumdiv :
      (∑ z : Support p,
        p z.1 * -(Real.log (p z.1) / Real.log 2)) =
      -(∑ z : Support p, p z.1 * Real.log (p z.1)) / Real.log 2 := by
    calc
      _ = ∑ z : Support p,
          (-(p z.1 * Real.log (p z.1))) * (Real.log 2)⁻¹ := by
            apply Finset.sum_congr rfl
            intro z _
            rw [div_eq_mul_inv]
            ring
      _ = (∑ z : Support p, -(p z.1 * Real.log (p z.1))) *
          (Real.log 2)⁻¹ := by rw [Finset.sum_mul]
      _ = _ := by rw [Finset.sum_neg_distrib, div_eq_mul_inv]
  rw [hsumdiv]
  field_simp [hlog2]
  ring

theorem entropyDefect_nonneg (P : FiniteSource X Y) (y : Y) :
    0 ≤ entropyDefect P y := by
  let p := P.conditional y
  let N : ℝ := Fintype.card (Support p)
  have hNnat : 0 < Fintype.card (Support p) := support_card_pos p
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hNnat
  have hsum : ∑ z : Support p, p z.1 = 1 := (supportLaw p).sum_prob
  have hbase :
      0 ≤ ∑ z : Support p,
        (N * p z.1) * Real.log (N * p z.1) := by
    calc
      0 = ∑ z : Support p, (N * p z.1 - 1) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
        simp [N]
      _ ≤ ∑ z : Support p,
          (N * p z.1) * Real.log (N * p z.1) := by
        exact Finset.sum_le_sum fun z _ ↦
          Real.self_sub_one_le_mul_log (mul_nonneg hN.le z.2.le)
  have hscaled :
      0 ≤ ∑ z : Support p, p z.1 * Real.log (N * p z.1) := by
    have heq : (∑ z : Support p, p z.1 * Real.log (N * p z.1)) =
        (∑ z : Support p, (N * p z.1) * Real.log (N * p z.1)) / N := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _
      field_simp [hN.ne']
    rw [heq]
    exact div_nonneg hbase hN.le
  have hid := entropyDefect_mul_log_two P y
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  change 0 ≤ entropyDefect P y
  nlinarith

theorem entropyDefect_pos_of_nonuniform (P : FiniteSource X Y) (y : Y)
    (hnu : ∃ z : Support (P.conditional y),
      (Fintype.card (Support (P.conditional y)) : ℝ) *
        P.conditional y z.1 ≠ 1) :
    0 < entropyDefect P y := by
  let p := P.conditional y
  let N : ℝ := Fintype.card (Support p)
  have hNnat : 0 < Fintype.card (Support p) := support_card_pos p
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hNnat
  have hsum : ∑ z : Support p, p z.1 = 1 := (supportLaw p).sum_prob
  have hstrict :
      0 < ∑ z : Support p,
        ((N * p z.1) * Real.log (N * p z.1) - (N * p z.1 - 1)) := by
    apply Finset.sum_pos'
    · intro z _
      linarith [Real.self_sub_one_le_mul_log
        (mul_nonneg hN.le z.2.le)]
    · rcases hnu with ⟨z, hz⟩
      refine ⟨z, Finset.mem_univ z, ?_⟩
      linarith [Real.self_sub_one_lt_mul_log
        (mul_nonneg hN.le z.2.le) hz]
  have hzero : ∑ z : Support p, (N * p z.1 - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    simp [N]
  have hbase :
      0 < ∑ z : Support p,
        (N * p z.1) * Real.log (N * p z.1) := by
    rw [Finset.sum_sub_distrib, hzero, sub_zero] at hstrict
    exact hstrict
  have hscaled :
      0 < ∑ z : Support p, p z.1 * Real.log (N * p z.1) := by
    have heq : (∑ z : Support p, p z.1 * Real.log (N * p z.1)) =
        (∑ z : Support p, (N * p z.1) * Real.log (N * p z.1)) / N := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _
      field_simp [hN.ne']
    rw [heq]
    exact div_pos hbase hN
  have hid := entropyDefect_mul_log_two P y
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  change 0 < entropyDefect P y
  nlinarith

theorem fiberVariance_eq_zero_of_uniform_support (P : FiniteSource X Y) (y : Y)
    (hu : ∀ z : Support (P.conditional y),
      (Fintype.card (Support (P.conditional y)) : ℝ) *
        P.conditional y z.1 = 1) :
    fiberVariance P y = 0 := by
  let p := P.conditional y
  let N : ℝ := Fintype.card (Support p)
  have hNnat : 0 < Fintype.card (Support p) := support_card_pos p
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hNnat
  have hprob : ∀ z : Support p, p z.1 = N⁻¹ := by
    intro z
    field_simp [hN.ne']
    simpa [mul_comm] using hu z
  have hinfo : ∀ z : Support p,
      information P z.1 y = Real.logb 2 N := by
    intro z
    rw [information, hprob z, Real.logb_inv]
    ring
  have hentropy : fiberEntropy P y = Real.logb 2 N := by
    rw [fiberEntropy, expect_eq_support]
    simp_rw [hinfo]
    rw [← Finset.sum_mul]
    change (∑ i : Support p, p i.1) * Real.logb 2 N = Real.logb 2 N
    have hsump : ∑ i : Support p, p i.1 = 1 := (supportLaw p).sum_prob
    rw [hsump, one_mul]
  rw [fiberVariance, expect_eq_support]
  simp_rw [hinfo, hentropy, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  simp

theorem entropyDefect_pos_of_fiberVariance_pos (P : FiniteSource X Y) (y : Y)
    (hv : 0 < fiberVariance P y) : 0 < entropyDefect P y := by
  apply entropyDefect_pos_of_nonuniform
  by_contra hnone
  push Not at hnone
  have hz := fiberVariance_eq_zero_of_uniform_support P y hnone
  linarith

theorem meanEntropyDefect_pos (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV2 : 0 < variance₂ P) :
    0 < meanEntropyDefect P := by
  have hex : ∃ y : Y, 0 < fiberVariance P y := by
    by_contra hnone
    push Not at hnone
    have hsum : variance₂ P ≤ 0 := by
      rw [variance₂, FinProb.expect]
      exact Finset.sum_nonpos fun y _ ↦
        mul_nonpos_of_nonneg_of_nonpos (P.marginal.nonneg y) (hnone y)
    linarith
  rcases hex with ⟨y₀, hy₀⟩
  rw [meanEntropyDefect, FinProb.expect]
  apply Finset.sum_pos'
  · intro y _
    exact mul_nonneg (P.marginal.nonneg y) (entropyDefect_nonneg P y)
  · refine ⟨y₀, Finset.mem_univ y₀, ?_⟩
    exact mul_pos (hpY y₀) (entropyDefect_pos_of_fiberVariance_pos P y₀ hy₀)

/-- The typical event in equation (76). -/
def IsTypical (P : FiniteSource X Y) (K : ℝ) {n : ℕ}
    (y : Fin n → Y) : Prop :=
  |center P y| ≤ K ∧
    |conditionalVariance P y / (n : ℝ) - variance₂ P| ≤ variance₂ P / 2 ∧
    |(∑ i, entropyDefect P (y i)) / (n : ℝ) - meanEntropyDefect P| ≤
      meanEntropyDefect P / 2

noncomputable def typicalArgumentBound (P : FiniteSource X Y)
    (x K : ℝ) : ℝ :=
  (|x * Real.sqrt (totalVariance P)| + K) /
    Real.sqrt (variance₂ P / 2)

theorem empiricalArgument_abs_le_on_typical (P : FiniteSource X Y)
    {n : ℕ} (hn : 0 < n) (hV2 : 0 < variance₂ P) (x : ℝ)
    {K : ℝ} (hK : 0 ≤ K) (y : Fin n → Y) (hy : IsTypical P K y) :
    |empiricalGaussianArgument P y x| ≤ typicalArgumentBound P x K := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratio : variance₂ P / 2 ≤ conditionalVariance P y / (n : ℝ) := by
    linarith [abs_le.mp hy.2.1 |>.1]
  have hbase : 0 < variance₂ P / 2 := by linarith
  have hσratio : 0 < conditionalVariance P y / (n : ℝ) :=
    hbase.trans_le hratio
  have hσ : 0 < conditionalVariance P y := by
    have := (div_pos_iff.mp hσratio)
    rcases this with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hnR.le hneg.2).elim
  rw [empiricalGaussianArgument_eq_normalized P hn y x hσ]
  rw [normalizedEmpiricalGaussianArgument, abs_div,
    abs_of_pos (Real.sqrt_pos.2 hσratio)]
  have hnum : |x * Real.sqrt (totalVariance P) + center P y| ≤
      |x * Real.sqrt (totalVariance P)| + K :=
    (abs_add_le _ _).trans
      (add_le_add le_rfl hy.1)
  have hA : 0 ≤ |x * Real.sqrt (totalVariance P)| + K :=
    add_nonneg (abs_nonneg _) hK
  have hsqrt : Real.sqrt (variance₂ P / 2) ≤
      Real.sqrt (conditionalVariance P y / (n : ℝ)) :=
    Real.sqrt_le_sqrt hratio
  calc
    |x * Real.sqrt (totalVariance P) + center P y| /
        Real.sqrt (conditionalVariance P y / (n : ℝ)) ≤
      (|x * Real.sqrt (totalVariance P)| + K) /
        Real.sqrt (conditionalVariance P y / (n : ℝ)) :=
      div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)
    _ ≤ (|x * Real.sqrt (totalVariance P)| + K) /
        Real.sqrt (variance₂ P / 2) := by
      exact div_le_div_of_nonneg_left hA (Real.sqrt_pos.2 hbase) hsqrt
    _ = typicalArgumentBound P x K := rfl

/-- Conditional support tail at the paper threshold. -/
noncomputable def supportTail (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x : ℝ) : ℝ :=
  TailLimit.tailGE (fiberSupportLaw P y) (threshold P n x)

/-- Scaled capped value on one conditional support fibre. -/
noncomputable def fiberScaledCappedValue (f : AdmissibleGenerator)
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) (x a : ℝ) : ℝ :=
  scaledCappedValue f a ((2 : ℝ) ^ (-threshold P n x)) (fiberSupportLaw P y)

theorem supportTail_eq_conditionalTail (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x : ℝ) :
    supportTail P y x = conditionalTail P y x := by
  classical
  let A : Set (Fin n → X) :=
    {z | threshold P n x ≤ blockInformation P z y}
  have hs := supportLaw_event (conditionalProduct P y) A
  unfold supportTail TailLimit.tailGE TailLimit.eventProbability
  simp only [Finset.sum_filter]
  calc
    (∑ z : FiberSupport P y,
        if threshold P n x ≤ ProbabilityRepresentation.surprisal
            (fiberSupportLaw P y) z then fiberSupportLaw P y z else 0) =
      ∑ w : Support (conditionalProduct P y),
        if w.1 ∈ A then supportLaw (conditionalProduct P y) w else 0 := by
          apply Fintype.sum_equiv (fiberSupportEquiv P y)
          intro z
          rw [fiberSupport_surprisal_eq,
            fiberSupportLaw_eq_supportLaw_under_equiv]
          rfl
    _ = (conditionalProduct P y).event A := by
      simpa [FinProb.event, Finset.sum_filter] using hs
    _ = conditionalTail P y x := rfl

theorem fiberSupport_card (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) :
    (Fintype.card (FiberSupport P y) : ℝ) =
      ∏ i, (Fintype.card (Support (P.conditional (y i))) : ℝ) := by
  norm_cast
  exact Fintype.card_pi

theorem logb_fiberSupport_card (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) :
    Real.logb 2 (Fintype.card (FiberSupport P y)) =
      ∑ i, Real.logb 2 (Fintype.card (Support (P.conditional (y i)))) := by
  rw [fiberSupport_card]
  apply Real.logb_prod
  intro i _
  exact_mod_cast (support_card_pos (P.conditional (y i))).ne'

/-- Equation (79), including the support cardinality identity that is
implicit in the paper's product notation. -/
theorem supportGap_identity (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x : ℝ) :
    Real.logb 2 (Fintype.card (FiberSupport P y)) - threshold P n x =
      (∑ i, entropyDefect P (y i)) + conditionalMean P y -
        threshold P n x := by
  rw [logb_fiberSupport_card]
  simp only [entropyDefect, conditionalMean]
  rw [Finset.sum_sub_distrib]
  ring

/-- Equations (77) and (80): uniformly on a fixed typical set, the
conditional tail stays in a compact subinterval of `(0,1)`. -/
theorem typicalTail_boundedAway
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hV2 : 0 < variance₂ P) (x : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      ∀ᶠ n in atTop, ∀ y : Fin n → Y, IsTypical P K y →
        η ≤ supportTail P y x ∧ supportTail P y x ≤ 1 - η := by
  let B := typicalArgumentBound P x K
  let η := min (gaussianCDF (-B)) (1 - gaussianCDF B) / 3
  have hphiL : 0 < gaussianCDF (-B) := gaussianCDF_pos _
  have hphiR : 0 < 1 - gaussianCDF B := sub_pos.mpr (gaussianCDF_lt_one _)
  have heta : 0 < η := div_pos (lt_min hphiL hphiR) (by norm_num)
  have hetaL : 3 * η ≤ gaussianCDF (-B) := by
    dsimp [η]
    have := min_le_left (gaussianCDF (-B)) (1 - gaussianCDF B)
    linarith
  have hetaR : 3 * η ≤ 1 - gaussianCDF B := by
    dsimp [η]
    have := min_le_right (gaussianCDF (-B)) (1 - gaussianCDF B)
    linarith
  have hetaHalf : η < 1 / 2 := by
    have hlt : gaussianCDF (-B) < 1 := gaussianCDF_lt_one _
    linarith
  let R : ℕ → ℝ := fun n ↦
    berryEsseenConstant hBE * ((n : ℝ) * thirdMomentTotal P) /
      (Real.sqrt ((n : ℝ) * (variance₂ P / 2))) ^ 3
  have hR : Tendsto R atTop (𝓝 0) :=
    berryEsseen_iid_rate_tendsto_zero hBE (thirdMomentTotal P)
      (variance₂ P / 2) (by linarith)
  have hRsmall : ∀ᶠ n in atTop, R n < η :=
    (tendsto_order.1 hR).2 η heta
  refine ⟨η, heta, hetaHalf, ?_⟩
  filter_upwards [eventually_gt_atTop 0, hRsmall] with n hn hRn
  intro y hy
  have hgood : variance₂ P / 2 ≤ conditionalVariance P y / (n : ℝ) := by
    linarith [abs_le.mp hy.2.1 |>.1]
  have herr := conditionalTail_berryEsseen_rate hBE P hn y x hV2 hgood
  change |conditionalTail P y x -
      gaussianCDF (empiricalGaussianArgument P y x)| ≤ R n at herr
  have harg := empiricalArgument_abs_le_on_typical P hn hV2 x hK y hy
  have hargIcc : -B ≤ empiricalGaussianArgument P y x ∧
      empiricalGaussianArgument P y x ≤ B := by
    simpa [B, abs_le] using (abs_le.mp harg)
  have hmono : Monotone gaussianCDF :=
    ProbabilityTheory.monotone_cdf (ProbabilityTheory.gaussianReal 0 1)
  have hphiLower : gaussianCDF (-B) ≤
      gaussianCDF (empiricalGaussianArgument P y x) := hmono hargIcc.1
  have hphiUpper : gaussianCDF (empiricalGaussianArgument P y x) ≤
      gaussianCDF B := hmono hargIcc.2
  rw [supportTail_eq_conditionalTail]
  constructor
  · have herrLower := (abs_le.mp herr).1
    linarith
  · have herrUpper := (abs_le.mp herr).2
    linarith

noncomputable def shiftedThresholdParameter (P : FiniteSource X Y)
    (n : ℕ) (x s : ℝ) : ℝ :=
  x - s / Real.sqrt ((n : ℝ) * totalVariance P)

theorem threshold_shiftedParameter (P : FiniteSource X Y) {n : ℕ}
    (hn : 0 < n) (hV2 : 0 < variance₂ P) (x s : ℝ) :
    threshold P n (shiftedThresholdParameter P n x s) =
      threshold P n x + s := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hV : 0 < totalVariance P := by
    dsimp [totalVariance]
    linarith [variance₁_nonneg P]
  have hsqrt : 0 < Real.sqrt ((n : ℝ) * totalVariance P) :=
    Real.sqrt_pos.2 (mul_pos hnR hV)
  unfold threshold shiftedThresholdParameter
  field_simp [hsqrt.ne']
  ring

theorem empiricalArgument_shiftedParameter (P : FiniteSource X Y) {n : ℕ}
    (hn : 0 < n) (hV2 : 0 < variance₂ P) (x s : ℝ)
    (y : Fin n → Y) (hσ : 0 < conditionalVariance P y) :
    empiricalGaussianArgument P y (shiftedThresholdParameter P n x s) =
      empiricalGaussianArgument P y x - s / Real.sqrt (conditionalVariance P y) := by
  rw [empiricalGaussianArgument, empiricalGaussianArgument,
    threshold_shiftedParameter P hn hV2]
  have hsqrt : 0 < Real.sqrt (conditionalVariance P y) := Real.sqrt_pos.2 hσ
  field_simp [hsqrt.ne']
  ring

theorem conditionalTail_shiftedParameter (P : FiniteSource X Y) {n : ℕ}
    (hn : 0 < n) (hV2 : 0 < variance₂ P) (x s : ℝ)
    (y : Fin n → Y) :
    conditionalTail P y (shiftedThresholdParameter P n x s) =
      (conditionalProduct P y).event
        {z | threshold P n x + s ≤ blockInformation P z y} := by
  rw [conditionalTail, threshold_shiftedParameter P hn hV2]

noncomputable def supportWindow (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x u B : ℝ) : ℝ :=
  TailLimit.windowProbability (fiberSupportLaw P y) (threshold P n x) u B

theorem finProb_event_add_le_event {A : Type} [Fintype A]
    (p : FinProb A) (E F G : Set A)
    (hEG : ∀ z, z ∈ E → z ∈ G) (hFG : ∀ z, z ∈ F → z ∈ G)
    (hdisj : ∀ z, z ∈ E → z ∈ F → False) :
    p.event E + p.event F ≤ p.event G := by
  classical
  simp only [FinProb.event, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  by_cases hE : z ∈ E <;> by_cases hF : z ∈ F
  · exact (hdisj z hE hF).elim
  · simp [hE, hF, hEG z hE]
  · simp [hE, hF, hFG z hF]
  · by_cases hG : z ∈ G
    · simpa [hE, hF, hG] using p.nonneg z
    · simp [hE, hF, hG]

theorem supportWindow_le_shiftedTail_sub (P : FiniteSource X Y)
    {n : ℕ} (hn : 0 < n) (hV2 : 0 < variance₂ P)
    (y : Fin n → Y) (x u B : ℝ) (hB : 0 ≤ B) :
    supportWindow P y x u B ≤
      conditionalTail P y (shiftedThresholdParameter P n x (u - B)) -
        conditionalTail P y (shiftedThresholdParameter P n x (u + B + 1)) := by
  let W : Set (Fin n → X) :=
    {z | |blockInformation P z y - threshold P n x - u| ≤ B}
  let E : Set (Fin n → X) :=
    {z | threshold P n x + (u - B) ≤ blockInformation P z y}
  let F : Set (Fin n → X) :=
    {z | threshold P n x + (u + B + 1) ≤ blockInformation P z y}
  have hadd : (conditionalProduct P y).event W +
      (conditionalProduct P y).event F ≤ (conditionalProduct P y).event E := by
    apply finProb_event_add_le_event
    · intro z hz
      dsimp [W, E] at hz ⊢
      linarith [abs_le.mp hz |>.1]
    · intro z hz
      dsimp [F, E] at hz ⊢
      linarith
    · intro z hzW hzF
      dsimp [W, F] at hzW hzF
      linarith [abs_le.mp hzW |>.2]
  rw [conditionalTail_shiftedParameter P hn hV2,
    conditionalTail_shiftedParameter P hn hV2]
  have hwindow : supportWindow P y x u B = (conditionalProduct P y).event W := by
    unfold supportWindow TailLimit.windowProbability TailLimit.eventProbability
    simp only [Finset.sum_filter]
    let A : Set (Fin n → X) :=
      {z | |blockInformation P z y - threshold P n x - u| ≤ B}
    have hs := supportLaw_event (conditionalProduct P y) A
    calc
      (∑ z : FiberSupport P y,
          if |ProbabilityRepresentation.surprisal (fiberSupportLaw P y) z -
              threshold P n x - u| ≤ B then fiberSupportLaw P y z else 0) =
        ∑ z : Support (conditionalProduct P y),
          if z.1 ∈ A then supportLaw (conditionalProduct P y) z else 0 := by
            apply Fintype.sum_equiv (fiberSupportEquiv P y)
            intro z
            rw [fiberSupport_surprisal_eq,
              fiberSupportLaw_eq_supportLaw_under_equiv]
            rfl
      _ = (conditionalProduct P y).event A := by
        simpa [FinProb.event, Finset.sum_filter] using hs
      _ = (conditionalProduct P y).event W := rfl
  rw [hwindow]
  linarith

theorem constant_div_sqrt_nat_mul_tendsto_zero (D c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ D / Real.sqrt ((n : ℝ) * c)) atTop (𝓝 0) := by
  let K := D / Real.sqrt c
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hsimple : Tendsto (fun n : ℕ ↦ K * (Real.sqrt (n : ℝ))⁻¹)
      atTop (𝓝 0) := by simpa using tendsto_const_nhds.mul hinv
  apply hsimple.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  rw [Real.sqrt_mul hnR.le c]
  dsimp [K]
  field_simp [Real.sqrt_ne_zero'.2 hnR, hsqrtc.ne']

/-- Equation (78), in the uniform epsilon form actually needed by the
subsequence argument.  The bound is independent of the center shift `u`. -/
theorem typical_uniformAntiConcentration
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hV2 : 0 < variance₂ P) (x K : ℝ) :
    ∀ T B : ℝ, 0 < T → 0 < B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ y : Fin n → Y, IsTypical P K y →
        ∀ u : ℝ, |u| ≤ T → supportWindow P y x u B < ε := by
  intro T B _hT hB ε hε
  obtain ⟨δ, hδ, hmap⟩ :=
    (Metric.uniformContinuous_iff.1 uniformContinuous_gaussianCDF)
      (ε / 2) (by linarith)
  let D := 2 * B + 1
  have hD : 0 < D := by dsimp [D]; linarith
  have hgap : Tendsto
      (fun n : ℕ ↦ D / Real.sqrt ((n : ℝ) * (variance₂ P / 2)))
      atTop (𝓝 0) :=
    constant_div_sqrt_nat_mul_tendsto_zero D (variance₂ P / 2) (by linarith)
  have hgapSmall : ∀ᶠ n : ℕ in atTop,
      D / Real.sqrt ((n : ℝ) * (variance₂ P / 2)) < δ :=
    (tendsto_order.1 hgap).2 δ hδ
  let R : ℕ → ℝ := fun n ↦
    berryEsseenConstant hBE * ((n : ℝ) * thirdMomentTotal P) /
      (Real.sqrt ((n : ℝ) * (variance₂ P / 2))) ^ 3
  have hR : Tendsto R atTop (𝓝 0) :=
    berryEsseen_iid_rate_tendsto_zero hBE (thirdMomentTotal P)
      (variance₂ P / 2) (by linarith)
  have hRsmall : ∀ᶠ n in atTop, R n < ε / 4 :=
    (tendsto_order.1 hR).2 _ (by linarith)
  filter_upwards [eventually_gt_atTop 0, hgapSmall, hRsmall] with n hn hgn hRn
  intro y hy u _hu
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hgood : variance₂ P / 2 ≤ conditionalVariance P y / (n : ℝ) := by
    linarith [abs_le.mp hy.2.1 |>.1]
  have hbase : 0 < (n : ℝ) * (variance₂ P / 2) :=
    mul_pos hnR (by linarith)
  have hσlower : (n : ℝ) * (variance₂ P / 2) ≤ conditionalVariance P y := by
    have := (le_div_iff₀ hnR).mp hgood
    nlinarith
  have hσ : 0 < conditionalVariance P y := hbase.trans_le hσlower
  let sL := u - B
  let sU := u + B + 1
  let aL := shiftedThresholdParameter P n x sL
  let aU := shiftedThresholdParameter P n x sU
  have herrL := conditionalTail_berryEsseen_rate hBE P hn y aL hV2 hgood
  have herrU := conditionalTail_berryEsseen_rate hBE P hn y aU hV2 hgood
  change |conditionalTail P y aL - gaussianCDF (empiricalGaussianArgument P y aL)| ≤
      R n at herrL
  change |conditionalTail P y aU - gaussianCDF (empiricalGaussianArgument P y aU)| ≤
      R n at herrU
  have hargL := empiricalArgument_shiftedParameter P hn hV2 x sL y hσ
  have hargU := empiricalArgument_shiftedParameter P hn hV2 x sU y hσ
  have hsqrtσ : 0 < Real.sqrt (conditionalVariance P y) := Real.sqrt_pos.2 hσ
  have hdist : dist (empiricalGaussianArgument P y aL)
      (empiricalGaussianArgument P y aU) < δ := by
    have heq : dist (empiricalGaussianArgument P y aL)
        (empiricalGaussianArgument P y aU) =
        D / Real.sqrt (conditionalVariance P y) := by
      rw [hargL, hargU, Real.dist_eq]
      have hdiff :
          (empiricalGaussianArgument P y x - sL / Real.sqrt (conditionalVariance P y)) -
            (empiricalGaussianArgument P y x - sU / Real.sqrt (conditionalVariance P y)) =
          D / Real.sqrt (conditionalVariance P y) := by
        dsimp [sL, sU, D]
        field_simp [hsqrtσ.ne']
        ring
      rw [hdiff, abs_of_nonneg (div_nonneg hD.le hsqrtσ.le)]
    rw [heq]
    have hsqrtLower : Real.sqrt ((n : ℝ) * (variance₂ P / 2)) ≤
        Real.sqrt (conditionalVariance P y) := Real.sqrt_le_sqrt hσlower
    exact (div_le_div_of_nonneg_left hD.le (Real.sqrt_pos.2 hbase)
      hsqrtLower).trans_lt hgn
  have hphiDist := hmap hdist
  rw [Real.dist_eq] at hphiDist
  have hargOrder : empiricalGaussianArgument P y aU ≤
      empiricalGaussianArgument P y aL := by
    rw [hargL, hargU]
    dsimp [sL, sU]
    have hsqrtInv : 0 ≤ (Real.sqrt (conditionalVariance P y))⁻¹ :=
      (inv_nonneg.mpr hsqrtσ.le)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    nlinarith
  have hmono : Monotone gaussianCDF :=
    ProbabilityTheory.monotone_cdf (ProbabilityTheory.gaussianReal 0 1)
  have hphiOrder := hmono hargOrder
  have hphiGap : gaussianCDF (empiricalGaussianArgument P y aL) -
      gaussianCDF (empiricalGaussianArgument P y aU) < ε / 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hphiOrder)] at hphiDist
    exact hphiDist
  have hwindow := supportWindow_le_shiftedTail_sub P hn hV2 y x u B hB.le
  change supportWindow P y x u B ≤ conditionalTail P y aL -
      conditionalTail P y aU at hwindow
  have hLupper := (abs_le.mp herrL).2
  have hUlower := (abs_le.mp herrU).1
  linarith

/-- The support condition following equation (79), uniformly on the typical
set. -/
theorem typical_supportCondition_eventually
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : 0 < variance₂ P) (x : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ n in atTop, ∀ y : Fin n → Y, IsTypical P K y →
      1 < (2 : ℝ) ^ (-threshold P n x) * Fintype.card (FiberSupport P y) := by
  have hD0 : 0 < meanEntropyDefect P := meanEntropyDefect_pos P hpY hV2
  let C := |x * Real.sqrt (totalVariance P)| + K
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) hK
  have hratio : Tendsto (fun n : ℕ ↦ C / Real.sqrt ((n : ℝ) * 1))
      atTop (𝓝 0) := constant_div_sqrt_nat_mul_tendsto_zero C 1 (by norm_num)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C / Real.sqrt ((n : ℝ) * 1) < meanEntropyDefect P / 4 :=
    (tendsto_order.1 hratio).2 _ (by linarith)
  filter_upwards [eventually_gt_atTop 0, hsmall] with n hn hsmalln
  intro y hy
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrtn_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnR.le
  have hsumDefect : (n : ℝ) * (meanEntropyDefect P / 2) ≤
      ∑ i, entropyDefect P (y i) := by
    have hlower : meanEntropyDefect P / 2 ≤
        (∑ i, entropyDefect P (y i)) / (n : ℝ) := by
      linarith [abs_le.mp hy.2.2 |>.1]
    simpa [mul_comm] using (le_div_iff₀ hnR).mp hlower
  have hsqrtNV : Real.sqrt ((n : ℝ) * totalVariance P) =
      Real.sqrt n * Real.sqrt (totalVariance P) :=
    Real.sqrt_mul hnR.le _
  have hmean : conditionalMean P y - threshold P n x =
      Real.sqrt n * (x * Real.sqrt (totalVariance P) + center P y) := by
    rw [threshold, ConditionalLimit.center, hsqrtNV]
    field_simp [hsqrtn.ne']
    ring
  have hinside : -C ≤ x * Real.sqrt (totalVariance P) + center P y := by
    dsimp [C]
    have hx : -|x * Real.sqrt (totalVariance P)| ≤
        x * Real.sqrt (totalVariance P) := neg_abs_le _
    have hyc : -K ≤ center P y := (abs_le.mp hy.1).1
    linarith
  have hmeanLower : -(Real.sqrt n * C) ≤
      conditionalMean P y - threshold P n x := by
    rw [hmean]
    have := mul_le_mul_of_nonneg_left hinside hsqrtn.le
    linarith
  have hCsqrt : Real.sqrt n * C < (n : ℝ) * (meanEntropyDefect P / 4) := by
    have hsmall' : C / Real.sqrt n < meanEntropyDefect P / 4 := by
      simpa using hsmalln
    rw [div_lt_iff₀ hsqrtn] at hsmall'
    nlinarith
  have hgap : 0 <
      Real.logb 2 (Fintype.card (FiberSupport P y)) - threshold P n x := by
    rw [supportGap_identity]
    have hnD : 0 < (n : ℝ) * (meanEntropyDefect P / 4) :=
      mul_pos hnR (by linarith)
    linarith
  have hcardNat : 0 < Fintype.card (FiberSupport P y) :=
    Fintype.card_pos_iff.mpr ⟨fun i ↦ Classical.choice
      (support_nonempty (P.conditional (y i)))⟩
  have hcard : 0 < (Fintype.card (FiberSupport P y) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    1 < (2 : ℝ) ^
        (Real.logb 2 (Fintype.card (FiberSupport P y)) - threshold P n x) :=
      Real.one_lt_rpow (by norm_num) hgap
    _ = (2 : ℝ) ^ (-threshold P n x) *
        Fintype.card (FiberSupport P y) := by
      rw [show Real.logb 2 (Fintype.card (FiberSupport P y)) - threshold P n x =
          -threshold P n x + Real.logb 2 (Fintype.card (FiberSupport P y)) by ring,
        Real.rpow_add (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) hcard]

/-- The first conclusion of Lemma 14, stated without supremum notation. -/
def UniformTypicalScaledApproximation (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (x K : ℝ) : Prop :=
  ∀ aMin aMax : ℝ, 0 < aMin → aMin < aMax →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ y : Fin n → Y, IsTypical P K y →
        ∀ a : ℝ, a ∈ Set.Icc aMin aMax →
          |fiberScaledCappedValue f P y x a - f (a * supportTail P y x)| < ε

theorem uniformTypicalScaledApproximation
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : 0 < variance₂ P) (x : ℝ) {K : ℝ} (hK : 0 < K) :
    UniformTypicalScaledApproximation f P x K := by
  intro aMin aMax haMin haMM ε hε
  by_contra hnot
  have hfreq : ∃ᶠ n : ℕ in atTop,
      ¬(∀ y : Fin n → Y, IsTypical P K y →
        ∀ a : ℝ, a ∈ Set.Icc aMin aMax →
          |fiberScaledCappedValue f P y x a - f (a * supportTail P y x)| < ε) :=
    (Filter.not_eventually.mp hnot)
  obtain ⟨η, heta, hetaHalf, hqEventually⟩ :=
    typicalTail_boundedAway hBE P hV2 x hK.le
  have hfreq' : ∃ᶠ n : ℕ in atTop,
      (¬(∀ y : Fin n → Y, IsTypical P K y →
        ∀ a : ℝ, a ∈ Set.Icc aMin aMax →
          |fiberScaledCappedValue f P y x a - f (a * supportTail P y x)| < ε)) ∧
      (∀ y : Fin n → Y, IsTypical P K y →
        η ≤ supportTail P y x ∧ supportTail P y x ≤ 1 - η) :=
    hfreq.and_eventually hqEventually
  obtain ⟨φ, hφ, hsel⟩ := Filter.extraction_of_frequently_atTop hfreq'
  have hex : ∀ j, ∃ y : Fin (φ j) → Y, IsTypical P K y ∧
      ∃ a : ℝ, a ∈ Set.Icc aMin aMax ∧
        ε ≤ |fiberScaledCappedValue f P y x a - f (a * supportTail P y x)| := by
    intro j
    have hb := (hsel j).1
    push Not at hb
    exact hb
  let yj : ∀ j, Fin (φ j) → Y := fun j ↦ Classical.choose (hex j)
  have hyj (j : ℕ) : IsTypical P K (yj j) := (Classical.choose_spec (hex j)).1
  have haExists (j : ℕ) : ∃ a : ℝ, a ∈ Set.Icc aMin aMax ∧
      ε ≤ |fiberScaledCappedValue f P (yj j) x a -
        f (a * supportTail P (yj j) x)| :=
    (Classical.choose_spec (hex j)).2
  let aj : ℕ → ℝ := fun j ↦ Classical.choose (haExists j)
  have haj (j : ℕ) : aj j ∈ Set.Icc aMin aMax :=
    (Classical.choose_spec (haExists j)).1
  have hbad (j : ℕ) : ε ≤
      |fiberScaledCappedValue f P (yj j) x (aj j) -
        f (aj j * supportTail P (yj j) x)| :=
    (Classical.choose_spec (haExists j)).2
  let qj : ℕ → ℝ := fun j ↦ supportTail P (yj j) x
  have hqj (j : ℕ) : qj j ∈ Set.Icc η (1 - η) := by
    exact (hsel j).2 (yj j) (hyj j)
  let aqj : ℕ → ℝ × ℝ := fun j ↦ (aj j, qj j)
  have haqj (j : ℕ) : aqj j ∈
      Set.Icc aMin aMax ×ˢ Set.Icc η (1 - η) := ⟨haj j, hqj j⟩
  obtain ⟨aq, haq, ψ, hψ, hconv⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq haqj
  rcases aq with ⟨a, q⟩
  rcases haq with ⟨ha, hq⟩
  let χ : ℕ → ℕ := φ ∘ ψ
  have hχmono : StrictMono χ := hφ.comp hψ
  have hχ : Tendsto χ atTop atTop := hχmono.tendsto_atTop
  have haConv : Tendsto (fun j ↦ aj (ψ j)) atTop (𝓝 a) := by
    have := (continuous_fst.tendsto (a, q)).comp hconv
    simpa [aqj, Function.comp_def] using this
  have hqConv : Tendsto (fun j ↦ qj (ψ j)) atTop (𝓝 q) := by
    have := (continuous_snd.tendsto (a, q)).comp hconv
    simpa [aqj, Function.comp_def] using this
  have hq0 : 0 < q := heta.trans_le hq.1
  have hq1 : q < 1 := by linarith [hq.2]
  have hTail : Tendsto
      (fun j ↦ TailLimit.tailGE (fiberSupportLaw P (yj (ψ j)))
        (threshold P (χ j) x)) atTop (𝓝 q) := by
    simpa [qj, supportTail, χ, Function.comp_def] using hqConv
  have hAnti : TailLimit.UniformAntiConcentration
      (fun j ↦ FiberSupport P (yj (ψ j)))
      (fun j ↦ fiberSupportLaw P (yj (ψ j)))
      (fun j ↦ threshold P (χ j) x) := by
    intro T B hT hB δ hδ
    have hraw := typical_uniformAntiConcentration hBE P hV2 x K
      T B hT hB δ hδ
    have hcomp := hχ.eventually hraw
    filter_upwards [hcomp] with j hj
    intro u hu
    simpa [supportWindow, χ, Function.comp_def] using
      hj (yj (ψ j)) (hyj (ψ j)) u hu
  have hSupport : ∀ᶠ j in atTop,
      1 < (2 : ℝ) ^ (-threshold P (χ j) x) *
        Fintype.card (FiberSupport P (yj (ψ j))) := by
    have hraw := typical_supportCondition_eventually P hpY hV2 x hK.le
    have hcomp := hχ.eventually hraw
    filter_upwards [hcomp] with j hj
    simpa [χ, Function.comp_def] using hj (yj (ψ j)) (hyj (ψ j))
  have hL11 := TailLimit.paperLemma11.{0, 0}
    (fun j ↦ FiberSupport P (yj (ψ j))) f
    (fun j ↦ fiberSupportLaw P (yj (ψ j)))
    (fun j z ↦ fiberSupportLaw_pos P (yj (ψ j)) z)
    (fun j ↦ threshold P (χ j) x) q hq0 hq1 hTail hAnti hSupport
  have hlocal := hL11.1 aMin aMax haMin haMM (ε / 3) (by linarith)
  have hprodFixed : Tendsto (fun j ↦ aj (ψ j) * q) atTop (𝓝 (a * q)) :=
    haConv.mul tendsto_const_nhds
  have hprodMoving : Tendsto (fun j ↦ aj (ψ j) * qj (ψ j))
      atTop (𝓝 (a * q)) := haConv.mul hqConv
  have hfFixed : Tendsto (fun j ↦ f (aj (ψ j) * q)) atTop (𝓝 (f (a * q))) :=
    (f.continuousAt (a * q)).tendsto.comp hprodFixed
  have hfMoving : Tendsto (fun j ↦ f (aj (ψ j) * qj (ψ j)))
      atTop (𝓝 (f (a * q))) :=
    (f.continuousAt (a * q)).tendsto.comp hprodMoving
  have hdiff : Tendsto
      (fun j ↦ f (aj (ψ j) * q) - f (aj (ψ j) * qj (ψ j)))
      atTop (𝓝 0) := by
    convert hfFixed.sub hfMoving using 1 <;> simp
  have habsDiff : Tendsto
      (fun j ↦ |f (aj (ψ j) * q) - f (aj (ψ j) * qj (ψ j))|)
      atTop (𝓝 0) := by
    simpa using hdiff.abs
  have hdiffSmall : ∀ᶠ j in atTop,
      |f (aj (ψ j) * q) - f (aj (ψ j) * qj (ψ j))| < ε / 3 :=
    (tendsto_order.1 habsDiff).2 (ε / 3) (by linarith)
  obtain ⟨j, hjLocal, hjDiff⟩ := (hlocal.and hdiffSmall).exists
  have hloc :
      |fiberScaledCappedValue f P (yj (ψ j)) x (aj (ψ j)) -
        f (aj (ψ j) * q)| < ε / 3 := by
    simpa [fiberScaledCappedValue, χ, Function.comp_def] using
      hjLocal (aj (ψ j)) (haj (ψ j))
  have htri :
      |fiberScaledCappedValue f P (yj (ψ j)) x (aj (ψ j)) -
          f (aj (ψ j) * qj (ψ j))| < ε := by
    calc
      _ ≤ |fiberScaledCappedValue f P (yj (ψ j)) x (aj (ψ j)) -
            f (aj (ψ j) * q)| +
          |f (aj (ψ j) * q) - f (aj (ψ j) * qj (ψ j))| := by
        simpa only [sub_add_sub_cancel] using abs_add_le
          (fiberScaledCappedValue f P (yj (ψ j)) x (aj (ψ j)) -
            f (aj (ψ j) * q))
          (f (aj (ψ j) * q) - f (aj (ψ j) * qj (ψ j)))
      _ < ε := by linarith
  exact (not_lt_of_ge (hbad (ψ j)) htri)

theorem entropyDefect_centered (P : FiniteSource X Y) {n : ℕ}
    (hn : 0 < n) (y : Fin n → Y) :
    (∑ i, entropyDefect P (y i)) / (n : ℝ) - meanEntropyDefect P =
      (∑ i, centered P.marginal (entropyDefect P) (y i)) / (n : ℝ) := by
  simp only [centered, meanEntropyDefect]
  rw [Finset.sum_sub_distrib]
  simp
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

theorem entropyDefect_weakLaw
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) :
    TendstoInProbabilityZero (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
      (fun n y ↦ (∑ i, entropyDefect P (y i)) / (n : ℝ) -
        meanEntropyDefect P) := by
  intro ε hε
  have hraw := iid_weakLaw hBE P.marginal hpY (entropyDefect P) ε hε
  apply hraw.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply congrArg (P.marginal.iid n).event
  ext y
  simp only [Set.mem_ofPred_eq]
  rw [entropyDefect_centered P hn y]

theorem typical_complement_small
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV2 : 0 < variance₂ P) :
    ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 < K ∧
      ∀ᶠ n in atTop,
        (P.marginal.iid n).event {y | ¬IsTypical P K y} < δ := by
  intro δ hδ
  obtain ⟨K, hK, hcenter⟩ :=
    center_tightInProbability hBE P hpY (δ / 3) (by linarith)
  have hvarLim := conditionalVariance_weakLaw hBE P hpY
    (variance₂ P / 2) (by linarith)
  have hvar : ∀ᶠ n in atTop,
      (P.marginal.iid n).event
        {y | variance₂ P / 2 ≤
          |conditionalVariance P y / (n : ℝ) - variance₂ P|} < δ / 3 :=
    (tendsto_order.1 hvarLim).2 _ (by linarith)
  have hD0 : 0 < meanEntropyDefect P := meanEntropyDefect_pos P hpY hV2
  have hdefLim := entropyDefect_weakLaw hBE P hpY
    (meanEntropyDefect P / 2) (by linarith)
  have hdef : ∀ᶠ n in atTop,
      (P.marginal.iid n).event
        {y | meanEntropyDefect P / 2 ≤
          |(∑ i, entropyDefect P (y i)) / (n : ℝ) - meanEntropyDefect P|} <
        δ / 3 := (tendsto_order.1 hdefLim).2 _ (by linarith)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcenter, hvar, hdef] with n hc hv hd
  have hfirst := finProb_event_le_add (P.marginal.iid n)
    {y | ¬IsTypical P K y}
    {y | K ≤ |center P y|}
    {y | variance₂ P / 2 ≤
        |conditionalVariance P y / (n : ℝ) - variance₂ P| ∨
      meanEntropyDefect P / 2 ≤
        |(∑ i, entropyDefect P (y i)) / (n : ℝ) - meanEntropyDefect P|}
    (fun y hy ↦ by
      by_cases hcen : |center P y| ≤ K
      · by_cases hvariance :
          |conditionalVariance P y / (n : ℝ) - variance₂ P| ≤ variance₂ P / 2
        · have hdefect : ¬|(∑ i, entropyDefect P (y i)) / (n : ℝ) -
              meanEntropyDefect P| ≤ meanEntropyDefect P / 2 := by
            intro hdgood
            exact hy ⟨hcen, hvariance, hdgood⟩
          exact Or.inr (Or.inr (le_of_lt (lt_of_not_ge hdefect)))
        · exact Or.inr (Or.inl (le_of_lt (lt_of_not_ge hvariance)))
      · exact Or.inl (le_of_lt (lt_of_not_ge hcen)))
  have hsecond := finProb_event_le_add (P.marginal.iid n)
    {y | variance₂ P / 2 ≤
        |conditionalVariance P y / (n : ℝ) - variance₂ P| ∨
      meanEntropyDefect P / 2 ≤
        |(∑ i, entropyDefect P (y i)) / (n : ℝ) - meanEntropyDefect P|}
    {y | variance₂ P / 2 ≤
        |conditionalVariance P y / (n : ℝ) - variance₂ P|}
    {y | meanEntropyDefect P / 2 ≤
        |(∑ i, entropyDefect P (y i)) / (n : ℝ) - meanEntropyDefect P|}
    (fun _ hy ↦ hy)
  linarith

noncomputable def conditionalCappedError (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (n : ℕ) (x : ℝ) : ℝ :=
  (P.marginal.iid n).expect fun y ↦
    |fiberScaledCappedValue f P y x 1 - f (supportTail P y x)|

theorem fiberCappedError_nonneg (f : AdmissibleGenerator)
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) (x : ℝ) :
    0 ≤ |fiberScaledCappedValue f P y x 1 - f (supportTail P y x)| :=
  abs_nonneg _

theorem fiberCappedError_le (f : AdmissibleGenerator)
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) (x : ℝ) :
    |fiberScaledCappedValue f P y x 1 - f (supportTail P y x)| ≤ 2 * f 0 := by
  have hg := TailLimit.scaled_bounds f 1 ((2 : ℝ) ^ (-threshold P n x))
    (by norm_num) (Real.rpow_nonneg (by norm_num) _) (fiberSupportLaw P y)
  have hq0 : 0 ≤ supportTail P y x := TailLimit.tailGE_nonneg _ _
  have hq1 : supportTail P y x ≤ 1 := TailLimit.tailGE_le_one _ _
  have hfq0 : 0 ≤ f (supportTail P y x) := f.nonneg_of_mem_unit hq0 hq1
  have hfqUpper : f (supportTail P y x) ≤ f 0 :=
    f.antitoneOn_nonneg (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hq0) hq0
  have hf0 := f.map_zero_nonneg
  have hg0 : 0 ≤ scaledCappedValue f 1 ((2 : ℝ) ^ (-threshold P n x))
      (fiberSupportLaw P y) := by simpa using hg.1
  rw [abs_le]
  constructor <;> dsimp [fiberScaledCappedValue] at hg ⊢ <;> linarith

theorem expect_le_local_add_bad
    (p : FinProb X) (u : X → ℝ) (G : Set X) (e C : ℝ)
    (hu : ∀ z, 0 ≤ u z) (hgood : ∀ z, z ∈ G → u z ≤ e)
    (hglobal : ∀ z, u z ≤ C) (he : 0 ≤ e) (hC : 0 ≤ C) :
    p.expect u ≤ e + C * p.event Gᶜ := by
  calc
    p.expect u ≤ p.expect (fun z ↦ e + C * if z ∈ Gᶜ then 1 else 0) := by
      apply p.expect_mono
      intro z
      by_cases hz : z ∈ G
      · simp [hz, hgood z hz]
      · have hzc : z ∈ Gᶜ := hz
        simp [hzc]
        linarith [hglobal z]
    _ = e + C * p.event Gᶜ := by
      classical
      simp only [FinProb.expect, FinProb.event, Finset.sum_filter,
        mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, p.sum_prob, one_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ Gᶜ <;> simp [hz, mul_comm]

theorem conditionalCappedError_tendsto_zero
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : 0 < variance₂ P) (x : ℝ) :
    Tendsto (fun n ↦ conditionalCappedError f P n x) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le
      ((P.marginal.iid n).expect_nonneg fun y ↦ fiberCappedError_nonneg f P y x)
  · intro ε hε
    by_cases hf0 : f 0 = 0
    · have hzero : ∀ n, conditionalCappedError f P n x = 0 := by
        intro n
        apply le_antisymm
        · rw [conditionalCappedError]
          apply le_trans ((P.marginal.iid n).expect_mono
            (fun y ↦ fiberCappedError_le f P y x))
          simp [hf0]
        · exact (P.marginal.iid n).expect_nonneg fun y ↦
            fiberCappedError_nonneg f P y x
      filter_upwards [] with n
      rw [hzero n]
      exact hε
    · have hf0pos : 0 < f 0 := lt_of_le_of_ne f.map_zero_nonneg (Ne.symm hf0)
      obtain ⟨K, hK, htyp⟩ := typical_complement_small hBE P hpY hV2
        (ε / (8 * f 0)) (div_pos hε (mul_pos (by norm_num) hf0pos))
      have hunif := uniformTypicalScaledApproximation hBE f P hpY hV2 x hK
        (1 / 2) 2 (by norm_num) (by norm_num) (ε / 2) (by linarith)
      filter_upwards [htyp, hunif] with n hbad hgood
      rw [conditionalCappedError]
      have hbound := expect_le_local_add_bad (P.marginal.iid n)
        (fun y ↦ |fiberScaledCappedValue f P y x 1 - f (supportTail P y x)|)
        {y | IsTypical P K y} (ε / 2) (2 * f 0)
        (fun y ↦ fiberCappedError_nonneg f P y x)
        (fun y hy ↦ by
          simpa only [one_mul] using
            (hgood y hy 1 (by constructor <;> norm_num)).le)
        (fun y ↦ fiberCappedError_le f P y x) (by linarith)
        (mul_nonneg (by norm_num) f.map_zero_nonneg)
      have hcomp : (P.marginal.iid n).event {y | IsTypical P K y}ᶜ <
          ε / (8 * f 0) := by simpa only [compl_setOf] using hbad
      have hmul : 2 * f 0 * (P.marginal.iid n).event {y | IsTypical P K y}ᶜ <
          2 * f 0 * (ε / (8 * f 0)) :=
        mul_lt_mul_of_pos_left hcomp (mul_pos (by norm_num) hf0pos)
      have hcalc : 2 * f 0 * (ε / (8 * f 0)) = ε / 4 := by
        field_simp [hf0]
        ring
      rw [hcalc] at hmul
      exact hbound.trans_lt (by linarith)

/-- **Lemma 14 (uniform conditional scaled approximation).** -/
theorem paperLemma14
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV2 : 0 < variance₂ P) (x : ℝ) {K : ℝ} (hK : 0 < K) :
    UniformTypicalScaledApproximation f P x K ∧
      Tendsto (fun n ↦ conditionalCappedError f P n x) atTop (𝓝 0) := by
  exact ⟨uniformTypicalScaledApproximation hBE f P hpY hV2 x hK,
    conditionalCappedError_tendsto_zero hBE f P hpY hV2 x⟩

end ConditionalCapped

end RandomnessExtraction
