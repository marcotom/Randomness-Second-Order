import RandomnessExtraction.BerryEsseen
import RandomnessExtraction.TailLimit
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Conditional product asymptotics

This file contains the finite-product notation and the formal versions of
Lemmas 13, 14, and 16.  All random quantities are finite sums under explicit
probability vectors.
-/

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

namespace ConditionalLimit

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- Single-letter conditional surprisal. -/
noncomputable def information (P : FiniteSource X Y) (x : X) (y : Y) : ℝ :=
  -Real.logb 2 (P.conditional y x)

/-- `h(y)` in equation (68). -/
noncomputable def fiberEntropy (P : FiniteSource X Y) (y : Y) : ℝ :=
  (P.conditional y).expect (fun x ↦ information P x y)

/-- `v(y)` in equation (69). -/
noncomputable def fiberVariance (P : FiniteSource X Y) (y : Y) : ℝ :=
  (P.conditional y).expect (fun x ↦ (information P x y - fiberEntropy P y) ^ 2)

/-- `ρ(y)` in equation (70). -/
noncomputable def fiberThirdMoment (P : FiniteSource X Y) (y : Y) : ℝ :=
  (P.conditional y).expect (fun x ↦ |information P x y - fiberEntropy P y| ^ 3)

/-- Conditional entropy `H`. -/
noncomputable def entropy (P : FiniteSource X Y) : ℝ :=
  P.marginal.expect (fiberEntropy P)

/-- Across-fibre variance `V₁`. -/
noncomputable def variance₁ (P : FiniteSource X Y) : ℝ :=
  P.marginal.expect (fun y ↦ (fiberEntropy P y - entropy P) ^ 2)

/-- Average within-fibre varentropy `V₂`. -/
noncomputable def variance₂ (P : FiniteSource X Y) : ℝ :=
  P.marginal.expect (fiberVariance P)

/-- Total varentropy `V=V₁+V₂`. -/
noncomputable def totalVariance (P : FiniteSource X Y) : ℝ :=
  variance₁ P + variance₂ P

/-- Conditional product law on `Xⁿ` at a fixed `yⁿ`. -/
def conditionalProduct (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) : FinProb (Fin n → X) where
  prob x := ∏ i, P.conditional (y i) (x i)
  nonneg x := Finset.prod_nonneg fun i _ ↦ (P.conditional (y i)).nonneg (x i)
  sum_prob := by
    rw [← Fintype.prod_sum]
    simp [FinProb.sum_apply]

@[simp]
theorem conditionalProduct_apply (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x : Fin n → X) :
    conditionalProduct P y x = ∏ i, P.conditional (y i) (x i) := rfl

/-- Block conditional surprisal. -/
noncomputable def blockInformation (P : FiniteSource X Y) {n : ℕ}
    (x : Fin n → X) (y : Fin n → Y) : ℝ :=
  ∑ i, information P (x i) (y i)

/-- Conditional mean `μₙ(yⁿ)`. -/
noncomputable def conditionalMean (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) : ℝ := ∑ i, fiberEntropy P (y i)

/-- Conditional variance `σₙ²(yⁿ)`. -/
noncomputable def conditionalVariance (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) : ℝ := ∑ i, fiberVariance P (y i)

/-- The threshold `hₙ(x)=nH-√(nV)x`. -/
noncomputable def threshold (P : FiniteSource X Y) (n : ℕ) (x : ℝ) : ℝ :=
  n * entropy P - Real.sqrt (n * totalVariance P) * x

/-- The normalized random fibre centre `Zₙ`. -/
noncomputable def center (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) : ℝ :=
  (conditionalMean P y - n * entropy P) / Real.sqrt n

/-- Conditional tail `Qₙ(yⁿ;x)` in equation (71). -/
noncomputable def conditionalTail (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x : ℝ) : ℝ :=
  (conditionalProduct P y).event
    {z | threshold P n x ≤ blockInformation P z y}

/-- Convergence to zero in probability for variables on changing finite
spaces. -/
def TendstoInProbabilityZero
    (A : ℕ → Type*) [∀ n, Fintype (A n)]
    (law : ∀ n, FinProb (A n)) (Z : ∀ n, A n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n ↦ (law n).event {ω | ε ≤ |Z n ω|}) atTop (𝓝 0)

/-- CDF convergence to the centered Gaussian of variance `v`, including the
degenerate interpretation at `v=0`. -/
def TendstoGaussianCDF
    (A : ℕ → Type*) [∀ n, Fintype (A n)]
    (law : ∀ n, FinProb (A n)) (Z : ∀ n, A n → ℝ) (v : ℝ) : Prop :=
  ∀ t : ℝ, t ≠ 0 ∨ v ≠ 0 → Tendsto
    (fun n ↦ (law n).event {ω | Z n ω ≤ t}) atTop
      (𝓝 (if v = 0 then if 0 ≤ t then 1 else 0
        else gaussianCDF (t / Real.sqrt v)))

/-- Tightness for real random variables on changing finite spaces. -/
def TightInProbability
    (A : ℕ → Type*) [∀ n, Fintype (A n)]
    (law : ∀ n, FinProb (A n)) (Z : ∀ n, A n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
    ∀ᶠ n in atTop, (law n).event {ω | K ≤ |Z n ω|} < ε

theorem fiberVariance_nonneg (P : FiniteSource X Y) (y : Y) :
    0 ≤ fiberVariance P y :=
  (P.conditional y).expect_nonneg fun _ ↦ sq_nonneg _

theorem fiberThirdMoment_nonneg (P : FiniteSource X Y) (y : Y) :
    0 ≤ fiberThirdMoment P y :=
  (P.conditional y).expect_nonneg fun _ ↦ pow_nonneg (abs_nonneg _) _

theorem variance₁_nonneg (P : FiniteSource X Y) : 0 ≤ variance₁ P :=
  P.marginal.expect_nonneg fun _ ↦ sq_nonneg _

theorem variance₂_nonneg (P : FiniteSource X Y) : 0 ≤ variance₂ P :=
  P.marginal.expect_nonneg (fiberVariance_nonneg P)

theorem totalVariance_nonneg (P : FiniteSource X Y) : 0 ≤ totalVariance P :=
  add_nonneg (variance₁_nonneg P) (variance₂_nonneg P)

section FiniteLimitTools

variable {A : Type} [Fintype A]

noncomputable def centered (p : FinProb A) (g : A → ℝ) (a : A) : ℝ :=
  g a - p.expect g

theorem expect_centered (p : FinProb A) (g : A → ℝ) :
    p.expect (centered p g) = 0 := by
  rw [FinProb.expect]
  simp_rw [centered, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, p.sum_prob, one_mul]
  simp [FinProb.expect]

theorem expect_neg_centered (p : FinProb A) (g : A → ℝ) :
    p.expect (fun a ↦ -centered p g a) = 0 := by
  rw [FinProb.expect]
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  change -p.expect (centered p g) = 0
  rw [expect_centered]
  simp

noncomputable def finiteVariance (p : FinProb A) (g : A → ℝ) : ℝ :=
  p.expect (fun a ↦ (centered p g a) ^ 2)

noncomputable def finiteThirdMoment (p : FinProb A) (g : A → ℝ) : ℝ :=
  p.expect (fun a ↦ |centered p g a| ^ 3)

theorem finiteVariance_nonneg (p : FinProb A) (g : A → ℝ) :
    0 ≤ finiteVariance p g := p.expect_nonneg fun _ ↦ sq_nonneg _

theorem finiteThirdMoment_nonneg (p : FinProb A) (g : A → ℝ) :
    0 ≤ finiteThirdMoment p g :=
  p.expect_nonneg fun _ ↦ pow_nonneg (abs_nonneg _) _

theorem centered_eq_zero_of_finiteVariance_eq_zero
    (p : FinProb A) (hp : ∀ a, 0 < p a) (g : A → ℝ)
    (hv : finiteVariance p g = 0) : ∀ a, centered p g a = 0 := by
  intro a
  have hterm : p a * (centered p g a) ^ 2 ≤ 0 := by
    calc
      p a * (centered p g a) ^ 2 ≤
          ∑ z, p z * (centered p g z) ^ 2 :=
        Finset.single_le_sum
          (fun z _ ↦ mul_nonneg (p.nonneg z) (sq_nonneg _)) (Finset.mem_univ a)
      _ = 0 := by simpa [finiteVariance, FinProb.expect] using hv
  have hprod : p a * (centered p g a) ^ 2 = 0 :=
    le_antisymm hterm (mul_nonneg (p.nonneg a) (sq_nonneg _))
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod).resolve_left (hp a).ne')

private theorem iid_normalized_event_eq (p : FinProb A) (g : A → ℝ)
    (n : ℕ) (hn : 0 < n) (v t : ℝ) (hv : 0 < v) :
    (p.iid n).event
        {ω | -(t / Real.sqrt v) ≤
          (∑ i, -centered p g (ω i)) / Real.sqrt ((n : ℝ) * v)} =
      (p.iid n).event
        {ω | (∑ i, centered p g (ω i)) / Real.sqrt n ≤ t} := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hsmul : Real.sqrt ((n : ℝ) * v) =
      Real.sqrt n * Real.sqrt v := Real.sqrt_mul hnR.le v
  apply Finset.sum_congr
  · ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rw [hsmul, Finset.sum_neg_distrib]
    constructor <;> intro hh
    · field_simp [hsn.ne', hsv.ne'] at hh ⊢
      linarith
    · field_simp [hsn.ne', hsv.ne'] at hh ⊢
      linarith
  · intro ω _
    rfl

/-- The ordinary finite-i.i.d. CLT, derived from Fact 12 with its explicit
Berry--Esseen remainder. -/
theorem iid_centered_cdf_tendsto
    (hBE : paperFact12.{0}) (p : FinProb A) (g : A → ℝ)
    (hv : 0 < finiteVariance p g) (t : ℝ) :
    Tendsto (fun n ↦ (p.iid n).event
      {ω | (∑ i, centered p g (ω i)) / Real.sqrt n ≤ t})
      atTop (𝓝 (gaussianCDF (t / Real.sqrt (finiteVariance p g)))) := by
  let v := finiteVariance p g
  let ρ := finiteThirdMoment p g
  let R : ℕ → ℝ := fun n ↦ berryEsseenConstant hBE * ((n : ℝ) * ρ) /
    (Real.sqrt ((n : ℝ) * v)) ^ 3
  have hR : Tendsto R atTop (𝓝 0) :=
    berryEsseen_iid_rate_tendsto_zero hBE ρ v hv
  have hbound : ∀ᶠ n in atTop,
      |(p.iid n).event {ω | (∑ i, centered p g (ω i)) / Real.sqrt n ≤ t} -
        gaussianCDF (t / Real.sqrt v)| ≤ R n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hvarEq : p.expect (fun a ↦ (-centered p g a) ^ 2) = v := by
      simp [v, finiteVariance]
    have hrhoEq : p.expect (fun a ↦ |-centered p g a| ^ 3) = ρ := by
      simp [ρ, finiteThirdMoment]
    have hvarNeg : 0 < p.expect (fun a ↦ (-centered p g a) ^ 2) := by
      rw [hvarEq]
      exact hv
    have hBEbound := iid_berryEsseen (A := A) hBE p (fun a ↦ -centered p g a)
      (expect_neg_centered p g) n hn hvarNeg (t / Real.sqrt v)
    rw [hvarEq, hrhoEq] at hBEbound
    rw [iid_normalized_event_eq p g n hn v t hv] at hBEbound
    exact hBEbound
  have habs : Tendsto (fun n ↦
      |(p.iid n).event {ω | (∑ i, centered p g (ω i)) / Real.sqrt n ≤ t} -
        gaussianCDF (t / Real.sqrt v)|) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · exact hbound
    · exact hR
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa [Real.norm_eq_abs, v] using habs

theorem finProb_event_le_add {B : Type*} [Fintype B]
    (p : FinProb B) (E F G : Set B)
    (hEFG : ∀ x, x ∈ E → x ∈ F ∨ x ∈ G) :
    p.event E ≤ p.event F + p.event G := by
  simpa [FinProb.event, TailLimit.eventProbability] using
    TailLimit.eventProbability_le_add p
      (fun x ↦ x ∈ E) (fun x ↦ x ∈ F) (fun x ↦ x ∈ G) hEFG

theorem finProb_event_mono {B : Type*} [Fintype B]
    (p : FinProb B) (E F : Set B) (hEF : ∀ x, x ∈ E → x ∈ F) :
    p.event E ≤ p.event F := by
  simpa [FinProb.event, TailLimit.eventProbability] using
    TailLimit.eventProbability_mono p (fun x ↦ x ∈ E) (fun x ↦ x ∈ F) hEF

theorem finProb_event_compl {B : Type*} [Fintype B]
    (p : FinProb B) (E : Set B) : p.event Eᶜ = 1 - p.event E := by
  classical
  have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x : B ↦ x ∈ E) p
  have : p.event E + p.event Eᶜ = 1 := by
    simpa [FinProb.event] using hsum.trans p.sum_prob
  linarith

theorem tendstoInProbabilityZero_continuousAt
    {B : ℕ → Type*} [∀ n, Fintype (B n)]
    (law : ∀ n, FinProb (B n)) (Z : ∀ n, B n → ℝ)
    (z₀ : ℝ) (g : ℝ → ℝ)
    (hZ : TendstoInProbabilityZero B law (fun n ω ↦ Z n ω - z₀))
    (hg : ContinuousAt g z₀) :
    TendstoInProbabilityZero B law (fun n ω ↦ g (Z n ω) - g z₀) := by
  intro ε hε
  obtain ⟨δ, hδ, hmap⟩ := (Metric.continuousAt_iff.1 hg) ε hε
  have hbase := hZ δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbase
  · exact Eventually.of_forall fun n ↦ (law n).event_nonneg _
  · exact Eventually.of_forall fun n ↦ finProb_event_mono (law n) _ _ fun ω hω ↦ by
      by_contra hnot
      have hsmall : |Z n ω - z₀| < δ := lt_of_not_ge hnot
      have hgsmall : |g (Z n ω) - g z₀| < ε := by
        simpa only [Real.dist_eq] using hmap (by simpa only [Real.dist_eq] using hsmall)
      exact (not_le_of_gt hgsmall hω)

theorem tendstoInProbabilityZero_uniformContinuous_sub
    {B : ℕ → Type*} [∀ n, Fintype (B n)]
    (law : ∀ n, FinProb (B n)) (U V : ∀ n, B n → ℝ)
    (g : ℝ → ℝ)
    (hUV : TendstoInProbabilityZero B law (fun n ω ↦ U n ω - V n ω))
    (hg : UniformContinuous g) :
    TendstoInProbabilityZero B law
      (fun n ω ↦ g (U n ω) - g (V n ω)) := by
  intro ε hε
  obtain ⟨δ, hδ, hmap⟩ := (Metric.uniformContinuous_iff.1 hg) ε hε
  have hbase := hUV δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbase
  · exact Eventually.of_forall fun n ↦ (law n).event_nonneg _
  · exact Eventually.of_forall fun n ↦ finProb_event_mono (law n) _ _ fun ω hω ↦ by
      by_contra hnot
      have hsmall : |U n ω - V n ω| < δ := lt_of_not_ge hnot
      have hgsmall : |g (U n ω) - g (V n ω)| < ε := by
        simpa only [Real.dist_eq] using hmap (by simpa only [Real.dist_eq] using hsmall)
      exact (not_le_of_gt hgsmall hω)

theorem tendstoInProbabilityZero_add
    {B : ℕ → Type*} [∀ n, Fintype (B n)]
    (law : ∀ n, FinProb (B n)) (U V : ∀ n, B n → ℝ)
    (hU : TendstoInProbabilityZero B law U)
    (hV : TendstoInProbabilityZero B law V) :
    TendstoInProbabilityZero B law (fun n ω ↦ U n ω + V n ω) := by
  intro ε hε
  have hU₂ := hU (ε / 2) (by linarith)
  have hV₂ := hV (ε / 2) (by linarith)
  have hsum : Tendsto (fun n ↦
      (law n).event {ω | ε / 2 ≤ |U n ω|} +
        (law n).event {ω | ε / 2 ≤ |V n ω|}) atTop (nhds 0) := by
    convert hU₂.add hV₂ using 1 <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall fun n ↦ (law n).event_nonneg _
  · exact Eventually.of_forall fun n ↦ finProb_event_le_add (law n) _ _ _ fun ω hω ↦ by
      simp only [Set.mem_setOf_eq, not_le] at hω ⊢
      by_contra hnot
      push_neg at hnot
      have htri := abs_add_le (U n ω) (V n ω)
      linarith

theorem tightInProbability_const_add
    {B : ℕ → Type*} [∀ n, Fintype (B n)]
    (law : ∀ n, FinProb (B n)) (Z : ∀ n, B n → ℝ)
    (c : ℝ) (hZ : TightInProbability B law Z) :
    TightInProbability B law (fun n ω ↦ c + Z n ω) := by
  intro ε hε
  obtain ⟨K, hK, htail⟩ := hZ ε hε
  refine ⟨K + |c|, by positivity, ?_⟩
  filter_upwards [htail] with n hn
  exact lt_of_le_of_lt (finProb_event_mono (law n) _ _ fun ω hω ↦ by
    simp only [Set.mem_setOf_eq, not_le] at hω ⊢
    by_contra hnot
    have hz : |Z n ω| < K := lt_of_not_ge hnot
    have htri := abs_add_le c (Z n ω)
    linarith) hn

theorem tendstoInProbabilityZero_mul_tight
    {B : ℕ → Type*} [∀ n, Fintype (B n)]
    (law : ∀ n, FinProb (B n)) (U V : ∀ n, B n → ℝ)
    (hU : TendstoInProbabilityZero B law U)
    (hV : TightInProbability B law V) :
    TendstoInProbabilityZero B law (fun n ω ↦ U n ω * V n ω) := by
  intro ε hε
  refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun n ↦
    ha.trans_le ((law n).event_nonneg _), ?_⟩
  intro a ha
  obtain ⟨K, hK, hVtail⟩ := hV (a / 2) (by linarith)
  have hUsmall : ∀ᶠ n in atTop, (law n).event {ω | ε / K ≤ |U n ω|} < a / 2 :=
    (tendsto_order.1 (hU (ε / K) (div_pos hε hK))).2 _ (by linarith)
  filter_upwards [hUsmall, hVtail] with n hnU hnV
  have hbound := finProb_event_le_add (law n)
    {ω | ε ≤ |U n ω * V n ω|}
    {ω | ε / K ≤ |U n ω|} {ω | K ≤ |V n ω|} fun ω hω ↦ by
      simp only [Set.mem_setOf_eq, not_le] at hω ⊢
      by_contra hnot
      push_neg at hnot
      rw [abs_mul] at hω
      have : |U n ω| * |V n ω| < ε := by
        calc
          |U n ω| * |V n ω| ≤ (ε / K) * |V n ω| :=
            mul_le_mul_of_nonneg_right hnot.1.le (abs_nonneg _)
          _ < (ε / K) * K :=
            mul_lt_mul_of_pos_left hnot.2 (div_pos hε hK)
          _ = ε := by field_simp [hK.ne']
      exact (not_lt_of_ge hω this)
  linarith

theorem centered_neg (p : FinProb A) (g : A → ℝ) (a : A) :
    centered p (fun z ↦ -g z) a = -centered p g a := by
  dsimp [centered]
  have hneg : p.expect (fun z ↦ -g z) = -p.expect g := by
    rw [FinProb.expect, FinProb.expect]
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
  rw [hneg]
  ring

theorem finiteVariance_neg (p : FinProb A) (g : A → ℝ) :
    finiteVariance p (fun z ↦ -g z) = finiteVariance p g := by
  apply Finset.sum_congr rfl
  intro a _
  dsimp [finiteVariance, FinProb.expect]
  rw [centered_neg]
  ring

/-- Weak law of large numbers for a finite i.i.d. law, proved from the same
Berry--Esseen input. -/
theorem iid_weakLaw
    (hBE : paperFact12.{0}) (p : FinProb A) (hp : ∀ a, 0 < p a) (g : A → ℝ) :
    TendstoInProbabilityZero (fun n ↦ Fin n → A) (fun n ↦ p.iid n)
      (fun n ω ↦ (∑ i, centered p g (ω i)) / n) := by
  intro ε hε
  let v := finiteVariance p g
  by_cases hv0 : v = 0
  · have hpoint : ∀ a, centered p g a = 0 := by
      intro a
      have hsum : p.expect (fun z ↦ (centered p g z) ^ 2) = 0 := by
        simpa [v, finiteVariance] using hv0
      have hterm : p a * (centered p g a) ^ 2 ≤ 0 := by
        calc
          p a * (centered p g a) ^ 2 ≤
              ∑ z, p z * (centered p g z) ^ 2 :=
            Finset.single_le_sum
              (fun z _ ↦ mul_nonneg (p.nonneg z) (sq_nonneg _)) (Finset.mem_univ a)
          _ = 0 := by simpa [FinProb.expect] using hsum
      have hprod : p a * (centered p g a) ^ 2 = 0 :=
        le_antisymm hterm (mul_nonneg (p.nonneg a) (sq_nonneg _))
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod).resolve_left (hp a).ne')
    have hzero : ∀ (n : ℕ) (ω : Fin n → A),
        (∑ i, centered p g (ω i)) / (n : ℝ) = 0 := by
      intro n ω
      simp [hpoint]
    have hevent : ∀ n,
        ((p.iid n).event {ω | ε ≤ |(∑ i, centered p g (ω i)) / (n : ℝ)|}) = 0 := by
      intro n
      rw [FinProb.event]
      apply Finset.sum_eq_zero
      intro ω hω
      have hbad : ε ≤ |(∑ i, centered p g (ω i)) / (n : ℝ)| := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
          using hω
      rw [hzero n ω, abs_zero] at hbad
      exact (not_le_of_gt hε hbad).elim
    simp_rw [hevent]
    exact tendsto_const_nhds
  · have hv : 0 < v := lt_of_le_of_ne (finiteVariance_nonneg p g) (Ne.symm hv0)
    have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
    have hcdf : Tendsto gaussianCDF atBot (𝓝 0) := by
      exact ProbabilityTheory.tendsto_cdf_atBot (ProbabilityTheory.gaussianReal 0 1)
    have hcdfSmall : ∀ᶠ z in atBot, gaussianCDF z < ε / 8 :=
      (tendsto_order.1 hcdf).2 (ε / 8) (by linarith)
    obtain ⟨z0, hz0⟩ := eventually_atBot.1 hcdfSmall
    let K : ℝ := max 1 (-z0 * Real.sqrt v)
    have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
    have harg : -K / Real.sqrt v ≤ z0 := by
      have hmax : -z0 * Real.sqrt v ≤ K := le_max_right _ _
      rw [div_le_iff₀ hsv]
      nlinarith
    have hPhi : gaussianCDF (-K / Real.sqrt v) < ε / 8 := hz0 _ harg
    have hCLTpos := iid_centered_cdf_tendsto hBE p g hv (-K)
    have hCLTnegRaw := iid_centered_cdf_tendsto hBE p (fun a ↦ -g a)
      (by simpa [finiteVariance_neg, v] using hv) (-K)
    have hCLTneg : Tendsto (fun n ↦ (p.iid n).event
        {ω | (∑ i, -centered p g (ω i)) / Real.sqrt n ≤ -K})
        atTop (𝓝 (gaussianCDF (-K / Real.sqrt v))) := by
      convert hCLTnegRaw using 1
      · ext n
        apply congrArg
        ext ω
        simp_rw [centered_neg]
      · rw [finiteVariance_neg]
    have hposSmall : ∀ᶠ n in atTop,
        (p.iid n).event {ω | (∑ i, centered p g (ω i)) / Real.sqrt n ≤ -K} < ε / 4 :=
      (tendsto_order.1 hCLTpos).2 _ (by linarith)
    have hnegSmall : ∀ᶠ n in atTop,
        (p.iid n).event {ω | (∑ i, -centered p g (ω i)) / Real.sqrt n ≤ -K} < ε / 4 :=
      (tendsto_order.1 hCLTneg).2 _ (by linarith)
    have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hlarge : ∀ᶠ n : ℕ in atTop, K / ε ≤ Real.sqrt (n : ℝ) :=
      (tendsto_atTop.1 hsqrt) (K / ε)
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact Eventually.of_forall fun n ↦ ha.trans_le ((p.iid n).event_nonneg _)
    · intro a ha
      have hcdfSmallA : ∀ᶠ z in atBot, gaussianCDF z < a / 8 :=
        (tendsto_order.1 hcdf).2 (a / 8) (by linarith)
      obtain ⟨zA, hzA⟩ := eventually_atBot.1 hcdfSmallA
      let KA : ℝ := max 1 (-zA * Real.sqrt v)
      have hargA : -KA / Real.sqrt v ≤ zA := by
        have hmaxA : -zA * Real.sqrt v ≤ KA := le_max_right _ _
        rw [div_le_iff₀ hsv]
        nlinarith
      have hPhiA : gaussianCDF (-KA / Real.sqrt v) < a / 8 := hzA _ hargA
      have hCLTposA := iid_centered_cdf_tendsto hBE p g hv (-KA)
      have hCLTnegRawA := iid_centered_cdf_tendsto hBE p (fun b ↦ -g b)
        (by simpa [finiteVariance_neg, v] using hv) (-KA)
      have hCLTnegA : Tendsto (fun n ↦ (p.iid n).event
          {ω | (∑ i, -centered p g (ω i)) / Real.sqrt n ≤ -KA})
          atTop (nhds (gaussianCDF (-KA / Real.sqrt v))) := by
        convert hCLTnegRawA using 1
        · ext n
          apply congrArg
          ext ω
          simp_rw [centered_neg]
        · rw [finiteVariance_neg]
      have hposSmallA : ∀ᶠ n in atTop,
          (p.iid n).event
            {ω | (∑ i, centered p g (ω i)) / Real.sqrt n ≤ -KA} < a / 4 :=
        (tendsto_order.1 hCLTposA).2 _ (by linarith)
      have hnegSmallA : ∀ᶠ n in atTop,
          (p.iid n).event
            {ω | (∑ i, -centered p g (ω i)) / Real.sqrt n ≤ -KA} < a / 4 :=
        (tendsto_order.1 hCLTnegA).2 _ (by linarith)
      have hlargeA : ∀ᶠ n : ℕ in atTop, KA / ε ≤ Real.sqrt (n : ℝ) :=
        (tendsto_atTop.1 hsqrt) (KA / ε)
      filter_upwards [eventually_gt_atTop 0, hposSmallA, hnegSmallA, hlargeA] with
        n hn hpos hneg hnlarge
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
      have hsquare : (Real.sqrt (n : ℝ)) ^ 2 = n := by simpa using Real.sq_sqrt hnR.le
      have hKE : KA ≤ ε * Real.sqrt n := by
        rw [div_le_iff₀ hε] at hnlarge
        linarith
      have hsubset : ∀ (ω : Fin n → A),
          ε ≤ |(∑ i, centered p g (ω i)) / (n : ℝ)| →
          (∑ i, centered p g (ω i)) / Real.sqrt n ≤ -KA ∨
            (∑ i, -centered p g (ω i)) / Real.sqrt n ≤ -KA := by
        intro ω hω
        let S := ∑ i, centered p g (ω i)
        have hscaled : KA ≤ |S / Real.sqrt n| := by
          rw [abs_div, abs_of_pos hsn]
          rw [abs_div, abs_of_pos hnR] at hω
          have hmul := mul_le_mul_of_nonneg_right hω hsn.le
          have hrewrite : |S| / (n : ℝ) * Real.sqrt n = |S| / Real.sqrt n := by
            field_simp [hsn.ne', hnR.ne']
            rw [hsquare]
          rw [hrewrite] at hmul
          exact hKE.trans hmul
        rcases (le_abs.mp hscaled) with hright | hleft
        · right
          rw [Finset.sum_neg_distrib]
          field_simp [hsn.ne'] at hright ⊢
          linarith
        · left
          dsimp [S] at hleft
          linarith
      have hprob := finProb_event_le_add (p.iid n)
        {ω | ε ≤ |(∑ i, centered p g (ω i)) / (n : ℝ)|}
        {ω | (∑ i, centered p g (ω i)) / Real.sqrt n ≤ -KA}
        {ω | (∑ i, -centered p g (ω i)) / Real.sqrt n ≤ -KA} hsubset
      have heps : (p.iid n).event
          {ω | ε ≤ |(∑ i, centered p g (ω i)) / (n : ℝ)|} < a / 2 := by
        linarith
      exact heps.trans (by linarith)

theorem finiteVariance_fiberEntropy (P : FiniteSource X Y) :
    finiteVariance P.marginal (fiberEntropy P) = variance₁ P := rfl

theorem finiteVariance_fiberVariance (P : FiniteSource X Y) :
    finiteVariance P.marginal (fiberVariance P) =
      P.marginal.expect
        (fun y ↦ (fiberVariance P y - variance₂ P) ^ 2) := rfl

theorem center_eq_centered_sum (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) :
    center P y = (∑ i, centered P.marginal (fiberEntropy P) (y i)) /
      Real.sqrt n := by
  simp only [center, conditionalMean, centered, entropy]
  rw [Finset.sum_sub_distrib]
  simp

theorem conditionalVariance_centered (P : FiniteSource X Y) {n : ℕ}
    (hn : 0 < n) (y : Fin n → Y) :
    conditionalVariance P y / (n : ℝ) - variance₂ P =
      (∑ i, centered P.marginal (fiberVariance P) (y i)) / (n : ℝ) := by
  simp only [conditionalVariance, centered, variance₂]
  rw [Finset.sum_sub_distrib]
  simp
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

/-- The conditional variance law of large numbers used in Lemma 13. -/
theorem conditionalVariance_weakLaw
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) :
    TendstoInProbabilityZero (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
      (fun n y ↦ conditionalVariance P y / (n : ℝ) - variance₂ P) := by
  intro ε hε
  have hraw := iid_weakLaw hBE P.marginal hpY (fiberVariance P) ε hε
  apply hraw.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply congrArg (P.marginal.iid n).event
  ext y
  simp only [Set.mem_setOf_eq]
  rw [conditionalVariance_centered P hn y]

/-- The outer ordinary CLT for the random conditional mean, including its
degenerate `V₁=0` interpretation. -/
theorem center_tendstoGaussianCDF
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) :
    TendstoGaussianCDF (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
      (fun _ y ↦ center P y) (variance₁ P) := by
  intro t ht
  by_cases hv0 : variance₁ P = 0
  · have hpoint : ∀ y, centered P.marginal (fiberEntropy P) y = 0 :=
      centered_eq_zero_of_finiteVariance_eq_zero P.marginal hpY (fiberEntropy P)
        (by simpa only [finiteVariance_fiberEntropy] using hv0)
    have hcenter : ∀ (n : ℕ) (y : Fin n → Y), center P y = 0 := by
      intro n y
      rw [center_eq_centered_sum]
      simp [hpoint]
    have ht0 : t ≠ 0 := by
      rcases ht with ht | hv
      · exact ht
      · exact (hv hv0).elim
    by_cases htNonneg : 0 ≤ t
    · have htpos : 0 < t := lt_of_le_of_ne htNonneg (Ne.symm ht0)
      simp only [hv0, if_pos, if_pos htNonneg]
      have hevent : ∀ n, (P.marginal.iid n).event {y | center P y ≤ t} = 1 := by
        intro n
        simpa [FinProb.event, hcenter, htNonneg] using (P.marginal.iid n).sum_prob
      simp_rw [hevent]
      exact tendsto_const_nhds
    · have htneg : t < 0 := lt_of_not_ge htNonneg
      simp only [hv0, if_pos, if_neg htNonneg]
      have hevent : ∀ n, (P.marginal.iid n).event {y | center P y ≤ t} = 0 := by
        intro n
        simp [FinProb.event, hcenter, htNonneg]
      simp_rw [hevent]
      exact tendsto_const_nhds
  · have hv : 0 < variance₁ P :=
      lt_of_le_of_ne (variance₁_nonneg P) (Ne.symm hv0)
    have hclt := iid_centered_cdf_tendsto hBE P.marginal (fiberEntropy P)
      (by simpa only [finiteVariance_fiberEntropy] using hv) t
    simpa only [center_eq_centered_sum, finiteVariance_fiberEntropy, hv0, if_false]
      using hclt

/-- The outer conditional-mean fluctuation is tight. -/
theorem center_tightInProbability
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) :
    TightInProbability (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
      (fun _ y ↦ center P y) := by
  intro ε hε
  by_cases hv0 : variance₁ P = 0
  · have hpoint : ∀ y, centered P.marginal (fiberEntropy P) y = 0 :=
      centered_eq_zero_of_finiteVariance_eq_zero P.marginal hpY (fiberEntropy P)
        (by simpa only [finiteVariance_fiberEntropy] using hv0)
    have hcenter : ∀ (n : ℕ) (y : Fin n → Y), center P y = 0 := by
      intro n y
      rw [center_eq_centered_sum]
      simp [hpoint]
    refine ⟨1, zero_lt_one, ?_⟩
    exact Eventually.of_forall fun n ↦ by
      have heq : (P.marginal.iid n).event {y | (1 : ℝ) ≤ |center P y|} = 0 := by
        rw [FinProb.event]
        apply Finset.sum_eq_zero
        intro y hy
        have hbad : (1 : ℝ) ≤ |center P y| := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
            using hy
        rw [hcenter n y, abs_zero] at hbad
        norm_num at hbad
      rw [heq]
      exact hε
  · have hv : 0 < variance₁ P :=
      lt_of_le_of_ne (variance₁_nonneg P) (Ne.symm hv0)
    have hsv : 0 < Real.sqrt (variance₁ P) := Real.sqrt_pos.2 hv
    have hbot : Tendsto gaussianCDF atBot (nhds 0) :=
      ProbabilityTheory.tendsto_cdf_atBot (ProbabilityTheory.gaussianReal 0 1)
    have htop : Tendsto gaussianCDF atTop (nhds 1) :=
      ProbabilityTheory.tendsto_cdf_atTop (ProbabilityTheory.gaussianReal 0 1)
    have hleftRaw : ∀ᶠ z in atBot, gaussianCDF z < ε / 8 :=
      (tendsto_order.1 hbot).2 _ (by linarith)
    have hrightRaw : ∀ᶠ z in atTop, 1 - ε / 8 < gaussianCDF z :=
      (tendsto_order.1 htop).1 _ (by linarith)
    obtain ⟨zL, hzL⟩ := eventually_atBot.1 hleftRaw
    obtain ⟨zR, hzR⟩ := eventually_atTop.1 hrightRaw
    let K : ℝ := max 1 (max (-zL * Real.sqrt (variance₁ P))
      (2 * zR * Real.sqrt (variance₁ P)))
    have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
    have hargL : -K / Real.sqrt (variance₁ P) ≤ zL := by
      have hh : -zL * Real.sqrt (variance₁ P) ≤ K :=
        (le_max_left _ _).trans (le_max_right _ _)
      rw [div_le_iff₀ hsv]
      nlinarith
    have hargR : zR ≤ (K / 2) / Real.sqrt (variance₁ P) := by
      have hh : 2 * zR * Real.sqrt (variance₁ P) ≤ K :=
        (le_max_right _ _).trans (le_max_right _ _)
      rw [le_div_iff₀ hsv]
      nlinarith
    have hPhiL : gaussianCDF (-K / Real.sqrt (variance₁ P)) < ε / 8 :=
      hzL _ hargL
    have hPhiR : 1 - ε / 8 < gaussianCDF ((K / 2) / Real.sqrt (variance₁ P)) :=
      hzR _ hargR
    have hclt := center_tendstoGaussianCDF hBE P hpY
    have hleftCLT := hclt (-K) (Or.inl (neg_ne_zero.mpr hK.ne'))
    have hrightCLT := hclt (K / 2) (Or.inl (div_ne_zero hK.ne' (by norm_num)))
    simp only [hv0, if_false] at hleftCLT hrightCLT
    have hleft : ∀ᶠ n in atTop,
        (P.marginal.iid n).event {y | center P y ≤ -K} < ε / 4 :=
      (tendsto_order.1 hleftCLT).2 _ (by linarith)
    have hright : ∀ᶠ n in atTop,
        1 - ε / 4 < (P.marginal.iid n).event {y | center P y ≤ K / 2} :=
      (tendsto_order.1 hrightCLT).1 _ (by linarith)
    refine ⟨K, hK, ?_⟩
    filter_upwards [hleft, hright] with n hnL hnR
    have hupper : (P.marginal.iid n).event {y | K ≤ center P y} < ε / 4 := by
      have hmono := finProb_event_mono (P.marginal.iid n)
        {y | K ≤ center P y} ({y | center P y ≤ K / 2}ᶜ) fun y hy ↦ by
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
          change K ≤ center P y at hy
          linarith
      rw [finProb_event_compl] at hmono
      linarith
    have hunion := finProb_event_le_add (P.marginal.iid n)
      {y | K ≤ |center P y|} {y | center P y ≤ -K}
      {y | K ≤ center P y} fun y hy ↦ by
        change K ≤ |center P y| at hy
        rcases le_abs.mp hy with hpos | hneg
        · right
          exact hpos
        · left
          change center P y ≤ -K
          linarith
    linarith

/-- The Gaussian argument with the empirical conditional variance retained. -/
noncomputable def empiricalGaussianArgument (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x : ℝ) : ℝ :=
  (conditionalMean P y - threshold P n x) /
    Real.sqrt (conditionalVariance P y)

/-- Algebraically normalized version of `empiricalGaussianArgument`. -/
noncomputable def normalizedEmpiricalGaussianArgument (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x : ℝ) : ℝ :=
  (x * Real.sqrt (totalVariance P) + center P y) /
    Real.sqrt (conditionalVariance P y / (n : ℝ))

/-- The deterministic-variance Gaussian argument in Lemma 13. -/
noncomputable def limitingGaussianArgument (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x : ℝ) : ℝ :=
  (x * Real.sqrt (totalVariance P) + center P y) / Real.sqrt (variance₂ P)

theorem empiricalGaussianArgument_eq_normalized (P : FiniteSource X Y)
    {n : ℕ} (hn : 0 < n) (y : Fin n → Y) (x : ℝ)
    (hσ : 0 < conditionalVariance P y) :
    empiricalGaussianArgument P y x = normalizedEmpiricalGaussianArgument P y x := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsquare : (Real.sqrt (n : ℝ)) ^ 2 = n := by
    simpa using Real.sq_sqrt hnR.le
  have hV : 0 ≤ totalVariance P := totalVariance_nonneg P
  have hsqrtNV : Real.sqrt ((n : ℝ) * totalVariance P) =
      Real.sqrt n * Real.sqrt (totalVariance P) := Real.sqrt_mul hnR.le _
  have hbar : 0 ≤ conditionalVariance P y / (n : ℝ) :=
    div_nonneg hσ.le hnR.le
  have hsqrtσ : Real.sqrt (conditionalVariance P y) =
      Real.sqrt n * Real.sqrt (conditionalVariance P y / (n : ℝ)) := by
    calc
      Real.sqrt (conditionalVariance P y) =
          Real.sqrt ((n : ℝ) * (conditionalVariance P y / (n : ℝ))) := by
            congr 1
            field_simp [hnR.ne']
      _ = Real.sqrt n * Real.sqrt (conditionalVariance P y / (n : ℝ)) :=
        Real.sqrt_mul hnR.le _
  have hnum : conditionalMean P y - threshold P n x =
      Real.sqrt n * (x * Real.sqrt (totalVariance P) + center P y) := by
    rw [threshold, center, hsqrtNV]
    field_simp [hsn.ne']
    ring
  have hsbar : 0 < Real.sqrt (conditionalVariance P y / (n : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hσ hnR)
  rw [empiricalGaussianArgument, normalizedEmpiricalGaussianArgument, hnum, hsqrtσ]
  field_simp [hsn.ne', hsbar.ne']

theorem centeredInformation_sum (P : FiniteSource X Y) {n : ℕ}
    (z : Fin n → X) (y : Fin n → Y) :
    (∑ i : Fin n, (information P (z i) (y i) - fiberEntropy P (y i))) =
      blockInformation P z y - conditionalMean P y := by
  simp only [blockInformation, conditionalMean]
  rw [Finset.sum_sub_distrib]

theorem conditional_secondMoment_sum (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) :
    (∑ i, (P.conditional (y i)).expect
      (fun z ↦ (information P z (y i) - fiberEntropy P (y i)) ^ 2)) =
      conditionalVariance P y := rfl

theorem conditional_thirdMoment_sum (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) :
    (∑ i, (P.conditional (y i)).expect
      (fun z ↦ |information P z (y i) - fiberEntropy P (y i)| ^ 3)) =
      ∑ i, fiberThirdMoment P (y i) := rfl

/-- The explicit conditional Berry--Esseen estimate appearing as equation
(73) in the proof of Lemma 13. -/
theorem conditionalTail_berryEsseen
    (hBE : paperFact12.{0}) (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (x : ℝ) (hσ : 0 < conditionalVariance P y) :
    |conditionalTail P y x - gaussianCDF (empiricalGaussianArgument P y x)| ≤
      berryEsseenConstant hBE * (∑ i, fiberThirdMoment P (y i)) /
        (Real.sqrt (conditionalVariance P y)) ^ 3 := by
  let W : ∀ _ : Fin n, X → ℝ :=
    fun i z ↦ information P z (y i) - fiberEntropy P (y i)
  have hW : ∀ i, (P.conditional (y i)).expect (W i) = 0 := by
    intro i
    rw [FinProb.expect]
    simp_rw [W, fiberEntropy, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
      (P.conditional (y i)).sum_prob, one_mul]
    change (P.conditional (y i)).expect (fun z ↦ information P z (y i)) -
      (P.conditional (y i)).expect (fun z ↦ information P z (y i)) = 0
    exact sub_self _
  have hraw := (Classical.choose_spec hBE).2 n (fun _ : Fin n ↦ X)
    (fun i ↦ P.conditional (y i)) W hW
  dsimp only at hraw
  have hineq := hraw (by simpa only [W, conditional_secondMoment_sum] using hσ)
    (empiricalGaussianArgument P y x)
  have hevent :
      finiteProductEventProbability (fun _ : Fin n ↦ X)
        (fun i ↦ P.conditional (y i))
        {z | -empiricalGaussianArgument P y x ≤
          (∑ i, W i (z i)) / Real.sqrt (conditionalVariance P y)} =
        conditionalTail P y x := by
    rw [finiteProductEventProbability, conditionalTail, FinProb.event]
    apply Finset.sum_congr
    · ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      rw [centeredInformation_sum]
      have hsqrt : 0 < Real.sqrt (conditionalVariance P y) := Real.sqrt_pos.2 hσ
      dsimp only [empiricalGaussianArgument]
      constructor <;> intro hz
      · field_simp [hsqrt.ne'] at hz
        linarith
      · field_simp [hsqrt.ne']
        linarith
    · intro z _
      rfl
  rw [show (∑ i, (P.conditional (y i)).expect (fun z ↦ (W i z) ^ 2)) =
      conditionalVariance P y by rfl] at hineq
  have hrho : (∑ i, (P.conditional (y i)).expect (fun z ↦ |W i z| ^ 3)) =
      ∑ i, fiberThirdMoment P (y i) := by
    rfl
  rw [hrho] at hineq
  rw [hevent] at hineq
  simpa only [abs_sub_comm, berryEsseenConstant] using hineq

/-- A finite uniform bound for the conditional third centered moments. -/
noncomputable def thirdMomentTotal (P : FiniteSource X Y) : ℝ :=
  ∑ y, fiberThirdMoment P y

theorem thirdMomentTotal_nonneg (P : FiniteSource X Y) :
    0 ≤ thirdMomentTotal P :=
  Finset.sum_nonneg fun y _ ↦ fiberThirdMoment_nonneg P y

theorem fiberThirdMoment_le_total (P : FiniteSource X Y) (y : Y) :
    fiberThirdMoment P y ≤ thirdMomentTotal P := by
  exact Finset.single_le_sum (fun z _ ↦ fiberThirdMoment_nonneg P z)
    (Finset.mem_univ y)

/-- Equation (73): on the event where the empirical conditional variance is
at least `V₂/2`, the conditional Berry--Esseen error has a deterministic
`O(n⁻¹/²)` upper bound. -/
theorem conditionalTail_berryEsseen_rate
    (hBE : paperFact12.{0}) (P : FiniteSource X Y) {n : ℕ}
    (hn : 0 < n) (y : Fin n → Y) (x : ℝ) (hV2 : 0 < variance₂ P)
    (hgood : variance₂ P / 2 ≤ conditionalVariance P y / (n : ℝ)) :
    |conditionalTail P y x - gaussianCDF (empiricalGaussianArgument P y x)| ≤
      berryEsseenConstant hBE * ((n : ℝ) * thirdMomentTotal P) /
        (Real.sqrt ((n : ℝ) * (variance₂ P / 2))) ^ 3 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbase : 0 < (n : ℝ) * (variance₂ P / 2) := mul_pos hnR (by linarith)
  have hσlower : (n : ℝ) * (variance₂ P / 2) ≤ conditionalVariance P y := by
    have hh := (le_div_iff₀ hnR).mp hgood
    nlinarith
  have hσ : 0 < conditionalVariance P y := hbase.trans_le hσlower
  have hraw := conditionalTail_berryEsseen hBE P y x hσ
  have hthird : (∑ i, fiberThirdMoment P (y i)) ≤
      (n : ℝ) * thirdMomentTotal P := by
    calc
      (∑ i, fiberThirdMoment P (y i)) ≤ ∑ _i : Fin n, thirdMomentTotal P :=
        Finset.sum_le_sum fun i _ ↦ fiberThirdMoment_le_total P (y i)
      _ = (n : ℝ) * thirdMomentTotal P := by simp
  have hnum : 0 ≤ berryEsseenConstant hBE *
      (∑ i, fiberThirdMoment P (y i)) :=
    mul_nonneg (berryEsseenConstant_nonneg hBE)
      (Finset.sum_nonneg fun i _ ↦ fiberThirdMoment_nonneg P (y i))
  have hnumle : berryEsseenConstant hBE *
      (∑ i, fiberThirdMoment P (y i)) ≤
      berryEsseenConstant hBE * ((n : ℝ) * thirdMomentTotal P) :=
    mul_le_mul_of_nonneg_left hthird (berryEsseenConstant_nonneg hBE)
  have hnumTarget : 0 ≤ berryEsseenConstant hBE *
      ((n : ℝ) * thirdMomentTotal P) :=
    mul_nonneg (berryEsseenConstant_nonneg hBE)
      (mul_nonneg hnR.le (thirdMomentTotal_nonneg P))
  have hsqrt : Real.sqrt ((n : ℝ) * (variance₂ P / 2)) ≤
      Real.sqrt (conditionalVariance P y) := Real.sqrt_le_sqrt hσlower
  have hden : (Real.sqrt ((n : ℝ) * (variance₂ P / 2))) ^ 3 ≤
      (Real.sqrt (conditionalVariance P y)) ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 3
  exact hraw.trans
    (div_le_div₀ hnumTarget hnumle (pow_pos (Real.sqrt_pos.2 hbase) 3) hden)

/-- The conditional tail is asymptotically equal in probability to the
Gaussian approximation with its empirical variance still present. -/
theorem conditionalTail_empiricalGaussian_tendsto
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV2 : 0 < variance₂ P) (x : ℝ) :
    TendstoInProbabilityZero (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
      (fun _ y ↦ conditionalTail P y x -
        gaussianCDF (empiricalGaussianArgument P y x)) := by
  intro ε hε
  let R : ℕ → ℝ := fun n ↦
    berryEsseenConstant hBE * ((n : ℝ) * thirdMomentTotal P) /
      (Real.sqrt ((n : ℝ) * (variance₂ P / 2))) ^ 3
  have hR : Tendsto R atTop (nhds 0) :=
    berryEsseen_iid_rate_tendsto_zero hBE (thirdMomentTotal P)
      (variance₂ P / 2) (by linarith)
  have hRsmall : ∀ᶠ n in atTop, R n < ε :=
    (tendsto_order.1 hR).2 ε hε
  have hbad := conditionalVariance_weakLaw hBE P hpY (variance₂ P / 2) (by linarith)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
  · exact Eventually.of_forall fun n ↦ (P.marginal.iid n).event_nonneg _
  · filter_upwards [eventually_gt_atTop 0, hRsmall] with n hn hRn
    apply TailLimit.eventProbability_mono
    intro y hy
    by_contra hnot
    have hgood : variance₂ P / 2 ≤ conditionalVariance P y / (n : ℝ) := by
      have habs : |conditionalVariance P y / (n : ℝ) - variance₂ P| <
          variance₂ P / 2 := lt_of_not_ge hnot
      linarith [abs_lt.mp habs |>.1]
    have hbound := conditionalTail_berryEsseen_rate hBE P hn y x hV2 hgood
    have herr : ε ≤
        |conditionalTail P y x - gaussianCDF (empiricalGaussianArgument P y x)| := hy
    exact (not_le_of_gt hRn (herr.trans hbound))

theorem inverseSqrtConditionalVariance_tendsto
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV2 : 0 < variance₂ P) :
    TendstoInProbabilityZero (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
      (fun n y ↦ (Real.sqrt (conditionalVariance P y / (n : ℝ)))⁻¹ -
        (Real.sqrt (variance₂ P))⁻¹) := by
  apply tendstoInProbabilityZero_continuousAt
    (fun n ↦ P.marginal.iid n)
    (fun n y ↦ conditionalVariance P y / (n : ℝ)) (variance₂ P)
    (fun r ↦ (Real.sqrt r)⁻¹)
  · exact conditionalVariance_weakLaw hBE P hpY
  · exact Real.continuous_sqrt.continuousAt.inv₀
      (Real.sqrt_ne_zero'.2 hV2)

theorem normalizedEmpiricalArgument_tendsto
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV2 : 0 < variance₂ P) (x : ℝ) :
    TendstoInProbabilityZero (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
      (fun _ y ↦ normalizedEmpiricalGaussianArgument P y x -
        limitingGaussianArgument P y x) := by
  have hinv := inverseSqrtConditionalVariance_tendsto hBE P hpY hV2
  have htight := tightInProbability_const_add (fun n ↦ P.marginal.iid n)
    (fun _ y ↦ center P y) (x * Real.sqrt (totalVariance P))
    (center_tightInProbability hBE P hpY)
  have hprod := tendstoInProbabilityZero_mul_tight (fun n ↦ P.marginal.iid n)
    (fun n y ↦ (Real.sqrt (conditionalVariance P y / (n : ℝ)))⁻¹ -
      (Real.sqrt (variance₂ P))⁻¹)
    (fun _ y ↦ x * Real.sqrt (totalVariance P) + center P y) hinv htight
  convert hprod using 1
  ext n y
  dsimp only [normalizedEmpiricalGaussianArgument, limitingGaussianArgument]
  ring

theorem empiricalArgument_eq_normalized_tendsto
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV2 : 0 < variance₂ P) (x : ℝ) :
    TendstoInProbabilityZero (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
      (fun _ y ↦ empiricalGaussianArgument P y x -
        normalizedEmpiricalGaussianArgument P y x) := by
  intro ε hε
  have hbad := conditionalVariance_weakLaw hBE P hpY (variance₂ P / 2) (by linarith)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
  · exact Eventually.of_forall fun n ↦ (P.marginal.iid n).event_nonneg _
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact finProb_event_mono (P.marginal.iid n) _ _ fun y hy ↦ by
      by_contra hnot
      have hgood : |conditionalVariance P y / (n : ℝ) - variance₂ P| <
          variance₂ P / 2 := lt_of_not_ge hnot
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hσ : 0 < conditionalVariance P y := by
        have : variance₂ P / 2 < conditionalVariance P y / (n : ℝ) := by
          linarith [abs_lt.mp hgood |>.1]
        have hratio : 0 < conditionalVariance P y / (n : ℝ) := by linarith
        rcases div_pos_iff.mp hratio with hpos | hneg
        · exact hpos.1
        · exact (not_lt_of_ge hnR.le hneg.2).elim
      change ε ≤ |empiricalGaussianArgument P y x -
        normalizedEmpiricalGaussianArgument P y x| at hy
      rw [empiricalGaussianArgument_eq_normalized P hn y x hσ, sub_self, abs_zero] at hy
      exact (not_le_of_gt hε hy)

theorem empiricalArgument_tendsto
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV2 : 0 < variance₂ P) (x : ℝ) :
    TendstoInProbabilityZero (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
      (fun _ y ↦ empiricalGaussianArgument P y x -
        limitingGaussianArgument P y x) := by
  have hadd := tendstoInProbabilityZero_add (fun n ↦ P.marginal.iid n)
    (fun _ y ↦ empiricalGaussianArgument P y x -
      normalizedEmpiricalGaussianArgument P y x)
    (fun _ y ↦ normalizedEmpiricalGaussianArgument P y x -
      limitingGaussianArgument P y x)
    (empiricalArgument_eq_normalized_tendsto hBE P hpY hV2 x)
    (normalizedEmpiricalArgument_tendsto hBE P hpY hV2 x)
  simpa only [sub_add_sub_cancel] using hadd

/-- **Lemma 13 (conditional CLT).** -/
theorem paperLemma13
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV2 : 0 < variance₂ P) (x : ℝ) :
    TendstoInProbabilityZero (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
        (fun _ y ↦ conditionalTail P y x -
          gaussianCDF (limitingGaussianArgument P y x)) ∧
      TendstoGaussianCDF (fun n ↦ Fin n → Y) (fun n ↦ P.marginal.iid n)
        (fun _ y ↦ center P y) (variance₁ P) := by
  constructor
  · have hBEpart := conditionalTail_empiricalGaussian_tendsto hBE P hpY hV2 x
    have hCDFpart := tendstoInProbabilityZero_uniformContinuous_sub
      (fun n ↦ P.marginal.iid n)
      (fun _ y ↦ empiricalGaussianArgument P y x)
      (fun _ y ↦ limitingGaussianArgument P y x) gaussianCDF
      (empiricalArgument_tendsto hBE P hpY hV2 x) uniformContinuous_gaussianCDF
    have hadd := tendstoInProbabilityZero_add (fun n ↦ P.marginal.iid n)
      (fun _ y ↦ conditionalTail P y x -
        gaussianCDF (empiricalGaussianArgument P y x))
      (fun _ y ↦ gaussianCDF (empiricalGaussianArgument P y x) -
        gaussianCDF (limitingGaussianArgument P y x)) hBEpart hCDFpart
    simpa only [sub_add_sub_cancel] using hadd
  · exact center_tendstoGaussianCDF hBE P hpY

end FiniteLimitTools

end ConditionalLimit

end RandomnessExtraction
