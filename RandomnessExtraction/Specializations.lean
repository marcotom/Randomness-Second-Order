import RandomnessExtraction.MainTheorem
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Rényi and total-variation generators
-/

open Filter Set MeasureTheory
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

open ConditionalLimit OneShot

/-- The power generator for order `α ∈ (0,1)`. -/
noncomputable def powerGenerator (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    AdmissibleGenerator where
  toFun t := (1 - t ^ α) / (1 - α)
  continuous :=
    (continuous_const.sub (Real.continuous_rpow_const hα0.le)).div_const _
  convexOn_nonneg := by
    have hc := Real.concaveOn_rpow hα0.le hα1.le
    refine ⟨hc.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hpow := hc.2 hx hy ha hb hab
    have hden : 0 < 1 - α := sub_pos.mpr hα1
    simp only [smul_eq_mul] at hpow ⊢
    change (1 - (a * x + b * y) ^ α) / (1 - α) ≤
      a * ((1 - x ^ α) / (1 - α)) + b * ((1 - y ^ α) / (1 - α))
    rw [div_le_iff₀ hden]
    field_simp [hden.ne']
    linarith
  map_one := by simp
  sublinear_atTop := by
    have hden : 1 - α ≠ 0 := (sub_pos.mpr hα1).ne'
    have hinv : Tendsto (fun t : ℝ ↦ ((1 - α) : ℝ)⁻¹ * t⁻¹)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (nhds 0))
    have hpow : Tendsto (fun t : ℝ ↦ ((1 - α) : ℝ)⁻¹ * t ^ (α - 1))
        atTop (nhds 0) := by
      have hr : Tendsto (fun t : ℝ ↦ t ^ (-(1 - α))) atTop (nhds 0) :=
        tendsto_rpow_neg_atTop (sub_pos.mpr hα1)
      have hr' : Tendsto (fun t : ℝ ↦ t ^ (α - 1)) atTop (nhds 0) := by
        simpa only [show α - 1 = -(1 - α) by ring] using hr
      simpa using tendsto_const_nhds.mul hr'
    have hlim := hinv.sub hpow
    have heq : (fun t : ℝ ↦
        ((1 - α) : ℝ)⁻¹ * t⁻¹ - ((1 - α) : ℝ)⁻¹ * t ^ (α - 1)) =ᶠ[atTop]
        (fun t : ℝ ↦ (1 - t ^ α) / (1 - α) / t) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [show t ^ (α - 1) = t ^ α / t by
        simpa using Real.rpow_sub_one ht.ne' α]
      field_simp
    simpa using hlim.congr' heq

@[simp]
theorem powerGenerator_apply (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (t : ℝ) :
    powerGenerator α hα0 hα1 t = (1 - t ^ α) / (1 - α) := rfl

@[simp]
theorem powerGenerator_zero (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    powerGenerator α hα0 hα1 0 = (1 - α)⁻¹ := by
  rw [powerGenerator_apply]
  simp [hα0.ne', div_eq_mul_inv]

theorem powerGenerator_strictAntiOn (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    StrictAntiOn (powerGenerator α hα0 hα1) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  have hp := Real.strictMonoOn_rpow_Ici_of_exponent_pos hα0 hx.1.le hy.1.le hxy
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  rw [powerGenerator_apply, powerGenerator_apply]
  exact (div_lt_div_iff_of_pos_right hden).2 (by linarith)

/-- The Gaussian Rényi overlap profile, packaged so that the endpoint `r=1`
agrees with the continuous definition of the paper's overlap profile. -/
noncomputable def gaussianRenyiOverlap
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (r x : ℝ) : ℝ :=
  1 - (1 - α) * gaussianProfile (powerGenerator α hα0 hα1) r x

theorem gaussianRenyiOverlap_pos
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    0 < gaussianRenyiOverlap α hα0 hα1 r x := by
  let f := powerGenerator α hα0 hα1
  have hstrict : StrictAnti (gaussianProfile f r) :=
    strictAnti_gaussianProfile f hr.1 hr.2
      (powerGenerator_strictAntiOn α hα0 hα1)
  have hle : gaussianProfile f r (x - 1) ≤ f 0 :=
    (antitone_gaussianProfile f hr.1 hr.2).ge_of_tendsto
      (gaussianProfile_tendsto_atBot f hr.1 hr.2) (x - 1)
  have hlt : gaussianProfile f r x < f 0 :=
    (hstrict (by linarith : x - 1 < x)).trans_le hle
  change 0 < 1 - (1 - α) * gaussianProfile f r x
  have hlt' : gaussianProfile f r x < (1 - α)⁻¹ := by
    simpa only [show f 0 = (1 - α)⁻¹ by
      exact powerGenerator_zero α hα0 hα1] using hlt
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  have hinv : (1 - α) * (1 - α)⁻¹ = 1 := mul_inv_cancel₀ hden.ne'
  nlinarith [hlt']

/-- The increasing transformation from power `f`-divergence
to Rényi divergence (base two). -/
noncomputable def renyiTransform (α d : ℝ) : ℝ :=
  -(1 / (1 - α)) * Real.logb 2 (1 - (1 - α) * d)

/-- The native order-`α` overlap `∑ P^α Q¹⁻ᵅ`. -/
noncomputable def renyiOverlap {A : Type*} [Fintype A]
    (α : ℝ) (P Q : FinProb A) : ℝ :=
  ∑ a, (P a) ^ α * (Q a) ^ (1 - α)

/-- The finite real formula for Rényi divergence.  Operational uses below
come with a proof that the overlap is positive. -/
noncomputable def finiteRenyiDivergence {A : Type*} [Fintype A]
    (α : ℝ) (P Q : FinProb A) : ℝ :=
  -(1 / (1 - α)) * Real.logb 2 (renyiOverlap α P Q)

/-- Native extended Rényi divergence.  Unlike `Real.log`, this definition
records a zero overlap as `+∞`. -/
noncomputable def renyiDivergence {A : Type*} [Fintype A]
    (α : ℝ) (P Q : FinProb A) : WithTop ℝ :=
  if renyiOverlap α P Q = 0 then ⊤ else
    (finiteRenyiDivergence α P Q : WithTop ℝ)

theorem renyiDivergence_of_overlap_pos {A : Type*} [Fintype A]
    (α : ℝ) (P Q : FinProb A) (h : 0 < renyiOverlap α P Q) :
    renyiDivergence α P Q = (finiteRenyiDivergence α P Q : WithTop ℝ) := by
  simp [renyiDivergence, h.ne']

theorem renyiOverlap_nonneg {A : Type*} [Fintype A]
    (α : ℝ) (P Q : FinProb A) : 0 ≤ renyiOverlap α P Q := by
  unfold renyiOverlap
  exact Finset.sum_nonneg fun a _ ↦ mul_nonneg (Real.rpow_nonneg (P.nonneg a) _)
    (Real.rpow_nonneg (Q.nonneg a) _)

theorem renyiOverlap_pos_of_common_support {A : Type*} [Fintype A]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (P Q : FinProb A)
    {a : A} (hP : 0 < P a) (hQ : 0 < Q a) :
    0 < renyiOverlap α P Q := by
  unfold renyiOverlap
  apply Finset.sum_pos'
  · exact fun b _ ↦ mul_nonneg (Real.rpow_nonneg (P.nonneg b) _)
      (Real.rpow_nonneg (Q.nonneg b) _)
  · exact ⟨a, Finset.mem_univ a,
      mul_pos (Real.rpow_pos_of_pos hP α)
        (Real.rpow_pos_of_pos hQ (1 - α))⟩

private theorem powerPerspective_identity
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (1 - α) * perspective (powerGenerator α hα0 hα1) p q =
      q - p ^ α * q ^ (1 - α) := by
  by_cases hq0 : q = 0
  · subst q
    have h1a : 1 - α ≠ 0 := (sub_pos.mpr hα1).ne'
    simp [perspective_zero_right, Real.zero_rpow h1a]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    rw [perspective_of_pos _ hqpos, powerGenerator_apply]
    have hpow : q * (p / q) ^ α = p ^ α * q ^ (1 - α) := by
      rw [Real.div_rpow hp hq α, Real.rpow_sub hqpos 1 α, Real.rpow_one]
      have hqa : q ^ α ≠ 0 := (Real.rpow_pos_of_pos hqpos α).ne'
      field_simp [hqa, hq0]
    have hden : 1 - α ≠ 0 := (sub_pos.mpr hα1).ne'
    calc
      (1 - α) * (q * ((1 - (p / q) ^ α) / (1 - α))) =
          q * (1 - (p / q) ^ α) := by field_simp [hden]
      _ = q - q * (p / q) ^ α := by ring
      _ = q - p ^ α * q ^ (1 - α) := by rw [hpow]

/-- The power-divergence identity, proved from the native overlap and the
perspective definition, including reference-zero coordinates. -/
theorem powerFDiv_identity {A : Type*} [Fintype A]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (P Q : FinProb A) :
    1 - (1 - α) * fDivergence (powerGenerator α hα0 hα1) P Q =
      renyiOverlap α P Q := by
  classical
  unfold fDivergence renyiOverlap
  rw [Finset.mul_sum]
  simp_rw [powerPerspective_identity α hα0 hα1 (P.nonneg _) (Q.nonneg _)]
  rw [Finset.sum_sub_distrib, Q.sum_prob]
  ring

/-- The power-to-Rényi transformation on its finite domain. -/
theorem finiteRenyiDivergence_eq_transform {A : Type*} [Fintype A]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (P Q : FinProb A) :
    finiteRenyiDivergence α P Q =
      renyiTransform α (fDivergence (powerGenerator α hα0 hα1) P Q) := by
  unfold finiteRenyiDivergence renyiTransform
  rw [powerFDiv_identity α hα0 hα1 P Q]

theorem continuousAt_renyiTransform
    {α d : ℝ} (hα1 : α < 1) (hpos : 0 < 1 - (1 - α) * d) :
    ContinuousAt (renyiTransform α) d := by
  unfold renyiTransform
  exact continuousAt_const.mul
    ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).logb
      hpos.ne')

theorem powerFDiv_lt_endpoint_iff {A : Type*} [Fintype A]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (P Q : FinProb A) :
    fDivergence (powerGenerator α hα0 hα1) P Q < (1 - α)⁻¹ ↔
      0 < renyiOverlap α P Q := by
  let d := fDivergence (powerGenerator α hα0 hα1) P Q
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  have hinv : (1 - α) * (1 - α)⁻¹ = 1 := mul_inv_cancel₀ hden.ne'
  have hid : renyiOverlap α P Q = 1 - (1 - α) * d := by
    simpa [d] using (powerFDiv_identity α hα0 hα1 P Q).symm
  rw [hid]
  constructor
  · intro hd
    rw [inv_eq_one_div, lt_div_iff₀ hden] at hd
    nlinarith
  · intro hoverlap
    rw [inv_eq_one_div, lt_div_iff₀ hden]
    linarith

theorem powerFDiv_le_endpoint {A : Type*} [Fintype A]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (P Q : FinProb A) :
    fDivergence (powerGenerator α hα0 hα1) P Q ≤ (1 - α)⁻¹ := by
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  have hinv : (1 - α) * (1 - α)⁻¹ = 1 := mul_inv_cancel₀ hden.ne'
  rw [inv_eq_one_div, le_div_iff₀ hden]
  have hoverlap := renyiOverlap_nonneg α P Q
  rw [← powerFDiv_identity α hα0 hα1 P Q] at hoverlap
  nlinarith

private theorem renyiTransform_mono_of_lt_endpoint
    (α : ℝ) (hα1 : α < 1) {d e : ℝ}
    (hde : d ≤ e) (he : e < (1 - α)⁻¹) :
    renyiTransform α d ≤ renyiTransform α e := by
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  have hinv : (1 - α) * (1 - α)⁻¹ = 1 := mul_inv_cancel₀ hden.ne'
  have hearg : 0 < 1 - (1 - α) * e := by
    rw [inv_eq_one_div, lt_div_iff₀ hden] at he
    nlinarith
  have hdarg : 0 < 1 - (1 - α) * d := by
    have hm := mul_le_mul_of_nonneg_left hde hden.le
    linarith
  have harg : 1 - (1 - α) * e ≤ 1 - (1 - α) * d := by
    gcongr
  have hlog : Real.logb 2 (1 - (1 - α) * e) ≤
      Real.logb 2 (1 - (1 - α) * d) :=
    Real.logb_le_logb_of_le (by norm_num) hearg harg
  unfold renyiTransform
  have hc : -(1 / (1 - α)) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg zero_le_one hden.le)
  exact mul_le_mul_of_nonpos_left hlog hc

private theorem renyiTransform_strictMono_of_lt_endpoint
    (α : ℝ) (hα1 : α < 1) {d e : ℝ}
    (hde : d < e) (he : e < (1 - α)⁻¹) :
    renyiTransform α d < renyiTransform α e := by
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  have hearg : 0 < 1 - (1 - α) * e := by
    rw [inv_eq_one_div, lt_div_iff₀ hden] at he
    nlinarith
  have hdarg : 0 < 1 - (1 - α) * d := by
    nlinarith [mul_lt_mul_of_pos_left hde hden]
  have harg : 1 - (1 - α) * e < 1 - (1 - α) * d := by
    nlinarith [mul_lt_mul_of_pos_left hde hden]
  have hlog : Real.logb 2 (1 - (1 - α) * e) <
      Real.logb 2 (1 - (1 - α) * d) :=
    Real.logb_lt_logb (by norm_num) hearg harg
  unfold renyiTransform
  exact mul_lt_mul_of_neg_left hlog
    (neg_neg_of_pos (div_pos zero_lt_one hden))

theorem renyiTransform_le_renyiTransform_iff
    (α : ℝ) (hα1 : α < 1) {d e : ℝ}
    (hd : d < (1 - α)⁻¹) (he : e < (1 - α)⁻¹) :
    renyiTransform α d ≤ renyiTransform α e ↔ d ≤ e := by
  constructor
  · intro hT
    by_contra hde
    exact (not_lt_of_ge hT)
      (renyiTransform_strictMono_of_lt_endpoint α hα1 (lt_of_not_ge hde) hd)
  · intro hde
    exact renyiTransform_mono_of_lt_endpoint α hα1 hde he

private theorem renyiTransform_sInf
    (α : ℝ) (hα1 : α < 1) (A : Set ℝ)
    (hne : A.Nonempty) (hbdd : BddBelow A)
    (hlt : ∀ d ∈ A, d < (1 - α)⁻¹) :
    renyiTransform α (sInf A) = sInf (renyiTransform α '' A) := by
  have hneA := hne
  obtain ⟨d, hd⟩ := hne
  have hinflt : sInf A < (1 - α)⁻¹ :=
    (csInf_le hbdd hd).trans_lt (hlt d hd)
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  have hinv : (1 - α) * (1 - α)⁻¹ = 1 := mul_inv_cancel₀ hden.ne'
  have harg : 0 < 1 - (1 - α) * sInf A := by
    rw [inv_eq_one_div, lt_div_iff₀ hden] at hinflt
    nlinarith
  refine MonotoneOn.map_csInf_of_continuousWithinAt
    (continuousAt_renyiTransform hα1 harg).continuousWithinAt ?_ hneA hbdd
  intro d hd e he hde
  exact renyiTransform_mono_of_lt_endpoint α hα1 hde (hlt e he)

private theorem sInf_restrict_lt
    (A : Set ℝ) (c : ℝ) (hne : A.Nonempty) (hbdd : BddBelow A)
    (hbelow : ∃ d ∈ A, d < c) :
    sInf A = sInf {d : ℝ | d ∈ A ∧ d < c} := by
  let B : Set ℝ := {d : ℝ | d ∈ A ∧ d < c}
  obtain ⟨d₀, hd₀A, hd₀c⟩ := hbelow
  have hBne : B.Nonempty := ⟨d₀, hd₀A, hd₀c⟩
  have hbddA := hbdd
  obtain ⟨l, hl⟩ := hbdd
  have hBbdd : BddBelow B := ⟨l, fun d hd ↦ hl hd.1⟩
  change sInf A = sInf B
  apply le_antisymm
  · apply le_csInf hBne
    intro d hd
    exact csInf_le hbddA hd.1
  · apply le_csInf hne
    intro d hdA
    by_cases hdc : d < c
    · exact csInf_le hBbdd ⟨hdA, hdc⟩
    · have hcd : c ≤ d := le_of_not_gt hdc
      exact (csInf_le hBbdd ⟨hd₀A, hd₀c⟩).trans (hd₀c.le.trans hcd)

theorem fixedRenyiOverlap_pos
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    0 < renyiOverlap α (hashedLaw P H)
      (uniformViewLaw M hM (P.marginal.prod H.seed)) := by
  obtain ⟨o, ho⟩ := (hashedLaw P H).exists_pos
  rcases o with ⟨z, y, s⟩
  have hpys : 0 < P.marginal y * H.seed s := by
    rcases (mul_pos_iff.mp ho) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge
        (mul_nonneg (P.marginal.nonneg y) (H.seed.nonneg s))) h.1)
  have hQ : 0 < uniformViewLaw M hM (P.marginal.prod H.seed) (z, (y, s)) := by
    rw [uniformViewLaw_apply, FinProb.prod_apply]
    exact mul_pos (inv_pos.mpr (by exact_mod_cast hM)) hpys
  exact renyiOverlap_pos_of_common_support α hα0 hα1 _ _ ho hQ

/-- Fixed-reference Rényi leakage, defined directly from the extracted and
ideal probability laws. -/
noncomputable def fixedRenyiLeakage
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (α : ℝ) (P : FiniteSource X Y) (H : SeededHash X S M)
    (hM : 0 < M) : ℝ :=
  finiteRenyiDivergence α (hashedLaw P H)
    (uniformViewLaw M hM (P.marginal.prod H.seed))

/-- Rényi leakage to a specified public-view reference.  The codomain records
the zero-overlap case as `+∞`. -/
noncomputable def referenceRenyiLeakage
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (α : ℝ) (P : FiniteSource X Y) (H : SeededHash X S M)
    (hM : 0 < M) (R : FinProb (Y × S)) : WithTop ℝ :=
  renyiDivergence α (hashedLaw P H) (uniformViewLaw M hM R)

/-- Optimized-reference Rényi leakage of a fixed seeded family.  Only finite
reference values enter the real infimum; the actual `(Y,S)` marginal always
supplies one. -/
noncomputable def optimizedRenyiLeakage
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (α : ℝ) (P : FiniteSource X Y) (H : SeededHash X S M)
    (hM : 0 < M) : ℝ :=
  sInf {v : ℝ | ∃ R : FinProb (Y × S),
    0 < renyiOverlap α (hashedLaw P H) (uniformViewLaw M hM R) ∧
    v = finiteRenyiDivergence α (hashedLaw P H) (uniformViewLaw M hM R)}

theorem fixedRenyiLeakage_eq_native
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    renyiDivergence α (hashedLaw P H)
        (uniformViewLaw M hM (P.marginal.prod H.seed)) =
      (fixedRenyiLeakage α P H hM : WithTop ℝ) := by
  rw [renyiDivergence_of_overlap_pos]
  · rfl
  · exact fixedRenyiOverlap_pos α hα0 hα1 P H hM

theorem fixedRenyiLeakage_eq_transform
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    fixedRenyiLeakage α P H hM =
      renyiTransform α (fixedLeakage (powerGenerator α hα0 hα1) P H) := by
  rw [fixedRenyiLeakage, finiteRenyiDivergence_eq_transform,
    ← fixedLeakage_eq_fDivergence]

theorem optimizedRenyiLeakage_eq_transform
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    optimizedRenyiLeakage α P H hM =
      renyiTransform α (optimizedLeakage (powerGenerator α hα0 hα1) P H) := by
  let f := powerGenerator α hα0 hα1
  let A : Set ℝ := {d : ℝ | ∃ R : FinProb (Y × S),
    d = referenceLeakage f P H R}
  let A' : Set ℝ := {d : ℝ | d ∈ A ∧ d < (1 - α)⁻¹}
  let B : Set ℝ := {v : ℝ | ∃ R : FinProb (Y × S),
    0 < renyiOverlap α (hashedLaw P H) (uniformViewLaw M hM R) ∧
    v = finiteRenyiDivergence α (hashedLaw P H) (uniformViewLaw M hM R)}
  let R₀ := P.marginal.prod H.seed
  have hAne : A.Nonempty := ⟨referenceLeakage f P H R₀, R₀, rfl⟩
  have hAbdd : BddBelow A := ⟨0, by
    rintro d ⟨R, rfl⟩
    rw [referenceLeakage_eq_fDivergence f P H hM R]
    exact fDivergence_nonneg f _ _⟩
  have hR₀lt : referenceLeakage f P H R₀ < (1 - α)⁻¹ := by
    rw [referenceLeakage_eq_fDivergence f P H hM R₀,
      powerFDiv_lt_endpoint_iff]
    exact fixedRenyiOverlap_pos α hα0 hα1 P H hM
  have hsinf : sInf A = sInf A' := by
    exact sInf_restrict_lt A ((1 - α)⁻¹) hAne hAbdd
      ⟨referenceLeakage f P H R₀, ⟨R₀, rfl⟩, hR₀lt⟩
  have hA'ne : A'.Nonempty :=
    ⟨referenceLeakage f P H R₀, ⟨R₀, rfl⟩, hR₀lt⟩
  have hA'bdd : BddBelow A' := ⟨0, by
    rintro d ⟨⟨R, rfl⟩, _⟩
    rw [referenceLeakage_eq_fDivergence f P H hM R]
    exact fDivergence_nonneg f _ _⟩
  have hBimage : B = renyiTransform α '' A' := by
    ext v
    constructor
    · rintro ⟨R, hoverlap, rfl⟩
      let d := referenceLeakage f P H R
      have hdEq : d = fDivergence f (hashedLaw P H)
          (uniformViewLaw M hM R) := referenceLeakage_eq_fDivergence f P H hM R
      have hdlt : d < (1 - α)⁻¹ := by
        rw [hdEq, powerFDiv_lt_endpoint_iff α hα0 hα1]
        exact hoverlap
      refine ⟨d, ⟨⟨R, rfl⟩, hdlt⟩, ?_⟩
      rw [finiteRenyiDivergence_eq_transform α hα0 hα1]
      simpa [f] using congrArg (renyiTransform α) hdEq
    · rintro ⟨d, ⟨⟨R, rfl⟩, hdlt⟩, rfl⟩
      have hdEq := referenceLeakage_eq_fDivergence f P H hM R
      have hoverlap : 0 < renyiOverlap α (hashedLaw P H)
          (uniformViewLaw M hM R) := by
        rw [hdEq, powerFDiv_lt_endpoint_iff α hα0 hα1] at hdlt
        exact hdlt
      refine ⟨R, hoverlap, ?_⟩
      rw [finiteRenyiDivergence_eq_transform α hα0 hα1]
      simpa [f] using congrArg (renyiTransform α) hdEq
  have hmap := renyiTransform_sInf α hα1 A' hA'ne hA'bdd
    (fun d hd ↦ hd.2)
  change sInf B = renyiTransform α (sInf A)
  rw [hBimage, ← hmap, hsinf]

/-- Optimal fixed-reference Rényi leakage, defined by optimizing the native
Rényi leakage of the extracted law. -/
noncomputable def optimalFixedRenyiLeakage
    {X Y : Type} [Fintype X] [Fintype Y]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) : ℝ :=
  sInf {v : ℝ | ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M,
    v = fixedRenyiLeakage α P H hM}

/-- Optimal optimized-reference Rényi leakage, with both the seeded family
and the reference probability law optimized. -/
noncomputable def optimalOptimizedRenyiLeakage
    {X Y : Type} [Fintype X] [Fintype Y]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) : ℝ :=
  sInf {v : ℝ | ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M,
    v = optimizedRenyiLeakage α P H hM}

theorem optimalFixedRenyiLeakage_eq_transform
    {X Y : Type} [Fintype X] [Fintype Y]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) :
    optimalFixedRenyiLeakage α hα0 hα1 P M hM =
      renyiTransform α
        (optimalFixedLeakage (powerGenerator α hα0 hα1) P M) := by
  let f := powerGenerator α hα0 hα1
  let A : Set ℝ := {d : ℝ | ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M,
    d = fixedLeakage f P H}
  let B : Set ℝ := {v : ℝ | ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M,
    v = fixedRenyiLeakage α P H hM}
  let H₀ : SeededHash X (Fin 1) M :=
    { seed := FinProb.uniformFin 1 (by omega)
      hash := fun _ _ ↦ ⟨0, hM⟩ }
  have hAne : A.Nonempty := ⟨fixedLeakage f P H₀, 1, H₀, rfl⟩
  have hAbdd : BddBelow A := ⟨0, by
    rintro d ⟨N, H, rfl⟩
    rw [fixedLeakage_eq_fDivergence f P H hM]
    exact fDivergence_nonneg f _ _⟩
  have hAlt : ∀ d ∈ A, d < (1 - α)⁻¹ := by
    rintro d ⟨N, H, rfl⟩
    rw [fixedLeakage_eq_fDivergence f P H hM,
      powerFDiv_lt_endpoint_iff α hα0 hα1]
    exact fixedRenyiOverlap_pos α hα0 hα1 P H hM
  have hBimage : B = renyiTransform α '' A := by
    ext v
    constructor
    · rintro ⟨N, H, rfl⟩
      refine ⟨fixedLeakage f P H, ⟨N, H, rfl⟩, ?_⟩
      exact (fixedRenyiLeakage_eq_transform α hα0 hα1 P H hM).symm
    · rintro ⟨d, ⟨N, H, rfl⟩, rfl⟩
      exact ⟨N, H, (fixedRenyiLeakage_eq_transform α hα0 hα1 P H hM).symm⟩
  have hmap := renyiTransform_sInf α hα1 A hAne hAbdd hAlt
  change sInf B = renyiTransform α (sInf A)
  rw [hBimage, ← hmap]

theorem optimalOptimizedRenyiLeakage_eq_transform
    {X Y : Type} [Fintype X] [Fintype Y]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) :
    optimalOptimizedRenyiLeakage α hα0 hα1 P M hM =
      renyiTransform α
        (optimalOptimizedLeakage (powerGenerator α hα0 hα1) P M) := by
  let f := powerGenerator α hα0 hα1
  let A : Set ℝ := {d : ℝ | ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M,
    d = optimizedLeakage f P H}
  let B : Set ℝ := {v : ℝ | ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M,
    v = optimizedRenyiLeakage α P H hM}
  let H₀ : SeededHash X (Fin 1) M :=
    { seed := FinProb.uniformFin 1 (by omega)
      hash := fun _ _ ↦ ⟨0, hM⟩ }
  have hAne : A.Nonempty := ⟨optimizedLeakage f P H₀, 1, H₀, rfl⟩
  have hAbdd : BddBelow A := ⟨0, by
    rintro d ⟨N, H, rfl⟩
    exact optimizedLeakage_nonneg f P H hM⟩
  have hAlt : ∀ d ∈ A, d < (1 - α)⁻¹ := by
    rintro d ⟨N, H, rfl⟩
    let R₀ := P.marginal.prod H.seed
    have hle : optimizedLeakage f P H ≤ referenceLeakage f P H R₀ :=
      optimizedLeakage_le_reference f P H hM R₀
    have hlt : referenceLeakage f P H R₀ < (1 - α)⁻¹ := by
      rw [referenceLeakage_eq_fDivergence f P H hM R₀,
        powerFDiv_lt_endpoint_iff α hα0 hα1]
      exact fixedRenyiOverlap_pos α hα0 hα1 P H hM
    exact hle.trans_lt hlt
  have hBimage : B = renyiTransform α '' A := by
    ext v
    constructor
    · rintro ⟨N, H, rfl⟩
      refine ⟨optimizedLeakage f P H, ⟨N, H, rfl⟩, ?_⟩
      exact (optimizedRenyiLeakage_eq_transform α hα0 hα1 P H hM).symm
    · rintro ⟨d, ⟨N, H, rfl⟩, rfl⟩
      exact ⟨N, H,
        (optimizedRenyiLeakage_eq_transform α hα0 hα1 P H hM).symm⟩
  have hmap := renyiTransform_sInf α hα1 A hAne hAbdd hAlt
  change sInf B = renyiTransform α (sInf A)
  rw [hBimage, ← hmap]

theorem optimalFixedPowerLeakage_lt_endpoint
    {X Y : Type} [Fintype X] [Fintype Y]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) :
    optimalFixedLeakage (powerGenerator α hα0 hα1) P M < (1 - α)⁻¹ := by
  let H₀ : SeededHash X (Fin 1) M :=
    { seed := FinProb.uniformFin 1 (by omega)
      hash := fun _ _ ↦ ⟨0, hM⟩ }
  refine (optimalFixedLeakage_le_family
    (powerGenerator α hα0 hα1) P H₀ hM).trans_lt ?_
  rw [fixedLeakage_eq_fDivergence, powerFDiv_lt_endpoint_iff α hα0 hα1]
  exact fixedRenyiOverlap_pos α hα0 hα1 P H₀ hM

theorem optimalOptimizedPowerLeakage_lt_endpoint
    {X Y : Type} [Fintype X] [Fintype Y]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) :
    optimalOptimizedLeakage (powerGenerator α hα0 hα1) P M < (1 - α)⁻¹ := by
  let H₀ : SeededHash X (Fin 1) M :=
    { seed := FinProb.uniformFin 1 (by omega)
      hash := fun _ _ ↦ ⟨0, hM⟩ }
  refine (optimalOptimizedLeakage_le_family
    (powerGenerator α hα0 hα1) P H₀ hM).trans_lt ?_
  let R₀ := P.marginal.prod H₀.seed
  refine (optimizedLeakage_le_reference
    (powerGenerator α hα0 hα1) P H₀ hM R₀).trans_lt ?_
  rw [referenceLeakage_eq_fDivergence,
    powerFDiv_lt_endpoint_iff α hα0 hα1]
  exact fixedRenyiOverlap_pos α hα0 hα1 P H₀ hM

/-- The one-shot fixed-reference converse transported to native Rényi
divergence. -/
theorem fixedRenyi_family_converse
    {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    renyiTransform α
        (fixedGamma (powerGenerator α hα0 hα1) P M) ≤
      fixedRenyiLeakage α P H hM := by
  rw [fixedRenyiLeakage_eq_transform α hα0 hα1 P H hM]
  apply renyiTransform_mono_of_lt_endpoint α hα1
    (fixed_family_converse (powerGenerator α hα0 hα1) P H hM)
  rw [fixedLeakage_eq_fDivergence,
    powerFDiv_lt_endpoint_iff α hα0 hα1]
  exact fixedRenyiOverlap_pos α hα0 hα1 P H hM

/-- The one-shot optimized-reference converse transported to native Rényi
divergence. -/
theorem optimizedRenyi_family_converse
    {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    renyiTransform α
        (optimizedGamma (powerGenerator α hα0 hα1) P M) ≤
      optimizedRenyiLeakage α P H hM := by
  let f := powerGenerator α hα0 hα1
  let R₀ := P.marginal.prod H.seed
  have hlt : optimizedLeakage f P H < (1 - α)⁻¹ := by
    refine (optimizedLeakage_le_reference f P H hM R₀).trans_lt ?_
    rw [referenceLeakage_eq_fDivergence,
      powerFDiv_lt_endpoint_iff α hα0 hα1]
    exact fixedRenyiOverlap_pos α hα0 hα1 P H hM
  rw [optimizedRenyiLeakage_eq_transform α hα0 hα1 P H hM]
  exact renyiTransform_mono_of_lt_endpoint α hα1
    (optimized_family_converse f P H hM) hlt

/-- The leakage, hashing-achievability, and converse parts of **Corollary 3
(Rényi specialization)**. -/
theorem paperCorollary3_leakage
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L : ℝ)
    (hV : 0 < ConditionalLimit.totalVariance P)
    (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ optimalFixedRenyiLeakage α hα0 hα1
        (blockSource P n) (M n) (hM n)) atTop
      (nhds (-(1 / (1 - α)) * Real.logb 2
        (gaussianRenyiOverlap α hα0 hα1
          (ConditionalLimit.variance₁ P / ConditionalLimit.totalVariance P)
          (-L / Real.sqrt (ConditionalLimit.totalVariance P))))) ∧
    Tendsto (fun n ↦ optimalOptimizedRenyiLeakage α hα0 hα1
        (blockSource P n) (M n) (hM n)) atTop
      (nhds (-(α / (1 - α)) * Real.logb 2
        (gaussianCDF (-L / Real.sqrt (ConditionalLimit.totalVariance P))))) ∧
    (∀ (N : ℕ → ℕ)
      (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n)),
      (∀ n, SeededHash.paperDefinition6 (H n)) →
      Tendsto (fun n ↦ fixedRenyiLeakage α
          (blockSource P n) (H n) (hM n)) atTop
        (nhds (-(1 / (1 - α)) * Real.logb 2
          (gaussianRenyiOverlap α hα0 hα1
            (ConditionalLimit.variance₁ P / ConditionalLimit.totalVariance P)
            (-L / Real.sqrt (ConditionalLimit.totalVariance P))))) ∧
      Tendsto (fun n ↦ optimizedRenyiLeakage α
          (blockSource P n) (H n) (hM n)) atTop
        (nhds (-(α / (1 - α)) * Real.logb 2
          (gaussianCDF
            (-L / Real.sqrt (ConditionalLimit.totalVariance P)))))) ∧
    (∀ (N : ℕ → ℕ)
      (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n)),
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        -(1 / (1 - α)) * Real.logb 2
            (gaussianRenyiOverlap α hα0 hα1
              (ConditionalLimit.variance₁ P / ConditionalLimit.totalVariance P)
              (-L / Real.sqrt (ConditionalLimit.totalVariance P))) - ε ≤
          fixedRenyiLeakage α (blockSource P n) (H n) (hM n)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        -(α / (1 - α)) * Real.logb 2
            (gaussianCDF (-L / Real.sqrt
              (ConditionalLimit.totalVariance P))) - ε ≤
          optimizedRenyiLeakage α (blockSource P n) (H n) (hM n))) := by
  let f := powerGenerator α hα0 hα1
  let x := -L / Real.sqrt (ConditionalLimit.totalVariance P)
  let r := ConditionalLimit.variance₁ P / ConditionalLimit.totalVariance P
  have hmain := paperTheorem1 hBE f P hpY M hM L hV hRate
  have hr := varianceRatio_mem_unit P hV
  have hoverlap := gaussianRenyiOverlap_pos α hα0 hα1 hr x
  have hTfixed : ContinuousAt (renyiTransform α)
      (gaussianProfile f r x) :=
    continuousAt_renyiTransform hα1 (by
      simpa [gaussianRenyiOverlap, f, r, x] using hoverlap)
  have hPhi : 0 < gaussianCDF x := gaussianCDF_pos x
  have hpowPhi : 0 < (gaussianCDF x) ^ α := Real.rpow_pos_of_pos hPhi α
  have hoptArg :
      1 - (1 - α) * f (gaussianCDF x) = (gaussianCDF x) ^ α := by
    change 1 - (1 - α) * ((1 - (gaussianCDF x) ^ α) / (1 - α)) =
      (gaussianCDF x) ^ α
    field_simp [show 1 - α ≠ 0 by linarith]
    ring
  have hToptimized : ContinuousAt (renyiTransform α)
      (f (gaussianCDF x)) :=
    continuousAt_renyiTransform hα1 (by
      rw [hoptArg]
      exact hpowPhi)
  have hlogpow : Real.logb 2 ((gaussianCDF x) ^ α) =
      α * Real.logb 2 (gaussianCDF x) :=
    Real.logb_rpow_eq_mul_logb_of_pos hPhi
  have hfixedLimit : renyiTransform α (gaussianProfile f r x) =
      -(1 / (1 - α)) * Real.logb 2
        (gaussianRenyiOverlap α hα0 hα1 r x) := by
    rfl
  have hoptimizedLimit : renyiTransform α (f (gaussianCDF x)) =
      -(α / (1 - α)) * Real.logb 2 (gaussianCDF x) := by
    rw [renyiTransform, hoptArg, hlogpow]
    ring
  have hfixedOptimal := hTfixed.tendsto.comp hmain.1
  have hoptimizedOptimal := hToptimized.tendsto.comp hmain.2.1
  have hfixedGamma := hTfixed.tendsto.comp
    (fixedGamma_rate_tendsto hBE f P hpY M hM L hV hRate)
  have hoptimizedGamma := hToptimized.tendsto.comp
    (optimizedGamma_rate_tendsto hBE f P hpY M hM L hV hRate)
  rw [hfixedLimit] at hfixedGamma
  rw [hoptimizedLimit] at hoptimizedGamma
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hfixedLimit]
    simpa only [optimalFixedRenyiLeakage_eq_transform, Function.comp_def,
      r, x] using hfixedOptimal
  · rw [← hoptimizedLimit]
    simpa only [optimalOptimizedRenyiLeakage_eq_transform,
      Function.comp_def, x] using hoptimizedOptimal
  · intro N H htwo
    have hfamilies := hmain.2.2.1 N H htwo
    constructor
    · rw [← hfixedLimit]
      have hfamily := hTfixed.tendsto.comp hfamilies.1
      apply hfamily.congr'
      exact Eventually.of_forall fun n ↦
        (fixedRenyiLeakage_eq_transform α hα0 hα1
          (blockSource P n) (H n) (hM n)).symm
    · rw [← hoptimizedLimit]
      have hfamily := hToptimized.tendsto.comp hfamilies.2
      apply hfamily.congr'
      exact Eventually.of_forall fun n ↦
        (optimizedRenyiLeakage_eq_transform α hα0 hα1
          (blockSource P n) (H n) (hM n)).symm
  · intro N H
    constructor
    · intro ε hε
      exact (hfixedGamma.eventually
          (Ioi_mem_nhds (sub_lt_self _ hε))).mono fun n hn ↦
        hn.le.trans (fixedRenyi_family_converse α hα0 hα1
          (blockSource P n) (H n) (hM n))
    · intro ε hε
      exact (hoptimizedGamma.eventually
          (Ioi_mem_nhds (sub_lt_self _ hε))).mono fun n hn ↦
        hn.le.trans (optimizedRenyi_family_converse α hα0 hα1
          (blockSource P n) (H n) (hM n))

/-- The affine-on-`[0,1]` total-variation generator. -/
noncomputable def totalVariationGenerator : AdmissibleGenerator where
  toFun t := max (1 - t) 0
  continuous := (continuous_const.sub continuous_id).max continuous_const
  convexOn_nonneg :=
    by
      refine ⟨convex_Ici (0 : ℝ), ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [smul_eq_mul]
      apply max_le
      · have hxle : 1 - x ≤ max (1 - x) 0 := le_max_left _ _
        have hyle : 1 - y ≤ max (1 - y) 0 := le_max_left _ _
        nlinarith
      · exact add_nonneg (mul_nonneg ha (le_max_right _ _))
          (mul_nonneg hb (le_max_right _ _))
  map_one := by simp
  sublinear_atTop := by
    have heq : (fun t : ℝ ↦ max (1 - t) 0 / t) =ᶠ[atTop]
        (fun _ : ℝ ↦ 0) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      simp [max_eq_right (sub_nonpos.mpr ht)]
    exact tendsto_const_nhds.congr' heq.symm

@[simp]
theorem totalVariationGenerator_apply (t : ℝ) :
    totalVariationGenerator t = max (1 - t) 0 := by
  rw [totalVariationGenerator]

@[simp]
theorem totalVariationGenerator_of_mem_unit {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    totalVariationGenerator t = 1 - t := by
  rw [totalVariationGenerator_apply]
  exact max_eq_left (sub_nonneg.mpr ht.2)

/-- Native total-variation distance on finite probability laws. -/
noncomputable def totalVariation {A : Type*} [Fintype A]
    (P Q : FinProb A) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |P a - Q a|

private theorem perspective_totalVariationGenerator {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    perspective totalVariationGenerator p q = max (q - p) 0 := by
  by_cases hq0 : q = 0
  · subst q
    simp [perspective, max_eq_right (neg_nonpos.mpr hp)]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    rw [perspective_of_pos totalVariationGenerator hqpos,
      totalVariationGenerator_apply]
    calc
      q * max (1 - p / q) 0 =
          max (q * (1 - p / q)) (q * 0) :=
        mul_max_of_nonneg (1 - p / q) 0 hq
      _ = max (q - p) 0 := by
        congr 1
        · field_simp [hq0]
        · ring

/-- The generator `(1-t)₊` gives exactly total variation,
including coordinates where the reference mass vanishes. -/
theorem fDivergence_totalVariationGenerator {A : Type*} [Fintype A]
    (P Q : FinProb A) :
    fDivergence totalVariationGenerator P Q = totalVariation P Q := by
  classical
  unfold fDivergence totalVariation
  simp_rw [perspective_totalVariationGenerator (P.nonneg _) (Q.nonneg _)]
  have hpoint (a : A) :
      max (Q a - P a) 0 = (|P a - Q a| + (Q a - P a)) / 2 := by
    by_cases h : P a ≤ Q a
    · rw [max_eq_left (sub_nonneg.mpr h), abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · have h' : Q a ≤ P a := le_of_not_ge h
      rw [max_eq_right (sub_nonpos.mpr h'), abs_of_nonneg (sub_nonneg.mpr h')]
      ring
  simp_rw [hpoint]
  rw [← Finset.sum_div]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, P.sum_prob, Q.sum_prob,
    sub_self, add_zero]
  ring

/-- Native fixed-reference total-variation leakage of a seeded family. -/
noncomputable def fixedTotalVariationLeakage
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) : ℝ :=
  totalVariation (hashedLaw P H)
    (uniformViewLaw M hM (P.marginal.prod H.seed))

/-- Native total-variation leakage to a specified public-view reference. -/
noncomputable def referenceTotalVariationLeakage
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M)
    (R : FinProb (Y × S)) : ℝ :=
  totalVariation (hashedLaw P H) (uniformViewLaw M hM R)

noncomputable def optimizedTotalVariationLeakage
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) : ℝ :=
  sInf {v : ℝ | ∃ R : FinProb (Y × S),
    v = referenceTotalVariationLeakage P H hM R}

noncomputable def optimalFixedTotalVariationLeakage
    {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) : ℝ :=
  sInf {v : ℝ | ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M,
    v = fixedTotalVariationLeakage P H hM}

noncomputable def optimalOptimizedTotalVariationLeakage
    {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) : ℝ :=
  sInf {v : ℝ | ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M,
    v = optimizedTotalVariationLeakage P H hM}

theorem fixedTotalVariationLeakage_eq_fLeakage
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    fixedTotalVariationLeakage P H hM =
      fixedLeakage totalVariationGenerator P H := by
  rw [fixedTotalVariationLeakage, ← fDivergence_totalVariationGenerator,
    ← fixedLeakage_eq_fDivergence]

theorem referenceTotalVariationLeakage_eq_fLeakage
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M)
    (R : FinProb (Y × S)) :
    referenceTotalVariationLeakage P H hM R =
      referenceLeakage totalVariationGenerator P H R := by
  rw [referenceTotalVariationLeakage, ← fDivergence_totalVariationGenerator,
    ← referenceLeakage_eq_fDivergence]

theorem optimizedTotalVariationLeakage_eq_fLeakage
    {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (P : FiniteSource X Y) (H : SeededHash X S M) (hM : 0 < M) :
    optimizedTotalVariationLeakage P H hM =
      optimizedLeakage totalVariationGenerator P H := by
  unfold optimizedTotalVariationLeakage optimizedLeakage
  congr 1
  ext v
  constructor
  · rintro ⟨R, rfl⟩
    exact ⟨R, referenceTotalVariationLeakage_eq_fLeakage P H hM R⟩
  · rintro ⟨R, rfl⟩
    exact ⟨R, (referenceTotalVariationLeakage_eq_fLeakage P H hM R).symm⟩

theorem optimalFixedTotalVariationLeakage_eq_fLeakage
    {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) :
    optimalFixedTotalVariationLeakage P M hM =
      optimalFixedLeakage totalVariationGenerator P M := by
  unfold optimalFixedTotalVariationLeakage optimalFixedLeakage
  congr 1
  ext v
  constructor
  · rintro ⟨N, H, rfl⟩
    exact ⟨N, H, fixedTotalVariationLeakage_eq_fLeakage P H hM⟩
  · rintro ⟨N, H, rfl⟩
    exact ⟨N, H, (fixedTotalVariationLeakage_eq_fLeakage P H hM).symm⟩

theorem optimalOptimizedTotalVariationLeakage_eq_fLeakage
    {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (M : ℕ) (hM : 0 < M) :
    optimalOptimizedTotalVariationLeakage P M hM =
      optimalOptimizedLeakage totalVariationGenerator P M := by
  unfold optimalOptimizedTotalVariationLeakage optimalOptimizedLeakage
  congr 1
  ext v
  constructor
  · rintro ⟨N, H, rfl⟩
    exact ⟨N, H, optimizedTotalVariationLeakage_eq_fLeakage P H hM⟩
  · rintro ⟨N, H, rfl⟩
    exact ⟨N, H, (optimizedTotalVariationLeakage_eq_fLeakage P H hM).symm⟩

private theorem cdf_centeredGaussian_eq_standardized
    {v t : ℝ} (hv : 0 < v) :
    ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 (Real.toNNReal v)) t =
      gaussianCDF (t / Real.sqrt v) := by
  let s := Real.sqrt v
  have hs : 0 < s := Real.sqrt_pos.2 hv
  have hmap :
      (ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ ↦ s * z) =
        ProbabilityTheory.gaussianReal 0 (Real.toNNReal v) := by
    rw [ProbabilityTheory.gaussianReal_map_const_mul]
    congr 1
    · norm_num
    · apply NNReal.eq
      simp [s, Real.sq_sqrt hv.le, hv.le]
  rw [ProbabilityTheory.cdf_eq_real, ← hmap, Measure.real_def,
    Measure.map_apply (by fun_prop) measurableSet_Iic,
    gaussianCDF, ProbabilityTheory.cdf_eq_real]
  congr 2
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic]
  simpa [s, mul_comm] using (le_div_iff₀ hs).symm

/-- Gaussian convolution identity (10): `E[Q_r(G;x)] = Φ(x)`. -/
theorem gaussianTransition_expectation {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    ∫ G, gaussianTransition r x G
      ∂(ProbabilityTheory.gaussianReal 0 1) = gaussianCDF x := by
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  let vr : NNReal := ⟨r, hr0⟩
  let v1r : NNReal := ⟨1 - r, h1r.le⟩
  let μr := ProbabilityTheory.gaussianReal 0 vr
  let μ1r := ProbabilityTheory.gaussianReal 0 v1r
  letI : IsProbabilityMeasure μr := by dsimp [μr]; infer_instance
  letI : IsProbabilityMeasure μ1r := by dsimp [μ1r]; infer_instance
  let F : ℝ → ℝ := Set.indicator (Set.Iic x) (fun _ ↦ 1)
  have hmeasure : μr ∗ μ1r = ProbabilityTheory.gaussianReal 0 1 := by
    calc
      μr ∗ μ1r = ProbabilityTheory.gaussianReal (0 + 0) (vr + v1r) := by
        exact ProbabilityTheory.gaussianReal_conv_gaussianReal
      _ = ProbabilityTheory.gaussianReal 0 1 := by
        congr 1
        · norm_num
        · refine NNReal.eq ?_
          change r + (1 - r) = 1
          ring
  have hFint : Integrable F (μr ∗ μ1r) := by
    rw [hmeasure]
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hconv := integral_conv hFint
  have hlhs : ∫ z, F z ∂(μr ∗ μ1r) = gaussianCDF x := by
    rw [hmeasure, gaussianCDF, ProbabilityTheory.cdf_eq_real]
    simp [F]
  have hinner (a : ℝ) :
      ∫ b, F (a + b) ∂μ1r = gaussianCDF ((x - a) / Real.sqrt (1 - r)) := by
    have hset : (fun b : ℝ ↦ a + b) ⁻¹' Set.Iic x = Set.Iic (x - a) := by
      ext b
      simp
    calc
      ∫ b, F (a + b) ∂μ1r = μ1r.real (Set.Iic (x - a)) := by
        rw [← integral_indicator_one measurableSet_Iic]
        apply integral_congr_ae
        filter_upwards with b
        simp only [F]
        by_cases hb : a + b ∈ Set.Iic x
        · have hb' : b ∈ Set.Iic (x - a) := by
            change b ≤ x - a
            change a + b ≤ x at hb
            linarith
          simp [Set.indicator, hb, hb']
        · have hb' : b ∉ Set.Iic (x - a) := by
            intro hb'
            apply hb
            change a + b ≤ x
            change b ≤ x - a at hb'
            linarith
          simp [Set.indicator, hb, hb']
      _ = ProbabilityTheory.cdf μ1r (x - a) := by
        rw [ProbabilityTheory.cdf_eq_real]
      _ = gaussianCDF ((x - a) / Real.sqrt (1 - r)) := by
        have hv1 : Real.toNNReal (1 - r) = v1r := by
          rw [Real.toNNReal_of_nonneg h1r.le]
          dsimp [v1r]
          rfl
        simpa only [μ1r, hv1] using
          (cdf_centeredGaussian_eq_standardized (t := x - a) h1r)
  have houter :
      ∫ a, gaussianCDF ((x - a) / Real.sqrt (1 - r)) ∂μr = gaussianCDF x := by
    rw [← hlhs, hconv]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a ↦ (hinner a).symm
  have hsqrtr : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hmapr :
      (ProbabilityTheory.gaussianReal 0 1).map
          (fun G : ℝ ↦ -(Real.sqrt r) * G) = μr := by
    dsimp [μr, vr]
    rw [ProbabilityTheory.gaussianReal_map_const_mul]
    congr 1
    · norm_num
    · apply NNReal.eq
      change (-Real.sqrt r) ^ 2 * 1 = r
      rw [neg_sq, Real.sq_sqrt hr0]
      ring
  rw [← hmapr] at houter
  rw [integral_map (by fun_prop)] at houter
  · simpa [gaussianTransition, sub_eq_add_neg] using houter
  · exact (continuous_gaussianCDF.comp
      ((continuous_const.sub continuous_id).div_const _)).aestronglyMeasurable

theorem gaussianProfile_totalVariation {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    gaussianProfile totalVariationGenerator r x = 1 - gaussianCDF x := by
  by_cases hr1 : r = 1
  · subst r
    rw [gaussianProfile, if_pos rfl]
    change max (1 - 0) 0 * (1 - gaussianCDF x) = 1 - gaussianCDF x
    norm_num
  rw [gaussianProfile, if_neg hr1]
  have hpoint (G : ℝ) :
      totalVariationGenerator (gaussianTransition r x G) =
        1 - gaussianTransition r x G :=
    totalVariationGenerator_of_mem_unit
      (gaussianCDF_mem_unit _)
  simp_rw [hpoint]
  have hrlt : r < 1 := lt_of_le_of_ne hr.2 hr1
  have hqInt : Integrable (fun G ↦ gaussianTransition r x G)
      (ProbabilityTheory.gaussianReal 0 1) := by
    apply Integrable.of_bound
      (continuous_gaussianCDF.comp
        ((continuous_const.add (continuous_const.mul continuous_id)).div_const _)
        |>.aestronglyMeasurable) 1
    filter_upwards with G
    change |gaussianCDF
      ((x + Real.sqrt r * G) / Real.sqrt (1 - r))| ≤ 1
    have hu := gaussianCDF_mem_unit
      ((x + Real.sqrt r * G) / Real.sqrt (1 - r))
    exact abs_le.2 ⟨by linarith [hu.1], hu.2⟩
  rw [integral_sub, integral_const, gaussianTransition_expectation hr.1 hrlt x]
  · simp
  · exact integrable_const 1
  · exact hqInt

/-- The leakage, hashing-achievability, and converse parts of **Corollary 4
(total variation)**. -/
theorem paperCorollary4_leakage
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (L : ℝ)
    (hV : 0 < ConditionalLimit.totalVariance P)
    (hRate : SecondOrderRate P M L) :
    Tendsto (fun n ↦ optimalFixedTotalVariationLeakage
        (blockSource P n) (M n) (hM n)) atTop
        (nhds (gaussianCDF (L / Real.sqrt (ConditionalLimit.totalVariance P)))) ∧
    Tendsto (fun n ↦ optimalOptimizedTotalVariationLeakage
        (blockSource P n) (M n) (hM n)) atTop
        (nhds (gaussianCDF (L / Real.sqrt (ConditionalLimit.totalVariance P)))) ∧
    (∀ (N : ℕ → ℕ)
      (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n)),
      (∀ n, SeededHash.paperDefinition6 (H n)) →
      Tendsto (fun n ↦ fixedTotalVariationLeakage
          (blockSource P n) (H n) (hM n)) atTop
        (nhds (gaussianCDF
          (L / Real.sqrt (ConditionalLimit.totalVariance P)))) ∧
      Tendsto (fun n ↦ optimizedTotalVariationLeakage
          (blockSource P n) (H n) (hM n)) atTop
        (nhds (gaussianCDF
          (L / Real.sqrt (ConditionalLimit.totalVariance P))))) ∧
    (∀ (N : ℕ → ℕ)
      (H : ∀ n, SeededHash (Fin n → X) (Fin (N n)) (M n)),
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        gaussianCDF (L / Real.sqrt (ConditionalLimit.totalVariance P)) - ε ≤
          fixedTotalVariationLeakage
            (blockSource P n) (H n) (hM n)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        gaussianCDF (L / Real.sqrt (ConditionalLimit.totalVariance P)) - ε ≤
          optimizedTotalVariationLeakage
            (blockSource P n) (H n) (hM n))) := by
  have hmain := paperTheorem1 hBE totalVariationGenerator P hpY M hM L hV hRate
  have hr := varianceRatio_mem_unit P hV
  have hsymm : 1 - gaussianCDF (-L / Real.sqrt (ConditionalLimit.totalVariance P)) =
      gaussianCDF (L / Real.sqrt (ConditionalLimit.totalVariance P)) := by
    rw [show -L / Real.sqrt (ConditionalLimit.totalVariance P) =
      -(L / Real.sqrt (ConditionalLimit.totalVariance P)) by ring,
      gaussianCDF_neg]
    ring
  have hunit := gaussianCDF_mem_unit
      (-L / Real.sqrt (ConditionalLimit.totalVariance P))
  have hzero : 0 ≤ gaussianCDF
      (L / Real.sqrt (ConditionalLimit.totalVariance P)) :=
    (gaussianCDF_mem_unit _).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [optimalFixedTotalVariationLeakage_eq_fLeakage,
      gaussianProfile_totalVariation hr, hsymm] using hmain.1
  ·
    simpa [optimalOptimizedTotalVariationLeakage_eq_fLeakage,
      totalVariationGenerator_of_mem_unit hunit, hsymm,
      max_eq_left hzero] using hmain.2.1
  · intro N H htwo
    have hfamilies := hmain.2.2.1 N H htwo
    constructor
    · simpa [fixedTotalVariationLeakage_eq_fLeakage,
        gaussianProfile_totalVariation hr, hsymm] using hfamilies.1
    · simpa [optimizedTotalVariationLeakage_eq_fLeakage,
        totalVariationGenerator_of_mem_unit hunit, hsymm,
        max_eq_left hzero] using hfamilies.2
  · intro N H
    have hconverses := hmain.2.2.2 N H
    constructor
    · intro ε hε
      simpa [fixedTotalVariationLeakage_eq_fLeakage,
        gaussianProfile_totalVariation hr, hsymm] using hconverses.1 ε hε
    · intro ε hε
      simpa [optimizedTotalVariationLeakage_eq_fLeakage,
        totalVariationGenerator_of_mem_unit hunit, hsymm,
        max_eq_left hzero] using hconverses.2 ε hε

end RandomnessExtraction
