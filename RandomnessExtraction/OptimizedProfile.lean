import RandomnessExtraction.GaussianProfile

/-!
# The optimized Gaussian profile

This file specializes the perspective-aggregation lemma and proves
Proposition 18.  The optimized capped quantity is written directly at the
real threshold used in the paper; this avoids an irrelevant integrality
restriction on the intermediate cap.
-/

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

open ConditionalLimit ConditionalCapped UniformEndpoint

/-- The unconditional block-surprisal tail appearing in Proposition 18. -/
noncomputable def unconditionalTail {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (n : ℕ) (x shift : ℝ) : ℝ :=
  (P.marginal.iid n).expect fun y ↦
    (conditionalProduct P y).event
      {z | threshold P n x + shift ≤ blockInformation P z y}

/-- The real-cap optimized capped quantity in Proposition 18. -/
noncomputable def optimizedCappedProfileValue
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) (n : ℕ) (x : ℝ) : ℝ :=
  PerspectiveAggregation.value
    (fun n y a ↦ fiberScaledCappedValue f P y x a)
    (fun n ↦ P.marginal.iid n) n

theorem joint_expect_information
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) :
    P.joint.expect (fun xy ↦ information P xy.1 xy.2) = entropy P := by
  rw [entropy, FinProb.expect, FinProb.expect, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [fiberEntropy, FinProb.expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [FiniteSource.joint_apply]
  ring

theorem conditional_second_moment_decomposition
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (y : Y) :
    (P.conditional y).expect
        (fun x ↦ (information P x y - entropy P) ^ 2) =
      fiberVariance P y + (fiberEntropy P y - entropy P) ^ 2 := by
  rw [fiberVariance, FinProb.expect, FinProb.expect]
  calc
    (∑ x, P.conditional y x * (information P x y - entropy P) ^ 2) =
        ∑ x, P.conditional y x *
          ((information P x y - fiberEntropy P y) ^ 2 +
            2 * (information P x y - fiberEntropy P y) *
              (fiberEntropy P y - entropy P) +
            (fiberEntropy P y - entropy P) ^ 2) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
    _ = (∑ x, P.conditional y x *
          (information P x y - fiberEntropy P y) ^ 2) +
        2 * (fiberEntropy P y - entropy P) *
          (∑ x, P.conditional y x *
            (information P x y - fiberEntropy P y)) +
        (fiberEntropy P y - entropy P) ^ 2 *
          (∑ x, P.conditional y x) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = (∑ x, P.conditional y x *
          (information P x y - fiberEntropy P y) ^ 2) +
        (fiberEntropy P y - entropy P) ^ 2 := by
          have hcenter : (∑ x, P.conditional y x *
              (information P x y - fiberEntropy P y)) = 0 := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
            rw [← Finset.sum_mul, (P.conditional y).sum_prob, one_mul]
            change fiberEntropy P y - fiberEntropy P y = 0
            ring
          rw [hcenter, (P.conditional y).sum_prob]
          ring
    _ = _ := rfl

theorem joint_information_variance
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) :
    finiteVariance P.joint (fun xy ↦ information P xy.1 xy.2) =
      totalVariance P := by
  unfold finiteVariance centered
  rw [joint_expect_information, FinProb.expect,
    Fintype.sum_prod_type, totalVariance, variance₁, variance₂,
    FinProb.expect, FinProb.expect]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ x, P.joint (x, y) *
        (information P x y - entropy P) ^ 2) =
        ∑ y, P.marginal y *
          ((P.conditional y).expect
            (fun x ↦ (information P x y - entropy P) ^ 2)) := by
              apply Finset.sum_congr rfl
              intro y _
              rw [FinProb.expect, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              simp only [FiniteSource.joint_apply]
              ring
    _ = ∑ y, P.marginal y *
          (fiberVariance P y + (fiberEntropy P y - entropy P) ^ 2) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [conditional_second_moment_decomposition]
    _ = (∑ y, P.marginal y * (fiberEntropy P y - entropy P) ^ 2) +
        ∑ y, P.marginal y * fiberVariance P y := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          ring
    _ = _ := rfl

/-- Splitting a word of pairs into its `X`- and `Y`-words. -/
def splitWordEquiv {X Y : Type} {n : ℕ} :
    (Fin n → X × Y) ≃ ((Fin n → X) × (Fin n → Y)) where
  toFun w := (λ i ↦ (w i).1, λ i ↦ (w i).2)
  invFun w i := (w.1 i, w.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

theorem unconditionalTail_eq_joint_event
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (n : ℕ) (x shift : ℝ) :
    unconditionalTail P n x shift =
      (P.joint.iid n).event
        {w | threshold P n x + shift ≤
          ∑ i, information P (w i).1 (w i).2} := by
  classical
  unfold unconditionalTail FinProb.expect FinProb.event
  simp_rw [Finset.sum_filter]
  calc
    (∑ y, (P.marginal.iid n) y *
        ∑ z, if z ∈ {z | threshold P n x + shift ≤ blockInformation P z y}
          then conditionalProduct P y z else 0) =
      ∑ y, ∑ z, if threshold P n x + shift ≤ blockInformation P z y
          then (P.marginal.iid n) y * conditionalProduct P y z else 0 := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            by_cases hz : threshold P n x + shift ≤ blockInformation P z y <;>
              simp [hz]
    _ = ∑ z, ∑ y, if threshold P n x + shift ≤ blockInformation P z y
          then (P.marginal.iid n) y * conditionalProduct P y z else 0 :=
      Finset.sum_comm
    _ = ∑ zy : (Fin n → X) × (Fin n → Y),
        if threshold P n x + shift ≤ blockInformation P zy.1 zy.2
          then (P.marginal.iid n) zy.2 * conditionalProduct P zy.2 zy.1 else 0 := by
            rw [Fintype.sum_prod_type]
    _ = ∑ w : Fin n → X × Y,
        if threshold P n x + shift ≤
            ∑ i, information P (w i).1 (w i).2
          then (P.joint.iid n) w else 0 := by
            apply Fintype.sum_equiv
              (splitWordEquiv (X := X) (Y := Y) (n := n)).symm
            intro zy
            rcases zy with ⟨z, y⟩
            have hsplit :
                (splitWordEquiv (X := X) (Y := Y) (n := n)).symm (z, y) =
                  (fun i ↦ (z i, y i)) := rfl
            rw [hsplit]
            by_cases hw : threshold P n x + shift ≤
                ∑ i, information P (z i) (y i)
            · simp only [blockInformation, hw, if_true,
                FinProb.iid_apply, FiniteSource.joint_apply,
                conditionalProduct_apply]
              rw [Finset.prod_mul_distrib]
            · simp only [blockInformation, hw, if_false]
    _ = _ := rfl

theorem unconditionalTail_berryEsseen_bound
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    {n : ℕ} (hn : 0 < n) (hV : 0 < totalVariance P)
    (x shift : ℝ) :
    |unconditionalTail P n x shift -
        gaussianCDF (x - shift /
          Real.sqrt ((n : ℝ) * totalVariance P))| ≤
      berryEsseenConstant hBE *
        ((n : ℝ) * finiteThirdMoment P.joint
          (fun xy ↦ information P xy.1 xy.2)) /
        (Real.sqrt ((n : ℝ) * totalVariance P)) ^ 3 := by
  let g : X × Y → ℝ := fun xy ↦ information P xy.1 xy.2
  have hvar : 0 < P.joint.expect
      (fun a ↦ (centered P.joint g a) ^ 2) := by
    change 0 < finiteVariance P.joint g
    rw [joint_information_variance]
    exact hV
  have hraw := iid_berryEsseen hBE P.joint
    (centered P.joint g) (expect_centered P.joint g) n hn
    hvar
    (x - shift / Real.sqrt ((n : ℝ) * totalVariance P))
  have hevent : (P.joint.iid n).event
      {w | -(x - shift / Real.sqrt ((n : ℝ) * totalVariance P)) ≤
        (∑ i, centered P.joint g (w i)) /
          Real.sqrt ((n : ℝ) *
            P.joint.expect (fun a ↦ (centered P.joint g a) ^ 2))} =
      unconditionalTail P n x shift := by
    rw [unconditionalTail_eq_joint_event]
    apply congrArg (P.joint.iid n).event
    ext w
    simp only [Set.mem_setOf_eq]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsqrt : 0 < Real.sqrt ((n : ℝ) * totalVariance P) :=
      Real.sqrt_pos.2 (mul_pos hnR hV)
    rw [show P.joint.expect (fun a ↦ (centered P.joint g a) ^ 2) =
      totalVariance P by
        change finiteVariance P.joint g = totalVariance P
        exact joint_information_variance P]
    simp only [centered, g, joint_expect_information]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by simp
    rw [hcard]
    unfold threshold
    rw [le_div_iff₀ hsqrt]
    have hcalc :
        -(x - shift / Real.sqrt ((n : ℝ) * totalVariance P)) *
            Real.sqrt ((n : ℝ) * totalVariance P) =
          -x * Real.sqrt ((n : ℝ) * totalVariance P) + shift := by
      field_simp [hsqrt.ne']
      ring
    rw [hcalc]
    constructor <;> intro h <;> linarith
  rw [hevent] at hraw
  have hvEq : P.joint.expect (fun a ↦ (centered P.joint g a) ^ 2) =
      totalVariance P := by
    change finiteVariance P.joint g = totalVariance P
    exact joint_information_variance P
  rw [hvEq] at hraw
  simpa only [finiteThirdMoment] using hraw

theorem unconditionalTail_tendsto
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hV : 0 < totalVariance P) (x : ℝ)
    (tau : ℕ → ℝ)
    (htau : Tendsto (fun n ↦ tau n / Real.sqrt (n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun n ↦ unconditionalTail P n x (tau n)) atTop
      (nhds (gaussianCDF x)) := by
  have hparam : Tendsto
      (fun n ↦ x - tau n / Real.sqrt ((n : ℝ) * totalVariance P))
      atTop (nhds x) := by
    have hratio : Tendsto
        (fun n ↦ (tau n / Real.sqrt (n : ℝ)) /
          Real.sqrt (totalVariance P)) atTop (nhds 0) := by
      simpa using htau.div_const (Real.sqrt (totalVariance P))
    have heq : (fun n ↦ tau n / Real.sqrt ((n : ℝ) * totalVariance P)) =
        (fun n ↦ (tau n / Real.sqrt (n : ℝ)) /
          Real.sqrt (totalVariance P)) := by
      funext n
      by_cases hn : n = 0
      · simp [hn]
      · rw [Real.sqrt_mul (Nat.cast_nonneg n) (totalVariance P)]
        ring
    have hsmall : Tendsto
        (fun n ↦ tau n / Real.sqrt ((n : ℝ) * totalVariance P))
        atTop (nhds 0) := by rwa [heq]
    simpa using tendsto_const_nhds.sub hsmall
  have hphi : Tendsto
      (fun n ↦ gaussianCDF
        (x - tau n / Real.sqrt ((n : ℝ) * totalVariance P)))
      atTop (nhds (gaussianCDF x)) :=
    (continuous_gaussianCDF.continuousAt.tendsto.comp hparam)
  let R : ℕ → ℝ := fun n ↦ berryEsseenConstant hBE *
    ((n : ℝ) * finiteThirdMoment P.joint
      (fun xy ↦ information P xy.1 xy.2)) /
      (Real.sqrt ((n : ℝ) * totalVariance P)) ^ 3
  have hR : Tendsto R atTop (nhds 0) :=
    berryEsseen_iid_rate_tendsto_zero hBE
      (finiteThirdMoment P.joint (fun xy ↦ information P xy.1 xy.2))
      (totalVariance P) hV
  have hdiff : Tendsto (fun n ↦
      |unconditionalTail P n x (tau n) -
        gaussianCDF (x - tau n / Real.sqrt ((n : ℝ) * totalVariance P))|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · filter_upwards [eventually_gt_atTop 0] with n hn
      exact unconditionalTail_berryEsseen_bound hBE P hn hV x (tau n)
    · exact hR
  have hsub : Tendsto (fun n ↦ unconditionalTail P n x (tau n) -
      gaussianCDF (x - tau n / Real.sqrt ((n : ℝ) * totalVariance P)))
      atTop (nhds 0) := by
    let d : ℕ → ℝ := fun n ↦ unconditionalTail P n x (tau n) -
      gaussianCDF (x - tau n / Real.sqrt ((n : ℝ) * totalVariance P))
    change Tendsto d atTop (nhds 0)
    have hneg : Tendsto (fun n ↦ -|d n|) atTop (nhds 0) := by
      simpa [d] using hdiff.neg
    have habs : Tendsto (fun n ↦ |d n|) atTop (nhds 0) := by
      simpa [d] using hdiff
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg habs
    · exact Eventually.of_forall fun n ↦ neg_abs_le _
    · exact Eventually.of_forall fun n ↦ le_abs_self _
  convert hsub.add hphi using 1 <;> simp

theorem optimizedCappedProfileValue_tendsto_of_variance₂_pos
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV₂ : 0 < variance₂ P) (x : ℝ) :
    Tendsto (fun n ↦ optimizedCappedProfileValue f P n x) atTop
      (nhds (f (gaussianCDF x))) := by
  let π : ∀ n, FinProb (Fin n → Y) := fun n ↦ P.marginal.iid n
  let q : ∀ n, (Fin n → Y) → ℝ := fun _ y ↦ supportTail P y x
  let G : ∀ n, (Fin n → Y) → ℝ → ℝ :=
    fun _ y a ↦ fiberScaledCappedValue f P y x a
  let T : ∀ n, ℝ → Set (Fin n → Y) :=
    fun _ K ↦ {y | IsTypical P K y}
  have hV : 0 < totalVariance P := by
    unfold totalVariance
    linarith [variance₁_nonneg P]
  have havg : Tendsto (PerspectiveAggregation.average π q) atTop
      (nhds (gaussianCDF x)) := by
    have htail := unconditionalTail_tendsto hBE P hV x (fun _ ↦ 0)
      (by simpa using tendsto_const_nhds)
    change Tendsto (fun n ↦ (P.marginal.iid n).expect
      (fun y ↦ supportTail P y x)) atTop (nhds (gaussianCDF x))
    simpa [unconditionalTail, supportTail_eq_conditionalTail,
      conditionalTail] using htail
  have htight : PerspectiveAggregation.TightTypicalSets π T := by
    intro δ hδ
    obtain ⟨K, hK, h⟩ := typical_complement_small hBE P hpY hV₂ δ hδ
    refine ⟨K, hK, ?_⟩
    filter_upwards [h] with n hn
    simpa only [π, T, Set.compl_setOf] using hn
  have htail : PerspectiveAggregation.TypicalTailBounds q T := by
    intro K hK
    obtain ⟨η, hη0, hη1, h⟩ := typicalTail_boundedAway hBE P hV₂ x hK.le
    exact ⟨η, hη0, hη1, by simpa [q, T] using h⟩
  have hlocal : PerspectiveAggregation.TypicalLocalLimit f q G T := by
    intro K hK aMin aMax haMin haMax ε hε
    have h := uniformTypicalScaledApproximation hBE f P hpY hV₂ x hK
      aMin aMax haMin haMax ε hε
    filter_upwards [h] with n hn
    intro y hy a ha
    exact hn y hy a ha
  have hq0 : ∀ n y, 0 ≤ q n y := fun n y ↦ TailLimit.tailGE_nonneg _ _
  have hq1 : ∀ n y, q n y ≤ 1 := fun n y ↦ TailLimit.tailGE_le_one _ _
  have hGlower : ∀ n y a, 0 ≤ a → f a ≤ G n y a := by
    intro n y a ha
    exact (TailLimit.scaled_bounds f a _ ha
      (Real.rpow_nonneg (by norm_num) _) (fiberSupportLaw P y)).1
  have hGupper : ∀ n y a, 0 ≤ a → G n y a ≤ f 0 := by
    intro n y a ha
    exact (TailLimit.scaled_bounds f a _ ha
      (Real.rpow_nonneg (by norm_num) _) (fiberSupportLaw P y)).2
  have h15 := PerspectiveAggregation.paperLemma15 f π q G T
    (gaussianCDF x) (gaussianCDF_pos x) (gaussianCDF_lt_one x)
    hq0 hq1 hGlower hGupper havg htight htail hlocal
  simpa [optimizedCappedProfileValue, π, G] using h15

theorem endpointScale_pos
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) (x : ℝ) :
    0 < endpointScale P y x := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem endpointScale_ge_iff
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) (x δ : ℝ)
    (hδ : 0 < δ) :
    δ ≤ endpointScale P y x ↔
      threshold P n x + Real.logb 2 δ ≤ conditionalMean P y := by
  unfold endpointScale
  rw [← Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hδ]
  constructor <;> intro h <;> linarith

theorem unconditionalTail_eq_endpointScale_event
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV₂ : variance₂ P = 0) (n : ℕ) (x shift : ℝ) :
    unconditionalTail P n x shift =
      (P.marginal.iid n).event
        {y | threshold P n x + shift ≤ conditionalMean P y} := by
  unfold unconditionalTail
  change (P.marginal.iid n).expect
      (fun y ↦ shiftedConditionalTail P y x shift) = _
  simp_rw [shiftedConditionalTail_eq_indicator P hpY hV₂]
  simpa only [Set.mem_setOf_eq, one_mul] using
    (UniformEndpoint.expect_indicator (P.marginal.iid n)
      {y | threshold P n x + shift ≤ conditionalMean P y} 1)

theorem endpointScale_event_tendsto
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV₂ : variance₂ P = 0)
    (hV : 0 < totalVariance P) (x δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n ↦ (P.marginal.iid n).event
      {y | δ ≤ endpointScale P y x}) atTop (nhds (gaussianCDF x)) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹) atTop
      (nhds 0) := tendsto_inv_atTop_zero.comp hsqrt
  have hsmall : Tendsto
      (fun n : ℕ ↦ Real.logb 2 δ / Real.sqrt (n : ℝ)) atTop
      (nhds 0) := by
    have hc : Tendsto (fun _ : ℕ ↦ Real.logb 2 δ) atTop
        (nhds (Real.logb 2 δ)) := tendsto_const_nhds
    simpa [div_eq_mul_inv] using hc.mul hinv
  have htail := unconditionalTail_tendsto hBE P hV x
    (fun _ ↦ Real.logb 2 δ) hsmall
  apply htail.congr'
  exact Eventually.of_forall fun n ↦ by
    change unconditionalTail P n x (Real.logb 2 δ) = _
    rw [unconditionalTail_eq_endpointScale_event P hpY hV₂]
    apply congrArg (P.marginal.iid n).event
    ext y
    exact endpointScale_ge_iff P y x δ hδ |>.symm

theorem event_sdiff_eq_sub
    {A : Type} [Fintype A] (p : FinProb A) (S T : Set A)
    (hTS : T ⊆ S) :
    p.event (S \ T) = p.event S - p.event T := by
  classical
  unfold FinProb.event
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases haT : a ∈ T
  · have haS := hTS haT
    simp [haT, haS]
  · by_cases haS : a ∈ S <;> simp [haT, haS]

theorem endpointScale_strip_tendsto_zero
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV₂ : variance₂ P = 0)
    (hV : 0 < totalVariance P) (x δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Tendsto (fun n ↦ (P.marginal.iid n).event
      ({y | δ ≤ endpointScale P y x} \ {y | 1 ≤ endpointScale P y x}))
      atTop (nhds 0) := by
  have hC := endpointScale_event_tendsto hBE P hpY hV₂ hV x δ hδ
  have hH := endpointScale_event_tendsto hBE P hpY hV₂ hV x 1 zero_lt_one
  have hsub := hC.sub hH
  convert hsub using 1
  · funext n
    rw [event_sdiff_eq_sub]
    intro y hy
    exact hδ1.le.trans hy
  · simp

theorem endpoint_optimized_lower_bound
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV₂ : variance₂ P = 0)
    (n : ℕ) (x δ T ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hT : 1 < T) (hε : 0 ≤ ε)
    (hlarge : ∀ u : ℝ, T < u → |f u / u| ≤ ε) :
    f ((P.marginal.iid n).event {y | δ ≤ endpointScale P y x}) -
        δ * (f 0 - f T + f 0) - ε ≤
      optimizedCappedProfileValue f P n x := by
  let π : FinProb (Fin n → Y) := P.marginal.iid n
  let r : (Fin n → Y) → ℝ := fun y ↦
    if δ ≤ endpointScale P y x then 1 else 0
  let G : (Fin n → Y) → ℝ → ℝ := fun y a ↦
    fiberScaledCappedValue f P y x a
  have hT0 : 0 ≤ T := zero_le_one.trans hT.le
  have hfTle : f T ≤ f 0 :=
    f.antitoneOn_nonneg (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT0) hT0
  have hC0 : 0 ≤ f 0 - f T + f 0 := by
    linarith [f.map_zero_nonneg]
  have hr0 : ∀ y, 0 ≤ r y := by
    intro y
    simp only [r]
    split_ifs <;> norm_num
  have hrexpect : π.expect r =
      (P.marginal.iid n).event {y | δ ≤ endpointScale P y x} := by
    simpa only [π, r, Set.mem_setOf_eq, one_mul] using
      (UniformEndpoint.expect_indicator π
        {y | δ ≤ endpointScale P y x} 1)
  unfold optimizedCappedProfileValue PerspectiveAggregation.value
  apply le_csInf
  · exact ⟨PerspectiveAggregation.objective
      (fun _ y a ↦ fiberScaledCappedValue f P y x a)
      (fun _ ↦ P.marginal.iid n) n π, π, rfl⟩
  · rintro v ⟨R, rfl⟩
    have hj := PerspectiveAggregation.weighted_modifiedTail_jensen
      (E := fun _ : ℕ ↦ Fin n → Y) (n := 0) f π R r hr0
    rw [hrexpect] at hj
    have hpoint (y : Fin n → Y) :
        (if R y = 0 then 0 else R y * f ((π y / R y) * r y)) -
            (R y * δ * (f 0 - f T + f 0) + π y * ε) ≤
          if R y = 0 then 0 else R y * G y (π y / R y) := by
      by_cases hR0 : R y = 0
      · simp [hR0]
        exact mul_nonneg (π.nonneg y) hε
      have hRpos : 0 < R y := lt_of_le_of_ne (R.nonneg y) (Ne.symm hR0)
      let a := π y / R y
      let s := endpointScale P y x
      let u := a / s
      have ha : 0 ≤ a := div_nonneg (π.nonneg y) hRpos.le
      have hs : 0 < s := endpointScale_pos P y x
      have hu : 0 ≤ u := div_nonneg ha hs.le
      have hRa : R y * a = π y := by
        dsimp [a]
        field_simp [hR0]
      simp only [if_neg hR0]
      by_cases hyC : δ ≤ s
      · have hr1 : r y = 1 := by simp [r, s, hyC]
        rw [hr1, mul_one]
        have hGlow := (TailLimit.scaled_bounds f a
          ((2 : ℝ) ^ (-threshold P n x)) ha
          (Real.rpow_nonneg (by norm_num) _) (fiberSupportLaw P y)).1
        have herr0 : 0 ≤ R y * δ * (f 0 - f T + f 0) + π y * ε :=
          add_nonneg (mul_nonneg (mul_nonneg (R.nonneg y) hδ.le) hC0)
            (mul_nonneg (π.nonneg y) hε)
        change R y * f a -
            (R y * δ * (f 0 - f T + f 0) + π y * ε) ≤
          R y * G y a
        have hGlowG : f a ≤ G y a := hGlow
        exact (sub_le_self _ herr0).trans
          (mul_le_mul_of_nonneg_left hGlowG (R.nonneg y))
      · have hsδ : s < δ := lt_of_not_ge hyC
        have hs1 : s < 1 := hsδ.trans hδ1
        have hr0y : r y = 0 := by simp [r, s, hyC]
        rw [hr0y, mul_zero]
        have hGexact := fiberScaledCappedValue_uniform_exact f P hpY hV₂
          y x a ha
        rw [show endpointScale P y x = s by rfl,
          if_neg (not_le.mpr hs1)] at hGexact
        change R y * f 0 -
            (R y * δ * (f 0 - f T + f 0) + π y * ε) ≤
          R y * fiberScaledCappedValue f P y x a
        rw [hGexact]
        by_cases huT : u ≤ T
        · have hfTleu : f T ≤ f u :=
            f.antitoneOn_nonneg (Set.mem_Ici.mpr hu)
              (Set.mem_Ici.mpr hT0) huT
          have hfuLe0 : f u ≤ f 0 :=
            f.antitoneOn_nonneg (Set.mem_Ici.mpr le_rfl)
              (Set.mem_Ici.mpr hu) hu
          have hdiff0 : 0 ≤ f 0 - f u := sub_nonneg.mpr hfuLe0
          have hdiffC : f 0 - f u ≤ f 0 - f T + f 0 := by
            linarith [f.map_zero_nonneg]
          have hRs : R y * s ≤ R y * δ :=
            mul_le_mul_of_nonneg_left hsδ.le (R.nonneg y)
          have hloss : R y * s * (f 0 - f u) ≤
              R y * δ * (f 0 - f T + f 0) := by
            exact (mul_le_mul hRs hdiffC hdiff0
              (mul_nonneg (R.nonneg y) hδ.le))
          dsimp [u] at hloss
          have hpie : 0 ≤ π y * ε := mul_nonneg (π.nonneg y) hε
          nlinarith
        · have hTu : T < u := lt_of_not_ge huT
          have huPos : 0 < u := zero_lt_one.trans (hT.trans hTu)
          have hratio := hlarge u hTu
          have hlow : -ε ≤ f u / u := by linarith [neg_le_abs (f u / u)]
          have hmul := mul_le_mul_of_nonneg_right hlow huPos.le
          rw [div_mul_cancel₀ _ huPos.ne'] at hmul
          have hRsu : R y * s * u = π y := by
            dsimp [u, a]
            field_simp [hR0, hs.ne']
          have hsC : s * f 0 ≤ δ * (f 0 - f T + f 0) := by
            calc
              s * f 0 ≤ δ * f 0 :=
                mul_le_mul_of_nonneg_right hsδ.le f.map_zero_nonneg
              _ ≤ δ * (f 0 - f T + f 0) := by
                apply mul_le_mul_of_nonneg_left _ hδ.le
                linarith
          have hmain := mul_le_mul_of_nonneg_left hmul
            (mul_nonneg (R.nonneg y) hs.le)
          have hmain' : -(π y * ε) ≤ R y * s * f u := by
            calc
              -(π y * ε) = R y * s * (-ε * u) := by
                rw [← hRsu]
                ring
              _ ≤ R y * s * f u := hmain
          have hsCR := mul_le_mul_of_nonneg_left hsC (R.nonneg y)
          have hform : R y * (s * f (a / s) + (1 - s) * f 0) =
              R y * f 0 + R y * s * f u - R y * s * f 0 := by
            dsimp [u]
            ring
          rw [hform]
          linarith
    have hsum := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) ↦ hpoint y
    have herrsum :
        ∑ y, (R y * δ * (f 0 - f T + f 0) + π y * ε) =
          δ * (f 0 - f T + f 0) + ε := by
      rw [Finset.sum_add_distrib]
      simp_rw [mul_assoc]
      rw [← Finset.sum_mul, ← Finset.sum_mul, R.sum_prob, π.sum_prob]
      ring
    rw [Finset.sum_sub_distrib, herrsum] at hsum
    change (∑ y, if R y = 0 then 0 else
      R y * f ((π y / R y) * r y)) -
        (δ * (f 0 - f T + f 0) + ε) ≤ _ at hsum
    change f ((P.marginal.iid n).event {y | δ ≤ endpointScale P y x}) -
        δ * (f 0 - f T + f 0) - ε ≤
      ∑ y, if R y = 0 then 0 else R y * G y (π y / R y)
    linarith

theorem endpoint_optimized_upper_bound
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (hpY : ∀ y, 0 < P.marginal y) (hV₂ : variance₂ P = 0)
    (n : ℕ) (x δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbar : 0 < (P.marginal.iid n).event
      {y | δ ≤ endpointScale P y x}) :
    optimizedCappedProfileValue f P n x ≤
      f ((P.marginal.iid n).event {y | δ ≤ endpointScale P y x}) +
        f 0 / ((P.marginal.iid n).event
          {y | δ ≤ endpointScale P y x}) *
          (P.marginal.iid n).event
            ({y | δ ≤ endpointScale P y x} \
              {y | 1 ≤ endpointScale P y x}) := by
  let π : FinProb (Fin n → Y) := P.marginal.iid n
  let C : Set (Fin n → Y) := {y | δ ≤ endpointScale P y x}
  let H : Set (Fin n → Y) := {y | 1 ≤ endpointScale P y x}
  let bar : ℝ := π.event C
  have hbar' : 0 < bar := by simpa [bar, π, C] using hbar
  let R : FinProb (Fin n → Y) :=
    { prob := fun y ↦ if y ∈ C then π y / bar else 0
      nonneg := fun y ↦ by
        split_ifs
        · exact div_nonneg (π.nonneg y) hbar'.le
        · exact le_rfl
      sum_prob := by
        change (∑ y, if y ∈ C then π y / bar else 0) = 1
        calc
          (∑ y, if y ∈ C then π y / bar else 0) =
              (∑ y, if y ∈ C then π y else 0) * bar⁻¹ := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro y _
                by_cases hy : y ∈ C <;> simp [hy, div_eq_mul_inv]
          _ = bar * bar⁻¹ := by
                congr 1
                unfold bar FinProb.event
                simp only [Finset.sum_filter]
          _ = 1 := mul_inv_cancel₀ hbar'.ne' }
  let πs : ∀ m, FinProb (Fin m → Y) := fun m ↦ P.marginal.iid m
  let G : ∀ m, (Fin m → Y) → ℝ → ℝ :=
    fun _ y a ↦ fiberScaledCappedValue f P y x a
  let q : ∀ m, (Fin m → Y) → ℝ := fun _ _ ↦ 0
  have hGlower : ∀ m y a, 0 ≤ a → f a ≤ G m y a := by
    intro m y a ha
    exact (TailLimit.scaled_bounds f a _ ha
      (Real.rpow_nonneg (by norm_num) _) (fiberSupportLaw P y)).1
  have hvle := PerspectiveAggregation.value_le_objective f πs q G hGlower n R
  change optimizedCappedProfileValue f P n x ≤ _ at hvle
  have hbar0 : 0 ≤ bar := hbar'.le
  have hbar1 : bar ≤ 1 := π.event_le_one C
  have hfbar0 : 0 ≤ f bar := f.nonneg_of_mem_unit hbar0 hbar1
  have hpoint (y : Fin n → Y) :
      (if R y = 0 then 0 else R y * G n y (π y / R y)) ≤
        R y * f bar +
          (if y ∈ C \ H then (π y / bar) * f 0 else 0) := by
    by_cases hyC : y ∈ C
    · have hπpos : 0 < π y := by
        dsimp [π]
        exact Finset.prod_pos fun i _ ↦ hpY (y i)
      have hRy : R y = π y / bar := by simp [R, hyC]
      have hRpos : 0 < R y := by rw [hRy]; exact div_pos hπpos hbar'
      have hscale : π y / R y = bar := by
        rw [hRy]
        field_simp [hπpos.ne', hbar'.ne']
      simp only [if_neg hRpos.ne']
      rw [hscale]
      by_cases hyH : y ∈ H
      · have hsHigh : 1 ≤ endpointScale P y x := hyH
        have hGexact := fiberScaledCappedValue_uniform_exact f P hpY hV₂
          y x bar hbar0
        rw [if_pos hsHigh] at hGexact
        have hynot : y ∉ C \ H := by simp [hyH]
        rw [if_neg hynot, add_zero]
        change R y * fiberScaledCappedValue f P y x bar ≤ R y * f bar
        rw [hGexact]
      · have hyStrip : y ∈ C \ H := ⟨hyC, hyH⟩
        rw [if_pos hyStrip]
        have hGupper : G n y bar ≤ f 0 :=
          (TailLimit.scaled_bounds f bar
            ((2 : ℝ) ^ (-threshold P n x)) hbar0
            (Real.rpow_nonneg (by norm_num) _) (fiberSupportLaw P y)).2
        rw [hRy]
        have hnonneg : 0 ≤ (π y / bar) * f bar :=
          mul_nonneg (div_nonneg (π.nonneg y) hbar0) hfbar0
        linarith [mul_le_mul_of_nonneg_left hGupper
          (div_nonneg (π.nonneg y) hbar0)]
    · have hRy : R y = 0 := by simp [R, hyC]
      have hynot : y ∉ C \ H := by simp [hyC]
      simp [hRy, hynot]
  have hsum := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) ↦ hpoint y
  have hfirst : ∑ y, R y * f bar = f bar := by
    rw [← Finset.sum_mul, R.sum_prob, one_mul]
  have hsecond :
      ∑ y, (if y ∈ C \ H then (π y / bar) * f 0 else 0) =
        f 0 / bar * π.event (C \ H) := by
    unfold FinProb.event
    simp only [Finset.sum_filter]
    simp_rw [div_eq_mul_inv]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ C \ H <;> simp [hy]
    ring
  rw [Finset.sum_add_distrib, hfirst, hsecond] at hsum
  exact hvle.trans (by
    simpa [PerspectiveAggregation.objective, πs, π, G] using hsum)

theorem optimizedCappedProfileValue_tendsto_of_variance₂_zero
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV₂ : variance₂ P = 0) (hV : 0 < totalVariance P) (x : ℝ) :
    Tendsto (fun n ↦ optimizedCappedProfileValue f P n x) atTop
      (nhds (f (gaussianCDF x))) := by
  let q₀ := gaussianCDF x
  have hq₀ : 0 < q₀ := gaussianCDF_pos x
  have hq₁ : q₀ < 1 := gaussianCDF_lt_one x
  rw [Metric.tendsto_nhds]
  intro e he
  let κ := e / 8
  have hκ : 0 < κ := div_pos he (by norm_num)
  have hsub := f.sublinear_atTop.eventually (Metric.ball_mem_nhds 0 hκ)
  have hsub' : ∀ᶠ u : ℝ in atTop, |f u / u| < κ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsub
  obtain ⟨A, hA⟩ := eventually_atTop.1 hsub'
  let T := max A 2
  have hT : 1 < T := lt_of_lt_of_le (by norm_num) (le_max_right A 2)
  have hlarge : ∀ u : ℝ, T < u → |f u / u| ≤ κ := by
    intro u hu
    exact (hA u ((le_max_left A 2).trans hu.le)).le
  have hT0 : 0 ≤ T := zero_le_one.trans hT.le
  have hfTle : f T ≤ f 0 :=
    f.antitoneOn_nonneg (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT0) hT0
  let C₀ := f 0 - f T + f 0
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    linarith [f.map_zero_nonneg]
  let δ := min (1 / 2) (e / (8 * (C₀ + 1)))
  have hden : 0 < 8 * (C₀ + 1) := mul_pos (by norm_num) (by linarith)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos he hden)
  have hδ1 : δ < 1 := (min_le_left (1 / 2) _).trans_lt (by norm_num)
  have herror : δ * C₀ + κ ≤ e / 4 := by
    have hδle : δ ≤ e / (8 * (C₀ + 1)) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hδle hC₀
    have hfrac : e / (8 * (C₀ + 1)) * C₀ ≤ e / 8 := by
      have heq : e / 8 = e * (C₀ + 1) / (8 * (C₀ + 1)) := by
        field_simp [show (8 : ℝ) ≠ 0 by norm_num,
          show C₀ + 1 ≠ 0 by linarith]
      rw [div_mul_eq_mul_div, heq]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : C₀ ≤ C₀ + 1) he.le)
        hden.le
    dsimp [κ]
    linarith [hmul.trans hfrac]
  obtain ⟨η, hη, hfcont⟩ :=
    (Metric.continuousAt_iff.1 f.continuous.continuousAt) (e / 4)
      (div_pos he (by norm_num))
  let radius := min η (q₀ / 2)
  have hradius : 0 < radius := lt_min hη (div_pos hq₀ (by norm_num))
  let B := 2 * f 0 / q₀
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (by norm_num) f.map_zero_nonneg) hq₀.le
  let stripRadius := e / (8 * (B + 1))
  have hstripRadius : 0 < stripRadius :=
    div_pos he (mul_pos (by norm_num) (by linarith))
  have hC := endpointScale_event_tendsto hBE P hpY hV₂ hV x δ hδ
  have hstrip := endpointScale_strip_tendsto_zero hBE P hpY hV₂ hV
    x δ hδ hδ1
  have hCEv := hC.eventually (Metric.ball_mem_nhds q₀ hradius)
  have hstripEv := hstrip.eventually
    (Metric.ball_mem_nhds 0 hstripRadius)
  filter_upwards [hCEv, hstripEv] with n hnC hnstrip
  let bar := (P.marginal.iid n).event {y | δ ≤ endpointScale P y x}
  let strip := (P.marginal.iid n).event
    ({y | δ ≤ endpointScale P y x} \ {y | 1 ≤ endpointScale P y x})
  have hbarClose : dist bar q₀ < radius := hnC
  have hbarCloseη : dist bar q₀ < η :=
    hbarClose.trans_le (min_le_left _ _)
  have hfclose : dist (f bar) (f q₀) < e / 4 := hfcont hbarCloseη
  have hbarHalf : q₀ / 2 < bar := by
    rw [Real.dist_eq, abs_lt] at hbarClose
    have hrle : radius ≤ q₀ / 2 := min_le_right _ _
    linarith [hbarClose.1]
  have hbarPos : 0 < bar := (div_pos hq₀ (by norm_num)).trans hbarHalf
  have hstrip0 : 0 ≤ strip := (P.marginal.iid n).event_nonneg _
  have hstripSmall : strip < stripRadius := by
    change dist strip 0 < stripRadius at hnstrip
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hstrip0] at hnstrip
    exact hnstrip
  have hcoef : f 0 / bar ≤ B := by
    dsimp [B]
    calc
      f 0 / bar ≤ f 0 / (q₀ / 2) :=
        div_le_div_of_nonneg_left f.map_zero_nonneg
          (div_pos hq₀ (by norm_num)) hbarHalf.le
      _ = 2 * f 0 / q₀ := by
        field_simp [hq₀.ne']
  have hstripTerm : f 0 / bar * strip < e / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hstripSmall.le hB
    have hBcalc : B * stripRadius < e / 8 := by
      have hBden : 0 < B + 1 := by linarith
      have hratio : B / (B + 1) < 1 := (div_lt_one hBden).2 (by linarith)
      calc
        B * stripRadius = (e / 8) * (B / (B + 1)) := by
          dsimp [stripRadius]
          field_simp [show (8 : ℝ) ≠ 0 by norm_num, hBden.ne']
        _ < (e / 8) * 1 :=
          mul_lt_mul_of_pos_left hratio (div_pos he (by norm_num))
        _ = e / 8 := mul_one _
    exact (mul_le_mul_of_nonneg_right hcoef hstrip0).trans_lt
      (hmul.trans_lt hBcalc)
  have hlo := endpoint_optimized_lower_bound f P hpY hV₂ n x δ T κ
    hδ hδ1 hT hκ.le hlarge
  have hup := endpoint_optimized_upper_bound f P hpY hV₂ n x δ hδ hδ1
    (by simpa [bar] using hbarPos)
  change dist (optimizedCappedProfileValue f P n x) (f q₀) < e
  rw [Real.dist_eq, abs_lt]
  rw [Real.dist_eq, abs_lt] at hfclose
  dsimp [bar, strip] at hlo hup hstripTerm ⊢
  constructor <;> linarith

/-- **Proposition 18 (Optimized Gaussian `f`-profile).**  The optimized
capped program converges to `f (Φ(x))`; every admissibly shifted
unconditional surprisal tail converges to `Φ(x)`. -/
theorem paperProposition18
    {X Y : Type} [Fintype X] [Fintype Y]
    (hBE : paperFact12.{0}) (f : AdmissibleGenerator)
    (P : FiniteSource X Y) (hpY : ∀ y, 0 < P.marginal y)
    (hV : 0 < totalVariance P) (x : ℝ) :
    Tendsto (fun n ↦ optimizedCappedProfileValue f P n x) atTop
        (nhds (f (gaussianCDF x))) ∧
      ∀ tau : ℕ → ℝ, AdmissibleShift tau →
        Tendsto (fun n ↦ unconditionalTail P n x (tau n)) atTop
          (nhds (gaussianCDF x)) := by
  constructor
  · by_cases hV₂zero : variance₂ P = 0
    · exact optimizedCappedProfileValue_tendsto_of_variance₂_zero
        hBE f P hpY hV₂zero hV x
    · have hV₂ : 0 < variance₂ P :=
        lt_of_le_of_ne (variance₂_nonneg P) (Ne.symm hV₂zero)
      exact optimizedCappedProfileValue_tendsto_of_variance₂_pos
        hBE f P hpY hV₂ x
  · intro tau htau
    exact unconditionalTail_tendsto hBE P hV x tau htau.2

end RandomnessExtraction
