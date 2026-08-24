import RandomnessExtraction.OptimizedProfile
import RandomnessExtraction.ProfileRegularity
import RandomnessExtraction.LightAchievability

/-!
# Operational asymptotics

This file supplies the finite-product and zero-padding identifications needed
to pass from Propositions 17--18 to the operational quantities of Theorem 1.
-/

open Filter Set
open scoped BigOperators Classical Topology

namespace RandomnessExtraction

open ConditionalLimit ConditionalCapped UniformEndpoint
open OneShot LightAchievability PerspectiveAggregation

/-- The `n`-fold source used in the operational statements. -/
def blockSource {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (n : ℕ) :
    FiniteSource (Fin n → X) (Fin n → Y) where
  marginal := P.marginal.iid n
  conditional := fun y ↦ conditionalProduct P y

@[simp]
theorem blockSource_marginal {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (n : ℕ) :
    (blockSource P n).marginal = P.marginal.iid n := rfl

@[simp]
theorem blockSource_conditional {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (n : ℕ) (y : Fin n → Y) :
    (blockSource P n).conditional y = conditionalProduct P y := rfl

private theorem perspective_zero_left (f : AdmissibleGenerator) {q : ℝ}
    (hq : 0 ≤ q) : perspective f 0 q = q * f 0 := by
  rcases hq.eq_or_lt with rfl | hq
  · simp [perspective]
  · rw [perspective_of_pos f hq]
    simp

private def restrictCapped {A : Type} [Fintype A] (p : FinProb A)
    {c : ℝ} (q : CappedVector A c) : CappedVector (Support p) c where
  mass x := q x.1
  nonneg x := q.nonneg x.1
  le_cap x := q.le_cap x.1
  sum_le_one := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x ↦ 0 < p x) q
    have hcomp : 0 ≤ ∑ x : {x : A // ¬ 0 < p x}, q x.1 :=
      Finset.sum_nonneg fun x _ ↦ q.nonneg x.1
    linarith [q.sum_le_one]

private noncomputable def extendCapped {A : Type} [Fintype A] (p : FinProb A)
    {c : ℝ} (hc : 0 ≤ c) (q : CappedVector (Support p) c) :
    CappedVector A c where
  mass x := if hx : 0 < p x then q ⟨x, hx⟩ else 0
  nonneg x := by split_ifs with hx; exact q.nonneg _; exact le_rfl
  le_cap x := by split_ifs with hx; exact q.le_cap _; exact hc
  sum_le_one := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x ↦ 0 < p x)
      (fun x ↦ if hx : 0 < p x then q ⟨x, hx⟩ else 0)
    have hleft : (∑ x : Support p,
        (if hx : 0 < p x.1 then q ⟨x.1, hx⟩ else 0)) = ∑ x, q x := by
      apply Finset.sum_congr rfl
      intro x _
      simp [x.2]
    have hright : (∑ x : {x : A // ¬ 0 < p x},
        (if hx : 0 < p x.1 then q ⟨x.1, hx⟩ else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      simp [x.2]
    rw [hleft, hright, add_zero] at hsplit
    rw [← hsplit]
    exact q.sum_le_one

private theorem extendCapped_sum {A : Type} [Fintype A] (p : FinProb A)
    {c : ℝ} (hc : 0 ≤ c) (q : CappedVector (Support p) c) :
    ∑ x, extendCapped p hc q x = ∑ x, q x := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x ↦ 0 < p x)
    (extendCapped p hc q)
  have hleft : (∑ x : Support p, extendCapped p hc q x.1) = ∑ x, q x := by
    apply Finset.sum_congr rfl
    intro x _
    simp [extendCapped, x.2]
  have hright : (∑ x : {x : A // ¬ 0 < p x},
      extendCapped p hc q x.1) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    simp [extendCapped, x.2]
  linarith

private theorem restrictCapped_cost {A : Type} [Fintype A]
    (f : AdmissibleGenerator) (a : ℝ) (p : FinProb A) {c : ℝ}
    (q : CappedVector A c) :
    scaledCappedCost f a (supportLaw p) (restrictCapped p q) =
      scaledCappedCost f a p q := by
  have hsplitP := Fintype.sum_subtype_add_sum_subtype (fun x ↦ 0 < p x)
    (fun x ↦ perspective f (a * p x) (q x))
  have hsplitQ := Fintype.sum_subtype_add_sum_subtype (fun x ↦ 0 < p x) q
  have hzeroP : (∑ x : {x : A // ¬ 0 < p x},
      perspective f (a * p x.1) (q x.1)) =
      (∑ x : {x : A // ¬ 0 < p x}, q x.1) * f 0 := by
    calc
      _ = ∑ x : {x : A // ¬ 0 < p x}, q x.1 * f 0 := by
        apply Finset.sum_congr rfl
        intro x _
        have hpx : p x.1 = 0 := le_antisymm (le_of_not_gt x.2) (p.nonneg x.1)
        rw [hpx, mul_zero, perspective_zero_left f (q.nonneg x.1)]
      _ = _ := by rw [Finset.sum_mul]
  unfold scaledCappedCost
  simp only [supportLaw_apply, restrictCapped]
  rw [← hsplitP, hzeroP, ← hsplitQ]
  ring

private theorem extendCapped_cost {A : Type} [Fintype A]
    (f : AdmissibleGenerator) (a : ℝ) (p : FinProb A) {c : ℝ}
    (hc : 0 ≤ c) (q : CappedVector (Support p) c) :
    scaledCappedCost f a p (extendCapped p hc q) =
      scaledCappedCost f a (supportLaw p) q := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x ↦ 0 < p x)
    (fun x ↦ perspective f (a * p x) (extendCapped p hc q x))
  have hleft : (∑ x : Support p,
      perspective f (a * p x.1) (extendCapped p hc q x.1)) =
      ∑ x : Support p, perspective f (a * supportLaw p x) (q x) := by
    apply Finset.sum_congr rfl
    intro x _
    simp [extendCapped, x.2]
  have hright : (∑ x : {x : A // ¬ 0 < p x},
      perspective f (a * p x.1) (extendCapped p hc q x.1)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hpx : p x.1 = 0 := le_antisymm (le_of_not_gt x.2) (p.nonneg x.1)
    simp [extendCapped, x.2, hpx, perspective]
  unfold scaledCappedCost
  rw [← hsplit, hleft, hright, add_zero, extendCapped_sum]

/-- Adding or deleting zero-probability coordinates does not change the
capped program. -/
theorem scaledCappedValue_supportLaw {A : Type} [Fintype A]
    (f : AdmissibleGenerator) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (p : FinProb A) :
    scaledCappedValue f a c (supportLaw p) = scaledCappedValue f a c p := by
  apply le_antisymm
  · rw [scaledCappedValue]
    apply le_csInf
    · exact ⟨scaledCappedCost f a p (CappedVector.zero hc),
          CappedVector.zero hc, rfl⟩
    · rintro v ⟨q, rfl⟩
      have h := CappedCost.scaledCappedValue_le_cost f a c ha
        (supportLaw p) (restrictCapped p q)
      rwa [restrictCapped_cost] at h
  · rw [scaledCappedValue]
    apply le_csInf
    · exact ⟨scaledCappedCost f a (supportLaw p) (CappedVector.zero hc),
          CappedVector.zero hc, rfl⟩
    · rintro v ⟨q, rfl⟩
      have h := CappedCost.scaledCappedValue_le_cost f a c ha p
        (extendCapped p hc q)
      rwa [extendCapped_cost] at h

private def widenCapped {A : Type} [Fintype A] {c d : ℝ}
    (hcd : c ≤ d) (q : CappedVector A c) : CappedVector A d where
  mass := q
  nonneg := q.nonneg
  le_cap x := (q.le_cap x).trans hcd
  sum_le_one := q.sum_le_one

private theorem widenCapped_cost {A : Type} [Fintype A]
    (f : AdmissibleGenerator) (a : ℝ) (p : FinProb A) {c d : ℝ}
    (hcd : c ≤ d) (q : CappedVector A c) :
    scaledCappedCost f a p (widenCapped hcd q) = scaledCappedCost f a p q := rfl

/-- Enlarging the coordinate cap enlarges the feasible set and can only
decrease the capped value. -/
theorem scaledCappedValue_antitone_cap {A : Type} [Fintype A]
    (f : AdmissibleGenerator) (a : ℝ) (p : FinProb A) {c d : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hcd : c ≤ d) :
    scaledCappedValue f a d p ≤ scaledCappedValue f a c p := by
  rw [scaledCappedValue]
  apply le_csInf
  · exact ⟨scaledCappedCost f a p (CappedVector.zero hc),
        CappedVector.zero hc, rfl⟩
  · rintro v ⟨q, rfl⟩
    have h := CappedCost.scaledCappedValue_le_cost f a d ha p
      (widenCapped hcd q)
    rwa [widenCapped_cost] at h

private def equivCapped {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) {c : ℝ} (q : CappedVector B c) : CappedVector A c where
  mass a := q (e a)
  nonneg a := q.nonneg (e a)
  le_cap a := q.le_cap (e a)
  sum_le_one := by
    calc
      (∑ a, q (e a)) = ∑ b, q b :=
        Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
      _ ≤ 1 := q.sum_le_one

private theorem equivCapped_cost {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : AdmissibleGenerator) (a : ℝ)
    (pA : FinProb A) (pB : FinProb B) (hp : ∀ x, pA x = pB (e x))
    {c : ℝ} (q : CappedVector B c) :
    scaledCappedCost f a pA (equivCapped e q) =
      scaledCappedCost f a pB q := by
  unfold scaledCappedCost
  have hP : (∑ x, perspective f (a * pA x) (equivCapped e q x)) =
      ∑ y, perspective f (a * pB y) (q y) := by
    apply Fintype.sum_equiv e
    intro x
    simp [equivCapped, hp]
  have hQ : (∑ x, equivCapped e q x) = ∑ y, q y := by
    exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  rw [hP, hQ]

theorem scaledCappedValue_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : AdmissibleGenerator) (a c : ℝ) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (pA : FinProb A) (pB : FinProb B)
    (hp : ∀ x, pA x = pB (e x)) :
    scaledCappedValue f a c pA = scaledCappedValue f a c pB := by
  apply le_antisymm
  · rw [scaledCappedValue]
    apply le_csInf
    · exact ⟨scaledCappedCost f a pB (CappedVector.zero hc),
          CappedVector.zero hc, rfl⟩
    · rintro v ⟨q, rfl⟩
      have h := CappedCost.scaledCappedValue_le_cost f a c ha pA
        (equivCapped e q)
      rwa [equivCapped_cost e f a pA pB hp] at h
  · have hp' : ∀ y, pB y = pA (e.symm y) := by
      intro y
      simpa using (hp (e.symm y)).symm
    rw [scaledCappedValue]
    apply le_csInf
    · exact ⟨scaledCappedCost f a pA (CappedVector.zero hc),
          CappedVector.zero hc, rfl⟩
    · rintro v ⟨q, rfl⟩
      have h := CappedCost.scaledCappedValue_le_cost f a c ha pB
        (equivCapped e.symm q)
      rwa [equivCapped_cost e.symm f a pB pA hp'] at h

theorem fiber_scaledCappedValue_eq_full
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) {n : ℕ}
    (y : Fin n → Y) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    scaledCappedValue f a c (fiberSupportLaw P y) =
      scaledCappedValue f a c (conditionalProduct P y) := by
  calc
    scaledCappedValue f a c (fiberSupportLaw P y) =
        scaledCappedValue f a c (supportLaw (conditionalProduct P y)) :=
      scaledCappedValue_equiv (fiberSupportEquiv P y) f a c ha hc
        (fiberSupportLaw P y) (supportLaw (conditionalProduct P y))
        (fiberSupportLaw_eq_supportLaw_under_equiv P y)
    _ = scaledCappedValue f a c (conditionalProduct P y) :=
      scaledCappedValue_supportLaw f a c ha hc (conditionalProduct P y)

/-- The integer-cap fixed converse quantity is exactly the real-threshold
quantity of Proposition 17 when their caps agree. -/
theorem fixedGamma_eq_endpointCappedAverage
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) (n M : ℕ) (x : ℝ)
    (hM : 0 < M)
    (hcap : (M : ℝ)⁻¹ = (2 : ℝ) ^ (-threshold P n x)) :
    fixedGamma f (blockSource P n) M = endpointCappedAverage f P n x := by
  unfold fixedGamma endpointCappedAverage fiberScaledCappedValue cappedValue
  apply congrArg (P.marginal.iid n).expect
  funext y
  simp only [blockSource_conditional]
  rw [hcap]
  exact (fiber_scaledCappedValue_eq_full f P y 1 _ zero_le_one
    (Real.rpow_nonneg (by norm_num) _)).symm

private theorem optimizedGammaObjective_eq_profileObjective
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) (n M : ℕ) (x : ℝ)
    (hM : 0 < M)
    (hcap : (M : ℝ)⁻¹ = (2 : ℝ) ^ (-threshold P n x))
    (Q : FinProb (Fin n → Y)) :
    optimizedGammaObjective f (blockSource P n) M Q =
      PerspectiveAggregation.objective
        (fun n y a ↦ fiberScaledCappedValue f P y x a)
        (fun n ↦ P.marginal.iid n) n Q := by
  unfold optimizedGammaObjective PerspectiveAggregation.objective
  apply Finset.sum_congr rfl
  intro y _
  by_cases hQ : Q y = 0
  · simp [gammaTerm, hQ]
  · have hQpos : 0 < Q y := lt_of_le_of_ne (Q.nonneg y) (Ne.symm hQ)
    simp only [gammaTerm, hQ, if_false, fiberScaledCappedValue]
    simp only [blockSource_marginal, blockSource_conditional]
    congr 1
    rw [hcap]
    exact (fiber_scaledCappedValue_eq_full f P y
      ((P.marginal.iid n) y / Q y) _
      (div_nonneg ((P.marginal.iid n).nonneg y) hQpos.le)
      (Real.rpow_nonneg (by norm_num) _)).symm

/-- The integer-cap optimized converse quantity is exactly the real-threshold
quantity of Proposition 18 when their caps agree. -/
theorem optimizedGamma_eq_optimizedCappedProfileValue
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) (n M : ℕ) (x : ℝ)
    (hM : 0 < M)
    (hcap : (M : ℝ)⁻¹ = (2 : ℝ) ^ (-threshold P n x)) :
    optimizedGamma f (blockSource P n) M =
      optimizedCappedProfileValue f P n x := by
  unfold optimizedGamma optimizedCappedProfileValue PerspectiveAggregation.value
  congr 1
  ext v
  constructor
  · rintro ⟨Q, rfl⟩
    refine ⟨Q, ?_⟩
    exact optimizedGammaObjective_eq_profileObjective f P n M x hM hcap Q
  · rintro ⟨Q, rfl⟩
    refine ⟨Q, ?_⟩
    exact (optimizedGammaObjective_eq_profileObjective f P n M x hM hcap Q).symm

theorem lightMass_eq_tailGE_of_cap {A : Type} [Fintype A]
    (p : FinProb A) (M : ℕ) (tau h : ℝ)
    (hcap : (2 : ℝ) ^ (-tau) / (M : ℝ) = (2 : ℝ) ^ (-h)) :
    lightMass p M tau = TailLimit.tailGE (supportLaw p) h := by
  classical
  unfold lightMass lightPart TailLimit.tailGE TailLimit.eventProbability
  simp only [Finset.sum_filter]
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x ↦ 0 < p x)
    (fun x ↦ if p x ≤ (2 : ℝ) ^ (-tau) / (M : ℝ) then p x else 0)
  have hzero : (∑ x : {x : A // ¬ 0 < p x},
      if p x.1 ≤ (2 : ℝ) ^ (-tau) / (M : ℝ) then p x.1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hp0 : p x.1 = 0 := le_antisymm (le_of_not_gt x.2) (p.nonneg x.1)
    simp [hp0]
  rw [hzero, add_zero] at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro x _
  rw [hcap]
  have heq : p x.1 ≤ (2 : ℝ) ^ (-h) ↔
      h ≤ ProbabilityRepresentation.surprisal (supportLaw p) x := by
    rw [← Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) x.2]
    simp [ProbabilityRepresentation.surprisal, supportLaw]
    constructor <;> intro hx <;> linarith
  by_cases hx : h ≤ ProbabilityRepresentation.surprisal (supportLaw p) x
  · rw [if_pos (heq.mpr hx), if_pos hx]
    exact (supportLaw_apply p x).symm
  · rw [if_neg (fun hp ↦ hx (heq.mp hp)), if_neg hx]

theorem fiberTail_eq_conditionalEvent
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y) (h : ℝ) :
    TailLimit.tailGE (supportLaw (conditionalProduct P y)) h =
      (conditionalProduct P y).event {z | h ≤ blockInformation P z y} := by
  classical
  let A : Set (Fin n → X) := {z | h ≤ blockInformation P z y}
  have hs := supportLaw_event (conditionalProduct P y) A
  unfold TailLimit.tailGE TailLimit.eventProbability
  simp only [Finset.sum_filter]
  calc
    (∑ w : Support (conditionalProduct P y),
        if h ≤ ProbabilityRepresentation.surprisal
            (supportLaw (conditionalProduct P y)) w
          then supportLaw (conditionalProduct P y) w else 0) =
      ∑ w : Support (conditionalProduct P y),
        if w.1 ∈ A then supportLaw (conditionalProduct P y) w else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          let z := (fiberSupportEquiv P y).symm w
          have hz : ProbabilityRepresentation.surprisal
              (supportLaw (conditionalProduct P y)) w =
              blockInformation P w.1 y := by
            have hsur := fiberSupport_surprisal_eq P y z
            have hlaw := fiberSupportLaw_eq_supportLaw_under_equiv P y z
            have hw : fiberSupportEquiv P y z = w :=
              (fiberSupportEquiv P y).apply_symm_apply w
            calc
              ProbabilityRepresentation.surprisal
                  (supportLaw (conditionalProduct P y)) w =
                  ProbabilityRepresentation.surprisal
                    (supportLaw (conditionalProduct P y))
                      (fiberSupportEquiv P y z) := by rw [hw]
              _ = ProbabilityRepresentation.surprisal (fiberSupportLaw P y) z := by
                unfold ProbabilityRepresentation.surprisal
                rw [hlaw]
              _ = fiberSurprisal P y z := hsur
              _ = blockInformation P w.1 y := by
                rw [← hw]
                rfl
          rw [hz]
          rfl
    _ = (conditionalProduct P y).event A := by
      simpa [FinProb.event, Finset.sum_filter] using hs
    _ = _ := rfl

theorem lightMass_eq_shiftedConditionalTail
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) {n : ℕ} (y : Fin n → Y)
    (M : ℕ) (x tau : ℝ)
    (hcap : (M : ℝ)⁻¹ = (2 : ℝ) ^ (-threshold P n x)) :
    lightMass (conditionalProduct P y) M tau =
      shiftedConditionalTail P y x tau := by
  have hcap' : (2 : ℝ) ^ (-tau) / (M : ℝ) =
      (2 : ℝ) ^ (-(threshold P n x + tau)) := by
    rw [div_eq_mul_inv, hcap, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [lightMass_eq_tailGE_of_cap _ M tau _ hcap',
    fiberTail_eq_conditionalEvent]
  rfl

theorem averageLightMass_eq_unconditionalTail
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (n M : ℕ) (x tau : ℝ)
    (hcap : (M : ℝ)⁻¹ = (2 : ℝ) ^ (-threshold P n x)) :
    averageLightMass (blockSource P n) M tau = unconditionalTail P n x tau := by
  unfold averageLightMass unconditionalTail
  apply congrArg (P.marginal.iid n).expect
  funext y
  exact lightMass_eq_shiftedConditionalTail P y M x tau hcap

private theorem threshold_antitone_parameter
    {X Y : Type} [Fintype X] [Fintype Y]
    (P : FiniteSource X Y) (n : ℕ) : Antitone (threshold P n) := by
  intro x₁ x₂ hx
  unfold threshold
  gcongr

theorem endpointCappedAverage_antitone
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) (n : ℕ) :
    Antitone (endpointCappedAverage f P n) := by
  intro x₁ x₂ hx
  unfold endpointCappedAverage fiberScaledCappedValue
  apply (P.marginal.iid n).expect_mono
  intro y
  apply scaledCappedValue_antitone_cap f 1 (fiberSupportLaw P y)
    zero_le_one (Real.rpow_nonneg (by norm_num) _)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have ht := threshold_antitone_parameter P n hx
  linarith

theorem optimizedCappedProfileValue_antitone
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : AdmissibleGenerator) (P : FiniteSource X Y) (n : ℕ) :
    Antitone (optimizedCappedProfileValue f P n) := by
  intro x₁ x₂ hx
  unfold optimizedCappedProfileValue PerspectiveAggregation.value
  apply le_csInf
  · let Q := P.marginal.iid n
    refine ⟨PerspectiveAggregation.objective
      (fun n y a ↦ fiberScaledCappedValue f P y x₁ a)
      (fun n ↦ P.marginal.iid n) n Q, Q, rfl⟩
  · rintro v ⟨Q, rfl⟩
    have hbdd : BddBelow {w : ℝ | ∃ R : FinProb (Fin n → Y),
        w = PerspectiveAggregation.objective
          (fun n e a ↦ fiberScaledCappedValue f P e x₂ a)
          (fun n ↦ P.marginal.iid n) n R} := by
      refine ⟨0, ?_⟩
      rintro w ⟨R, rfl⟩
      apply PerspectiveAggregation.objective_nonneg f
        (fun n ↦ P.marginal.iid n) (fun _ _ ↦ 0)
        (fun n e a ↦ fiberScaledCappedValue f P e x₂ a)
      intro m e a ha
      unfold fiberScaledCappedValue
      exact CappedCost.scaledCappedValue_lower f a _ ha
        (Real.rpow_nonneg (by norm_num) _) _
    calc
      sInf {w : ℝ | ∃ R : FinProb (Fin n → Y),
          w = PerspectiveAggregation.objective
            (fun n e a ↦ fiberScaledCappedValue f P e x₂ a)
            (fun n ↦ P.marginal.iid n) n R} ≤
          PerspectiveAggregation.objective
            (fun n e a ↦ fiberScaledCappedValue f P e x₂ a)
            (fun n ↦ P.marginal.iid n) n Q :=
        csInf_le hbdd ⟨Q, rfl⟩
      _ ≤ PerspectiveAggregation.objective
            (fun n e a ↦ fiberScaledCappedValue f P e x₁ a)
            (fun n ↦ P.marginal.iid n) n Q := by
        unfold PerspectiveAggregation.objective
        apply Finset.sum_le_sum
        intro e _
        by_cases hQ : Q e = 0
        · simp [hQ]
        · simp only [hQ, if_false]
          apply mul_le_mul_of_nonneg_left _ (Q.nonneg e)
          unfold fiberScaledCappedValue
          apply scaledCappedValue_antitone_cap f _ (fiberSupportLaw P e)
            (div_nonneg ((P.marginal.iid n).nonneg e) (Q.nonneg e))
            (Real.rpow_nonneg (by norm_num) _)
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          have ht := threshold_antitone_parameter P n hx
          linarith

/-- A reusable moving-parameter sandwich. -/
theorem tendsto_moving_of_antitone
    (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (u : ℕ → ℝ) (x : ℝ)
    (hanti : ∀ n, Antitone (F n))
    (hpoint : ∀ z, Tendsto (fun n ↦ F n z) atTop (nhds (g z)))
    (hg : ContinuousAt g x) (hu : Tendsto u atTop (nhds x)) :
    Tendsto (fun n ↦ F n (u n)) atTop (nhds (g x)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨eta, heta, hcont⟩ := (Metric.continuousAt_iff.1 hg)
    (eps / 3) (by linarith)
  let d := eta / 2
  have hd : 0 < d := div_pos heta (by norm_num)
  have hdl : dist (x - d) x < eta := by
    rw [Real.dist_eq]
    simpa [abs_of_nonneg hd.le, d] using hd
  have hdr : dist (x + d) x < eta := by
    rw [Real.dist_eq]
    simpa [abs_of_nonneg hd.le, d] using hd
  have hgl := hcont hdl
  have hgr := hcont hdr
  have huEv := hu.eventually (Metric.ball_mem_nhds x hd)
  have hlEv := (hpoint (x - d)).eventually
    (Metric.ball_mem_nhds _ (by linarith : 0 < eps / 3))
  have hrEv := (hpoint (x + d)).eventually
    (Metric.ball_mem_nhds _ (by linarith : 0 < eps / 3))
  filter_upwards [huEv, hlEv, hrEv] with n hun hln hrn
  rw [Real.dist_eq, abs_lt] at hun hln hrn hgl hgr ⊢
  have hleft := hanti n (show x - d ≤ u n by linarith [hun.1])
  have hright := hanti n (show u n ≤ x + d by linarith [hun.2])
  constructor <;> linarith

/-! ## Bounds needed to squeeze the operational infima -/

theorem fixedLeakage_nonneg
    {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (H : SeededHash X S M) (hM : 0 < M) :
    0 ≤ fixedLeakage f P H := by
  unfold fixedLeakage
  apply H.seed.expect_nonneg
  intro s
  apply P.marginal.expect_nonneg
  intro y
  have h := CappedCost.scaledCappedCost_lower f 1 zero_le_one
    (P.conditional y) (OneShot.vectorFromBins H (P.conditional y) hM s)
  rw [OneShot.scaled_bin_identity f 1 H (P.conditional y) hM s] at h
  simpa using h

theorem referenceLeakage_nonneg
    {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (H : SeededHash X S M) (hM : 0 < M) (R : FinProb (Y × S)) :
    0 ≤ referenceLeakage f P H R := by
  let p : (Y × S) × Fin M → ℝ := fun o ↦
    P.marginal o.1.1 * H.seed o.1.2 *
      OneShot.outputMass H (P.conditional o.1.1) o.1.2 o.2
  let q : (Y × S) × Fin M → ℝ := fun o ↦
    (M : ℝ)⁻¹ * R o.1
  have hp : ∀ o, 0 ≤ p o := by
    intro o
    exact mul_nonneg
      (mul_nonneg (P.marginal.nonneg _) (H.seed.nonneg _))
      (Finset.sum_nonneg fun _ _ ↦ (P.conditional _).nonneg _)
  have hq : ∀ o, 0 ≤ q o := by
    intro o
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg M)) (R.nonneg _)
  have hpsum : ∑ o, p o = 1 := by
    rw [Fintype.sum_prod_type]
    change ∑ ys : Y × S, ∑ z : Fin M,
      P.marginal ys.1 * H.seed ys.2 *
        OneShot.outputMass H (P.conditional ys.1) ys.2 z = 1
    have hout (ys : Y × S) :
        ∑ z : Fin M, OneShot.outputMass H (P.conditional ys.1) ys.2 z = 1 := by
      calc
        _ = SeededHash.totalMass (P.conditional ys.1) := by
          exact H.sum_binMass (P.conditional ys.1) ys.2
        _ = 1 := (P.conditional ys.1).sum_prob
    simp_rw [← Finset.mul_sum, hout, mul_one]
    change ∑ ys : Y × S, P.marginal ys.1 * H.seed ys.2 = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, H.seed.sum_prob, mul_one]
    exact P.marginal.sum_prob
  have hqsum : ∑ o, q o = 1 := by
    have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [Fintype.sum_prod_type]
    simp_rw [q, ← Finset.sum_mul]
    simp [hMr, R.sum_prob]
  calc
    0 = perspective f 1 1 := by simp [perspective, f.map_one]
    _ = perspective f (∑ o, p o) (∑ o, q o) := by rw [hpsum, hqsum]
    _ ≤ ∑ o, perspective f (p o) (q o) :=
      perspective_sum_le f p q hp hq
    _ = referenceLeakage f P H R := by
      rw [Fintype.sum_prod_type]
      unfold referenceLeakage
      rw [Fintype.sum_prod_type]

theorem optimizedLeakage_nonneg
    {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (H : SeededHash X S M) (hM : 0 < M) :
    0 ≤ optimizedLeakage f P H := by
  unfold optimizedLeakage
  apply le_csInf
  · let R₀ := P.marginal.prod H.seed
    exact ⟨referenceLeakage f P H R₀, R₀, rfl⟩
  · rintro v ⟨R, rfl⟩
    exact referenceLeakage_nonneg f P H hM R

theorem optimalFixedLeakage_le_family
    {X Y : Type} [Fintype X] [Fintype Y] {M N : ℕ}
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (H : SeededHash X (Fin N) M) (hM : 0 < M) :
    optimalFixedLeakage f P M ≤ fixedLeakage f P H := by
  unfold optimalFixedLeakage
  apply csInf_le
  · exact ⟨0, by
      rintro v ⟨K, G, rfl⟩
      exact fixedLeakage_nonneg f P G hM⟩
  · exact ⟨N, H, rfl⟩

theorem optimizedLeakage_le_reference
    {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] {M : ℕ}
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (H : SeededHash X S M) (hM : 0 < M) (R : FinProb (Y × S)) :
    optimizedLeakage f P H ≤ referenceLeakage f P H R := by
  unfold optimizedLeakage
  apply csInf_le
  · exact ⟨0, by
      rintro v ⟨Q, rfl⟩
      exact referenceLeakage_nonneg f P H hM Q⟩
  · exact ⟨R, rfl⟩

theorem optimalOptimizedLeakage_le_family
    {X Y : Type} [Fintype X] [Fintype Y] {M N : ℕ}
    (f : AdmissibleGenerator) (P : FiniteSource X Y)
    (H : SeededHash X (Fin N) M) (hM : 0 < M) :
    optimalOptimizedLeakage f P M ≤ optimizedLeakage f P H := by
  unfold optimalOptimizedLeakage
  apply csInf_le
  · exact ⟨0, by
      rintro v ⟨K, G, rfl⟩
      exact optimizedLeakage_nonneg f P G hM⟩
  · exact ⟨N, H, rfl⟩

end RandomnessExtraction
