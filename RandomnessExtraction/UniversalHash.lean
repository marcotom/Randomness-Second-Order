import RandomnessExtraction.Hashing
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp

/-!
# An explicit two-universal family

The achievability proof uses no existence postulate for hashing.  This file
constructs the family of all maps to `Fin M`, with the uniform seed, proves
that it is exactly two-universal, and reindexes its finite seed alphabet by a
type of the form `Fin N` used in the operational definitions.
-/

open scoped BigOperators Classical

namespace RandomnessExtraction

namespace SeededHash

variable {X S : Type*} [Fintype X] [Fintype S] {M : ℕ}

/-- The uniform law on an arbitrary nonempty finite type. -/
noncomputable def uniformFintype (A : Type*) [Fintype A] [Nonempty A] :
    FinProb A where
  prob _ := (Fintype.card A : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_prob := by
    simp [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)]

@[simp]
theorem uniformFintype_apply (A : Type*) [Fintype A] [Nonempty A] (a : A) :
    uniformFintype A a = (Fintype.card A : ℝ)⁻¹ := rfl

/-- The family whose seeds are all functions `X → Fin M`. -/
noncomputable def allFunctionsHash (X : Type*) [Fintype X]
    (M : ℕ) (hM : 0 < M) : SeededHash X (X → Fin M) M := by
  letI : Nonempty (Fin M) := Fin.pos_iff_nonempty.mp hM
  exact
    { seed := uniformFintype (X → Fin M)
      hash := fun s x ↦ s x }

private noncomputable def collisionRestrictionEquiv
    (x x' : X) (hne : x ≠ x') :
    {s : X → Fin M // s x = s x'} ≃ ({z : X // z ≠ x} → Fin M) where
  toFun s z := s.1 z.1
  invFun g := ⟨fun z ↦ if hz : z = x then g ⟨x', Ne.symm hne⟩ else g ⟨z, hz⟩, by
    simp [hne]⟩
  left_inv s := by
    apply Subtype.ext
    funext z
    by_cases hz : z = x
    · subst z
      simp [s.2]
    · simp [hz]
  right_inv g := by
    funext z
    simp [z.2]

private theorem collision_card (x x' : X) (hne : x ≠ x') :
    ((Finset.univ.filter fun s : X → Fin M ↦ s x = s x').card) =
      M ^ (Fintype.card X - 1) := by
  calc
    ((Finset.univ.filter fun s : X → Fin M ↦ s x = s x').card) =
        Fintype.card {s : X → Fin M // s x = s x'} := by
          rw [Fintype.card_subtype]
    _ = Fintype.card ({z : X // z ≠ x} → Fin M) :=
      Fintype.card_congr (collisionRestrictionEquiv x x' hne)
    _ = M ^ Fintype.card {z : X // z ≠ x} := by
      rw [Fintype.card_fun, Fintype.card_fin]
    _ = M ^ (Fintype.card X - 1) := by
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

private theorem collisionProbability_allFunctions
    [Nonempty X] (hM : 0 < M) (x x' : X) (hne : x ≠ x') :
    (allFunctionsHash X M hM).collisionProbability x x' = (M : ℝ)⁻¹ := by
  classical
  let k := Fintype.card X - 1
  have hcardX : Fintype.card X = k + 1 := by
    dsimp [k]
    have := Fintype.card_pos_iff.mpr (inferInstance : Nonempty X)
    omega
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  letI : Nonempty (Fin M) := Fin.pos_iff_nonempty.mp hM
  unfold collisionProbability allFunctionsHash FinProb.expect
  rw [show (∑ s : X → Fin M,
      uniformFintype (X → Fin M) s * if s x = s x' then 1 else 0) =
      (Fintype.card (X → Fin M) : ℝ)⁻¹ *
        ∑ s : X → Fin M, if s x = s x' then 1 else 0 by
    simp only [uniformFintype_apply]
    rw [Finset.mul_sum]]
  rw [Finset.sum_boole, collision_card x x' hne, Fintype.card_fun,
    Fintype.card_fin, hcardX, pow_succ]
  push_cast
  field_simp

/-- The all-functions family is exactly two-universal. -/
theorem allFunctionsHash_twoUniversal [Nonempty X] (hM : 0 < M) :
    paperDefinition6 (allFunctionsHash X M hM) := by
  intro x x' hne
  rw [collisionProbability_allFunctions hM x x' hne]

/-- Pull a seeded family back along an equivalence of seed alphabets. -/
noncomputable def reindexSeed {T : Type*} [Fintype T]
    (H : SeededHash X S M) (e : T ≃ S) : SeededHash X T M where
  seed :=
    { prob := fun t ↦ H.seed (e t)
      nonneg := fun t ↦ H.seed.nonneg (e t)
      sum_prob := by
        exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl) |>.trans H.seed.sum_prob }
  hash t x := H.hash (e t) x

theorem collisionProbability_reindexSeed {T : Type*} [Fintype T]
    (H : SeededHash X S M) (e : T ≃ S) (x x' : X) :
    (reindexSeed H e).collisionProbability x x' = H.collisionProbability x x' := by
  classical
  unfold collisionProbability FinProb.expect reindexSeed
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

theorem reindexSeed_twoUniversal {T : Type*} [Fintype T]
    (H : SeededHash X S M) (e : T ≃ S) (hH : paperDefinition6 H) :
    paperDefinition6 (reindexSeed H e) := by
  intro x x' hne
  rw [collisionProbability_reindexSeed]
  exact hH hne

/-- An explicit all-functions hash family whose seed alphabet is `Fin N`. -/
noncomputable def universalFinHash (X : Type*) [Fintype X]
    (M : ℕ) (hM : 0 < M) :
    SeededHash X (Fin (Fintype.card (X → Fin M))) M := by
  letI : Nonempty (Fin M) := Fin.pos_iff_nonempty.mp hM
  exact reindexSeed (allFunctionsHash X M hM)
    (Fintype.equivFin (X → Fin M)).symm

theorem universalFinHash_twoUniversal [Nonempty X] (hM : 0 < M) :
    paperDefinition6 (universalFinHash X M hM) := by
  apply reindexSeed_twoUniversal
  exact allFunctionsHash_twoUniversal hM

/-- Existential packaging used to keep the seed cardinal opaque in the
blocklength-indexed operational family. -/
theorem exists_fin_twoUniversal [Nonempty X] (hM : 0 < M) :
    ∃ N : ℕ, ∃ H : SeededHash X (Fin N) M, paperDefinition6 H := by
  exact ⟨Fintype.card (X → Fin M), universalFinHash X M hM,
    universalFinHash_twoUniversal hM⟩

end SeededHash

end RandomnessExtraction
