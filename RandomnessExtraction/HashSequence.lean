import RandomnessExtraction.RateAsymptotics
import RandomnessExtraction.UniversalHash
import Mathlib.Data.Fintype.Pi

open scoped Classical

namespace RandomnessExtraction

set_option maxHeartbeats 800000

private theorem blockHashExists (X : Type*) [Fintype X] [Nonempty X]
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (n : ℕ) :
    ∃ N : ℕ, ∃ H : SeededHash (Fin n → X) (Fin N) (M n),
      SeededHash.paperDefinition6 H :=
  SeededHash.exists_fin_twoUniversal (hM n)

/-- Number of seeds in the explicit all-functions family at blocklength `n`.
The cardinal is kept opaque to avoid expanding a large function-space type
in every downstream declaration. -/
noncomputable def universalSeedCount (X : Type*) [Fintype X] [Nonempty X]
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (n : ℕ) : ℕ :=
  Classical.choose (blockHashExists X M hM n)

/-- The explicit two-universal block hash used in the direct part. -/
noncomputable def blockUniversalHash (X : Type*) [Fintype X] [Nonempty X]
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (n : ℕ) :
    SeededHash (Fin n → X) (Fin (universalSeedCount X M hM n)) (M n) :=
  Classical.choose (Classical.choose_spec (blockHashExists X M hM n))

theorem blockUniversalHash_twoUniversal
    (X : Type*) [Fintype X] [Nonempty X]
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (n : ℕ) :
    SeededHash.paperDefinition6 (blockUniversalHash X M hM n) := by
  exact Classical.choose_spec
    (Classical.choose_spec (blockHashExists X M hM n))

/-- The opaque seed count, with nonemptiness obtained canonically from the
source law.  This wrapper keeps downstream theorem statements free of an
additional typeclass hypothesis. -/
noncomputable def sourceUniversalSeedCount
    {X Y : Type} [Fintype X] [Fintype Y] (P : FiniteSource X Y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (n : ℕ) : ℕ := by
  letI : Nonempty X := finiteSource_nonempty_left P
  exact universalSeedCount X M hM n

/-- The canonical block hash, with nonemptiness obtained from the source. -/
noncomputable def sourceBlockUniversalHash
    {X Y : Type} [Fintype X] [Fintype Y] (P : FiniteSource X Y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (n : ℕ) :
    SeededHash (Fin n → X) (Fin (sourceUniversalSeedCount P M hM n)) (M n) := by
  letI : Nonempty X := finiteSource_nonempty_left P
  exact blockUniversalHash X M hM n

theorem sourceBlockUniversalHash_twoUniversal
    {X Y : Type} [Fintype X] [Fintype Y] (P : FiniteSource X Y)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n) (n : ℕ) :
    SeededHash.paperDefinition6 (sourceBlockUniversalHash P M hM n) := by
  letI : Nonempty X := finiteSource_nonempty_left P
  exact blockUniversalHash_twoUniversal X M hM n

end RandomnessExtraction
