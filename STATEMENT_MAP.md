# Paper-to-Lean statement map

Each numbered theorem-like item in `main.tex` has one correspondingly named
public Lean declaration. Supporting results use descriptive names and are
not entries in this table.

| Paper item | TeX label | Lean declaration | Module |
|---|---|---|---|
| Theorem 1 | `thm:main-f` | `RandomnessExtraction.paperTheorem1` | `MainTheorem.lean` |
| Corollary 2 | `cor:fixed-f-leakage` | `RandomnessExtraction.paperCorollary2` | `FixedLeakage.lean` |
| Corollary 3 | `cor:renyi` | `RandomnessExtraction.paperCorollary3` | `Corollaries.lean` |
| Corollary 4 | `cor:total-variation` | `RandomnessExtraction.paperCorollary4` | `Corollaries.lean` |
| Lemma 5 | `lem:oneshot-converse` | `RandomnessExtraction.OneShot.paperLemma5` | `OneShot.lean` |
| Definition 6 | `def:two-universal` | `RandomnessExtraction.SeededHash.paperDefinition6` | `Hashing.lean` |
| Lemma 7 | `lem:two-universal-second-moment` | `RandomnessExtraction.SeededHash.paperLemma7` | `Hashing.lean` |
| Lemma 8 | `lem:light-achievability` | `RandomnessExtraction.LightAchievability.paperLemma8` | `LightAchievability.lean` |
| Lemma 9 | `lem:waterfilling` | `RandomnessExtraction.WaterFilling.paperLemma9` | `WaterFilling.lean` |
| Lemma 10 | `lem:prob-rep` | `RandomnessExtraction.ProbabilityRepresentation.paperLemma10` | `ProbabilityRepresentation.lean` |
| Lemma 11 | `lem:f-tail` | `RandomnessExtraction.TailLimit.paperLemma11` | `TailLimit.lean` |
| Fact 12 | `fact:BE` | `RandomnessExtraction.paperFact12` | `BerryEsseen.lean` |
| Lemma 13 | `lem:conditional-CLT` | `RandomnessExtraction.ConditionalLimit.paperLemma13` | `ConditionalLimit.lean` |
| Lemma 14 | `lem:conditional-capped` | `RandomnessExtraction.ConditionalCapped.paperLemma14` | `ConditionalCapped.lean` |
| Lemma 15 | `lem:perspective-aggregation` | `RandomnessExtraction.PerspectiveAggregation.paperLemma15` | `PerspectiveAggregation.lean` |
| Lemma 16 | `lem:uniform-endpoint` | `RandomnessExtraction.UniformEndpoint.paperLemma16` | `UniformEndpoint.lean` |
| Proposition 17 | `prop:Gaussian-profile` | `RandomnessExtraction.paperProposition17` | `GaussianProfile.lean` |
| Proposition 18 | `prop:Gaussian-profile-down` | `RandomnessExtraction.paperProposition18` | `OptimizedProfile.lean` |
| Lemma 19 | `lem:profile-regularity` | `RandomnessExtraction.paperLemma19` | `ProfileRegularity.lean` |

## Representation conventions

- A finite law is a `FinProb`; a source is a marginal law on `Y` together
  with a conditional law on `X` for every `y`.
- The paper says “finite support.” Public asymptotic declarations present
  `Y` as that support, expressed by `hpY : ∀ y, 0 < P.marginal y`. Zero-mass
  alphabet symbols may first be deleted without changing the law.
- The paper's `o(√n)` fixed-error formulas are stated in the equivalent
  normalized `Tendsto` form.  Output-length suprema have codomain `WithTop ℕ`,
  faithfully representing the paper's `ℕ₀ ∪ {+∞}`; the asymptotic formulas
  use the finite value after eventual boundedness has been proved.
- Theorem 1 and Corollaries 3--4 explicitly quantify over every
  two-universal family sequence for achievability and every seeded-family
  sequence for the converse.
- Rényi criteria are defined natively from the probability laws.  A zero
  overlap has value `+∞`, and separate theorems prove that optimization over
  reference laws and hash families commutes with the power-to-Rényi
  transform on the relevant domain.
- Total-variation criteria are likewise defined directly from the laws; the
  equality with the chosen `f`-divergence generator is proved rather than
  used as a definition.
- `gaussianProfileInverse`, `gaussianRenyiOverlapInverse`, and
  `gaussianQuantile` are defined through their unique level-set points; their
  defining equations are proved.
- `paperFact12` is an explicit proposition giving exactly the Berry--Esseen
  estimate used in the manuscript. Theorem 1 and all downstream corollaries
  take a proof of it as an argument. Mathlib 4.33.1 contains no suitable
  Berry--Esseen theorem, so this is the sole conditional paper fact.

There are no `sorry`, `admit`, or user-defined `axiom` declarations.
