# Dependency graphs

Arrows point from a prerequisite to a statement that uses it. Unnumbered
technical lemmas are expanded in the second and third graphs.

## Numbered paper statements

```mermaid
flowchart TD
  D6[Definition 6] --> L7[Lemma 7]
  L7 --> L8[Lemma 8]
  L9[Lemma 9] --> L16[Lemma 16]
  L10[Lemma 10] --> L11[Lemma 11]
  L11 --> L14[Lemma 14]
  F12[Fact 12] --> L13[Lemma 13]
  F12 --> L14
  L13 --> L14
  L13 --> L16
  F12 --> L16
  L13 --> P17[Proposition 17]
  L14 --> P17
  L16 --> P17
  F12 --> P17
  L15[Lemma 15] --> P18[Proposition 18]
  F12 --> P18
  L5[Lemma 5] --> T1[Theorem 1]
  L8 --> T1
  P17 --> T1
  P18 --> T1
  T1 --> C2[Corollary 2]
  L19[Lemma 19] --> C2
  T1 --> C3[Corollary 3]
  C2 --> C3
  T1 --> C4[Corollary 4]
  C2 --> C4
```

Lemmas 5, 9, 10, 15, and 19 are proved directly from definitions and
mathlib. The graph records logical use, not merely module imports.

## Theorem 1: internal proof structure

```mermaid
flowchart TD
  Finite[finite probability and perspective calculus]
  Hash[Definition 6 + Lemmas 7 and 8]
  Cap[Lemma 5 + water filling]
  CLT[Fact 12 + Lemmas 11--16]
  Fixed[Proposition 17: fixed profile]
  Opt[Proposition 18: optimized profile]
  UH[explicit all-functions two-universal family]
  Rate[moving-rate asymptotics]
  FFamily[fixedFamilyOperationalLimits]
  OFamily[optimizedFamilyOperationalLimits]
  FMain[fixedOperationalLimits: canonical wrapper]
  OMain[optimizedOperationalLimits: canonical wrapper]
  T1[paperTheorem1]

  Finite --> Hash
  Finite --> Cap
  Cap --> CLT
  CLT --> Fixed
  CLT --> Opt
  Hash --> FFamily
  Hash --> OFamily
  Fixed --> Rate
  Opt --> Rate
  Rate --> FFamily
  Rate --> OFamily
  Cap --> FFamily
  Cap --> OFamily
  FFamily --> FMain
  OFamily --> OMain
  UH --> FMain
  UH --> OMain
  FFamily --> T1
  OFamily --> T1
  FMain --> T1
  OMain --> T1
```

The constructed all-functions family witnesses the operational infima.
The achievability clause itself is stronger: it quantifies over every
sequence of two-universal families.  The converse clause separately
quantifies over every sequence of seeded families, without a universality
assumption.

## Fixed-error inversions and specializations

```mermaid
flowchart TD
  DPI[finite perspective data processing]
  Drop[discardOutputBit]
  Mono[monotonicity in output length]
  Ent[V > 0 implies H > 0]
  Round[roundedBitLength_rate]
  Reg[Lemma 19 + unique profile inverse]
  T1[Theorem 1]
  Inv[leakageLength_inversion]
  C2[Corollary 2]
  Pow[power generator and Rényi transform]
  NativeR[native Rényi divergence + infimum commutation]
  Conv[Gaussian convolution identity]
  NativeTV[native total variation = f-divergence]
  TV[total-variation profile]
  C3[Corollary 3]
  C4[Corollary 4]

  DPI --> Drop --> Mono --> Inv
  Ent --> Round --> Inv
  Reg --> Inv
  T1 --> Inv --> C2
  Pow --> NativeR --> C3
  C2 --> C3
  Conv --> TV --> C4
  NativeTV --> C4
  C2 --> C4
```

The maximum extractable length is an extended-natural supremum in
`WithTop ℕ`, so an unbounded feasible set is represented by `+∞` rather
than by an arbitrary natural default.  A strict upper leakage bracket proves
the i.i.d. feasible set bounded eventually; `Nat.sSup_mem` then supplies its
actual finite maximum.  This formally resolves the infinite case, integer
rounding, and uniformity in the manuscript's inversion argument.

## Conditional boundary

```mermaid
flowchart LR
  BE[proof of paperFact12] --> L13[Lemma 13]
  BE --> L14[Lemma 14]
  BE --> L16[Lemma 16]
  BE --> P17[Proposition 17]
  BE --> P18[Proposition 18]
  P17 --> T1[Theorem 1]
  P18 --> T1
  T1 --> C2[Corollary 2]
  T1 --> C3[Corollary 3]
  T1 --> C4[Corollary 4]
```

Supplying a proof of `paperFact12` makes all headline results unconditional.
No other paper fact or added hypothesis is used.
