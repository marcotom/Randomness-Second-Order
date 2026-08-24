# Exact second-order classical randomness extraction

This repository contains the Lean 4 formalization accompanying the paper
*Exact Second-Order Classical Randomness Extraction Under f-Divergence
Criteria*.

The formalization covers every numbered theorem, corollary, lemma,
proposition, fact, and definition in the manuscript. It uses only mathlib.

## Build

The project is pinned to Lean and mathlib 4.33.1 by `lean-toolchain` and
`lake-manifest.json`.

```bash
lake build RandomnessExtraction
```

The aggregate import is `RandomnessExtraction.lean`. To print the kernel
axioms used by every numbered declaration, run:

```bash
lake env lean Audit.lean
```

The source snapshot copied into this export passed a 3162-job build, and the
exported Lean and configuration files were then verified byte-for-byte against
that snapshot. The build emits only linter and deprecation warnings.

## Formalization boundary

The main theorem and its corollaries take a proof of `paperFact12` as an
explicit argument. This proposition is the finite-product Berry--Esseen
estimate used in the manuscript. It is not declared as an axiom. All other
numbered statements are proved from definitions, `paperFact12`, and mathlib.

The source contains no `sorry`, `admit`, or user-defined `axiom`
declarations. `Audit.lean` reports only Lean/mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound` kernel axioms.

## Paper-to-Lean correspondence

The following GitHub-native Mermaid diagram summarizes the one-to-one
correspondence. The complete table, including TeX labels and module names, is
in [`STATEMENT_MAP.md`](STATEMENT_MAP.md).

```mermaid
flowchart LR
  subgraph Headline["Headline results"]
    direction LR
    T1["Theorem 1"] --> LT1["paperTheorem1<br/>MainTheorem.lean"]
    C2["Corollary 2"] --> LC2["paperCorollary2<br/>FixedLeakage.lean"]
    C3["Corollary 3"] --> LC3["paperCorollary3<br/>Corollaries.lean"]
    C4["Corollary 4"] --> LC4["paperCorollary4<br/>Corollaries.lean"]
  end

  subgraph OneShot["One-shot structure"]
    direction LR
    L5["Lemma 5"] --> LL5["OneShot.paperLemma5<br/>OneShot.lean"]
    D6["Definition 6"] --> LD6["SeededHash.paperDefinition6<br/>Hashing.lean"]
    L7["Lemma 7"] --> LL7["SeededHash.paperLemma7<br/>Hashing.lean"]
    L8["Lemma 8"] --> LL8["LightAchievability.paperLemma8<br/>LightAchievability.lean"]
    L9["Lemma 9"] --> LL9["WaterFilling.paperLemma9<br/>WaterFilling.lean"]
    L10["Lemma 10"] --> LL10["ProbabilityRepresentation.paperLemma10<br/>ProbabilityRepresentation.lean"]
  end

  subgraph Asymptotic["Asymptotic analysis"]
    direction LR
    L11["Lemma 11"] --> LL11["TailLimit.paperLemma11<br/>TailLimit.lean"]
    F12["Fact 12"] --> LF12["paperFact12<br/>BerryEsseen.lean"]
    L13["Lemma 13"] --> LL13["ConditionalLimit.paperLemma13<br/>ConditionalLimit.lean"]
    L14["Lemma 14"] --> LL14["ConditionalCapped.paperLemma14<br/>ConditionalCapped.lean"]
    L15["Lemma 15"] --> LL15["PerspectiveAggregation.paperLemma15<br/>PerspectiveAggregation.lean"]
    L16["Lemma 16"] --> LL16["UniformEndpoint.paperLemma16<br/>UniformEndpoint.lean"]
    P17["Proposition 17"] --> LP17["paperProposition17<br/>GaussianProfile.lean"]
    P18["Proposition 18"] --> LP18["paperProposition18<br/>OptimizedProfile.lean"]
    L19["Lemma 19"] --> LL19["paperLemma19<br/>ProfileRegularity.lean"]
  end
```

## Logical relationships

Arrows below point from a prerequisite to a numbered statement that uses it.
Expanded internal graphs for Theorem 1, the fixed-leakage inversions, and the
conditional Berry--Esseen boundary are in
[`DEPENDENCIES.md`](DEPENDENCIES.md).

```mermaid
flowchart TD
  D6["Definition 6"] --> L7["Lemma 7"]
  L7 --> L8["Lemma 8"]
  L9["Lemma 9"] --> L16["Lemma 16"]
  L10["Lemma 10"] --> L11["Lemma 11"]
  L11 --> L14["Lemma 14"]
  F12["Fact 12"] --> L13["Lemma 13"]
  F12 --> L14
  L13 --> L14
  L13 --> L16
  F12 --> L16
  L13 --> P17["Proposition 17"]
  L14 --> P17
  L16 --> P17
  F12 --> P17
  L15["Lemma 15"] --> P18["Proposition 18"]
  F12 --> P18
  L5["Lemma 5"] --> T1["Theorem 1"]
  L8 --> T1
  P17 --> T1
  P18 --> T1
  T1 --> C2["Corollary 2"]
  L19["Lemma 19"] --> C2
  T1 --> C3["Corollary 3"]
  C2 --> C3
  T1 --> C4["Corollary 4"]
  C2 --> C4
```

## Repository layout

```text
.
├── RandomnessExtraction/      # Formalization modules
├── RandomnessExtraction.lean  # Aggregate import
├── Audit.lean                 # Kernel-axiom audit
├── STATEMENT_MAP.md           # Full paper-to-Lean correspondence
├── DEPENDENCIES.md            # Detailed dependency graphs
├── lakefile.toml              # Lake package definition
├── lake-manifest.json         # Pinned dependency manifest
├── lean-toolchain             # Pinned Lean toolchain
├── CITATION.cff               # Citation metadata
└── .gitignore
```

## Library policy

Every external import begins with `Mathlib`. The sole package dependency in
`lakefile.toml` is mathlib; no other Lean library is used.
