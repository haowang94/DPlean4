# DPlean4: Differential Privacy in Lean 4

A formally verified library for differential privacy, built on [Lean 4](https://lean-lang.org/) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/). Every proof is machine-checked by Lean's kernel. Note the usual caveat of formal verification: Lean checks that each proof establishes its stated theorem, not that the theorem statement faithfully encodes the intended algorithm or the standard mathematical definition — read the definitions, not just the theorem names.

## What's Included

### Privacy Definitions
- Pure ε-DP
- Approximate (ε, δ)-DP
- Rényi DP (Mironov 2017)
- Zero-concentrated DP (Bun & Steinke 2016)
- Conversions between all notions (pure DP → zCDP → RDP → approximate DP)

All DP predicates are **directed**: they quantify over ordered pairs `adj d₁ d₂` and constrain the output distributions in that one direction. The usual two-sided guarantee follows automatically only when the adjacency relation is symmetric (as built-in relations like add/remove and replace are); with an arbitrary custom relation, supply both directions.

### Mechanisms
- **Laplace** — scalar and vector, pure ε-DP
- **Gaussian** — scalar and vector, ρ-zCDP and (ε, δ)-DP
- **Exponential** (McSherry & Talwar 2007) — ε-DP
- **Sparse Vector Technique** — single-query Above Threshold, ε-DP (general multi-query SVT is future work)
- **Report Noisy Max** — exponential-mechanism argmax (equivalently, Gumbel-noise RNM) and a classical add-Laplace-noise-then-argmax variant
- **Randomized Response** — classic ε-calibration (truth probability `exp(ε)/(exp(ε)+1)`)

### Composition and Amplification
- Independent composition (pure and approximate DP)
- Parallel composition (disjoint data → max instead of sum)
- zCDP composition with conversion: ρ → (ε, δ)-DP
- n-fold product composition over finite index types
- Group privacy (k-hop adjacency chains)
- Postprocessing preservation (all DP notions)
- Subsampling: directed measure-level mixture bounds (not yet a mechanism-level amplification theorem — see `Privacy/Subsampling.lean`)

### Foundations
- Generic adjacency relations (add/remove, replace)
- L1/L2 sensitivity with algebraic operations
- Rényi divergence (moments, data processing inequality, product measures)

## Getting Started

### Requirements
- Lean 4.33.0
- Mathlib v4.33.0

### Build
```bash
lake build
```
The first build downloads ~2 GB of Mathlib precompiled binaries.

### Use as a Dependency
Add to your `lakefile.toml`:
```toml
[[require]]
name = "DPlean4"
git = "https://github.com/haowang94/DPlean4"
rev = "master"
```

### Quick Example
```lean
import DPlean4

-- Laplace mechanism with sensitivity 1 satisfies 1-DP
#check laplaceMech_isPureDP

-- Gaussian mechanism satisfies zCDP
#check gaussianMech_isZCDP

-- Compose two mechanisms
#check isPureDP_prod

-- Convert zCDP to (ε,δ)-DP
#check isApproxDP_of_isZCDP
```

## Module Structure

```
DPlean4/
  Basic/          -- Adjacency relations, L1/L2 sensitivity
  Probability/    -- Mechanism type (D → ProbabilityMeasure O)
  Distribution/   -- Laplace distribution (density, normalization, ratio bounds)
  Privacy/        -- DP definitions, composition, postprocessing, subsampling
  Mechanism/      -- Laplace, Gaussian, Exponential, SVT, Report Noisy Max
  Examples/       -- 27 worked examples covering all features
```

## Key Theorems

| Theorem | Statement |
|---------|-----------|
| `laplaceMech_isPureDP` | Laplace mechanism satisfies ε-DP |
| `gaussianMech_isZCDP` | Gaussian mechanism satisfies ρ-zCDP |
| `expMech_isPureDP` | Exponential mechanism satisfies ε-DP |
| `isPureDP_prod` | Independent composition: ε₁ + ε₂ |
| `isApproxDP_prod_tight` | Approx. basic composition: (ε₁+ε₂, δ₁+δ₂) |
| `isZCDP_prod` | zCDP independent composition: ρ₁ + ρ₂ |
| `isZCDP_seqFinite` | Adaptive zCDP composition: ρ₁ + ρ₂ |
| `isPureDP_parallel` | Parallel composition: max(ε₁, ε₂) |
| `isPureDP_postprocess` | Postprocessing preserves DP |
| `isApproxDP_of_isZCDP` | zCDP → (ε, δ)-DP conversion |
| `isApproxDP_of_isRenyiDP` | RDP → (ε, δ)-DP conversion |
| `vectorGaussianMech_isZCDP` | Vector Gaussian mechanism satisfies ρ-zCDP |
| `vectorLaplaceMech_isPureDP` | Vector Laplace mechanism satisfies ε-DP |

## License

Apache 2.0
