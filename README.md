# DPlean4: Differential Privacy in Lean 4

A formally verified library for differential privacy, built on [Lean 4](https://lean-lang.org/) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/). All theorems are machine-checked — if it compiles, the proofs are correct.

## What's Included

### Privacy Definitions
- Pure ε-DP
- Approximate (ε, δ)-DP
- Rényi DP (Mironov 2017)
- Zero-concentrated DP (Bun & Dwork 2016)
- Conversions between all notions (pure DP → zCDP → RDP → approximate DP)

### Mechanisms
- **Laplace** — scalar and vector, pure ε-DP
- **Gaussian** — scalar and vector, ρ-zCDP and (ε, δ)-DP
- **Exponential** (McSherry & Talwar 2007) — ε-DP
- **Sparse Vector Technique** — Above Threshold with ε-DP
- **Report Noisy Max** — via exponential mechanism
- **Randomized Response**

### Composition and Amplification
- Sequential composition (pure and approximate DP)
- Parallel composition (disjoint data → max instead of sum)
- zCDP composition with conversion: ρ → (ε, δ)-DP
- n-fold product composition over finite index types
- Group privacy (k-hop adjacency chains)
- Postprocessing preservation (all DP notions)
- Subsampling amplification bounds

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
| `isPureDP_prod` | Sequential composition: ε₁ + ε₂ |
| `isZCDP_prod` | zCDP composition: ρ₁ + ρ₂ |
| `isPureDP_parallel` | Parallel composition: max(ε₁, ε₂) |
| `isPureDP_postprocess` | Postprocessing preserves DP |
| `isApproxDP_of_isZCDP` | zCDP → (ε, δ)-DP conversion |
| `isApproxDP_of_isRenyiDP` | RDP → (ε, δ)-DP conversion |
| `vectorGaussianMech_isZCDP` | Vector Gaussian mechanism satisfies ρ-zCDP |
| `vectorLaplaceMech_isPureDP` | Vector Laplace mechanism satisfies ε-DP |

## License

Apache 2.0
