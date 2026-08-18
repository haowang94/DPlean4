# DPlean4: Differential Privacy with Continuous Distributions in Lean 4

A formal verification library for proving differential privacy (DP) of algorithms with continuous output distributions, built in Lean 4 with Mathlib.

All theorems are fully machine-checked with zero `sorry` axioms.

## Features

### Mechanisms
- Continuous Laplace mechanism with pure ε-DP proof
- Continuous Gaussian mechanism with ρ-zCDP and (ε,δ)-DP proofs
- Exponential mechanism (McSherry & Talwar 2007) with ε-DP proof
- Sparse Vector Technique (single-query Above Threshold)
- Report Noisy Max (via exponential mechanism)

### Privacy Definitions and Conversions
- Pure ε-DP (measure-level event inequalities)
- Approximate (ε,δ)-DP
- Rényi DP (Mironov 2017) with RDP-to-(ε,δ)-DP conversion
- Zero-concentrated DP / zCDP (Bun & Dwork 2016) with zCDP-to-(ε,δ)-DP conversion
- Pure DP → zCDP → RDP conversion chain

### Composition and Privacy Amplification
- Sequential composition (pure and approximate DP)
- Parallel composition (disjoint data → max instead of sum)
- Advanced composition via zCDP (√k scaling)
- Group privacy (k-hop adjacency chains)
- Postprocessing preservation (all DP notions)
- Privacy amplification by subsampling (Poisson subsampling)
- k-fold mechanism combinator (Mechanism.piCopy)

### Foundations
- Generic adjacency relations (add/remove, replace)
- L1/L2 sensitivity with algebra (negation, subtraction, Lipschitz, max, min)
- Rényi divergence (moments, DPI, product measures, tail bounds)

### Counterexamples
14 theorems proving specific mechanisms are NOT differentially private, including identity mechanism, buggy SVT, noise reuse, correlated mechanisms, data-dependent noise, thresholded histogram, conditional release, and unbounded sensitivity.

### Examples
- DP-SGD privacy analysis (gradient clipping + Gaussian noise + zCDP composition)
- Private mean estimation (clamped sum + Laplace + postprocessing)
- Private selection (exponential mechanism for model/feature selection)
- Privacy budget management (Laplace splitting, Gaussian zCDP accounting)
- Sensitivity calibration examples
- End-to-end validation tests covering the full library pipeline

## Key Theorems

| Theorem | Statement | File |
|---------|-----------|------|
| `laplaceMech_isPureDP` | Laplace mechanism satisfies ε-DP | `Mechanism/Laplace.lean` |
| `gaussianMech_isZCDP` | Gaussian mechanism satisfies ρ-zCDP | `Mechanism/Gaussian.lean` |
| `expMech_isPureDP` | Exponential mechanism satisfies ε-DP | `Mechanism/Exponential.lean` |
| `isPureDP_prod` | Independent composition: ε₁+ε₂ | `Privacy/Composition.lean` |
| `isZCDP_prod` | zCDP composition: ρ₁+ρ₂ | `Privacy/ZCDP.lean` |
| `isPureDP_parallel` | Parallel composition: max(ε₁,ε₂) | `Privacy/Composition.lean` |
| `isPureDP_postprocess` | Postprocessing preserves DP | `Privacy/Postprocessing.lean` |
| `isZCDP_to_isApproxDP` | zCDP → (ε,δ)-DP conversion | `Privacy/ZCDP.lean` |
| `isRenyiDP_to_isApproxDP` | RDP → (ε,δ)-DP conversion | `Privacy/RenyiDP.lean` |
| `pureMeasureClose_subsample` | Privacy amplification by subsampling | `Privacy/Subsampling.lean` |
| `identityMech_not_pureDP` | Deterministic output is not DP | `Examples/Counterexamples.lean` |
| `noiseReuse_not_pureDP` | Noise reuse breaks DP | `Examples/NoiseReuseCounterexample.lean` |

## Architecture

### Core Design Principles

1. **Mechanisms as functions to probability measures**: `D → ProbabilityMeasure O`
2. **Events first, divergences second**: DP defined via measurable-event inequalities; divergences (hockey-stick, Rényi) proved equivalent later
3. **Generic adjacency**: Adjacency is a relation parameter, not a typeclass
4. **No premature abstraction**: Concrete theorems before any abstract typeclass

### Module Structure

```
DPlean4/
  Basic/          -- Adjacency relations (add/remove, replace), L1/L2 sensitivity
  Probability/    -- Mechanism representation (D → ProbabilityMeasure O), piCopy
  Privacy/        -- DP definitions, composition, postprocessing, subsampling
    MeasureClose.lean      -- Event-level DP inequalities
    Pure.lean              -- Pure ε-DP
    Approximate.lean       -- (ε,δ)-DP
    Composition.lean       -- Sequential, parallel, group privacy
    Postprocessing.lean    -- Postprocessing preservation
    RenyiDivergence.lean   -- Rényi moments, DPI, product measures
    RenyiDP.lean           -- (α,ε)-RDP, conversions to/from zCDP and approx DP
    ZCDP.lean              -- ρ-zCDP, composition, conversion to (ε,δ)-DP
    Subsampling.lean       -- Privacy amplification by Poisson subsampling
  Distribution/   -- Laplace distribution (density, normalization, ratio bounds)
  Mechanism/      -- Laplace, Gaussian, Exponential, SVT, Report Noisy Max
  Examples/       -- 25 example/test files covering all features
```

## Dependencies

- Lean 4.33.0
- Mathlib v4.33.0

## Building

```bash
lake build
```

The first build downloads ~2GB of Mathlib precompiled binaries.

## License

Apache 2.0
