# DPlean4: Differential Privacy with Continuous Distributions in Lean 4

A formal verification library for proving differential privacy (DP) of algorithms with continuous output distributions, built in Lean 4 with Mathlib.

## Project Status

**48 files, 0 sorrys, 3702 build jobs** -- Milestones 0-6 complete.

All theorems are fully machine-checked. The library covers continuous Laplace and Gaussian mechanisms, four DP notions (pure, approximate, Renyi, zCDP), composition, postprocessing, subsampling amplification, and 14 counterexample theorems proving that specific mechanisms are NOT differentially private.

## Features

### Mechanisms
- ✅ Continuous Laplace mechanism with pure ε-DP proof
- ✅ Continuous Gaussian mechanism with ρ-zCDP and (ε,δ)-DP proofs
- ✅ Exponential mechanism (McSherry & Talwar 2007) with ε-DP proof
- ✅ Sparse Vector Technique (single-query Above Threshold)
- ✅ Report Noisy Max (via exponential mechanism)

### Privacy Definitions and Conversions
- ✅ Pure ε-DP (measure-level event inequalities)
- ✅ Approximate (ε,δ)-DP
- ✅ Renyi DP (Mironov 2017) with RDP-to-(ε,δ)-DP conversion
- ✅ Zero-concentrated DP / zCDP (Bun & Dwork 2016) with zCDP-to-(ε,δ)-DP conversion
- ✅ Pure DP → zCDP → RDP conversion chain

### Composition and Privacy Amplification
- ✅ Sequential composition (pure and approximate DP)
- ✅ Parallel composition (disjoint data → max instead of sum)
- ✅ Advanced composition via zCDP (√k scaling)
- ✅ Group privacy (k-hop adjacency chains)
- ✅ Postprocessing preservation (all DP notions)
- ✅ Privacy amplification by subsampling (Poisson subsampling)
- ✅ k-fold mechanism combinator (Mechanism.piCopy)

### Foundations
- ✅ Generic adjacency relations (add/remove, replace)
- ✅ L1/L2 sensitivity with algebra (negation, subtraction, Lipschitz, max, min)
- ✅ Renyi divergence (moments, DPI, product measures, tail bounds)

### Counterexamples (14 theorems proving mechanisms are NOT DP)
- ✅ Identity mechanism (deterministic output)
- ✅ Buggy SVT5 (no query noise, Lyu et al. 2017)
- ✅ Noise reuse (same Laplace noise for two queries)
- ✅ Correlated mechanisms (shared noise reveals input)
- ✅ Data-dependent noise scale (scale leaks information)
- ✅ Thresholded histogram (suppress noise for zeros)
- ✅ Conditional release (safety flag leaks check result)
- ✅ Unbounded sensitivity (unclamped max/sum queries)

### Examples and Validation
- ✅ DP-SGD privacy analysis (gradient clipping + Gaussian noise + zCDP composition)
- ✅ Private mean estimation (clamped sum + Laplace + postprocessing)
- ✅ Private selection (exponential mechanism for model/feature selection)
- ✅ Privacy budget management (Laplace splitting, Gaussian zCDP accounting)
- ✅ Sensitivity calibration examples
- ✅ 19 end-to-end validation tests covering the full library pipeline

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

All flagship theorems depend only on `propext`, `Classical.choice`, and `Quot.sound` (verified via `#print axioms`).

## Architecture

### Core Design Principles

1. **Mechanisms as functions to probability measures**: `D → ProbabilityMeasure O`
2. **Events first, divergences second**: DP defined via measurable-event inequalities; divergences (hockey-stick, Renyi) proved equivalent later
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
    RenyiDivergence.lean   -- Renyi moments, DPI, product measures
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

## Testing Strategy

We validate the library through:

1. **Zero sorry policy**: All 48 files compile with 0 sorrys -- this is a machine-checked guarantee
2. **Axiom audits**: `#print axioms` on all flagship theorems (must show only `propext`, `Classical.choice`, `Quot.sound`)
3. **Counterexamples**: 14 theorems proving specific mechanisms are NOT DP, demonstrating the framework can refute incorrect claims
4. **End-to-end validation**: 19 integration tests exercising the full pipeline (mechanism → DP proof → composition → conversion → amplification)
5. **Boundary cases**: ε=0, δ=0, zero sensitivity, degenerate measures, rate-0/rate-1 subsampling

## Comparison with Existing Work

| System | Proof Assistant | Continuous? | Scope |
|--------|----------------|-------------|-------|
| **SampCert** (PLDI 2025) | Lean 4 | No (discrete only) | Pure DP, zCDP, discrete Laplace/Gaussian |
| **CertiPriv** (POPL 2012) | Coq | No | Laplace, Gaussian, Exponential via apRHL |
| **Sato & Minamide** (CPP 2025) | Isabelle/HOL | Yes | Continuous Laplace, report noisy max |
| **DPlean4** (this project) | Lean 4 | **Yes** | Continuous Laplace/Gaussian, Exponential, zCDP/RDP, composition, subsampling |

DPlean4 is the first Lean 4 library proving DP for continuous mechanisms, and the first formalization of continuous zCDP/RDP with full composition and conversion theorems in any proof assistant.

## Roadmap

Remaining extensions (all current features are complete):
- Adaptive composition via Markov kernels
- General n-query SVT
- More SVT counterexamples (SVT3, SVT6)
- Truncated Laplace counterexample

## Documentation

- [`PLAN.md`](PLAN.md) - Detailed implementation plan with milestones
- [`PROGRESS.md`](PROGRESS.md) - Implementation progress tracking
- [`CODEX_CONTINUOUS_DP_PLAN.md`](CODEX_CONTINUOUS_DP_PLAN.md) - Architecture review

## License

Apache 2.0

## Contributing

The core API is stable through Milestone 6. Contributions are welcome, especially for:
- New mechanism implementations
- Additional counterexamples from the DP literature
- Adaptive composition via Markov kernels

## References

- [SampCert: PLDI 2025](https://arxiv.org/abs/2412.01671) - Discrete DP in Lean 4
- [Sato & Minamide: CPP 2025](https://arxiv.org/abs/2410.15386) - Continuous DP in Isabelle/HOL
- [Mathlib Measure Theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory.html)
- [The Algorithmic Foundations of Differential Privacy](https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf) - Dwork & Roth
- [Concentrated Differential Privacy](https://arxiv.org/abs/1605.02065) - Bun & Dwork, 2016
- [Renyi Differential Privacy](https://arxiv.org/abs/1702.07476) - Mironov, 2017
