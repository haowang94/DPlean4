# DPlean4: Differential Privacy with Continuous Distributions in Lean 4

A formal verification library for proving differential privacy (DP) of algorithms with continuous output distributions, built in Lean 4 with Mathlib.

## Project Status

🚧 **Early Development** - Milestone 0 in progress

This library is under active development. The goal is to provide the first comprehensive Lean 4 formalization of differential privacy that handles continuous distributions through measure-theoretic foundations.

## Features (Planned)

- ✅ Continuous Laplace mechanism with pure ε-DP proof
- ✅ Continuous Gaussian mechanism with (ε,δ)-DP proof  
- ✅ Generic adjacency relations (unbounded/bounded DP)
- ✅ Composition theorems (sequential, parallel, adaptive)
- ✅ Postprocessing theorem
- ⬜ Rényi DP and zero-concentrated DP (zCDP)
- ⬜ Exponential mechanism
- ⬜ Advanced composition
- ⬜ Privacy amplification by subsampling

## Architecture

### Core Design Principles

1. **Mechanisms as functions to probability measures**: `D → ProbabilityMeasure O`
2. **Events first, divergences second**: DP defined via measurable-event inequalities; divergences (hockey-stick, Rényi) proved equivalent later
3. **Generic adjacency**: Adjacency is a relation parameter, not a typeclass
4. **No premature abstraction**: Concrete theorems before any abstract typeclass

### Module Structure

```
DPlean4/
  Basic/          -- Adjacency relations, sensitivity
  Probability/    -- Mechanism representation, kernel bridges
  Privacy/        -- DP definitions, composition, postprocessing
  Divergence/     -- Hockey-stick, Rényi divergence
  Distribution/   -- Laplace, Gaussian distributions
  Mechanism/      -- Verified DP mechanisms
  Examples/       -- Randomized response, report noisy max
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

1. **Boundary case tests**: ε=0, δ=0, zero sensitivity, degenerate measures
2. **Composition round-trips**: End-to-end examples that compose mechanisms and verify bounds
3. **Classical mechanisms**: Laplace, Gaussian, Randomized Response as regression tests
4. **Axiom audits**: `#print axioms` on all flagship theorems (must show only classical/choice/quotient)

## Comparison with Existing Work

| System | Proof Assistant | Continuous? | Scope |
|--------|----------------|-------------|-------|
| **SampCert** (PLDI 2025) | Lean 4 | No (discrete only) | Pure DP, zCDP, discrete Laplace/Gaussian |
| **CertiPriv** (POPL 2012) | Coq | No | Laplace, Gaussian, Exponential via apRHL |
| **Sato & Minamide** (CPP 2025) | Isabelle/HOL | Yes | Continuous Laplace, report noisy max |
| **DPlean4** (this project) | Lean 4 | **Yes** | Continuous Laplace, Gaussian, zCDP, composition |

This is the first Lean 4 library proving DP for continuous mechanisms, and aims to be the first formalization of continuous zCDP/RDP in any proof assistant.

## Documentation

- [`PLAN.md`](PLAN.md) - Detailed implementation plan with milestones
- [`CODEX_CONTINUOUS_DP_PLAN.md`](CODEX_CONTINUOUS_DP_PLAN.md) - Critical architecture review

## License

Apache 2.0

## Contributing

This project is in early development. Design decisions are still being finalized through Milestone 3 (continuous Laplace mechanism). After that milestone, the API will stabilize and contributions will be welcome.

## References

- [SampCert: PLDI 2025](https://arxiv.org/abs/2412.01671) - Discrete DP in Lean 4
- [Sato & Minamide: CPP 2025](https://arxiv.org/abs/2410.15386) - Continuous DP in Isabelle/HOL
- [Mathlib Measure Theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory.html)
- [The Algorithmic Foundations of Differential Privacy](https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf) - Dwork & Roth
